Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_PRODUCT_term_abbrevs.
Require Import CARD_PRODUCT_spec.
Require Import FINITE_PRODUCT_spec.
Require Import HAS_SIZE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4323934 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4323391 A B s). Qed.
Lemma lem4323935 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4323936 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4323935 A B s) (@lem4323934 A B s)). Qed.
Lemma lem4323937 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term2 A B s t.
Proof. exact (@lem4323936 A B s t). Qed.
Lemma lem4323938 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term2 A B s t) = (term3 A B s t).
Proof. exact (eq_refl (term2 A B s t)). Qed.
Lemma lem4323939 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term3 A B s t.
Proof. exact (EQ_MP (@lem4323938 A B s t) (@lem4323937 A B s t)). Qed.
Lemma lem4323940 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term4 A B s t) : term4 A B s t.
Proof. exact (h1). Qed.
Lemma lem4323941 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term4 A B s t) : term5 A B s t.
Proof. exact (@lem4323939 A B s t (@lem4323940 A B s t h1)). Qed.
Lemma lem4323942 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term5 A B s t) = ((term5 A B s t) = True).
Proof. exact (@lem7 (term5 A B s t)). Qed.
Lemma lem4323943 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term4 A B s t) : (term5 A B s t) = True.
Proof. exact (EQ_MP (@lem4323942 A B s t) (@lem4323941 A B s t h1)). Qed.
Lemma lem4323949 {A B : Type'} (s : A -> Prop) : term6 A B s.
Proof. exact (@lem4323933 A B s). Qed.
Lemma lem4323950 {A B : Type'} (s : A -> Prop) : (term6 A B s) = (term7 A B s).
Proof. exact (eq_refl (term6 A B s)). Qed.
Lemma lem4323951 {A B : Type'} (s : A -> Prop) : term7 A B s.
Proof. exact (EQ_MP (@lem4323950 A B s) (@lem4323949 A B s)). Qed.
Lemma lem4323952 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term8 A B s t.
Proof. exact (@lem4323951 A B s t). Qed.
Lemma lem4323953 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term8 A B s t) = (term9 A B s t).
Proof. exact (eq_refl (term8 A B s t)). Qed.
Lemma lem4323954 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term9 A B s t.
Proof. exact (EQ_MP (@lem4323953 A B s t) (@lem4323952 A B s t)). Qed.
Lemma lem4323955 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term4 A B s t) : term4 A B s t.
Proof. exact (h1). Qed.
Lemma lem4323956 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term4 A B s t) : (term10 A B s t) = (term11 A B s t).
Proof. exact (@lem4323954 A B s t (@lem4323955 A B s t h1)). Qed.
Lemma lem4323962 {_100044 : Type'} (s : _100044 -> Prop) : term12 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4323963 {_100044 : Type'} (s : _100044 -> Prop) : (term12 _100044 s) = (term13 _100044 s).
Proof. exact (eq_refl (term12 _100044 s)). Qed.
Lemma lem4323964 {_100044 : Type'} (s : _100044 -> Prop) : term13 _100044 s.
Proof. exact (EQ_MP (@lem4323963 _100044 s) (@lem4323962 _100044 s)). Qed.
Lemma lem4323965 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term14 _100044 s n.
Proof. exact (@lem4323964 _100044 s n). Qed.
Lemma lem4323966 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term14 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term15 _100044 s n)).
Proof. exact (eq_refl (term14 _100044 s n)). Qed.
Lemma lem4323987 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term16 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4323988 (p : Prop) (q : Prop) (p' : Prop) : term17 p q p'.
Proof. exact (fun q' : Prop => @lem4323987 p q p' q'). Qed.
Lemma lem4323989 (p : Prop) (q : Prop) : term18 p q.
Proof. exact (fun p' : Prop => @lem4323988 p q p'). Qed.
Lemma lem4323990 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) : term19 A B s t m n.
Proof. exact (@lem4323989 (term20 A B s m t n) (term21 A B s t m n)). Qed.
Lemma lem4323991 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) (p' : Prop) : term22 A B s t m n p'.
Proof. exact (@lem4323990 A B s t m n p'). Qed.
Lemma lem4323992 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) (p' : Prop) : (term22 A B s t m n p') = (term23 A B s t m n p').
Proof. exact (eq_refl (term22 A B s t m n p')). Qed.
Lemma lem4323993 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) (p' : Prop) : term23 A B s t m n p'.
Proof. exact (EQ_MP (@lem4323992 A B s t m n p') (@lem4323991 A B s t m n p')). Qed.
Lemma lem4323994 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term24 A B s t m n p' q'.
Proof. exact (@lem4323993 A B s t m n p' q'). Qed.
Lemma lem4323995 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term24 A B s t m n p' q') = (term25 A B s t m n p' q').
Proof. exact (eq_refl (term24 A B s t m n p' q')). Qed.
Lemma lem4323996 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term25 A B s t m n p' q'.
Proof. exact (EQ_MP (@lem4323995 A B s t m n p' q') (@lem4323994 A B s t m n p' q')). Qed.
Lemma lem4324000 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term15 _100044 s n).
Proof. exact (EQ_MP (@lem4323966 _100044 s n) (@lem4323965 _100044 s n)). Qed.
Lemma lem4324001 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term15 A s n).
Proof. exact (@lem4324000 A s n). Qed.
Lemma lem4324002 {A : Type'} (s : A -> Prop) (m : nat) : (@HAS_SIZE A s m) = (term15 A s m).
Proof. exact (@lem4324001 A s m). Qed.
Lemma lem4324007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4324008 {A : Type'} (s : A -> Prop) (m : nat) : (term26 A s m) = (term27 A s m).
Proof. exact (MK_COMB (@lem4324007) (@lem4324002 A s m)). Qed.
Lemma lem4324014 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term15 _100044 s n).
Proof. exact (EQ_MP (@lem4323966 _100044 s n) (@lem4323965 _100044 s n)). Qed.
Lemma lem4324015 {B : Type'} (s : B -> Prop) (n : nat) : (@HAS_SIZE B s n) = (term15 B s n).
Proof. exact (@lem4324014 B s n). Qed.
Lemma lem4324016 {B : Type'} (t : B -> Prop) (n : nat) : (@HAS_SIZE B t n) = (term15 B t n).
Proof. exact (@lem4324015 B t n). Qed.
Lemma lem4324021 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) : (term20 A B s m t n) = (term28 A B s m t n).
Proof. exact (MK_COMB (@lem4324008 A s m) (@lem4324016 B t n)). Qed.
Lemma lem4324032 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (q' : Prop) : term29 A B s m t n q'.
Proof. exact (@lem4323996 A B s t m n (term28 A B s m t n) q'). Qed.
Lemma lem4324033 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (q' : Prop) : term30 A B s m t n q'.
Proof. exact (@lem4324032 A B s m t n q' (@lem4324021 A B s m t n)). Qed.
Lemma lem4324034 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : term28 A B s m t n.
Proof. exact (h1). Qed.
Lemma lem4324035 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : term15 B t n.
Proof. exact (proj2 (@lem4324034 A B s m t n h1)). Qed.
Lemma lem4324037 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : @FINITE B t.
Proof. exact (proj1 (@lem4324035 A B s m t n h1)). Qed.
Lemma lem4324038 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem4324040 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : term15 A s m.
Proof. exact (proj1 (@lem4324034 A B s m t n h1)). Qed.
Lemma lem4324042 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : @FINITE A s.
Proof. exact (proj1 (@lem4324040 A B s m t n h1)). Qed.
Lemma lem4324043 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4324046 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term15 _100044 s n).
Proof. exact (EQ_MP (@lem4323966 _100044 s n) (@lem4323965 _100044 s n)). Qed.
Lemma lem4324047 {A B : Type'} (s : type1210 A B) (n : nat) : (@HAS_SIZE (prod A B) s n) = (term31 A B s n).
Proof. exact (@lem4324046 (prod A B) s n). Qed.
Lemma lem4324048 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) : (term21 A B s t m n) = (term32 A B s t m n).
Proof. exact (@lem4324047 A B (term33 A B s t) (Nat.mul m n)). Qed.
Lemma lem4324052 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term34 A B s t.
Proof. exact (fun h0 : term4 A B s t => @lem4323943 A B s t h0). Qed.
Lemma lem4324053 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term34 A B s t.
Proof. exact (@lem4324052 A B s t). Qed.
Lemma lem4324057 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4324043 A s) (@lem4324042 A B s m t n h1)). Qed.
Lemma lem4324058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4324059 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term35 A s) = (and True).
Proof. exact (MK_COMB (@lem4324058) (@lem4324057 A B s m t n h1)). Qed.
Lemma lem4324061 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem4324038 B t) (@lem4324037 A B s m t n h1)). Qed.
Lemma lem4324062 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term4 A B s t) = (True /\ True).
Proof. exact (MK_COMB (@lem4324059 A B s m t n h1) (@lem4324061 A B s m t n h1)). Qed.
Lemma lem4324064 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4324065 : (True /\ True) = True.
Proof. exact (@lem4324064 True). Qed.
Lemma lem4324066 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term4 A B s t) = True.
Proof. exact (TRANS (@lem4324062 A B s m t n h1) (@lem4324065)). Qed.
Lemma lem4324067 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : True = (term4 A B s t).
Proof. exact (SYM (@lem4324066 A B s m t n h1)). Qed.
Lemma lem4324068 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : term4 A B s t.
Proof. exact (EQ_MP (@lem4324067 A B s m t n h1) (@lem0)). Qed.
Lemma lem4324069 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term5 A B s t) = True.
Proof. exact (@lem4324053 A B s t (@lem4324068 A B s m t n h1)). Qed.
Lemma lem4324070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4324071 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term36 A B s t) = (and True).
Proof. exact (MK_COMB (@lem4324070) (@lem4324069 A B s m t n h1)). Qed.
Lemma lem4324075 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term9 A B s t.
Proof. exact (fun h0 : term4 A B s t => @lem4323956 A B s t h0). Qed.
Lemma lem4324076 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term9 A B s t.
Proof. exact (@lem4324075 A B s t). Qed.
Lemma lem4324080 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4324043 A s) (@lem4324042 A B s m t n h1)). Qed.
Lemma lem4324081 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4324082 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term35 A s) = (and True).
Proof. exact (MK_COMB (@lem4324081) (@lem4324080 A B s m t n h1)). Qed.
Lemma lem4324084 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem4324038 B t) (@lem4324037 A B s m t n h1)). Qed.
Lemma lem4324085 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term4 A B s t) = (True /\ True).
Proof. exact (MK_COMB (@lem4324082 A B s m t n h1) (@lem4324084 A B s m t n h1)). Qed.
Lemma lem4324087 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4324088 : (True /\ True) = True.
Proof. exact (@lem4324087 True). Qed.
Lemma lem4324089 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term4 A B s t) = True.
Proof. exact (TRANS (@lem4324085 A B s m t n h1) (@lem4324088)). Qed.
Lemma lem4324090 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : True = (term4 A B s t).
Proof. exact (SYM (@lem4324089 A B s m t n h1)). Qed.
Lemma lem4324091 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : term4 A B s t.
Proof. exact (EQ_MP (@lem4324090 A B s m t n h1) (@lem0)). Qed.
Lemma lem4324092 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term10 A B s t) = (term11 A B s t).
Proof. exact (@lem4324076 A B s t (@lem4324091 A B s m t n h1)). Qed.
Lemma lem4324094 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (@CARD A s) = m.
Proof. exact (proj2 (@lem4324040 A B s m t n h1)). Qed.
Lemma lem4324095 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem4324096 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term37 A s) = (Nat.mul m).
Proof. exact (MK_COMB (@lem4324095) (@lem4324094 A B s m t n h1)). Qed.
Lemma lem4324098 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (@CARD B t) = n.
Proof. exact (proj2 (@lem4324035 A B s m t n h1)). Qed.
Lemma lem4324099 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term11 A B s t) = (Nat.mul m n).
Proof. exact (MK_COMB (@lem4324096 A B s m t n h1) (@lem4324098 A B s m t n h1)). Qed.
Lemma lem4324100 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term10 A B s t) = (Nat.mul m n).
Proof. exact (TRANS (@lem4324092 A B s m t n h1) (@lem4324099 A B s m t n h1)). Qed.
Lemma lem4324101 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4324102 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term38 A B s t) = (term39 m n).
Proof. exact (MK_COMB (@lem4324101) (@lem4324100 A B s m t n h1)). Qed.
Lemma lem4324103 (m : nat) (n : nat) : (Nat.mul m n) = (Nat.mul m n).
Proof. exact (eq_refl (Nat.mul m n)). Qed.
Lemma lem4324104 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : ((term10 A B s t) = (Nat.mul m n)) = ((Nat.mul m n) = (Nat.mul m n)).
Proof. exact (MK_COMB (@lem4324102 A B s m t n h1) (@lem4324103 m n)). Qed.
Lemma lem4324106 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4324107 (x : nat) : (x = x) = True.
Proof. exact (@lem4324106 nat x). Qed.
Lemma lem4324108 (m : nat) (n : nat) : ((Nat.mul m n) = (Nat.mul m n)) = True.
Proof. exact (@lem4324107 (Nat.mul m n)). Qed.
Lemma lem4324109 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : ((term10 A B s t) = (Nat.mul m n)) = True.
Proof. exact (TRANS (@lem4324104 A B s m t n h1) (@lem4324108 m n)). Qed.
Lemma lem4324110 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term32 A B s t m n) = (True /\ True).
Proof. exact (MK_COMB (@lem4324071 A B s m t n h1) (@lem4324109 A B s m t n h1)). Qed.
Lemma lem4324112 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4324113 : (True /\ True) = True.
Proof. exact (@lem4324112 True). Qed.
Lemma lem4324114 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term32 A B s t m n) = True.
Proof. exact (TRANS (@lem4324110 A B s m t n h1) (@lem4324113)). Qed.
Lemma lem4324115 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term28 A B s m t n) : (term21 A B s t m n) = True.
Proof. exact (TRANS (@lem4324048 A B s t m n) (@lem4324114 A B s m t n h1)). Qed.
Lemma lem4324116 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) : term40 A B s t m n.
Proof. exact (fun h0 : term28 A B s m t n => @lem4324115 A B s m t n h0). Qed.
Lemma lem4324117 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) : term41 A B s m t n.
Proof. exact (@lem4324033 A B s m t n True). Qed.
Lemma lem4324118 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) : (term42 A B s t m n) = (term43 A B s m t n).
Proof. exact (@lem4324117 A B s m t n (@lem4324116 A B s t m n)). Qed.
Lemma lem4324120 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4324121 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) : (term43 A B s m t n) = True.
Proof. exact (@lem4324120 (term28 A B s m t n)). Qed.
Lemma lem4324122 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) : (term42 A B s t m n) = True.
Proof. exact (TRANS (@lem4324118 A B s m t n) (@lem4324121 A B s m t n)). Qed.
Lemma lem4324123 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) : (term44 A B s t m) = term45.
Proof. exact (fun_ext (fun n : nat => @lem4324122 A B s t m n)). Qed.
Lemma lem4324124 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4324125 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) : (term46 A B s t m) = term47.
Proof. exact (MK_COMB (@lem4324124) (@lem4324123 A B s t m)). Qed.
Lemma lem4324127 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4324128 (t : Prop) : (term49 t) = t.
Proof. exact (@lem4324127 nat t). Qed.
Lemma lem4324129 : term47 = True.
Proof. exact (@lem4324128 True). Qed.
Lemma lem4324130 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) : (term46 A B s t m) = True.
Proof. exact (TRANS (@lem4324125 A B s t m) (@lem4324129)). Qed.
Lemma lem4324131 {A B : Type'} (s : A -> Prop) (m : nat) : (term50 A B s m) = (term51 B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4324130 A B s t m)). Qed.
Lemma lem4324132 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4324133 {A B : Type'} (s : A -> Prop) (m : nat) : (term52 A B s m) = (term53 B).
Proof. exact (MK_COMB (@lem4324132 B) (@lem4324131 A B s m)). Qed.
Lemma lem4324135 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4324136 {B : Type'} (t : Prop) : (term54 B t) = t.
Proof. exact (@lem4324135 (B -> Prop) t). Qed.
Lemma lem4324137 {B : Type'} : (term53 B) = True.
Proof. exact (@lem4324136 B True). Qed.
Lemma lem4324138 {A B : Type'} (s : A -> Prop) (m : nat) : (term52 A B s m) = True.
Proof. exact (TRANS (@lem4324133 A B s m) (@lem4324137 B)). Qed.
Lemma lem4324139 {A B : Type'} (s : A -> Prop) : (term55 A B s) = term45.
Proof. exact (fun_ext (fun m : nat => @lem4324138 A B s m)). Qed.
Lemma lem4324140 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4324141 {A B : Type'} (s : A -> Prop) : (term56 A B s) = term47.
Proof. exact (MK_COMB (@lem4324140) (@lem4324139 A B s)). Qed.
Lemma lem4324143 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4324144 (t : Prop) : (term49 t) = t.
Proof. exact (@lem4324143 nat t). Qed.
Lemma lem4324145 : term47 = True.
Proof. exact (@lem4324144 True). Qed.
Lemma lem4324146 {A B : Type'} (s : A -> Prop) : (term56 A B s) = True.
Proof. exact (TRANS (@lem4324141 A B s) (@lem4324145)). Qed.
Lemma lem4324147 {A B : Type'} : (term57 A B) = (term51 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4324146 A B s)). Qed.
Lemma lem4324148 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4324149 {A B : Type'} : (term58 A B) = (term53 A).
Proof. exact (MK_COMB (@lem4324148 A) (@lem4324147 A B)). Qed.
Lemma lem4324151 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4324152 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (@lem4324151 (A -> Prop) t). Qed.
Lemma lem4324153 {A : Type'} : (term53 A) = True.
Proof. exact (@lem4324152 A True). Qed.
Lemma lem4324154 {A B : Type'} : (term58 A B) = True.
Proof. exact (TRANS (@lem4324149 A B) (@lem4324153 A)). Qed.
Lemma lem4324155 {A B : Type'} : True = (term58 A B).
Proof. exact (SYM (@lem4324154 A B)). Qed.
Lemma lem4324156 {A B : Type'} : term58 A B.
Proof. exact (EQ_MP (@lem4324155 A B) (@lem0)). Qed.
