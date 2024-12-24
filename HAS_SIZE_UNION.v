Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_UNION_term_abbrevs.
Require Import CARD_UNION_spec.
Require Import DISJOINT_spec.
Require Import FINITE_UNION_spec.
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
Lemma lem3867913 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3843862 A s). Qed.
Lemma lem3867914 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3867915 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3867914 A s) (@lem3867913 A s)). Qed.
Lemma lem3867916 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3867915 A s t). Qed.
Lemma lem3867917 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem3867918 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term3 A s t.
Proof. exact (EQ_MP (@lem3867917 A s t) (@lem3867916 A s t)). Qed.
Lemma lem3867919 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term4 A s t) : term4 A s t.
Proof. exact (h1). Qed.
Lemma lem3867920 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term4 A s t) : (term5 A s t) = (term6 A s t).
Proof. exact (@lem3867918 A s t (@lem3867919 A s t h1)). Qed.
Lemma lem3867926 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3196110 A s). Qed.
Lemma lem3867927 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem3867928 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem3867927 A s) (@lem3867926 A s)). Qed.
Lemma lem3867929 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem3867928 A s t). Qed.
Lemma lem3867930 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = ((@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A))).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem3867932 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (@lem3606772 A s). Qed.
Lemma lem3867933 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (eq_refl (term10 A s)). Qed.
Lemma lem3867934 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (EQ_MP (@lem3867933 A s) (@lem3867932 A s)). Qed.
Lemma lem3867935 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term12 A s t.
Proof. exact (@lem3867934 A s t). Qed.
Lemma lem3867936 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term12 A s t) = ((term13 A s t) = (term14 A s t)).
Proof. exact (eq_refl (term12 A s t)). Qed.
Lemma lem3867938 {_100044 : Type'} (s : _100044 -> Prop) : term15 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem3867939 {_100044 : Type'} (s : _100044 -> Prop) : (term15 _100044 s) = (term16 _100044 s).
Proof. exact (eq_refl (term15 _100044 s)). Qed.
Lemma lem3867940 {_100044 : Type'} (s : _100044 -> Prop) : term16 _100044 s.
Proof. exact (EQ_MP (@lem3867939 _100044 s) (@lem3867938 _100044 s)). Qed.
Lemma lem3867941 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term17 _100044 s n.
Proof. exact (@lem3867940 _100044 s n). Qed.
Lemma lem3867942 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term17 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term18 _100044 s n)).
Proof. exact (eq_refl (term17 _100044 s n)). Qed.
Lemma lem3867963 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term19 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3867964 (p : Prop) (q : Prop) (p' : Prop) : term20 p q p'.
Proof. exact (fun q' : Prop => @lem3867963 p q p' q'). Qed.
Lemma lem3867965 (p : Prop) (q : Prop) : term21 p q.
Proof. exact (fun p' : Prop => @lem3867964 p q p'). Qed.
Lemma lem3867966 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) : term22 _100197 s t m n.
Proof. exact (@lem3867965 (term23 _100197 m n s t) (term24 _100197 s t m n)). Qed.
Lemma lem3867967 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) (p' : Prop) : term25 _100197 s t m n p'.
Proof. exact (@lem3867966 _100197 s t m n p'). Qed.
Lemma lem3867968 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) (p' : Prop) : (term25 _100197 s t m n p') = (term26 _100197 s t m n p').
Proof. exact (eq_refl (term25 _100197 s t m n p')). Qed.
Lemma lem3867969 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) (p' : Prop) : term26 _100197 s t m n p'.
Proof. exact (EQ_MP (@lem3867968 _100197 s t m n p') (@lem3867967 _100197 s t m n p')). Qed.
Lemma lem3867970 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term27 _100197 s t m n p' q'.
Proof. exact (@lem3867969 _100197 s t m n p' q'). Qed.
Lemma lem3867971 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term27 _100197 s t m n p' q') = (term28 _100197 s t m n p' q').
Proof. exact (eq_refl (term27 _100197 s t m n p' q')). Qed.
Lemma lem3867972 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term28 _100197 s t m n p' q'.
Proof. exact (EQ_MP (@lem3867971 _100197 s t m n p' q') (@lem3867970 _100197 s t m n p' q')). Qed.
Lemma lem3867976 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term18 _100044 s n).
Proof. exact (EQ_MP (@lem3867942 _100044 s n) (@lem3867941 _100044 s n)). Qed.
Lemma lem3867977 {_100197 : Type'} (s : _100197 -> Prop) (n : nat) : (@HAS_SIZE _100197 s n) = (term18 _100197 s n).
Proof. exact (@lem3867976 _100197 s n). Qed.
Lemma lem3867978 {_100197 : Type'} (s : _100197 -> Prop) (m : nat) : (@HAS_SIZE _100197 s m) = (term18 _100197 s m).
Proof. exact (@lem3867977 _100197 s m). Qed.
Lemma lem3867983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3867984 {_100197 : Type'} (s : _100197 -> Prop) (m : nat) : (term29 _100197 s m) = (term30 _100197 s m).
Proof. exact (MK_COMB (@lem3867983) (@lem3867978 _100197 s m)). Qed.
Lemma lem3867992 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term18 _100044 s n).
Proof. exact (EQ_MP (@lem3867942 _100044 s n) (@lem3867941 _100044 s n)). Qed.
Lemma lem3867993 {_100197 : Type'} (s : _100197 -> Prop) (n : nat) : (@HAS_SIZE _100197 s n) = (term18 _100197 s n).
Proof. exact (@lem3867992 _100197 s n). Qed.
Lemma lem3867994 {_100197 : Type'} (t : _100197 -> Prop) (n : nat) : (@HAS_SIZE _100197 t n) = (term18 _100197 t n).
Proof. exact (@lem3867993 _100197 t n). Qed.
Lemma lem3867999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3868000 {_100197 : Type'} (t : _100197 -> Prop) (n : nat) : (term29 _100197 t n) = (term30 _100197 t n).
Proof. exact (MK_COMB (@lem3867999) (@lem3867994 _100197 t n)). Qed.
Lemma lem3868006 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3867930 A s t) (@lem3867929 A s t)). Qed.
Lemma lem3868007 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) : (@DISJOINT _100197 s t) = ((@INTER _100197 s t) = (@EMPTY _100197)).
Proof. exact (@lem3868006 _100197 s t). Qed.
Lemma lem3868010 {_100197 : Type'} (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) : (term31 _100197 n s t) = (term32 _100197 n s t).
Proof. exact (MK_COMB (@lem3868000 _100197 t n) (@lem3868007 _100197 s t)). Qed.
Lemma lem3868019 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) : (term23 _100197 m n s t) = (term33 _100197 m n s t).
Proof. exact (MK_COMB (@lem3867984 _100197 s m) (@lem3868010 _100197 n s t)). Qed.
Lemma lem3868034 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (q' : Prop) : term34 _100197 m n s t q'.
Proof. exact (@lem3867972 _100197 s t m n (term33 _100197 m n s t) q'). Qed.
Lemma lem3868035 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (q' : Prop) : term35 _100197 m n s t q'.
Proof. exact (@lem3868034 _100197 m n s t q' (@lem3868019 _100197 m n s t)). Qed.
Lemma lem3868036 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : term33 _100197 m n s t.
Proof. exact (h1). Qed.
Lemma lem3868037 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : term32 _100197 n s t.
Proof. exact (proj2 (@lem3868036 _100197 m n s t h1)). Qed.
Lemma lem3868039 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : term18 _100197 t n.
Proof. exact (proj1 (@lem3868037 _100197 m n s t h1)). Qed.
Lemma lem3868041 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : @FINITE _100197 t.
Proof. exact (proj1 (@lem3868039 _100197 m n s t h1)). Qed.
Lemma lem3868042 {_100197 : Type'} (t : _100197 -> Prop) : (@FINITE _100197 t) = ((@FINITE _100197 t) = True).
Proof. exact (@lem7 (@FINITE _100197 t)). Qed.
Lemma lem3868044 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : term18 _100197 s m.
Proof. exact (proj1 (@lem3868036 _100197 m n s t h1)). Qed.
Lemma lem3868046 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : @FINITE _100197 s.
Proof. exact (proj1 (@lem3868044 _100197 m n s t h1)). Qed.
Lemma lem3868047 {_100197 : Type'} (s : _100197 -> Prop) : (@FINITE _100197 s) = ((@FINITE _100197 s) = True).
Proof. exact (@lem7 (@FINITE _100197 s)). Qed.
Lemma lem3868050 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term18 _100044 s n).
Proof. exact (EQ_MP (@lem3867942 _100044 s n) (@lem3867941 _100044 s n)). Qed.
Lemma lem3868051 {_100197 : Type'} (s : _100197 -> Prop) (n : nat) : (@HAS_SIZE _100197 s n) = (term18 _100197 s n).
Proof. exact (@lem3868050 _100197 s n). Qed.
Lemma lem3868052 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) : (term24 _100197 s t m n) = (term36 _100197 s t m n).
Proof. exact (@lem3868051 _100197 (@UNION _100197 s t) (Nat.add m n)). Qed.
Lemma lem3868056 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term13 A s t) = (term14 A s t).
Proof. exact (EQ_MP (@lem3867936 A s t) (@lem3867935 A s t)). Qed.
Lemma lem3868057 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) : (term13 _100197 s t) = (term14 _100197 s t).
Proof. exact (@lem3868056 _100197 s t). Qed.
Lemma lem3868061 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (@FINITE _100197 s) = True.
Proof. exact (EQ_MP (@lem3868047 _100197 s) (@lem3868046 _100197 m n s t h1)). Qed.
Lemma lem3868062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3868063 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term37 _100197 s) = (and True).
Proof. exact (MK_COMB (@lem3868062) (@lem3868061 _100197 m n s t h1)). Qed.
Lemma lem3868065 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (@FINITE _100197 t) = True.
Proof. exact (EQ_MP (@lem3868042 _100197 t) (@lem3868041 _100197 m n s t h1)). Qed.
Lemma lem3868066 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term14 _100197 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem3868063 _100197 m n s t h1) (@lem3868065 _100197 m n s t h1)). Qed.
Lemma lem3868068 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3868069 : (True /\ True) = True.
Proof. exact (@lem3868068 True). Qed.
Lemma lem3868070 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term14 _100197 s t) = True.
Proof. exact (TRANS (@lem3868066 _100197 m n s t h1) (@lem3868069)). Qed.
Lemma lem3868071 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term13 _100197 s t) = True.
Proof. exact (TRANS (@lem3868057 _100197 s t) (@lem3868070 _100197 m n s t h1)). Qed.
Lemma lem3868072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3868073 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term38 _100197 s t) = (and True).
Proof. exact (MK_COMB (@lem3868072) (@lem3868071 _100197 m n s t h1)). Qed.
Lemma lem3868077 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term3 A s t.
Proof. exact (fun h0 : term4 A s t => @lem3867920 A s t h0). Qed.
Lemma lem3868078 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) : term3 _100197 s t.
Proof. exact (@lem3868077 _100197 s t). Qed.
Lemma lem3868082 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (@FINITE _100197 s) = True.
Proof. exact (EQ_MP (@lem3868047 _100197 s) (@lem3868046 _100197 m n s t h1)). Qed.
Lemma lem3868083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3868084 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term37 _100197 s) = (and True).
Proof. exact (MK_COMB (@lem3868083) (@lem3868082 _100197 m n s t h1)). Qed.
Lemma lem3868088 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (@FINITE _100197 t) = True.
Proof. exact (EQ_MP (@lem3868042 _100197 t) (@lem3868041 _100197 m n s t h1)). Qed.
Lemma lem3868089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3868090 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term37 _100197 t) = (and True).
Proof. exact (MK_COMB (@lem3868089) (@lem3868088 _100197 m n s t h1)). Qed.
Lemma lem3868094 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (@INTER _100197 s t) = (@EMPTY _100197).
Proof. exact (proj2 (@lem3868037 _100197 m n s t h1)). Qed.
Lemma lem3868095 {_100197 : Type'} : (@eq (_100197 -> Prop)) = (@eq (_100197 -> Prop)).
Proof. exact (eq_refl (@eq (_100197 -> Prop))). Qed.
Lemma lem3868096 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term39 _100197 s t) = (@eq (_100197 -> Prop) (@EMPTY _100197)).
Proof. exact (MK_COMB (@lem3868095 _100197) (@lem3868094 _100197 m n s t h1)). Qed.
Lemma lem3868097 {_100197 : Type'} : (@EMPTY _100197) = (@EMPTY _100197).
Proof. exact (eq_refl (@EMPTY _100197)). Qed.
Lemma lem3868098 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : ((@INTER _100197 s t) = (@EMPTY _100197)) = ((@EMPTY _100197) = (@EMPTY _100197)).
Proof. exact (MK_COMB (@lem3868096 _100197 m n s t h1) (@lem3868097 _100197)). Qed.
Lemma lem3868100 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3868101 {_100197 : Type'} (x : _100197 -> Prop) : (x = x) = True.
Proof. exact (@lem3868100 (_100197 -> Prop) x). Qed.
Lemma lem3868102 {_100197 : Type'} : ((@EMPTY _100197) = (@EMPTY _100197)) = True.
Proof. exact (@lem3868101 _100197 (@EMPTY _100197)). Qed.
Lemma lem3868103 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : ((@INTER _100197 s t) = (@EMPTY _100197)) = True.
Proof. exact (TRANS (@lem3868098 _100197 m n s t h1) (@lem3868102 _100197)). Qed.
Lemma lem3868104 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term40 _100197 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem3868090 _100197 m n s t h1) (@lem3868103 _100197 m n s t h1)). Qed.
Lemma lem3868106 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3868107 : (True /\ True) = True.
Proof. exact (@lem3868106 True). Qed.
Lemma lem3868108 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term40 _100197 s t) = True.
Proof. exact (TRANS (@lem3868104 _100197 m n s t h1) (@lem3868107)). Qed.
Lemma lem3868109 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term4 _100197 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem3868084 _100197 m n s t h1) (@lem3868108 _100197 m n s t h1)). Qed.
Lemma lem3868111 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3868112 : (True /\ True) = True.
Proof. exact (@lem3868111 True). Qed.
Lemma lem3868113 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term4 _100197 s t) = True.
Proof. exact (TRANS (@lem3868109 _100197 m n s t h1) (@lem3868112)). Qed.
Lemma lem3868114 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : True = (term4 _100197 s t).
Proof. exact (SYM (@lem3868113 _100197 m n s t h1)). Qed.
Lemma lem3868115 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : term4 _100197 s t.
Proof. exact (EQ_MP (@lem3868114 _100197 m n s t h1) (@lem0)). Qed.
Lemma lem3868116 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term5 _100197 s t) = (term6 _100197 s t).
Proof. exact (@lem3868078 _100197 s t (@lem3868115 _100197 m n s t h1)). Qed.
Lemma lem3868118 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (@CARD _100197 s) = m.
Proof. exact (proj2 (@lem3868044 _100197 m n s t h1)). Qed.
Lemma lem3868119 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem3868120 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term41 _100197 s) = (Nat.add m).
Proof. exact (MK_COMB (@lem3868119) (@lem3868118 _100197 m n s t h1)). Qed.
Lemma lem3868122 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (@CARD _100197 t) = n.
Proof. exact (proj2 (@lem3868039 _100197 m n s t h1)). Qed.
Lemma lem3868123 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term6 _100197 s t) = (Nat.add m n).
Proof. exact (MK_COMB (@lem3868120 _100197 m n s t h1) (@lem3868122 _100197 m n s t h1)). Qed.
Lemma lem3868124 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term5 _100197 s t) = (Nat.add m n).
Proof. exact (TRANS (@lem3868116 _100197 m n s t h1) (@lem3868123 _100197 m n s t h1)). Qed.
Lemma lem3868125 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3868126 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term42 _100197 s t) = (term43 m n).
Proof. exact (MK_COMB (@lem3868125) (@lem3868124 _100197 m n s t h1)). Qed.
Lemma lem3868127 (m : nat) (n : nat) : (Nat.add m n) = (Nat.add m n).
Proof. exact (eq_refl (Nat.add m n)). Qed.
Lemma lem3868128 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : ((term5 _100197 s t) = (Nat.add m n)) = ((Nat.add m n) = (Nat.add m n)).
Proof. exact (MK_COMB (@lem3868126 _100197 m n s t h1) (@lem3868127 m n)). Qed.
Lemma lem3868130 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3868131 (x : nat) : (x = x) = True.
Proof. exact (@lem3868130 nat x). Qed.
Lemma lem3868132 (m : nat) (n : nat) : ((Nat.add m n) = (Nat.add m n)) = True.
Proof. exact (@lem3868131 (Nat.add m n)). Qed.
Lemma lem3868133 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : ((term5 _100197 s t) = (Nat.add m n)) = True.
Proof. exact (TRANS (@lem3868128 _100197 m n s t h1) (@lem3868132 m n)). Qed.
Lemma lem3868134 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term36 _100197 s t m n) = (True /\ True).
Proof. exact (MK_COMB (@lem3868073 _100197 m n s t h1) (@lem3868133 _100197 m n s t h1)). Qed.
Lemma lem3868136 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3868137 : (True /\ True) = True.
Proof. exact (@lem3868136 True). Qed.
Lemma lem3868138 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term36 _100197 s t m n) = True.
Proof. exact (TRANS (@lem3868134 _100197 m n s t h1) (@lem3868137)). Qed.
Lemma lem3868139 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term33 _100197 m n s t) : (term24 _100197 s t m n) = True.
Proof. exact (TRANS (@lem3868052 _100197 s t m n) (@lem3868138 _100197 m n s t h1)). Qed.
Lemma lem3868140 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) : term44 _100197 s t m n.
Proof. exact (fun h0 : term33 _100197 m n s t => @lem3868139 _100197 m n s t h0). Qed.
Lemma lem3868141 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) : term45 _100197 m n s t.
Proof. exact (@lem3868035 _100197 m n s t True). Qed.
Lemma lem3868142 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) : (term46 _100197 s t m n) = (term47 _100197 m n s t).
Proof. exact (@lem3868141 _100197 m n s t (@lem3868140 _100197 s t m n)). Qed.
Lemma lem3868144 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3868145 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) : (term47 _100197 m n s t) = True.
Proof. exact (@lem3868144 (term33 _100197 m n s t)). Qed.
Lemma lem3868146 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) : (term46 _100197 s t m n) = True.
Proof. exact (TRANS (@lem3868142 _100197 m n s t) (@lem3868145 _100197 m n s t)). Qed.
Lemma lem3868147 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) : (term48 _100197 s t m) = term49.
Proof. exact (fun_ext (fun n : nat => @lem3868146 _100197 s t m n)). Qed.
Lemma lem3868148 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3868149 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) : (term50 _100197 s t m) = term51.
Proof. exact (MK_COMB (@lem3868148) (@lem3868147 _100197 s t m)). Qed.
Lemma lem3868151 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3868152 (t : Prop) : (term53 t) = t.
Proof. exact (@lem3868151 nat t). Qed.
Lemma lem3868153 : term51 = True.
Proof. exact (@lem3868152 True). Qed.
Lemma lem3868154 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) : (term50 _100197 s t m) = True.
Proof. exact (TRANS (@lem3868149 _100197 s t m) (@lem3868153)). Qed.
Lemma lem3868155 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) : (term54 _100197 s t) = term49.
Proof. exact (fun_ext (fun m : nat => @lem3868154 _100197 s t m)). Qed.
Lemma lem3868156 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3868157 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) : (term55 _100197 s t) = term51.
Proof. exact (MK_COMB (@lem3868156) (@lem3868155 _100197 s t)). Qed.
Lemma lem3868159 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3868160 (t : Prop) : (term53 t) = t.
Proof. exact (@lem3868159 nat t). Qed.
Lemma lem3868161 : term51 = True.
Proof. exact (@lem3868160 True). Qed.
Lemma lem3868162 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) : (term55 _100197 s t) = True.
Proof. exact (TRANS (@lem3868157 _100197 s t) (@lem3868161)). Qed.
Lemma lem3868163 {_100197 : Type'} (s : _100197 -> Prop) : (term56 _100197 s) = (term57 _100197).
Proof. exact (fun_ext (fun t : _100197 -> Prop => @lem3868162 _100197 s t)). Qed.
Lemma lem3868164 {_100197 : Type'} : (@all (_100197 -> Prop)) = (@all (_100197 -> Prop)).
Proof. exact (eq_refl (@all (_100197 -> Prop))). Qed.
Lemma lem3868165 {_100197 : Type'} (s : _100197 -> Prop) : (term58 _100197 s) = (term59 _100197).
Proof. exact (MK_COMB (@lem3868164 _100197) (@lem3868163 _100197 s)). Qed.
Lemma lem3868167 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3868168 {_100197 : Type'} (t : Prop) : (term60 _100197 t) = t.
Proof. exact (@lem3868167 (_100197 -> Prop) t). Qed.
Lemma lem3868169 {_100197 : Type'} : (term59 _100197) = True.
Proof. exact (@lem3868168 _100197 True). Qed.
Lemma lem3868170 {_100197 : Type'} (s : _100197 -> Prop) : (term58 _100197 s) = True.
Proof. exact (TRANS (@lem3868165 _100197 s) (@lem3868169 _100197)). Qed.
Lemma lem3868171 {_100197 : Type'} : (term61 _100197) = (term57 _100197).
Proof. exact (fun_ext (fun s : _100197 -> Prop => @lem3868170 _100197 s)). Qed.
Lemma lem3868172 {_100197 : Type'} : (@all (_100197 -> Prop)) = (@all (_100197 -> Prop)).
Proof. exact (eq_refl (@all (_100197 -> Prop))). Qed.
Lemma lem3868173 {_100197 : Type'} : (term62 _100197) = (term59 _100197).
Proof. exact (MK_COMB (@lem3868172 _100197) (@lem3868171 _100197)). Qed.
Lemma lem3868175 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3868176 {_100197 : Type'} (t : Prop) : (term60 _100197 t) = t.
Proof. exact (@lem3868175 (_100197 -> Prop) t). Qed.
Lemma lem3868177 {_100197 : Type'} : (term59 _100197) = True.
Proof. exact (@lem3868176 _100197 True). Qed.
Lemma lem3868178 {_100197 : Type'} : (term62 _100197) = True.
Proof. exact (TRANS (@lem3868173 _100197) (@lem3868177 _100197)). Qed.
Lemma lem3868179 {_100197 : Type'} : True = (term62 _100197).
Proof. exact (SYM (@lem3868178 _100197)). Qed.
Lemma lem3868180 {_100197 : Type'} : term62 _100197.
Proof. exact (EQ_MP (@lem3868179 _100197) (@lem0)). Qed.
