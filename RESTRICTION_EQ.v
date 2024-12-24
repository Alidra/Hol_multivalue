Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_EQ_term_abbrevs.
Require Import RESTRICTION_DEFINED_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4386973 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4386843 A B s). Qed.
Lemma lem4386974 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4386975 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4386974 A B s) (@lem4386973 A B s)). Qed.
Lemma lem4386976 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem4386975 A B s f). Qed.
Lemma lem4386977 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B s f) = (term3 A B s f).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem4386978 {A B : Type'} (s : A -> Prop) (f : A -> B) : term3 A B s f.
Proof. exact (EQ_MP (@lem4386977 A B s f) (@lem4386976 A B s f)). Qed.
Lemma lem4386979 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term4 A B s f x.
Proof. exact (@lem4386978 A B s f x). Qed.
Lemma lem4386980 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term4 A B s f x) = (term5 A B s f x).
Proof. exact (eq_refl (term4 A B s f x)). Qed.
Lemma lem4386981 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term5 A B s f x.
Proof. exact (EQ_MP (@lem4386980 A B s f x) (@lem4386979 A B s f x)). Qed.
Lemma lem4386982 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem4386983 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@RESTRICTION A B s f x) = (f x).
Proof. exact (@lem4386981 A B s f x (@lem4386982 A x s h1)). Qed.
Lemma lem4387008 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term6 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4387009 (p : Prop) (q : Prop) (p' : Prop) : term7 p q p'.
Proof. exact (fun q' : Prop => @lem4387008 p q p' q'). Qed.
Lemma lem4387010 (p : Prop) (q : Prop) : term8 p q.
Proof. exact (fun p' : Prop => @lem4387009 p q p'). Qed.
Lemma lem4387011 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : term9 A B s f x y.
Proof. exact (@lem4387010 (term10 A B s f x y) ((@RESTRICTION A B s f x) = y)). Qed.
Lemma lem4387012 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (p' : Prop) : term11 A B s f x y p'.
Proof. exact (@lem4387011 A B s f x y p'). Qed.
Lemma lem4387013 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (p' : Prop) : (term11 A B s f x y p') = (term12 A B s f x y p').
Proof. exact (eq_refl (term11 A B s f x y p')). Qed.
Lemma lem4387014 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (p' : Prop) : term12 A B s f x y p'.
Proof. exact (EQ_MP (@lem4387013 A B s f x y p') (@lem4387012 A B s f x y p')). Qed.
Lemma lem4387015 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (p' : Prop) (q' : Prop) : term13 A B s f x y p' q'.
Proof. exact (@lem4387014 A B s f x y p' q'). Qed.
Lemma lem4387016 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (p' : Prop) (q' : Prop) : (term13 A B s f x y p' q') = (term14 A B s f x y p' q').
Proof. exact (eq_refl (term13 A B s f x y p' q')). Qed.
Lemma lem4387017 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (p' : Prop) (q' : Prop) : term14 A B s f x y p' q'.
Proof. exact (EQ_MP (@lem4387016 A B s f x y p' q') (@lem4387015 A B s f x y p' q')). Qed.
Lemma lem4387022 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term10 A B s f x y) = (term10 A B s f x y).
Proof. exact (eq_refl (term10 A B s f x y)). Qed.
Lemma lem4387023 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (q' : Prop) : term15 A B s f x y q'.
Proof. exact (@lem4387017 A B s f x y (term10 A B s f x y) q'). Qed.
Lemma lem4387024 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (q' : Prop) : term16 A B s f x y q'.
Proof. exact (@lem4387023 A B s f x y q' (@lem4387022 A B s f x y)). Qed.
Lemma lem4387025 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term10 A B s f x y) : term10 A B s f x y.
Proof. exact (h1). Qed.
Lemma lem4387027 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term10 A B s f x y) : @IN A x s.
Proof. exact (proj1 (@lem4387025 A B s f x y h1)). Qed.
Lemma lem4387028 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem4387033 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term5 A B s f x.
Proof. exact (fun h0 : @IN A x s => @lem4386983 A B f x s h0). Qed.
Lemma lem4387034 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term5 A B s f x.
Proof. exact (@lem4387033 A B s f x). Qed.
Lemma lem4387036 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term10 A B s f x y) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem4387028 A x s) (@lem4387027 A B s f x y h1)). Qed.
Lemma lem4387037 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term10 A B s f x y) : True = (@IN A x s).
Proof. exact (SYM (@lem4387036 A B s f x y h1)). Qed.
Lemma lem4387038 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term10 A B s f x y) : @IN A x s.
Proof. exact (EQ_MP (@lem4387037 A B s f x y h1) (@lem0)). Qed.
Lemma lem4387039 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term10 A B s f x y) : (@RESTRICTION A B s f x) = (f x).
Proof. exact (@lem4387034 A B s f x (@lem4387038 A B s f x y h1)). Qed.
Lemma lem4387041 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term10 A B s f x y) : (f x) = y.
Proof. exact (proj2 (@lem4387025 A B s f x y h1)). Qed.
Lemma lem4387042 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term10 A B s f x y) : (@RESTRICTION A B s f x) = y.
Proof. exact (TRANS (@lem4387039 A B s f x y h1) (@lem4387041 A B s f x y h1)). Qed.
Lemma lem4387043 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4387044 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term10 A B s f x y) : (term17 A B s f x) = (@eq B y).
Proof. exact (MK_COMB (@lem4387043 B) (@lem4387042 A B s f x y h1)). Qed.
Lemma lem4387045 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4387046 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term10 A B s f x y) : ((@RESTRICTION A B s f x) = y) = (y = y).
Proof. exact (MK_COMB (@lem4387044 A B s f x y h1) (@lem4387045 B y)). Qed.
Lemma lem4387048 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4387049 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4387048 B x). Qed.
Lemma lem4387050 {B : Type'} (y : B) : (y = y) = True.
Proof. exact (@lem4387049 B y). Qed.
Lemma lem4387051 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term10 A B s f x y) : ((@RESTRICTION A B s f x) = y) = True.
Proof. exact (TRANS (@lem4387046 A B s f x y h1) (@lem4387050 B y)). Qed.
Lemma lem4387052 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : term18 A B s f x y.
Proof. exact (fun h0 : term10 A B s f x y => @lem4387051 A B s f x y h0). Qed.
Lemma lem4387053 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : term19 A B s f x y.
Proof. exact (@lem4387024 A B s f x y True). Qed.
Lemma lem4387054 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term20 A B s f x y) = (term21 A B s f x y).
Proof. exact (@lem4387053 A B s f x y (@lem4387052 A B s f x y)). Qed.
Lemma lem4387056 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4387057 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term21 A B s f x y) = True.
Proof. exact (@lem4387056 (term10 A B s f x y)). Qed.
Lemma lem4387058 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term20 A B s f x y) = True.
Proof. exact (TRANS (@lem4387054 A B s f x y) (@lem4387057 A B s f x y)). Qed.
Lemma lem4387059 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term22 A B s f x) = (term23 B).
Proof. exact (fun_ext (fun y : B => @lem4387058 A B s f x y)). Qed.
Lemma lem4387060 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4387061 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term24 A B s f x) = (term25 B).
Proof. exact (MK_COMB (@lem4387060 B) (@lem4387059 A B s f x)). Qed.
Lemma lem4387063 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4387064 {B : Type'} (t : Prop) : (term26 B t) = t.
Proof. exact (@lem4387063 B t). Qed.
Lemma lem4387065 {B : Type'} : (term25 B) = True.
Proof. exact (@lem4387064 B True). Qed.
Lemma lem4387066 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term24 A B s f x) = True.
Proof. exact (TRANS (@lem4387061 A B s f x) (@lem4387065 B)). Qed.
Lemma lem4387067 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term27 A B s f) = (term23 A).
Proof. exact (fun_ext (fun x : A => @lem4387066 A B s f x)). Qed.
Lemma lem4387068 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4387069 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term28 A B s f) = (term25 A).
Proof. exact (MK_COMB (@lem4387068 A) (@lem4387067 A B s f)). Qed.
Lemma lem4387071 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4387072 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (@lem4387071 A t). Qed.
Lemma lem4387073 {A : Type'} : (term25 A) = True.
Proof. exact (@lem4387072 A True). Qed.
Lemma lem4387074 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term28 A B s f) = True.
Proof. exact (TRANS (@lem4387069 A B s f) (@lem4387073 A)). Qed.
Lemma lem4387075 {A B : Type'} (s : A -> Prop) : (term29 A B s) = (term30 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4387074 A B s f)). Qed.
Lemma lem4387076 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4387077 {A B : Type'} (s : A -> Prop) : (term31 A B s) = (term32 A B).
Proof. exact (MK_COMB (@lem4387076 A B) (@lem4387075 A B s)). Qed.
Lemma lem4387079 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4387080 {A B : Type'} (t : Prop) : (term33 A B t) = t.
Proof. exact (@lem4387079 (A -> B) t). Qed.
Lemma lem4387081 {A B : Type'} : (term32 A B) = True.
Proof. exact (@lem4387080 A B True). Qed.
Lemma lem4387082 {A B : Type'} (s : A -> Prop) : (term31 A B s) = True.
Proof. exact (TRANS (@lem4387077 A B s) (@lem4387081 A B)). Qed.
Lemma lem4387083 {A B : Type'} : (term34 A B) = (term35 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4387082 A B s)). Qed.
Lemma lem4387084 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4387085 {A B : Type'} : (term36 A B) = (term37 A).
Proof. exact (MK_COMB (@lem4387084 A) (@lem4387083 A B)). Qed.
Lemma lem4387087 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4387088 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (@lem4387087 (A -> Prop) t). Qed.
Lemma lem4387089 {A : Type'} : (term37 A) = True.
Proof. exact (@lem4387088 A True). Qed.
Lemma lem4387090 {A B : Type'} : (term36 A B) = True.
Proof. exact (TRANS (@lem4387085 A B) (@lem4387089 A)). Qed.
Lemma lem4387091 {A B : Type'} : True = (term36 A B).
Proof. exact (SYM (@lem4387090 A B)). Qed.
Lemma lem4387092 {A B : Type'} : term36 A B.
Proof. exact (EQ_MP (@lem4387091 A B) (@lem0)). Qed.
