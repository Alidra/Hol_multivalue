Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm309993_term_abbrevs.
Require Import thm75635_spec.
Lemma lem309934 {A : Type'} (s : nat -> A) (a : A) (h1 : (term0 A s) = a) : (term0 A s) = a.
Proof. exact (h1). Qed.
Lemma lem309935 {A : Type'} (f : A -> A) (s : nat -> A) (h1 : term1 A f s) : term1 A f s.
Proof. exact (h1). Qed.
Lemma lem309936 {A : Type'} (n : nat) (f : A -> A) (s : nat -> A) (h1 : term1 A f s) : term2 A f s n.
Proof. exact (@lem309935 A f s h1 n). Qed.
Lemma lem309937 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : (term2 A f s n) = ((term3 A s n) = (term4 A f s n)).
Proof. exact (eq_refl (term2 A f s n)). Qed.
Lemma lem309938 {A : Type'} (n : nat) (f : A -> A) (s : nat -> A) (h1 : term1 A f s) : (term3 A s n) = (term4 A f s n).
Proof. exact (EQ_MP (@lem309937 A f s n) (@lem309936 A n f s h1)). Qed.
Lemma lem309939 {A : Type'} (f : A -> A) (s : nat -> A) (h1 : term1 A f s) : term1 A f s.
Proof. exact (fun n : nat => @lem309938 A n f s h1). Qed.
Lemma lem309940 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : term5 A a f s.
Proof. exact (h1). Qed.
Lemma lem309941 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : term1 A f s.
Proof. exact (proj2 (@lem309940 A a f s h1)). Qed.
Lemma lem309942 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : (term0 A s) = a.
Proof. exact (proj1 (@lem309940 A a f s h1)). Qed.
Lemma lem309943 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : ((term0 A s) = a) = ((term0 A s) = a).
Proof. exact (prop_ext (fun h2 : (term0 A s) = a => @lem309934 A s a h2) (fun h2 : (term0 A s) = a => @lem309942 A a f s h1)). Qed.
Lemma lem309944 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : (term0 A s) = a.
Proof. exact (EQ_MP (@lem309943 A a f s h1) (@lem309942 A a f s h1)). Qed.
Lemma lem309945 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : (term1 A f s) = (term1 A f s).
Proof. exact (prop_ext (fun h2 : term1 A f s => @lem309939 A f s h2) (fun h2 : term1 A f s => @lem309941 A a f s h1)). Qed.
Lemma lem309946 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : term1 A f s.
Proof. exact (EQ_MP (@lem309945 A a f s h1) (@lem309941 A a f s h1)). Qed.
Lemma lem309947 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : term5 A a f s.
Proof. exact (conj (@lem309944 A a f s h1) (@lem309946 A a f s h1)). Qed.
Lemma lem309948 {A : Type'} (e : A) : term6 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem309949 {A : Type'} (e : A) : (term6 A e) = (term7 A e).
Proof. exact (eq_refl (term6 A e)). Qed.
Lemma lem309950 {A : Type'} (e : A) : term7 A e.
Proof. exact (EQ_MP (@lem309949 A e) (@lem309948 A e)). Qed.
Lemma lem309951 {A : Type'} (e : A) (f : type1423 A) : term8 A e f.
Proof. exact (@lem309950 A e f). Qed.
Lemma lem309952 {A : Type'} (e : A) (f : type1423 A) : (term8 A e f) = (term9 A e f).
Proof. exact (eq_refl (term8 A e f)). Qed.
Lemma lem309953 {A : Type'} (e : A) (f : type1423 A) : term9 A e f.
Proof. exact (EQ_MP (@lem309952 A e f) (@lem309951 A e f)). Qed.
Lemma lem309954 {A : Type'} (e : A) (f : type1423 A) : term9 A e f.
Proof. exact (@lem309953 A e f). Qed.
Lemma lem309955 {A : Type'} (a : A) (f : A -> A) : term10 A a f.
Proof. exact (@lem309954 A a (term11 A f)). Qed.
Lemma lem309956 {A : Type'} (f : A -> A) (fn : nat -> A) (n : nat) : (term12 A f fn n) = (term13 A f fn n).
Proof. exact (eq_refl (term12 A f fn n)). Qed.
Lemma lem309957 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem309958 {A : Type'} (f : A -> A) (fn : nat -> A) (n : nat) : (term14 A f fn n) = (term15 A f fn n).
Proof. exact (MK_COMB (@lem309956 A f fn n) (@lem309957 n)). Qed.
Lemma lem309959 {A : Type'} (f : A -> A) (fn : nat -> A) (n : nat) : (term15 A f fn n) = (term4 A f fn n).
Proof. exact (eq_refl (term15 A f fn n)). Qed.
Lemma lem309960 {A : Type'} (f : A -> A) (fn : nat -> A) (n : nat) : (term14 A f fn n) = (term4 A f fn n).
Proof. exact (TRANS (@lem309958 A f fn n) (@lem309959 A f fn n)). Qed.
Lemma lem309961 {A : Type'} (fn : nat -> A) (n : nat) : (term16 A fn n) = (term16 A fn n).
Proof. exact (eq_refl (term16 A fn n)). Qed.
Lemma lem309962 {A : Type'} (f : A -> A) (fn : nat -> A) (n : nat) : ((term3 A fn n) = (term14 A f fn n)) = ((term3 A fn n) = (term4 A f fn n)).
Proof. exact (MK_COMB (@lem309961 A fn n) (@lem309960 A f fn n)). Qed.
Lemma lem309963 {A : Type'} (f : A -> A) (fn : nat -> A) : (term17 A f fn) = (term18 A f fn).
Proof. exact (fun_ext (fun n : nat => @lem309962 A f fn n)). Qed.
Lemma lem309964 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem309965 {A : Type'} (f : A -> A) (fn : nat -> A) : (term19 A f fn) = (term1 A f fn).
Proof. exact (MK_COMB (@lem309964) (@lem309963 A f fn)). Qed.
Lemma lem309966 {A : Type'} (fn : nat -> A) (a : A) : (term20 A fn a) = (term20 A fn a).
Proof. exact (eq_refl (term20 A fn a)). Qed.
Lemma lem309967 {A : Type'} (a : A) (f : A -> A) (fn : nat -> A) : (term21 A a f fn) = (term5 A a f fn).
Proof. exact (MK_COMB (@lem309966 A fn a) (@lem309965 A f fn)). Qed.
Lemma lem309968 {A : Type'} (a : A) (f : A -> A) : (term22 A a f) = (term23 A a f).
Proof. exact (fun_ext (fun fn : nat -> A => @lem309967 A a f fn)). Qed.
Lemma lem309969 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem309970 {A : Type'} (a : A) (f : A -> A) : (term10 A a f) = (term24 A a f).
Proof. exact (MK_COMB (@lem309969 A) (@lem309968 A a f)). Qed.
Lemma lem309971 {A : Type'} (a : A) (f : A -> A) : term24 A a f.
Proof. exact (EQ_MP (@lem309970 A a f) (@lem309955 A a f)). Qed.
Lemma lem309972 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : term5 A a f s.
Proof. exact (h1). Qed.
Lemma lem309973 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : term1 A f s.
Proof. exact (proj2 (@lem309972 A a f s h1)). Qed.
Lemma lem309974 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : (term0 A s) = a.
Proof. exact (proj1 (@lem309972 A a f s h1)). Qed.
Lemma lem309975 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : term5 A a f s.
Proof. exact (conj (@lem309974 A a f s h1) (@lem309973 A a f s h1)). Qed.
Lemma lem309976 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : term24 A a f.
Proof. exact (ex_intro (term23 A a f) s (@lem309975 A a f s h1)). Qed.
Lemma lem309977 {A : Type'} (a : A) (f : A -> A) (h1 : term24 A a f) : term24 A a f.
Proof. exact (h1). Qed.
Lemma lem309978 {A : Type'} (a : A) (f : A -> A) (h1 : term24 A a f) : term24 A a f.
Proof. exact (ex_elim (@lem309977 A a f h1) (fun s : nat -> A => fun h0 : term23 A a f s => @lem309976 A a f s h0)). Qed.
Lemma lem309979 {A : Type'} (a : A) (f : A -> A) : (term24 A a f) = (term24 A a f).
Proof. exact (prop_ext (fun h1 : term24 A a f => @lem309978 A a f h1) (fun h1 : term24 A a f => @lem309971 A a f)). Qed.
Lemma lem309980 {A : Type'} (a : A) (f : A -> A) : term24 A a f.
Proof. exact (EQ_MP (@lem309979 A a f) (@lem309971 A a f)). Qed.
Lemma lem309981 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : term24 A a f.
Proof. exact (ex_intro (term23 A a f) s (@lem309947 A a f s h1)). Qed.
Lemma lem309982 {A : Type'} (a : A) (f : A -> A) (h1 : term24 A a f) : term24 A a f.
Proof. exact (h1). Qed.
Lemma lem309983 {A : Type'} (a : A) (f : A -> A) (h1 : term24 A a f) : term24 A a f.
Proof. exact (ex_elim (@lem309982 A a f h1) (fun s : nat -> A => fun h0 : term23 A a f s => @lem309981 A a f s h0)). Qed.
Lemma lem309984 {A : Type'} (a : A) (f : A -> A) : (term24 A a f) = (term24 A a f).
Proof. exact (prop_ext (fun h1 : term24 A a f => @lem309983 A a f h1) (fun h1 : term24 A a f => @lem309980 A a f)). Qed.
Lemma lem309985 {A : Type'} (a : A) (f : A -> A) : term24 A a f.
Proof. exact (EQ_MP (@lem309984 A a f) (@lem309980 A a f)). Qed.
Lemma lem309988 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : term5 A a f s.
Proof. exact (h1). Qed.
Lemma lem309989 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term5 A a f s) : term24 A a f.
Proof. exact (ex_intro (term23 A a f) s (@lem309988 A a f s h1)). Qed.
Lemma lem309990 {A : Type'} (a : A) (f : A -> A) (h1 : term24 A a f) : term24 A a f.
Proof. exact (h1). Qed.
Lemma lem309991 {A : Type'} (a : A) (f : A -> A) (h1 : term24 A a f) : term24 A a f.
Proof. exact (ex_elim (@lem309990 A a f h1) (fun s : nat -> A => fun h0 : term23 A a f s => @lem309989 A a f s h0)). Qed.
Lemma lem309992 {A : Type'} (a : A) (f : A -> A) : (term24 A a f) = (term24 A a f).
Proof. exact (prop_ext (fun h1 : term24 A a f => @lem309991 A a f h1) (fun h1 : term24 A a f => @lem309985 A a f)). Qed.
Lemma lem309993 {A : Type'} (a : A) (f : A -> A) : term24 A a f.
Proof. exact (EQ_MP (@lem309992 A a f) (@lem309985 A a f)). Qed.
