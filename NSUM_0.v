Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_0_term_abbrevs.
Require Import NSUM_EQ_0_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Lemma lem6930974 {A : Type'} (f : A -> nat) : term0 A f.
Proof. exact (@lem6930973 A f). Qed.
Lemma lem6930975 {A : Type'} (f : A -> nat) : (term0 A f) = (term1 A f).
Proof. exact (eq_refl (term0 A f)). Qed.
Lemma lem6930976 {A : Type'} (f : A -> nat) : term1 A f.
Proof. exact (EQ_MP (@lem6930975 A f) (@lem6930974 A f)). Qed.
Lemma lem6930977 {A : Type'} (f : A -> nat) (s : A -> Prop) : term2 A f s.
Proof. exact (@lem6930976 A f s). Qed.
Lemma lem6930978 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term2 A f s) = (term3 A s f).
Proof. exact (eq_refl (term2 A f s)). Qed.
Lemma lem6930979 {A : Type'} (s : A -> Prop) (f : A -> nat) : term3 A s f.
Proof. exact (EQ_MP (@lem6930978 A s f) (@lem6930977 A f s)). Qed.
Lemma lem6930980 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term4 A s f) : term4 A s f.
Proof. exact (h1). Qed.
Lemma lem6930981 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term4 A s f) : (@nsum A s f) = (NUMERAL 0).
Proof. exact (@lem6930979 A s f (@lem6930980 A s f h1)). Qed.
Lemma lem6930994 {A : Type'} (s : A -> Prop) (f : A -> nat) : term3 A s f.
Proof. exact (fun h0 : term4 A s f => @lem6930981 A s f h0). Qed.
Lemma lem6930995 {A : Type'} (s : A -> Prop) (f : A -> nat) : term3 A s f.
Proof. exact (@lem6930994 A s f). Qed.
Lemma lem6930996 {A : Type'} (s : A -> Prop) : term5 A s.
Proof. exact (@lem6930995 A s (term6 A)). Qed.
Lemma lem6931004 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term7 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6931005 (p : Prop) (q : Prop) (p' : Prop) : term8 p q p'.
Proof. exact (fun q' : Prop => @lem6931004 p q p' q'). Qed.
Lemma lem6931006 (p : Prop) (q : Prop) : term9 p q.
Proof. exact (fun p' : Prop => @lem6931005 p q p'). Qed.
Lemma lem6931007 {A : Type'} (s : A -> Prop) (x : A) : term10 A s x.
Proof. exact (@lem6931006 (@IN A x s) ((term11 A x) = (NUMERAL 0))). Qed.
Lemma lem6931008 {A : Type'} (s : A -> Prop) (x : A) (p' : Prop) : term12 A s x p'.
Proof. exact (@lem6931007 A s x p'). Qed.
Lemma lem6931009 {A : Type'} (s : A -> Prop) (x : A) (p' : Prop) : (term12 A s x p') = (term13 A s x p').
Proof. exact (eq_refl (term12 A s x p')). Qed.
Lemma lem6931010 {A : Type'} (s : A -> Prop) (x : A) (p' : Prop) : term13 A s x p'.
Proof. exact (EQ_MP (@lem6931009 A s x p') (@lem6931008 A s x p')). Qed.
Lemma lem6931011 {A : Type'} (s : A -> Prop) (x : A) (p' : Prop) (q' : Prop) : term14 A s x p' q'.
Proof. exact (@lem6931010 A s x p' q'). Qed.
Lemma lem6931012 {A : Type'} (s : A -> Prop) (x : A) (p' : Prop) (q' : Prop) : (term14 A s x p' q') = (term15 A s x p' q').
Proof. exact (eq_refl (term14 A s x p' q')). Qed.
Lemma lem6931013 {A : Type'} (s : A -> Prop) (x : A) (p' : Prop) (q' : Prop) : term15 A s x p' q'.
Proof. exact (EQ_MP (@lem6931012 A s x p' q') (@lem6931011 A s x p' q')). Qed.
Lemma lem6931014 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem6931015 {A : Type'} (x : A) (s : A -> Prop) (q' : Prop) : term16 A x s q'.
Proof. exact (@lem6931013 A s x (@IN A x s) q'). Qed.
Lemma lem6931016 {A : Type'} (x : A) (s : A -> Prop) (q' : Prop) : term17 A x s q'.
Proof. exact (@lem6931015 A x s q' (@lem6931014 A x s)). Qed.
Lemma lem6931023 {A B : Type'} (f : A -> B) (y : A) : (term18 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6931024 {A : Type'} (f : A -> nat) (y : A) : (term19 A f y) = (f y).
Proof. exact (@lem6931023 A nat f y). Qed.
Lemma lem6931025 {A : Type'} (x : A) : (term20 A x) = (term11 A x).
Proof. exact (@lem6931024 A (term6 A) x). Qed.
Lemma lem6931026 {A : Type'} (n : A) : (term11 A n) = (NUMERAL 0).
Proof. exact (eq_refl (term11 A n)). Qed.
Lemma lem6931027 {A : Type'} : (term21 A) = (term6 A).
Proof. exact (fun_ext (fun n : A => @lem6931026 A n)). Qed.
Lemma lem6931028 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6931029 {A : Type'} (x : A) : (term20 A x) = (term11 A x).
Proof. exact (MK_COMB (@lem6931027 A) (@lem6931028 A x)). Qed.
Lemma lem6931030 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6931031 {A : Type'} (x : A) : (term22 A x) = (term23 A x).
Proof. exact (MK_COMB (@lem6931030) (@lem6931029 A x)). Qed.
Lemma lem6931032 {A : Type'} (x : A) : (term11 A x) = (NUMERAL 0).
Proof. exact (eq_refl (term11 A x)). Qed.
Lemma lem6931033 {A : Type'} (x : A) : ((term20 A x) = (term11 A x)) = ((term11 A x) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6931031 A x) (@lem6931032 A x)). Qed.
Lemma lem6931034 {A : Type'} (x : A) : (term11 A x) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6931033 A x) (@lem6931025 A x)). Qed.
Lemma lem6931035 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6931036 {A : Type'} (x : A) : (term23 A x) = term24.
Proof. exact (MK_COMB (@lem6931035) (@lem6931034 A x)). Qed.
Lemma lem6931037 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem6931038 {A : Type'} (x : A) : ((term11 A x) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6931036 A x) (@lem6931037)). Qed.
Lemma lem6931040 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6931041 (x : nat) : (x = x) = True.
Proof. exact (@lem6931040 nat x). Qed.
Lemma lem6931042 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem6931041 (NUMERAL 0)). Qed.
Lemma lem6931043 {A : Type'} (x : A) : ((term11 A x) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem6931038 A x) (@lem6931042)). Qed.
Lemma lem6931044 {A : Type'} (s : A -> Prop) (x : A) : term25 A s x.
Proof. exact (fun h0 : @IN A x s => @lem6931043 A x). Qed.
Lemma lem6931045 {A : Type'} (x : A) (s : A -> Prop) : term26 A x s.
Proof. exact (@lem6931016 A x s True). Qed.
Lemma lem6931046 {A : Type'} (x : A) (s : A -> Prop) : (term27 A s x) = (term28 A x s).
Proof. exact (@lem6931045 A x s (@lem6931044 A s x)). Qed.
Lemma lem6931048 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6931049 {A : Type'} (x : A) (s : A -> Prop) : (term28 A x s) = True.
Proof. exact (@lem6931048 (@IN A x s)). Qed.
Lemma lem6931050 {A : Type'} (s : A -> Prop) (x : A) : (term27 A s x) = True.
Proof. exact (TRANS (@lem6931046 A x s) (@lem6931049 A x s)). Qed.
Lemma lem6931051 {A : Type'} (s : A -> Prop) : (term29 A s) = (term30 A).
Proof. exact (fun_ext (fun x : A => @lem6931050 A s x)). Qed.
Lemma lem6931052 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6931053 {A : Type'} (s : A -> Prop) : (term31 A s) = (term32 A).
Proof. exact (MK_COMB (@lem6931052 A) (@lem6931051 A s)). Qed.
Lemma lem6931055 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6931056 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (@lem6931055 A t). Qed.
Lemma lem6931057 {A : Type'} : (term32 A) = True.
Proof. exact (@lem6931056 A True). Qed.
Lemma lem6931058 {A : Type'} (s : A -> Prop) : (term31 A s) = True.
Proof. exact (TRANS (@lem6931053 A s) (@lem6931057 A)). Qed.
Lemma lem6931059 {A : Type'} (s : A -> Prop) : True = (term31 A s).
Proof. exact (SYM (@lem6931058 A s)). Qed.
Lemma lem6931060 {A : Type'} (s : A -> Prop) : term31 A s.
Proof. exact (EQ_MP (@lem6931059 A s) (@lem0)). Qed.
Lemma lem6931061 {A : Type'} (s : A -> Prop) : (term34 A s) = (NUMERAL 0).
Proof. exact (@lem6930996 A s (@lem6931060 A s)). Qed.
Lemma lem6931062 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6931063 {A : Type'} (s : A -> Prop) : (term35 A s) = term24.
Proof. exact (MK_COMB (@lem6931062) (@lem6931061 A s)). Qed.
Lemma lem6931064 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem6931065 {A : Type'} (s : A -> Prop) : ((term34 A s) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6931063 A s) (@lem6931064)). Qed.
Lemma lem6931067 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6931068 (x : nat) : (x = x) = True.
Proof. exact (@lem6931067 nat x). Qed.
Lemma lem6931069 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem6931068 (NUMERAL 0)). Qed.
Lemma lem6931070 {A : Type'} (s : A -> Prop) : ((term34 A s) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem6931065 A s) (@lem6931069)). Qed.
Lemma lem6931071 {A : Type'} : (term36 A) = (term37 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6931070 A s)). Qed.
Lemma lem6931072 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6931073 {A : Type'} : (term38 A) = (term39 A).
Proof. exact (MK_COMB (@lem6931072 A) (@lem6931071 A)). Qed.
Lemma lem6931075 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6931076 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (@lem6931075 (A -> Prop) t). Qed.
Lemma lem6931077 {A : Type'} : (term39 A) = True.
Proof. exact (@lem6931076 A True). Qed.
Lemma lem6931078 {A : Type'} : (term38 A) = True.
Proof. exact (TRANS (@lem6931073 A) (@lem6931077 A)). Qed.
Lemma lem6931079 {A : Type'} : True = (term38 A).
Proof. exact (SYM (@lem6931078 A)). Qed.
Lemma lem6931080 {A : Type'} : term38 A.
Proof. exact (EQ_MP (@lem6931079 A) (@lem0)). Qed.
