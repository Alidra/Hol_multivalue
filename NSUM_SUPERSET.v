Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_SUPERSET_term_abbrevs.
Require Import ITERATE_SUPERSET_spec.
Require Import MONOIDAL_ADD_spec.
Require Import NEUTRAL_ADD_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm4211_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem6961681 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem6961682 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (SYM (@lem6961681 h1)). Qed.
Lemma lem6961683 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (h1). Qed.
Lemma lem6961684 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (SYM (@lem6961683 h1)). Qed.
Lemma lem6961685 : ((@neutral nat Nat.add) = (NUMERAL 0)) = ((NUMERAL 0) = (@neutral nat Nat.add)).
Proof. exact (prop_ext (fun h1 : (@neutral nat Nat.add) = (NUMERAL 0) => @lem6961682 h1) (fun h1 : (NUMERAL 0) = (@neutral nat Nat.add) => @lem6961684 h1)). Qed.
Lemma lem6961687 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem6961689 {A B : Type'} (op : type1400 B) : term0 A B op.
Proof. exact (@lem6016892 A B op). Qed.
Lemma lem6961690 {A B : Type'} (op : type1400 B) : (term0 A B op) = (term1 A B op).
Proof. exact (eq_refl (term0 A B op)). Qed.
Lemma lem6961691 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (EQ_MP (@lem6961690 A B op) (@lem6961689 A B op)). Qed.
Lemma lem6961692 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6961693 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term2 A B op.
Proof. exact (@lem6961691 A B op (@lem6961692 B op h1)). Qed.
Lemma lem6961694 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term3 A B op f.
Proof. exact (@lem6961693 A B op h1 f). Qed.
Lemma lem6961695 {A B : Type'} (op : type1400 B) (f : A -> B) : (term3 A B op f) = (term4 A B op f).
Proof. exact (eq_refl (term3 A B op f)). Qed.
Lemma lem6961696 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term4 A B op f.
Proof. exact (EQ_MP (@lem6961695 A B op f) (@lem6961694 A B f op h1)). Qed.
Lemma lem6961697 {A B : Type'} (f : A -> B) (u : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term5 A B op f u.
Proof. exact (@lem6961696 A B f op h1 u). Qed.
Lemma lem6961698 {A B : Type'} (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term5 A B op f u) = (term6 A B op u f).
Proof. exact (eq_refl (term5 A B op f u)). Qed.
Lemma lem6961699 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term6 A B op u f.
Proof. exact (EQ_MP (@lem6961698 A B op u f) (@lem6961697 A B f u op h1)). Qed.
Lemma lem6961700 {A B : Type'} (u : A -> Prop) (f : A -> B) (v : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term7 A B op u f v.
Proof. exact (@lem6961699 A B u f op h1 v). Qed.
Lemma lem6961701 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term7 A B op u f v) = (term8 A B v op u f).
Proof. exact (eq_refl (term7 A B op u f v)). Qed.
Lemma lem6961702 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term8 A B v op u f.
Proof. exact (EQ_MP (@lem6961701 A B v op u f) (@lem6961700 A B u f v op h1)). Qed.
Lemma lem6961703 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term9 A B v u f op) : term9 A B v u f op.
Proof. exact (h1). Qed.
Lemma lem6961704 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term9 A B v u f op) : (@iterate B A op v f) = (@iterate B A op u f).
Proof. exact (@lem6961702 A B v u f op h1 (@lem6961703 A B v u f op h2)). Qed.
Lemma lem6961705 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term8 A B v op u f.
Proof. exact (fun h0 : term9 A B v u f op => @lem6961704 A B v u f op h1 h0). Qed.
Lemma lem6961706 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : term10 A B v op u f.
Proof. exact (fun h0 : @monoidal B op => @lem6961705 A B v u f op h0). Qed.
Lemma lem6961708 (p : Prop) (q : Prop) (r : Prop) : (term11 p q r) = (term12 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6961713 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term10 A B v op u f) = (term13 A B v op u f).
Proof. exact (@lem6961708 (@monoidal B op) (term9 A B v u f op) ((@iterate B A op v f) = (@iterate B A op u f))). Qed.
Lemma lem6961730 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term14 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6961731 (p : Prop) (q : Prop) (p' : Prop) : term15 p q p'.
Proof. exact (fun q' : Prop => @lem6961730 p q p' q'). Qed.
Lemma lem6961732 (p : Prop) (q : Prop) : term16 p q.
Proof. exact (fun p' : Prop => @lem6961731 p q p'). Qed.
Lemma lem6961733 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term17 A v u f.
Proof. exact (@lem6961732 (term18 A v u f) ((@nsum A v f) = (@nsum A u f))). Qed.
Lemma lem6961734 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (p' : Prop) : term19 A v u f p'.
Proof. exact (@lem6961733 A v u f p'). Qed.
Lemma lem6961735 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (p' : Prop) : (term19 A v u f p') = (term20 A v u f p').
Proof. exact (eq_refl (term19 A v u f p')). Qed.
Lemma lem6961736 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (p' : Prop) : term20 A v u f p'.
Proof. exact (EQ_MP (@lem6961735 A v u f p') (@lem6961734 A v u f p')). Qed.
Lemma lem6961737 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term21 A v u f p' q'.
Proof. exact (@lem6961736 A v u f p' q'). Qed.
Lemma lem6961738 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : (term21 A v u f p' q') = (term22 A v u f p' q').
Proof. exact (eq_refl (term21 A v u f p' q')). Qed.
Lemma lem6961739 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term22 A v u f p' q'.
Proof. exact (EQ_MP (@lem6961738 A v u f p' q') (@lem6961737 A v u f p' q')). Qed.
Lemma lem6961749 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term14 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6961750 (p : Prop) (q : Prop) (p' : Prop) : term15 p q p'.
Proof. exact (fun q' : Prop => @lem6961749 p q p' q'). Qed.
Lemma lem6961751 (p : Prop) (q : Prop) : term16 p q.
Proof. exact (fun p' : Prop => @lem6961750 p q p'). Qed.
Lemma lem6961752 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : term23 A v u f x.
Proof. exact (@lem6961751 (term24 A v x u) ((f x) = (NUMERAL 0))). Qed.
Lemma lem6961753 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term25 A v u f x p'.
Proof. exact (@lem6961752 A v u f x p'). Qed.
Lemma lem6961754 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) : (term25 A v u f x p') = (term26 A v u f x p').
Proof. exact (eq_refl (term25 A v u f x p')). Qed.
Lemma lem6961755 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term26 A v u f x p'.
Proof. exact (EQ_MP (@lem6961754 A v u f x p') (@lem6961753 A v u f x p')). Qed.
Lemma lem6961756 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term27 A v u f x p' q'.
Proof. exact (@lem6961755 A v u f x p' q'). Qed.
Lemma lem6961757 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : (term27 A v u f x p' q') = (term28 A v u f x p' q').
Proof. exact (eq_refl (term27 A v u f x p' q')). Qed.
Lemma lem6961758 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term28 A v u f x p' q'.
Proof. exact (EQ_MP (@lem6961757 A v u f x p' q') (@lem6961756 A v u f x p' q')). Qed.
Lemma lem6961761 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term24 A v x u) = (term24 A v x u).
Proof. exact (eq_refl (term24 A v x u)). Qed.
Lemma lem6961762 {A : Type'} (f : A -> nat) (v : A -> Prop) (x : A) (u : A -> Prop) (q' : Prop) : term29 A f v x u q'.
Proof. exact (@lem6961758 A v u f x (term24 A v x u) q'). Qed.
Lemma lem6961763 {A : Type'} (f : A -> nat) (v : A -> Prop) (x : A) (u : A -> Prop) (q' : Prop) : term30 A f v x u q'.
Proof. exact (@lem6961762 A f v x u q' (@lem6961761 A v x u)). Qed.
Lemma lem6961774 : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (EQ_MP (@lem6961685) (@lem6921993)). Qed.
Lemma lem6961775 {A : Type'} (f : A -> nat) (x : A) : (term31 A f x) = (term31 A f x).
Proof. exact (eq_refl (term31 A f x)). Qed.
Lemma lem6961776 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((f x) = (@neutral nat Nat.add)).
Proof. exact (MK_COMB (@lem6961775 A f x) (@lem6961774)). Qed.
Lemma lem6961779 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : term32 A v u f x.
Proof. exact (fun h0 : term24 A v x u => @lem6961776 A f x). Qed.
Lemma lem6961780 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : term33 A v u f x.
Proof. exact (@lem6961763 A f v x u ((f x) = (@neutral nat Nat.add))). Qed.
Lemma lem6961781 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term34 A v u f x) = (term35 A v u f x).
Proof. exact (@lem6961780 A v u f x (@lem6961779 A v u f x)). Qed.
Lemma lem6961817 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term36 A v u f) = (term37 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6961781 A v u f x)). Qed.
Lemma lem6961853 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6961854 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term38 A v u f) = (term39 A v u f).
Proof. exact (MK_COMB (@lem6961853 A) (@lem6961817 A v u f)). Qed.
Lemma lem6961894 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term40 A u v) = (term40 A u v).
Proof. exact (eq_refl (term40 A u v)). Qed.
Lemma lem6961895 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term18 A v u f) = (term41 A v u f).
Proof. exact (MK_COMB (@lem6961894 A u v) (@lem6961854 A v u f)). Qed.
Lemma lem6961937 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (q' : Prop) : term42 A v u f q'.
Proof. exact (@lem6961739 A v u f (term41 A v u f) q'). Qed.
Lemma lem6961938 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (q' : Prop) : term43 A v u f q'.
Proof. exact (@lem6961937 A v u f q' (@lem6961895 A v u f)). Qed.
Lemma lem6961939 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : term41 A v u f.
Proof. exact (h1). Qed.
Lemma lem6961940 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : term39 A v u f.
Proof. exact (proj2 (@lem6961939 A v u f h1)). Qed.
Lemma lem6961941 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : term44 A v u f x.
Proof. exact (@lem6961940 A v u f h1 x). Qed.
Lemma lem6961942 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term44 A v u f x) = (term35 A v u f x).
Proof. exact (eq_refl (term44 A v u f x)). Qed.
Lemma lem6961943 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : term35 A v u f x.
Proof. exact (EQ_MP (@lem6961942 A v u f x) (@lem6961941 A x v u f h1)). Qed.
Lemma lem6961944 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term24 A v x u) : term24 A v x u.
Proof. exact (h1). Qed.
Lemma lem6961945 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term24 A v x u) (h2 : term41 A v u f) : (f x) = (@neutral nat Nat.add).
Proof. exact (@lem6961943 A x v u f h2 (@lem6961944 A v x u h1)). Qed.
Lemma lem6961951 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : @SUBSET A u v.
Proof. exact (proj1 (@lem6961939 A v u f h1)). Qed.
Lemma lem6961952 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@SUBSET A u v) = ((@SUBSET A u v) = True).
Proof. exact (@lem7 (@SUBSET A u v)). Qed.
Lemma lem6961957 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6961958 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6961957 A). Qed.
Lemma lem6961959 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem6961960 {A : Type'} (v : A -> Prop) : (@nsum A v) = (@iterate nat A Nat.add v).
Proof. exact (MK_COMB (@lem6961958 A) (@lem6961959 A v)). Qed.
Lemma lem6961961 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6961962 {A : Type'} (v : A -> Prop) (f : A -> nat) : (@nsum A v f) = (@iterate nat A Nat.add v f).
Proof. exact (MK_COMB (@lem6961960 A v) (@lem6961961 A f)). Qed.
Lemma lem6961964 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : term13 A B v op u f.
Proof. exact (EQ_MP (@lem6961713 A B v op u f) (@lem6961706 A B v op u f)). Qed.
Lemma lem6961965 {A : Type'} (v : A -> Prop) (op : type1606) (u : A -> Prop) (f : A -> nat) : term45 A v op u f.
Proof. exact (@lem6961964 A nat v op u f). Qed.
Lemma lem6961966 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term46 A v u f.
Proof. exact (@lem6961965 A v Nat.add u f). Qed.
Lemma lem6961970 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem6961687) (@lem6924403)). Qed.
Lemma lem6961971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6961972 : term47 = (and True).
Proof. exact (MK_COMB (@lem6961971) (@lem6961970)). Qed.
Lemma lem6961976 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : (@SUBSET A u v) = True.
Proof. exact (EQ_MP (@lem6961952 A u v) (@lem6961951 A v u f h1)). Qed.
Lemma lem6961977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6961978 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : (term40 A u v) = (and True).
Proof. exact (MK_COMB (@lem6961977) (@lem6961976 A v u f h1)). Qed.
Lemma lem6961986 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term14 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6961987 (p : Prop) (q : Prop) (p' : Prop) : term15 p q p'.
Proof. exact (fun q' : Prop => @lem6961986 p q p' q'). Qed.
Lemma lem6961988 (p : Prop) (q : Prop) : term16 p q.
Proof. exact (fun p' : Prop => @lem6961987 p q p'). Qed.
Lemma lem6961989 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : term48 A v u f x.
Proof. exact (@lem6961988 (term24 A v x u) ((f x) = (@neutral nat Nat.add))). Qed.
Lemma lem6961990 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term49 A v u f x p'.
Proof. exact (@lem6961989 A v u f x p'). Qed.
Lemma lem6961991 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) : (term49 A v u f x p') = (term50 A v u f x p').
Proof. exact (eq_refl (term49 A v u f x p')). Qed.
Lemma lem6961992 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) : term50 A v u f x p'.
Proof. exact (EQ_MP (@lem6961991 A v u f x p') (@lem6961990 A v u f x p')). Qed.
Lemma lem6961993 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term51 A v u f x p' q'.
Proof. exact (@lem6961992 A v u f x p' q'). Qed.
Lemma lem6961994 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : (term51 A v u f x p' q') = (term52 A v u f x p' q').
Proof. exact (eq_refl (term51 A v u f x p' q')). Qed.
Lemma lem6961995 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term52 A v u f x p' q'.
Proof. exact (EQ_MP (@lem6961994 A v u f x p' q') (@lem6961993 A v u f x p' q')). Qed.
Lemma lem6961998 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term24 A v x u) = (term24 A v x u).
Proof. exact (eq_refl (term24 A v x u)). Qed.
Lemma lem6961999 {A : Type'} (f : A -> nat) (v : A -> Prop) (x : A) (u : A -> Prop) (q' : Prop) : term53 A f v x u q'.
Proof. exact (@lem6961995 A v u f x (term24 A v x u) q'). Qed.
Lemma lem6962000 {A : Type'} (f : A -> nat) (v : A -> Prop) (x : A) (u : A -> Prop) (q' : Prop) : term54 A f v x u q'.
Proof. exact (@lem6961999 A f v x u q' (@lem6961998 A v x u)). Qed.
Lemma lem6962001 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term24 A v x u) : term24 A v x u.
Proof. exact (h1). Qed.
Lemma lem6962002 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term24 A v x u) : term55 A x u.
Proof. exact (proj2 (@lem6962001 A v x u h1)). Qed.
Lemma lem6962003 {A : Type'} (x : A) (u : A -> Prop) : term56 A x u.
Proof. exact (@lem82 (@IN A x u)). Qed.
Lemma lem6962005 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term24 A v x u) : @IN A x v.
Proof. exact (proj1 (@lem6962001 A v x u h1)). Qed.
Lemma lem6962006 {A : Type'} (x : A) (v : A -> Prop) : (@IN A x v) = ((@IN A x v) = True).
Proof. exact (@lem7 (@IN A x v)). Qed.
Lemma lem6962011 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : term35 A v u f x.
Proof. exact (fun h0 : term24 A v x u => @lem6961945 A x v u f h0 h1). Qed.
Lemma lem6962012 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : term35 A v u f x.
Proof. exact (@lem6962011 A x v u f h1). Qed.
Lemma lem6962016 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term24 A v x u) : (@IN A x v) = True.
Proof. exact (EQ_MP (@lem6962006 A x v) (@lem6962005 A v x u h1)). Qed.
Lemma lem6962017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6962018 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term24 A v x u) : (term57 A x v) = (and True).
Proof. exact (MK_COMB (@lem6962017) (@lem6962016 A v x u h1)). Qed.
Lemma lem6962020 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term24 A v x u) : (@IN A x u) = False.
Proof. exact (@lem6962003 A x u (@lem6962002 A v x u h1)). Qed.
Lemma lem6962021 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6962022 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term24 A v x u) : (term55 A x u) = (~ False).
Proof. exact (MK_COMB (@lem6962021) (@lem6962020 A v x u h1)). Qed.
Lemma lem6962024 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem6962025 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term24 A v x u) : (term55 A x u) = True.
Proof. exact (TRANS (@lem6962022 A v x u h1) (@lem6962024)). Qed.
Lemma lem6962026 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term24 A v x u) : (term24 A v x u) = (True /\ True).
Proof. exact (MK_COMB (@lem6962018 A v x u h1) (@lem6962025 A v x u h1)). Qed.
Lemma lem6962028 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6962029 : (True /\ True) = True.
Proof. exact (@lem6962028 True). Qed.
Lemma lem6962030 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term24 A v x u) : (term24 A v x u) = True.
Proof. exact (TRANS (@lem6962026 A v x u h1) (@lem6962029)). Qed.
Lemma lem6962031 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term24 A v x u) : True = (term24 A v x u).
Proof. exact (SYM (@lem6962030 A v x u h1)). Qed.
Lemma lem6962032 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term24 A v x u) : term24 A v x u.
Proof. exact (EQ_MP (@lem6962031 A v x u h1) (@lem0)). Qed.
Lemma lem6962033 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term24 A v x u) (h2 : term41 A v u f) : (f x) = (@neutral nat Nat.add).
Proof. exact (@lem6962012 A x v u f h2 (@lem6962032 A v x u h1)). Qed.
Lemma lem6962034 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6962035 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term24 A v x u) (h2 : term41 A v u f) : (term31 A f x) = term58.
Proof. exact (MK_COMB (@lem6962034) (@lem6962033 A x v u f h1 h2)). Qed.
Lemma lem6962036 : (@neutral nat Nat.add) = (@neutral nat Nat.add).
Proof. exact (eq_refl (@neutral nat Nat.add)). Qed.
Lemma lem6962037 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term24 A v x u) (h2 : term41 A v u f) : ((f x) = (@neutral nat Nat.add)) = ((@neutral nat Nat.add) = (@neutral nat Nat.add)).
Proof. exact (MK_COMB (@lem6962035 A x v u f h1 h2) (@lem6962036)). Qed.
Lemma lem6962039 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6962040 (x : nat) : (x = x) = True.
Proof. exact (@lem6962039 nat x). Qed.
Lemma lem6962041 : ((@neutral nat Nat.add) = (@neutral nat Nat.add)) = True.
Proof. exact (@lem6962040 (@neutral nat Nat.add)). Qed.
Lemma lem6962042 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term24 A v x u) (h2 : term41 A v u f) : ((f x) = (@neutral nat Nat.add)) = True.
Proof. exact (TRANS (@lem6962037 A x v u f h1 h2) (@lem6962041)). Qed.
Lemma lem6962043 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : term59 A v u f x.
Proof. exact (fun h0 : term24 A v x u => @lem6962042 A x v u f h0 h1). Qed.
Lemma lem6962044 {A : Type'} (f : A -> nat) (v : A -> Prop) (x : A) (u : A -> Prop) : term60 A f v x u.
Proof. exact (@lem6962000 A f v x u True). Qed.
Lemma lem6962045 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : (term35 A v u f x) = (term61 A v x u).
Proof. exact (@lem6962044 A f v x u (@lem6962043 A x v u f h1)). Qed.
Lemma lem6962047 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6962048 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term61 A v x u) = True.
Proof. exact (@lem6962047 (term24 A v x u)). Qed.
Lemma lem6962049 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : (term35 A v u f x) = True.
Proof. exact (TRANS (@lem6962045 A x v u f h1) (@lem6962048 A v x u)). Qed.
Lemma lem6962050 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : (term37 A v u f) = (term62 A).
Proof. exact (fun_ext (fun x : A => @lem6962049 A x v u f h1)). Qed.
Lemma lem6962051 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6962052 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : (term39 A v u f) = (term63 A).
Proof. exact (MK_COMB (@lem6962051 A) (@lem6962050 A v u f h1)). Qed.
Lemma lem6962054 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6962055 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (@lem6962054 A t). Qed.
Lemma lem6962056 {A : Type'} : (term63 A) = True.
Proof. exact (@lem6962055 A True). Qed.
Lemma lem6962057 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : (term39 A v u f) = True.
Proof. exact (TRANS (@lem6962052 A v u f h1) (@lem6962056 A)). Qed.
Lemma lem6962058 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : (term41 A v u f) = (True /\ True).
Proof. exact (MK_COMB (@lem6961978 A v u f h1) (@lem6962057 A v u f h1)). Qed.
Lemma lem6962060 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6962061 : (True /\ True) = True.
Proof. exact (@lem6962060 True). Qed.
Lemma lem6962062 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : (term41 A v u f) = True.
Proof. exact (TRANS (@lem6962058 A v u f h1) (@lem6962061)). Qed.
Lemma lem6962063 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : (term65 A v u f) = (True /\ True).
Proof. exact (MK_COMB (@lem6961972) (@lem6962062 A v u f h1)). Qed.
Lemma lem6962065 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6962066 : (True /\ True) = True.
Proof. exact (@lem6962065 True). Qed.
Lemma lem6962067 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : (term65 A v u f) = True.
Proof. exact (TRANS (@lem6962063 A v u f h1) (@lem6962066)). Qed.
Lemma lem6962068 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : True = (term65 A v u f).
Proof. exact (SYM (@lem6962067 A v u f h1)). Qed.
Lemma lem6962069 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : term65 A v u f.
Proof. exact (EQ_MP (@lem6962068 A v u f h1) (@lem0)). Qed.
Lemma lem6962070 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : (@iterate nat A Nat.add v f) = (@iterate nat A Nat.add u f).
Proof. exact (@lem6961966 A v u f (@lem6962069 A v u f h1)). Qed.
Lemma lem6962075 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : (@nsum A v f) = (@iterate nat A Nat.add u f).
Proof. exact (TRANS (@lem6961962 A v f) (@lem6962070 A v u f h1)). Qed.
Lemma lem6962076 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6962077 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : (term66 A v f) = (term67 A u f).
Proof. exact (MK_COMB (@lem6962076) (@lem6962075 A v u f h1)). Qed.
Lemma lem6962083 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6962084 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6962083 A). Qed.
Lemma lem6962085 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem6962086 {A : Type'} (u : A -> Prop) : (@nsum A u) = (@iterate nat A Nat.add u).
Proof. exact (MK_COMB (@lem6962084 A) (@lem6962085 A u)). Qed.
Lemma lem6962087 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6962088 {A : Type'} (u : A -> Prop) (f : A -> nat) : (@nsum A u f) = (@iterate nat A Nat.add u f).
Proof. exact (MK_COMB (@lem6962086 A u) (@lem6962087 A f)). Qed.
Lemma lem6962093 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : ((@nsum A v f) = (@nsum A u f)) = ((@iterate nat A Nat.add u f) = (@iterate nat A Nat.add u f)).
Proof. exact (MK_COMB (@lem6962077 A v u f h1) (@lem6962088 A u f)). Qed.
Lemma lem6962095 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6962096 (x : nat) : (x = x) = True.
Proof. exact (@lem6962095 nat x). Qed.
Lemma lem6962097 {A : Type'} (u : A -> Prop) (f : A -> nat) : ((@iterate nat A Nat.add u f) = (@iterate nat A Nat.add u f)) = True.
Proof. exact (@lem6962096 (@iterate nat A Nat.add u f)). Qed.
Lemma lem6962098 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term41 A v u f) : ((@nsum A v f) = (@nsum A u f)) = True.
Proof. exact (TRANS (@lem6962093 A v u f h1) (@lem6962097 A u f)). Qed.
Lemma lem6962099 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term68 A v u f.
Proof. exact (fun h0 : term41 A v u f => @lem6962098 A v u f h0). Qed.
Lemma lem6962100 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term69 A v u f.
Proof. exact (@lem6961938 A v u f True). Qed.
Lemma lem6962101 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term70 A v u f) = (term71 A v u f).
Proof. exact (@lem6962100 A v u f (@lem6962099 A v u f)). Qed.
Lemma lem6962103 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6962104 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term71 A v u f) = True.
Proof. exact (@lem6962103 (term41 A v u f)). Qed.
Lemma lem6962105 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term70 A v u f) = True.
Proof. exact (TRANS (@lem6962101 A v u f) (@lem6962104 A v u f)). Qed.
Lemma lem6962106 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term72 A u f) = (term73 A).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6962105 A v u f)). Qed.
Lemma lem6962107 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6962108 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term74 A u f) = (term75 A).
Proof. exact (MK_COMB (@lem6962107 A) (@lem6962106 A u f)). Qed.
Lemma lem6962110 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6962111 {A : Type'} (t : Prop) : (term76 A t) = t.
Proof. exact (@lem6962110 (A -> Prop) t). Qed.
Lemma lem6962112 {A : Type'} : (term75 A) = True.
Proof. exact (@lem6962111 A True). Qed.
Lemma lem6962113 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term74 A u f) = True.
Proof. exact (TRANS (@lem6962108 A u f) (@lem6962112 A)). Qed.
Lemma lem6962114 {A : Type'} (f : A -> nat) : (term77 A f) = (term73 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6962113 A u f)). Qed.
Lemma lem6962115 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6962116 {A : Type'} (f : A -> nat) : (term78 A f) = (term75 A).
Proof. exact (MK_COMB (@lem6962115 A) (@lem6962114 A f)). Qed.
Lemma lem6962118 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6962119 {A : Type'} (t : Prop) : (term76 A t) = t.
Proof. exact (@lem6962118 (A -> Prop) t). Qed.
Lemma lem6962120 {A : Type'} : (term75 A) = True.
Proof. exact (@lem6962119 A True). Qed.
Lemma lem6962121 {A : Type'} (f : A -> nat) : (term78 A f) = True.
Proof. exact (TRANS (@lem6962116 A f) (@lem6962120 A)). Qed.
Lemma lem6962122 {A : Type'} : (term79 A) = (term80 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6962121 A f)). Qed.
Lemma lem6962123 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6962124 {A : Type'} : (term81 A) = (term82 A).
Proof. exact (MK_COMB (@lem6962123 A) (@lem6962122 A)). Qed.
Lemma lem6962126 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6962127 {A : Type'} (t : Prop) : (term83 A t) = t.
Proof. exact (@lem6962126 (A -> nat) t). Qed.
Lemma lem6962128 {A : Type'} : (term82 A) = True.
Proof. exact (@lem6962127 A True). Qed.
Lemma lem6962129 {A : Type'} : (term81 A) = True.
Proof. exact (TRANS (@lem6962124 A) (@lem6962128 A)). Qed.
Lemma lem6962130 {A : Type'} : True = (term81 A).
Proof. exact (SYM (@lem6962129 A)). Qed.
Lemma lem6962131 {A : Type'} : term81 A.
Proof. exact (EQ_MP (@lem6962130 A) (@lem0)). Qed.
