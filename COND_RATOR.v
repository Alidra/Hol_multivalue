Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import COND_RATOR_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem12959 (b : Prop) : term0 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem12960 (b : Prop) : (term0 b) = (term1 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem12961 (b : Prop) : term1 b.
Proof. exact (EQ_MP (@lem12960 b) (@lem12959 b)). Qed.
Lemma lem12962 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem12963 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem12964 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term2 A B f g x) = (term2 A B f g x).
Proof. exact (eq_refl (term2 A B f g x)). Qed.
Lemma lem12965 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (b : Prop) (h1 : b = True) : (term3 A B f g x b) = (term4 A B f g x).
Proof. exact (MK_COMB (@lem12964 A B f g x) (@lem12962 b h1)). Qed.
Lemma lem12966 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term4 A B f g x) = ((@COND (A -> B) True f g x) = (term5 A B f g x)).
Proof. exact (eq_refl (term4 A B f g x)). Qed.
Lemma lem12967 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (b : Prop) : (term6 A B f g x b) = (term6 A B f g x b).
Proof. exact (eq_refl (term6 A B f g x b)). Qed.
Lemma lem12968 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) (x : A) : ((term3 A B f g x b) = (term4 A B f g x)) = ((term3 A B f g x b) = ((@COND (A -> B) True f g x) = (term5 A B f g x))).
Proof. exact (MK_COMB (@lem12967 A B f g x b) (@lem12966 A B f g x)). Qed.
Lemma lem12969 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) (x : A) : (term3 A B f g x b) = ((@COND (A -> B) b f g x) = (term7 A B b f g x)).
Proof. exact (eq_refl (term3 A B f g x b)). Qed.
Lemma lem12970 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12971 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) (x : A) : (term6 A B f g x b) = (term8 A B b f g x).
Proof. exact (MK_COMB (@lem12970) (@lem12969 A B b f g x)). Qed.
Lemma lem12972 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : ((@COND (A -> B) True f g x) = (term5 A B f g x)) = ((@COND (A -> B) True f g x) = (term5 A B f g x)).
Proof. exact (eq_refl ((@COND (A -> B) True f g x) = (term5 A B f g x))). Qed.
Lemma lem12973 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) (x : A) : ((term3 A B f g x b) = ((@COND (A -> B) True f g x) = (term5 A B f g x))) = (((@COND (A -> B) b f g x) = (term7 A B b f g x)) = ((@COND (A -> B) True f g x) = (term5 A B f g x))).
Proof. exact (MK_COMB (@lem12971 A B b f g x) (@lem12972 A B f g x)). Qed.
Lemma lem12974 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) (x : A) : ((term3 A B f g x b) = (term4 A B f g x)) = (((@COND (A -> B) b f g x) = (term7 A B b f g x)) = ((@COND (A -> B) True f g x) = (term5 A B f g x))).
Proof. exact (TRANS (@lem12968 A B b f g x) (@lem12973 A B b f g x)). Qed.
Lemma lem12975 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (b : Prop) (h1 : b = True) : ((@COND (A -> B) b f g x) = (term7 A B b f g x)) = ((@COND (A -> B) True f g x) = (term5 A B f g x)).
Proof. exact (EQ_MP (@lem12974 A B b f g x) (@lem12965 A B f g x b h1)). Qed.
Lemma lem12976 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (b : Prop) (h1 : b = True) : ((@COND (A -> B) True f g x) = (term5 A B f g x)) = ((@COND (A -> B) b f g x) = (term7 A B b f g x)).
Proof. exact (SYM (@lem12975 A B f g x b h1)). Qed.
Lemma lem12977 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term2 A B f g x) = (term2 A B f g x).
Proof. exact (eq_refl (term2 A B f g x)). Qed.
Lemma lem12978 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (b : Prop) (h1 : b = False) : (term3 A B f g x b) = (term9 A B f g x).
Proof. exact (MK_COMB (@lem12977 A B f g x) (@lem12963 b h1)). Qed.
Lemma lem12979 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term9 A B f g x) = ((@COND (A -> B) False f g x) = (term10 A B f g x)).
Proof. exact (eq_refl (term9 A B f g x)). Qed.
Lemma lem12980 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (b : Prop) : (term6 A B f g x b) = (term6 A B f g x b).
Proof. exact (eq_refl (term6 A B f g x b)). Qed.
Lemma lem12981 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) (x : A) : ((term3 A B f g x b) = (term9 A B f g x)) = ((term3 A B f g x b) = ((@COND (A -> B) False f g x) = (term10 A B f g x))).
Proof. exact (MK_COMB (@lem12980 A B f g x b) (@lem12979 A B f g x)). Qed.
Lemma lem12982 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) (x : A) : (term3 A B f g x b) = ((@COND (A -> B) b f g x) = (term7 A B b f g x)).
Proof. exact (eq_refl (term3 A B f g x b)). Qed.
Lemma lem12983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12984 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) (x : A) : (term6 A B f g x b) = (term8 A B b f g x).
Proof. exact (MK_COMB (@lem12983) (@lem12982 A B b f g x)). Qed.
Lemma lem12985 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : ((@COND (A -> B) False f g x) = (term10 A B f g x)) = ((@COND (A -> B) False f g x) = (term10 A B f g x)).
Proof. exact (eq_refl ((@COND (A -> B) False f g x) = (term10 A B f g x))). Qed.
Lemma lem12986 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) (x : A) : ((term3 A B f g x b) = ((@COND (A -> B) False f g x) = (term10 A B f g x))) = (((@COND (A -> B) b f g x) = (term7 A B b f g x)) = ((@COND (A -> B) False f g x) = (term10 A B f g x))).
Proof. exact (MK_COMB (@lem12984 A B b f g x) (@lem12985 A B f g x)). Qed.
Lemma lem12987 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) (x : A) : ((term3 A B f g x b) = (term9 A B f g x)) = (((@COND (A -> B) b f g x) = (term7 A B b f g x)) = ((@COND (A -> B) False f g x) = (term10 A B f g x))).
Proof. exact (TRANS (@lem12981 A B b f g x) (@lem12986 A B b f g x)). Qed.
Lemma lem12988 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (b : Prop) (h1 : b = False) : ((@COND (A -> B) b f g x) = (term7 A B b f g x)) = ((@COND (A -> B) False f g x) = (term10 A B f g x)).
Proof. exact (EQ_MP (@lem12987 A B b f g x) (@lem12978 A B f g x b h1)). Qed.
Lemma lem12989 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (b : Prop) (h1 : b = False) : ((@COND (A -> B) False f g x) = (term10 A B f g x)) = ((@COND (A -> B) b f g x) = (term7 A B b f g x)).
Proof. exact (SYM (@lem12988 A B f g x b h1)). Qed.
Lemma lem12993 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem12994 {A B : Type'} (t2 : A -> B) (t1 : A -> B) : (@COND (A -> B) True t1 t2) = t1.
Proof. exact (@lem12993 (A -> B) t2 t1). Qed.
Lemma lem12995 {A B : Type'} (g : A -> B) (f : A -> B) : (@COND (A -> B) True f g) = f.
Proof. exact (@lem12994 A B g f). Qed.
Lemma lem12996 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem12997 {A B : Type'} (g : A -> B) (f : A -> B) (x : A) : (@COND (A -> B) True f g x) = (f x).
Proof. exact (MK_COMB (@lem12995 A B g f) (@lem12996 A x)). Qed.
Lemma lem12998 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem12999 {A B : Type'} (g : A -> B) (f : A -> B) (x : A) : (term11 A B f g x) = (term12 A B f x).
Proof. exact (MK_COMB (@lem12998 B) (@lem12997 A B g f x)). Qed.
Lemma lem13001 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem13002 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem13001 B t2 t1). Qed.
Lemma lem13003 {A B : Type'} (g : A -> B) (f : A -> B) (x : A) : (term5 A B f g x) = (f x).
Proof. exact (@lem13002 B (g x) (f x)). Qed.
Lemma lem13004 {A B : Type'} (g : A -> B) (f : A -> B) (x : A) : ((@COND (A -> B) True f g x) = (term5 A B f g x)) = ((f x) = (f x)).
Proof. exact (MK_COMB (@lem12999 A B g f x) (@lem13003 A B g f x)). Qed.
Lemma lem13006 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem13007 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem13006 B x). Qed.
Lemma lem13008 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (f x)) = True.
Proof. exact (@lem13007 B (f x)). Qed.
Lemma lem13009 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : ((@COND (A -> B) True f g x) = (term5 A B f g x)) = True.
Proof. exact (TRANS (@lem13004 A B g f x) (@lem13008 A B f x)). Qed.
Lemma lem13010 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : True = ((@COND (A -> B) True f g x) = (term5 A B f g x)).
Proof. exact (SYM (@lem13009 A B f g x)). Qed.
Lemma lem13011 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (@COND (A -> B) True f g x) = (term5 A B f g x).
Proof. exact (EQ_MP (@lem13010 A B f g x) (@lem0)). Qed.
Lemma lem13015 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem13016 {A B : Type'} (t1 : A -> B) (t2 : A -> B) : (@COND (A -> B) False t1 t2) = t2.
Proof. exact (@lem13015 (A -> B) t1 t2). Qed.
Lemma lem13017 {A B : Type'} (f : A -> B) (g : A -> B) : (@COND (A -> B) False f g) = g.
Proof. exact (@lem13016 A B f g). Qed.
Lemma lem13018 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem13019 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (@COND (A -> B) False f g x) = (g x).
Proof. exact (MK_COMB (@lem13017 A B f g) (@lem13018 A x)). Qed.
Lemma lem13020 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem13021 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term13 A B f g x) = (term12 A B g x).
Proof. exact (MK_COMB (@lem13020 B) (@lem13019 A B f g x)). Qed.
Lemma lem13023 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem13024 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem13023 B t1 t2). Qed.
Lemma lem13025 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term10 A B f g x) = (g x).
Proof. exact (@lem13024 B (f x) (g x)). Qed.
Lemma lem13026 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : ((@COND (A -> B) False f g x) = (term10 A B f g x)) = ((g x) = (g x)).
Proof. exact (MK_COMB (@lem13021 A B f g x) (@lem13025 A B f g x)). Qed.
Lemma lem13028 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem13029 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem13028 B x). Qed.
Lemma lem13030 {A B : Type'} (g : A -> B) (x : A) : ((g x) = (g x)) = True.
Proof. exact (@lem13029 B (g x)). Qed.
Lemma lem13031 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : ((@COND (A -> B) False f g x) = (term10 A B f g x)) = True.
Proof. exact (TRANS (@lem13026 A B f g x) (@lem13030 A B g x)). Qed.
Lemma lem13032 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : True = ((@COND (A -> B) False f g x) = (term10 A B f g x)).
Proof. exact (SYM (@lem13031 A B f g x)). Qed.
Lemma lem13033 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (@COND (A -> B) False f g x) = (term10 A B f g x).
Proof. exact (EQ_MP (@lem13032 A B f g x) (@lem0)). Qed.
Lemma lem13034 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (b : Prop) (h1 : b = False) : (@COND (A -> B) b f g x) = (term7 A B b f g x).
Proof. exact (EQ_MP (@lem12989 A B f g x b h1) (@lem13033 A B f g x)). Qed.
Lemma lem13035 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (b : Prop) (h1 : b = True) : (@COND (A -> B) b f g x) = (term7 A B b f g x).
Proof. exact (EQ_MP (@lem12976 A B f g x b h1) (@lem13011 A B f g x)). Qed.
Lemma lem13036 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) (x : A) : (@COND (A -> B) b f g x) = (term7 A B b f g x).
Proof. exact (or_elim (@lem12961 b) (fun h0 : b = True => @lem13035 A B f g x b h0) (fun h0 : b = False => @lem13034 A B f g x b h0)). Qed.
Lemma lem13041 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) : term14 A B b f g.
Proof. exact (fun x : A => @lem13036 A B b f g x). Qed.
Lemma lem13046 {A B : Type'} (b : Prop) (f : A -> B) : term15 A B b f.
Proof. exact (fun g : A -> B => @lem13041 A B b f g). Qed.
Lemma lem13051 {A B : Type'} (b : Prop) : term16 A B b.
Proof. exact (fun f : A -> B => @lem13046 A B b f). Qed.
Lemma lem13056 {A B : Type'} : term17 A B.
Proof. exact (fun b : Prop => @lem13051 A B b). Qed.
