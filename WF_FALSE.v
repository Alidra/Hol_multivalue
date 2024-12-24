Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_FALSE_term_abbrevs.
Require Import WF_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1843_spec.
Lemma lem369022 {A : Type'} (lt2 : type1402 A) : term0 A lt2.
Proof. exact (@lem303045 A lt2). Qed.
Lemma lem369023 {A : Type'} (lt2 : type1402 A) : (term0 A lt2) = ((@WF A lt2) = (term1 A lt2)).
Proof. exact (eq_refl (term0 A lt2)). Qed.
Lemma lem369026 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term1 A lt2).
Proof. exact (EQ_MP (@lem369023 A lt2) (@lem369022 A lt2)). Qed.
Lemma lem369027 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term1 A lt2).
Proof. exact (@lem369026 A lt2). Qed.
Lemma lem369028 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (@lem369027 A (term4 A)). Qed.
Lemma lem369052 {A B : Type'} (f : A -> B) (y : A) : (term5 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem369053 {A : Type'} (f : type1402 A) (y : A) : (term6 A f y) = (f y).
Proof. exact (@lem369052 A (A -> Prop) f y). Qed.
Lemma lem369054 {A : Type'} (y : A) : (term7 A y) = (term8 A y).
Proof. exact (@lem369053 A (term4 A) y). Qed.
Lemma lem369055 {A : Type'} (x : A) : (term8 A x) = (term9 A).
Proof. exact (eq_refl (term8 A x)). Qed.
Lemma lem369056 {A : Type'} : (term10 A) = (term4 A).
Proof. exact (fun_ext (fun x : A => @lem369055 A x)). Qed.
Lemma lem369057 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem369058 {A : Type'} (y : A) : (term7 A y) = (term8 A y).
Proof. exact (MK_COMB (@lem369056 A) (@lem369057 A y)). Qed.
Lemma lem369059 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem369060 {A : Type'} (y : A) : (term11 A y) = (term12 A y).
Proof. exact (MK_COMB (@lem369059 A) (@lem369058 A y)). Qed.
Lemma lem369061 {A : Type'} (y : A) : (term8 A y) = (term9 A).
Proof. exact (eq_refl (term8 A y)). Qed.
Lemma lem369062 {A : Type'} (y : A) : ((term7 A y) = (term8 A y)) = ((term8 A y) = (term9 A)).
Proof. exact (MK_COMB (@lem369060 A y) (@lem369061 A y)). Qed.
Lemma lem369063 {A : Type'} (y : A) : (term8 A y) = (term9 A).
Proof. exact (EQ_MP (@lem369062 A y) (@lem369054 A y)). Qed.
Lemma lem369064 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem369065 {A : Type'} (y : A) (x : A) : (term13 A y x) = (term14 A x).
Proof. exact (MK_COMB (@lem369063 A y) (@lem369064 A x)). Qed.
Lemma lem369067 {A B : Type'} (f : A -> B) (y : A) : (term5 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem369068 {A : Type'} (f : A -> Prop) (y : A) : (term15 A f y) = (f y).
Proof. exact (@lem369067 A Prop f y). Qed.
Lemma lem369069 {A : Type'} (x : A) : (term16 A x) = (term14 A x).
Proof. exact (@lem369068 A (term9 A) x). Qed.
Lemma lem369070 {A : Type'} (y : A) : (term14 A y) = False.
Proof. exact (eq_refl (term14 A y)). Qed.
Lemma lem369071 {A : Type'} : (term17 A) = (term9 A).
Proof. exact (fun_ext (fun y : A => @lem369070 A y)). Qed.
Lemma lem369072 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem369073 {A : Type'} (x : A) : (term16 A x) = (term14 A x).
Proof. exact (MK_COMB (@lem369071 A) (@lem369072 A x)). Qed.
Lemma lem369074 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem369075 {A : Type'} (x : A) : (term18 A x) = (term19 A x).
Proof. exact (MK_COMB (@lem369074) (@lem369073 A x)). Qed.
Lemma lem369076 {A : Type'} (x : A) : (term14 A x) = False.
Proof. exact (eq_refl (term14 A x)). Qed.
Lemma lem369077 {A : Type'} (x : A) : ((term16 A x) = (term14 A x)) = ((term14 A x) = False).
Proof. exact (MK_COMB (@lem369075 A x) (@lem369076 A x)). Qed.
Lemma lem369078 {A : Type'} (x : A) : (term14 A x) = False.
Proof. exact (EQ_MP (@lem369077 A x) (@lem369069 A x)). Qed.
Lemma lem369079 {A : Type'} (y : A) (x : A) : (term13 A y x) = False.
Proof. exact (TRANS (@lem369065 A y x) (@lem369078 A x)). Qed.
Lemma lem369080 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem369081 {A : Type'} (y : A) (x : A) : (term20 A y x) = (imp False).
Proof. exact (MK_COMB (@lem369080) (@lem369079 A y x)). Qed.
Lemma lem369082 {A : Type'} (P : A -> Prop) (y : A) : (term21 A P y) = (term21 A P y).
Proof. exact (eq_refl (term21 A P y)). Qed.
Lemma lem369083 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term22 A x P y) = (term23 A P y).
Proof. exact (MK_COMB (@lem369081 A y x) (@lem369082 A P y)). Qed.
Lemma lem369085 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem369086 {A : Type'} (P : A -> Prop) (y : A) : (term23 A P y) = True.
Proof. exact (@lem369085 (term21 A P y)). Qed.
Lemma lem369087 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term22 A x P y) = True.
Proof. exact (TRANS (@lem369083 A x P y) (@lem369086 A P y)). Qed.
Lemma lem369088 {A : Type'} (x : A) (P : A -> Prop) : (term24 A x P) = (term25 A).
Proof. exact (fun_ext (fun y : A => @lem369087 A x P y)). Qed.
Lemma lem369089 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem369090 {A : Type'} (x : A) (P : A -> Prop) : (term26 A x P) = (term27 A).
Proof. exact (MK_COMB (@lem369089 A) (@lem369088 A x P)). Qed.
Lemma lem369092 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem369093 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (@lem369092 A t). Qed.
Lemma lem369094 {A : Type'} : (term27 A) = True.
Proof. exact (@lem369093 A True). Qed.
Lemma lem369095 {A : Type'} (x : A) (P : A -> Prop) : (term26 A x P) = True.
Proof. exact (TRANS (@lem369090 A x P) (@lem369094 A)). Qed.
Lemma lem369096 {A : Type'} (P : A -> Prop) (x : A) : (term29 A P x) = (term29 A P x).
Proof. exact (eq_refl (term29 A P x)). Qed.
Lemma lem369097 {A : Type'} (P : A -> Prop) (x : A) : (term30 A x P) = (term31 A P x).
Proof. exact (MK_COMB (@lem369096 A P x) (@lem369095 A x P)). Qed.
Lemma lem369099 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem369100 {A : Type'} (P : A -> Prop) (x : A) : (term31 A P x) = (P x).
Proof. exact (@lem369099 (P x)). Qed.
Lemma lem369101 {A : Type'} (P : A -> Prop) (x : A) : (term30 A x P) = (P x).
Proof. exact (TRANS (@lem369097 A P x) (@lem369100 A P x)). Qed.
Lemma lem369102 {A : Type'} (P : A -> Prop) : (term32 A P) = (term33 A P).
Proof. exact (fun_ext (fun x : A => @lem369101 A P x)). Qed.
Lemma lem369103 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem369104 {A : Type'} (P : A -> Prop) : (term34 A P) = (term35 A P).
Proof. exact (MK_COMB (@lem369103 A) (@lem369102 A P)). Qed.
Lemma lem369109 {A : Type'} (P : A -> Prop) : (term36 A P) = (term36 A P).
Proof. exact (eq_refl (term36 A P)). Qed.
Lemma lem369110 {A : Type'} (P : A -> Prop) : (term37 A P) = (term38 A P).
Proof. exact (MK_COMB (@lem369109 A P) (@lem369104 A P)). Qed.
Lemma lem369112 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem369113 {A : Type'} (P : A -> Prop) : (term38 A P) = True.
Proof. exact (@lem369112 (term35 A P)). Qed.
Lemma lem369114 {A : Type'} (P : A -> Prop) : (term37 A P) = True.
Proof. exact (TRANS (@lem369110 A P) (@lem369113 A P)). Qed.
Lemma lem369115 {A : Type'} : (term39 A) = (term40 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem369114 A P)). Qed.
Lemma lem369116 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem369117 {A : Type'} : (term3 A) = (term41 A).
Proof. exact (MK_COMB (@lem369116 A) (@lem369115 A)). Qed.
Lemma lem369119 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem369120 {A : Type'} (t : Prop) : (term42 A t) = t.
Proof. exact (@lem369119 (A -> Prop) t). Qed.
Lemma lem369121 {A : Type'} : (term41 A) = True.
Proof. exact (@lem369120 A True). Qed.
Lemma lem369122 {A : Type'} : (term3 A) = True.
Proof. exact (TRANS (@lem369117 A) (@lem369121 A)). Qed.
Lemma lem369123 {A : Type'} : (term2 A) = True.
Proof. exact (TRANS (@lem369028 A) (@lem369122 A)). Qed.
Lemma lem369124 {A : Type'} : True = (term2 A).
Proof. exact (SYM (@lem369123 A)). Qed.
Lemma lem369125 {A : Type'} : term2 A.
Proof. exact (EQ_MP (@lem369124 A) (@lem0)). Qed.
