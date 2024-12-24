Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_EMPTY_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3220005 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3220006 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3220005 A s t). Qed.
Lemma lem3220007 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@EMPTY A)) = (term1 A s).
Proof. exact (@lem3220006 A s (@EMPTY A)). Qed.
Lemma lem3220014 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3220015 {A : Type'} (s : A -> Prop) : (term2 A s) = (term3 A s).
Proof. exact (MK_COMB (@lem3220014) (@lem3220007 A s)). Qed.
Lemma lem3220019 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3220020 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (@lem3220019 A s t). Qed.
Lemma lem3220021 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term5 A s).
Proof. exact (@lem3220020 A s (@EMPTY A)). Qed.
Lemma lem3220030 {A : Type'} (s : A -> Prop) : ((@SUBSET A s (@EMPTY A)) = (s = (@EMPTY A))) = ((term1 A s) = (term5 A s)).
Proof. exact (MK_COMB (@lem3220015 A s) (@lem3220021 A s)). Qed.
Lemma lem3220035 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3220030 A s)). Qed.
Lemma lem3220036 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3220037 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (MK_COMB (@lem3220036 A) (@lem3220035 A)). Qed.
Lemma lem3220042 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem3220037 A)). Qed.
Lemma lem3220056 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3220057 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3220056 A P x). Qed.
Lemma lem3220058 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3220057 A s x). Qed.
Lemma lem3220059 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3220060 {A : Type'} (s : A -> Prop) (x : A) : (term10 A x s) = (term11 A s x).
Proof. exact (MK_COMB (@lem3220059) (@lem3220058 A s x)). Qed.
Lemma lem3220062 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3220063 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3220062 A x). Qed.
Lemma lem3220064 {A : Type'} (s : A -> Prop) (x : A) : (term12 A s x) = (term13 A s x).
Proof. exact (MK_COMB (@lem3220060 A s x) (@lem3220063 A x)). Qed.
Lemma lem3220066 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem3220067 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = (term14 A s x).
Proof. exact (@lem3220066 (s x)). Qed.
Lemma lem3220068 {A : Type'} (s : A -> Prop) (x : A) : (term12 A s x) = (term14 A s x).
Proof. exact (TRANS (@lem3220064 A s x) (@lem3220067 A s x)). Qed.
Lemma lem3220069 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A s).
Proof. exact (fun_ext (fun x : A => @lem3220068 A s x)). Qed.
Lemma lem3220070 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3220071 {A : Type'} (s : A -> Prop) : (term1 A s) = (term17 A s).
Proof. exact (MK_COMB (@lem3220070 A) (@lem3220069 A s)). Qed.
Lemma lem3220076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3220077 {A : Type'} (s : A -> Prop) : (term3 A s) = (term18 A s).
Proof. exact (MK_COMB (@lem3220076) (@lem3220071 A s)). Qed.
Lemma lem3220085 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3220086 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3220085 A P x). Qed.
Lemma lem3220087 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3220086 A s x). Qed.
Lemma lem3220088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3220089 {A : Type'} (s : A -> Prop) (x : A) : (term19 A x s) = (term20 A s x).
Proof. exact (MK_COMB (@lem3220088) (@lem3220087 A s x)). Qed.
Lemma lem3220091 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3220092 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3220091 A x). Qed.
Lemma lem3220093 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = ((s x) = False).
Proof. exact (MK_COMB (@lem3220089 A s x) (@lem3220092 A x)). Qed.
Lemma lem3220095 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3220096 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = False) = (term14 A s x).
Proof. exact (@lem3220095 (s x)). Qed.
Lemma lem3220097 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = (term14 A s x).
Proof. exact (TRANS (@lem3220093 A s x) (@lem3220096 A s x)). Qed.
Lemma lem3220098 {A : Type'} (s : A -> Prop) : (term21 A s) = (term16 A s).
Proof. exact (fun_ext (fun x : A => @lem3220097 A s x)). Qed.
Lemma lem3220099 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3220100 {A : Type'} (s : A -> Prop) : (term5 A s) = (term17 A s).
Proof. exact (MK_COMB (@lem3220099 A) (@lem3220098 A s)). Qed.
Lemma lem3220105 {A : Type'} (s : A -> Prop) : ((term1 A s) = (term5 A s)) = ((term17 A s) = (term17 A s)).
Proof. exact (MK_COMB (@lem3220077 A s) (@lem3220100 A s)). Qed.
Lemma lem3220107 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3220108 (x : Prop) : (x = x) = True.
Proof. exact (@lem3220107 Prop x). Qed.
Lemma lem3220109 {A : Type'} (s : A -> Prop) : ((term17 A s) = (term17 A s)) = True.
Proof. exact (@lem3220108 (term17 A s)). Qed.
Lemma lem3220110 {A : Type'} (s : A -> Prop) : ((term1 A s) = (term5 A s)) = True.
Proof. exact (TRANS (@lem3220105 A s) (@lem3220109 A s)). Qed.
Lemma lem3220111 {A : Type'} : (term7 A) = (term22 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3220110 A s)). Qed.
Lemma lem3220112 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3220113 {A : Type'} : (term9 A) = (term23 A).
Proof. exact (MK_COMB (@lem3220112 A) (@lem3220111 A)). Qed.
Lemma lem3220115 {A : Type'} (t : Prop) : (term24 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3220116 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (@lem3220115 (A -> Prop) t). Qed.
Lemma lem3220117 {A : Type'} : (term23 A) = True.
Proof. exact (@lem3220116 A True). Qed.
Lemma lem3220118 {A : Type'} : (term9 A) = True.
Proof. exact (TRANS (@lem3220113 A) (@lem3220117 A)). Qed.
Lemma lem3220119 {A : Type'} : True = (term9 A).
Proof. exact (SYM (@lem3220118 A)). Qed.
Lemma lem3220120 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem3220119 A) (@lem0)). Qed.
Lemma lem3220121 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem3220042 A) (@lem3220120 A)). Qed.
