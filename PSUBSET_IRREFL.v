Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PSUBSET_IRREFL_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211744_spec.
Require Import thm3211745_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3227989 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3227990 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (@lem3227989 A s t). Qed.
Lemma lem3227991 {A : Type'} (s : A -> Prop) : (@PSUBSET A s s) = (term1 A s).
Proof. exact (@lem3227990 A s s). Qed.
Lemma lem3227995 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3227996 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term2 A s t).
Proof. exact (@lem3227995 A s t). Qed.
Lemma lem3227997 {A : Type'} (s : A -> Prop) : (@SUBSET A s s) = (term3 A s).
Proof. exact (@lem3227996 A s s). Qed.
Lemma lem3228003 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3228004 {A : Type'} (x : A) (s : A -> Prop) : (term4 A x s) = True.
Proof. exact (@lem3228003 (@IN A x s)). Qed.
Lemma lem3228005 {A : Type'} (s : A -> Prop) : (term5 A s) = (term6 A).
Proof. exact (fun_ext (fun x : A => @lem3228004 A x s)). Qed.
Lemma lem3228006 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228007 {A : Type'} (s : A -> Prop) : (term3 A s) = (term7 A).
Proof. exact (MK_COMB (@lem3228006 A) (@lem3228005 A s)). Qed.
Lemma lem3228009 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3228010 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (@lem3228009 A t). Qed.
Lemma lem3228011 {A : Type'} : (term7 A) = True.
Proof. exact (@lem3228010 A True). Qed.
Lemma lem3228012 {A : Type'} (s : A -> Prop) : (term3 A s) = True.
Proof. exact (TRANS (@lem3228007 A s) (@lem3228011 A)). Qed.
Lemma lem3228013 {A : Type'} (s : A -> Prop) : (@SUBSET A s s) = True.
Proof. exact (TRANS (@lem3227997 A s) (@lem3228012 A s)). Qed.
Lemma lem3228014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3228015 {A : Type'} (s : A -> Prop) : (term9 A s) = (and True).
Proof. exact (MK_COMB (@lem3228014) (@lem3228013 A s)). Qed.
Lemma lem3228017 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3228018 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem3228017 (A -> Prop) x). Qed.
Lemma lem3228019 {A : Type'} (s : A -> Prop) : (s = s) = True.
Proof. exact (@lem3228018 A s). Qed.
Lemma lem3228020 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228021 {A : Type'} (s : A -> Prop) : (term10 A s) = (~ True).
Proof. exact (MK_COMB (@lem3228020) (@lem3228019 A s)). Qed.
Lemma lem3228023 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3228024 {A : Type'} (s : A -> Prop) : (term10 A s) = False.
Proof. exact (TRANS (@lem3228021 A s) (@lem3228023)). Qed.
Lemma lem3228025 {A : Type'} (s : A -> Prop) : (term1 A s) = (True /\ False).
Proof. exact (MK_COMB (@lem3228015 A s) (@lem3228024 A s)). Qed.
Lemma lem3228027 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3228028 : (True /\ False) = False.
Proof. exact (@lem3228027 False). Qed.
Lemma lem3228029 {A : Type'} (s : A -> Prop) : (term1 A s) = False.
Proof. exact (TRANS (@lem3228025 A s) (@lem3228028)). Qed.
Lemma lem3228030 {A : Type'} (s : A -> Prop) : (@PSUBSET A s s) = False.
Proof. exact (TRANS (@lem3227991 A s) (@lem3228029 A s)). Qed.
Lemma lem3228031 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228032 {A : Type'} (s : A -> Prop) : (term11 A s) = (~ False).
Proof. exact (MK_COMB (@lem3228031) (@lem3228030 A s)). Qed.
Lemma lem3228034 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3228035 {A : Type'} (s : A -> Prop) : (term11 A s) = True.
Proof. exact (TRANS (@lem3228032 A s) (@lem3228034)). Qed.
Lemma lem3228036 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3228035 A s)). Qed.
Lemma lem3228037 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3228038 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem3228037 A) (@lem3228036 A)). Qed.
Lemma lem3228040 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3228041 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (@lem3228040 (A -> Prop) t). Qed.
Lemma lem3228042 {A : Type'} : (term15 A) = True.
Proof. exact (@lem3228041 A True). Qed.
Lemma lem3228043 {A : Type'} : (term14 A) = True.
Proof. exact (TRANS (@lem3228038 A) (@lem3228042 A)). Qed.
Lemma lem3228044 {A : Type'} : True = (term14 A).
Proof. exact (SYM (@lem3228043 A)). Qed.
Lemma lem3228045 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3228044 A) (@lem0)). Qed.
