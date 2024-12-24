Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EMPTY_SUBSET_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3219926 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3219927 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3219926 A s t). Qed.
Lemma lem3219928 {A : Type'} (s : A -> Prop) : (@SUBSET A (@EMPTY A) s) = (term1 A s).
Proof. exact (@lem3219927 A (@EMPTY A) s). Qed.
Lemma lem3219935 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3219928 A s)). Qed.
Lemma lem3219936 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3219937 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem3219936 A) (@lem3219935 A)). Qed.
Lemma lem3219942 {A : Type'} : (term5 A) = (term4 A).
Proof. exact (SYM (@lem3219937 A)). Qed.
Lemma lem3219954 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3219955 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3219954 A x). Qed.
Lemma lem3219956 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3219957 {A : Type'} (x : A) : (term6 A x) = (imp False).
Proof. exact (MK_COMB (@lem3219956) (@lem3219955 A x)). Qed.
Lemma lem3219959 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3219960 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3219959 A P x). Qed.
Lemma lem3219961 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3219960 A s x). Qed.
Lemma lem3219962 {A : Type'} (s : A -> Prop) (x : A) : (term7 A x s) = (term8 A s x).
Proof. exact (MK_COMB (@lem3219957 A x) (@lem3219961 A s x)). Qed.
Lemma lem3219964 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3219965 {A : Type'} (s : A -> Prop) (x : A) : (term8 A s x) = True.
Proof. exact (@lem3219964 (s x)). Qed.
Lemma lem3219966 {A : Type'} (x : A) (s : A -> Prop) : (term7 A x s) = True.
Proof. exact (TRANS (@lem3219962 A s x) (@lem3219965 A s x)). Qed.
Lemma lem3219967 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A).
Proof. exact (fun_ext (fun x : A => @lem3219966 A x s)). Qed.
Lemma lem3219968 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3219969 {A : Type'} (s : A -> Prop) : (term1 A s) = (term11 A).
Proof. exact (MK_COMB (@lem3219968 A) (@lem3219967 A s)). Qed.
Lemma lem3219971 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3219972 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (@lem3219971 A t). Qed.
Lemma lem3219973 {A : Type'} : (term11 A) = True.
Proof. exact (@lem3219972 A True). Qed.
Lemma lem3219974 {A : Type'} (s : A -> Prop) : (term1 A s) = True.
Proof. exact (TRANS (@lem3219969 A s) (@lem3219973 A)). Qed.
Lemma lem3219975 {A : Type'} : (term3 A) = (term13 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3219974 A s)). Qed.
Lemma lem3219976 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3219977 {A : Type'} : (term5 A) = (term14 A).
Proof. exact (MK_COMB (@lem3219976 A) (@lem3219975 A)). Qed.
Lemma lem3219979 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3219980 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (@lem3219979 (A -> Prop) t). Qed.
Lemma lem3219981 {A : Type'} : (term14 A) = True.
Proof. exact (@lem3219980 A True). Qed.
Lemma lem3219982 {A : Type'} : (term5 A) = True.
Proof. exact (TRANS (@lem3219977 A) (@lem3219981 A)). Qed.
Lemma lem3219983 {A : Type'} : True = (term5 A).
Proof. exact (SYM (@lem3219982 A)). Qed.
Lemma lem3219984 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem3219983 A) (@lem0)). Qed.
Lemma lem3219985 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem3219942 A) (@lem3219984 A)). Qed.
