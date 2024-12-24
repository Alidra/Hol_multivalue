Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_FORALL_THM_term_abbrevs.
Require Import EXISTS_NOT_THM_spec.
Lemma lem10865 {A : Type'} (P : A -> Prop) (h1 : (term0 A P) = (term1 A P)) : (term0 A P) = (term1 A P).
Proof. exact (h1). Qed.
Lemma lem10866 {A : Type'} (P : A -> Prop) (h1 : (term0 A P) = (term1 A P)) : (term1 A P) = (term0 A P).
Proof. exact (SYM (@lem10865 A P h1)). Qed.
Lemma lem10867 {A : Type'} (P : A -> Prop) (h1 : (term1 A P) = (term0 A P)) : (term1 A P) = (term0 A P).
Proof. exact (h1). Qed.
Lemma lem10868 {A : Type'} (P : A -> Prop) (h1 : (term1 A P) = (term0 A P)) : (term0 A P) = (term1 A P).
Proof. exact (SYM (@lem10867 A P h1)). Qed.
Lemma lem10869 {A : Type'} (P : A -> Prop) : ((term0 A P) = (term1 A P)) = ((term1 A P) = (term0 A P)).
Proof. exact (prop_ext (fun h1 : (term0 A P) = (term1 A P) => @lem10866 A P h1) (fun h1 : (term1 A P) = (term0 A P) => @lem10868 A P h1)). Qed.
Lemma lem10870 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem10869 A P)). Qed.
Lemma lem10871 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem10872 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem10871 A) (@lem10870 A)). Qed.
Lemma lem10873 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem10872 A) (@lem10863 A)). Qed.
Lemma lem10874 {A : Type'} (P : A -> Prop) : term6 A P.
Proof. exact (@lem10873 A P). Qed.
Lemma lem10875 {A : Type'} (P : A -> Prop) : (term6 A P) = ((term1 A P) = (term0 A P)).
Proof. exact (eq_refl (term6 A P)). Qed.
Lemma lem10878 {A : Type'} (P : A -> Prop) : (term1 A P) = (term0 A P).
Proof. exact (EQ_MP (@lem10875 A P) (@lem10874 A P)). Qed.
Lemma lem10879 {A : Type'} (P : A -> Prop) : (term1 A P) = (term0 A P).
Proof. exact (@lem10878 A P). Qed.
Lemma lem10884 {A : Type'} : term5 A.
Proof. exact (fun P : A -> Prop => @lem10879 A P). Qed.
