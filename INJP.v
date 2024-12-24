Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJP_term_abbrevs.
Lemma lem1056932 {A : Type'} : (@INJP A) = (term0 A).
Proof. exact (@INJP_def A). Qed.
Lemma lem1056933 {A : Type'} (_17391 : type1597 A) : _17391 = _17391.
Proof. exact (eq_refl _17391). Qed.
Lemma lem1056934 {A : Type'} (_17391 : type1597 A) : (@INJP A _17391) = (term1 A _17391).
Proof. exact (MK_COMB (@lem1056932 A) (@lem1056933 A _17391)). Qed.
Lemma lem1056935 {A : Type'} (_17391 : type1597 A) : (term1 A _17391) = (term2 A _17391).
Proof. exact (eq_refl (term1 A _17391)). Qed.
Lemma lem1056936 {A : Type'} (_17391 : type1597 A) : (@INJP A _17391) = (term2 A _17391).
Proof. exact (TRANS (@lem1056934 A _17391) (@lem1056935 A _17391)). Qed.
Lemma lem1056937 {A : Type'} (_17392 : type1597 A) : _17392 = _17392.
Proof. exact (eq_refl _17392). Qed.
Lemma lem1056938 {A : Type'} (_17391 : type1597 A) (_17392 : type1597 A) : (@INJP A _17391 _17392) = (term3 A _17391 _17392).
Proof. exact (MK_COMB (@lem1056936 A _17391) (@lem1056937 A _17392)). Qed.
Lemma lem1056939 {A : Type'} (_17391 : type1597 A) (_17392 : type1597 A) : (term3 A _17391 _17392) = (term4 A _17391 _17392).
Proof. exact (eq_refl (term3 A _17391 _17392)). Qed.
Lemma lem1056940 {A : Type'} (_17391 : type1597 A) (_17392 : type1597 A) : (@INJP A _17391 _17392) = (term4 A _17391 _17392).
Proof. exact (TRANS (@lem1056938 A _17391 _17392) (@lem1056939 A _17391 _17392)). Qed.
Lemma lem1056941 {A : Type'} (_17391 : type1597 A) : term5 A _17391.
Proof. exact (fun _17392 : type1597 A => @lem1056940 A _17391 _17392). Qed.
Lemma lem1056942 {A : Type'} : term6 A.
Proof. exact (fun _17391 : type1597 A => @lem1056941 A _17391). Qed.
Lemma lem1056943 {A : Type'} (_17391 : type1597 A) : term7 A _17391.
Proof. exact (@lem1056942 A _17391). Qed.
Lemma lem1056944 {A : Type'} (_17391 : type1597 A) : (term7 A _17391) = (term5 A _17391).
Proof. exact (eq_refl (term7 A _17391)). Qed.
Lemma lem1056945 {A : Type'} (_17391 : type1597 A) : term5 A _17391.
Proof. exact (EQ_MP (@lem1056944 A _17391) (@lem1056943 A _17391)). Qed.
Lemma lem1056946 {A : Type'} (_17391 : type1597 A) (_17392 : type1597 A) : term8 A _17391 _17392.
Proof. exact (@lem1056945 A _17391 _17392). Qed.
Lemma lem1056947 {A : Type'} (_17391 : type1597 A) (_17392 : type1597 A) : (term8 A _17391 _17392) = ((@INJP A _17391 _17392) = (term4 A _17391 _17392)).
Proof. exact (eq_refl (term8 A _17391 _17392)). Qed.
Lemma lem1056948 {A : Type'} (_17391 : type1597 A) (_17392 : type1597 A) : (@INJP A _17391 _17392) = (term4 A _17391 _17392).
Proof. exact (EQ_MP (@lem1056947 A _17391 _17392) (@lem1056946 A _17391 _17392)). Qed.
Lemma lem1056991 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) : (@INJP A f1 f2) = (term4 A f1 f2).
Proof. exact (@lem1056948 A f1 f2). Qed.
Lemma lem1056992 {A : Type'} (f1 : type1597 A) : term5 A f1.
Proof. exact (fun f2 : type1597 A => @lem1056991 A f1 f2). Qed.
Lemma lem1056993 {A : Type'} : term6 A.
Proof. exact (fun f1 : type1597 A => @lem1056992 A f1). Qed.
