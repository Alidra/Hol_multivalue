Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_AND_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem4897 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem4898 {A : Type'} (_95 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term1 A P Q _95.
Proof. exact (@lem4897 A P Q h1 _95). Qed.
Lemma lem4899 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (_95 : A) : (term1 A P Q _95) = (term2 A P Q _95).
Proof. exact (eq_refl (term1 A P Q _95)). Qed.
Lemma lem4900 {A : Type'} (_95 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term2 A P Q _95.
Proof. exact (EQ_MP (@lem4899 A P Q _95) (@lem4898 A _95 P Q h1)). Qed.
Lemma lem4902 {A : Type'} (_95 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : P _95.
Proof. exact (proj1 (@lem4900 A _95 P Q h1)). Qed.
Lemma lem4903 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : P x.
Proof. exact (@lem4902 A x P Q h1). Qed.
Lemma lem4909 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem4897 A P Q h1). Qed.
Lemma lem4910 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : (term0 A P Q) = (P x).
Proof. exact (prop_ext (fun h2 : term0 A P Q => @lem4903 A x P Q h1) (fun h2 : P x => @lem4909 A P Q h1)). Qed.
Lemma lem4911 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : P x.
Proof. exact (EQ_MP (@lem4910 A x P Q h1) (@lem4909 A P Q h1)). Qed.
Lemma lem4916 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P.
Proof. exact (fun x : A => @lem4911 A x P Q h1). Qed.
Lemma lem4917 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem4897 A P Q h1). Qed.
Lemma lem4918 {A : Type'} (_96 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term1 A P Q _96.
Proof. exact (@lem4917 A P Q h1 _96). Qed.
Lemma lem4919 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (_96 : A) : (term1 A P Q _96) = (term2 A P Q _96).
Proof. exact (eq_refl (term1 A P Q _96)). Qed.
Lemma lem4920 {A : Type'} (_96 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term2 A P Q _96.
Proof. exact (EQ_MP (@lem4919 A P Q _96) (@lem4918 A _96 P Q h1)). Qed.
Lemma lem4921 {A : Type'} (_96 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : Q _96.
Proof. exact (proj2 (@lem4920 A _96 P Q h1)). Qed.
Lemma lem4923 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : Q x.
Proof. exact (@lem4921 A x P Q h1). Qed.
Lemma lem4929 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem4917 A P Q h1). Qed.
Lemma lem4930 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : (term0 A P Q) = (Q x).
Proof. exact (prop_ext (fun h2 : term0 A P Q => @lem4923 A x P Q h1) (fun h2 : Q x => @lem4929 A P Q h1)). Qed.
Lemma lem4931 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : Q x.
Proof. exact (EQ_MP (@lem4930 A x P Q h1) (@lem4929 A P Q h1)). Qed.
Lemma lem4936 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A Q.
Proof. exact (fun x : A => @lem4931 A x P Q h1). Qed.
Lemma lem4937 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P.
Proof. exact (@lem4916 A P Q h1). Qed.
Lemma lem4938 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term4 A P Q.
Proof. exact (conj (@lem4937 A P Q h1) (@lem4936 A P Q h1)). Qed.
Lemma lem4939 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem4938 A P Q h0). Qed.
Lemma lem4940 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (h1). Qed.
Lemma lem4942 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term3 A P.
Proof. exact (proj1 (@lem4940 A P Q h1)). Qed.
Lemma lem4952 {A : Type'} (_100 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term6 A P _100.
Proof. exact (@lem4942 A P Q h1 _100). Qed.
Lemma lem4953 {A : Type'} (P : A -> Prop) (_100 : A) : (term6 A P _100) = (P _100).
Proof. exact (eq_refl (term6 A P _100)). Qed.
Lemma lem4954 {A : Type'} (_100 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : P _100.
Proof. exact (EQ_MP (@lem4953 A P _100) (@lem4952 A _100 P Q h1)). Qed.
Lemma lem4955 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : P x.
Proof. exact (@lem4954 A x P Q h1). Qed.
Lemma lem4962 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (@lem4940 A P Q h1). Qed.
Lemma lem4963 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term3 A Q.
Proof. exact (proj2 (@lem4962 A P Q h1)). Qed.
Lemma lem4965 {A : Type'} (_101 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term6 A Q _101.
Proof. exact (@lem4963 A P Q h1 _101). Qed.
Lemma lem4966 {A : Type'} (Q : A -> Prop) (_101 : A) : (term6 A Q _101) = (Q _101).
Proof. exact (eq_refl (term6 A Q _101)). Qed.
Lemma lem4967 {A : Type'} (_101 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : Q _101.
Proof. exact (EQ_MP (@lem4966 A Q _101) (@lem4965 A _101 P Q h1)). Qed.
Lemma lem4968 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : Q x.
Proof. exact (@lem4967 A x P Q h1). Qed.
Lemma lem4975 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : P x.
Proof. exact (@lem4955 A x P Q h1). Qed.
Lemma lem4976 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term2 A P Q x.
Proof. exact (conj (@lem4975 A x P Q h1) (@lem4968 A x P Q h1)). Qed.
Lemma lem4981 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term0 A P Q.
Proof. exact (fun x : A => @lem4976 A x P Q h1). Qed.
Lemma lem4982 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (fun h0 : term4 A P Q => @lem4981 A P Q h0). Qed.
Lemma lem4983 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (@lem4939 A P Q). Qed.
Lemma lem4984 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term8 A P Q.
Proof. exact (conj (@lem4983 A P Q) (@lem4982 A P Q)). Qed.
Lemma lem4985 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term8 A P Q) = ((term0 A P Q) = (term4 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term4 A P Q)). Qed.
Lemma lem4986 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term0 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem4985 A P Q) (@lem4984 A P Q)). Qed.
Lemma lem4991 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (fun Q : A -> Prop => @lem4986 A P Q). Qed.
Lemma lem4996 {A : Type'} : term10 A.
Proof. exact (fun P : A -> Prop => @lem4991 A P). Qed.
Lemma lem4997 {A : Type'} : term10 A.
Proof. exact (@lem4996 A). Qed.
