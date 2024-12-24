Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TRIV_FORALL_IMP_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem6796 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem6797 {A : Type'} (P : Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (h1). Qed.
Lemma lem6798 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem6799 {A : Type'} (_339 : A) (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term2 A P Q _339.
Proof. exact (@lem6796 A P Q h1 _339). Qed.
Lemma lem6800 {A : Type'} (_339 : A) (P : Prop) (Q : Prop) : (term2 A P Q _339) = (P -> Q).
Proof. exact (eq_refl (term2 A P Q _339)). Qed.
Lemma lem6801 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : P -> Q.
Proof. exact (EQ_MP (@lem6800 A (@el A) P Q) (@lem6799 A (@el A) P Q h1)). Qed.
Lemma lem6805 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem6806 {A : Type'} (P : Prop) (Q : Prop) (h1 : P) (h2 : term0 A P Q) : Q.
Proof. exact (@lem6801 A P Q h2 (@lem6805 P h1)). Qed.
Lemma lem6807 {A : Type'} (P : Prop) (Q : Prop) (h1 : P) (h2 : term0 A P Q) : P = Q.
Proof. exact (prop_ext (fun h3 : P => @lem6806 A P Q h1 h2) (fun h3 : Q => @lem6798 P h1)). Qed.
Lemma lem6808 {A : Type'} (P : Prop) (Q : Prop) (h1 : P) (h2 : term0 A P Q) : Q.
Proof. exact (EQ_MP (@lem6807 A P Q h1 h2) (@lem6798 P h1)). Qed.
Lemma lem6812 {A : Type'} (P : Prop) (Q : Prop) (h1 : P) (h2 : term0 A P Q) : (term0 A P Q) = Q.
Proof. exact (prop_ext (fun h3 : term0 A P Q => @lem6808 A P Q h1 h2) (fun h3 : Q => @lem6796 A P Q h2)). Qed.
Lemma lem6813 {A : Type'} (P : Prop) (Q : Prop) (h1 : P) (h2 : term0 A P Q) : Q.
Proof. exact (EQ_MP (@lem6812 A P Q h1 h2) (@lem6796 A P Q h2)). Qed.
Lemma lem6814 {A : Type'} (Q : Prop) (P : Prop) (h1 : term0 A P Q) (h2 : term1 A P) : Q.
Proof. exact (ex_elim (@lem6797 A P h2) (fun x : A => fun h0 : term3 A P x => @lem6813 A P Q h0 h1)). Qed.
Lemma lem6819 {A : Type'} (Q : Prop) (P : Prop) (h1 : term0 A P Q) (h2 : term1 A P) : term4 A Q.
Proof. exact (fun x : A => @lem6814 A Q P h1 h2). Qed.
Lemma lem6820 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term5 A P Q.
Proof. exact (fun h0 : term1 A P => @lem6819 A Q P h1 h0). Qed.
Lemma lem6821 {A : Type'} (P : Prop) (Q : Prop) : term6 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem6820 A P Q h0). Qed.
Lemma lem6822 {A : Type'} (P : Prop) (Q : Prop) (h1 : term5 A P Q) : term5 A P Q.
Proof. exact (h1). Qed.
Lemma lem6823 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem6824 {A : Type'} (P : Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (h1). Qed.
Lemma lem6825 {A : Type'} (P : Prop) (Q : Prop) (h1 : term1 A P) (h2 : term5 A P Q) : term4 A Q.
Proof. exact (@lem6822 A P Q h2 (@lem6824 A P h1)). Qed.
Lemma lem6826 {A : Type'} (P : Prop) (h1 : P) : term1 A P.
Proof. exact (ex_intro (term3 A P) (@el A) (@lem6823 P h1)). Qed.
Lemma lem6827 {A : Type'} (_342 : A) (P : Prop) (Q : Prop) (h1 : term1 A P) (h2 : term5 A P Q) : term7 A Q _342.
Proof. exact (@lem6825 A P Q h1 h2 _342). Qed.
Lemma lem6828 {A : Type'} (_342 : A) (Q : Prop) : (term7 A Q _342) = Q.
Proof. exact (eq_refl (term7 A Q _342)). Qed.
Lemma lem6829 {A : Type'} (P : Prop) (Q : Prop) (h1 : term1 A P) (h2 : term5 A P Q) : Q.
Proof. exact (EQ_MP (@lem6828 A (@el A) Q) (@lem6827 A (@el A) P Q h1 h2)). Qed.
Lemma lem6833 {A : Type'} (P : Prop) (Q : Prop) (h1 : P) (h2 : term5 A P Q) : (term1 A P) = Q.
Proof. exact (prop_ext (fun h3 : term1 A P => @lem6829 A P Q h3 h2) (fun h3 : Q => @lem6826 A P h1)). Qed.
Lemma lem6834 {A : Type'} (P : Prop) (Q : Prop) (h1 : P) (h2 : term5 A P Q) : Q.
Proof. exact (EQ_MP (@lem6833 A P Q h1 h2) (@lem6826 A P h1)). Qed.
Lemma lem6835 {A : Type'} (P : Prop) (Q : Prop) (h1 : term5 A P Q) : P -> Q.
Proof. exact (fun h0 : P => @lem6834 A P Q h0 h1). Qed.
Lemma lem6840 {A : Type'} (P : Prop) (Q : Prop) (h1 : term5 A P Q) : term0 A P Q.
Proof. exact (fun x : A => @lem6835 A P Q h1). Qed.
Lemma lem6841 {A : Type'} (P : Prop) (Q : Prop) : term8 A P Q.
Proof. exact (fun h0 : term5 A P Q => @lem6840 A P Q h0). Qed.
Lemma lem6842 {A : Type'} (P : Prop) (Q : Prop) : term9 A P Q.
Proof. exact (conj (@lem6821 A P Q) (@lem6841 A P Q)). Qed.
Lemma lem6843 {A : Type'} (P : Prop) (Q : Prop) : (term9 A P Q) = ((term0 A P Q) = (term5 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term5 A P Q)). Qed.
Lemma lem6844 {A : Type'} (P : Prop) (Q : Prop) : (term0 A P Q) = (term5 A P Q).
Proof. exact (EQ_MP (@lem6843 A P Q) (@lem6842 A P Q)). Qed.
Lemma lem6849 {A : Type'} (P : Prop) : term10 A P.
Proof. exact (fun Q : Prop => @lem6844 A P Q). Qed.
Lemma lem6854 {A : Type'} : term11 A.
Proof. exact (fun P : Prop => @lem6849 A P). Qed.
