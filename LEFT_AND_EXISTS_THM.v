Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LEFT_AND_EXISTS_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem5836 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem5837 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : Q.
Proof. exact (proj2 (@lem5836 A P Q h1)). Qed.
Lemma lem5838 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term1 A P.
Proof. exact (proj1 (@lem5836 A P Q h1)). Qed.
Lemma lem5839 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem5840 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (@lem5839 A P x h1). Qed.
Lemma lem5842 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : Q.
Proof. exact (@lem5837 A P Q h1). Qed.
Lemma lem5843 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : P x) (h2 : term0 A P Q) : term2 A P x Q.
Proof. exact (conj (@lem5840 A P x h1) (@lem5842 A P Q h2)). Qed.
Lemma lem5844 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : P x) (h2 : term0 A P Q) : term3 A P Q.
Proof. exact (ex_intro (term4 A P Q) x (@lem5843 A x P Q h1 h2)). Qed.
Lemma lem5845 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term1 A P.
Proof. exact (@lem5838 A P Q h1). Qed.
Lemma lem5846 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term3 A P Q.
Proof. exact (ex_elim (@lem5845 A P Q h1) (fun x : A => fun h0 : term5 A P x => @lem5844 A x P Q h0 h1)). Qed.
Lemma lem5849 {A : Type'} (P : A -> Prop) (Q : Prop) : term6 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem5846 A P Q h0). Qed.
Lemma lem5850 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term3 A P Q) : term3 A P Q.
Proof. exact (h1). Qed.
Lemma lem5851 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) (h1 : term2 A P x Q) : term2 A P x Q.
Proof. exact (h1). Qed.
Lemma lem5853 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) (h1 : term2 A P x Q) : P x.
Proof. exact (proj1 (@lem5851 A P x Q h1)). Qed.
Lemma lem5854 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) (h1 : term2 A P x Q) : P x.
Proof. exact (@lem5853 A P x Q h1). Qed.
Lemma lem5855 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) (h1 : term2 A P x Q) : term1 A P.
Proof. exact (ex_intro (term5 A P) x (@lem5854 A P x Q h1)). Qed.
Lemma lem5858 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term3 A P Q) : term3 A P Q.
Proof. exact (@lem5850 A P Q h1). Qed.
Lemma lem5859 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term3 A P Q) : term1 A P.
Proof. exact (ex_elim (@lem5858 A P Q h1) (fun x : A => fun h0 : term4 A P Q x => @lem5855 A P x Q h0)). Qed.
Lemma lem5860 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term3 A P Q) : term3 A P Q.
Proof. exact (@lem5850 A P Q h1). Qed.
Lemma lem5861 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) (h1 : term2 A P x Q) : term2 A P x Q.
Proof. exact (h1). Qed.
Lemma lem5862 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) (h1 : term2 A P x Q) : Q.
Proof. exact (proj2 (@lem5861 A P x Q h1)). Qed.
Lemma lem5864 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term3 A P Q) : Q.
Proof. exact (ex_elim (@lem5860 A P Q h1) (fun x : A => fun h0 : term4 A P Q x => @lem5862 A P x Q h0)). Qed.
Lemma lem5865 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term3 A P Q) : term0 A P Q.
Proof. exact (conj (@lem5859 A P Q h1) (@lem5864 A P Q h1)). Qed.
Lemma lem5866 {A : Type'} (P : A -> Prop) (Q : Prop) : term7 A P Q.
Proof. exact (fun h0 : term3 A P Q => @lem5865 A P Q h0). Qed.
Lemma lem5867 {A : Type'} (P : A -> Prop) (Q : Prop) : term6 A P Q.
Proof. exact (@lem5849 A P Q). Qed.
Lemma lem5868 {A : Type'} (P : A -> Prop) (Q : Prop) : term8 A P Q.
Proof. exact (conj (@lem5867 A P Q) (@lem5866 A P Q)). Qed.
Lemma lem5869 {A : Type'} (P : A -> Prop) (Q : Prop) : (term8 A P Q) = ((term0 A P Q) = (term3 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term3 A P Q)). Qed.
Lemma lem5870 {A : Type'} (P : A -> Prop) (Q : Prop) : (term0 A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem5869 A P Q) (@lem5868 A P Q)). Qed.
Lemma lem5875 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (fun Q : Prop => @lem5870 A P Q). Qed.
Lemma lem5880 {A : Type'} : term10 A.
Proof. exact (fun P : A -> Prop => @lem5875 A P). Qed.
Lemma lem5881 {A : Type'} : term10 A.
Proof. exact (@lem5880 A). Qed.
