Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RIGHT_AND_EXISTS_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem5906 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem5907 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term1 A Q.
Proof. exact (proj2 (@lem5906 A P Q h1)). Qed.
Lemma lem5908 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : P.
Proof. exact (proj1 (@lem5906 A P Q h1)). Qed.
Lemma lem5909 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (h1). Qed.
Lemma lem5910 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (@lem5909 A Q x h1). Qed.
Lemma lem5911 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : P.
Proof. exact (@lem5908 A P Q h1). Qed.
Lemma lem5912 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : Q x) (h2 : term0 A P Q) : term2 A P Q x.
Proof. exact (conj (@lem5911 A P Q h2) (@lem5910 A Q x h1)). Qed.
Lemma lem5913 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : Q x) (h2 : term0 A P Q) : term3 A P Q.
Proof. exact (ex_intro (term4 A P Q) x (@lem5912 A x P Q h1 h2)). Qed.
Lemma lem5914 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term1 A Q.
Proof. exact (@lem5907 A P Q h1). Qed.
Lemma lem5915 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P Q.
Proof. exact (ex_elim (@lem5914 A P Q h1) (fun x : A => fun h0 : term5 A Q x => @lem5913 A x P Q h0 h1)). Qed.
Lemma lem5918 {A : Type'} (P : Prop) (Q : A -> Prop) : term6 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem5915 A P Q h0). Qed.
Lemma lem5919 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term3 A P Q) : term3 A P Q.
Proof. exact (h1). Qed.
Lemma lem5920 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : term2 A P Q x) : term2 A P Q x.
Proof. exact (h1). Qed.
Lemma lem5922 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : term2 A P Q x) : P.
Proof. exact (proj1 (@lem5920 A P Q x h1)). Qed.
Lemma lem5923 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term3 A P Q) : P.
Proof. exact (ex_elim (@lem5919 A P Q h1) (fun x : A => fun h0 : term4 A P Q x => @lem5922 A P Q x h0)). Qed.
Lemma lem5924 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : term2 A P Q x) : term2 A P Q x.
Proof. exact (h1). Qed.
Lemma lem5925 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : term2 A P Q x) : Q x.
Proof. exact (proj2 (@lem5924 A P Q x h1)). Qed.
Lemma lem5927 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : term2 A P Q x) : Q x.
Proof. exact (@lem5925 A P Q x h1). Qed.
Lemma lem5928 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : term2 A P Q x) : term1 A Q.
Proof. exact (ex_intro (term5 A Q) x (@lem5927 A P Q x h1)). Qed.
Lemma lem5931 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term3 A P Q) : term3 A P Q.
Proof. exact (@lem5919 A P Q h1). Qed.
Lemma lem5932 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term3 A P Q) : term1 A Q.
Proof. exact (ex_elim (@lem5931 A P Q h1) (fun x : A => fun h0 : term4 A P Q x => @lem5928 A P Q x h0)). Qed.
Lemma lem5933 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term3 A P Q) : P.
Proof. exact (@lem5923 A P Q h1). Qed.
Lemma lem5934 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term3 A P Q) : term0 A P Q.
Proof. exact (conj (@lem5933 A P Q h1) (@lem5932 A P Q h1)). Qed.
Lemma lem5935 {A : Type'} (P : Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (fun h0 : term3 A P Q => @lem5934 A P Q h0). Qed.
Lemma lem5936 {A : Type'} (P : Prop) (Q : A -> Prop) : term6 A P Q.
Proof. exact (@lem5918 A P Q). Qed.
Lemma lem5937 {A : Type'} (P : Prop) (Q : A -> Prop) : term8 A P Q.
Proof. exact (conj (@lem5936 A P Q) (@lem5935 A P Q)). Qed.
Lemma lem5938 {A : Type'} (P : Prop) (Q : A -> Prop) : (term8 A P Q) = ((term0 A P Q) = (term3 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term3 A P Q)). Qed.
Lemma lem5939 {A : Type'} (P : Prop) (Q : A -> Prop) : (term0 A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem5938 A P Q) (@lem5937 A P Q)). Qed.
Lemma lem5944 {A : Type'} (P : Prop) : term9 A P.
Proof. exact (fun Q : A -> Prop => @lem5939 A P Q). Qed.
Lemma lem5949 {A : Type'} : term10 A.
Proof. exact (fun P : Prop => @lem5944 A P). Qed.
Lemma lem5950 {A : Type'} : term10 A.
Proof. exact (@lem5949 A). Qed.
