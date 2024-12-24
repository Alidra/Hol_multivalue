Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TRIV_AND_EXISTS_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem5975 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem5976 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term1 A Q.
Proof. exact (proj2 (@lem5975 A P Q h1)). Qed.
Lemma lem5977 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term1 A P.
Proof. exact (proj1 (@lem5975 A P Q h1)). Qed.
Lemma lem5978 (Q : Prop) (h1 : Q) : Q.
Proof. exact (h1). Qed.
Lemma lem5979 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem5980 (P : Prop) (Q : Prop) (h1 : P) (h2 : Q) : P /\ Q.
Proof. exact (conj (@lem5979 P h1) (@lem5978 Q h2)). Qed.
Lemma lem5981 {A : Type'} (P : Prop) (Q : Prop) (h1 : P) (h2 : Q) : term2 A P Q.
Proof. exact (ex_intro (term3 A P Q) (@el A) (@lem5980 P Q h1 h2)). Qed.
Lemma lem5982 {A : Type'} (P : Prop) (Q : Prop) (h1 : Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (ex_elim (@lem5977 A P Q h2) (fun x : A => fun h0 : term4 A P x => @lem5981 A P Q h0 h1)). Qed.
Lemma lem5983 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term2 A P Q.
Proof. exact (ex_elim (@lem5976 A P Q h1) (fun x : A => fun h0 : term4 A Q x => @lem5982 A P Q h0 h1)). Qed.
Lemma lem5984 {A : Type'} (P : Prop) (Q : Prop) : term5 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem5983 A P Q h0). Qed.
Lemma lem5985 {A : Type'} (P : Prop) (Q : Prop) (h1 : term2 A P Q) : term2 A P Q.
Proof. exact (h1). Qed.
Lemma lem5986 (P : Prop) (Q : Prop) (h1 : P /\ Q) : P /\ Q.
Proof. exact (h1). Qed.
Lemma lem5988 (P : Prop) (Q : Prop) (h1 : P /\ Q) : P.
Proof. exact (proj1 (@lem5986 P Q h1)). Qed.
Lemma lem5989 {A : Type'} (P : Prop) (Q : Prop) (h1 : P /\ Q) : term1 A P.
Proof. exact (ex_intro (term4 A P) (@el A) (@lem5988 P Q h1)). Qed.
Lemma lem5990 {A : Type'} (P : Prop) (Q : Prop) (h1 : term2 A P Q) : term1 A P.
Proof. exact (ex_elim (@lem5985 A P Q h1) (fun x : A => fun h0 : term3 A P Q x => @lem5989 A P Q h0)). Qed.
Lemma lem5991 (P : Prop) (Q : Prop) (h1 : P /\ Q) : P /\ Q.
Proof. exact (h1). Qed.
Lemma lem5992 (P : Prop) (Q : Prop) (h1 : P /\ Q) : Q.
Proof. exact (proj2 (@lem5991 P Q h1)). Qed.
Lemma lem5994 {A : Type'} (P : Prop) (Q : Prop) (h1 : P /\ Q) : term1 A Q.
Proof. exact (ex_intro (term4 A Q) (@el A) (@lem5992 P Q h1)). Qed.
Lemma lem5995 {A : Type'} (P : Prop) (Q : Prop) (h1 : term2 A P Q) : term1 A Q.
Proof. exact (ex_elim (@lem5985 A P Q h1) (fun x : A => fun h0 : term3 A P Q x => @lem5994 A P Q h0)). Qed.
Lemma lem5996 {A : Type'} (P : Prop) (Q : Prop) (h1 : term2 A P Q) : term0 A P Q.
Proof. exact (conj (@lem5990 A P Q h1) (@lem5995 A P Q h1)). Qed.
Lemma lem5997 {A : Type'} (P : Prop) (Q : Prop) : term6 A P Q.
Proof. exact (fun h0 : term2 A P Q => @lem5996 A P Q h0). Qed.
Lemma lem5998 {A : Type'} (P : Prop) (Q : Prop) : term7 A P Q.
Proof. exact (conj (@lem5984 A P Q) (@lem5997 A P Q)). Qed.
Lemma lem5999 {A : Type'} (P : Prop) (Q : Prop) : (term7 A P Q) = ((term0 A P Q) = (term2 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term2 A P Q)). Qed.
Lemma lem6000 {A : Type'} (P : Prop) (Q : Prop) : (term0 A P Q) = (term2 A P Q).
Proof. exact (EQ_MP (@lem5999 A P Q) (@lem5998 A P Q)). Qed.
Lemma lem6005 {A : Type'} (P : Prop) : term8 A P.
Proof. exact (fun Q : Prop => @lem6000 A P Q). Qed.
Lemma lem6010 {A : Type'} : term9 A.
Proof. exact (fun P : Prop => @lem6005 A P). Qed.
