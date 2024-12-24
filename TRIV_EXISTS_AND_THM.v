Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TRIV_EXISTS_AND_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem5776 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem5777 (P : Prop) (Q : Prop) (h1 : P /\ Q) : P /\ Q.
Proof. exact (h1). Qed.
Lemma lem5779 (P : Prop) (Q : Prop) (h1 : P /\ Q) : P.
Proof. exact (proj1 (@lem5777 P Q h1)). Qed.
Lemma lem5780 {A : Type'} (P : Prop) (Q : Prop) (h1 : P /\ Q) : term1 A P.
Proof. exact (ex_intro (term2 A P) (@el A) (@lem5779 P Q h1)). Qed.
Lemma lem5781 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term1 A P.
Proof. exact (ex_elim (@lem5776 A P Q h1) (fun x : A => fun h0 : term3 A P Q x => @lem5780 A P Q h0)). Qed.
Lemma lem5782 (P : Prop) (Q : Prop) (h1 : P /\ Q) : P /\ Q.
Proof. exact (h1). Qed.
Lemma lem5783 (P : Prop) (Q : Prop) (h1 : P /\ Q) : Q.
Proof. exact (proj2 (@lem5782 P Q h1)). Qed.
Lemma lem5785 {A : Type'} (P : Prop) (Q : Prop) (h1 : P /\ Q) : term1 A Q.
Proof. exact (ex_intro (term2 A Q) (@el A) (@lem5783 P Q h1)). Qed.
Lemma lem5786 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term1 A Q.
Proof. exact (ex_elim (@lem5776 A P Q h1) (fun x : A => fun h0 : term3 A P Q x => @lem5785 A P Q h0)). Qed.
Lemma lem5787 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term4 A P Q.
Proof. exact (conj (@lem5781 A P Q h1) (@lem5786 A P Q h1)). Qed.
Lemma lem5788 {A : Type'} (P : Prop) (Q : Prop) : term5 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem5787 A P Q h0). Qed.
Lemma lem5789 {A : Type'} (P : Prop) (Q : Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (h1). Qed.
Lemma lem5790 {A : Type'} (P : Prop) (Q : Prop) (h1 : term4 A P Q) : term1 A Q.
Proof. exact (proj2 (@lem5789 A P Q h1)). Qed.
Lemma lem5791 {A : Type'} (P : Prop) (Q : Prop) (h1 : term4 A P Q) : term1 A P.
Proof. exact (proj1 (@lem5789 A P Q h1)). Qed.
Lemma lem5792 (Q : Prop) (h1 : Q) : Q.
Proof. exact (h1). Qed.
Lemma lem5793 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem5794 (P : Prop) (Q : Prop) (h1 : P) (h2 : Q) : P /\ Q.
Proof. exact (conj (@lem5793 P h1) (@lem5792 Q h2)). Qed.
Lemma lem5795 {A : Type'} (P : Prop) (Q : Prop) (h1 : P) (h2 : Q) : term0 A P Q.
Proof. exact (ex_intro (term3 A P Q) (@el A) (@lem5794 P Q h1 h2)). Qed.
Lemma lem5796 {A : Type'} (P : Prop) (Q : Prop) (h1 : Q) (h2 : term4 A P Q) : term0 A P Q.
Proof. exact (ex_elim (@lem5791 A P Q h2) (fun x : A => fun h0 : term2 A P x => @lem5795 A P Q h0 h1)). Qed.
Lemma lem5797 {A : Type'} (P : Prop) (Q : Prop) (h1 : term4 A P Q) : term0 A P Q.
Proof. exact (ex_elim (@lem5790 A P Q h1) (fun x : A => fun h0 : term2 A Q x => @lem5796 A P Q h0 h1)). Qed.
Lemma lem5798 {A : Type'} (P : Prop) (Q : Prop) : term6 A P Q.
Proof. exact (fun h0 : term4 A P Q => @lem5797 A P Q h0). Qed.
Lemma lem5799 {A : Type'} (P : Prop) (Q : Prop) : term7 A P Q.
Proof. exact (conj (@lem5788 A P Q) (@lem5798 A P Q)). Qed.
Lemma lem5800 {A : Type'} (P : Prop) (Q : Prop) : (term7 A P Q) = ((term0 A P Q) = (term4 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term4 A P Q)). Qed.
Lemma lem5801 {A : Type'} (P : Prop) (Q : Prop) : (term0 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem5800 A P Q) (@lem5799 A P Q)). Qed.
Lemma lem5806 {A : Type'} (P : Prop) : term8 A P.
Proof. exact (fun Q : Prop => @lem5801 A P Q). Qed.
Lemma lem5811 {A : Type'} : term9 A.
Proof. exact (fun P : Prop => @lem5806 A P). Qed.
