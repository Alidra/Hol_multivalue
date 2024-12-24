Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RIGHT_EXISTS_AND_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem5707 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem5708 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : term1 A P Q x) : term1 A P Q x.
Proof. exact (h1). Qed.
Lemma lem5710 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : term1 A P Q x) : P.
Proof. exact (proj1 (@lem5708 A P Q x h1)). Qed.
Lemma lem5711 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : P.
Proof. exact (ex_elim (@lem5707 A P Q h1) (fun x : A => fun h0 : term2 A P Q x => @lem5710 A P Q x h0)). Qed.
Lemma lem5712 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : term1 A P Q x) : term1 A P Q x.
Proof. exact (h1). Qed.
Lemma lem5713 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : term1 A P Q x) : Q x.
Proof. exact (proj2 (@lem5712 A P Q x h1)). Qed.
Lemma lem5715 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : term1 A P Q x) : Q x.
Proof. exact (@lem5713 A P Q x h1). Qed.
Lemma lem5716 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : term1 A P Q x) : term3 A Q.
Proof. exact (ex_intro (term4 A Q) x (@lem5715 A P Q x h1)). Qed.
Lemma lem5719 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem5707 A P Q h1). Qed.
Lemma lem5720 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A Q.
Proof. exact (ex_elim (@lem5719 A P Q h1) (fun x : A => fun h0 : term2 A P Q x => @lem5716 A P Q x h0)). Qed.
Lemma lem5721 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : P.
Proof. exact (@lem5711 A P Q h1). Qed.
Lemma lem5722 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term5 A P Q.
Proof. exact (conj (@lem5721 A P Q h1) (@lem5720 A P Q h1)). Qed.
Lemma lem5723 {A : Type'} (P : Prop) (Q : A -> Prop) : term6 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem5722 A P Q h0). Qed.
Lemma lem5724 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term5 A P Q) : term5 A P Q.
Proof. exact (h1). Qed.
Lemma lem5725 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term5 A P Q) : term3 A Q.
Proof. exact (proj2 (@lem5724 A P Q h1)). Qed.
Lemma lem5726 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term5 A P Q) : P.
Proof. exact (proj1 (@lem5724 A P Q h1)). Qed.
Lemma lem5727 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (h1). Qed.
Lemma lem5728 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (@lem5727 A Q x h1). Qed.
Lemma lem5729 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term5 A P Q) : P.
Proof. exact (@lem5726 A P Q h1). Qed.
Lemma lem5730 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : Q x) (h2 : term5 A P Q) : term1 A P Q x.
Proof. exact (conj (@lem5729 A P Q h2) (@lem5728 A Q x h1)). Qed.
Lemma lem5731 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : Q x) (h2 : term5 A P Q) : term0 A P Q.
Proof. exact (ex_intro (term2 A P Q) x (@lem5730 A x P Q h1 h2)). Qed.
Lemma lem5732 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term5 A P Q) : term3 A Q.
Proof. exact (@lem5725 A P Q h1). Qed.
Lemma lem5733 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term5 A P Q) : term0 A P Q.
Proof. exact (ex_elim (@lem5732 A P Q h1) (fun x : A => fun h0 : term4 A Q x => @lem5731 A x P Q h0 h1)). Qed.
Lemma lem5736 {A : Type'} (P : Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (fun h0 : term5 A P Q => @lem5733 A P Q h0). Qed.
Lemma lem5737 {A : Type'} (P : Prop) (Q : A -> Prop) : term6 A P Q.
Proof. exact (@lem5723 A P Q). Qed.
Lemma lem5738 {A : Type'} (P : Prop) (Q : A -> Prop) : term8 A P Q.
Proof. exact (conj (@lem5737 A P Q) (@lem5736 A P Q)). Qed.
Lemma lem5739 {A : Type'} (P : Prop) (Q : A -> Prop) : (term8 A P Q) = ((term0 A P Q) = (term5 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term5 A P Q)). Qed.
Lemma lem5740 {A : Type'} (P : Prop) (Q : A -> Prop) : (term0 A P Q) = (term5 A P Q).
Proof. exact (EQ_MP (@lem5739 A P Q) (@lem5738 A P Q)). Qed.
Lemma lem5745 {A : Type'} (P : Prop) : term9 A P.
Proof. exact (fun Q : A -> Prop => @lem5740 A P Q). Qed.
Lemma lem5750 {A : Type'} : term10 A.
Proof. exact (fun P : Prop => @lem5745 A P). Qed.
Lemma lem5751 {A : Type'} : term10 A.
Proof. exact (@lem5750 A). Qed.
