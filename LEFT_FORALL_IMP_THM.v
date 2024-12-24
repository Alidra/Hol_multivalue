Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LEFT_FORALL_IMP_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem6686 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem6687 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (h1). Qed.
Lemma lem6688 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem6689 {A : Type'} (_329 : A) (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term2 A P Q _329.
Proof. exact (@lem6686 A P Q h1 _329). Qed.
Lemma lem6690 {A : Type'} (P : A -> Prop) (_329 : A) (Q : Prop) : (term2 A P Q _329) = (term3 A P _329 Q).
Proof. exact (eq_refl (term2 A P Q _329)). Qed.
Lemma lem6691 {A : Type'} (_329 : A) (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term3 A P _329 Q.
Proof. exact (EQ_MP (@lem6690 A P _329 Q) (@lem6689 A _329 P Q h1)). Qed.
Lemma lem6695 {A : Type'} (P : A -> Prop) (_329 : A) (h1 : P _329) : P _329.
Proof. exact (h1). Qed.
Lemma lem6696 {A : Type'} (Q : Prop) (P : A -> Prop) (_329 : A) (h1 : term0 A P Q) (h2 : P _329) : Q.
Proof. exact (@lem6691 A _329 P Q h1 (@lem6695 A P _329 h2)). Qed.
Lemma lem6697 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (@lem6688 A P x h1). Qed.
Lemma lem6698 {A : Type'} (_329 : A) (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term3 A P _329 Q.
Proof. exact (fun h0 : P _329 => @lem6696 A Q P _329 h1 h0). Qed.
Lemma lem6699 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term3 A P x Q.
Proof. exact (@lem6698 A x P Q h1). Qed.
Lemma lem6700 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem6701 {A : Type'} (Q : Prop) (P : A -> Prop) (x : A) (h1 : term0 A P Q) (h2 : P x) : Q.
Proof. exact (@lem6699 A x P Q h1 (@lem6700 A P x h2)). Qed.
Lemma lem6709 {A : Type'} (Q : Prop) (P : A -> Prop) (x : A) (h1 : term0 A P Q) (h2 : P x) : (P x) = Q.
Proof. exact (prop_ext (fun h3 : P x => @lem6701 A Q P x h1 h2) (fun h3 : Q => @lem6697 A P x h2)). Qed.
Lemma lem6710 {A : Type'} (Q : Prop) (P : A -> Prop) (x : A) (h1 : term0 A P Q) (h2 : P x) : Q.
Proof. exact (EQ_MP (@lem6709 A Q P x h1 h2) (@lem6697 A P x h2)). Qed.
Lemma lem6714 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem6686 A P Q h1). Qed.
Lemma lem6715 {A : Type'} (Q : Prop) (P : A -> Prop) (x : A) (h1 : term0 A P Q) (h2 : P x) : (term0 A P Q) = Q.
Proof. exact (prop_ext (fun h3 : term0 A P Q => @lem6710 A Q P x h1 h2) (fun h3 : Q => @lem6714 A P Q h1)). Qed.
Lemma lem6716 {A : Type'} (Q : Prop) (P : A -> Prop) (x : A) (h1 : term0 A P Q) (h2 : P x) : Q.
Proof. exact (EQ_MP (@lem6715 A Q P x h1 h2) (@lem6714 A P Q h1)). Qed.
Lemma lem6717 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (@lem6687 A P h1). Qed.
Lemma lem6718 {A : Type'} (Q : Prop) (P : A -> Prop) (h1 : term0 A P Q) (h2 : term1 A P) : Q.
Proof. exact (ex_elim (@lem6717 A P h2) (fun x : A => fun h0 : term4 A P x => @lem6716 A Q P x h1 h0)). Qed.
Lemma lem6719 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term5 A P Q.
Proof. exact (fun h0 : term1 A P => @lem6718 A Q P h1 h0). Qed.
Lemma lem6720 {A : Type'} (P : A -> Prop) (Q : Prop) : term6 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem6719 A P Q h0). Qed.
Lemma lem6721 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term5 A P Q) : term5 A P Q.
Proof. exact (h1). Qed.
Lemma lem6722 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem6723 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (h1). Qed.
Lemma lem6724 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term1 A P) (h2 : term5 A P Q) : Q.
Proof. exact (@lem6721 A P Q h2 (@lem6723 A P h1)). Qed.
Lemma lem6725 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (@lem6722 A P x h1). Qed.
Lemma lem6726 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : term1 A P.
Proof. exact (ex_intro (term4 A P) x (@lem6725 A P x h1)). Qed.
Lemma lem6727 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term1 A P) (h2 : term5 A P Q) : Q.
Proof. exact (@lem6724 A P Q h1 h2). Qed.
Lemma lem6731 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : P x) (h2 : term5 A P Q) : (term1 A P) = Q.
Proof. exact (prop_ext (fun h3 : term1 A P => @lem6727 A P Q h3 h2) (fun h3 : Q => @lem6726 A P x h1)). Qed.
Lemma lem6732 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : P x) (h2 : term5 A P Q) : Q.
Proof. exact (EQ_MP (@lem6731 A x P Q h1 h2) (@lem6726 A P x h1)). Qed.
Lemma lem6733 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : term5 A P Q) : term3 A P x Q.
Proof. exact (fun h0 : P x => @lem6732 A x P Q h0 h1). Qed.
Lemma lem6738 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term5 A P Q) : term0 A P Q.
Proof. exact (fun x : A => @lem6733 A x P Q h1). Qed.
Lemma lem6739 {A : Type'} (P : A -> Prop) (Q : Prop) : term7 A P Q.
Proof. exact (fun h0 : term5 A P Q => @lem6738 A P Q h0). Qed.
Lemma lem6740 {A : Type'} (P : A -> Prop) (Q : Prop) : term6 A P Q.
Proof. exact (@lem6720 A P Q). Qed.
Lemma lem6741 {A : Type'} (P : A -> Prop) (Q : Prop) : term8 A P Q.
Proof. exact (conj (@lem6740 A P Q) (@lem6739 A P Q)). Qed.
Lemma lem6742 {A : Type'} (P : A -> Prop) (Q : Prop) : (term8 A P Q) = ((term0 A P Q) = (term5 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term5 A P Q)). Qed.
Lemma lem6743 {A : Type'} (P : A -> Prop) (Q : Prop) : (term0 A P Q) = (term5 A P Q).
Proof. exact (EQ_MP (@lem6742 A P Q) (@lem6741 A P Q)). Qed.
Lemma lem6748 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (fun Q : Prop => @lem6743 A P Q). Qed.
Lemma lem6753 {A : Type'} : term10 A.
Proof. exact (fun P : A -> Prop => @lem6748 A P). Qed.
Lemma lem6754 {A : Type'} : term10 A.
Proof. exact (@lem6753 A). Qed.
