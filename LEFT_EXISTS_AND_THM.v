Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LEFT_EXISTS_AND_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem5637 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem5638 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) (h1 : term1 A P x Q) : term1 A P x Q.
Proof. exact (h1). Qed.
Lemma lem5640 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) (h1 : term1 A P x Q) : P x.
Proof. exact (proj1 (@lem5638 A P x Q h1)). Qed.
Lemma lem5641 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) (h1 : term1 A P x Q) : P x.
Proof. exact (@lem5640 A P x Q h1). Qed.
Lemma lem5642 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) (h1 : term1 A P x Q) : term2 A P.
Proof. exact (ex_intro (term3 A P) x (@lem5641 A P x Q h1)). Qed.
Lemma lem5645 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem5637 A P Q h1). Qed.
Lemma lem5646 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term2 A P.
Proof. exact (ex_elim (@lem5645 A P Q h1) (fun x : A => fun h0 : term4 A P Q x => @lem5642 A P x Q h0)). Qed.
Lemma lem5647 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem5637 A P Q h1). Qed.
Lemma lem5648 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) (h1 : term1 A P x Q) : term1 A P x Q.
Proof. exact (h1). Qed.
Lemma lem5649 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) (h1 : term1 A P x Q) : Q.
Proof. exact (proj2 (@lem5648 A P x Q h1)). Qed.
Lemma lem5651 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : Q.
Proof. exact (ex_elim (@lem5647 A P Q h1) (fun x : A => fun h0 : term4 A P Q x => @lem5649 A P x Q h0)). Qed.
Lemma lem5652 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term5 A P Q.
Proof. exact (conj (@lem5646 A P Q h1) (@lem5651 A P Q h1)). Qed.
Lemma lem5653 {A : Type'} (P : A -> Prop) (Q : Prop) : term6 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem5652 A P Q h0). Qed.
Lemma lem5654 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term5 A P Q) : term5 A P Q.
Proof. exact (h1). Qed.
Lemma lem5655 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term5 A P Q) : Q.
Proof. exact (proj2 (@lem5654 A P Q h1)). Qed.
Lemma lem5656 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term5 A P Q) : term2 A P.
Proof. exact (proj1 (@lem5654 A P Q h1)). Qed.
Lemma lem5657 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem5658 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (@lem5657 A P x h1). Qed.
Lemma lem5660 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term5 A P Q) : Q.
Proof. exact (@lem5655 A P Q h1). Qed.
Lemma lem5661 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : P x) (h2 : term5 A P Q) : term1 A P x Q.
Proof. exact (conj (@lem5658 A P x h1) (@lem5660 A P Q h2)). Qed.
Lemma lem5662 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : P x) (h2 : term5 A P Q) : term0 A P Q.
Proof. exact (ex_intro (term4 A P Q) x (@lem5661 A x P Q h1 h2)). Qed.
Lemma lem5663 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term5 A P Q) : term2 A P.
Proof. exact (@lem5656 A P Q h1). Qed.
Lemma lem5664 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term5 A P Q) : term0 A P Q.
Proof. exact (ex_elim (@lem5663 A P Q h1) (fun x : A => fun h0 : term3 A P x => @lem5662 A x P Q h0 h1)). Qed.
Lemma lem5667 {A : Type'} (P : A -> Prop) (Q : Prop) : term7 A P Q.
Proof. exact (fun h0 : term5 A P Q => @lem5664 A P Q h0). Qed.
Lemma lem5668 {A : Type'} (P : A -> Prop) (Q : Prop) : term6 A P Q.
Proof. exact (@lem5653 A P Q). Qed.
Lemma lem5669 {A : Type'} (P : A -> Prop) (Q : Prop) : term8 A P Q.
Proof. exact (conj (@lem5668 A P Q) (@lem5667 A P Q)). Qed.
Lemma lem5670 {A : Type'} (P : A -> Prop) (Q : Prop) : (term8 A P Q) = ((term0 A P Q) = (term5 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term5 A P Q)). Qed.
Lemma lem5671 {A : Type'} (P : A -> Prop) (Q : Prop) : (term0 A P Q) = (term5 A P Q).
Proof. exact (EQ_MP (@lem5670 A P Q) (@lem5669 A P Q)). Qed.
Lemma lem5676 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (fun Q : Prop => @lem5671 A P Q). Qed.
Lemma lem5681 {A : Type'} : term10 A.
Proof. exact (fun P : A -> Prop => @lem5676 A P). Qed.
Lemma lem5682 {A : Type'} : term10 A.
Proof. exact (@lem5681 A). Qed.
