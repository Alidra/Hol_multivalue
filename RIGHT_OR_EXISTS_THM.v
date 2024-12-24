Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RIGHT_OR_EXISTS_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem5569 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem5570 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem5571 {A : Type'} (Q : A -> Prop) (h1 : term1 A Q) : term1 A Q.
Proof. exact (h1). Qed.
Lemma lem5572 {A : Type'} (Q : A -> Prop) (_191 : A) (P : Prop) (h1 : P) : term2 A P Q _191.
Proof. exact (or_intro1 (@lem5570 P h1) (Q _191)). Qed.
Lemma lem5573 {A : Type'} (Q : A -> Prop) (P : Prop) (h1 : P) : term3 A P Q.
Proof. exact (ex_intro (term4 A P Q) (@el A) (@lem5572 A Q (@el A) P h1)). Qed.
Lemma lem5574 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (h1). Qed.
Lemma lem5575 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (@lem5574 A Q x h1). Qed.
Lemma lem5576 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : Q x) : term2 A P Q x.
Proof. exact (or_intro2 P (@lem5575 A Q x h1)). Qed.
Lemma lem5577 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : Q x) : term3 A P Q.
Proof. exact (ex_intro (term4 A P Q) x (@lem5576 A P Q x h1)). Qed.
Lemma lem5578 {A : Type'} (Q : A -> Prop) (h1 : term1 A Q) : term1 A Q.
Proof. exact (@lem5571 A Q h1). Qed.
Lemma lem5579 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term1 A Q) : term3 A P Q.
Proof. exact (ex_elim (@lem5578 A Q h1) (fun x : A => fun h0 : term5 A Q x => @lem5577 A P Q x h0)). Qed.
Lemma lem5580 {A : Type'} (Q : A -> Prop) (P : Prop) (h1 : P) : term3 A P Q.
Proof. exact (@lem5573 A Q P h1). Qed.
Lemma lem5581 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem5569 A P Q h1). Qed.
Lemma lem5582 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P Q.
Proof. exact (or_elim (@lem5581 A P Q h1) (fun h0 : P => @lem5580 A Q P h0) (fun h0 : term1 A Q => @lem5579 A P Q h0)). Qed.
Lemma lem5583 {A : Type'} (P : Prop) (Q : A -> Prop) : term6 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem5582 A P Q h0). Qed.
Lemma lem5584 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term3 A P Q) : term3 A P Q.
Proof. exact (h1). Qed.
Lemma lem5585 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : term2 A P Q x) : term2 A P Q x.
Proof. exact (h1). Qed.
Lemma lem5586 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem5587 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (h1). Qed.
Lemma lem5588 {A : Type'} (Q : A -> Prop) (P : Prop) (h1 : P) : term0 A P Q.
Proof. exact (or_intro1 (@lem5586 P h1) (term1 A Q)). Qed.
Lemma lem5589 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (@lem5587 A Q x h1). Qed.
Lemma lem5590 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : term1 A Q.
Proof. exact (ex_intro (term5 A Q) x (@lem5589 A Q x h1)). Qed.
Lemma lem5591 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : Q x) : term0 A P Q.
Proof. exact (or_intro2 P (@lem5590 A Q x h1)). Qed.
Lemma lem5592 {A : Type'} (Q : A -> Prop) (P : Prop) (h1 : P) : term0 A P Q.
Proof. exact (@lem5588 A Q P h1). Qed.
Lemma lem5593 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : term2 A P Q x) : term2 A P Q x.
Proof. exact (@lem5585 A P Q x h1). Qed.
Lemma lem5594 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) (h1 : term2 A P Q x) : term0 A P Q.
Proof. exact (or_elim (@lem5593 A P Q x h1) (fun h0 : P => @lem5592 A Q P h0) (fun h0 : Q x => @lem5591 A P Q x h0)). Qed.
Lemma lem5595 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term3 A P Q) : term3 A P Q.
Proof. exact (@lem5584 A P Q h1). Qed.
Lemma lem5596 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term3 A P Q) : term0 A P Q.
Proof. exact (ex_elim (@lem5595 A P Q h1) (fun x : A => fun h0 : term4 A P Q x => @lem5594 A P Q x h0)). Qed.
Lemma lem5597 {A : Type'} (P : Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (fun h0 : term3 A P Q => @lem5596 A P Q h0). Qed.
Lemma lem5598 {A : Type'} (P : Prop) (Q : A -> Prop) : term6 A P Q.
Proof. exact (@lem5583 A P Q). Qed.
Lemma lem5599 {A : Type'} (P : Prop) (Q : A -> Prop) : term8 A P Q.
Proof. exact (conj (@lem5598 A P Q) (@lem5597 A P Q)). Qed.
Lemma lem5600 {A : Type'} (P : Prop) (Q : A -> Prop) : (term8 A P Q) = ((term0 A P Q) = (term3 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term3 A P Q)). Qed.
Lemma lem5601 {A : Type'} (P : Prop) (Q : A -> Prop) : (term0 A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem5600 A P Q) (@lem5599 A P Q)). Qed.
Lemma lem5606 {A : Type'} (P : Prop) : term9 A P.
Proof. exact (fun Q : A -> Prop => @lem5601 A P Q). Qed.
Lemma lem5611 {A : Type'} : term10 A.
Proof. exact (fun P : Prop => @lem5606 A P). Qed.
Lemma lem5612 {A : Type'} : term10 A.
Proof. exact (@lem5611 A). Qed.
