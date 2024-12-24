Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LEFT_IMP_EXISTS_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem6576 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem6577 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem6578 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (h1). Qed.
Lemma lem6579 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term1 A P) (h2 : term0 A P Q) : Q.
Proof. exact (@lem6576 A P Q h2 (@lem6578 A P h1)). Qed.
Lemma lem6580 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (@lem6577 A P x h1). Qed.
Lemma lem6581 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : term1 A P.
Proof. exact (ex_intro (term2 A P) x (@lem6580 A P x h1)). Qed.
Lemma lem6582 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term1 A P) (h2 : term0 A P Q) : Q.
Proof. exact (@lem6579 A P Q h1 h2). Qed.
Lemma lem6586 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : P x) (h2 : term0 A P Q) : (term1 A P) = Q.
Proof. exact (prop_ext (fun h3 : term1 A P => @lem6582 A P Q h3 h2) (fun h3 : Q => @lem6581 A P x h1)). Qed.
Lemma lem6587 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : P x) (h2 : term0 A P Q) : Q.
Proof. exact (EQ_MP (@lem6586 A x P Q h1 h2) (@lem6581 A P x h1)). Qed.
Lemma lem6588 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term3 A P x Q.
Proof. exact (fun h0 : P x => @lem6587 A x P Q h0 h1). Qed.
Lemma lem6593 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term4 A P Q.
Proof. exact (fun x : A => @lem6588 A x P Q h1). Qed.
Lemma lem6594 {A : Type'} (P : A -> Prop) (Q : Prop) : term5 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem6593 A P Q h0). Qed.
Lemma lem6595 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (h1). Qed.
Lemma lem6596 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (h1). Qed.
Lemma lem6597 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem6598 {A : Type'} (_320 : A) (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term6 A P Q _320.
Proof. exact (@lem6595 A P Q h1 _320). Qed.
Lemma lem6599 {A : Type'} (P : A -> Prop) (_320 : A) (Q : Prop) : (term6 A P Q _320) = (term3 A P _320 Q).
Proof. exact (eq_refl (term6 A P Q _320)). Qed.
Lemma lem6600 {A : Type'} (_320 : A) (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term3 A P _320 Q.
Proof. exact (EQ_MP (@lem6599 A P _320 Q) (@lem6598 A _320 P Q h1)). Qed.
Lemma lem6604 {A : Type'} (P : A -> Prop) (_320 : A) (h1 : P _320) : P _320.
Proof. exact (h1). Qed.
Lemma lem6605 {A : Type'} (Q : Prop) (P : A -> Prop) (_320 : A) (h1 : term4 A P Q) (h2 : P _320) : Q.
Proof. exact (@lem6600 A _320 P Q h1 (@lem6604 A P _320 h2)). Qed.
Lemma lem6606 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (@lem6597 A P x h1). Qed.
Lemma lem6607 {A : Type'} (_320 : A) (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term3 A P _320 Q.
Proof. exact (fun h0 : P _320 => @lem6605 A Q P _320 h1 h0). Qed.
Lemma lem6608 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term3 A P x Q.
Proof. exact (@lem6607 A x P Q h1). Qed.
Lemma lem6609 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem6610 {A : Type'} (Q : Prop) (P : A -> Prop) (x : A) (h1 : term4 A P Q) (h2 : P x) : Q.
Proof. exact (@lem6608 A x P Q h1 (@lem6609 A P x h2)). Qed.
Lemma lem6618 {A : Type'} (Q : Prop) (P : A -> Prop) (x : A) (h1 : term4 A P Q) (h2 : P x) : (P x) = Q.
Proof. exact (prop_ext (fun h3 : P x => @lem6610 A Q P x h1 h2) (fun h3 : Q => @lem6606 A P x h2)). Qed.
Lemma lem6619 {A : Type'} (Q : Prop) (P : A -> Prop) (x : A) (h1 : term4 A P Q) (h2 : P x) : Q.
Proof. exact (EQ_MP (@lem6618 A Q P x h1 h2) (@lem6606 A P x h2)). Qed.
Lemma lem6623 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (@lem6595 A P Q h1). Qed.
Lemma lem6624 {A : Type'} (Q : Prop) (P : A -> Prop) (x : A) (h1 : term4 A P Q) (h2 : P x) : (term4 A P Q) = Q.
Proof. exact (prop_ext (fun h3 : term4 A P Q => @lem6619 A Q P x h1 h2) (fun h3 : Q => @lem6623 A P Q h1)). Qed.
Lemma lem6625 {A : Type'} (Q : Prop) (P : A -> Prop) (x : A) (h1 : term4 A P Q) (h2 : P x) : Q.
Proof. exact (EQ_MP (@lem6624 A Q P x h1 h2) (@lem6623 A P Q h1)). Qed.
Lemma lem6626 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (@lem6596 A P h1). Qed.
Lemma lem6627 {A : Type'} (Q : Prop) (P : A -> Prop) (h1 : term4 A P Q) (h2 : term1 A P) : Q.
Proof. exact (ex_elim (@lem6626 A P h2) (fun x : A => fun h0 : term2 A P x => @lem6625 A Q P x h1 h0)). Qed.
Lemma lem6628 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term0 A P Q.
Proof. exact (fun h0 : term1 A P => @lem6627 A Q P h1 h0). Qed.
Lemma lem6629 {A : Type'} (P : A -> Prop) (Q : Prop) : term7 A P Q.
Proof. exact (fun h0 : term4 A P Q => @lem6628 A P Q h0). Qed.
Lemma lem6630 {A : Type'} (P : A -> Prop) (Q : Prop) : term5 A P Q.
Proof. exact (@lem6594 A P Q). Qed.
Lemma lem6631 {A : Type'} (P : A -> Prop) (Q : Prop) : term8 A P Q.
Proof. exact (conj (@lem6630 A P Q) (@lem6629 A P Q)). Qed.
Lemma lem6632 {A : Type'} (P : A -> Prop) (Q : Prop) : (term8 A P Q) = ((term0 A P Q) = (term4 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term4 A P Q)). Qed.
Lemma lem6633 {A : Type'} (P : A -> Prop) (Q : Prop) : (term0 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem6632 A P Q) (@lem6631 A P Q)). Qed.
Lemma lem6638 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (fun Q : Prop => @lem6633 A P Q). Qed.
Lemma lem6643 {A : Type'} : term10 A.
Proof. exact (fun P : A -> Prop => @lem6638 A P). Qed.
Lemma lem6644 {A : Type'} : term10 A.
Proof. exact (@lem6643 A). Qed.
