Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LEFT_OR_EXISTS_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem5507 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem5508 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (h1). Qed.
Lemma lem5509 (Q : Prop) (h1 : Q) : Q.
Proof. exact (h1). Qed.
Lemma lem5510 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem5511 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (@lem5510 A P x h1). Qed.
Lemma lem5512 {A : Type'} (Q : Prop) (P : A -> Prop) (x : A) (h1 : P x) : term2 A P x Q.
Proof. exact (or_intro1 (@lem5511 A P x h1) Q). Qed.
Lemma lem5513 {A : Type'} (Q : Prop) (P : A -> Prop) (x : A) (h1 : P x) : term3 A P Q.
Proof. exact (ex_intro (term4 A P Q) x (@lem5512 A Q P x h1)). Qed.
Lemma lem5514 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (@lem5508 A P h1). Qed.
Lemma lem5515 {A : Type'} (Q : Prop) (P : A -> Prop) (h1 : term1 A P) : term3 A P Q.
Proof. exact (ex_elim (@lem5514 A P h1) (fun x : A => fun h0 : term5 A P x => @lem5513 A Q P x h0)). Qed.
Lemma lem5516 (Q : Prop) (h1 : Q) : Q.
Proof. exact (@lem5509 Q h1). Qed.
Lemma lem5517 {A : Type'} (P : A -> Prop) (_182 : A) (Q : Prop) (h1 : Q) : term2 A P _182 Q.
Proof. exact (or_intro2 (P _182) (@lem5516 Q h1)). Qed.
Lemma lem5518 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : Q) : term3 A P Q.
Proof. exact (ex_intro (term4 A P Q) (@el A) (@lem5517 A P (@el A) Q h1)). Qed.
Lemma lem5519 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem5507 A P Q h1). Qed.
Lemma lem5520 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term3 A P Q.
Proof. exact (or_elim (@lem5519 A P Q h1) (fun h0 : term1 A P => @lem5515 A Q P h0) (fun h0 : Q => @lem5518 A P Q h0)). Qed.
Lemma lem5521 {A : Type'} (P : A -> Prop) (Q : Prop) : term6 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem5520 A P Q h0). Qed.
Lemma lem5522 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term3 A P Q) : term3 A P Q.
Proof. exact (h1). Qed.
Lemma lem5523 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) (h1 : term2 A P x Q) : term2 A P x Q.
Proof. exact (h1). Qed.
Lemma lem5524 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem5525 (Q : Prop) (h1 : Q) : Q.
Proof. exact (h1). Qed.
Lemma lem5526 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (@lem5524 A P x h1). Qed.
Lemma lem5527 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : term1 A P.
Proof. exact (ex_intro (term5 A P) x (@lem5526 A P x h1)). Qed.
Lemma lem5528 {A : Type'} (Q : Prop) (P : A -> Prop) (x : A) (h1 : P x) : term0 A P Q.
Proof. exact (or_intro1 (@lem5527 A P x h1) Q). Qed.
Lemma lem5529 (Q : Prop) (h1 : Q) : Q.
Proof. exact (@lem5525 Q h1). Qed.
Lemma lem5530 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : Q) : term0 A P Q.
Proof. exact (or_intro2 (term1 A P) (@lem5529 Q h1)). Qed.
Lemma lem5531 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) (h1 : term2 A P x Q) : term2 A P x Q.
Proof. exact (@lem5523 A P x Q h1). Qed.
Lemma lem5532 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) (h1 : term2 A P x Q) : term0 A P Q.
Proof. exact (or_elim (@lem5531 A P x Q h1) (fun h0 : P x => @lem5528 A Q P x h0) (fun h0 : Q => @lem5530 A P Q h0)). Qed.
Lemma lem5533 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term3 A P Q) : term3 A P Q.
Proof. exact (@lem5522 A P Q h1). Qed.
Lemma lem5534 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term3 A P Q) : term0 A P Q.
Proof. exact (ex_elim (@lem5533 A P Q h1) (fun x : A => fun h0 : term4 A P Q x => @lem5532 A P x Q h0)). Qed.
Lemma lem5535 {A : Type'} (P : A -> Prop) (Q : Prop) : term7 A P Q.
Proof. exact (fun h0 : term3 A P Q => @lem5534 A P Q h0). Qed.
Lemma lem5536 {A : Type'} (P : A -> Prop) (Q : Prop) : term6 A P Q.
Proof. exact (@lem5521 A P Q). Qed.
Lemma lem5537 {A : Type'} (P : A -> Prop) (Q : Prop) : term8 A P Q.
Proof. exact (conj (@lem5536 A P Q) (@lem5535 A P Q)). Qed.
Lemma lem5538 {A : Type'} (P : A -> Prop) (Q : Prop) : (term8 A P Q) = ((term0 A P Q) = (term3 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term3 A P Q)). Qed.
Lemma lem5539 {A : Type'} (P : A -> Prop) (Q : Prop) : (term0 A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem5538 A P Q) (@lem5537 A P Q)). Qed.
Lemma lem5544 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (fun Q : Prop => @lem5539 A P Q). Qed.
Lemma lem5549 {A : Type'} : term10 A.
Proof. exact (fun P : A -> Prop => @lem5544 A P). Qed.
Lemma lem5550 {A : Type'} : term10 A.
Proof. exact (@lem5549 A). Qed.
