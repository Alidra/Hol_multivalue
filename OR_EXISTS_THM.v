Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import OR_EXISTS_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem5437 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem5438 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (h1). Qed.
Lemma lem5439 {A : Type'} (Q : A -> Prop) (h1 : term1 A Q) : term1 A Q.
Proof. exact (h1). Qed.
Lemma lem5440 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem5441 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (@lem5440 A P x h1). Qed.
Lemma lem5442 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : P x) : term2 A P Q x.
Proof. exact (or_intro1 (@lem5441 A P x h1) (Q x)). Qed.
Lemma lem5443 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : P x) : term3 A P Q.
Proof. exact (ex_intro (term4 A P Q) x (@lem5442 A Q P x h1)). Qed.
Lemma lem5444 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (@lem5438 A P h1). Qed.
Lemma lem5445 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h1 : term1 A P) : term3 A P Q.
Proof. exact (ex_elim (@lem5444 A P h1) (fun x : A => fun h0 : term5 A P x => @lem5443 A Q P x h0)). Qed.
Lemma lem5446 {A : Type'} (Q : A -> Prop) (h1 : term1 A Q) : term1 A Q.
Proof. exact (@lem5439 A Q h1). Qed.
Lemma lem5447 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (h1). Qed.
Lemma lem5448 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (@lem5447 A Q x h1). Qed.
Lemma lem5449 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) (h1 : Q x) : term2 A P Q x.
Proof. exact (or_intro2 (P x) (@lem5448 A Q x h1)). Qed.
Lemma lem5450 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) (h1 : Q x) : term3 A P Q.
Proof. exact (ex_intro (term4 A P Q) x (@lem5449 A P Q x h1)). Qed.
Lemma lem5451 {A : Type'} (Q : A -> Prop) (h1 : term1 A Q) : term1 A Q.
Proof. exact (@lem5446 A Q h1). Qed.
Lemma lem5452 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A Q) : term3 A P Q.
Proof. exact (ex_elim (@lem5451 A Q h1) (fun x : A => fun h0 : term5 A Q x => @lem5450 A P Q x h0)). Qed.
Lemma lem5453 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h1 : term1 A P) : term3 A P Q.
Proof. exact (@lem5445 A Q P h1). Qed.
Lemma lem5454 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem5437 A P Q h1). Qed.
Lemma lem5455 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P Q.
Proof. exact (or_elim (@lem5454 A P Q h1) (fun h0 : term1 A P => @lem5453 A Q P h0) (fun h0 : term1 A Q => @lem5452 A P Q h0)). Qed.
Lemma lem5456 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term6 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem5455 A P Q h0). Qed.
Lemma lem5457 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term3 A P Q) : term3 A P Q.
Proof. exact (h1). Qed.
Lemma lem5458 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) (h1 : term2 A P Q x) : term2 A P Q x.
Proof. exact (h1). Qed.
Lemma lem5459 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem5460 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (h1). Qed.
Lemma lem5461 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (@lem5459 A P x h1). Qed.
Lemma lem5462 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : term1 A P.
Proof. exact (ex_intro (term5 A P) x (@lem5461 A P x h1)). Qed.
Lemma lem5463 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : P x) : term0 A P Q.
Proof. exact (or_intro1 (@lem5462 A P x h1) (term1 A Q)). Qed.
Lemma lem5464 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (@lem5460 A Q x h1). Qed.
Lemma lem5465 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (@lem5464 A Q x h1). Qed.
Lemma lem5466 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : term1 A Q.
Proof. exact (ex_intro (term5 A Q) x (@lem5465 A Q x h1)). Qed.
Lemma lem5467 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) (h1 : Q x) : term0 A P Q.
Proof. exact (or_intro2 (term1 A P) (@lem5466 A Q x h1)). Qed.
Lemma lem5468 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : P x) : term0 A P Q.
Proof. exact (@lem5463 A Q P x h1). Qed.
Lemma lem5469 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) (h1 : term2 A P Q x) : term2 A P Q x.
Proof. exact (@lem5458 A P Q x h1). Qed.
Lemma lem5470 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) (h1 : term2 A P Q x) : term0 A P Q.
Proof. exact (or_elim (@lem5469 A P Q x h1) (fun h0 : P x => @lem5468 A Q P x h0) (fun h0 : Q x => @lem5467 A P Q x h0)). Qed.
Lemma lem5471 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term3 A P Q) : term3 A P Q.
Proof. exact (@lem5457 A P Q h1). Qed.
Lemma lem5472 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term3 A P Q) : term0 A P Q.
Proof. exact (ex_elim (@lem5471 A P Q h1) (fun x : A => fun h0 : term4 A P Q x => @lem5470 A P Q x h0)). Qed.
Lemma lem5473 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (fun h0 : term3 A P Q => @lem5472 A P Q h0). Qed.
Lemma lem5474 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term6 A P Q.
Proof. exact (@lem5456 A P Q). Qed.
Lemma lem5475 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term8 A P Q.
Proof. exact (conj (@lem5474 A P Q) (@lem5473 A P Q)). Qed.
Lemma lem5476 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term8 A P Q) = ((term0 A P Q) = (term3 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term3 A P Q)). Qed.
Lemma lem5477 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term0 A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem5476 A P Q) (@lem5475 A P Q)). Qed.
Lemma lem5482 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (fun Q : A -> Prop => @lem5477 A P Q). Qed.
Lemma lem5487 {A : Type'} : term10 A.
Proof. exact (fun P : A -> Prop => @lem5482 A P). Qed.
Lemma lem5488 {A : Type'} : term10 A.
Proof. exact (@lem5487 A). Qed.
