Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_OR_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem5367 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem5368 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) (h1 : term1 A P Q x) : term1 A P Q x.
Proof. exact (h1). Qed.
Lemma lem5369 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem5370 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (h1). Qed.
Lemma lem5371 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (@lem5369 A P x h1). Qed.
Lemma lem5372 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : term2 A P.
Proof. exact (ex_intro (term3 A P) x (@lem5371 A P x h1)). Qed.
Lemma lem5373 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : P x) : term4 A P Q.
Proof. exact (or_intro1 (@lem5372 A P x h1) (term2 A Q)). Qed.
Lemma lem5374 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (@lem5370 A Q x h1). Qed.
Lemma lem5375 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (@lem5374 A Q x h1). Qed.
Lemma lem5376 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : term2 A Q.
Proof. exact (ex_intro (term3 A Q) x (@lem5375 A Q x h1)). Qed.
Lemma lem5377 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) (h1 : Q x) : term4 A P Q.
Proof. exact (or_intro2 (term2 A P) (@lem5376 A Q x h1)). Qed.
Lemma lem5378 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : P x) : term4 A P Q.
Proof. exact (@lem5373 A Q P x h1). Qed.
Lemma lem5379 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) (h1 : term1 A P Q x) : term1 A P Q x.
Proof. exact (@lem5368 A P Q x h1). Qed.
Lemma lem5380 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) (h1 : term1 A P Q x) : term4 A P Q.
Proof. exact (or_elim (@lem5379 A P Q x h1) (fun h0 : P x => @lem5378 A Q P x h0) (fun h0 : Q x => @lem5377 A P Q x h0)). Qed.
Lemma lem5381 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem5367 A P Q h1). Qed.
Lemma lem5382 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term4 A P Q.
Proof. exact (ex_elim (@lem5381 A P Q h1) (fun x : A => fun h0 : term5 A P Q x => @lem5380 A P Q x h0)). Qed.
Lemma lem5383 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term6 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem5382 A P Q h0). Qed.
Lemma lem5384 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (h1). Qed.
Lemma lem5385 {A : Type'} (P : A -> Prop) (h1 : term2 A P) : term2 A P.
Proof. exact (h1). Qed.
Lemma lem5386 {A : Type'} (Q : A -> Prop) (h1 : term2 A Q) : term2 A Q.
Proof. exact (h1). Qed.
Lemma lem5387 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem5388 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (@lem5387 A P x h1). Qed.
Lemma lem5389 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : P x) : term1 A P Q x.
Proof. exact (or_intro1 (@lem5388 A P x h1) (Q x)). Qed.
Lemma lem5390 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : P x) : term0 A P Q.
Proof. exact (ex_intro (term5 A P Q) x (@lem5389 A Q P x h1)). Qed.
Lemma lem5391 {A : Type'} (P : A -> Prop) (h1 : term2 A P) : term2 A P.
Proof. exact (@lem5385 A P h1). Qed.
Lemma lem5392 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h1 : term2 A P) : term0 A P Q.
Proof. exact (ex_elim (@lem5391 A P h1) (fun x : A => fun h0 : term3 A P x => @lem5390 A Q P x h0)). Qed.
Lemma lem5393 {A : Type'} (Q : A -> Prop) (h1 : term2 A Q) : term2 A Q.
Proof. exact (@lem5386 A Q h1). Qed.
Lemma lem5394 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (h1). Qed.
Lemma lem5395 {A : Type'} (Q : A -> Prop) (x : A) (h1 : Q x) : Q x.
Proof. exact (@lem5394 A Q x h1). Qed.
Lemma lem5396 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) (h1 : Q x) : term1 A P Q x.
Proof. exact (or_intro2 (P x) (@lem5395 A Q x h1)). Qed.
Lemma lem5397 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) (h1 : Q x) : term0 A P Q.
Proof. exact (ex_intro (term5 A P Q) x (@lem5396 A P Q x h1)). Qed.
Lemma lem5398 {A : Type'} (Q : A -> Prop) (h1 : term2 A Q) : term2 A Q.
Proof. exact (@lem5393 A Q h1). Qed.
Lemma lem5399 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term2 A Q) : term0 A P Q.
Proof. exact (ex_elim (@lem5398 A Q h1) (fun x : A => fun h0 : term3 A Q x => @lem5397 A P Q x h0)). Qed.
Lemma lem5400 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h1 : term2 A P) : term0 A P Q.
Proof. exact (@lem5392 A Q P h1). Qed.
Lemma lem5401 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (@lem5384 A P Q h1). Qed.
Lemma lem5402 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term0 A P Q.
Proof. exact (or_elim (@lem5401 A P Q h1) (fun h0 : term2 A P => @lem5400 A Q P h0) (fun h0 : term2 A Q => @lem5399 A P Q h0)). Qed.
Lemma lem5403 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (fun h0 : term4 A P Q => @lem5402 A P Q h0). Qed.
Lemma lem5404 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term6 A P Q.
Proof. exact (@lem5383 A P Q). Qed.
Lemma lem5405 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term8 A P Q.
Proof. exact (conj (@lem5404 A P Q) (@lem5403 A P Q)). Qed.
Lemma lem5406 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term8 A P Q) = ((term0 A P Q) = (term4 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term4 A P Q)). Qed.
Lemma lem5407 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term0 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem5406 A P Q) (@lem5405 A P Q)). Qed.
Lemma lem5412 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (fun Q : A -> Prop => @lem5407 A P Q). Qed.
Lemma lem5417 {A : Type'} : term10 A.
Proof. exact (fun P : A -> Prop => @lem5412 A P). Qed.
Lemma lem5418 {A : Type'} : term10 A.
Proof. exact (@lem5417 A). Qed.
