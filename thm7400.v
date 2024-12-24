Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7400_term_abbrevs.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem7364 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem7365 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (h1). Qed.
Lemma lem7366 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem7367 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem7368 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term2 A P Q x.
Proof. exact (@lem7367 A P Q h1 x). Qed.
Lemma lem7369 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) : (term2 A P Q x) = (term3 A P Q x).
Proof. exact (eq_refl (term2 A P Q x)). Qed.
Lemma lem7370 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P Q x.
Proof. exact (EQ_MP (@lem7369 A P Q x) (@lem7368 A x P Q h1)). Qed.
Lemma lem7371 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem7372 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : term0 A P Q) (h2 : P x) : Q x.
Proof. exact (@lem7370 A x P Q h1 (@lem7371 A P x h2)). Qed.
Lemma lem7373 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : P x) : term4 A P Q x.
Proof. exact (fun h0 : term0 A P Q => @lem7372 A Q P x h0 h1). Qed.
Lemma lem7374 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem7375 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : term0 A P Q) (h2 : P x) : Q x.
Proof. exact (@lem7373 A Q P x h2 (@lem7374 A P Q h1)). Qed.
Lemma lem7376 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P Q x.
Proof. exact (fun h0 : P x => @lem7375 A Q P x h1 h0). Qed.
Lemma lem7377 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (fun x : A => @lem7376 A x P Q h1). Qed.
Lemma lem7378 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem7377 A P Q h0). Qed.
Lemma lem7379 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem7378 A P Q (@lem7364 A P Q h1)). Qed.
Lemma lem7380 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term2 A P Q x.
Proof. exact (@lem7379 A P Q h1 x). Qed.
Lemma lem7381 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) : (term2 A P Q x) = (term3 A P Q x).
Proof. exact (eq_refl (term2 A P Q x)). Qed.
Lemma lem7384 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P Q x.
Proof. exact (EQ_MP (@lem7381 A P Q x) (@lem7380 A x P Q h1)). Qed.
Lemma lem7385 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P Q x.
Proof. exact (@lem7384 A x P Q h1). Qed.
Lemma lem7391 {A : Type'} (P : A -> Prop) (x : A) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem7394 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : (P x) = True.
Proof. exact (EQ_MP (@lem7391 A P x) (@lem7366 A P x h1)). Qed.
Lemma lem7395 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : True = (P x).
Proof. exact (SYM (@lem7394 A P x h1)). Qed.
Lemma lem7396 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (EQ_MP (@lem7395 A P x h1) (@lem0)). Qed.
Lemma lem7397 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : term0 A P Q) (h2 : P x) : Q x.
Proof. exact (@lem7385 A x P Q h1 (@lem7396 A P x h2)). Qed.
Lemma lem7398 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : term0 A P Q) (h2 : P x) : term1 A Q.
Proof. exact (ex_intro (term6 A Q) x (@lem7397 A Q P x h1 h2)). Qed.
Lemma lem7399 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h1 : term0 A P Q) (h2 : term1 A P) : term1 A Q.
Proof. exact (ex_elim (@lem7365 A P h2) (fun x : A => fun h0 : term6 A P x => @lem7398 A Q P x h1 h0)). Qed.
Lemma lem7400 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term7 A P Q.
Proof. exact (fun h0 : term1 A P => @lem7399 A Q P h1 h0). Qed.
