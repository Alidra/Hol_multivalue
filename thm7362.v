Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7362_term_abbrevs.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem7316 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem7317 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (h1). Qed.
Lemma lem7318 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem7319 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term2 A P Q x.
Proof. exact (@lem7318 A P Q h1 x). Qed.
Lemma lem7320 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) : (term2 A P Q x) = (term3 A P Q x).
Proof. exact (eq_refl (term2 A P Q x)). Qed.
Lemma lem7321 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P Q x.
Proof. exact (EQ_MP (@lem7320 A P Q x) (@lem7319 A x P Q h1)). Qed.
Lemma lem7322 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem7323 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : term0 A P Q) (h2 : P x) : Q x.
Proof. exact (@lem7321 A x P Q h1 (@lem7322 A P x h2)). Qed.
Lemma lem7324 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : P x) : term4 A P Q x.
Proof. exact (fun h0 : term0 A P Q => @lem7323 A Q P x h0 h1). Qed.
Lemma lem7325 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem7326 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) (h1 : term0 A P Q) (h2 : P x) : Q x.
Proof. exact (@lem7324 A Q P x h2 (@lem7325 A P Q h1)). Qed.
Lemma lem7327 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P Q x.
Proof. exact (fun h0 : P x => @lem7326 A Q P x h1 h0). Qed.
Lemma lem7328 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (fun x : A => @lem7327 A x P Q h1). Qed.
Lemma lem7329 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem7328 A P Q h0). Qed.
Lemma lem7330 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem7329 A P Q (@lem7316 A P Q h1)). Qed.
Lemma lem7331 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term2 A P Q x.
Proof. exact (@lem7330 A P Q h1 x). Qed.
Lemma lem7332 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) : (term2 A P Q x) = (term3 A P Q x).
Proof. exact (eq_refl (term2 A P Q x)). Qed.
Lemma lem7335 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P Q x.
Proof. exact (EQ_MP (@lem7332 A P Q x) (@lem7331 A x P Q h1)). Qed.
Lemma lem7336 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P Q x.
Proof. exact (@lem7335 A x P Q h1). Qed.
Lemma lem7342 {A : Type'} (x : A) (P : A -> Prop) (h1 : term1 A P) : term6 A P x.
Proof. exact (@lem7317 A P h1 x). Qed.
Lemma lem7343 {A : Type'} (P : A -> Prop) (x : A) : (term6 A P x) = (P x).
Proof. exact (eq_refl (term6 A P x)). Qed.
Lemma lem7344 {A : Type'} (x : A) (P : A -> Prop) (h1 : term1 A P) : P x.
Proof. exact (EQ_MP (@lem7343 A P x) (@lem7342 A x P h1)). Qed.
Lemma lem7345 {A : Type'} (P : A -> Prop) (x : A) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem7348 {A : Type'} (x : A) (P : A -> Prop) (h1 : term1 A P) : (P x) = True.
Proof. exact (EQ_MP (@lem7345 A P x) (@lem7344 A x P h1)). Qed.
Lemma lem7349 {A : Type'} (x : A) (P : A -> Prop) (h1 : term1 A P) : (P x) = True.
Proof. exact (@lem7348 A x P h1). Qed.
Lemma lem7350 {A : Type'} (x : A) (P : A -> Prop) (h1 : term1 A P) : True = (P x).
Proof. exact (SYM (@lem7349 A x P h1)). Qed.
Lemma lem7351 {A : Type'} (x : A) (P : A -> Prop) (h1 : term1 A P) : P x.
Proof. exact (EQ_MP (@lem7350 A x P h1) (@lem0)). Qed.
Lemma lem7352 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P) (h2 : term0 A P Q) : Q x.
Proof. exact (@lem7336 A x P Q h2 (@lem7351 A x P h1)). Qed.
Lemma lem7357 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P) (h2 : term0 A P Q) : term1 A Q.
Proof. exact (fun x : A => @lem7352 A x P Q h1 h2). Qed.
Lemma lem7358 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P) (h2 : term0 A P Q) : (term1 A P) = (term1 A Q).
Proof. exact (prop_ext (fun h3 : term1 A P => @lem7357 A P Q h1 h2) (fun h3 : term1 A Q => @lem7317 A P h1)). Qed.
Lemma lem7359 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P) (h2 : term0 A P Q) : term1 A Q.
Proof. exact (EQ_MP (@lem7358 A P Q h1 h2) (@lem7317 A P h1)). Qed.
Lemma lem7360 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term7 A P Q.
Proof. exact (fun h0 : term1 A P => @lem7359 A P Q h0 h1). Qed.
Lemma lem7361 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : (term0 A P Q) = (term7 A P Q).
Proof. exact (prop_ext (fun h2 : term0 A P Q => @lem7360 A P Q h1) (fun h2 : term7 A P Q => @lem7316 A P Q h1)). Qed.
Lemma lem7362 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term7 A P Q.
Proof. exact (EQ_MP (@lem7361 A P Q h1) (@lem7316 A P Q h1)). Qed.
