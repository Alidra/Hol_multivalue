Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RIGHT_IMP_FORALL_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem6353 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem6354 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem6355 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem6356 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term0 A P Q) : term1 A Q.
Proof. exact (@lem6353 A P Q h2 (@lem6355 P h1)). Qed.
Lemma lem6357 {A : Type'} (_298 : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term0 A P Q) : term2 A Q _298.
Proof. exact (@lem6356 A P Q h1 h2 _298). Qed.
Lemma lem6358 {A : Type'} (Q : A -> Prop) (_298 : A) : (term2 A Q _298) = (Q _298).
Proof. exact (eq_refl (term2 A Q _298)). Qed.
Lemma lem6359 {A : Type'} (_298 : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term0 A P Q) : Q _298.
Proof. exact (EQ_MP (@lem6358 A Q _298) (@lem6357 A _298 P Q h1 h2)). Qed.
Lemma lem6360 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term0 A P Q) : Q x.
Proof. exact (@lem6359 A x P Q h1 h2). Qed.
Lemma lem6365 (P : Prop) (h1 : P) : P.
Proof. exact (@lem6354 P h1). Qed.
Lemma lem6367 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term0 A P Q) : P = (Q x).
Proof. exact (prop_ext (fun h3 : P => @lem6360 A x P Q h1 h2) (fun h3 : Q x => @lem6365 P h1)). Qed.
Lemma lem6368 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term0 A P Q) : Q x.
Proof. exact (EQ_MP (@lem6367 A x P Q h1 h2) (@lem6365 P h1)). Qed.
Lemma lem6369 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P Q x.
Proof. exact (fun h0 : P => @lem6368 A x P Q h0 h1). Qed.
Lemma lem6374 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term4 A P Q.
Proof. exact (fun x : A => @lem6369 A x P Q h1). Qed.
Lemma lem6375 {A : Type'} (P : Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem6374 A P Q h0). Qed.
Lemma lem6376 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (h1). Qed.
Lemma lem6377 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem6378 {A : Type'} (_299 : A) (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term6 A P Q _299.
Proof. exact (@lem6376 A P Q h1 _299). Qed.
Lemma lem6379 {A : Type'} (P : Prop) (Q : A -> Prop) (_299 : A) : (term6 A P Q _299) = (term3 A P Q _299).
Proof. exact (eq_refl (term6 A P Q _299)). Qed.
Lemma lem6380 {A : Type'} (_299 : A) (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term3 A P Q _299.
Proof. exact (EQ_MP (@lem6379 A P Q _299) (@lem6378 A _299 P Q h1)). Qed.
Lemma lem6384 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem6385 {A : Type'} (_299 : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term4 A P Q) : Q _299.
Proof. exact (@lem6380 A _299 P Q h2 (@lem6384 P h1)). Qed.
Lemma lem6386 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term4 A P Q) : Q x.
Proof. exact (@lem6385 A x P Q h1 h2). Qed.
Lemma lem6387 (P : Prop) (h1 : P) : P.
Proof. exact (@lem6377 P h1). Qed.
Lemma lem6389 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term4 A P Q) : P = (Q x).
Proof. exact (prop_ext (fun h3 : P => @lem6386 A x P Q h1 h2) (fun h3 : Q x => @lem6387 P h1)). Qed.
Lemma lem6390 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term4 A P Q) : Q x.
Proof. exact (EQ_MP (@lem6389 A x P Q h1 h2) (@lem6387 P h1)). Qed.
Lemma lem6394 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (@lem6376 A P Q h1). Qed.
Lemma lem6395 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term4 A P Q) : (term4 A P Q) = (Q x).
Proof. exact (prop_ext (fun h3 : term4 A P Q => @lem6390 A x P Q h1 h2) (fun h3 : Q x => @lem6394 A P Q h2)). Qed.
Lemma lem6396 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term4 A P Q) : Q x.
Proof. exact (EQ_MP (@lem6395 A x P Q h1 h2) (@lem6394 A P Q h2)). Qed.
Lemma lem6401 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term4 A P Q) : term1 A Q.
Proof. exact (fun x : A => @lem6396 A x P Q h1 h2). Qed.
Lemma lem6402 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term0 A P Q.
Proof. exact (fun h0 : P => @lem6401 A P Q h0 h1). Qed.
Lemma lem6403 {A : Type'} (P : Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (fun h0 : term4 A P Q => @lem6402 A P Q h0). Qed.
Lemma lem6404 {A : Type'} (P : Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (@lem6375 A P Q). Qed.
Lemma lem6405 {A : Type'} (P : Prop) (Q : A -> Prop) : term8 A P Q.
Proof. exact (conj (@lem6404 A P Q) (@lem6403 A P Q)). Qed.
Lemma lem6406 {A : Type'} (P : Prop) (Q : A -> Prop) : (term8 A P Q) = ((term0 A P Q) = (term4 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term4 A P Q)). Qed.
Lemma lem6407 {A : Type'} (P : Prop) (Q : A -> Prop) : (term0 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem6406 A P Q) (@lem6405 A P Q)). Qed.
Lemma lem6412 {A : Type'} (P : Prop) : term9 A P.
Proof. exact (fun Q : A -> Prop => @lem6407 A P Q). Qed.
Lemma lem6417 {A : Type'} : term10 A.
Proof. exact (fun P : Prop => @lem6412 A P). Qed.
Lemma lem6418 {A : Type'} : term10 A.
Proof. exact (@lem6417 A). Qed.
