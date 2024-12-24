Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RIGHT_FORALL_IMP_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem6469 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem6470 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem6471 {A : Type'} (_309 : A) (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term1 A P Q _309.
Proof. exact (@lem6469 A P Q h1 _309). Qed.
Lemma lem6472 {A : Type'} (P : Prop) (Q : A -> Prop) (_309 : A) : (term1 A P Q _309) = (term2 A P Q _309).
Proof. exact (eq_refl (term1 A P Q _309)). Qed.
Lemma lem6473 {A : Type'} (_309 : A) (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term2 A P Q _309.
Proof. exact (EQ_MP (@lem6472 A P Q _309) (@lem6471 A _309 P Q h1)). Qed.
Lemma lem6477 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem6478 {A : Type'} (_309 : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term0 A P Q) : Q _309.
Proof. exact (@lem6473 A _309 P Q h2 (@lem6477 P h1)). Qed.
Lemma lem6479 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term0 A P Q) : Q x.
Proof. exact (@lem6478 A x P Q h1 h2). Qed.
Lemma lem6480 (P : Prop) (h1 : P) : P.
Proof. exact (@lem6470 P h1). Qed.
Lemma lem6482 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term0 A P Q) : P = (Q x).
Proof. exact (prop_ext (fun h3 : P => @lem6479 A x P Q h1 h2) (fun h3 : Q x => @lem6480 P h1)). Qed.
Lemma lem6483 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term0 A P Q) : Q x.
Proof. exact (EQ_MP (@lem6482 A x P Q h1 h2) (@lem6480 P h1)). Qed.
Lemma lem6487 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem6469 A P Q h1). Qed.
Lemma lem6488 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term0 A P Q) : (term0 A P Q) = (Q x).
Proof. exact (prop_ext (fun h3 : term0 A P Q => @lem6483 A x P Q h1 h2) (fun h3 : Q x => @lem6487 A P Q h2)). Qed.
Lemma lem6489 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term0 A P Q) : Q x.
Proof. exact (EQ_MP (@lem6488 A x P Q h1 h2) (@lem6487 A P Q h2)). Qed.
Lemma lem6494 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term0 A P Q) : term3 A Q.
Proof. exact (fun x : A => @lem6489 A x P Q h1 h2). Qed.
Lemma lem6495 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term4 A P Q.
Proof. exact (fun h0 : P => @lem6494 A P Q h0 h1). Qed.
Lemma lem6496 {A : Type'} (P : Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem6495 A P Q h0). Qed.
Lemma lem6497 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (h1). Qed.
Lemma lem6498 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem6499 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem6500 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term4 A P Q) : term3 A Q.
Proof. exact (@lem6497 A P Q h2 (@lem6499 P h1)). Qed.
Lemma lem6501 {A : Type'} (_311 : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term4 A P Q) : term6 A Q _311.
Proof. exact (@lem6500 A P Q h1 h2 _311). Qed.
Lemma lem6502 {A : Type'} (Q : A -> Prop) (_311 : A) : (term6 A Q _311) = (Q _311).
Proof. exact (eq_refl (term6 A Q _311)). Qed.
Lemma lem6503 {A : Type'} (_311 : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term4 A P Q) : Q _311.
Proof. exact (EQ_MP (@lem6502 A Q _311) (@lem6501 A _311 P Q h1 h2)). Qed.
Lemma lem6504 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term4 A P Q) : Q x.
Proof. exact (@lem6503 A x P Q h1 h2). Qed.
Lemma lem6509 (P : Prop) (h1 : P) : P.
Proof. exact (@lem6498 P h1). Qed.
Lemma lem6511 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term4 A P Q) : P = (Q x).
Proof. exact (prop_ext (fun h3 : P => @lem6504 A x P Q h1 h2) (fun h3 : Q x => @lem6509 P h1)). Qed.
Lemma lem6512 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : P) (h2 : term4 A P Q) : Q x.
Proof. exact (EQ_MP (@lem6511 A x P Q h1 h2) (@lem6509 P h1)). Qed.
Lemma lem6513 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term2 A P Q x.
Proof. exact (fun h0 : P => @lem6512 A x P Q h0 h1). Qed.
Lemma lem6518 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term0 A P Q.
Proof. exact (fun x : A => @lem6513 A x P Q h1). Qed.
Lemma lem6519 {A : Type'} (P : Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (fun h0 : term4 A P Q => @lem6518 A P Q h0). Qed.
Lemma lem6520 {A : Type'} (P : Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (@lem6496 A P Q). Qed.
Lemma lem6521 {A : Type'} (P : Prop) (Q : A -> Prop) : term8 A P Q.
Proof. exact (conj (@lem6520 A P Q) (@lem6519 A P Q)). Qed.
Lemma lem6522 {A : Type'} (P : Prop) (Q : A -> Prop) : (term8 A P Q) = ((term0 A P Q) = (term4 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term4 A P Q)). Qed.
Lemma lem6523 {A : Type'} (P : Prop) (Q : A -> Prop) : (term0 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem6522 A P Q) (@lem6521 A P Q)). Qed.
Lemma lem6528 {A : Type'} (P : Prop) : term9 A P.
Proof. exact (fun Q : A -> Prop => @lem6523 A P Q). Qed.
Lemma lem6533 {A : Type'} : term10 A.
Proof. exact (fun P : Prop => @lem6528 A P). Qed.
Lemma lem6534 {A : Type'} : term10 A.
Proof. exact (@lem6533 A). Qed.
