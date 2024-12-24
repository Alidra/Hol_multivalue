Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7931514_term_abbrevs.
Require Import HAS_SIZE_IMAGE_INJ_spec.
Lemma lem7931487 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7931488 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term1 A B f.
Proof. exact (@lem7931487 A B h1 f). Qed.
Lemma lem7931489 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem7931490 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (EQ_MP (@lem7931489 A B f) (@lem7931488 A B f h1)). Qed.
Lemma lem7931491 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term3 A B f s.
Proof. exact (@lem7931490 A B f h1 s). Qed.
Lemma lem7931492 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem7931493 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (EQ_MP (@lem7931492 A B f s) (@lem7931491 A B f s h1)). Qed.
Lemma lem7931494 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) : term5 A B f s n.
Proof. exact (@lem7931493 A B f s h1 n). Qed.
Lemma lem7931495 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term5 A B f s n) = (term6 A B f s n).
Proof. exact (eq_refl (term5 A B f s n)). Qed.
Lemma lem7931496 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) : term6 A B f s n.
Proof. exact (EQ_MP (@lem7931495 A B f s n) (@lem7931494 A B f s n h1)). Qed.
Lemma lem7931497 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term7 A B f s n) : term7 A B f s n.
Proof. exact (h1). Qed.
Lemma lem7931498 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) (h2 : term7 A B f s n) : term8 A B f s n.
Proof. exact (@lem7931496 A B f s n h1 (@lem7931497 A B f s n h2)). Qed.
Lemma lem7931499 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term7 A B f s n) : term9 A B f s n.
Proof. exact (fun h0 : term0 A B => @lem7931498 A B f s n h0 h1). Qed.
Lemma lem7931500 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7931501 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) (h2 : term7 A B f s n) : term8 A B f s n.
Proof. exact (@lem7931499 A B f s n h2 (@lem7931500 A B h1)). Qed.
Lemma lem7931502 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) : term6 A B f s n.
Proof. exact (fun h0 : term7 A B f s n => @lem7931501 A B f s n h1 h0). Qed.
Lemma lem7931503 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (fun n : nat => @lem7931502 A B f s n h1). Qed.
Lemma lem7931504 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (fun s : A -> Prop => @lem7931503 A B f s h1). Qed.
Lemma lem7931505 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun f : A -> B => @lem7931504 A B f h1). Qed.
Lemma lem7931506 {A B : Type'} : term10 A B.
Proof. exact (fun h0 : term0 A B => @lem7931505 A B h0). Qed.
Lemma lem7931507 {A B : Type'} : term0 A B.
Proof. exact (@lem7931506 A B (@lem4004559 A B)). Qed.
Lemma lem7931508 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem7931507 A B f). Qed.
Lemma lem7931509 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem7931510 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem7931509 A B f) (@lem7931508 A B f)). Qed.
Lemma lem7931511 {A B : Type'} (f : A -> B) (s : A -> Prop) : term3 A B f s.
Proof. exact (@lem7931510 A B f s). Qed.
Lemma lem7931512 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem7931513 {A B : Type'} (f : A -> B) (s : A -> Prop) : term4 A B f s.
Proof. exact (EQ_MP (@lem7931512 A B f s) (@lem7931511 A B f s)). Qed.
Lemma lem7931514 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term5 A B f s n.
Proof. exact (@lem7931513 A B f s n). Qed.
