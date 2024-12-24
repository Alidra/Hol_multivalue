Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7932316_term_abbrevs.
Require Import HAS_SIZE_IMAGE_INJ_spec.
Lemma lem7932289 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7932290 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term1 A B f.
Proof. exact (@lem7932289 A B h1 f). Qed.
Lemma lem7932291 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem7932292 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (EQ_MP (@lem7932291 A B f) (@lem7932290 A B f h1)). Qed.
Lemma lem7932293 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term3 A B f s.
Proof. exact (@lem7932292 A B f h1 s). Qed.
Lemma lem7932294 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem7932295 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (EQ_MP (@lem7932294 A B f s) (@lem7932293 A B f s h1)). Qed.
Lemma lem7932296 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) : term5 A B f s n.
Proof. exact (@lem7932295 A B f s h1 n). Qed.
Lemma lem7932297 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term5 A B f s n) = (term6 A B f s n).
Proof. exact (eq_refl (term5 A B f s n)). Qed.
Lemma lem7932298 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) : term6 A B f s n.
Proof. exact (EQ_MP (@lem7932297 A B f s n) (@lem7932296 A B f s n h1)). Qed.
Lemma lem7932299 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term7 A B f s n) : term7 A B f s n.
Proof. exact (h1). Qed.
Lemma lem7932300 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) (h2 : term7 A B f s n) : term8 A B f s n.
Proof. exact (@lem7932298 A B f s n h1 (@lem7932299 A B f s n h2)). Qed.
Lemma lem7932301 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term7 A B f s n) : term9 A B f s n.
Proof. exact (fun h0 : term0 A B => @lem7932300 A B f s n h0 h1). Qed.
Lemma lem7932302 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7932303 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) (h2 : term7 A B f s n) : term8 A B f s n.
Proof. exact (@lem7932301 A B f s n h2 (@lem7932302 A B h1)). Qed.
Lemma lem7932304 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) : term6 A B f s n.
Proof. exact (fun h0 : term7 A B f s n => @lem7932303 A B f s n h1 h0). Qed.
Lemma lem7932305 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (fun n : nat => @lem7932304 A B f s n h1). Qed.
Lemma lem7932306 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (fun s : A -> Prop => @lem7932305 A B f s h1). Qed.
Lemma lem7932307 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun f : A -> B => @lem7932306 A B f h1). Qed.
Lemma lem7932308 {A B : Type'} : term10 A B.
Proof. exact (fun h0 : term0 A B => @lem7932307 A B h0). Qed.
Lemma lem7932309 {A B : Type'} : term0 A B.
Proof. exact (@lem7932308 A B (@lem4004559 A B)). Qed.
Lemma lem7932310 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem7932309 A B f). Qed.
Lemma lem7932311 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem7932312 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem7932311 A B f) (@lem7932310 A B f)). Qed.
Lemma lem7932313 {A B : Type'} (f : A -> B) (s : A -> Prop) : term3 A B f s.
Proof. exact (@lem7932312 A B f s). Qed.
Lemma lem7932314 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem7932315 {A B : Type'} (f : A -> B) (s : A -> Prop) : term4 A B f s.
Proof. exact (EQ_MP (@lem7932314 A B f s) (@lem7932313 A B f s)). Qed.
Lemma lem7932316 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term5 A B f s n.
Proof. exact (@lem7932315 A B f s n). Qed.
