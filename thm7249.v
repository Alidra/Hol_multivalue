Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7249_term_abbrevs.
Lemma lem7171 (B : Prop) (A : Prop) (C : Prop) (D : Prop) (h1 : term0 B A C D) : term0 B A C D.
Proof. exact (h1). Qed.
Lemma lem7172 (A : Prop) (C : Prop) (h1 : A -> C) : A -> C.
Proof. exact (h1). Qed.
Lemma lem7173 (B : Prop) (h1 : B) : B.
Proof. exact (h1). Qed.
Lemma lem7174 (B : Prop) (A : Prop) (C : Prop) (D : Prop) (h1 : term0 B A C D) : C -> D.
Proof. exact (proj2 (@lem7171 B A C D h1)). Qed.
Lemma lem7175 (B : Prop) (A : Prop) (C : Prop) (D : Prop) (h1 : term0 B A C D) : B -> A.
Proof. exact (proj1 (@lem7171 B A C D h1)). Qed.
Lemma lem7228 (A : Prop) (h1 : A) : A.
Proof. exact (h1). Qed.
Lemma lem7229 (A : Prop) (C : Prop) (h1 : A) (h2 : A -> C) : C.
Proof. exact (@lem7172 A C h2 (@lem7228 A h1)). Qed.
Lemma lem7238 (B : Prop) (h1 : B) : B.
Proof. exact (h1). Qed.
Lemma lem7239 (B : Prop) (A : Prop) (C : Prop) (D : Prop) (h1 : B) (h2 : term0 B A C D) : A.
Proof. exact (@lem7175 B A C D h2 (@lem7238 B h1)). Qed.
Lemma lem7240 (B : Prop) (A : Prop) (C : Prop) (D : Prop) (h1 : B) (h2 : term0 B A C D) : B = A.
Proof. exact (prop_ext (fun h3 : B => @lem7239 B A C D h1 h2) (fun h3 : A => @lem7173 B h1)). Qed.
Lemma lem7241 (B : Prop) (A : Prop) (C : Prop) (D : Prop) (h1 : B) (h2 : term0 B A C D) : A.
Proof. exact (EQ_MP (@lem7240 B A C D h1 h2) (@lem7173 B h1)). Qed.
Lemma lem7242 (C : Prop) (h1 : C) : C.
Proof. exact (h1). Qed.
Lemma lem7243 (B : Prop) (A : Prop) (C : Prop) (D : Prop) (h1 : C) (h2 : term0 B A C D) : D.
Proof. exact (@lem7174 B A C D h2 (@lem7242 C h1)). Qed.
Lemma lem7244 (B : Prop) (D : Prop) (A : Prop) (C : Prop) (h1 : A) (h2 : term0 B A C D) (h3 : A -> C) : C = D.
Proof. exact (prop_ext (fun h4 : C => @lem7243 B A C D h4 h2) (fun h4 : D => @lem7229 A C h1 h3)). Qed.
Lemma lem7245 (B : Prop) (D : Prop) (A : Prop) (C : Prop) (h1 : A) (h2 : term0 B A C D) (h3 : A -> C) : D.
Proof. exact (EQ_MP (@lem7244 B D A C h1 h2 h3) (@lem7229 A C h1 h3)). Qed.
Lemma lem7246 (B : Prop) (D : Prop) (A : Prop) (C : Prop) (h1 : B) (h2 : term0 B A C D) (h3 : A -> C) : A = D.
Proof. exact (prop_ext (fun h4 : A => @lem7245 B D A C h4 h2 h3) (fun h4 : D => @lem7241 B A C D h1 h2)). Qed.
Lemma lem7247 (B : Prop) (D : Prop) (A : Prop) (C : Prop) (h1 : B) (h2 : term0 B A C D) (h3 : A -> C) : D.
Proof. exact (EQ_MP (@lem7246 B D A C h1 h2 h3) (@lem7241 B A C D h1 h2)). Qed.
Lemma lem7248 (B : Prop) (D : Prop) (A : Prop) (C : Prop) (h1 : term0 B A C D) (h2 : A -> C) : B -> D.
Proof. exact (fun h0 : B => @lem7247 B D A C h0 h1 h2). Qed.
Lemma lem7249 (B : Prop) (A : Prop) (C : Prop) (D : Prop) (h1 : term0 B A C D) : term1 A C B D.
Proof. exact (fun h0 : A -> C => @lem7248 B D A C h1 h0). Qed.
