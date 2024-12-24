Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7129_term_abbrevs.
Lemma lem7092 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : term0 A B C D) : term0 A B C D.
Proof. exact (h1). Qed.
Lemma lem7093 (A : Prop) (C : Prop) (h1 : A \/ C) : A \/ C.
Proof. exact (h1). Qed.
Lemma lem7094 (A : Prop) (h1 : A) : A.
Proof. exact (h1). Qed.
Lemma lem7095 (C : Prop) (h1 : C) : C.
Proof. exact (h1). Qed.
Lemma lem7097 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : term0 A B C D) : A -> B.
Proof. exact (proj1 (@lem7092 A B C D h1)). Qed.
Lemma lem7104 (A : Prop) (h1 : A) : A.
Proof. exact (h1). Qed.
Lemma lem7105 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : A) (h2 : term0 A B C D) : B.
Proof. exact (@lem7097 A B C D h2 (@lem7104 A h1)). Qed.
Lemma lem7106 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : A) (h2 : term0 A B C D) : A = B.
Proof. exact (prop_ext (fun h3 : A => @lem7105 A B C D h1 h2) (fun h3 : B => @lem7094 A h1)). Qed.
Lemma lem7107 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : A) (h2 : term0 A B C D) : B.
Proof. exact (EQ_MP (@lem7106 A B C D h1 h2) (@lem7094 A h1)). Qed.
Lemma lem7108 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : A) (h2 : term0 A B C D) : B \/ D.
Proof. exact (or_intro1 (@lem7107 A B C D h1 h2) D). Qed.
Lemma lem7109 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : term0 A B C D) : C -> D.
Proof. exact (proj2 (@lem7092 A B C D h1)). Qed.
Lemma lem7123 (C : Prop) (h1 : C) : C.
Proof. exact (h1). Qed.
Lemma lem7124 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : C) (h2 : term0 A B C D) : D.
Proof. exact (@lem7109 A B C D h2 (@lem7123 C h1)). Qed.
Lemma lem7125 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : C) (h2 : term0 A B C D) : C = D.
Proof. exact (prop_ext (fun h3 : C => @lem7124 A B C D h1 h2) (fun h3 : D => @lem7095 C h1)). Qed.
Lemma lem7126 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : C) (h2 : term0 A B C D) : D.
Proof. exact (EQ_MP (@lem7125 A B C D h1 h2) (@lem7095 C h1)). Qed.
Lemma lem7127 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : C) (h2 : term0 A B C D) : B \/ D.
Proof. exact (or_intro2 B (@lem7126 A B C D h1 h2)). Qed.
Lemma lem7128 (B : Prop) (D : Prop) (A : Prop) (C : Prop) (h1 : term0 A B C D) (h2 : A \/ C) : B \/ D.
Proof. exact (or_elim (@lem7093 A C h2) (fun h0 : A => @lem7108 A B C D h0 h1) (fun h0 : C => @lem7127 A B C D h0 h1)). Qed.
Lemma lem7129 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : term0 A B C D) : term1 A C B D.
Proof. exact (fun h0 : A \/ C => @lem7128 B D A C h1 h0). Qed.
