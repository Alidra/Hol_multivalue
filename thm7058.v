Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7058_term_abbrevs.
Lemma lem7033 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : term0 A B C D) : term0 A B C D.
Proof. exact (h1). Qed.
Lemma lem7034 (A : Prop) (C : Prop) (h1 : A /\ C) : A /\ C.
Proof. exact (h1). Qed.
Lemma lem7036 (A : Prop) (C : Prop) (h1 : A /\ C) : A.
Proof. exact (proj1 (@lem7034 A C h1)). Qed.
Lemma lem7038 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : term0 A B C D) : A -> B.
Proof. exact (proj1 (@lem7033 A B C D h1)). Qed.
Lemma lem7045 (A : Prop) (h1 : A) : A.
Proof. exact (h1). Qed.
Lemma lem7046 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : A) (h2 : term0 A B C D) : B.
Proof. exact (@lem7038 A B C D h2 (@lem7045 A h1)). Qed.
Lemma lem7047 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : A /\ C) (h2 : term0 A B C D) : A = B.
Proof. exact (prop_ext (fun h3 : A => @lem7046 A B C D h3 h2) (fun h3 : B => @lem7036 A C h1)). Qed.
Lemma lem7048 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : A /\ C) (h2 : term0 A B C D) : B.
Proof. exact (EQ_MP (@lem7047 A B C D h1 h2) (@lem7036 A C h1)). Qed.
Lemma lem7049 (A : Prop) (C : Prop) (h1 : A /\ C) : C.
Proof. exact (proj2 (@lem7034 A C h1)). Qed.
Lemma lem7051 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : term0 A B C D) : C -> D.
Proof. exact (proj2 (@lem7033 A B C D h1)). Qed.
Lemma lem7053 (C : Prop) (h1 : C) : C.
Proof. exact (h1). Qed.
Lemma lem7054 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : C) (h2 : term0 A B C D) : D.
Proof. exact (@lem7051 A B C D h2 (@lem7053 C h1)). Qed.
Lemma lem7055 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : A /\ C) (h2 : term0 A B C D) : C = D.
Proof. exact (prop_ext (fun h3 : C => @lem7054 A B C D h3 h2) (fun h3 : D => @lem7049 A C h1)). Qed.
Lemma lem7056 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : A /\ C) (h2 : term0 A B C D) : D.
Proof. exact (EQ_MP (@lem7055 A B C D h1 h2) (@lem7049 A C h1)). Qed.
Lemma lem7057 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : A /\ C) (h2 : term0 A B C D) : B /\ D.
Proof. exact (conj (@lem7048 A B C D h1 h2) (@lem7056 A B C D h1 h2)). Qed.
Lemma lem7058 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : term0 A B C D) : term1 A C B D.
Proof. exact (fun h0 : A /\ C => @lem7057 A B C D h0 h1). Qed.
