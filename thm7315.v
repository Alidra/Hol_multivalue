Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7315_term_abbrevs.
Require Import NOT_DEF_spec.
Require Import thm69_spec.
Lemma lem7287 (B : Prop) (A : Prop) (h1 : B -> A) : B -> A.
Proof. exact (h1). Qed.
Lemma lem7288 (A : Prop) (h1 : ~ A) : ~ A.
Proof. exact (h1). Qed.
Lemma lem7289 (B : Prop) (h1 : B) : B.
Proof. exact (h1). Qed.
Lemma lem7290 (A : Prop) : A = A.
Proof. exact (eq_refl A). Qed.
Lemma lem7291 (A : Prop) : (~ A) = (term0 A).
Proof. exact (MK_COMB (@lem56) (@lem7290 A)). Qed.
Lemma lem7292 (A : Prop) : (term0 A) = (A -> False).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem7293 (A : Prop) : (term1 A) = (term1 A).
Proof. exact (eq_refl (term1 A)). Qed.
Lemma lem7294 (A : Prop) : ((~ A) = (term0 A)) = ((~ A) = (A -> False)).
Proof. exact (MK_COMB (@lem7293 A) (@lem7292 A)). Qed.
Lemma lem7295 (A : Prop) : (~ A) = (A -> False).
Proof. exact (EQ_MP (@lem7294 A) (@lem7291 A)). Qed.
Lemma lem7296 (A : Prop) (h1 : ~ A) : A -> False.
Proof. exact (EQ_MP (@lem7295 A) (@lem7288 A h1)). Qed.
Lemma lem7297 (A : Prop) (h1 : A) : A.
Proof. exact (h1). Qed.
Lemma lem7298 (A : Prop) (h1 : A) (h2 : ~ A) : False.
Proof. exact (@lem7296 A h2 (@lem7297 A h1)). Qed.
Lemma lem7305 (B : Prop) (h1 : B) : B.
Proof. exact (h1). Qed.
Lemma lem7306 (B : Prop) (A : Prop) (h1 : B) (h2 : B -> A) : A.
Proof. exact (@lem7287 B A h2 (@lem7305 B h1)). Qed.
Lemma lem7307 (B : Prop) (A : Prop) (h1 : B) (h2 : B -> A) : B = A.
Proof. exact (prop_ext (fun h3 : B => @lem7306 B A h1 h2) (fun h3 : A => @lem7289 B h1)). Qed.
Lemma lem7308 (B : Prop) (A : Prop) (h1 : B) (h2 : B -> A) : A.
Proof. exact (EQ_MP (@lem7307 B A h1 h2) (@lem7289 B h1)). Qed.
Lemma lem7309 (B : Prop) (A : Prop) (h1 : B) (h2 : ~ A) (h3 : B -> A) : A = False.
Proof. exact (prop_ext (fun h4 : A => @lem7298 A h4 h2) (fun h4 : False => @lem7308 B A h1 h3)). Qed.
Lemma lem7310 (B : Prop) (A : Prop) (h1 : B) (h2 : ~ A) (h3 : B -> A) : False.
Proof. exact (EQ_MP (@lem7309 B A h1 h2 h3) (@lem7308 B A h1 h3)). Qed.
Lemma lem7311 (B : Prop) (A : Prop) (h1 : ~ A) (h2 : B -> A) : B -> False.
Proof. exact (fun h0 : B => @lem7310 B A h0 h1 h2). Qed.
Lemma lem7312 (B : Prop) : (B -> False) = (~ B).
Proof. exact (@lem69 B). Qed.
Lemma lem7313 (B : Prop) (A : Prop) (h1 : ~ A) (h2 : B -> A) : ~ B.
Proof. exact (EQ_MP (@lem7312 B) (@lem7311 B A h1 h2)). Qed.
Lemma lem7314 (B : Prop) (A : Prop) (h1 : B -> A) : term2 A B.
Proof. exact (fun h0 : ~ A => @lem7313 B A h0 h1). Qed.
Lemma lem7315 (A : Prop) (B : Prop) : term3 A B.
Proof. exact (fun h0 : B -> A => @lem7314 B A h0). Qed.
