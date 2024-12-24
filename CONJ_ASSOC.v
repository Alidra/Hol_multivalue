Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CONJ_ASSOC_term_abbrevs.
Require Import thm32_spec.
Lemma lem467 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term0 t1 t2 t3) : term0 t1 t2 t3.
Proof. exact (h1). Qed.
Lemma lem469 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term0 t1 t2 t3) : t1.
Proof. exact (proj1 (@lem467 t1 t2 t3 h1)). Qed.
Lemma lem470 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term0 t1 t2 t3) : t2 /\ t3.
Proof. exact (proj2 (@lem467 t1 t2 t3 h1)). Qed.
Lemma lem473 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term0 t1 t2 t3) : t2.
Proof. exact (proj1 (@lem470 t1 t2 t3 h1)). Qed.
Lemma lem474 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term0 t1 t2 t3) : t1 /\ t2.
Proof. exact (conj (@lem469 t1 t2 t3 h1) (@lem473 t1 t2 t3 h1)). Qed.
Lemma lem475 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term0 t1 t2 t3) : t2 /\ t3.
Proof. exact (proj2 (@lem467 t1 t2 t3 h1)). Qed.
Lemma lem477 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term0 t1 t2 t3) : t3.
Proof. exact (proj2 (@lem475 t1 t2 t3 h1)). Qed.
Lemma lem479 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term0 t1 t2 t3) : term1 t1 t2 t3.
Proof. exact (conj (@lem474 t1 t2 t3 h1) (@lem477 t1 t2 t3 h1)). Qed.
Lemma lem480 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term2 t1 t2 t3.
Proof. exact (fun h0 : term0 t1 t2 t3 => @lem479 t1 t2 t3 h0). Qed.
Lemma lem481 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term1 t1 t2 t3) : term1 t1 t2 t3.
Proof. exact (h1). Qed.
Lemma lem483 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term1 t1 t2 t3) : t1 /\ t2.
Proof. exact (proj1 (@lem481 t1 t2 t3 h1)). Qed.
Lemma lem485 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term1 t1 t2 t3) : t1.
Proof. exact (proj1 (@lem483 t1 t2 t3 h1)). Qed.
Lemma lem487 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term1 t1 t2 t3) : t1 /\ t2.
Proof. exact (proj1 (@lem481 t1 t2 t3 h1)). Qed.
Lemma lem488 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term1 t1 t2 t3) : t2.
Proof. exact (proj2 (@lem487 t1 t2 t3 h1)). Qed.
Lemma lem490 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term1 t1 t2 t3) : t3.
Proof. exact (proj2 (@lem481 t1 t2 t3 h1)). Qed.
Lemma lem492 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term1 t1 t2 t3) : t2 /\ t3.
Proof. exact (conj (@lem488 t1 t2 t3 h1) (@lem490 t1 t2 t3 h1)). Qed.
Lemma lem493 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term1 t1 t2 t3) : term0 t1 t2 t3.
Proof. exact (conj (@lem485 t1 t2 t3 h1) (@lem492 t1 t2 t3 h1)). Qed.
Lemma lem494 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term3 t1 t2 t3.
Proof. exact (fun h0 : term1 t1 t2 t3 => @lem493 t1 t2 t3 h0). Qed.
Lemma lem495 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (conj (@lem480 t1 t2 t3) (@lem494 t1 t2 t3)). Qed.
Lemma lem496 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term0 t1 t2 t3) = (term1 t1 t2 t3)).
Proof. exact (@lem32 (term0 t1 t2 t3) (term1 t1 t2 t3)). Qed.
Lemma lem497 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (EQ_MP (@lem496 t1 t2 t3) (@lem495 t1 t2 t3)). Qed.
Lemma lem502 (t1 : Prop) (t2 : Prop) : term5 t1 t2.
Proof. exact (fun t3 : Prop => @lem497 t1 t2 t3). Qed.
Lemma lem507 (t1 : Prop) : term6 t1.
Proof. exact (fun t2 : Prop => @lem502 t1 t2). Qed.
Lemma lem512 : term7.
Proof. exact (fun t1 : Prop => @lem507 t1). Qed.
