Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CONJ_SYM_term_abbrevs.
Require Import thm32_spec.
Lemma lem513 (t1 : Prop) (t2 : Prop) (h1 : t1 /\ t2) : t1 /\ t2.
Proof. exact (h1). Qed.
Lemma lem514 (t1 : Prop) (t2 : Prop) (h1 : t1 /\ t2) : t2.
Proof. exact (proj2 (@lem513 t1 t2 h1)). Qed.
Lemma lem517 (t1 : Prop) (t2 : Prop) (h1 : t1 /\ t2) : t1.
Proof. exact (proj1 (@lem513 t1 t2 h1)). Qed.
Lemma lem518 (t1 : Prop) (t2 : Prop) (h1 : t1 /\ t2) : t2 /\ t1.
Proof. exact (conj (@lem514 t1 t2 h1) (@lem517 t1 t2 h1)). Qed.
Lemma lem519 (t2 : Prop) (t1 : Prop) : term0 t2 t1.
Proof. exact (fun h0 : t1 /\ t2 => @lem518 t1 t2 h0). Qed.
Lemma lem520 (t2 : Prop) (t1 : Prop) (h1 : t2 /\ t1) : t2 /\ t1.
Proof. exact (h1). Qed.
Lemma lem521 (t2 : Prop) (t1 : Prop) (h1 : t2 /\ t1) : t1.
Proof. exact (proj2 (@lem520 t2 t1 h1)). Qed.
Lemma lem524 (t2 : Prop) (t1 : Prop) (h1 : t2 /\ t1) : t2.
Proof. exact (proj1 (@lem520 t2 t1 h1)). Qed.
Lemma lem525 (t2 : Prop) (t1 : Prop) (h1 : t2 /\ t1) : t1 /\ t2.
Proof. exact (conj (@lem521 t2 t1 h1) (@lem524 t2 t1 h1)). Qed.
Lemma lem526 (t1 : Prop) (t2 : Prop) : term0 t1 t2.
Proof. exact (fun h0 : t2 /\ t1 => @lem525 t2 t1 h0). Qed.
Lemma lem527 (t1 : Prop) (t2 : Prop) : term1 t1 t2.
Proof. exact (conj (@lem519 t2 t1) (@lem526 t1 t2)). Qed.
Lemma lem528 (t2 : Prop) (t1 : Prop) : (term1 t1 t2) = ((t1 /\ t2) = (t2 /\ t1)).
Proof. exact (@lem32 (t1 /\ t2) (t2 /\ t1)). Qed.
Lemma lem529 (t2 : Prop) (t1 : Prop) : (t1 /\ t2) = (t2 /\ t1).
Proof. exact (EQ_MP (@lem528 t2 t1) (@lem527 t1 t2)). Qed.
Lemma lem534 (t1 : Prop) : term2 t1.
Proof. exact (fun t2 : Prop => @lem529 t2 t1). Qed.
Lemma lem539 : term3.
Proof. exact (fun t1 : Prop => @lem534 t1). Qed.
