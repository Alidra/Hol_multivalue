Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJ_SYM_term_abbrevs.
Require Import thm32_spec.
Lemma lem694 (t1 : Prop) (t2 : Prop) (h1 : t1 \/ t2) : t1 \/ t2.
Proof. exact (h1). Qed.
Lemma lem695 (t1 : Prop) (h1 : t1) : t1.
Proof. exact (h1). Qed.
Lemma lem696 (t2 : Prop) (h1 : t2) : t2.
Proof. exact (h1). Qed.
Lemma lem697 (t2 : Prop) (t1 : Prop) (h1 : t1) : t2 \/ t1.
Proof. exact (or_intro2 t2 (@lem695 t1 h1)). Qed.
Lemma lem698 (t1 : Prop) (t2 : Prop) (h1 : t2) : t2 \/ t1.
Proof. exact (or_intro1 (@lem696 t2 h1) t1). Qed.
Lemma lem699 (t1 : Prop) (t2 : Prop) (h1 : t1 \/ t2) : t2 \/ t1.
Proof. exact (or_elim (@lem694 t1 t2 h1) (fun h0 : t1 => @lem697 t2 t1 h0) (fun h0 : t2 => @lem698 t1 t2 h0)). Qed.
Lemma lem700 (t2 : Prop) (t1 : Prop) : term0 t2 t1.
Proof. exact (fun h0 : t1 \/ t2 => @lem699 t1 t2 h0). Qed.
Lemma lem701 (t2 : Prop) (t1 : Prop) (h1 : t2 \/ t1) : t2 \/ t1.
Proof. exact (h1). Qed.
Lemma lem702 (t2 : Prop) (h1 : t2) : t2.
Proof. exact (h1). Qed.
Lemma lem703 (t1 : Prop) (h1 : t1) : t1.
Proof. exact (h1). Qed.
Lemma lem704 (t1 : Prop) (t2 : Prop) (h1 : t2) : t1 \/ t2.
Proof. exact (or_intro2 t1 (@lem702 t2 h1)). Qed.
Lemma lem705 (t2 : Prop) (t1 : Prop) (h1 : t1) : t1 \/ t2.
Proof. exact (or_intro1 (@lem703 t1 h1) t2). Qed.
Lemma lem706 (t2 : Prop) (t1 : Prop) (h1 : t2 \/ t1) : t1 \/ t2.
Proof. exact (or_elim (@lem701 t2 t1 h1) (fun h0 : t2 => @lem704 t1 t2 h0) (fun h0 : t1 => @lem705 t2 t1 h0)). Qed.
Lemma lem707 (t1 : Prop) (t2 : Prop) : term0 t1 t2.
Proof. exact (fun h0 : t2 \/ t1 => @lem706 t2 t1 h0). Qed.
Lemma lem708 (t1 : Prop) (t2 : Prop) : term1 t1 t2.
Proof. exact (conj (@lem700 t2 t1) (@lem707 t1 t2)). Qed.
Lemma lem709 (t2 : Prop) (t1 : Prop) : (term1 t1 t2) = ((t1 \/ t2) = (t2 \/ t1)).
Proof. exact (@lem32 (t1 \/ t2) (t2 \/ t1)). Qed.
Lemma lem710 (t2 : Prop) (t1 : Prop) : (t1 \/ t2) = (t2 \/ t1).
Proof. exact (EQ_MP (@lem709 t2 t1) (@lem708 t1 t2)). Qed.
Lemma lem715 (t1 : Prop) : term2 t1.
Proof. exact (fun t2 : Prop => @lem710 t2 t1). Qed.
Lemma lem720 : term3.
Proof. exact (fun t1 : Prop => @lem715 t1). Qed.
