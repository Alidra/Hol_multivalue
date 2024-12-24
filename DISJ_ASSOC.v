Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJ_ASSOC_term_abbrevs.
Require Import thm32_spec.
Lemma lem650 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term0 t1 t2 t3) : term0 t1 t2 t3.
Proof. exact (h1). Qed.
Lemma lem651 (t1 : Prop) (h1 : t1) : t1.
Proof. exact (h1). Qed.
Lemma lem652 (t2 : Prop) (t3 : Prop) (h1 : t2 \/ t3) : t2 \/ t3.
Proof. exact (h1). Qed.
Lemma lem653 (t2 : Prop) (t1 : Prop) (h1 : t1) : t1 \/ t2.
Proof. exact (or_intro1 (@lem651 t1 h1) t2). Qed.
Lemma lem654 (t2 : Prop) (t3 : Prop) (t1 : Prop) (h1 : t1) : term1 t1 t2 t3.
Proof. exact (or_intro1 (@lem653 t2 t1 h1) t3). Qed.
Lemma lem655 (t2 : Prop) (h1 : t2) : t2.
Proof. exact (h1). Qed.
Lemma lem656 (t3 : Prop) (h1 : t3) : t3.
Proof. exact (h1). Qed.
Lemma lem657 (t1 : Prop) (t2 : Prop) (h1 : t2) : t1 \/ t2.
Proof. exact (or_intro2 t1 (@lem655 t2 h1)). Qed.
Lemma lem658 (t1 : Prop) (t3 : Prop) (t2 : Prop) (h1 : t2) : term1 t1 t2 t3.
Proof. exact (or_intro1 (@lem657 t1 t2 h1) t3). Qed.
Lemma lem659 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : t3) : term1 t1 t2 t3.
Proof. exact (or_intro2 (t1 \/ t2) (@lem656 t3 h1)). Qed.
Lemma lem660 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : t2 \/ t3) : term1 t1 t2 t3.
Proof. exact (or_elim (@lem652 t2 t3 h1) (fun h0 : t2 => @lem658 t1 t3 t2 h0) (fun h0 : t3 => @lem659 t1 t2 t3 h0)). Qed.
Lemma lem661 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term0 t1 t2 t3) : term1 t1 t2 t3.
Proof. exact (or_elim (@lem650 t1 t2 t3 h1) (fun h0 : t1 => @lem654 t2 t3 t1 h0) (fun h0 : t2 \/ t3 => @lem660 t1 t2 t3 h0)). Qed.
Lemma lem662 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term2 t1 t2 t3.
Proof. exact (fun h0 : term0 t1 t2 t3 => @lem661 t1 t2 t3 h0). Qed.
Lemma lem663 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term1 t1 t2 t3) : term1 t1 t2 t3.
Proof. exact (h1). Qed.
Lemma lem664 (t1 : Prop) (t2 : Prop) (h1 : t1 \/ t2) : t1 \/ t2.
Proof. exact (h1). Qed.
Lemma lem665 (t3 : Prop) (h1 : t3) : t3.
Proof. exact (h1). Qed.
Lemma lem666 (t1 : Prop) (h1 : t1) : t1.
Proof. exact (h1). Qed.
Lemma lem667 (t2 : Prop) (h1 : t2) : t2.
Proof. exact (h1). Qed.
Lemma lem668 (t2 : Prop) (t3 : Prop) (t1 : Prop) (h1 : t1) : term0 t1 t2 t3.
Proof. exact (or_intro1 (@lem666 t1 h1) (t2 \/ t3)). Qed.
Lemma lem669 (t3 : Prop) (t2 : Prop) (h1 : t2) : t2 \/ t3.
Proof. exact (or_intro1 (@lem667 t2 h1) t3). Qed.
Lemma lem670 (t1 : Prop) (t3 : Prop) (t2 : Prop) (h1 : t2) : term0 t1 t2 t3.
Proof. exact (or_intro2 t1 (@lem669 t3 t2 h1)). Qed.
Lemma lem671 (t3 : Prop) (t1 : Prop) (t2 : Prop) (h1 : t1 \/ t2) : term0 t1 t2 t3.
Proof. exact (or_elim (@lem664 t1 t2 h1) (fun h0 : t1 => @lem668 t2 t3 t1 h0) (fun h0 : t2 => @lem670 t1 t3 t2 h0)). Qed.
Lemma lem672 (t2 : Prop) (t3 : Prop) (h1 : t3) : t2 \/ t3.
Proof. exact (or_intro2 t2 (@lem665 t3 h1)). Qed.
Lemma lem673 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : t3) : term0 t1 t2 t3.
Proof. exact (or_intro2 t1 (@lem672 t2 t3 h1)). Qed.
Lemma lem674 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : term1 t1 t2 t3) : term0 t1 t2 t3.
Proof. exact (or_elim (@lem663 t1 t2 t3 h1) (fun h0 : t1 \/ t2 => @lem671 t3 t1 t2 h0) (fun h0 : t3 => @lem673 t1 t2 t3 h0)). Qed.
Lemma lem675 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term3 t1 t2 t3.
Proof. exact (fun h0 : term1 t1 t2 t3 => @lem674 t1 t2 t3 h0). Qed.
Lemma lem676 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (conj (@lem662 t1 t2 t3) (@lem675 t1 t2 t3)). Qed.
Lemma lem677 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term0 t1 t2 t3) = (term1 t1 t2 t3)).
Proof. exact (@lem32 (term0 t1 t2 t3) (term1 t1 t2 t3)). Qed.
Lemma lem678 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (EQ_MP (@lem677 t1 t2 t3) (@lem676 t1 t2 t3)). Qed.
Lemma lem683 (t1 : Prop) (t2 : Prop) : term5 t1 t2.
Proof. exact (fun t3 : Prop => @lem678 t1 t2 t3). Qed.
Lemma lem688 (t1 : Prop) : term6 t1.
Proof. exact (fun t2 : Prop => @lem683 t1 t2). Qed.
Lemma lem693 : term7.
Proof. exact (fun t1 : Prop => @lem688 t1). Qed.
