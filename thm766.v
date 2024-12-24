Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm766_term_abbrevs.
Require Import thm32_spec.
Lemma lem738 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term0 p q r.
Proof. exact (h1). Qed.
Lemma lem739 (p : Prop) (q : Prop) (h1 : p \/ q) : p \/ q.
Proof. exact (h1). Qed.
Lemma lem740 (r : Prop) (h1 : r) : r.
Proof. exact (h1). Qed.
Lemma lem741 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem742 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem743 (q : Prop) (r : Prop) (p : Prop) (h1 : p) : term1 p q r.
Proof. exact (or_intro1 (@lem741 p h1) (q \/ r)). Qed.
Lemma lem744 (r : Prop) (q : Prop) (h1 : q) : q \/ r.
Proof. exact (or_intro1 (@lem742 q h1) r). Qed.
Lemma lem745 (p : Prop) (r : Prop) (q : Prop) (h1 : q) : term1 p q r.
Proof. exact (or_intro2 p (@lem744 r q h1)). Qed.
Lemma lem746 (r : Prop) (p : Prop) (q : Prop) (h1 : p \/ q) : term1 p q r.
Proof. exact (or_elim (@lem739 p q h1) (fun h0 : p => @lem743 q r p h0) (fun h0 : q => @lem745 p r q h0)). Qed.
Lemma lem747 (q : Prop) (r : Prop) (h1 : r) : q \/ r.
Proof. exact (or_intro2 q (@lem740 r h1)). Qed.
Lemma lem748 (p : Prop) (q : Prop) (r : Prop) (h1 : r) : term1 p q r.
Proof. exact (or_intro2 p (@lem747 q r h1)). Qed.
Lemma lem749 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term1 p q r.
Proof. exact (or_elim (@lem738 p q r h1) (fun h0 : p \/ q => @lem746 r p q h0) (fun h0 : r => @lem748 p q r h0)). Qed.
Lemma lem750 (p : Prop) (q : Prop) (r : Prop) : term2 p q r.
Proof. exact (fun h0 : term0 p q r => @lem749 p q r h0). Qed.
Lemma lem751 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : term1 p q r.
Proof. exact (h1). Qed.
Lemma lem752 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem753 (q : Prop) (r : Prop) (h1 : q \/ r) : q \/ r.
Proof. exact (h1). Qed.
Lemma lem754 (q : Prop) (p : Prop) (h1 : p) : p \/ q.
Proof. exact (or_intro1 (@lem752 p h1) q). Qed.
Lemma lem755 (q : Prop) (r : Prop) (p : Prop) (h1 : p) : term0 p q r.
Proof. exact (or_intro1 (@lem754 q p h1) r). Qed.
Lemma lem756 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem757 (r : Prop) (h1 : r) : r.
Proof. exact (h1). Qed.
Lemma lem758 (p : Prop) (q : Prop) (h1 : q) : p \/ q.
Proof. exact (or_intro2 p (@lem756 q h1)). Qed.
Lemma lem759 (p : Prop) (r : Prop) (q : Prop) (h1 : q) : term0 p q r.
Proof. exact (or_intro1 (@lem758 p q h1) r). Qed.
Lemma lem760 (p : Prop) (q : Prop) (r : Prop) (h1 : r) : term0 p q r.
Proof. exact (or_intro2 (p \/ q) (@lem757 r h1)). Qed.
Lemma lem761 (p : Prop) (q : Prop) (r : Prop) (h1 : q \/ r) : term0 p q r.
Proof. exact (or_elim (@lem753 q r h1) (fun h0 : q => @lem759 p r q h0) (fun h0 : r => @lem760 p q r h0)). Qed.
Lemma lem762 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : term0 p q r.
Proof. exact (or_elim (@lem751 p q r h1) (fun h0 : p => @lem755 q r p h0) (fun h0 : q \/ r => @lem761 p q r h0)). Qed.
Lemma lem763 (p : Prop) (q : Prop) (r : Prop) : term3 p q r.
Proof. exact (fun h0 : term1 p q r => @lem762 p q r h0). Qed.
Lemma lem764 (p : Prop) (q : Prop) (r : Prop) : term4 p q r.
Proof. exact (conj (@lem750 p q r) (@lem763 p q r)). Qed.
Lemma lem765 (p : Prop) (q : Prop) (r : Prop) : (term4 p q r) = ((term0 p q r) = (term1 p q r)).
Proof. exact (@lem32 (term0 p q r) (term1 p q r)). Qed.
Lemma lem766 (p : Prop) (q : Prop) (r : Prop) : (term0 p q r) = (term1 p q r).
Proof. exact (EQ_MP (@lem765 p q r) (@lem764 p q r)). Qed.
