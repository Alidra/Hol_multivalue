Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm793_term_abbrevs.
Lemma lem767 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term0 p q r.
Proof. exact (h1). Qed.
Lemma lem768 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem769 (q : Prop) (r : Prop) (h1 : q \/ r) : q \/ r.
Proof. exact (h1). Qed.
Lemma lem770 (r : Prop) (p : Prop) (h1 : p) : p \/ r.
Proof. exact (or_intro1 (@lem768 p h1) r). Qed.
Lemma lem771 (q : Prop) (r : Prop) (p : Prop) (h1 : p) : term0 q p r.
Proof. exact (or_intro2 q (@lem770 r p h1)). Qed.
Lemma lem772 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem773 (r : Prop) (h1 : r) : r.
Proof. exact (h1). Qed.
Lemma lem774 (p : Prop) (r : Prop) (q : Prop) (h1 : q) : term0 q p r.
Proof. exact (or_intro1 (@lem772 q h1) (p \/ r)). Qed.
Lemma lem775 (p : Prop) (r : Prop) (h1 : r) : p \/ r.
Proof. exact (or_intro2 p (@lem773 r h1)). Qed.
Lemma lem776 (q : Prop) (p : Prop) (r : Prop) (h1 : r) : term0 q p r.
Proof. exact (or_intro2 q (@lem775 p r h1)). Qed.
Lemma lem777 (p : Prop) (q : Prop) (r : Prop) (h1 : q \/ r) : term0 q p r.
Proof. exact (or_elim (@lem769 q r h1) (fun h0 : q => @lem774 p r q h0) (fun h0 : r => @lem776 q p r h0)). Qed.
Lemma lem778 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term0 q p r.
Proof. exact (or_elim (@lem767 p q r h1) (fun h0 : p => @lem771 q r p h0) (fun h0 : q \/ r => @lem777 p q r h0)). Qed.
Lemma lem779 (q : Prop) (p : Prop) (r : Prop) : term1 q p r.
Proof. exact (fun h0 : term0 p q r => @lem778 p q r h0). Qed.
Lemma lem780 (q : Prop) (p : Prop) (r : Prop) (h1 : term0 q p r) : term0 q p r.
Proof. exact (h1). Qed.
Lemma lem781 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem782 (p : Prop) (r : Prop) (h1 : p \/ r) : p \/ r.
Proof. exact (h1). Qed.
Lemma lem783 (r : Prop) (q : Prop) (h1 : q) : q \/ r.
Proof. exact (or_intro1 (@lem781 q h1) r). Qed.
Lemma lem784 (p : Prop) (r : Prop) (q : Prop) (h1 : q) : term0 p q r.
Proof. exact (or_intro2 p (@lem783 r q h1)). Qed.
Lemma lem785 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem786 (r : Prop) (h1 : r) : r.
Proof. exact (h1). Qed.
Lemma lem787 (q : Prop) (r : Prop) (p : Prop) (h1 : p) : term0 p q r.
Proof. exact (or_intro1 (@lem785 p h1) (q \/ r)). Qed.
Lemma lem788 (q : Prop) (r : Prop) (h1 : r) : q \/ r.
Proof. exact (or_intro2 q (@lem786 r h1)). Qed.
Lemma lem789 (p : Prop) (q : Prop) (r : Prop) (h1 : r) : term0 p q r.
Proof. exact (or_intro2 p (@lem788 q r h1)). Qed.
Lemma lem790 (q : Prop) (p : Prop) (r : Prop) (h1 : p \/ r) : term0 p q r.
Proof. exact (or_elim (@lem782 p r h1) (fun h0 : p => @lem787 q r p h0) (fun h0 : r => @lem789 p q r h0)). Qed.
Lemma lem791 (q : Prop) (p : Prop) (r : Prop) (h1 : term0 q p r) : term0 p q r.
Proof. exact (or_elim (@lem780 q p r h1) (fun h0 : q => @lem784 p r q h0) (fun h0 : p \/ r => @lem790 q p r h0)). Qed.
Lemma lem792 (p : Prop) (q : Prop) (r : Prop) : term1 p q r.
Proof. exact (fun h0 : term0 q p r => @lem791 q p r h0). Qed.
Lemma lem793 (p : Prop) (q : Prop) (r : Prop) : term2 p q r.
Proof. exact (conj (@lem779 q p r) (@lem792 p q r)). Qed.
