Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm32_term_abbrevs.
Lemma lem10 (q : Prop) (p : Prop) (h1 : term0 q p) : term0 q p.
Proof. exact (h1). Qed.
Lemma lem11 (q : Prop) (p : Prop) (h1 : term0 q p) : q -> p.
Proof. exact (proj2 (@lem10 q p h1)). Qed.
Lemma lem12 (q : Prop) (p : Prop) (h1 : term0 q p) : p -> q.
Proof. exact (proj1 (@lem10 q p h1)). Qed.
Lemma lem13 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem14 (q : Prop) (p : Prop) (h1 : p) (h2 : term0 q p) : q.
Proof. exact (@lem12 q p h2 (@lem13 p h1)). Qed.
Lemma lem15 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem16 (q : Prop) (p : Prop) (h1 : q) (h2 : term0 q p) : p.
Proof. exact (@lem11 q p h2 (@lem15 q h1)). Qed.
Lemma lem17 (q : Prop) (p : Prop) (h1 : term0 q p) : p = q.
Proof. exact (prop_ext (fun h2 : p => @lem14 q p h2 h1) (fun h2 : q => @lem16 q p h2 h1)). Qed.
Lemma lem18 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem19 (q : Prop) : q -> q.
Proof. exact (fun h0 : q => @lem18 q h0). Qed.
Lemma lem20 (p : Prop) (q : Prop) (h1 : p = q) : p = q.
Proof. exact (h1). Qed.
Lemma lem21 (q : Prop) : (imp q) = (imp q).
Proof. exact (eq_refl (imp q)). Qed.
Lemma lem22 (p : Prop) (q : Prop) (h1 : p = q) : (q -> p) = (q -> q).
Proof. exact (MK_COMB (@lem21 q) (@lem20 p q h1)). Qed.
Lemma lem23 (p : Prop) (q : Prop) (h1 : p = q) : (q -> q) = (q -> p).
Proof. exact (SYM (@lem22 p q h1)). Qed.
Lemma lem24 (p : Prop) (q : Prop) (h1 : p = q) : q -> p.
Proof. exact (EQ_MP (@lem23 p q h1) (@lem19 q)). Qed.
Lemma lem25 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem26 (p : Prop) (q : Prop) (h1 : p = q) : (imp p) = (imp q).
Proof. exact (MK_COMB (@lem25) (@lem20 p q h1)). Qed.
Lemma lem27 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem28 (p : Prop) (q : Prop) (h1 : p = q) : (p -> q) = (q -> q).
Proof. exact (MK_COMB (@lem26 p q h1) (@lem27 q)). Qed.
Lemma lem29 (p : Prop) (q : Prop) (h1 : p = q) : (q -> q) = (p -> q).
Proof. exact (SYM (@lem28 p q h1)). Qed.
Lemma lem30 (p : Prop) (q : Prop) (h1 : p = q) : p -> q.
Proof. exact (EQ_MP (@lem29 p q h1) (@lem19 q)). Qed.
Lemma lem31 (p : Prop) (q : Prop) (h1 : p = q) : term0 q p.
Proof. exact (conj (@lem30 p q h1) (@lem24 p q h1)). Qed.
Lemma lem32 (p : Prop) (q : Prop) : (term0 q p) = (p = q).
Proof. exact (prop_ext (fun h1 : term0 q p => @lem17 q p h1) (fun h1 : p = q => @lem31 p q h1)). Qed.
