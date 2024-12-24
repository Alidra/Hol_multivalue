Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LEFT_OR_DISTRIB_term_abbrevs.
Require Import thm32_spec.
Lemma lem954 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term0 p q r.
Proof. exact (h1). Qed.
Lemma lem955 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : q \/ r.
Proof. exact (proj2 (@lem954 p q r h1)). Qed.
Lemma lem956 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : p.
Proof. exact (proj1 (@lem954 p q r h1)). Qed.
Lemma lem957 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem958 (r : Prop) (h1 : r) : r.
Proof. exact (h1). Qed.
Lemma lem959 (p : Prop) (q : Prop) (r : Prop) (h1 : q) (h2 : term0 p q r) : p /\ q.
Proof. exact (conj (@lem956 p q r h2) (@lem957 q h1)). Qed.
Lemma lem960 (p : Prop) (q : Prop) (r : Prop) (h1 : q) (h2 : term0 p q r) : term1 q p r.
Proof. exact (or_intro1 (@lem959 p q r h1 h2) (p /\ r)). Qed.
Lemma lem961 (p : Prop) (q : Prop) (r : Prop) (h1 : r) (h2 : term0 p q r) : p /\ r.
Proof. exact (conj (@lem956 p q r h2) (@lem958 r h1)). Qed.
Lemma lem962 (p : Prop) (q : Prop) (r : Prop) (h1 : r) (h2 : term0 p q r) : term1 q p r.
Proof. exact (or_intro2 (p /\ q) (@lem961 p q r h1 h2)). Qed.
Lemma lem963 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term1 q p r.
Proof. exact (or_elim (@lem955 p q r h1) (fun h0 : q => @lem960 p q r h0 h1) (fun h0 : r => @lem962 p q r h0 h1)). Qed.
Lemma lem964 (q : Prop) (p : Prop) (r : Prop) : term2 q p r.
Proof. exact (fun h0 : term0 p q r => @lem963 p q r h0). Qed.
Lemma lem965 (q : Prop) (p : Prop) (r : Prop) (h1 : term1 q p r) : term1 q p r.
Proof. exact (h1). Qed.
Lemma lem966 (p : Prop) (q : Prop) (h1 : p /\ q) : p /\ q.
Proof. exact (h1). Qed.
Lemma lem967 (p : Prop) (r : Prop) (h1 : p /\ r) : p /\ r.
Proof. exact (h1). Qed.
Lemma lem969 (p : Prop) (q : Prop) (h1 : p /\ q) : p.
Proof. exact (proj1 (@lem966 p q h1)). Qed.
Lemma lem971 (p : Prop) (r : Prop) (h1 : p /\ r) : p.
Proof. exact (proj1 (@lem967 p r h1)). Qed.
Lemma lem972 (q : Prop) (p : Prop) (r : Prop) (h1 : term1 q p r) : p.
Proof. exact (or_elim (@lem965 q p r h1) (fun h0 : p /\ q => @lem969 p q h0) (fun h0 : p /\ r => @lem971 p r h0)). Qed.
Lemma lem973 (p : Prop) (q : Prop) (h1 : p /\ q) : p /\ q.
Proof. exact (h1). Qed.
Lemma lem974 (p : Prop) (r : Prop) (h1 : p /\ r) : p /\ r.
Proof. exact (h1). Qed.
Lemma lem975 (p : Prop) (q : Prop) (h1 : p /\ q) : q.
Proof. exact (proj2 (@lem973 p q h1)). Qed.
Lemma lem977 (r : Prop) (p : Prop) (q : Prop) (h1 : p /\ q) : q \/ r.
Proof. exact (or_intro1 (@lem975 p q h1) r). Qed.
Lemma lem978 (p : Prop) (r : Prop) (h1 : p /\ r) : r.
Proof. exact (proj2 (@lem974 p r h1)). Qed.
Lemma lem980 (q : Prop) (p : Prop) (r : Prop) (h1 : p /\ r) : q \/ r.
Proof. exact (or_intro2 q (@lem978 p r h1)). Qed.
Lemma lem981 (q : Prop) (p : Prop) (r : Prop) (h1 : term1 q p r) : q \/ r.
Proof. exact (or_elim (@lem965 q p r h1) (fun h0 : p /\ q => @lem977 r p q h0) (fun h0 : p /\ r => @lem980 q p r h0)). Qed.
Lemma lem982 (q : Prop) (p : Prop) (r : Prop) (h1 : term1 q p r) : term0 p q r.
Proof. exact (conj (@lem972 q p r h1) (@lem981 q p r h1)). Qed.
Lemma lem983 (p : Prop) (q : Prop) (r : Prop) : term3 p q r.
Proof. exact (fun h0 : term1 q p r => @lem982 q p r h0). Qed.
Lemma lem984 (p : Prop) (q : Prop) (r : Prop) : term4 p q r.
Proof. exact (conj (@lem964 q p r) (@lem983 p q r)). Qed.
Lemma lem985 (q : Prop) (p : Prop) (r : Prop) : (term4 p q r) = ((term0 p q r) = (term1 q p r)).
Proof. exact (@lem32 (term0 p q r) (term1 q p r)). Qed.
Lemma lem986 (q : Prop) (p : Prop) (r : Prop) : (term0 p q r) = (term1 q p r).
Proof. exact (EQ_MP (@lem985 q p r) (@lem984 p q r)). Qed.
Lemma lem991 (q : Prop) (p : Prop) : term5 q p.
Proof. exact (fun r : Prop => @lem986 q p r). Qed.
Lemma lem996 (p : Prop) : term6 p.
Proof. exact (fun q : Prop => @lem991 q p). Qed.
Lemma lem1001 : term7.
Proof. exact (fun p : Prop => @lem996 p). Qed.
