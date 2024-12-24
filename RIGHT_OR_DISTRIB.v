Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RIGHT_OR_DISTRIB_term_abbrevs.
Require Import thm32_spec.
Lemma lem1002 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term0 p q r.
Proof. exact (h1). Qed.
Lemma lem1003 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : r.
Proof. exact (proj2 (@lem1002 p q r h1)). Qed.
Lemma lem1004 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : p \/ q.
Proof. exact (proj1 (@lem1002 p q r h1)). Qed.
Lemma lem1005 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem1006 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem1007 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : term0 p q r) : p /\ r.
Proof. exact (conj (@lem1005 p h1) (@lem1003 p q r h2)). Qed.
Lemma lem1008 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : term0 p q r) : term1 p q r.
Proof. exact (or_intro1 (@lem1007 p q r h1 h2) (q /\ r)). Qed.
Lemma lem1009 (p : Prop) (q : Prop) (r : Prop) (h1 : q) (h2 : term0 p q r) : q /\ r.
Proof. exact (conj (@lem1006 q h1) (@lem1003 p q r h2)). Qed.
Lemma lem1010 (p : Prop) (q : Prop) (r : Prop) (h1 : q) (h2 : term0 p q r) : term1 p q r.
Proof. exact (or_intro2 (p /\ r) (@lem1009 p q r h1 h2)). Qed.
Lemma lem1011 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term1 p q r.
Proof. exact (or_elim (@lem1004 p q r h1) (fun h0 : p => @lem1008 p q r h0 h1) (fun h0 : q => @lem1010 p q r h0 h1)). Qed.
Lemma lem1012 (p : Prop) (q : Prop) (r : Prop) : term2 p q r.
Proof. exact (fun h0 : term0 p q r => @lem1011 p q r h0). Qed.
Lemma lem1013 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : term1 p q r.
Proof. exact (h1). Qed.
Lemma lem1014 (p : Prop) (r : Prop) (h1 : p /\ r) : p /\ r.
Proof. exact (h1). Qed.
Lemma lem1015 (q : Prop) (r : Prop) (h1 : q /\ r) : q /\ r.
Proof. exact (h1). Qed.
Lemma lem1017 (p : Prop) (r : Prop) (h1 : p /\ r) : p.
Proof. exact (proj1 (@lem1014 p r h1)). Qed.
Lemma lem1018 (q : Prop) (p : Prop) (r : Prop) (h1 : p /\ r) : p \/ q.
Proof. exact (or_intro1 (@lem1017 p r h1) q). Qed.
Lemma lem1020 (q : Prop) (r : Prop) (h1 : q /\ r) : q.
Proof. exact (proj1 (@lem1015 q r h1)). Qed.
Lemma lem1021 (p : Prop) (q : Prop) (r : Prop) (h1 : q /\ r) : p \/ q.
Proof. exact (or_intro2 p (@lem1020 q r h1)). Qed.
Lemma lem1022 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : p \/ q.
Proof. exact (or_elim (@lem1013 p q r h1) (fun h0 : p /\ r => @lem1018 q p r h0) (fun h0 : q /\ r => @lem1021 p q r h0)). Qed.
Lemma lem1023 (p : Prop) (r : Prop) (h1 : p /\ r) : p /\ r.
Proof. exact (h1). Qed.
Lemma lem1024 (q : Prop) (r : Prop) (h1 : q /\ r) : q /\ r.
Proof. exact (h1). Qed.
Lemma lem1025 (p : Prop) (r : Prop) (h1 : p /\ r) : r.
Proof. exact (proj2 (@lem1023 p r h1)). Qed.
Lemma lem1027 (q : Prop) (r : Prop) (h1 : q /\ r) : r.
Proof. exact (proj2 (@lem1024 q r h1)). Qed.
Lemma lem1029 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : r.
Proof. exact (or_elim (@lem1013 p q r h1) (fun h0 : p /\ r => @lem1025 p r h0) (fun h0 : q /\ r => @lem1027 q r h0)). Qed.
Lemma lem1030 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : term0 p q r.
Proof. exact (conj (@lem1022 p q r h1) (@lem1029 p q r h1)). Qed.
Lemma lem1031 (p : Prop) (q : Prop) (r : Prop) : term3 p q r.
Proof. exact (fun h0 : term1 p q r => @lem1030 p q r h0). Qed.
Lemma lem1032 (p : Prop) (q : Prop) (r : Prop) : term4 p q r.
Proof. exact (conj (@lem1012 p q r) (@lem1031 p q r)). Qed.
Lemma lem1033 (p : Prop) (q : Prop) (r : Prop) : (term4 p q r) = ((term0 p q r) = (term1 p q r)).
Proof. exact (@lem32 (term0 p q r) (term1 p q r)). Qed.
Lemma lem1034 (p : Prop) (q : Prop) (r : Prop) : (term0 p q r) = (term1 p q r).
Proof. exact (EQ_MP (@lem1033 p q r) (@lem1032 p q r)). Qed.
Lemma lem1039 (p : Prop) (q : Prop) : term5 p q.
Proof. exact (fun r : Prop => @lem1034 p q r). Qed.
Lemma lem1044 (p : Prop) : term6 p.
Proof. exact (fun q : Prop => @lem1039 p q). Qed.
Lemma lem1049 : term7.
Proof. exact (fun p : Prop => @lem1044 p). Qed.
