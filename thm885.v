Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm885_term_abbrevs.
Lemma lem860 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term0 p q r.
Proof. exact (h1). Qed.
Lemma lem861 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem862 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem863 (p : Prop) (q : Prop) (h1 : p /\ q) : p /\ q.
Proof. exact (h1). Qed.
Lemma lem864 (p : Prop) (q : Prop) (r : Prop) (h1 : p /\ q) (h2 : term0 p q r) : r.
Proof. exact (@lem860 p q r h2 (@lem863 p q h1)). Qed.
Lemma lem865 (p : Prop) (q : Prop) (h1 : p) (h2 : q) : p /\ q.
Proof. exact (conj (@lem861 p h1) (@lem862 q h2)). Qed.
Lemma lem866 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : q) (h3 : term0 p q r) : (p /\ q) = r.
Proof. exact (prop_ext (fun h4 : p /\ q => @lem864 p q r h4 h3) (fun h4 : r => @lem865 p q h1 h2)). Qed.
Lemma lem867 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : q) (h3 : term0 p q r) : r.
Proof. exact (EQ_MP (@lem866 p q r h1 h2 h3) (@lem865 p q h1 h2)). Qed.
Lemma lem868 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : term0 p q r) : q -> r.
Proof. exact (fun h0 : q => @lem867 p q r h1 h0 h2). Qed.
Lemma lem869 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term1 p q r.
Proof. exact (fun h0 : p => @lem868 p q r h0 h1). Qed.
Lemma lem870 (p : Prop) (q : Prop) (r : Prop) : term2 p q r.
Proof. exact (fun h0 : term0 p q r => @lem869 p q r h0). Qed.
Lemma lem871 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : term1 p q r.
Proof. exact (h1). Qed.
Lemma lem872 (p : Prop) (q : Prop) (h1 : p /\ q) : p /\ q.
Proof. exact (h1). Qed.
Lemma lem873 (p : Prop) (q : Prop) (h1 : p /\ q) : q.
Proof. exact (proj2 (@lem872 p q h1)). Qed.
Lemma lem874 (p : Prop) (q : Prop) (h1 : p /\ q) : p.
Proof. exact (proj1 (@lem872 p q h1)). Qed.
Lemma lem875 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem876 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : term1 p q r) : q -> r.
Proof. exact (@lem871 p q r h2 (@lem875 p h1)). Qed.
Lemma lem877 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem878 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : q) (h3 : term1 p q r) : r.
Proof. exact (@lem876 p q r h1 h3 (@lem877 q h2)). Qed.
Lemma lem879 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : p /\ q) (h3 : term1 p q r) : q = r.
Proof. exact (prop_ext (fun h4 : q => @lem878 p q r h1 h4 h3) (fun h4 : r => @lem873 p q h2)). Qed.
Lemma lem880 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : p /\ q) (h3 : term1 p q r) : r.
Proof. exact (EQ_MP (@lem879 p q r h1 h2 h3) (@lem873 p q h2)). Qed.
Lemma lem881 (p : Prop) (q : Prop) (r : Prop) (h1 : p /\ q) (h2 : term1 p q r) : p = r.
Proof. exact (prop_ext (fun h3 : p => @lem880 p q r h3 h1 h2) (fun h3 : r => @lem874 p q h1)). Qed.
Lemma lem882 (p : Prop) (q : Prop) (r : Prop) (h1 : p /\ q) (h2 : term1 p q r) : r.
Proof. exact (EQ_MP (@lem881 p q r h1 h2) (@lem874 p q h1)). Qed.
Lemma lem883 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : term0 p q r.
Proof. exact (fun h0 : p /\ q => @lem882 p q r h0 h1). Qed.
Lemma lem884 (p : Prop) (q : Prop) (r : Prop) : term3 p q r.
Proof. exact (fun h0 : term1 p q r => @lem883 p q r h0). Qed.
Lemma lem885 (p : Prop) (q : Prop) (r : Prop) : term4 p q r.
Proof. exact (conj (@lem870 p q r) (@lem884 p q r)). Qed.
