Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm951_term_abbrevs.
Lemma lem926 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term0 p q r.
Proof. exact (h1). Qed.
Lemma lem927 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem928 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem929 (p : Prop) (q : Prop) (h1 : p /\ q) : p /\ q.
Proof. exact (h1). Qed.
Lemma lem930 (p : Prop) (q : Prop) (r : Prop) (h1 : p /\ q) (h2 : term0 p q r) : r.
Proof. exact (@lem926 p q r h2 (@lem929 p q h1)). Qed.
Lemma lem931 (p : Prop) (q : Prop) (h1 : p) (h2 : q) : p /\ q.
Proof. exact (conj (@lem928 p h1) (@lem927 q h2)). Qed.
Lemma lem932 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : q) (h3 : term0 p q r) : (p /\ q) = r.
Proof. exact (prop_ext (fun h4 : p /\ q => @lem930 p q r h4 h3) (fun h4 : r => @lem931 p q h1 h2)). Qed.
Lemma lem933 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : q) (h3 : term0 p q r) : r.
Proof. exact (EQ_MP (@lem932 p q r h1 h2 h3) (@lem931 p q h1 h2)). Qed.
Lemma lem934 (p : Prop) (q : Prop) (r : Prop) (h1 : q) (h2 : term0 p q r) : p -> r.
Proof. exact (fun h0 : p => @lem933 p q r h0 h1 h2). Qed.
Lemma lem935 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term1 q p r.
Proof. exact (fun h0 : q => @lem934 p q r h0 h1). Qed.
Lemma lem936 (q : Prop) (p : Prop) (r : Prop) : term2 q p r.
Proof. exact (fun h0 : term0 p q r => @lem935 p q r h0). Qed.
Lemma lem937 (q : Prop) (p : Prop) (r : Prop) (h1 : term1 q p r) : term1 q p r.
Proof. exact (h1). Qed.
Lemma lem938 (p : Prop) (q : Prop) (h1 : p /\ q) : p /\ q.
Proof. exact (h1). Qed.
Lemma lem939 (p : Prop) (q : Prop) (h1 : p /\ q) : q.
Proof. exact (proj2 (@lem938 p q h1)). Qed.
Lemma lem940 (p : Prop) (q : Prop) (h1 : p /\ q) : p.
Proof. exact (proj1 (@lem938 p q h1)). Qed.
Lemma lem941 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem942 (q : Prop) (p : Prop) (r : Prop) (h1 : q) (h2 : term1 q p r) : p -> r.
Proof. exact (@lem937 q p r h2 (@lem941 q h1)). Qed.
Lemma lem943 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem944 (q : Prop) (p : Prop) (r : Prop) (h1 : p) (h2 : q) (h3 : term1 q p r) : r.
Proof. exact (@lem942 q p r h2 h3 (@lem943 p h1)). Qed.
Lemma lem945 (q : Prop) (p : Prop) (r : Prop) (h1 : q) (h2 : p /\ q) (h3 : term1 q p r) : p = r.
Proof. exact (prop_ext (fun h4 : p => @lem944 q p r h4 h1 h3) (fun h4 : r => @lem940 p q h2)). Qed.
Lemma lem946 (q : Prop) (p : Prop) (r : Prop) (h1 : q) (h2 : p /\ q) (h3 : term1 q p r) : r.
Proof. exact (EQ_MP (@lem945 q p r h1 h2 h3) (@lem940 p q h2)). Qed.
Lemma lem947 (q : Prop) (p : Prop) (r : Prop) (h1 : p /\ q) (h2 : term1 q p r) : q = r.
Proof. exact (prop_ext (fun h3 : q => @lem946 q p r h3 h1 h2) (fun h3 : r => @lem939 p q h1)). Qed.
Lemma lem948 (q : Prop) (p : Prop) (r : Prop) (h1 : p /\ q) (h2 : term1 q p r) : r.
Proof. exact (EQ_MP (@lem947 q p r h1 h2) (@lem939 p q h1)). Qed.
Lemma lem949 (q : Prop) (p : Prop) (r : Prop) (h1 : term1 q p r) : term0 p q r.
Proof. exact (fun h0 : p /\ q => @lem948 q p r h0 h1). Qed.
Lemma lem950 (p : Prop) (q : Prop) (r : Prop) : term3 p q r.
Proof. exact (fun h0 : term1 q p r => @lem949 q p r h0). Qed.
Lemma lem951 (p : Prop) (q : Prop) (r : Prop) : term4 p q r.
Proof. exact (conj (@lem936 q p r) (@lem950 p q r)). Qed.
