Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm196_term_abbrevs.
Lemma lem171 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term0 p q r.
Proof. exact (h1). Qed.
Lemma lem172 (p : Prop) (q : Prop) (h1 : p /\ q) : p /\ q.
Proof. exact (h1). Qed.
Lemma lem173 (p : Prop) (q : Prop) (h1 : p /\ q) : q.
Proof. exact (proj2 (@lem172 p q h1)). Qed.
Lemma lem174 (p : Prop) (q : Prop) (h1 : p /\ q) : p.
Proof. exact (proj1 (@lem172 p q h1)). Qed.
Lemma lem175 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem176 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : term0 p q r) : q -> r.
Proof. exact (@lem171 p q r h2 (@lem175 p h1)). Qed.
Lemma lem177 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem178 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : q) (h3 : term0 p q r) : r.
Proof. exact (@lem176 p q r h1 h3 (@lem177 q h2)). Qed.
Lemma lem179 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : p /\ q) (h3 : term0 p q r) : q = r.
Proof. exact (prop_ext (fun h4 : q => @lem178 p q r h1 h4 h3) (fun h4 : r => @lem173 p q h2)). Qed.
Lemma lem180 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : p /\ q) (h3 : term0 p q r) : r.
Proof. exact (EQ_MP (@lem179 p q r h1 h2 h3) (@lem173 p q h2)). Qed.
Lemma lem181 (p : Prop) (q : Prop) (r : Prop) (h1 : p /\ q) (h2 : term0 p q r) : p = r.
Proof. exact (prop_ext (fun h3 : p => @lem180 p q r h3 h1 h2) (fun h3 : r => @lem174 p q h1)). Qed.
Lemma lem182 (p : Prop) (q : Prop) (r : Prop) (h1 : p /\ q) (h2 : term0 p q r) : r.
Proof. exact (EQ_MP (@lem181 p q r h1 h2) (@lem174 p q h1)). Qed.
Lemma lem183 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term1 p q r.
Proof. exact (fun h0 : p /\ q => @lem182 p q r h0 h1). Qed.
Lemma lem184 (p : Prop) (q : Prop) (r : Prop) : term2 p q r.
Proof. exact (fun h0 : term0 p q r => @lem183 p q r h0). Qed.
Lemma lem185 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : term1 p q r.
Proof. exact (h1). Qed.
Lemma lem186 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem187 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem188 (p : Prop) (q : Prop) (h1 : p /\ q) : p /\ q.
Proof. exact (h1). Qed.
Lemma lem189 (p : Prop) (q : Prop) (r : Prop) (h1 : p /\ q) (h2 : term1 p q r) : r.
Proof. exact (@lem185 p q r h2 (@lem188 p q h1)). Qed.
Lemma lem190 (p : Prop) (q : Prop) (h1 : p) (h2 : q) : p /\ q.
Proof. exact (conj (@lem186 p h1) (@lem187 q h2)). Qed.
Lemma lem191 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : q) (h3 : term1 p q r) : (p /\ q) = r.
Proof. exact (prop_ext (fun h4 : p /\ q => @lem189 p q r h4 h3) (fun h4 : r => @lem190 p q h1 h2)). Qed.
Lemma lem192 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : q) (h3 : term1 p q r) : r.
Proof. exact (EQ_MP (@lem191 p q r h1 h2 h3) (@lem190 p q h1 h2)). Qed.
Lemma lem193 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : term1 p q r) : q -> r.
Proof. exact (fun h0 : q => @lem192 p q r h1 h0 h2). Qed.
Lemma lem194 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : term0 p q r.
Proof. exact (fun h0 : p => @lem193 p q r h0 h1). Qed.
Lemma lem195 (p : Prop) (q : Prop) (r : Prop) : term3 p q r.
Proof. exact (fun h0 : term1 p q r => @lem194 p q r h0). Qed.
Lemma lem196 (p : Prop) (q : Prop) (r : Prop) : term4 p q r.
Proof. exact (conj (@lem184 p q r) (@lem195 p q r)). Qed.
