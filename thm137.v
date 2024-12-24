Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm137_term_abbrevs.
Lemma lem130 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term0 p q r.
Proof. exact (h1). Qed.
Lemma lem131 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : term1 p q r.
Proof. exact (h1). Qed.
Lemma lem132 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) (h2 : term0 p q r) : term2 p q r.
Proof. exact (@lem130 p q r h2 (@lem131 p q r h1)). Qed.
Lemma lem133 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : term3 p q r.
Proof. exact (fun h0 : term0 p q r => @lem132 p q r h1 h0). Qed.
Lemma lem134 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term0 p q r.
Proof. exact (h1). Qed.
Lemma lem135 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) (h2 : term0 p q r) : term2 p q r.
Proof. exact (@lem133 p q r h1 (@lem134 p q r h2)). Qed.
Lemma lem136 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term0 p q r.
Proof. exact (fun h0 : term1 p q r => @lem135 p q r h0 h1). Qed.
Lemma lem137 (p : Prop) (q : Prop) (r : Prop) : term4 p q r.
Proof. exact (fun h0 : term0 p q r => @lem136 p q r h0). Qed.
