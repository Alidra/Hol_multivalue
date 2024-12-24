Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm892_term_abbrevs.
Lemma lem888 (p : Prop) (q : Prop) (r : Prop) (h1 : (term0 p q r) = (term1 p q r)) : (term0 p q r) = (term1 p q r).
Proof. exact (h1). Qed.
Lemma lem889 (p : Prop) (q : Prop) (r : Prop) (h1 : (term0 p q r) = (term1 p q r)) : (term1 p q r) = (term0 p q r).
Proof. exact (SYM (@lem888 p q r h1)). Qed.
Lemma lem890 (p : Prop) (q : Prop) (r : Prop) (h1 : (term1 p q r) = (term0 p q r)) : (term1 p q r) = (term0 p q r).
Proof. exact (h1). Qed.
Lemma lem891 (p : Prop) (q : Prop) (r : Prop) (h1 : (term1 p q r) = (term0 p q r)) : (term0 p q r) = (term1 p q r).
Proof. exact (SYM (@lem890 p q r h1)). Qed.
Lemma lem892 (p : Prop) (q : Prop) (r : Prop) : ((term0 p q r) = (term1 p q r)) = ((term1 p q r) = (term0 p q r)).
Proof. exact (prop_ext (fun h1 : (term0 p q r) = (term1 p q r) => @lem889 p q r h1) (fun h1 : (term1 p q r) = (term0 p q r) => @lem891 p q r h1)). Qed.
