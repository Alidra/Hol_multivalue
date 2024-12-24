Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm804_term_abbrevs.
Lemma lem796 (p : Prop) (h1 : p \/ p) : p \/ p.
Proof. exact (h1). Qed.
Lemma lem797 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem798 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem799 (p : Prop) (h1 : p \/ p) : p.
Proof. exact (or_elim (@lem796 p h1) (fun h0 : p => @lem797 p h0) (fun h0 : p => @lem798 p h0)). Qed.
Lemma lem800 (p : Prop) : term0 p.
Proof. exact (fun h0 : p \/ p => @lem799 p h0). Qed.
Lemma lem801 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem802 (p : Prop) (h1 : p) : p \/ p.
Proof. exact (or_intro1 (@lem801 p h1) p). Qed.
Lemma lem803 (p : Prop) : term1 p.
Proof. exact (fun h0 : p => @lem802 p h0). Qed.
Lemma lem804 (p : Prop) : term2 p.
Proof. exact (conj (@lem800 p) (@lem803 p)). Qed.
