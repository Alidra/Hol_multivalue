Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21087_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1857_spec.
Lemma lem21069 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem21070 : term0 = (~ True).
Proof. exact (@lem21069 (~ True)). Qed.
Lemma lem21072 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem21073 : term0 = False.
Proof. exact (TRANS (@lem21070) (@lem21072)). Qed.
Lemma lem21074 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21075 : term1 = (@eq Prop False).
Proof. exact (MK_COMB (@lem21074) (@lem21073)). Qed.
Lemma lem21077 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem21078 : (term0 = (~ True)) = (False = False).
Proof. exact (MK_COMB (@lem21075) (@lem21077)). Qed.
Lemma lem21080 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem21081 : (False = False) = (~ False).
Proof. exact (@lem21080 False). Qed.
Lemma lem21083 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem21084 : (False = False) = True.
Proof. exact (TRANS (@lem21081) (@lem21083)). Qed.
Lemma lem21085 : (term0 = (~ True)) = True.
Proof. exact (TRANS (@lem21078) (@lem21084)). Qed.
Lemma lem21086 : True = (term0 = (~ True)).
Proof. exact (SYM (@lem21085)). Qed.
Lemma lem21087 : term0 = (~ True).
Proof. exact (EQ_MP (@lem21086) (@lem0)). Qed.
