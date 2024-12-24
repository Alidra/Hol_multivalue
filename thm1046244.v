Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1046244_term_abbrevs.
Require Import thm1013352_spec.
Require Import thm912739_spec.
Require Import thm93_spec.
Lemma lem1046239 : term0 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1046240 (h1 : term0 = (BIT1 0)) : (term1 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1046241 : (term0 = (BIT1 0)) = ((term1 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term0 = (BIT1 0) => @lem1046240 h1) (fun h1 : (term1 = (NUMERAL 0)) = False => @lem1046239)). Qed.
Lemma lem1046242 : (term1 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1046241) (@lem1046239)). Qed.
Lemma lem1046243 : term2.
Proof. exact (@lem93 (term1 = (NUMERAL 0))). Qed.
Lemma lem1046244 : term3.
Proof. exact (@lem1046243 (@lem1046242)). Qed.
