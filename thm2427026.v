Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2427026_term_abbrevs.
Require Import thm1013352_spec.
Require Import thm2405481_spec.
Require Import thm912739_spec.
Require Import thm93_spec.
Lemma lem2427018 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (proj1 (@lem2405481 m n)). Qed.
Lemma lem2427019 : (term0 = term1) = (term2 = (NUMERAL 0)).
Proof. exact (@lem2427018 term2 (NUMERAL 0)). Qed.
Lemma lem2427020 : term3 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2427021 (h1 : term3 = (BIT1 0)) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2427022 : (term3 = (BIT1 0)) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term3 = (BIT1 0) => @lem2427021 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem2427020)). Qed.
Lemma lem2427023 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2427022) (@lem2427020)). Qed.
Lemma lem2427024 : (term0 = term1) = False.
Proof. exact (TRANS (@lem2427019) (@lem2427023)). Qed.
Lemma lem2427025 : term4.
Proof. exact (@lem93 (term0 = term1)). Qed.
Lemma lem2427026 : term5.
Proof. exact (@lem2427025 (@lem2427024)). Qed.
