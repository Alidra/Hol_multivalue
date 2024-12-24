Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_REFL_term_abbrevs.
Require Import REAL_LT_REFL_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304769 (x : int) : term0 x.
Proof. exact (@lem1379422 (real_of_int x)). Qed.
Lemma lem2304770 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304771 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304770 x) (@lem2304769 x)). Qed.
Lemma lem2304773 (x : int) (y : int) : (term2 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304774 (x : int) : (term3 x) = (int_lt x x).
Proof. exact (@lem2304773 x x). Qed.
Lemma lem2304775 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2304776 (x : int) : (term1 x) = (term4 x).
Proof. exact (MK_COMB (@lem2304775) (@lem2304774 x)). Qed.
Lemma lem2304777 (x : int) : term4 x.
Proof. exact (EQ_MP (@lem2304776 x) (@lem2304771 x)). Qed.
Lemma lem2304778 : term5.
Proof. exact (fun x : int => @lem2304777 x). Qed.
