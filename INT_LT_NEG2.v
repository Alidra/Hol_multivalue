Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_NEG2_term_abbrevs.
Require Import REAL_LT_NEG2_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304565 (x : int) : term0 x.
Proof. exact (@lem1526141 (real_of_int x)). Qed.
Lemma lem2304566 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304567 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304566 x) (@lem2304565 x)). Qed.
Lemma lem2304568 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304567 x (real_of_int y)). Qed.
Lemma lem2304569 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term4 y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304570 (y : int) (x : int) : (term3 x y) = (term4 y x).
Proof. exact (EQ_MP (@lem2304569 y x) (@lem2304568 x y)). Qed.
Lemma lem2304572 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2304573 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304574 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2304573) (@lem2304572 x)). Qed.
Lemma lem2304576 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2304577 (y : int) : (term5 y) = (term6 y).
Proof. exact (@lem2304576 y). Qed.
Lemma lem2304578 (x : int) (y : int) : (term3 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2304574 x) (@lem2304577 y)). Qed.
Lemma lem2304580 (x : int) (y : int) : (term4 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304581 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (@lem2304580 (int_neg x) (int_neg y)). Qed.
Lemma lem2304582 (x : int) (y : int) : (term3 x y) = (term10 x y).
Proof. exact (TRANS (@lem2304578 x y) (@lem2304581 x y)). Qed.
Lemma lem2304583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304584 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2304583) (@lem2304582 x y)). Qed.
Lemma lem2304586 (x : int) (y : int) : (term4 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304587 (y : int) (x : int) : (term4 y x) = (int_lt y x).
Proof. exact (@lem2304586 y x). Qed.
Lemma lem2304588 (y : int) (x : int) : ((term3 x y) = (term4 y x)) = ((term10 x y) = (int_lt y x)).
Proof. exact (MK_COMB (@lem2304584 x y) (@lem2304587 y x)). Qed.
Lemma lem2304589 (y : int) (x : int) : (term10 x y) = (int_lt y x).
Proof. exact (EQ_MP (@lem2304588 y x) (@lem2304570 y x)). Qed.
Lemma lem2304590 (x : int) : term13 x.
Proof. exact (fun y : int => @lem2304589 y x). Qed.
Lemma lem2304591 : term14.
Proof. exact (fun x : int => @lem2304590 x). Qed.
