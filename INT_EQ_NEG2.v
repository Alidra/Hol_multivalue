Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EQ_NEG2_term_abbrevs.
Require Import REAL_EQ_NEG2_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301755 (x : int) : term0 x.
Proof. exact (@lem1525370 (real_of_int x)). Qed.
Lemma lem2301756 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301757 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301756 x) (@lem2301755 x)). Qed.
Lemma lem2301758 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301757 x (real_of_int y)). Qed.
Lemma lem2301759 (x : int) (y : int) : (term2 x y) = (((term3 x) = (term3 y)) = ((real_of_int x) = (real_of_int y))).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301760 (x : int) (y : int) : ((term3 x) = (term3 y)) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2301759 x y) (@lem2301758 x y)). Qed.
Lemma lem2301762 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2301763 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301764 (x : int) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem2301763) (@lem2301762 x)). Qed.
Lemma lem2301766 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2301767 (y : int) : (term3 y) = (term4 y).
Proof. exact (@lem2301766 y). Qed.
Lemma lem2301768 (x : int) (y : int) : ((term3 x) = (term3 y)) = ((term4 x) = (term4 y)).
Proof. exact (MK_COMB (@lem2301764 x) (@lem2301767 y)). Qed.
Lemma lem2301770 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301771 (x : int) (y : int) : ((term4 x) = (term4 y)) = ((int_neg x) = (int_neg y)).
Proof. exact (@lem2301770 (int_neg x) (int_neg y)). Qed.
Lemma lem2301772 (x : int) (y : int) : ((term3 x) = (term3 y)) = ((int_neg x) = (int_neg y)).
Proof. exact (TRANS (@lem2301768 x y) (@lem2301771 x y)). Qed.
Lemma lem2301773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2301774 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2301773) (@lem2301772 x y)). Qed.
Lemma lem2301776 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301777 (x : int) (y : int) : (((term3 x) = (term3 y)) = ((real_of_int x) = (real_of_int y))) = (((int_neg x) = (int_neg y)) = (x = y)).
Proof. exact (MK_COMB (@lem2301774 x y) (@lem2301776 x y)). Qed.
Lemma lem2301778 (x : int) (y : int) : ((int_neg x) = (int_neg y)) = (x = y).
Proof. exact (EQ_MP (@lem2301777 x y) (@lem2301760 x y)). Qed.
Lemma lem2301779 (x : int) : term9 x.
Proof. exact (fun y : int => @lem2301778 x y). Qed.
Lemma lem2301780 : term10.
Proof. exact (fun x : int => @lem2301779 x). Qed.
