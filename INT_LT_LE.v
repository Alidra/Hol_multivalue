Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_LE_term_abbrevs.
Require Import REAL_LT_LE_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2304132 (x : int) : term0 x.
Proof. exact (@lem1379381 (real_of_int x)). Qed.
Lemma lem2304133 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304134 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304133 x) (@lem2304132 x)). Qed.
Lemma lem2304135 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304134 x (real_of_int y)). Qed.
Lemma lem2304136 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304137 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2304136 x y) (@lem2304135 x y)). Qed.
Lemma lem2304139 (x : int) (y : int) : (term3 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304140 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304141 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2304140) (@lem2304139 x y)). Qed.
Lemma lem2304143 (x : int) (y : int) : (term7 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2304144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2304145 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2304144) (@lem2304143 x y)). Qed.
Lemma lem2304147 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2304148 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2304149 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem2304148) (@lem2304147 x y)). Qed.
Lemma lem2304150 (x : int) (y : int) : (term4 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2304145 x y) (@lem2304149 x y)). Qed.
Lemma lem2304151 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((int_lt x y) = (term12 x y)).
Proof. exact (MK_COMB (@lem2304141 x y) (@lem2304150 x y)). Qed.
Lemma lem2304152 (x : int) (y : int) : (int_lt x y) = (term12 x y).
Proof. exact (EQ_MP (@lem2304151 x y) (@lem2304137 x y)). Qed.
Lemma lem2304153 (x : int) : term13 x.
Proof. exact (fun y : int => @lem2304152 x y). Qed.
Lemma lem2304154 : term14.
Proof. exact (fun x : int => @lem2304153 x). Qed.
