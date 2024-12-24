Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_IMP_LE_term_abbrevs.
Require Import REAL_LT_IMP_LE_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303991 (x : int) : term0 x.
Proof. exact (@lem1369133 (real_of_int x)). Qed.
Lemma lem2303992 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303993 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303992 x) (@lem2303991 x)). Qed.
Lemma lem2303994 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303993 x (real_of_int y)). Qed.
Lemma lem2303995 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303996 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2303995 x y) (@lem2303994 x y)). Qed.
Lemma lem2303998 (x : int) (y : int) : (term4 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303999 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2304000 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2303999) (@lem2303998 x y)). Qed.
Lemma lem2304002 (x : int) (y : int) : (term7 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2304003 (x : int) (y : int) : (term3 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2304000 x y) (@lem2304002 x y)). Qed.
Lemma lem2304004 (x : int) (y : int) : term8 x y.
Proof. exact (EQ_MP (@lem2304003 x y) (@lem2303996 x y)). Qed.
Lemma lem2304005 (x : int) : term9 x.
Proof. exact (fun y : int => @lem2304004 x y). Qed.
Lemma lem2304006 : term10.
Proof. exact (fun x : int => @lem2304005 x). Qed.
