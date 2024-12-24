Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_IMP_NE_term_abbrevs.
Require Import REAL_LT_IMP_NE_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2304007 (x : int) : term0 x.
Proof. exact (@lem1509403 (real_of_int x)). Qed.
Lemma lem2304008 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304009 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304008 x) (@lem2304007 x)). Qed.
Lemma lem2304010 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304009 x (real_of_int y)). Qed.
Lemma lem2304011 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304012 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2304011 x y) (@lem2304010 x y)). Qed.
Lemma lem2304014 (x : int) (y : int) : (term4 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304015 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2304016 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2304015) (@lem2304014 x y)). Qed.
Lemma lem2304018 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2304019 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2304020 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2304019) (@lem2304018 x y)). Qed.
Lemma lem2304021 (x : int) (y : int) : (term3 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2304016 x y) (@lem2304020 x y)). Qed.
Lemma lem2304022 (x : int) (y : int) : term9 x y.
Proof. exact (EQ_MP (@lem2304021 x y) (@lem2304012 x y)). Qed.
Lemma lem2304023 (x : int) : term10 x.
Proof. exact (fun y : int => @lem2304022 x y). Qed.
Lemma lem2304024 : term11.
Proof. exact (fun x : int => @lem2304023 x). Qed.
