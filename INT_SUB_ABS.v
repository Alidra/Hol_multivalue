Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_ABS_term_abbrevs.
Require Import REAL_SUB_ABS_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2310064 (x : int) : term0 x.
Proof. exact (@lem1545462 (real_of_int x)). Qed.
Lemma lem2310065 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310066 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2310065 x) (@lem2310064 x)). Qed.
Lemma lem2310067 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2310066 x (real_of_int y)). Qed.
Lemma lem2310068 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2310069 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2310068 x y) (@lem2310067 x y)). Qed.
Lemma lem2310071 (x : int) : (term4 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2310072 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2310073 (x : int) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem2310072) (@lem2310071 x)). Qed.
Lemma lem2310075 (x : int) : (term4 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2310076 (y : int) : (term4 y) = (term5 y).
Proof. exact (@lem2310075 y). Qed.
Lemma lem2310077 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2310073 x) (@lem2310076 y)). Qed.
Lemma lem2310079 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310080 (x : int) (y : int) : (term9 x y) = (term12 x y).
Proof. exact (@lem2310079 (int_abs x) (int_abs y)). Qed.
Lemma lem2310081 (x : int) (y : int) : (term8 x y) = (term12 x y).
Proof. exact (TRANS (@lem2310077 x y) (@lem2310080 x y)). Qed.
Lemma lem2310082 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2310083 (x : int) (y : int) : (term13 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem2310082) (@lem2310081 x y)). Qed.
Lemma lem2310085 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310086 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2310087 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem2310086) (@lem2310085 x y)). Qed.
Lemma lem2310089 (x : int) : (term4 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2310090 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (@lem2310089 (int_sub x y)). Qed.
Lemma lem2310091 (x : int) (y : int) : (term15 x y) = (term17 x y).
Proof. exact (TRANS (@lem2310087 x y) (@lem2310090 x y)). Qed.
Lemma lem2310092 (x : int) (y : int) : (term3 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem2310083 x y) (@lem2310091 x y)). Qed.
Lemma lem2310094 (x : int) (y : int) : (term19 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2310095 (x : int) (y : int) : (term18 x y) = (term20 x y).
Proof. exact (@lem2310094 (term21 x y) (term22 x y)). Qed.
Lemma lem2310096 (x : int) (y : int) : (term3 x y) = (term20 x y).
Proof. exact (TRANS (@lem2310092 x y) (@lem2310095 x y)). Qed.
Lemma lem2310097 (x : int) (y : int) : term20 x y.
Proof. exact (EQ_MP (@lem2310096 x y) (@lem2310069 x y)). Qed.
Lemma lem2310098 (x : int) : term23 x.
Proof. exact (fun y : int => @lem2310097 x y). Qed.
Lemma lem2310099 : term24.
Proof. exact (fun x : int => @lem2310098 x). Qed.
