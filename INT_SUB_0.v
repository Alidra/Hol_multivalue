Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_0_term_abbrevs.
Require Import REAL_SUB_0_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2310038 (x : int) : term0 x.
Proof. exact (@lem1376695 (real_of_int x)). Qed.
Lemma lem2310039 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310040 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2310039 x) (@lem2310038 x)). Qed.
Lemma lem2310041 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2310040 x (real_of_int y)). Qed.
Lemma lem2310042 (x : int) (y : int) : (term2 x y) = (((term3 x y) = term4) = ((real_of_int x) = (real_of_int y))).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2310043 (x : int) (y : int) : ((term3 x y) = term4) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2310042 x y) (@lem2310041 x y)). Qed.
Lemma lem2310045 (x : int) (y : int) : (term3 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310046 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2310047 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2310046) (@lem2310045 x y)). Qed.
Lemma lem2310049 (n : nat) : (real_of_num n) = (term8 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2310050 : term4 = term9.
Proof. exact (@lem2310049 (NUMERAL 0)). Qed.
Lemma lem2310051 (x : int) (y : int) : ((term3 x y) = term4) = ((term5 x y) = term9).
Proof. exact (MK_COMB (@lem2310047 x y) (@lem2310050)). Qed.
Lemma lem2310053 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310054 (x : int) (y : int) : ((term5 x y) = term9) = ((int_sub x y) = term10).
Proof. exact (@lem2310053 (int_sub x y) term10). Qed.
Lemma lem2310055 (x : int) (y : int) : ((term3 x y) = term4) = ((int_sub x y) = term10).
Proof. exact (TRANS (@lem2310051 x y) (@lem2310054 x y)). Qed.
Lemma lem2310056 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2310057 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2310056) (@lem2310055 x y)). Qed.
Lemma lem2310059 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310060 (x : int) (y : int) : (((term3 x y) = term4) = ((real_of_int x) = (real_of_int y))) = (((int_sub x y) = term10) = (x = y)).
Proof. exact (MK_COMB (@lem2310057 x y) (@lem2310059 x y)). Qed.
Lemma lem2310061 (x : int) (y : int) : ((int_sub x y) = term10) = (x = y).
Proof. exact (EQ_MP (@lem2310060 x y) (@lem2310043 x y)). Qed.
Lemma lem2310062 (x : int) : term13 x.
Proof. exact (fun y : int => @lem2310061 x y). Qed.
Lemma lem2310063 : term14.
Proof. exact (fun x : int => @lem2310062 x). Qed.
