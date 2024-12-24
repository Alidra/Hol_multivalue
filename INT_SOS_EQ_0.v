Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SOS_EQ_0_term_abbrevs.
Require Import REAL_SOS_EQ_0_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2309982 (x : int) : term0 x.
Proof. exact (@lem1648586 (real_of_int x)). Qed.
Lemma lem2309983 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2309984 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2309983 x) (@lem2309982 x)). Qed.
Lemma lem2309985 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2309984 x (real_of_int y)). Qed.
Lemma lem2309986 (x : int) (y : int) : (term2 x y) = (((term3 x y) = term4) = (term5 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2309987 (x : int) (y : int) : ((term3 x y) = term4) = (term5 x y).
Proof. exact (EQ_MP (@lem2309986 x y) (@lem2309985 x y)). Qed.
Lemma lem2309989 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2309990 (x : int) : (term8 x) = (term9 x).
Proof. exact (@lem2309989 x term10). Qed.
Lemma lem2309991 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2309992 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2309991) (@lem2309990 x)). Qed.
Lemma lem2309994 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2309995 (y : int) : (term8 y) = (term9 y).
Proof. exact (@lem2309994 y term10). Qed.
Lemma lem2309996 (x : int) (y : int) : (term3 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2309992 x) (@lem2309995 y)). Qed.
Lemma lem2309998 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2309999 (x : int) (y : int) : (term13 x y) = (term16 x y).
Proof. exact (@lem2309998 (term17 x) (term17 y)). Qed.
Lemma lem2310000 (x : int) (y : int) : (term3 x y) = (term16 x y).
Proof. exact (TRANS (@lem2309996 x y) (@lem2309999 x y)). Qed.
Lemma lem2310001 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2310002 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (MK_COMB (@lem2310001) (@lem2310000 x y)). Qed.
Lemma lem2310004 (n : nat) : (real_of_num n) = (term20 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2310005 : term4 = term21.
Proof. exact (@lem2310004 (NUMERAL 0)). Qed.
Lemma lem2310006 (x : int) (y : int) : ((term3 x y) = term4) = ((term16 x y) = term21).
Proof. exact (MK_COMB (@lem2310002 x y) (@lem2310005)). Qed.
Lemma lem2310008 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310009 (x : int) (y : int) : ((term16 x y) = term21) = ((term22 x y) = term23).
Proof. exact (@lem2310008 (term22 x y) term23). Qed.
Lemma lem2310010 (x : int) (y : int) : ((term3 x y) = term4) = ((term22 x y) = term23).
Proof. exact (TRANS (@lem2310006 x y) (@lem2310009 x y)). Qed.
Lemma lem2310011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2310012 (x : int) (y : int) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem2310011) (@lem2310010 x y)). Qed.
Lemma lem2310014 (n : nat) : (real_of_num n) = (term20 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2310015 : term4 = term21.
Proof. exact (@lem2310014 (NUMERAL 0)). Qed.
Lemma lem2310016 (x : int) : (term26 x) = (term26 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem2310017 (x : int) : ((real_of_int x) = term4) = ((real_of_int x) = term21).
Proof. exact (MK_COMB (@lem2310016 x) (@lem2310015)). Qed.
Lemma lem2310019 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310020 (x : int) : ((real_of_int x) = term21) = (x = term23).
Proof. exact (@lem2310019 x term23). Qed.
Lemma lem2310021 (x : int) : ((real_of_int x) = term4) = (x = term23).
Proof. exact (TRANS (@lem2310017 x) (@lem2310020 x)). Qed.
Lemma lem2310022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2310023 (x : int) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem2310022) (@lem2310021 x)). Qed.
Lemma lem2310025 (n : nat) : (real_of_num n) = (term20 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2310026 : term4 = term21.
Proof. exact (@lem2310025 (NUMERAL 0)). Qed.
Lemma lem2310027 (y : int) : (term26 y) = (term26 y).
Proof. exact (eq_refl (term26 y)). Qed.
Lemma lem2310028 (y : int) : ((real_of_int y) = term4) = ((real_of_int y) = term21).
Proof. exact (MK_COMB (@lem2310027 y) (@lem2310026)). Qed.
Lemma lem2310030 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310031 (y : int) : ((real_of_int y) = term21) = (y = term23).
Proof. exact (@lem2310030 y term23). Qed.
Lemma lem2310032 (y : int) : ((real_of_int y) = term4) = (y = term23).
Proof. exact (TRANS (@lem2310028 y) (@lem2310031 y)). Qed.
Lemma lem2310033 (x : int) (y : int) : (term5 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem2310023 x) (@lem2310032 y)). Qed.
Lemma lem2310034 (x : int) (y : int) : (((term3 x y) = term4) = (term5 x y)) = (((term22 x y) = term23) = (term29 x y)).
Proof. exact (MK_COMB (@lem2310012 x y) (@lem2310033 x y)). Qed.
Lemma lem2310035 (x : int) (y : int) : ((term22 x y) = term23) = (term29 x y).
Proof. exact (EQ_MP (@lem2310034 x y) (@lem2309987 x y)). Qed.
Lemma lem2310036 (x : int) : term30 x.
Proof. exact (fun y : int => @lem2310035 x y). Qed.
Lemma lem2310037 : term31.
Proof. exact (fun x : int => @lem2310036 x). Qed.
