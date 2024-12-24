Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LET_ADD2_term_abbrevs.
Require Import REAL_LET_ADD2_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302054 (w : int) : term0 w.
Proof. exact (@lem1518504 (real_of_int w)). Qed.
Lemma lem2302055 (w : int) : (term0 w) = (term1 w).
Proof. exact (eq_refl (term0 w)). Qed.
Lemma lem2302056 (w : int) : term1 w.
Proof. exact (EQ_MP (@lem2302055 w) (@lem2302054 w)). Qed.
Lemma lem2302057 (w : int) (x : int) : term2 w x.
Proof. exact (@lem2302056 w (real_of_int x)). Qed.
Lemma lem2302058 (w : int) (x : int) : (term2 w x) = (term3 w x).
Proof. exact (eq_refl (term2 w x)). Qed.
Lemma lem2302059 (w : int) (x : int) : term3 w x.
Proof. exact (EQ_MP (@lem2302058 w x) (@lem2302057 w x)). Qed.
Lemma lem2302060 (w : int) (x : int) (y : int) : term4 w x y.
Proof. exact (@lem2302059 w x (real_of_int y)). Qed.
Lemma lem2302061 (w : int) (y : int) (x : int) : (term4 w x y) = (term5 w y x).
Proof. exact (eq_refl (term4 w x y)). Qed.
Lemma lem2302062 (w : int) (y : int) (x : int) : term5 w y x.
Proof. exact (EQ_MP (@lem2302061 w y x) (@lem2302060 w x y)). Qed.
Lemma lem2302063 (w : int) (y : int) (x : int) (z : int) : term6 w y x z.
Proof. exact (@lem2302062 w y x (real_of_int z)). Qed.
Lemma lem2302064 (w : int) (y : int) (x : int) (z : int) : (term6 w y x z) = (term7 w y x z).
Proof. exact (eq_refl (term6 w y x z)). Qed.
Lemma lem2302065 (w : int) (y : int) (x : int) (z : int) : term7 w y x z.
Proof. exact (EQ_MP (@lem2302064 w y x z) (@lem2302063 w y x z)). Qed.
Lemma lem2302067 (x : int) (y : int) : (term8 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302068 (w : int) (x : int) : (term8 w x) = (int_le w x).
Proof. exact (@lem2302067 w x). Qed.
Lemma lem2302069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2302070 (w : int) (x : int) : (term9 w x) = (term10 w x).
Proof. exact (MK_COMB (@lem2302069) (@lem2302068 w x)). Qed.
Lemma lem2302072 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2302073 (y : int) (z : int) : (term11 y z) = (int_lt y z).
Proof. exact (@lem2302072 y z). Qed.
Lemma lem2302074 (w : int) (x : int) (y : int) (z : int) : (term12 w x y z) = (term13 w x y z).
Proof. exact (MK_COMB (@lem2302070 w x) (@lem2302073 y z)). Qed.
Lemma lem2302075 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2302076 (w : int) (x : int) (y : int) (z : int) : (term14 w x y z) = (term15 w x y z).
Proof. exact (MK_COMB (@lem2302075) (@lem2302074 w x y z)). Qed.
Lemma lem2302078 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2302079 (w : int) (y : int) : (term16 w y) = (term17 w y).
Proof. exact (@lem2302078 w y). Qed.
Lemma lem2302080 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2302081 (w : int) (y : int) : (term18 w y) = (term19 w y).
Proof. exact (MK_COMB (@lem2302080) (@lem2302079 w y)). Qed.
Lemma lem2302083 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2302084 (x : int) (z : int) : (term16 x z) = (term17 x z).
Proof. exact (@lem2302083 x z). Qed.
Lemma lem2302085 (w : int) (y : int) (x : int) (z : int) : (term20 w y x z) = (term21 w y x z).
Proof. exact (MK_COMB (@lem2302081 w y) (@lem2302084 x z)). Qed.
Lemma lem2302087 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2302088 (w : int) (y : int) (x : int) (z : int) : (term21 w y x z) = (term22 w y x z).
Proof. exact (@lem2302087 (int_add w y) (int_add x z)). Qed.
Lemma lem2302089 (w : int) (y : int) (x : int) (z : int) : (term20 w y x z) = (term22 w y x z).
Proof. exact (TRANS (@lem2302085 w y x z) (@lem2302088 w y x z)). Qed.
Lemma lem2302090 (w : int) (y : int) (x : int) (z : int) : (term7 w y x z) = (term23 w y x z).
Proof. exact (MK_COMB (@lem2302076 w x y z) (@lem2302089 w y x z)). Qed.
Lemma lem2302091 (w : int) (y : int) (x : int) (z : int) : term23 w y x z.
Proof. exact (EQ_MP (@lem2302090 w y x z) (@lem2302065 w y x z)). Qed.
Lemma lem2302092 (w : int) (y : int) (x : int) : term24 w y x.
Proof. exact (fun z : int => @lem2302091 w y x z). Qed.
Lemma lem2302093 (w : int) (x : int) : term25 w x.
Proof. exact (fun y : int => @lem2302092 w y x). Qed.
Lemma lem2302094 (w : int) : term26 w.
Proof. exact (fun x : int => @lem2302093 w x). Qed.
Lemma lem2302095 : term27.
Proof. exact (fun w : int => @lem2302094 w). Qed.
