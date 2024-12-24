Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_TRANS_term_abbrevs.
Require Import REAL_LT_TRANS_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2305064 (x : int) : term0 x.
Proof. exact (@lem1372268 (real_of_int x)). Qed.
Lemma lem2305065 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305066 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305065 x) (@lem2305064 x)). Qed.
Lemma lem2305067 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305066 x (real_of_int y)). Qed.
Lemma lem2305068 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305069 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2305068 y x) (@lem2305067 x y)). Qed.
Lemma lem2305070 (y : int) (x : int) (z : int) : term4 y x z.
Proof. exact (@lem2305069 y x (real_of_int z)). Qed.
Lemma lem2305071 (y : int) (x : int) (z : int) : (term4 y x z) = (term5 y x z).
Proof. exact (eq_refl (term4 y x z)). Qed.
Lemma lem2305072 (y : int) (x : int) (z : int) : term5 y x z.
Proof. exact (EQ_MP (@lem2305071 y x z) (@lem2305070 y x z)). Qed.
Lemma lem2305074 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2305075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2305076 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2305075) (@lem2305074 x y)). Qed.
Lemma lem2305078 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2305079 (y : int) (z : int) : (term6 y z) = (int_lt y z).
Proof. exact (@lem2305078 y z). Qed.
Lemma lem2305080 (x : int) (y : int) (z : int) : (term9 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem2305076 x y) (@lem2305079 y z)). Qed.
Lemma lem2305081 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2305082 (x : int) (y : int) (z : int) : (term11 x y z) = (term12 x y z).
Proof. exact (MK_COMB (@lem2305081) (@lem2305080 x y z)). Qed.
Lemma lem2305084 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2305085 (x : int) (z : int) : (term6 x z) = (int_lt x z).
Proof. exact (@lem2305084 x z). Qed.
Lemma lem2305086 (y : int) (x : int) (z : int) : (term5 y x z) = (term13 y x z).
Proof. exact (MK_COMB (@lem2305082 x y z) (@lem2305085 x z)). Qed.
Lemma lem2305087 (y : int) (x : int) (z : int) : term13 y x z.
Proof. exact (EQ_MP (@lem2305086 y x z) (@lem2305072 y x z)). Qed.
Lemma lem2305088 (y : int) (x : int) : term14 y x.
Proof. exact (fun z : int => @lem2305087 y x z). Qed.
Lemma lem2305089 (x : int) : term15 x.
Proof. exact (fun y : int => @lem2305088 y x). Qed.
Lemma lem2305090 : term16.
Proof. exact (fun x : int => @lem2305089 x). Qed.
