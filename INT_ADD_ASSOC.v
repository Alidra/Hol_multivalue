Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ADD_ASSOC_term_abbrevs.
Require Import thm1338438_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301029 (x : int) : term0 x.
Proof. exact (@lem1338438 (real_of_int x)). Qed.
Lemma lem2301030 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301031 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301030 x) (@lem2301029 x)). Qed.
Lemma lem2301032 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301031 x (real_of_int y)). Qed.
Lemma lem2301033 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301034 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2301033 x y) (@lem2301032 x y)). Qed.
Lemma lem2301035 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2301034 x y (real_of_int z)). Qed.
Lemma lem2301036 (x : int) (y : int) (z : int) : (term4 x y z) = ((term5 x y z) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2301037 (x : int) (y : int) (z : int) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem2301036 x y z) (@lem2301035 x y z)). Qed.
Lemma lem2301039 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301040 (y : int) (z : int) : (term7 y z) = (term8 y z).
Proof. exact (@lem2301039 y z). Qed.
Lemma lem2301041 (x : int) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2301042 (x : int) (y : int) (z : int) : (term5 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem2301041 x) (@lem2301040 y z)). Qed.
Lemma lem2301044 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301045 (x : int) (y : int) (z : int) : (term10 x y z) = (term11 x y z).
Proof. exact (@lem2301044 x (int_add y z)). Qed.
Lemma lem2301046 (x : int) (y : int) (z : int) : (term5 x y z) = (term11 x y z).
Proof. exact (TRANS (@lem2301042 x y z) (@lem2301045 x y z)). Qed.
Lemma lem2301047 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301048 (x : int) (y : int) (z : int) : (term12 x y z) = (term13 x y z).
Proof. exact (MK_COMB (@lem2301047) (@lem2301046 x y z)). Qed.
Lemma lem2301050 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301051 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2301052 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem2301051) (@lem2301050 x y)). Qed.
Lemma lem2301053 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2301054 (x : int) (y : int) (z : int) : (term6 x y z) = (term16 x y z).
Proof. exact (MK_COMB (@lem2301052 x y) (@lem2301053 z)). Qed.
Lemma lem2301056 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301057 (x : int) (y : int) (z : int) : (term16 x y z) = (term17 x y z).
Proof. exact (@lem2301056 (int_add x y) z). Qed.
Lemma lem2301058 (x : int) (y : int) (z : int) : (term6 x y z) = (term17 x y z).
Proof. exact (TRANS (@lem2301054 x y z) (@lem2301057 x y z)). Qed.
Lemma lem2301059 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term11 x y z) = (term17 x y z)).
Proof. exact (MK_COMB (@lem2301048 x y z) (@lem2301058 x y z)). Qed.
Lemma lem2301061 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301062 (x : int) (y : int) (z : int) : ((term11 x y z) = (term17 x y z)) = ((term18 x y z) = (term19 x y z)).
Proof. exact (@lem2301061 (term18 x y z) (term19 x y z)). Qed.
Lemma lem2301063 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term18 x y z) = (term19 x y z)).
Proof. exact (TRANS (@lem2301059 x y z) (@lem2301062 x y z)). Qed.
Lemma lem2301064 (x : int) (y : int) (z : int) : (term18 x y z) = (term19 x y z).
Proof. exact (EQ_MP (@lem2301063 x y z) (@lem2301037 x y z)). Qed.
Lemma lem2301065 (x : int) (y : int) : term20 x y.
Proof. exact (fun z : int => @lem2301064 x y z). Qed.
Lemma lem2301066 (x : int) : term21 x.
Proof. exact (fun y : int => @lem2301065 x y). Qed.
Lemma lem2301067 : term22.
Proof. exact (fun x : int => @lem2301066 x). Qed.
