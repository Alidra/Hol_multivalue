Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MUL_ASSOC_term_abbrevs.
Require Import thm1338912_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2305919 (x : int) : term0 x.
Proof. exact (@lem1338912 (real_of_int x)). Qed.
Lemma lem2305920 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305921 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305920 x) (@lem2305919 x)). Qed.
Lemma lem2305922 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305921 x (real_of_int y)). Qed.
Lemma lem2305923 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305924 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2305923 x y) (@lem2305922 x y)). Qed.
Lemma lem2305925 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2305924 x y (real_of_int z)). Qed.
Lemma lem2305926 (x : int) (y : int) (z : int) : (term4 x y z) = ((term5 x y z) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2305927 (x : int) (y : int) (z : int) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem2305926 x y z) (@lem2305925 x y z)). Qed.
Lemma lem2305929 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305930 (y : int) (z : int) : (term7 y z) = (term8 y z).
Proof. exact (@lem2305929 y z). Qed.
Lemma lem2305931 (x : int) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2305932 (x : int) (y : int) (z : int) : (term5 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem2305931 x) (@lem2305930 y z)). Qed.
Lemma lem2305934 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305935 (x : int) (y : int) (z : int) : (term10 x y z) = (term11 x y z).
Proof. exact (@lem2305934 x (int_mul y z)). Qed.
Lemma lem2305936 (x : int) (y : int) (z : int) : (term5 x y z) = (term11 x y z).
Proof. exact (TRANS (@lem2305932 x y z) (@lem2305935 x y z)). Qed.
Lemma lem2305937 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305938 (x : int) (y : int) (z : int) : (term12 x y z) = (term13 x y z).
Proof. exact (MK_COMB (@lem2305937) (@lem2305936 x y z)). Qed.
Lemma lem2305940 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305941 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2305942 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem2305941) (@lem2305940 x y)). Qed.
Lemma lem2305943 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2305944 (x : int) (y : int) (z : int) : (term6 x y z) = (term16 x y z).
Proof. exact (MK_COMB (@lem2305942 x y) (@lem2305943 z)). Qed.
Lemma lem2305946 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305947 (x : int) (y : int) (z : int) : (term16 x y z) = (term17 x y z).
Proof. exact (@lem2305946 (int_mul x y) z). Qed.
Lemma lem2305948 (x : int) (y : int) (z : int) : (term6 x y z) = (term17 x y z).
Proof. exact (TRANS (@lem2305944 x y z) (@lem2305947 x y z)). Qed.
Lemma lem2305949 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term11 x y z) = (term17 x y z)).
Proof. exact (MK_COMB (@lem2305938 x y z) (@lem2305948 x y z)). Qed.
Lemma lem2305951 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305952 (x : int) (y : int) (z : int) : ((term11 x y z) = (term17 x y z)) = ((term18 x y z) = (term19 x y z)).
Proof. exact (@lem2305951 (term18 x y z) (term19 x y z)). Qed.
Lemma lem2305953 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term18 x y z) = (term19 x y z)).
Proof. exact (TRANS (@lem2305949 x y z) (@lem2305952 x y z)). Qed.
Lemma lem2305954 (x : int) (y : int) (z : int) : (term18 x y z) = (term19 x y z).
Proof. exact (EQ_MP (@lem2305953 x y z) (@lem2305927 x y z)). Qed.
Lemma lem2305955 (x : int) (y : int) : term20 x y.
Proof. exact (fun z : int => @lem2305954 x y z). Qed.
Lemma lem2305956 (x : int) : term21 x.
Proof. exact (fun y : int => @lem2305955 x y). Qed.
Lemma lem2305957 : term22.
Proof. exact (fun x : int => @lem2305956 x). Qed.
