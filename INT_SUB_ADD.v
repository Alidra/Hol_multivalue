Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_ADD_term_abbrevs.
Require Import REAL_SUB_ADD_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2310100 (x : int) : term0 x.
Proof. exact (@lem1504864 (real_of_int x)). Qed.
Lemma lem2310101 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310102 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2310101 x) (@lem2310100 x)). Qed.
Lemma lem2310103 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2310102 x (real_of_int y)). Qed.
Lemma lem2310104 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (real_of_int x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2310105 (y : int) (x : int) : (term3 x y) = (real_of_int x).
Proof. exact (EQ_MP (@lem2310104 y x) (@lem2310103 x y)). Qed.
Lemma lem2310107 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310108 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2310109 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2310108) (@lem2310107 x y)). Qed.
Lemma lem2310110 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2310111 (x : int) (y : int) : (term3 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2310109 x y) (@lem2310110 y)). Qed.
Lemma lem2310113 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2310114 (x : int) (y : int) : (term8 x y) = (term11 x y).
Proof. exact (@lem2310113 (int_sub x y) y). Qed.
Lemma lem2310115 (x : int) (y : int) : (term3 x y) = (term11 x y).
Proof. exact (TRANS (@lem2310111 x y) (@lem2310114 x y)). Qed.
Lemma lem2310116 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2310117 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2310116) (@lem2310115 x y)). Qed.
Lemma lem2310118 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2310119 (y : int) (x : int) : ((term3 x y) = (real_of_int x)) = ((term11 x y) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2310117 x y) (@lem2310118 x)). Qed.
Lemma lem2310121 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310122 (y : int) (x : int) : ((term11 x y) = (real_of_int x)) = ((term14 x y) = x).
Proof. exact (@lem2310121 (term14 x y) x). Qed.
Lemma lem2310123 (y : int) (x : int) : ((term3 x y) = (real_of_int x)) = ((term14 x y) = x).
Proof. exact (TRANS (@lem2310119 y x) (@lem2310122 y x)). Qed.
Lemma lem2310124 (y : int) (x : int) : (term14 x y) = x.
Proof. exact (EQ_MP (@lem2310123 y x) (@lem2310105 y x)). Qed.
Lemma lem2310125 (x : int) : term15 x.
Proof. exact (fun y : int => @lem2310124 y x). Qed.
Lemma lem2310126 : term16.
Proof. exact (fun x : int => @lem2310125 x). Qed.
