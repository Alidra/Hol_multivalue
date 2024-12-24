Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_ADDR_term_abbrevs.
Require Import REAL_LT_ADDR_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2303887 (x : int) : term0 x.
Proof. exact (@lem1511188 (real_of_int x)). Qed.
Lemma lem2303888 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303889 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303888 x) (@lem2303887 x)). Qed.
Lemma lem2303890 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303889 x (real_of_int y)). Qed.
Lemma lem2303891 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303892 (x : int) (y : int) : (term3 x y) = (term4 y).
Proof. exact (EQ_MP (@lem2303891 x y) (@lem2303890 x y)). Qed.
Lemma lem2303894 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303895 (x : int) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2303896 (x : int) (y : int) : (term3 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2303895 x) (@lem2303894 x y)). Qed.
Lemma lem2303898 (x : int) (y : int) : (term9 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303899 (x : int) (y : int) : (term8 x y) = (term10 x y).
Proof. exact (@lem2303898 x (int_add x y)). Qed.
Lemma lem2303900 (x : int) (y : int) : (term3 x y) = (term10 x y).
Proof. exact (TRANS (@lem2303896 x y) (@lem2303899 x y)). Qed.
Lemma lem2303901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2303902 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2303901) (@lem2303900 x y)). Qed.
Lemma lem2303904 (n : nat) : (real_of_num n) = (term13 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303905 : term14 = term15.
Proof. exact (@lem2303904 (NUMERAL 0)). Qed.
Lemma lem2303906 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2303907 : term16 = term17.
Proof. exact (MK_COMB (@lem2303906) (@lem2303905)). Qed.
Lemma lem2303908 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2303909 (y : int) : (term4 y) = (term18 y).
Proof. exact (MK_COMB (@lem2303907) (@lem2303908 y)). Qed.
Lemma lem2303911 (x : int) (y : int) : (term9 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303912 (y : int) : (term18 y) = (term19 y).
Proof. exact (@lem2303911 term20 y). Qed.
Lemma lem2303913 (y : int) : (term4 y) = (term19 y).
Proof. exact (TRANS (@lem2303909 y) (@lem2303912 y)). Qed.
Lemma lem2303914 (x : int) (y : int) : ((term3 x y) = (term4 y)) = ((term10 x y) = (term19 y)).
Proof. exact (MK_COMB (@lem2303902 x y) (@lem2303913 y)). Qed.
Lemma lem2303915 (x : int) (y : int) : (term10 x y) = (term19 y).
Proof. exact (EQ_MP (@lem2303914 x y) (@lem2303892 x y)). Qed.
Lemma lem2303916 (x : int) : term21 x.
Proof. exact (fun y : int => @lem2303915 x y). Qed.
Lemma lem2303917 : term22.
Proof. exact (fun x : int => @lem2303916 x). Qed.
