Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ADD2_SUB2_term_abbrevs.
Require Import REAL_ADD2_SUB2_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2300873 (a : int) : term0 a.
Proof. exact (@lem1517635 (real_of_int a)). Qed.
Lemma lem2300874 (a : int) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem2300875 (a : int) : term1 a.
Proof. exact (EQ_MP (@lem2300874 a) (@lem2300873 a)). Qed.
Lemma lem2300876 (a : int) (b : int) : term2 a b.
Proof. exact (@lem2300875 a (real_of_int b)). Qed.
Lemma lem2300877 (a : int) (b : int) : (term2 a b) = (term3 a b).
Proof. exact (eq_refl (term2 a b)). Qed.
Lemma lem2300878 (a : int) (b : int) : term3 a b.
Proof. exact (EQ_MP (@lem2300877 a b) (@lem2300876 a b)). Qed.
Lemma lem2300879 (a : int) (b : int) (c : int) : term4 a b c.
Proof. exact (@lem2300878 a b (real_of_int c)). Qed.
Lemma lem2300880 (a : int) (c : int) (b : int) : (term4 a b c) = (term5 a c b).
Proof. exact (eq_refl (term4 a b c)). Qed.
Lemma lem2300881 (a : int) (c : int) (b : int) : term5 a c b.
Proof. exact (EQ_MP (@lem2300880 a c b) (@lem2300879 a b c)). Qed.
Lemma lem2300882 (a : int) (c : int) (b : int) (d : int) : term6 a c b d.
Proof. exact (@lem2300881 a c b (real_of_int d)). Qed.
Lemma lem2300883 (a : int) (c : int) (b : int) (d : int) : (term6 a c b d) = ((term7 a b c d) = (term8 a c b d)).
Proof. exact (eq_refl (term6 a c b d)). Qed.
Lemma lem2300884 (a : int) (c : int) (b : int) (d : int) : (term7 a b c d) = (term8 a c b d).
Proof. exact (EQ_MP (@lem2300883 a c b d) (@lem2300882 a c b d)). Qed.
Lemma lem2300886 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300887 (a : int) (b : int) : (term9 a b) = (term10 a b).
Proof. exact (@lem2300886 a b). Qed.
Lemma lem2300888 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2300889 (a : int) (b : int) : (term11 a b) = (term12 a b).
Proof. exact (MK_COMB (@lem2300888) (@lem2300887 a b)). Qed.
Lemma lem2300891 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300892 (c : int) (d : int) : (term9 c d) = (term10 c d).
Proof. exact (@lem2300891 c d). Qed.
Lemma lem2300893 (a : int) (b : int) (c : int) (d : int) : (term7 a b c d) = (term13 a b c d).
Proof. exact (MK_COMB (@lem2300889 a b) (@lem2300892 c d)). Qed.
Lemma lem2300895 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300896 (a : int) (b : int) (c : int) (d : int) : (term13 a b c d) = (term16 a b c d).
Proof. exact (@lem2300895 (int_add a b) (int_add c d)). Qed.
Lemma lem2300897 (a : int) (b : int) (c : int) (d : int) : (term7 a b c d) = (term16 a b c d).
Proof. exact (TRANS (@lem2300893 a b c d) (@lem2300896 a b c d)). Qed.
Lemma lem2300898 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2300899 (a : int) (b : int) (c : int) (d : int) : (term17 a b c d) = (term18 a b c d).
Proof. exact (MK_COMB (@lem2300898) (@lem2300897 a b c d)). Qed.
Lemma lem2300901 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300902 (a : int) (c : int) : (term14 a c) = (term15 a c).
Proof. exact (@lem2300901 a c). Qed.
Lemma lem2300903 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2300904 (a : int) (c : int) : (term19 a c) = (term20 a c).
Proof. exact (MK_COMB (@lem2300903) (@lem2300902 a c)). Qed.
Lemma lem2300906 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300907 (b : int) (d : int) : (term14 b d) = (term15 b d).
Proof. exact (@lem2300906 b d). Qed.
Lemma lem2300908 (a : int) (c : int) (b : int) (d : int) : (term8 a c b d) = (term21 a c b d).
Proof. exact (MK_COMB (@lem2300904 a c) (@lem2300907 b d)). Qed.
Lemma lem2300910 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300911 (a : int) (c : int) (b : int) (d : int) : (term21 a c b d) = (term22 a c b d).
Proof. exact (@lem2300910 (int_sub a c) (int_sub b d)). Qed.
Lemma lem2300912 (a : int) (c : int) (b : int) (d : int) : (term8 a c b d) = (term22 a c b d).
Proof. exact (TRANS (@lem2300908 a c b d) (@lem2300911 a c b d)). Qed.
Lemma lem2300913 (a : int) (c : int) (b : int) (d : int) : ((term7 a b c d) = (term8 a c b d)) = ((term16 a b c d) = (term22 a c b d)).
Proof. exact (MK_COMB (@lem2300899 a b c d) (@lem2300912 a c b d)). Qed.
Lemma lem2300915 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2300916 (a : int) (c : int) (b : int) (d : int) : ((term16 a b c d) = (term22 a c b d)) = ((term23 a b c d) = (term24 a c b d)).
Proof. exact (@lem2300915 (term23 a b c d) (term24 a c b d)). Qed.
Lemma lem2300917 (a : int) (c : int) (b : int) (d : int) : ((term7 a b c d) = (term8 a c b d)) = ((term23 a b c d) = (term24 a c b d)).
Proof. exact (TRANS (@lem2300913 a c b d) (@lem2300916 a c b d)). Qed.
Lemma lem2300918 (a : int) (c : int) (b : int) (d : int) : (term23 a b c d) = (term24 a c b d).
Proof. exact (EQ_MP (@lem2300917 a c b d) (@lem2300884 a c b d)). Qed.
Lemma lem2300919 (a : int) (c : int) (b : int) : term25 a c b.
Proof. exact (fun d : int => @lem2300918 a c b d). Qed.
Lemma lem2300920 (a : int) (b : int) : term26 a b.
Proof. exact (fun c : int => @lem2300919 a c b). Qed.
Lemma lem2300921 (a : int) : term27 a.
Proof. exact (fun b : int => @lem2300920 a b). Qed.
Lemma lem2300922 : term28.
Proof. exact (fun a : int => @lem2300921 a). Qed.
