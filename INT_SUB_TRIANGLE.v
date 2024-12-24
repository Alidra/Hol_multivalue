Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_TRIANGLE_term_abbrevs.
Require Import REAL_SUB_TRIANGLE_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2310501 (a : int) : term0 a.
Proof. exact (@lem1520119 (real_of_int a)). Qed.
Lemma lem2310502 (a : int) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem2310503 (a : int) : term1 a.
Proof. exact (EQ_MP (@lem2310502 a) (@lem2310501 a)). Qed.
Lemma lem2310504 (a : int) (b : int) : term2 a b.
Proof. exact (@lem2310503 a (real_of_int b)). Qed.
Lemma lem2310505 (b : int) (a : int) : (term2 a b) = (term3 b a).
Proof. exact (eq_refl (term2 a b)). Qed.
Lemma lem2310506 (b : int) (a : int) : term3 b a.
Proof. exact (EQ_MP (@lem2310505 b a) (@lem2310504 a b)). Qed.
Lemma lem2310507 (b : int) (a : int) (c : int) : term4 b a c.
Proof. exact (@lem2310506 b a (real_of_int c)). Qed.
Lemma lem2310508 (b : int) (a : int) (c : int) : (term4 b a c) = ((term5 a b c) = (term6 a c)).
Proof. exact (eq_refl (term4 b a c)). Qed.
Lemma lem2310509 (b : int) (a : int) (c : int) : (term5 a b c) = (term6 a c).
Proof. exact (EQ_MP (@lem2310508 b a c) (@lem2310507 b a c)). Qed.
Lemma lem2310511 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310512 (a : int) (b : int) : (term6 a b) = (term7 a b).
Proof. exact (@lem2310511 a b). Qed.
Lemma lem2310513 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2310514 (a : int) (b : int) : (term8 a b) = (term9 a b).
Proof. exact (MK_COMB (@lem2310513) (@lem2310512 a b)). Qed.
Lemma lem2310516 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310517 (b : int) (c : int) : (term6 b c) = (term7 b c).
Proof. exact (@lem2310516 b c). Qed.
Lemma lem2310518 (a : int) (b : int) (c : int) : (term5 a b c) = (term10 a b c).
Proof. exact (MK_COMB (@lem2310514 a b) (@lem2310517 b c)). Qed.
Lemma lem2310520 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2310521 (a : int) (b : int) (c : int) : (term10 a b c) = (term13 a b c).
Proof. exact (@lem2310520 (int_sub a b) (int_sub b c)). Qed.
Lemma lem2310522 (a : int) (b : int) (c : int) : (term5 a b c) = (term13 a b c).
Proof. exact (TRANS (@lem2310518 a b c) (@lem2310521 a b c)). Qed.
Lemma lem2310523 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2310524 (a : int) (b : int) (c : int) : (term14 a b c) = (term15 a b c).
Proof. exact (MK_COMB (@lem2310523) (@lem2310522 a b c)). Qed.
Lemma lem2310526 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310527 (a : int) (c : int) : (term6 a c) = (term7 a c).
Proof. exact (@lem2310526 a c). Qed.
Lemma lem2310528 (b : int) (a : int) (c : int) : ((term5 a b c) = (term6 a c)) = ((term13 a b c) = (term7 a c)).
Proof. exact (MK_COMB (@lem2310524 a b c) (@lem2310527 a c)). Qed.
Lemma lem2310530 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310531 (b : int) (a : int) (c : int) : ((term13 a b c) = (term7 a c)) = ((term16 a b c) = (int_sub a c)).
Proof. exact (@lem2310530 (term16 a b c) (int_sub a c)). Qed.
Lemma lem2310532 (b : int) (a : int) (c : int) : ((term5 a b c) = (term6 a c)) = ((term16 a b c) = (int_sub a c)).
Proof. exact (TRANS (@lem2310528 b a c) (@lem2310531 b a c)). Qed.
Lemma lem2310533 (b : int) (a : int) (c : int) : (term16 a b c) = (int_sub a c).
Proof. exact (EQ_MP (@lem2310532 b a c) (@lem2310509 b a c)). Qed.
Lemma lem2310534 (b : int) (a : int) : term17 b a.
Proof. exact (fun c : int => @lem2310533 b a c). Qed.
Lemma lem2310535 (a : int) : term18 a.
Proof. exact (fun b : int => @lem2310534 b a). Qed.
Lemma lem2310536 : term19.
Proof. exact (fun a : int => @lem2310535 a). Qed.
