Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_SUB2_term_abbrevs.
Require Import REAL_SUB_SUB2_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2310476 (x : int) : term0 x.
Proof. exact (@lem1523199 (real_of_int x)). Qed.
Lemma lem2310477 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310478 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2310477 x) (@lem2310476 x)). Qed.
Lemma lem2310479 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2310478 x (real_of_int y)). Qed.
Lemma lem2310480 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (real_of_int y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2310481 (x : int) (y : int) : (term3 x y) = (real_of_int y).
Proof. exact (EQ_MP (@lem2310480 x y) (@lem2310479 x y)). Qed.
Lemma lem2310483 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310484 (x : int) : (term6 x) = (term6 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem2310485 (x : int) (y : int) : (term3 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2310484 x) (@lem2310483 x y)). Qed.
Lemma lem2310487 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310488 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (@lem2310487 x (int_sub x y)). Qed.
Lemma lem2310489 (x : int) (y : int) : (term3 x y) = (term8 x y).
Proof. exact (TRANS (@lem2310485 x y) (@lem2310488 x y)). Qed.
Lemma lem2310490 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2310491 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2310490) (@lem2310489 x y)). Qed.
Lemma lem2310492 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2310493 (x : int) (y : int) : ((term3 x y) = (real_of_int y)) = ((term8 x y) = (real_of_int y)).
Proof. exact (MK_COMB (@lem2310491 x y) (@lem2310492 y)). Qed.
Lemma lem2310495 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310496 (x : int) (y : int) : ((term8 x y) = (real_of_int y)) = ((term11 x y) = y).
Proof. exact (@lem2310495 (term11 x y) y). Qed.
Lemma lem2310497 (x : int) (y : int) : ((term3 x y) = (real_of_int y)) = ((term11 x y) = y).
Proof. exact (TRANS (@lem2310493 x y) (@lem2310496 x y)). Qed.
Lemma lem2310498 (x : int) (y : int) : (term11 x y) = y.
Proof. exact (EQ_MP (@lem2310497 x y) (@lem2310481 x y)). Qed.
Lemma lem2310499 (x : int) : term12 x.
Proof. exact (fun y : int => @lem2310498 x y). Qed.
Lemma lem2310500 : term13.
Proof. exact (fun x : int => @lem2310499 x). Qed.
