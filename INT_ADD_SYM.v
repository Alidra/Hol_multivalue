Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ADD_SYM_term_abbrevs.
Require Import thm1338238_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301300 (x : int) : term0 x.
Proof. exact (@lem1338238 (real_of_int x)). Qed.
Lemma lem2301301 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301302 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301301 x) (@lem2301300 x)). Qed.
Lemma lem2301303 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301302 x (real_of_int y)). Qed.
Lemma lem2301304 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term3 y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301305 (y : int) (x : int) : (term3 x y) = (term3 y x).
Proof. exact (EQ_MP (@lem2301304 y x) (@lem2301303 x y)). Qed.
Lemma lem2301307 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301308 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301309 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2301308) (@lem2301307 x y)). Qed.
Lemma lem2301311 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301312 (y : int) (x : int) : (term3 y x) = (term4 y x).
Proof. exact (@lem2301311 y x). Qed.
Lemma lem2301313 (y : int) (x : int) : ((term3 x y) = (term3 y x)) = ((term4 x y) = (term4 y x)).
Proof. exact (MK_COMB (@lem2301309 x y) (@lem2301312 y x)). Qed.
Lemma lem2301315 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301316 (y : int) (x : int) : ((term4 x y) = (term4 y x)) = ((int_add x y) = (int_add y x)).
Proof. exact (@lem2301315 (int_add x y) (int_add y x)). Qed.
Lemma lem2301317 (y : int) (x : int) : ((term3 x y) = (term3 y x)) = ((int_add x y) = (int_add y x)).
Proof. exact (TRANS (@lem2301313 y x) (@lem2301316 y x)). Qed.
Lemma lem2301318 (y : int) (x : int) : (int_add x y) = (int_add y x).
Proof. exact (EQ_MP (@lem2301317 y x) (@lem2301305 y x)). Qed.
Lemma lem2301319 (x : int) : term7 x.
Proof. exact (fun y : int => @lem2301318 y x). Qed.
Lemma lem2301320 : term8.
Proof. exact (fun x : int => @lem2301319 x). Qed.
