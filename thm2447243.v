Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2447243_term_abbrevs.
Require Import INT_ENTIRE_spec.
Lemma lem2447228 (x : int) (y : int) (h1 : ((int_mul x y) = term0) = (term1 x y)) : ((int_mul x y) = term0) = (term1 x y).
Proof. exact (h1). Qed.
Lemma lem2447229 (x : int) (y : int) (h1 : ((int_mul x y) = term0) = (term1 x y)) : (term1 x y) = ((int_mul x y) = term0).
Proof. exact (SYM (@lem2447228 x y h1)). Qed.
Lemma lem2447230 (x : int) (y : int) (h1 : (term1 x y) = ((int_mul x y) = term0)) : (term1 x y) = ((int_mul x y) = term0).
Proof. exact (h1). Qed.
Lemma lem2447231 (x : int) (y : int) (h1 : (term1 x y) = ((int_mul x y) = term0)) : ((int_mul x y) = term0) = (term1 x y).
Proof. exact (SYM (@lem2447230 x y h1)). Qed.
Lemma lem2447232 (x : int) (y : int) : (((int_mul x y) = term0) = (term1 x y)) = ((term1 x y) = ((int_mul x y) = term0)).
Proof. exact (prop_ext (fun h1 : ((int_mul x y) = term0) = (term1 x y) => @lem2447229 x y h1) (fun h1 : (term1 x y) = ((int_mul x y) = term0) => @lem2447231 x y h1)). Qed.
Lemma lem2447233 (x : int) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun y : int => @lem2447232 x y)). Qed.
Lemma lem2447234 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2447235 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2447234) (@lem2447233 x)). Qed.
Lemma lem2447236 : term6 = term7.
Proof. exact (fun_ext (fun x : int => @lem2447235 x)). Qed.
Lemma lem2447237 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2447238 : term8 = term9.
Proof. exact (MK_COMB (@lem2447237) (@lem2447236)). Qed.
Lemma lem2447239 : term9.
Proof. exact (EQ_MP (@lem2447238) (@lem2301483)). Qed.
Lemma lem2447240 (x : int) : term10 x.
Proof. exact (@lem2447239 x). Qed.
Lemma lem2447241 (x : int) : (term10 x) = (term5 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem2447242 (x : int) : term5 x.
Proof. exact (EQ_MP (@lem2447241 x) (@lem2447240 x)). Qed.
Lemma lem2447243 (x : int) (y : int) : term11 x y.
Proof. exact (@lem2447242 x y). Qed.
