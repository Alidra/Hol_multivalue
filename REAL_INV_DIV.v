Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INV_DIV_term_abbrevs.
Require Import REAL_INV_INV_spec.
Require Import REAL_INV_MUL_spec.
Require Import real_div_spec.
Require Import thm1338712_spec.
Lemma lem1595295 (x : real) : term0 x.
Proof. exact (@lem1595294 x). Qed.
Lemma lem1595296 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1595297 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1595296 x) (@lem1595295 x)). Qed.
Lemma lem1595298 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1595297 x y). Qed.
Lemma lem1595299 (x : real) (y : real) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1595301 (x : real) : term5 x.
Proof. exact (@lem1587920 x). Qed.
Lemma lem1595302 (x : real) : (term5 x) = ((term6 x) = x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1595304 (x : real) : term7 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1595305 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1595306 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem1595305 x) (@lem1595304 x)). Qed.
Lemma lem1595307 (x : real) (y : real) : term9 x y.
Proof. exact (@lem1595306 x y). Qed.
Lemma lem1595308 (x : real) (y : real) : (term9 x y) = ((real_div x y) = (term10 x y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1595321 (x : real) (y : real) : (real_div x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1595308 x y) (@lem1595307 x y)). Qed.
Lemma lem1595322 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1595323 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1595322) (@lem1595321 x y)). Qed.
Lemma lem1595325 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem1595299 x y) (@lem1595298 x y)). Qed.
Lemma lem1595326 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (@lem1595325 x (real_inv y)). Qed.
Lemma lem1595328 (x : real) : (term6 x) = x.
Proof. exact (EQ_MP (@lem1595302 x) (@lem1595301 x)). Qed.
Lemma lem1595329 (y : real) : (term6 y) = y.
Proof. exact (@lem1595328 y). Qed.
Lemma lem1595330 (x : real) : (term14 x) = (term14 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1595331 (x : real) (y : real) : (term13 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1595330 x) (@lem1595329 y)). Qed.
Lemma lem1595332 (x : real) (y : real) : (term12 x y) = (term15 x y).
Proof. exact (TRANS (@lem1595326 x y) (@lem1595331 x y)). Qed.
Lemma lem1595333 (x : real) (y : real) : (term11 x y) = (term15 x y).
Proof. exact (TRANS (@lem1595323 x y) (@lem1595332 x y)). Qed.
Lemma lem1595334 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1595335 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem1595334) (@lem1595333 x y)). Qed.
Lemma lem1595337 (x : real) (y : real) : (real_div x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1595308 x y) (@lem1595307 x y)). Qed.
Lemma lem1595338 (y : real) (x : real) : (real_div y x) = (term10 y x).
Proof. exact (@lem1595337 y x). Qed.
Lemma lem1595339 (y : real) (x : real) : ((term11 x y) = (real_div y x)) = ((term15 x y) = (term10 y x)).
Proof. exact (MK_COMB (@lem1595335 x y) (@lem1595338 y x)). Qed.
Lemma lem1595342 (x : real) : (term18 x) = (term19 x).
Proof. exact (fun_ext (fun y : real => @lem1595339 y x)). Qed.
Lemma lem1595343 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1595344 (x : real) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem1595343) (@lem1595342 x)). Qed.
Lemma lem1595349 : term22 = term23.
Proof. exact (fun_ext (fun x : real => @lem1595344 x)). Qed.
Lemma lem1595350 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1595351 : term24 = term25.
Proof. exact (MK_COMB (@lem1595350) (@lem1595349)). Qed.
Lemma lem1595356 : term25 = term24.
Proof. exact (SYM (@lem1595351)). Qed.
Lemma lem1595357 (x : real) : term26 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem1595358 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1595359 (x : real) : term27 x.
Proof. exact (EQ_MP (@lem1595358 x) (@lem1595357 x)). Qed.
Lemma lem1595360 (x : real) (y : real) : term28 x y.
Proof. exact (@lem1595359 x y). Qed.
Lemma lem1595361 (y : real) (x : real) : (term28 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem1595364 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1595361 y x) (@lem1595360 x y)). Qed.
Lemma lem1595365 (y : real) (x : real) : (term15 x y) = (term10 y x).
Proof. exact (@lem1595364 y (real_inv x)). Qed.
Lemma lem1595370 (x : real) : term21 x.
Proof. exact (fun y : real => @lem1595365 y x). Qed.
Lemma lem1595375 : term25.
Proof. exact (fun x : real => @lem1595370 x). Qed.
Lemma lem1595376 : term24.
Proof. exact (EQ_MP (@lem1595356) (@lem1595375)). Qed.
