Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_DIV_term_abbrevs.
Require Import SQRT_INV_spec.
Require Import SQRT_MUL_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1947378 (x : real) : term0 x.
Proof. exact (@lem1947377 x). Qed.
Lemma lem1947379 (x : real) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1947381 (x : real) : term3 x.
Proof. exact (@lem1947279 x). Qed.
Lemma lem1947382 (x : real) : (term3 x) = (term4 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1947383 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1947382 x) (@lem1947381 x)). Qed.
Lemma lem1947384 (x : real) (y : real) : term5 x y.
Proof. exact (@lem1947383 x y). Qed.
Lemma lem1947385 (x : real) (y : real) : (term5 x y) = ((term6 x y) = (term7 x y)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1947387 (x : real) : term8 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1947388 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1947389 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1947388 x) (@lem1947387 x)). Qed.
Lemma lem1947390 (x : real) (y : real) : term10 x y.
Proof. exact (@lem1947389 x y). Qed.
Lemma lem1947391 (x : real) (y : real) : (term10 x y) = ((real_div x y) = (term11 x y)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1947404 (x : real) (y : real) : (real_div x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1947391 x y) (@lem1947390 x y)). Qed.
Lemma lem1947405 : sqrt = sqrt.
Proof. exact (eq_refl sqrt). Qed.
Lemma lem1947406 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1947405) (@lem1947404 x y)). Qed.
Lemma lem1947408 (x : real) (y : real) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1947385 x y) (@lem1947384 x y)). Qed.
Lemma lem1947409 (x : real) (y : real) : (term13 x y) = (term14 x y).
Proof. exact (@lem1947408 x (real_inv y)). Qed.
Lemma lem1947411 (x : real) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem1947379 x) (@lem1947378 x)). Qed.
Lemma lem1947412 (y : real) : (term1 y) = (term2 y).
Proof. exact (@lem1947411 y). Qed.
Lemma lem1947413 (x : real) : (term15 x) = (term15 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1947414 (x : real) (y : real) : (term14 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem1947413 x) (@lem1947412 y)). Qed.
Lemma lem1947415 (x : real) (y : real) : (term13 x y) = (term16 x y).
Proof. exact (TRANS (@lem1947409 x y) (@lem1947414 x y)). Qed.
Lemma lem1947416 (x : real) (y : real) : (term12 x y) = (term16 x y).
Proof. exact (TRANS (@lem1947406 x y) (@lem1947415 x y)). Qed.
Lemma lem1947417 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1947418 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem1947417) (@lem1947416 x y)). Qed.
Lemma lem1947420 (x : real) (y : real) : (real_div x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1947391 x y) (@lem1947390 x y)). Qed.
Lemma lem1947421 (x : real) (y : real) : (term19 x y) = (term16 x y).
Proof. exact (@lem1947420 (sqrt x) (sqrt y)). Qed.
Lemma lem1947422 (x : real) (y : real) : ((term12 x y) = (term19 x y)) = ((term16 x y) = (term16 x y)).
Proof. exact (MK_COMB (@lem1947418 x y) (@lem1947421 x y)). Qed.
Lemma lem1947424 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1947425 (x : real) : (x = x) = True.
Proof. exact (@lem1947424 real x). Qed.
Lemma lem1947426 (x : real) (y : real) : ((term16 x y) = (term16 x y)) = True.
Proof. exact (@lem1947425 (term16 x y)). Qed.
Lemma lem1947427 (x : real) (y : real) : ((term12 x y) = (term19 x y)) = True.
Proof. exact (TRANS (@lem1947422 x y) (@lem1947426 x y)). Qed.
Lemma lem1947428 (x : real) : (term20 x) = term21.
Proof. exact (fun_ext (fun y : real => @lem1947427 x y)). Qed.
Lemma lem1947429 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1947430 (x : real) : (term22 x) = term23.
Proof. exact (MK_COMB (@lem1947429) (@lem1947428 x)). Qed.
Lemma lem1947432 {A : Type'} (t : Prop) : (term24 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1947433 (t : Prop) : (term25 t) = t.
Proof. exact (@lem1947432 real t). Qed.
Lemma lem1947434 : term23 = True.
Proof. exact (@lem1947433 True). Qed.
Lemma lem1947435 (x : real) : (term22 x) = True.
Proof. exact (TRANS (@lem1947430 x) (@lem1947434)). Qed.
Lemma lem1947436 : term26 = term21.
Proof. exact (fun_ext (fun x : real => @lem1947435 x)). Qed.
Lemma lem1947437 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1947438 : term27 = term23.
Proof. exact (MK_COMB (@lem1947437) (@lem1947436)). Qed.
Lemma lem1947440 {A : Type'} (t : Prop) : (term24 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1947441 (t : Prop) : (term25 t) = t.
Proof. exact (@lem1947440 real t). Qed.
Lemma lem1947442 : term23 = True.
Proof. exact (@lem1947441 True). Qed.
Lemma lem1947443 : term27 = True.
Proof. exact (TRANS (@lem1947438) (@lem1947442)). Qed.
Lemma lem1947444 : True = term27.
Proof. exact (SYM (@lem1947443)). Qed.
Lemma lem1947445 : term27.
Proof. exact (EQ_MP (@lem1947444) (@lem0)). Qed.
