Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm19490_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem19382 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem19383 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem19384 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem19383 a) (@lem19382 a)). Qed.
Lemma lem19385 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem19386 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem19401 (b : Prop) (c : Prop) : (term2 b c) = (term2 b c).
Proof. exact (eq_refl (term2 b c)). Qed.
Lemma lem19402 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term3 b c a) = (term4 b c).
Proof. exact (MK_COMB (@lem19401 b c) (@lem19385 a h1)). Qed.
Lemma lem19403 (b : Prop) (c : Prop) : (term4 b c) = ((term5 b c) = (term6 b c)).
Proof. exact (eq_refl (term4 b c)). Qed.
Lemma lem19404 (b : Prop) (c : Prop) (a : Prop) : (term7 b c a) = (term7 b c a).
Proof. exact (eq_refl (term7 b c a)). Qed.
Lemma lem19405 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term4 b c)) = ((term3 b c a) = ((term5 b c) = (term6 b c))).
Proof. exact (MK_COMB (@lem19404 b c a) (@lem19403 b c)). Qed.
Lemma lem19406 (b : Prop) (a : Prop) (c : Prop) : (term3 b c a) = ((term8 a b c) = (term9 b a c)).
Proof. exact (eq_refl (term3 b c a)). Qed.
Lemma lem19407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19408 (b : Prop) (a : Prop) (c : Prop) : (term7 b c a) = (term10 b a c).
Proof. exact (MK_COMB (@lem19407) (@lem19406 b a c)). Qed.
Lemma lem19409 (b : Prop) (c : Prop) : ((term5 b c) = (term6 b c)) = ((term5 b c) = (term6 b c)).
Proof. exact (eq_refl ((term5 b c) = (term6 b c))). Qed.
Lemma lem19410 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = ((term5 b c) = (term6 b c))) = (((term8 a b c) = (term9 b a c)) = ((term5 b c) = (term6 b c))).
Proof. exact (MK_COMB (@lem19408 b a c) (@lem19409 b c)). Qed.
Lemma lem19411 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term4 b c)) = (((term8 a b c) = (term9 b a c)) = ((term5 b c) = (term6 b c))).
Proof. exact (TRANS (@lem19405 a b c) (@lem19410 a b c)). Qed.
Lemma lem19412 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term8 a b c) = (term9 b a c)) = ((term5 b c) = (term6 b c)).
Proof. exact (EQ_MP (@lem19411 a b c) (@lem19402 b c a h1)). Qed.
Lemma lem19413 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term5 b c) = (term6 b c)) = ((term8 a b c) = (term9 b a c)).
Proof. exact (SYM (@lem19412 b c a h1)). Qed.
Lemma lem19414 (b : Prop) (c : Prop) : (term2 b c) = (term2 b c).
Proof. exact (eq_refl (term2 b c)). Qed.
Lemma lem19415 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term3 b c a) = (term11 b c).
Proof. exact (MK_COMB (@lem19414 b c) (@lem19386 a h1)). Qed.
Lemma lem19416 (b : Prop) (c : Prop) : (term11 b c) = ((term12 b c) = (term13 b c)).
Proof. exact (eq_refl (term11 b c)). Qed.
Lemma lem19417 (b : Prop) (c : Prop) (a : Prop) : (term7 b c a) = (term7 b c a).
Proof. exact (eq_refl (term7 b c a)). Qed.
Lemma lem19418 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term11 b c)) = ((term3 b c a) = ((term12 b c) = (term13 b c))).
Proof. exact (MK_COMB (@lem19417 b c a) (@lem19416 b c)). Qed.
Lemma lem19419 (b : Prop) (a : Prop) (c : Prop) : (term3 b c a) = ((term8 a b c) = (term9 b a c)).
Proof. exact (eq_refl (term3 b c a)). Qed.
Lemma lem19420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19421 (b : Prop) (a : Prop) (c : Prop) : (term7 b c a) = (term10 b a c).
Proof. exact (MK_COMB (@lem19420) (@lem19419 b a c)). Qed.
Lemma lem19422 (b : Prop) (c : Prop) : ((term12 b c) = (term13 b c)) = ((term12 b c) = (term13 b c)).
Proof. exact (eq_refl ((term12 b c) = (term13 b c))). Qed.
Lemma lem19423 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = ((term12 b c) = (term13 b c))) = (((term8 a b c) = (term9 b a c)) = ((term12 b c) = (term13 b c))).
Proof. exact (MK_COMB (@lem19421 b a c) (@lem19422 b c)). Qed.
Lemma lem19424 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term11 b c)) = (((term8 a b c) = (term9 b a c)) = ((term12 b c) = (term13 b c))).
Proof. exact (TRANS (@lem19418 a b c) (@lem19423 a b c)). Qed.
Lemma lem19425 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term8 a b c) = (term9 b a c)) = ((term12 b c) = (term13 b c)).
Proof. exact (EQ_MP (@lem19424 a b c) (@lem19415 b c a h1)). Qed.
Lemma lem19426 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term12 b c) = (term13 b c)) = ((term8 a b c) = (term9 b a c)).
Proof. exact (SYM (@lem19425 b c a h1)). Qed.
Lemma lem19430 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem19431 (b : Prop) (c : Prop) : (term5 b c) = True.
Proof. exact (@lem19430 (b /\ c)). Qed.
Lemma lem19432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19433 (b : Prop) (c : Prop) : (term14 b c) = (@eq Prop True).
Proof. exact (MK_COMB (@lem19432) (@lem19431 b c)). Qed.
Lemma lem19437 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem19438 (b : Prop) : (True \/ b) = True.
Proof. exact (@lem19437 b). Qed.
Lemma lem19439 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem19440 (b : Prop) : (term15 b) = (and True).
Proof. exact (MK_COMB (@lem19439) (@lem19438 b)). Qed.
Lemma lem19442 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem19443 (c : Prop) : (True \/ c) = True.
Proof. exact (@lem19442 c). Qed.
Lemma lem19444 (b : Prop) (c : Prop) : (term6 b c) = (True /\ True).
Proof. exact (MK_COMB (@lem19440 b) (@lem19443 c)). Qed.
Lemma lem19446 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem19447 : (True /\ True) = True.
Proof. exact (@lem19446 True). Qed.
Lemma lem19448 (b : Prop) (c : Prop) : (term6 b c) = True.
Proof. exact (TRANS (@lem19444 b c) (@lem19447)). Qed.
Lemma lem19449 (b : Prop) (c : Prop) : ((term5 b c) = (term6 b c)) = (True = True).
Proof. exact (MK_COMB (@lem19433 b c) (@lem19448 b c)). Qed.
Lemma lem19451 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem19452 : (True = True) = True.
Proof. exact (@lem19451 True). Qed.
Lemma lem19453 (b : Prop) (c : Prop) : ((term5 b c) = (term6 b c)) = True.
Proof. exact (TRANS (@lem19449 b c) (@lem19452)). Qed.
Lemma lem19454 (b : Prop) (c : Prop) : True = ((term5 b c) = (term6 b c)).
Proof. exact (SYM (@lem19453 b c)). Qed.
Lemma lem19455 (b : Prop) (c : Prop) : (term5 b c) = (term6 b c).
Proof. exact (EQ_MP (@lem19454 b c) (@lem0)). Qed.
Lemma lem19459 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem19460 (b : Prop) (c : Prop) : (term12 b c) = (b /\ c).
Proof. exact (@lem19459 (b /\ c)). Qed.
Lemma lem19463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19464 (b : Prop) (c : Prop) : (term16 b c) = (term17 b c).
Proof. exact (MK_COMB (@lem19463) (@lem19460 b c)). Qed.
Lemma lem19468 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem19469 (b : Prop) : (False \/ b) = b.
Proof. exact (@lem19468 b). Qed.
Lemma lem19470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem19471 (b : Prop) : (term18 b) = (and b).
Proof. exact (MK_COMB (@lem19470) (@lem19469 b)). Qed.
Lemma lem19473 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem19474 (c : Prop) : (False \/ c) = c.
Proof. exact (@lem19473 c). Qed.
Lemma lem19475 (b : Prop) (c : Prop) : (term13 b c) = (b /\ c).
Proof. exact (MK_COMB (@lem19471 b) (@lem19474 c)). Qed.
Lemma lem19478 (b : Prop) (c : Prop) : ((term12 b c) = (term13 b c)) = ((b /\ c) = (b /\ c)).
Proof. exact (MK_COMB (@lem19464 b c) (@lem19475 b c)). Qed.
Lemma lem19480 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem19481 (x : Prop) : (x = x) = True.
Proof. exact (@lem19480 Prop x). Qed.
Lemma lem19482 (b : Prop) (c : Prop) : ((b /\ c) = (b /\ c)) = True.
Proof. exact (@lem19481 (b /\ c)). Qed.
Lemma lem19483 (b : Prop) (c : Prop) : ((term12 b c) = (term13 b c)) = True.
Proof. exact (TRANS (@lem19478 b c) (@lem19482 b c)). Qed.
Lemma lem19484 (b : Prop) (c : Prop) : True = ((term12 b c) = (term13 b c)).
Proof. exact (SYM (@lem19483 b c)). Qed.
Lemma lem19485 (b : Prop) (c : Prop) : (term12 b c) = (term13 b c).
Proof. exact (EQ_MP (@lem19484 b c) (@lem0)). Qed.
Lemma lem19486 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term8 a b c) = (term9 b a c).
Proof. exact (EQ_MP (@lem19426 b c a h1) (@lem19485 b c)). Qed.
Lemma lem19487 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term8 a b c) = (term9 b a c).
Proof. exact (EQ_MP (@lem19413 b c a h1) (@lem19455 b c)). Qed.
Lemma lem19490 (b : Prop) (a : Prop) (c : Prop) : (term8 a b c) = (term9 b a c).
Proof. exact (or_elim (@lem19384 a) (fun h0 : a = True => @lem19487 b c a h0) (fun h0 : a = False => @lem19486 b c a h0)). Qed.
