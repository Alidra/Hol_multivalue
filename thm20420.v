Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20420_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1804_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm20262_spec.
Lemma lem20345 {_739 : Type'} (x : _739) (p : Prop) : (term0 _739 x p) = p.
Proof. exact (EQ_MP (@lem1804 _739 x p) (@lem0)). Qed.
Lemma lem20346 (x : Prop) (p : Prop) : (term1 x p) = p.
Proof. exact (@lem20345 Prop x p). Qed.
Lemma lem20347 (x : Prop) (x0 : Prop) : (term2 x x0) = (x = x0).
Proof. exact (@lem20346 False (x = x0)). Qed.
Lemma lem20350 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem20351 (x : Prop) (x0 : Prop) : (term3 x x0) = (term4 x x0).
Proof. exact (MK_COMB (@lem20350) (@lem20347 x x0)). Qed.
Lemma lem20357 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem20358 : (False = True) = (~ True).
Proof. exact (@lem20357 True). Qed.
Lemma lem20360 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem20361 : (False = True) = False.
Proof. exact (TRANS (@lem20358) (@lem20360)). Qed.
Lemma lem20362 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem20363 : term5 = (imp False).
Proof. exact (MK_COMB (@lem20362) (@lem20361)). Qed.
Lemma lem20366 (x : Prop) (x1 : Prop) : (x = x1) = (x = x1).
Proof. exact (eq_refl (x = x1)). Qed.
Lemma lem20367 (x : Prop) (x1 : Prop) : (term6 x x1) = (term7 x x1).
Proof. exact (MK_COMB (@lem20363) (@lem20366 x x1)). Qed.
Lemma lem20369 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem20370 (x : Prop) (x1 : Prop) : (term7 x x1) = True.
Proof. exact (@lem20369 (x = x1)). Qed.
Lemma lem20371 (x : Prop) (x1 : Prop) : (term6 x x1) = True.
Proof. exact (TRANS (@lem20367 x x1) (@lem20370 x x1)). Qed.
Lemma lem20372 (x1 : Prop) (x : Prop) (x0 : Prop) : (term8 x0 x x1) = (term9 x x0).
Proof. exact (MK_COMB (@lem20351 x x0) (@lem20371 x x1)). Qed.
Lemma lem20374 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem20375 (x : Prop) (x0 : Prop) : (term9 x x0) = (x = x0).
Proof. exact (@lem20374 (x = x0)). Qed.
Lemma lem20378 (x1 : Prop) (x : Prop) (x0 : Prop) : (term8 x0 x x1) = (x = x0).
Proof. exact (TRANS (@lem20372 x1 x x0) (@lem20375 x x0)). Qed.
Lemma lem20379 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem20380 (x1 : Prop) (x : Prop) (x0 : Prop) : (term10 x0 x x1) = (term11 x x0).
Proof. exact (MK_COMB (@lem20379) (@lem20378 x1 x x0)). Qed.
Lemma lem20386 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem20387 (x1 : Prop) : (False /\ x1) = False.
Proof. exact (@lem20386 x1). Qed.
Lemma lem20388 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem20389 (x1 : Prop) : (term12 x1) = (or False).
Proof. exact (MK_COMB (@lem20388) (@lem20387 x1)). Qed.
Lemma lem20393 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem20394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem20395 : term13 = (and True).
Proof. exact (MK_COMB (@lem20394) (@lem20393)). Qed.
Lemma lem20396 (x0 : Prop) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem20397 (x0 : Prop) : (term14 x0) = (True /\ x0).
Proof. exact (MK_COMB (@lem20395) (@lem20396 x0)). Qed.
Lemma lem20399 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem20400 (x0 : Prop) : (True /\ x0) = x0.
Proof. exact (@lem20399 x0). Qed.
Lemma lem20401 (x0 : Prop) : (term14 x0) = x0.
Proof. exact (TRANS (@lem20397 x0) (@lem20400 x0)). Qed.
Lemma lem20402 (x1 : Prop) (x0 : Prop) : (term15 x1 x0) = (False \/ x0).
Proof. exact (MK_COMB (@lem20389 x1) (@lem20401 x0)). Qed.
Lemma lem20404 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem20405 (x0 : Prop) : (False \/ x0) = x0.
Proof. exact (@lem20404 x0). Qed.
Lemma lem20406 (x1 : Prop) (x0 : Prop) : (term15 x1 x0) = x0.
Proof. exact (TRANS (@lem20402 x1 x0) (@lem20405 x0)). Qed.
Lemma lem20407 (x : Prop) : (@eq Prop x) = (@eq Prop x).
Proof. exact (eq_refl (@eq Prop x)). Qed.
Lemma lem20408 (x1 : Prop) (x : Prop) (x0 : Prop) : (x = (term15 x1 x0)) = (x = x0).
Proof. exact (MK_COMB (@lem20407 x) (@lem20406 x1 x0)). Qed.
Lemma lem20411 (x1 : Prop) (x : Prop) (x0 : Prop) : (term16 x x1 x0) = (term17 x x0).
Proof. exact (MK_COMB (@lem20380 x1 x x0) (@lem20408 x1 x x0)). Qed.
Lemma lem20415 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem20416 (x : Prop) (x0 : Prop) : (term17 x x0) = True.
Proof. exact (@lem20415 (x = x0)). Qed.
Lemma lem20417 (x : Prop) (x1 : Prop) (x0 : Prop) : (term16 x x1 x0) = True.
Proof. exact (TRANS (@lem20411 x1 x x0) (@lem20416 x x0)). Qed.
Lemma lem20418 (x : Prop) (x1 : Prop) (x0 : Prop) : True = (term16 x x1 x0).
Proof. exact (SYM (@lem20417 x x1 x0)). Qed.
Lemma lem20419 (x : Prop) (x1 : Prop) (x0 : Prop) : term16 x x1 x0.
Proof. exact (EQ_MP (@lem20418 x x1 x0) (@lem0)). Qed.
Lemma lem20420 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = False) : term18 x x1 b x0.
Proof. exact (EQ_MP (@lem20262 x x1 x0 b h1) (@lem20419 x x1 x0)). Qed.
