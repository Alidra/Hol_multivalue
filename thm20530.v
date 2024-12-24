Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20530_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1804_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Lemma lem20463 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem20464 : (True = False) = False.
Proof. exact (@lem20463 False). Qed.
Lemma lem20465 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem20466 : term0 = (imp False).
Proof. exact (MK_COMB (@lem20465) (@lem20464)). Qed.
Lemma lem20469 (x : Prop) (x0 : Prop) : (x = x0) = (x = x0).
Proof. exact (eq_refl (x = x0)). Qed.
Lemma lem20470 (x : Prop) (x0 : Prop) : (term1 x x0) = (term2 x x0).
Proof. exact (MK_COMB (@lem20466) (@lem20469 x x0)). Qed.
Lemma lem20472 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem20473 (x : Prop) (x0 : Prop) : (term2 x x0) = True.
Proof. exact (@lem20472 (x = x0)). Qed.
Lemma lem20474 (x : Prop) (x0 : Prop) : (term1 x x0) = True.
Proof. exact (TRANS (@lem20470 x x0) (@lem20473 x x0)). Qed.
Lemma lem20475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem20476 (x : Prop) (x0 : Prop) : (term3 x x0) = (and True).
Proof. exact (MK_COMB (@lem20475) (@lem20474 x x0)). Qed.
Lemma lem20478 {_739 : Type'} (x : _739) (p : Prop) : (term4 _739 x p) = p.
Proof. exact (EQ_MP (@lem1804 _739 x p) (@lem0)). Qed.
Lemma lem20479 (x : Prop) (p : Prop) : (term5 x p) = p.
Proof. exact (@lem20478 Prop x p). Qed.
Lemma lem20480 (x : Prop) (x1 : Prop) : (term6 x x1) = (x = x1).
Proof. exact (@lem20479 True (x = x1)). Qed.
Lemma lem20483 (x0 : Prop) (x : Prop) (x1 : Prop) : (term7 x0 x x1) = (term8 x x1).
Proof. exact (MK_COMB (@lem20476 x x0) (@lem20480 x x1)). Qed.
Lemma lem20485 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem20486 (x : Prop) (x1 : Prop) : (term8 x x1) = (x = x1).
Proof. exact (@lem20485 (x = x1)). Qed.
Lemma lem20489 (x0 : Prop) (x : Prop) (x1 : Prop) : (term7 x0 x x1) = (x = x1).
Proof. exact (TRANS (@lem20483 x0 x x1) (@lem20486 x x1)). Qed.
Lemma lem20490 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem20491 (x0 : Prop) (x : Prop) (x1 : Prop) : (term9 x0 x x1) = (term10 x x1).
Proof. exact (MK_COMB (@lem20490) (@lem20489 x0 x x1)). Qed.
Lemma lem20499 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem20500 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem20501 : term11 = (or False).
Proof. exact (MK_COMB (@lem20500) (@lem20499)). Qed.
Lemma lem20502 (x1 : Prop) : x1 = x1.
Proof. exact (eq_refl x1). Qed.
Lemma lem20503 (x1 : Prop) : (term12 x1) = (False \/ x1).
Proof. exact (MK_COMB (@lem20501) (@lem20502 x1)). Qed.
Lemma lem20505 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem20506 (x1 : Prop) : (False \/ x1) = x1.
Proof. exact (@lem20505 x1). Qed.
Lemma lem20507 (x1 : Prop) : (term12 x1) = x1.
Proof. exact (TRANS (@lem20503 x1) (@lem20506 x1)). Qed.
Lemma lem20508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem20509 (x1 : Prop) : (term13 x1) = (and x1).
Proof. exact (MK_COMB (@lem20508) (@lem20507 x1)). Qed.
Lemma lem20511 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem20512 (x0 : Prop) : (True \/ x0) = True.
Proof. exact (@lem20511 x0). Qed.
Lemma lem20513 (x0 : Prop) (x1 : Prop) : (term14 x1 x0) = (x1 /\ True).
Proof. exact (MK_COMB (@lem20509 x1) (@lem20512 x0)). Qed.
Lemma lem20515 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem20516 (x1 : Prop) : (x1 /\ True) = x1.
Proof. exact (@lem20515 x1). Qed.
Lemma lem20517 (x0 : Prop) (x1 : Prop) : (term14 x1 x0) = x1.
Proof. exact (TRANS (@lem20513 x0 x1) (@lem20516 x1)). Qed.
Lemma lem20518 (x : Prop) : (@eq Prop x) = (@eq Prop x).
Proof. exact (eq_refl (@eq Prop x)). Qed.
Lemma lem20519 (x0 : Prop) (x : Prop) (x1 : Prop) : (x = (term14 x1 x0)) = (x = x1).
Proof. exact (MK_COMB (@lem20518 x) (@lem20517 x0 x1)). Qed.
Lemma lem20522 (x0 : Prop) (x : Prop) (x1 : Prop) : (term15 x x1 x0) = (term16 x x1).
Proof. exact (MK_COMB (@lem20491 x0 x x1) (@lem20519 x0 x x1)). Qed.
Lemma lem20526 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem20527 (x : Prop) (x1 : Prop) : (term16 x x1) = True.
Proof. exact (@lem20526 (x = x1)). Qed.
Lemma lem20528 (x : Prop) (x1 : Prop) (x0 : Prop) : (term15 x x1 x0) = True.
Proof. exact (TRANS (@lem20522 x0 x x1) (@lem20527 x x1)). Qed.
Lemma lem20529 (x : Prop) (x1 : Prop) (x0 : Prop) : True = (term15 x x1 x0).
Proof. exact (SYM (@lem20528 x x1 x0)). Qed.
Lemma lem20530 (x : Prop) (x1 : Prop) (x0 : Prop) : term15 x x1 x0.
Proof. exact (EQ_MP (@lem20529 x x1 x0) (@lem0)). Qed.
