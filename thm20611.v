Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20611_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1804_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1857_spec.
Require Import thm20453_spec.
Lemma lem20536 {_739 : Type'} (x : _739) (p : Prop) : (term0 _739 x p) = p.
Proof. exact (EQ_MP (@lem1804 _739 x p) (@lem0)). Qed.
Lemma lem20537 (x : Prop) (p : Prop) : (term1 x p) = p.
Proof. exact (@lem20536 Prop x p). Qed.
Lemma lem20538 (x : Prop) (x0 : Prop) : (term2 x x0) = (x = x0).
Proof. exact (@lem20537 False (x = x0)). Qed.
Lemma lem20541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem20542 (x : Prop) (x0 : Prop) : (term3 x x0) = (term4 x x0).
Proof. exact (MK_COMB (@lem20541) (@lem20538 x x0)). Qed.
Lemma lem20548 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem20549 : (False = True) = (~ True).
Proof. exact (@lem20548 True). Qed.
Lemma lem20551 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem20552 : (False = True) = False.
Proof. exact (TRANS (@lem20549) (@lem20551)). Qed.
Lemma lem20553 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem20554 : term5 = (imp False).
Proof. exact (MK_COMB (@lem20553) (@lem20552)). Qed.
Lemma lem20557 (x : Prop) (x1 : Prop) : (x = x1) = (x = x1).
Proof. exact (eq_refl (x = x1)). Qed.
Lemma lem20558 (x : Prop) (x1 : Prop) : (term6 x x1) = (term7 x x1).
Proof. exact (MK_COMB (@lem20554) (@lem20557 x x1)). Qed.
Lemma lem20560 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem20561 (x : Prop) (x1 : Prop) : (term7 x x1) = True.
Proof. exact (@lem20560 (x = x1)). Qed.
Lemma lem20562 (x : Prop) (x1 : Prop) : (term6 x x1) = True.
Proof. exact (TRANS (@lem20558 x x1) (@lem20561 x x1)). Qed.
Lemma lem20563 (x1 : Prop) (x : Prop) (x0 : Prop) : (term8 x0 x x1) = (term9 x x0).
Proof. exact (MK_COMB (@lem20542 x x0) (@lem20562 x x1)). Qed.
Lemma lem20565 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem20566 (x : Prop) (x0 : Prop) : (term9 x x0) = (x = x0).
Proof. exact (@lem20565 (x = x0)). Qed.
Lemma lem20569 (x1 : Prop) (x : Prop) (x0 : Prop) : (term8 x0 x x1) = (x = x0).
Proof. exact (TRANS (@lem20563 x1 x x0) (@lem20566 x x0)). Qed.
Lemma lem20570 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem20571 (x1 : Prop) (x : Prop) (x0 : Prop) : (term10 x0 x x1) = (term11 x x0).
Proof. exact (MK_COMB (@lem20570) (@lem20569 x1 x x0)). Qed.
Lemma lem20579 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem20580 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem20581 : term12 = (or True).
Proof. exact (MK_COMB (@lem20580) (@lem20579)). Qed.
Lemma lem20582 (x1 : Prop) : x1 = x1.
Proof. exact (eq_refl x1). Qed.
Lemma lem20583 (x1 : Prop) : (term13 x1) = (True \/ x1).
Proof. exact (MK_COMB (@lem20581) (@lem20582 x1)). Qed.
Lemma lem20585 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem20586 (x1 : Prop) : (True \/ x1) = True.
Proof. exact (@lem20585 x1). Qed.
Lemma lem20587 (x1 : Prop) : (term13 x1) = True.
Proof. exact (TRANS (@lem20583 x1) (@lem20586 x1)). Qed.
Lemma lem20588 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem20589 (x1 : Prop) : (term14 x1) = (and True).
Proof. exact (MK_COMB (@lem20588) (@lem20587 x1)). Qed.
Lemma lem20591 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem20592 (x0 : Prop) : (False \/ x0) = x0.
Proof. exact (@lem20591 x0). Qed.
Lemma lem20593 (x1 : Prop) (x0 : Prop) : (term15 x1 x0) = (True /\ x0).
Proof. exact (MK_COMB (@lem20589 x1) (@lem20592 x0)). Qed.
Lemma lem20595 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem20596 (x0 : Prop) : (True /\ x0) = x0.
Proof. exact (@lem20595 x0). Qed.
Lemma lem20597 (x1 : Prop) (x0 : Prop) : (term15 x1 x0) = x0.
Proof. exact (TRANS (@lem20593 x1 x0) (@lem20596 x0)). Qed.
Lemma lem20598 (x : Prop) : (@eq Prop x) = (@eq Prop x).
Proof. exact (eq_refl (@eq Prop x)). Qed.
Lemma lem20599 (x1 : Prop) (x : Prop) (x0 : Prop) : (x = (term15 x1 x0)) = (x = x0).
Proof. exact (MK_COMB (@lem20598 x) (@lem20597 x1 x0)). Qed.
Lemma lem20602 (x1 : Prop) (x : Prop) (x0 : Prop) : (term16 x x1 x0) = (term17 x x0).
Proof. exact (MK_COMB (@lem20571 x1 x x0) (@lem20599 x1 x x0)). Qed.
Lemma lem20606 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem20607 (x : Prop) (x0 : Prop) : (term17 x x0) = True.
Proof. exact (@lem20606 (x = x0)). Qed.
Lemma lem20608 (x : Prop) (x1 : Prop) (x0 : Prop) : (term16 x x1 x0) = True.
Proof. exact (TRANS (@lem20602 x1 x x0) (@lem20607 x x0)). Qed.
Lemma lem20609 (x : Prop) (x1 : Prop) (x0 : Prop) : True = (term16 x x1 x0).
Proof. exact (SYM (@lem20608 x x1 x0)). Qed.
Lemma lem20610 (x : Prop) (x1 : Prop) (x0 : Prop) : term16 x x1 x0.
Proof. exact (EQ_MP (@lem20609 x x1 x0) (@lem0)). Qed.
Lemma lem20611 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = False) : term18 x x1 b x0.
Proof. exact (EQ_MP (@lem20453 x x1 x0 b h1) (@lem20610 x x1 x0)). Qed.
