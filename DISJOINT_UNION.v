Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJOINT_UNION_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211738_spec.
Require Import thm3211739_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3265534 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem3265535 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3265534 A s t). Qed.
Lemma lem3265536 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term0 A s t u) = ((term1 A s t u) = (@EMPTY A)).
Proof. exact (@lem3265535 A (@UNION A s t) u). Qed.
Lemma lem3265540 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3265541 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (@lem3265540 A s t). Qed.
Lemma lem3265542 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : ((term1 A s t u) = (@EMPTY A)) = (term3 A s t u).
Proof. exact (@lem3265541 A (term1 A s t u) (@EMPTY A)). Qed.
Lemma lem3265547 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term0 A s t u) = (term3 A s t u).
Proof. exact (TRANS (@lem3265536 A s t u) (@lem3265542 A s t u)). Qed.
Lemma lem3265552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3265553 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term4 A s t u) = (term5 A s t u).
Proof. exact (MK_COMB (@lem3265552) (@lem3265547 A s t u)). Qed.
Lemma lem3265557 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem3265558 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3265557 A s t). Qed.
Lemma lem3265559 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@DISJOINT A s u) = ((@INTER A s u) = (@EMPTY A)).
Proof. exact (@lem3265558 A s u). Qed.
Lemma lem3265563 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3265564 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (@lem3265563 A s t). Qed.
Lemma lem3265565 {A : Type'} (s : A -> Prop) (u : A -> Prop) : ((@INTER A s u) = (@EMPTY A)) = (term6 A s u).
Proof. exact (@lem3265564 A (@INTER A s u) (@EMPTY A)). Qed.
Lemma lem3265570 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@DISJOINT A s u) = (term6 A s u).
Proof. exact (TRANS (@lem3265559 A s u) (@lem3265565 A s u)). Qed.
Lemma lem3265575 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3265576 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term7 A s u) = (term8 A s u).
Proof. exact (MK_COMB (@lem3265575) (@lem3265570 A s u)). Qed.
Lemma lem3265578 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem3265579 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3265578 A s t). Qed.
Lemma lem3265580 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@DISJOINT A t u) = ((@INTER A t u) = (@EMPTY A)).
Proof. exact (@lem3265579 A t u). Qed.
Lemma lem3265584 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3265585 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (@lem3265584 A s t). Qed.
Lemma lem3265586 {A : Type'} (t : A -> Prop) (u : A -> Prop) : ((@INTER A t u) = (@EMPTY A)) = (term6 A t u).
Proof. exact (@lem3265585 A (@INTER A t u) (@EMPTY A)). Qed.
Lemma lem3265591 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@DISJOINT A t u) = (term6 A t u).
Proof. exact (TRANS (@lem3265580 A t u) (@lem3265586 A t u)). Qed.
Lemma lem3265596 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term9 A s t u) = (term10 A s t u).
Proof. exact (MK_COMB (@lem3265576 A s u) (@lem3265591 A t u)). Qed.
Lemma lem3265599 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : ((term0 A s t u) = (term9 A s t u)) = ((term3 A s t u) = (term10 A s t u)).
Proof. exact (MK_COMB (@lem3265553 A s t u) (@lem3265596 A s t u)). Qed.
Lemma lem3265604 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term11 A s t) = (term12 A s t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3265599 A s t u)). Qed.
Lemma lem3265605 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3265606 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term13 A s t) = (term14 A s t).
Proof. exact (MK_COMB (@lem3265605 A) (@lem3265604 A s t)). Qed.
Lemma lem3265611 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3265606 A s t)). Qed.
Lemma lem3265612 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3265613 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (MK_COMB (@lem3265612 A) (@lem3265611 A s)). Qed.
Lemma lem3265618 {A : Type'} : (term19 A) = (term20 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3265613 A s)). Qed.
Lemma lem3265619 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3265620 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (MK_COMB (@lem3265619 A) (@lem3265618 A)). Qed.
Lemma lem3265625 {A : Type'} : (term22 A) = (term21 A).
Proof. exact (SYM (@lem3265620 A)). Qed.
Lemma lem3265647 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term23 A x s t) = (term24 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3265648 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term23 A x s t) = (term24 A s x t).
Proof. exact (@lem3265647 A s x t). Qed.
Lemma lem3265649 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (u : A -> Prop) : (term25 A x s t u) = (term26 A s t x u).
Proof. exact (@lem3265648 A (@UNION A s t) x u). Qed.
Lemma lem3265653 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term27 A x s t) = (term28 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3265654 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term27 A x s t) = (term28 A s x t).
Proof. exact (@lem3265653 A s x t). Qed.
Lemma lem3265658 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3265659 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3265658 A P x). Qed.
Lemma lem3265660 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3265659 A s x). Qed.
Lemma lem3265661 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3265662 {A : Type'} (s : A -> Prop) (x : A) : (term29 A x s) = (term30 A s x).
Proof. exact (MK_COMB (@lem3265661) (@lem3265660 A s x)). Qed.
Lemma lem3265664 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3265665 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3265664 A P x). Qed.
Lemma lem3265666 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3265665 A t x). Qed.
Lemma lem3265667 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term28 A s x t) = (term31 A s t x).
Proof. exact (MK_COMB (@lem3265662 A s x) (@lem3265666 A t x)). Qed.
Lemma lem3265670 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term27 A x s t) = (term31 A s t x).
Proof. exact (TRANS (@lem3265654 A s x t) (@lem3265667 A s t x)). Qed.
Lemma lem3265671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3265672 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term32 A x s t) = (term33 A s t x).
Proof. exact (MK_COMB (@lem3265671) (@lem3265670 A s t x)). Qed.
Lemma lem3265674 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3265675 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3265674 A P x). Qed.
Lemma lem3265676 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3265675 A u x). Qed.
Lemma lem3265677 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term26 A s t x u) = (term34 A s t u x).
Proof. exact (MK_COMB (@lem3265672 A s t x) (@lem3265676 A u x)). Qed.
Lemma lem3265680 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term25 A x s t u) = (term34 A s t u x).
Proof. exact (TRANS (@lem3265649 A s t x u) (@lem3265677 A s t u x)). Qed.
Lemma lem3265681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3265682 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term35 A x s t u) = (term36 A s t u x).
Proof. exact (MK_COMB (@lem3265681) (@lem3265680 A s t u x)). Qed.
Lemma lem3265684 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3265685 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3265684 A x). Qed.
Lemma lem3265686 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : ((term25 A x s t u) = (@IN A x (@EMPTY A))) = ((term34 A s t u x) = False).
Proof. exact (MK_COMB (@lem3265682 A s t u x) (@lem3265685 A x)). Qed.
Lemma lem3265688 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3265689 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : ((term34 A s t u x) = False) = (term37 A s t u x).
Proof. exact (@lem3265688 (term34 A s t u x)). Qed.
Lemma lem3265694 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : ((term25 A x s t u) = (@IN A x (@EMPTY A))) = (term37 A s t u x).
Proof. exact (TRANS (@lem3265686 A s t u x) (@lem3265689 A s t u x)). Qed.
Lemma lem3265695 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term38 A s t u) = (term39 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3265694 A s t u x)). Qed.
Lemma lem3265696 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3265697 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term3 A s t u) = (term40 A s t u).
Proof. exact (MK_COMB (@lem3265696 A) (@lem3265695 A s t u)). Qed.
Lemma lem3265702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3265703 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term5 A s t u) = (term41 A s t u).
Proof. exact (MK_COMB (@lem3265702) (@lem3265697 A s t u)). Qed.
Lemma lem3265713 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term23 A x s t) = (term24 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3265714 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term23 A x s t) = (term24 A s x t).
Proof. exact (@lem3265713 A s x t). Qed.
Lemma lem3265715 {A : Type'} (s : A -> Prop) (x : A) (u : A -> Prop) : (term23 A x s u) = (term24 A s x u).
Proof. exact (@lem3265714 A s x u). Qed.
Lemma lem3265719 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3265720 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3265719 A P x). Qed.
Lemma lem3265721 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3265720 A s x). Qed.
Lemma lem3265722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3265723 {A : Type'} (s : A -> Prop) (x : A) : (term42 A x s) = (term43 A s x).
Proof. exact (MK_COMB (@lem3265722) (@lem3265721 A s x)). Qed.
Lemma lem3265725 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3265726 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3265725 A P x). Qed.
Lemma lem3265727 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3265726 A u x). Qed.
Lemma lem3265728 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term24 A s x u) = (term44 A s u x).
Proof. exact (MK_COMB (@lem3265723 A s x) (@lem3265727 A u x)). Qed.
Lemma lem3265731 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term23 A x s u) = (term44 A s u x).
Proof. exact (TRANS (@lem3265715 A s x u) (@lem3265728 A s u x)). Qed.
Lemma lem3265732 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3265733 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term45 A x s u) = (term46 A s u x).
Proof. exact (MK_COMB (@lem3265732) (@lem3265731 A s u x)). Qed.
Lemma lem3265735 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3265736 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3265735 A x). Qed.
Lemma lem3265737 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : ((term23 A x s u) = (@IN A x (@EMPTY A))) = ((term44 A s u x) = False).
Proof. exact (MK_COMB (@lem3265733 A s u x) (@lem3265736 A x)). Qed.
Lemma lem3265739 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3265740 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : ((term44 A s u x) = False) = (term47 A s u x).
Proof. exact (@lem3265739 (term44 A s u x)). Qed.
Lemma lem3265743 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : ((term23 A x s u) = (@IN A x (@EMPTY A))) = (term47 A s u x).
Proof. exact (TRANS (@lem3265737 A s u x) (@lem3265740 A s u x)). Qed.
Lemma lem3265744 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term48 A s u) = (term49 A s u).
Proof. exact (fun_ext (fun x : A => @lem3265743 A s u x)). Qed.
Lemma lem3265745 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3265746 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term6 A s u) = (term50 A s u).
Proof. exact (MK_COMB (@lem3265745 A) (@lem3265744 A s u)). Qed.
Lemma lem3265751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3265752 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term8 A s u) = (term51 A s u).
Proof. exact (MK_COMB (@lem3265751) (@lem3265746 A s u)). Qed.
Lemma lem3265760 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term23 A x s t) = (term24 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3265761 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term23 A x s t) = (term24 A s x t).
Proof. exact (@lem3265760 A s x t). Qed.
Lemma lem3265762 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term23 A x t u) = (term24 A t x u).
Proof. exact (@lem3265761 A t x u). Qed.
Lemma lem3265766 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3265767 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3265766 A P x). Qed.
Lemma lem3265768 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3265767 A t x). Qed.
Lemma lem3265769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3265770 {A : Type'} (t : A -> Prop) (x : A) : (term42 A x t) = (term43 A t x).
Proof. exact (MK_COMB (@lem3265769) (@lem3265768 A t x)). Qed.
Lemma lem3265772 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3265773 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3265772 A P x). Qed.
Lemma lem3265774 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3265773 A u x). Qed.
Lemma lem3265775 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term24 A t x u) = (term44 A t u x).
Proof. exact (MK_COMB (@lem3265770 A t x) (@lem3265774 A u x)). Qed.
Lemma lem3265778 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term23 A x t u) = (term44 A t u x).
Proof. exact (TRANS (@lem3265762 A t x u) (@lem3265775 A t u x)). Qed.
Lemma lem3265779 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3265780 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term45 A x t u) = (term46 A t u x).
Proof. exact (MK_COMB (@lem3265779) (@lem3265778 A t u x)). Qed.
Lemma lem3265782 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3265783 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3265782 A x). Qed.
Lemma lem3265784 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : ((term23 A x t u) = (@IN A x (@EMPTY A))) = ((term44 A t u x) = False).
Proof. exact (MK_COMB (@lem3265780 A t u x) (@lem3265783 A x)). Qed.
Lemma lem3265786 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3265787 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : ((term44 A t u x) = False) = (term47 A t u x).
Proof. exact (@lem3265786 (term44 A t u x)). Qed.
Lemma lem3265790 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : ((term23 A x t u) = (@IN A x (@EMPTY A))) = (term47 A t u x).
Proof. exact (TRANS (@lem3265784 A t u x) (@lem3265787 A t u x)). Qed.
Lemma lem3265791 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term48 A t u) = (term49 A t u).
Proof. exact (fun_ext (fun x : A => @lem3265790 A t u x)). Qed.
Lemma lem3265792 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3265793 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term6 A t u) = (term50 A t u).
Proof. exact (MK_COMB (@lem3265792 A) (@lem3265791 A t u)). Qed.
Lemma lem3265798 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term10 A s t u) = (term52 A s t u).
Proof. exact (MK_COMB (@lem3265752 A s u) (@lem3265793 A t u)). Qed.
Lemma lem3265801 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : ((term3 A s t u) = (term10 A s t u)) = ((term40 A s t u) = (term52 A s t u)).
Proof. exact (MK_COMB (@lem3265703 A s t u) (@lem3265798 A s t u)). Qed.
Lemma lem3265804 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term12 A s t) = (term53 A s t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3265801 A s t u)). Qed.
Lemma lem3265805 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3265806 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term14 A s t) = (term54 A s t).
Proof. exact (MK_COMB (@lem3265805 A) (@lem3265804 A s t)). Qed.
Lemma lem3265811 {A : Type'} (s : A -> Prop) : (term16 A s) = (term55 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3265806 A s t)). Qed.
Lemma lem3265812 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3265813 {A : Type'} (s : A -> Prop) : (term18 A s) = (term56 A s).
Proof. exact (MK_COMB (@lem3265812 A) (@lem3265811 A s)). Qed.
Lemma lem3265818 {A : Type'} : (term20 A) = (term57 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3265813 A s)). Qed.
Lemma lem3265819 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3265820 {A : Type'} : (term22 A) = (term58 A).
Proof. exact (MK_COMB (@lem3265819 A) (@lem3265818 A)). Qed.
Lemma lem3265825 {A : Type'} : (term58 A) = (term22 A).
Proof. exact (SYM (@lem3265820 A)). Qed.
Lemma lem3265827 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3265828 {A : Type'} : (term58 A) = (term60 A).
Proof. exact (@lem3265827 (term58 A)). Qed.
Lemma lem3265829 {A : Type'} : (term60 A) = (term58 A).
Proof. exact (SYM (@lem3265828 A)). Qed.
Lemma lem3265830 {A : Type'} (h1 : term61 A) : term61 A.
Proof. exact (h1). Qed.
Lemma lem3265833 {A : Type'} (h1 : term60 A) : term60 A.
Proof. exact (h1). Qed.
Lemma lem3265834 {A : Type'} : term62 A.
Proof. exact (fun h0 : term60 A => @lem3265833 A h0). Qed.
Lemma lem3265835 {A : Type'} (h1 : term62 A) : term62 A.
Proof. exact (h1). Qed.
Lemma lem3265836 {A : Type'} (h1 : term60 A) : term60 A.
Proof. exact (h1). Qed.
Lemma lem3265837 {A : Type'} (h1 : term60 A) (h2 : term62 A) : term60 A.
Proof. exact (@lem3265835 A h2 (@lem3265836 A h1)). Qed.
Lemma lem3265838 {A : Type'} (h1 : term60 A) : term63 A.
Proof. exact (fun h0 : term62 A => @lem3265837 A h1 h0). Qed.
Lemma lem3265839 {A : Type'} (h1 : term62 A) : term62 A.
Proof. exact (h1). Qed.
Lemma lem3265840 {A : Type'} (h1 : term60 A) (h2 : term62 A) : term60 A.
Proof. exact (@lem3265838 A h1 (@lem3265839 A h2)). Qed.
Lemma lem3265841 {A : Type'} (h1 : term62 A) : term62 A.
Proof. exact (fun h0 : term60 A => @lem3265840 A h0 h1). Qed.
Lemma lem3265842 {A : Type'} : term64 A.
Proof. exact (fun h0 : term62 A => @lem3265841 A h0). Qed.
Lemma lem3265845 {A : Type'} : term62 A.
Proof. exact (@lem3265842 A (@lem3265834 A)). Qed.
Lemma lem3265846 {A : Type'} : term62 A.
Proof. exact (@lem3265845 A). Qed.
Lemma lem3265848 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3265849 {A : Type'} : (term60 A) = (term65 A).
Proof. exact (@lem3265848 (term61 A)). Qed.
Lemma lem3265851 (t : Prop) : (term66 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3265852 {A : Type'} : (term65 A) = (term58 A).
Proof. exact (@lem3265851 (term58 A)). Qed.
Lemma lem3265891 {A : Type'} : (term60 A) = (term58 A).
Proof. exact (TRANS (@lem3265849 A) (@lem3265852 A)). Qed.
Lemma lem3265898 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term47 A t u x) = (term47 A t u x).
Proof. exact (eq_refl (term47 A t u x)). Qed.
Lemma lem3265899 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term49 A t u) = (term49 A t u).
Proof. exact (fun_ext (fun x : A => @lem3265898 A t u x)). Qed.
Lemma lem3265900 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3265901 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term50 A t u) = (term50 A t u).
Proof. exact (MK_COMB (@lem3265900 A) (@lem3265899 A t u)). Qed.
Lemma lem3265908 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term47 A s u x) = (term47 A s u x).
Proof. exact (eq_refl (term47 A s u x)). Qed.
Lemma lem3265909 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term49 A s u) = (term49 A s u).
Proof. exact (fun_ext (fun x : A => @lem3265908 A s u x)). Qed.
Lemma lem3265910 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3265911 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term50 A s u) = (term50 A s u).
Proof. exact (MK_COMB (@lem3265910 A) (@lem3265909 A s u)). Qed.
Lemma lem3265912 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3265913 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term51 A s u) = (term51 A s u).
Proof. exact (MK_COMB (@lem3265912) (@lem3265911 A s u)). Qed.
Lemma lem3265914 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term52 A s t u) = (term52 A s t u).
Proof. exact (MK_COMB (@lem3265913 A s u) (@lem3265901 A t u)). Qed.
Lemma lem3265925 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term37 A s t u x) = (term37 A s t u x).
Proof. exact (eq_refl (term37 A s t u x)). Qed.
Lemma lem3265926 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term39 A s t u) = (term39 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3265925 A s t u x)). Qed.
Lemma lem3265927 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3265928 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term40 A s t u) = (term40 A s t u).
Proof. exact (MK_COMB (@lem3265927 A) (@lem3265926 A s t u)). Qed.
Lemma lem3265929 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3265930 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term41 A s t u) = (term41 A s t u).
Proof. exact (MK_COMB (@lem3265929) (@lem3265928 A s t u)). Qed.
Lemma lem3265931 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : ((term40 A s t u) = (term52 A s t u)) = ((term40 A s t u) = (term52 A s t u)).
Proof. exact (MK_COMB (@lem3265930 A s t u) (@lem3265914 A s t u)). Qed.
Lemma lem3265932 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term53 A s t) = (term53 A s t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3265931 A s t u)). Qed.
Lemma lem3265933 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3265934 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term54 A s t) = (term54 A s t).
Proof. exact (MK_COMB (@lem3265933 A) (@lem3265932 A s t)). Qed.
Lemma lem3265935 {A : Type'} (s : A -> Prop) : (term55 A s) = (term55 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3265934 A s t)). Qed.
Lemma lem3265936 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3265937 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (MK_COMB (@lem3265936 A) (@lem3265935 A s)). Qed.
Lemma lem3265938 {A : Type'} : (term57 A) = (term57 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3265937 A s)). Qed.
Lemma lem3265939 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3265940 {A : Type'} : (term58 A) = (term58 A).
Proof. exact (MK_COMB (@lem3265939 A) (@lem3265938 A)). Qed.
Lemma lem3265989 {A : Type'} : (term60 A) = (term58 A).
Proof. exact (TRANS (@lem3265891 A) (@lem3265940 A)). Qed.
Lemma lem3265990 {A : Type'} : (term58 A) = (term60 A).
Proof. exact (SYM (@lem3265989 A)). Qed.
Lemma lem3265992 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3265993 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : ((term40 A s t u) = (term52 A s t u)) = (term67 A s t u).
Proof. exact (@lem3265992 ((term40 A s t u) = (term52 A s t u))). Qed.
Lemma lem3265994 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term67 A s t u) = ((term40 A s t u) = (term52 A s t u)).
Proof. exact (SYM (@lem3265993 A s t u)). Qed.
Lemma lem3265995 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term68 A s t u) : term68 A s t u.
Proof. exact (h1). Qed.
Lemma lem3266004 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term69 A s t x) = (term70 A s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem3266008 {A : Type'} (u : A -> Prop) (x : A) : (term71 A u x) = (term71 A u x).
Proof. exact (eq_refl (term71 A u x)). Qed.
Lemma lem3266010 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3266011 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term72 A s t x) = (term73 A s t x).
Proof. exact (MK_COMB (@lem3266010) (@lem3266004 A s t x)). Qed.
Lemma lem3266012 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term74 A s t u x) = (term75 A s t u x).
Proof. exact (MK_COMB (@lem3266011 A s t x) (@lem3266008 A u x)). Qed.
Lemma lem3266013 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term37 A s t u x) = (term74 A s t u x).
Proof. exact (@lem17045 (term31 A s t x) (u x)). Qed.
Lemma lem3266014 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term37 A s t u x) = (term75 A s t u x).
Proof. exact (TRANS (@lem3266013 A s t u x) (@lem3266012 A s t u x)). Qed.
Lemma lem3266019 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term76 A s t u x) = (term34 A s t u x).
Proof. exact (@lem16933 (term34 A s t u x)). Qed.
Lemma lem3266020 {A : Type'} (P : A -> Prop) : (term77 A P) = (term78 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3266021 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term79 A s t u) = (term80 A s t u).
Proof. exact (@lem3266020 A (term39 A s t u)). Qed.
Lemma lem3266022 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term81 A s t u x) = (term37 A s t u x).
Proof. exact (eq_refl (term81 A s t u x)). Qed.
Lemma lem3266023 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3266024 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term82 A s t u x) = (term76 A s t u x).
Proof. exact (MK_COMB (@lem3266023) (@lem3266022 A s t u x)). Qed.
Lemma lem3266025 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term82 A s t u x) = (term34 A s t u x).
Proof. exact (TRANS (@lem3266024 A s t u x) (@lem3266019 A s t u x)). Qed.
Lemma lem3266026 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term83 A s t u) = (term84 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3266025 A s t u x)). Qed.
Lemma lem3266027 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3266028 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term80 A s t u) = (term85 A s t u).
Proof. exact (MK_COMB (@lem3266027 A) (@lem3266026 A s t u)). Qed.
Lemma lem3266029 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term79 A s t u) = (term85 A s t u).
Proof. exact (TRANS (@lem3266021 A s t u) (@lem3266028 A s t u)). Qed.
Lemma lem3266030 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term39 A s t u) = (term86 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3266014 A s t u x)). Qed.
Lemma lem3266031 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3266032 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term40 A s t u) = (term87 A s t u).
Proof. exact (MK_COMB (@lem3266031 A) (@lem3266030 A s t u)). Qed.
Lemma lem3266041 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term47 A s u x) = (term88 A s u x).
Proof. exact (@lem17045 (s x) (u x)). Qed.
Lemma lem3266046 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term89 A s u x) = (term44 A s u x).
Proof. exact (@lem16933 (term44 A s u x)). Qed.
Lemma lem3266047 {A : Type'} (P : A -> Prop) : (term77 A P) = (term78 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3266048 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term90 A s u) = (term91 A s u).
Proof. exact (@lem3266047 A (term49 A s u)). Qed.
Lemma lem3266049 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term92 A s u x) = (term47 A s u x).
Proof. exact (eq_refl (term92 A s u x)). Qed.
Lemma lem3266050 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3266051 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term93 A s u x) = (term89 A s u x).
Proof. exact (MK_COMB (@lem3266050) (@lem3266049 A s u x)). Qed.
Lemma lem3266052 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term93 A s u x) = (term44 A s u x).
Proof. exact (TRANS (@lem3266051 A s u x) (@lem3266046 A s u x)). Qed.
Lemma lem3266053 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term94 A s u) = (term95 A s u).
Proof. exact (fun_ext (fun x : A => @lem3266052 A s u x)). Qed.
Lemma lem3266054 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3266055 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term91 A s u) = (term96 A s u).
Proof. exact (MK_COMB (@lem3266054 A) (@lem3266053 A s u)). Qed.
Lemma lem3266056 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term90 A s u) = (term96 A s u).
Proof. exact (TRANS (@lem3266048 A s u) (@lem3266055 A s u)). Qed.
Lemma lem3266057 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term49 A s u) = (term97 A s u).
Proof. exact (fun_ext (fun x : A => @lem3266041 A s u x)). Qed.
Lemma lem3266058 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3266059 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term50 A s u) = (term98 A s u).
Proof. exact (MK_COMB (@lem3266058 A) (@lem3266057 A s u)). Qed.
Lemma lem3266068 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term47 A t u x) = (term88 A t u x).
Proof. exact (@lem17045 (t x) (u x)). Qed.
Lemma lem3266073 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term89 A t u x) = (term44 A t u x).
Proof. exact (@lem16933 (term44 A t u x)). Qed.
Lemma lem3266074 {A : Type'} (P : A -> Prop) : (term77 A P) = (term78 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3266075 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term90 A t u) = (term91 A t u).
Proof. exact (@lem3266074 A (term49 A t u)). Qed.
Lemma lem3266076 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term92 A t u x) = (term47 A t u x).
Proof. exact (eq_refl (term92 A t u x)). Qed.
Lemma lem3266077 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3266078 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term93 A t u x) = (term89 A t u x).
Proof. exact (MK_COMB (@lem3266077) (@lem3266076 A t u x)). Qed.
Lemma lem3266079 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term93 A t u x) = (term44 A t u x).
Proof. exact (TRANS (@lem3266078 A t u x) (@lem3266073 A t u x)). Qed.
Lemma lem3266080 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term94 A t u) = (term95 A t u).
Proof. exact (fun_ext (fun x : A => @lem3266079 A t u x)). Qed.
Lemma lem3266081 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3266082 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term91 A t u) = (term96 A t u).
Proof. exact (MK_COMB (@lem3266081 A) (@lem3266080 A t u)). Qed.
Lemma lem3266083 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term90 A t u) = (term96 A t u).
Proof. exact (TRANS (@lem3266075 A t u) (@lem3266082 A t u)). Qed.
Lemma lem3266084 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term49 A t u) = (term97 A t u).
Proof. exact (fun_ext (fun x : A => @lem3266068 A t u x)). Qed.
Lemma lem3266085 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3266086 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term50 A t u) = (term98 A t u).
Proof. exact (MK_COMB (@lem3266085 A) (@lem3266084 A t u)). Qed.
Lemma lem3266087 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3266088 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term99 A s u) = (term100 A s u).
Proof. exact (MK_COMB (@lem3266087) (@lem3266056 A s u)). Qed.
Lemma lem3266089 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term101 A s t u) = (term102 A s t u).
Proof. exact (MK_COMB (@lem3266088 A s u) (@lem3266083 A t u)). Qed.
Lemma lem3266090 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term103 A s t u) = (term101 A s t u).
Proof. exact (@lem17045 (term50 A s u) (term50 A t u)). Qed.
Lemma lem3266091 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term103 A s t u) = (term102 A s t u).
Proof. exact (TRANS (@lem3266090 A s t u) (@lem3266089 A s t u)). Qed.
Lemma lem3266092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3266093 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term51 A s u) = (term104 A s u).
Proof. exact (MK_COMB (@lem3266092) (@lem3266059 A s u)). Qed.
Lemma lem3266094 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term52 A s t u) = (term105 A s t u).
Proof. exact (MK_COMB (@lem3266093 A s u) (@lem3266086 A t u)). Qed.
Lemma lem3266095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3266096 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term106 A s t u) = (term107 A s t u).
Proof. exact (MK_COMB (@lem3266095) (@lem3266029 A s t u)). Qed.
Lemma lem3266097 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term108 A s t u) = (term109 A s t u).
Proof. exact (MK_COMB (@lem3266096 A s t u) (@lem3266094 A s t u)). Qed.
Lemma lem3266098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3266099 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term110 A s t u) = (term111 A s t u).
Proof. exact (MK_COMB (@lem3266098) (@lem3266032 A s t u)). Qed.
Lemma lem3266100 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term112 A s t u) = (term113 A s t u).
Proof. exact (MK_COMB (@lem3266099 A s t u) (@lem3266091 A s t u)). Qed.
Lemma lem3266101 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3266102 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term114 A s t u) = (term115 A s t u).
Proof. exact (MK_COMB (@lem3266101) (@lem3266100 A s t u)). Qed.
Lemma lem3266103 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term116 A s t u) = (term117 A s t u).
Proof. exact (MK_COMB (@lem3266102 A s t u) (@lem3266097 A s t u)). Qed.
Lemma lem3266104 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term68 A s t u) = (term116 A s t u).
Proof. exact (@lem17646 (term40 A s t u) (term52 A s t u)). Qed.
Lemma lem3266105 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term68 A s t u) = (term117 A s t u).
Proof. exact (TRANS (@lem3266104 A s t u) (@lem3266103 A s t u)). Qed.
Lemma lem3266308 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term118 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3266309 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term118 A P Q) = (term119 A P Q).
Proof. exact (@lem3266308 A P Q). Qed.
Lemma lem3266310 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term120 A s t u) = (term121 A s t u).
Proof. exact (@lem3266309 A (term95 A s u) (term95 A t u)). Qed.
Lemma lem3266311 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term122 A s u x) = (term44 A s u x).
Proof. exact (eq_refl (term122 A s u x)). Qed.
Lemma lem3266312 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term123 A s u) = (term95 A s u).
Proof. exact (fun_ext (fun x : A => @lem3266311 A s u x)). Qed.
Lemma lem3266313 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3266314 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term124 A s u) = (term96 A s u).
Proof. exact (MK_COMB (@lem3266313 A) (@lem3266312 A s u)). Qed.
Lemma lem3266315 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3266316 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term125 A s u) = (term100 A s u).
Proof. exact (MK_COMB (@lem3266315) (@lem3266314 A s u)). Qed.
Lemma lem3266317 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term122 A t u x) = (term44 A t u x).
Proof. exact (eq_refl (term122 A t u x)). Qed.
Lemma lem3266318 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term123 A t u) = (term95 A t u).
Proof. exact (fun_ext (fun x : A => @lem3266317 A t u x)). Qed.
Lemma lem3266319 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3266320 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term124 A t u) = (term96 A t u).
Proof. exact (MK_COMB (@lem3266319 A) (@lem3266318 A t u)). Qed.
Lemma lem3266321 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term120 A s t u) = (term102 A s t u).
Proof. exact (MK_COMB (@lem3266316 A s u) (@lem3266320 A t u)). Qed.
Lemma lem3266322 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3266323 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term126 A s t u) = (term127 A s t u).
Proof. exact (MK_COMB (@lem3266322) (@lem3266321 A s t u)). Qed.
Lemma lem3266324 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term122 A s u x) = (term44 A s u x).
Proof. exact (eq_refl (term122 A s u x)). Qed.
Lemma lem3266325 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3266326 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term128 A s u x) = (term129 A s u x).
Proof. exact (MK_COMB (@lem3266325) (@lem3266324 A s u x)). Qed.
Lemma lem3266327 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term122 A t u x) = (term44 A t u x).
Proof. exact (eq_refl (term122 A t u x)). Qed.
Lemma lem3266328 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term130 A s t u x) = (term131 A s t u x).
Proof. exact (MK_COMB (@lem3266326 A s u x) (@lem3266327 A t u x)). Qed.
Lemma lem3266329 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term132 A s t u) = (term133 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3266328 A s t u x)). Qed.
Lemma lem3266330 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3266331 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term121 A s t u) = (term134 A s t u).
Proof. exact (MK_COMB (@lem3266330 A) (@lem3266329 A s t u)). Qed.
Lemma lem3266332 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : ((term120 A s t u) = (term121 A s t u)) = ((term102 A s t u) = (term134 A s t u)).
Proof. exact (MK_COMB (@lem3266323 A s t u) (@lem3266331 A s t u)). Qed.
Lemma lem3266333 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term102 A s t u) = (term134 A s t u).
Proof. exact (EQ_MP (@lem3266332 A s t u) (@lem3266310 A s t u)). Qed.
Lemma lem3266334 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term111 A s t u) = (term111 A s t u).
Proof. exact (eq_refl (term111 A s t u)). Qed.
Lemma lem3266335 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term113 A s t u) = (term135 A s t u).
Proof. exact (MK_COMB (@lem3266334 A s t u) (@lem3266333 A s t u)). Qed.
Lemma lem3266337 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3266338 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (@lem3266337 A P Q). Qed.
Lemma lem3266339 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term138 A s t u) = (term139 A s t u).
Proof. exact (@lem3266338 A (term87 A s t u) (term133 A s t u)). Qed.
Lemma lem3266340 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term140 A s t u x) = (term131 A s t u x).
Proof. exact (eq_refl (term140 A s t u x)). Qed.
Lemma lem3266341 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term141 A s t u) = (term133 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3266340 A s t u x)). Qed.
Lemma lem3266342 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3266343 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term142 A s t u) = (term134 A s t u).
Proof. exact (MK_COMB (@lem3266342 A) (@lem3266341 A s t u)). Qed.
Lemma lem3266344 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term111 A s t u) = (term111 A s t u).
Proof. exact (eq_refl (term111 A s t u)). Qed.
Lemma lem3266345 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term138 A s t u) = (term135 A s t u).
Proof. exact (MK_COMB (@lem3266344 A s t u) (@lem3266343 A s t u)). Qed.
Lemma lem3266346 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3266347 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term143 A s t u) = (term144 A s t u).
Proof. exact (MK_COMB (@lem3266346) (@lem3266345 A s t u)). Qed.
Lemma lem3266348 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term140 A s t u x) = (term131 A s t u x).
Proof. exact (eq_refl (term140 A s t u x)). Qed.
Lemma lem3266349 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term111 A s t u) = (term111 A s t u).
Proof. exact (eq_refl (term111 A s t u)). Qed.
Lemma lem3266350 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term145 A s t u x) = (term146 A s t u x).
Proof. exact (MK_COMB (@lem3266349 A s t u) (@lem3266348 A s t u x)). Qed.
Lemma lem3266351 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term147 A s t u) = (term148 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3266350 A s t u x)). Qed.
Lemma lem3266352 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3266353 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term139 A s t u) = (term149 A s t u).
Proof. exact (MK_COMB (@lem3266352 A) (@lem3266351 A s t u)). Qed.
Lemma lem3266354 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : ((term138 A s t u) = (term139 A s t u)) = ((term135 A s t u) = (term149 A s t u)).
Proof. exact (MK_COMB (@lem3266347 A s t u) (@lem3266353 A s t u)). Qed.
Lemma lem3266355 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term135 A s t u) = (term149 A s t u).
Proof. exact (EQ_MP (@lem3266354 A s t u) (@lem3266339 A s t u)). Qed.
Lemma lem3266356 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term113 A s t u) = (term149 A s t u).
Proof. exact (TRANS (@lem3266335 A s t u) (@lem3266355 A s t u)). Qed.
Lemma lem3266357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3266358 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term115 A s t u) = (term150 A s t u).
Proof. exact (MK_COMB (@lem3266357) (@lem3266356 A s t u)). Qed.
Lemma lem3266360 {A : Type'} (P : A -> Prop) (Q : Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3266361 {A : Type'} (P : A -> Prop) (Q : Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (@lem3266360 A P Q). Qed.
Lemma lem3266362 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term153 A s t u) = (term154 A s t u).
Proof. exact (@lem3266361 A (term84 A s t u) (term105 A s t u)). Qed.
Lemma lem3266363 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term155 A s t u x) = (term34 A s t u x).
Proof. exact (eq_refl (term155 A s t u x)). Qed.
Lemma lem3266364 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term156 A s t u) = (term84 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3266363 A s t u x)). Qed.
Lemma lem3266365 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3266366 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term157 A s t u) = (term85 A s t u).
Proof. exact (MK_COMB (@lem3266365 A) (@lem3266364 A s t u)). Qed.
Lemma lem3266367 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3266368 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term158 A s t u) = (term107 A s t u).
Proof. exact (MK_COMB (@lem3266367) (@lem3266366 A s t u)). Qed.
Lemma lem3266369 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term105 A s t u) = (term105 A s t u).
Proof. exact (eq_refl (term105 A s t u)). Qed.
Lemma lem3266370 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term153 A s t u) = (term109 A s t u).
Proof. exact (MK_COMB (@lem3266368 A s t u) (@lem3266369 A s t u)). Qed.
Lemma lem3266371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3266372 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term159 A s t u) = (term160 A s t u).
Proof. exact (MK_COMB (@lem3266371) (@lem3266370 A s t u)). Qed.
Lemma lem3266373 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term155 A s t u x) = (term34 A s t u x).
Proof. exact (eq_refl (term155 A s t u x)). Qed.
Lemma lem3266374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3266375 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term161 A s t u x) = (term162 A s t u x).
Proof. exact (MK_COMB (@lem3266374) (@lem3266373 A s t u x)). Qed.
Lemma lem3266376 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term105 A s t u) = (term105 A s t u).
Proof. exact (eq_refl (term105 A s t u)). Qed.
Lemma lem3266377 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term163 A x s t u) = (term164 A x s t u).
Proof. exact (MK_COMB (@lem3266375 A s t u x) (@lem3266376 A s t u)). Qed.
Lemma lem3266378 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term165 A s t u) = (term166 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3266377 A x s t u)). Qed.
Lemma lem3266379 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3266380 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term154 A s t u) = (term167 A s t u).
Proof. exact (MK_COMB (@lem3266379 A) (@lem3266378 A s t u)). Qed.
Lemma lem3266381 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : ((term153 A s t u) = (term154 A s t u)) = ((term109 A s t u) = (term167 A s t u)).
Proof. exact (MK_COMB (@lem3266372 A s t u) (@lem3266380 A s t u)). Qed.
Lemma lem3266382 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term109 A s t u) = (term167 A s t u).
Proof. exact (EQ_MP (@lem3266381 A s t u) (@lem3266362 A s t u)). Qed.
Lemma lem3266383 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term117 A s t u) = (term168 A s t u).
Proof. exact (MK_COMB (@lem3266358 A s t u) (@lem3266382 A s t u)). Qed.
Lemma lem3266385 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term118 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3266386 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term118 A P Q) = (term119 A P Q).
Proof. exact (@lem3266385 A P Q). Qed.
Lemma lem3266387 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term169 A s t u) = (term170 A s t u).
Proof. exact (@lem3266386 A (term148 A s t u) (term166 A s t u)). Qed.
Lemma lem3266388 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term171 A s t u x) = (term146 A s t u x).
Proof. exact (eq_refl (term171 A s t u x)). Qed.
Lemma lem3266389 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term172 A s t u) = (term148 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3266388 A s t u x)). Qed.
Lemma lem3266390 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3266391 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term173 A s t u) = (term149 A s t u).
Proof. exact (MK_COMB (@lem3266390 A) (@lem3266389 A s t u)). Qed.
Lemma lem3266392 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3266393 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term174 A s t u) = (term150 A s t u).
Proof. exact (MK_COMB (@lem3266392) (@lem3266391 A s t u)). Qed.
Lemma lem3266394 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term175 A s t u x) = (term164 A x s t u).
Proof. exact (eq_refl (term175 A s t u x)). Qed.
Lemma lem3266395 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term176 A s t u) = (term166 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3266394 A x s t u)). Qed.
Lemma lem3266396 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3266397 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term177 A s t u) = (term167 A s t u).
Proof. exact (MK_COMB (@lem3266396 A) (@lem3266395 A s t u)). Qed.
Lemma lem3266398 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term169 A s t u) = (term168 A s t u).
Proof. exact (MK_COMB (@lem3266393 A s t u) (@lem3266397 A s t u)). Qed.
Lemma lem3266399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3266400 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term178 A s t u) = (term179 A s t u).
Proof. exact (MK_COMB (@lem3266399) (@lem3266398 A s t u)). Qed.
Lemma lem3266401 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term171 A s t u x) = (term146 A s t u x).
Proof. exact (eq_refl (term171 A s t u x)). Qed.
Lemma lem3266402 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3266403 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term180 A s t u x) = (term181 A s t u x).
Proof. exact (MK_COMB (@lem3266402) (@lem3266401 A s t u x)). Qed.
Lemma lem3266404 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term175 A s t u x) = (term164 A x s t u).
Proof. exact (eq_refl (term175 A s t u x)). Qed.
Lemma lem3266405 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term182 A s t u x) = (term183 A x s t u).
Proof. exact (MK_COMB (@lem3266403 A s t u x) (@lem3266404 A x s t u)). Qed.
Lemma lem3266406 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term184 A s t u) = (term185 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3266405 A x s t u)). Qed.
Lemma lem3266407 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3266408 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term170 A s t u) = (term186 A s t u).
Proof. exact (MK_COMB (@lem3266407 A) (@lem3266406 A s t u)). Qed.
Lemma lem3266409 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : ((term169 A s t u) = (term170 A s t u)) = ((term168 A s t u) = (term186 A s t u)).
Proof. exact (MK_COMB (@lem3266400 A s t u) (@lem3266408 A s t u)). Qed.
Lemma lem3266410 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term168 A s t u) = (term186 A s t u).
Proof. exact (EQ_MP (@lem3266409 A s t u) (@lem3266387 A s t u)). Qed.
Lemma lem3266412 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term117 A s t u) = (term186 A s t u).
Proof. exact (TRANS (@lem3266383 A s t u) (@lem3266410 A s t u)). Qed.
Lemma lem3266413 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term68 A s t u) = (term186 A s t u).
Proof. exact (TRANS (@lem3266105 A s t u) (@lem3266412 A s t u)). Qed.
Lemma lem3266414 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term68 A s t u) : term186 A s t u.
Proof. exact (EQ_MP (@lem3266413 A s t u) (@lem3265995 A s t u h1)). Qed.
Lemma lem3266415 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term183 A x s t u) : term183 A x s t u.
Proof. exact (h1). Qed.
Lemma lem3266428 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term88 A t u x) = (term88 A t u x).
Proof. exact (eq_refl (term88 A t u x)). Qed.
Lemma lem3266429 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term97 A t u) = (term97 A t u).
Proof. exact (fun_ext (fun x : A => @lem3266428 A t u x)). Qed.
Lemma lem3266430 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3266431 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term98 A t u) = (term98 A t u).
Proof. exact (MK_COMB (@lem3266430 A) (@lem3266429 A t u)). Qed.
Lemma lem3266444 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term88 A s u x) = (term88 A s u x).
Proof. exact (eq_refl (term88 A s u x)). Qed.
Lemma lem3266445 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term97 A s u) = (term97 A s u).
Proof. exact (fun_ext (fun x : A => @lem3266444 A s u x)). Qed.
Lemma lem3266446 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3266447 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term98 A s u) = (term98 A s u).
Proof. exact (MK_COMB (@lem3266446 A) (@lem3266445 A s u)). Qed.
Lemma lem3266448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3266449 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term104 A s u) = (term104 A s u).
Proof. exact (MK_COMB (@lem3266448) (@lem3266447 A s u)). Qed.
Lemma lem3266450 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term105 A s t u) = (term105 A s t u).
Proof. exact (MK_COMB (@lem3266449 A s u) (@lem3266431 A t u)). Qed.
Lemma lem3266467 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term162 A s t u x) = (term162 A s t u x).
Proof. exact (eq_refl (term162 A s t u x)). Qed.
Lemma lem3266468 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term164 A x s t u) = (term164 A x s t u).
Proof. exact (MK_COMB (@lem3266467 A s t u x) (@lem3266450 A s t u)). Qed.
Lemma lem3266489 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term131 A s t u x) = (term131 A s t u x).
Proof. exact (eq_refl (term131 A s t u x)). Qed.
Lemma lem3266510 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term75 A s t u x) = (term75 A s t u x).
Proof. exact (eq_refl (term75 A s t u x)). Qed.
Lemma lem3266511 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term86 A s t u) = (term86 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3266510 A s t u x)). Qed.
Lemma lem3266512 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3266513 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term87 A s t u) = (term87 A s t u).
Proof. exact (MK_COMB (@lem3266512 A) (@lem3266511 A s t u)). Qed.
Lemma lem3266514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3266515 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term111 A s t u) = (term111 A s t u).
Proof. exact (MK_COMB (@lem3266514) (@lem3266513 A s t u)). Qed.
Lemma lem3266516 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term146 A s t u x) = (term146 A s t u x).
Proof. exact (MK_COMB (@lem3266515 A s t u) (@lem3266489 A s t u x)). Qed.
Lemma lem3266517 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3266518 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term181 A s t u x) = (term181 A s t u x).
Proof. exact (MK_COMB (@lem3266517) (@lem3266516 A s t u x)). Qed.
Lemma lem3266519 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term183 A x s t u) = (term183 A x s t u).
Proof. exact (MK_COMB (@lem3266518 A s t u x) (@lem3266468 A x s t u)). Qed.
Lemma lem3266520 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term183 A x s t u) : term183 A x s t u.
Proof. exact (EQ_MP (@lem3266519 A x s t u) (@lem3266415 A x s t u h1)). Qed.
Lemma lem3266521 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term146 A s t u x.
Proof. exact (h1). Qed.
Lemma lem3266522 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term164 A x s t u.
Proof. exact (h1). Qed.
Lemma lem3266523 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term131 A s t u x.
Proof. exact (proj2 (@lem3266521 A s t u x h1)). Qed.
Lemma lem3266524 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term87 A s t u.
Proof. exact (proj1 (@lem3266521 A s t u x h1)). Qed.
Lemma lem3266525 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A s u x) : term44 A s u x.
Proof. exact (h1). Qed.
Lemma lem3266526 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A t u x) : term44 A t u x.
Proof. exact (h1). Qed.
Lemma lem3266531 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term105 A s t u.
Proof. exact (proj2 (@lem3266522 A x s t u h1)). Qed.
Lemma lem3266532 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term34 A s t u x.
Proof. exact (proj1 (@lem3266522 A x s t u h1)). Qed.
Lemma lem3266533 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term98 A t u.
Proof. exact (proj2 (@lem3266531 A x s t u h1)). Qed.
Lemma lem3266534 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term98 A s u.
Proof. exact (proj1 (@lem3266531 A x s t u h1)). Qed.
Lemma lem3266536 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term31 A s t x.
Proof. exact (proj1 (@lem3266532 A x s t u h1)). Qed.
Lemma lem3266556 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term75 A s t u x) = (term187 A s t u x).
Proof. exact (@lem19699 (term71 A s x) (term71 A t x) (term71 A u x)). Qed.
Lemma lem3266557 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term86 A s t u) = (term188 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3266556 A s t u x)). Qed.
Lemma lem3266558 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3266560 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term87 A s t u) = (term189 A s t u).
Proof. exact (MK_COMB (@lem3266558 A) (@lem3266557 A s t u)). Qed.
Lemma lem3266561 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term189 A s t u.
Proof. exact (EQ_MP (@lem3266560 A s t u) (@lem3266524 A s t u x h1)). Qed.
Lemma lem3266587 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term75 A s t u x) = (term187 A s t u x).
Proof. exact (@lem19699 (term71 A s x) (term71 A t x) (term71 A u x)). Qed.
Lemma lem3266588 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term86 A s t u) = (term188 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3266587 A s t u x)). Qed.
Lemma lem3266589 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3266591 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term87 A s t u) = (term189 A s t u).
Proof. exact (MK_COMB (@lem3266589 A) (@lem3266588 A s t u)). Qed.
Lemma lem3266592 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term189 A s t u.
Proof. exact (EQ_MP (@lem3266591 A s t u) (@lem3266524 A s t u x h1)). Qed.
Lemma lem3266608 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term88 A s u x) = (term88 A s u x).
Proof. exact (eq_refl (term88 A s u x)). Qed.
Lemma lem3266609 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term97 A s u) = (term97 A s u).
Proof. exact (fun_ext (fun x : A => @lem3266608 A s u x)). Qed.
Lemma lem3266610 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3266612 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term98 A s u) = (term98 A s u).
Proof. exact (MK_COMB (@lem3266610 A) (@lem3266609 A s u)). Qed.
Lemma lem3266613 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term98 A s u.
Proof. exact (EQ_MP (@lem3266612 A s u) (@lem3266534 A x s t u h1)). Qed.
Lemma lem3266634 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3266655 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term88 A t u x) = (term88 A t u x).
Proof. exact (eq_refl (term88 A t u x)). Qed.
Lemma lem3266656 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term97 A t u) = (term97 A t u).
Proof. exact (fun_ext (fun x : A => @lem3266655 A t u x)). Qed.
Lemma lem3266657 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3266659 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term98 A t u) = (term98 A t u).
Proof. exact (MK_COMB (@lem3266657 A) (@lem3266656 A t u)). Qed.
Lemma lem3266660 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term98 A t u.
Proof. exact (EQ_MP (@lem3266659 A t u) (@lem3266533 A x s t u h1)). Qed.
Lemma lem3266668 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3266669 {A : Type'} (_33412 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term190 A s t u _33412.
Proof. exact (@lem3266561 A s t u x h1 _33412). Qed.
Lemma lem3266670 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (_33412 : A) : (term190 A s t u _33412) = (term187 A s t u _33412).
Proof. exact (eq_refl (term190 A s t u _33412)). Qed.
Lemma lem3266671 {A : Type'} (_33412 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term187 A s t u _33412.
Proof. exact (EQ_MP (@lem3266670 A s t u _33412) (@lem3266669 A _33412 s t u x h1)). Qed.
Lemma lem3266672 {A : Type'} (_33413 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term190 A s t u _33413.
Proof. exact (@lem3266592 A s t u x h1 _33413). Qed.
Lemma lem3266673 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (_33413 : A) : (term190 A s t u _33413) = (term187 A s t u _33413).
Proof. exact (eq_refl (term190 A s t u _33413)). Qed.
Lemma lem3266674 {A : Type'} (_33413 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term187 A s t u _33413.
Proof. exact (EQ_MP (@lem3266673 A s t u _33413) (@lem3266672 A _33413 s t u x h1)). Qed.
Lemma lem3266675 {A : Type'} (_33414 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term191 A s u _33414.
Proof. exact (@lem3266613 A x s t u h1 _33414). Qed.
Lemma lem3266676 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_33414 : A) : (term191 A s u _33414) = (term88 A s u _33414).
Proof. exact (eq_refl (term191 A s u _33414)). Qed.
Lemma lem3266684 {A : Type'} (_33417 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term191 A t u _33417.
Proof. exact (@lem3266660 A x s t u h1 _33417). Qed.
Lemma lem3266685 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33417 : A) : (term191 A t u _33417) = (term88 A t u _33417).
Proof. exact (eq_refl (term191 A t u _33417)). Qed.
Lemma lem3266700 {A : Type'} (_33412 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term88 A s u _33412.
Proof. exact (proj1 (@lem3266671 A _33412 s t u x h1)). Qed.
Lemma lem3266722 {A : Type'} (_33413 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term88 A t u _33413.
Proof. exact (proj2 (@lem3266674 A _33413 s t u x h1)). Qed.
Lemma lem3266728 {A : Type'} (_33414 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term88 A s u _33414.
Proof. exact (EQ_MP (@lem3266676 A s u _33414) (@lem3266675 A _33414 x s t u h1)). Qed.
Lemma lem3266738 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3266750 {A : Type'} (_33417 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term88 A t u _33417.
Proof. exact (EQ_MP (@lem3266685 A t u _33417) (@lem3266684 A _33417 x s t u h1)). Qed.
Lemma lem3266754 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3266756 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A s u x) : s x.
Proof. exact (proj1 (@lem3266525 A s u x h1)). Qed.
Lemma lem3266757 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A s u x) : term192 A s x.
Proof. exact (fun h0 : term71 A s x => @lem3266756 A s u x h1). Qed.
Lemma lem3266759 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3266760 {A : Type'} (s : A -> Prop) (x : A) : (term192 A s x) = (s x).
Proof. exact (@lem3266759 (s x)). Qed.
Lemma lem3266761 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A s u x) : s x.
Proof. exact (EQ_MP (@lem3266760 A s x) (@lem3266757 A s u x h1)). Qed.
Lemma lem3266763 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A s u x) : u x.
Proof. exact (proj2 (@lem3266525 A s u x h1)). Qed.
Lemma lem3266764 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A s u x) : term192 A u x.
Proof. exact (fun h0 : term71 A u x => @lem3266763 A s u x h1). Qed.
Lemma lem3266766 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3266767 {A : Type'} (u : A -> Prop) (x : A) : (term192 A u x) = (u x).
Proof. exact (@lem3266766 (u x)). Qed.
Lemma lem3266768 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A s u x) : u x.
Proof. exact (EQ_MP (@lem3266767 A u x) (@lem3266764 A s u x h1)). Qed.
Lemma lem3266770 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3266771 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_33412 : A) : (term88 A s u _33412) = (term47 A s u _33412).
Proof. exact (@lem3266770 (s _33412) (u _33412)). Qed.
Lemma lem3266773 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3266774 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_33412 : A) : (term47 A s u _33412) = (term196 A s u _33412).
Proof. exact (@lem3266773 (term44 A s u _33412)). Qed.
Lemma lem3266775 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_33412 : A) : (term88 A s u _33412) = (term196 A s u _33412).
Proof. exact (TRANS (@lem3266771 A s u _33412) (@lem3266774 A s u _33412)). Qed.
Lemma lem3266777 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A s u x) : term44 A s u x.
Proof. exact (conj (@lem3266761 A s u x h1) (@lem3266768 A s u x h1)). Qed.
Lemma lem3266779 {A : Type'} (_33412 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term196 A s u _33412.
Proof. exact (EQ_MP (@lem3266775 A s u _33412) (@lem3266700 A _33412 s t u x h1)). Qed.
Lemma lem3266780 {A : Type'} (_33412 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term196 A s u _33412.
Proof. exact (@lem3266779 A _33412 s t u x h1). Qed.
Lemma lem3266781 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term196 A s u x.
Proof. exact (@lem3266780 A x s t u x h1). Qed.
Lemma lem3266784 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) (h2 : term44 A s u x) : False.
Proof. exact (@lem3266781 A s t u x h1 (@lem3266777 A s u x h2)). Qed.
Lemma lem3266785 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) (h2 : term44 A s u x) : term197.
Proof. exact (fun h0 : ~ False => @lem3266784 A t s u x h1 h2). Qed.
Lemma lem3266787 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3266788 : term197 = False.
Proof. exact (@lem3266787 False). Qed.
Lemma lem3266789 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) (h2 : term44 A s u x) : False.
Proof. exact (EQ_MP (@lem3266788) (@lem3266785 A t s u x h1 h2)). Qed.
Lemma lem3266791 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A t u x) : t x.
Proof. exact (proj1 (@lem3266526 A t u x h1)). Qed.
Lemma lem3266792 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A t u x) : term192 A t x.
Proof. exact (fun h0 : term71 A t x => @lem3266791 A t u x h1). Qed.
Lemma lem3266794 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3266795 {A : Type'} (t : A -> Prop) (x : A) : (term192 A t x) = (t x).
Proof. exact (@lem3266794 (t x)). Qed.
Lemma lem3266796 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A t u x) : t x.
Proof. exact (EQ_MP (@lem3266795 A t x) (@lem3266792 A t u x h1)). Qed.
Lemma lem3266798 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A t u x) : u x.
Proof. exact (proj2 (@lem3266526 A t u x h1)). Qed.
Lemma lem3266799 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A t u x) : term192 A u x.
Proof. exact (fun h0 : term71 A u x => @lem3266798 A t u x h1). Qed.
Lemma lem3266801 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3266802 {A : Type'} (u : A -> Prop) (x : A) : (term192 A u x) = (u x).
Proof. exact (@lem3266801 (u x)). Qed.
Lemma lem3266803 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A t u x) : u x.
Proof. exact (EQ_MP (@lem3266802 A u x) (@lem3266799 A t u x h1)). Qed.
Lemma lem3266805 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3266806 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33413 : A) : (term88 A t u _33413) = (term47 A t u _33413).
Proof. exact (@lem3266805 (t _33413) (u _33413)). Qed.
Lemma lem3266808 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3266809 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33413 : A) : (term47 A t u _33413) = (term196 A t u _33413).
Proof. exact (@lem3266808 (term44 A t u _33413)). Qed.
Lemma lem3266810 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33413 : A) : (term88 A t u _33413) = (term196 A t u _33413).
Proof. exact (TRANS (@lem3266806 A t u _33413) (@lem3266809 A t u _33413)). Qed.
Lemma lem3266812 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term44 A t u x) : term44 A t u x.
Proof. exact (conj (@lem3266796 A t u x h1) (@lem3266803 A t u x h1)). Qed.
Lemma lem3266814 {A : Type'} (_33413 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term196 A t u _33413.
Proof. exact (EQ_MP (@lem3266810 A t u _33413) (@lem3266722 A _33413 s t u x h1)). Qed.
Lemma lem3266815 {A : Type'} (_33413 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term196 A t u _33413.
Proof. exact (@lem3266814 A _33413 s t u x h1). Qed.
Lemma lem3266816 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : term196 A t u x.
Proof. exact (@lem3266815 A x s t u x h1). Qed.
Lemma lem3266819 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) (h2 : term44 A t u x) : False.
Proof. exact (@lem3266816 A s t u x h1 (@lem3266812 A t u x h2)). Qed.
Lemma lem3266820 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) (h2 : term44 A t u x) : term197.
Proof. exact (fun h0 : ~ False => @lem3266819 A s t u x h1 h2). Qed.
Lemma lem3266822 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3266823 : term197 = False.
Proof. exact (@lem3266822 False). Qed.
Lemma lem3266824 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) (h2 : term44 A t u x) : False.
Proof. exact (EQ_MP (@lem3266823) (@lem3266820 A s t u x h1 h2)). Qed.
Lemma lem3266826 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3266827 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term192 A s x.
Proof. exact (fun h0 : term71 A s x => @lem3266826 A s x h1). Qed.
Lemma lem3266829 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3266830 {A : Type'} (s : A -> Prop) (x : A) : (term192 A s x) = (s x).
Proof. exact (@lem3266829 (s x)). Qed.
Lemma lem3266831 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3266830 A s x) (@lem3266827 A s x h1)). Qed.
Lemma lem3266833 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : u x.
Proof. exact (proj2 (@lem3266532 A x s t u h1)). Qed.
Lemma lem3266834 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term192 A u x.
Proof. exact (fun h0 : term71 A u x => @lem3266833 A x s t u h1). Qed.
Lemma lem3266836 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3266837 {A : Type'} (u : A -> Prop) (x : A) : (term192 A u x) = (u x).
Proof. exact (@lem3266836 (u x)). Qed.
Lemma lem3266838 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : u x.
Proof. exact (EQ_MP (@lem3266837 A u x) (@lem3266834 A x s t u h1)). Qed.
Lemma lem3266840 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3266841 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_33414 : A) : (term88 A s u _33414) = (term47 A s u _33414).
Proof. exact (@lem3266840 (s _33414) (u _33414)). Qed.
Lemma lem3266843 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3266844 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_33414 : A) : (term47 A s u _33414) = (term196 A s u _33414).
Proof. exact (@lem3266843 (term44 A s u _33414)). Qed.
Lemma lem3266845 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_33414 : A) : (term88 A s u _33414) = (term196 A s u _33414).
Proof. exact (TRANS (@lem3266841 A s u _33414) (@lem3266844 A s u _33414)). Qed.
Lemma lem3266847 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term164 A x s t u) : term44 A s u x.
Proof. exact (conj (@lem3266831 A s x h1) (@lem3266838 A x s t u h2)). Qed.
Lemma lem3266849 {A : Type'} (_33414 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term196 A s u _33414.
Proof. exact (EQ_MP (@lem3266845 A s u _33414) (@lem3266728 A _33414 x s t u h1)). Qed.
Lemma lem3266850 {A : Type'} (_33414 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term196 A s u _33414.
Proof. exact (@lem3266849 A _33414 x s t u h1). Qed.
Lemma lem3266851 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term196 A s u x.
Proof. exact (@lem3266850 A x x s t u h1). Qed.
Lemma lem3266854 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term164 A x s t u) : False.
Proof. exact (@lem3266851 A x s t u h2 (@lem3266847 A x s t u h1 h2)). Qed.
Lemma lem3266855 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term164 A x s t u) : term197.
Proof. exact (fun h0 : ~ False => @lem3266854 A x s t u h1 h2). Qed.
Lemma lem3266857 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3266858 : term197 = False.
Proof. exact (@lem3266857 False). Qed.
Lemma lem3266859 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term164 A x s t u) : False.
Proof. exact (EQ_MP (@lem3266858) (@lem3266855 A x s t u h1 h2)). Qed.
Lemma lem3266861 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3266862 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term192 A t x.
Proof. exact (fun h0 : term71 A t x => @lem3266861 A t x h1). Qed.
Lemma lem3266864 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3266865 {A : Type'} (t : A -> Prop) (x : A) : (term192 A t x) = (t x).
Proof. exact (@lem3266864 (t x)). Qed.
Lemma lem3266866 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3266865 A t x) (@lem3266862 A t x h1)). Qed.
Lemma lem3266868 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : u x.
Proof. exact (proj2 (@lem3266532 A x s t u h1)). Qed.
Lemma lem3266869 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term192 A u x.
Proof. exact (fun h0 : term71 A u x => @lem3266868 A x s t u h1). Qed.
Lemma lem3266871 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3266872 {A : Type'} (u : A -> Prop) (x : A) : (term192 A u x) = (u x).
Proof. exact (@lem3266871 (u x)). Qed.
Lemma lem3266873 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : u x.
Proof. exact (EQ_MP (@lem3266872 A u x) (@lem3266869 A x s t u h1)). Qed.
Lemma lem3266875 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3266876 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33417 : A) : (term88 A t u _33417) = (term47 A t u _33417).
Proof. exact (@lem3266875 (t _33417) (u _33417)). Qed.
Lemma lem3266878 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3266879 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33417 : A) : (term47 A t u _33417) = (term196 A t u _33417).
Proof. exact (@lem3266878 (term44 A t u _33417)). Qed.
Lemma lem3266880 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33417 : A) : (term88 A t u _33417) = (term196 A t u _33417).
Proof. exact (TRANS (@lem3266876 A t u _33417) (@lem3266879 A t u _33417)). Qed.
Lemma lem3266882 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : t x) (h2 : term164 A x s t u) : term44 A t u x.
Proof. exact (conj (@lem3266866 A t x h1) (@lem3266873 A x s t u h2)). Qed.
Lemma lem3266884 {A : Type'} (_33417 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term196 A t u _33417.
Proof. exact (EQ_MP (@lem3266880 A t u _33417) (@lem3266750 A _33417 x s t u h1)). Qed.
Lemma lem3266885 {A : Type'} (_33417 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term196 A t u _33417.
Proof. exact (@lem3266884 A _33417 x s t u h1). Qed.
Lemma lem3266886 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : term196 A t u x.
Proof. exact (@lem3266885 A x x s t u h1). Qed.
Lemma lem3266889 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : t x) (h2 : term164 A x s t u) : False.
Proof. exact (@lem3266886 A x s t u h2 (@lem3266882 A x s t u h1 h2)). Qed.
Lemma lem3266890 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : t x) (h2 : term164 A x s t u) : term197.
Proof. exact (fun h0 : ~ False => @lem3266889 A x s t u h1 h2). Qed.
Lemma lem3266892 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3266893 : term197 = False.
Proof. exact (@lem3266892 False). Qed.
Lemma lem3266894 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : t x) (h2 : term164 A x s t u) : False.
Proof. exact (EQ_MP (@lem3266893) (@lem3266890 A x s t u h1 h2)). Qed.
Lemma lem3266895 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : t x) (h2 : term164 A x s t u) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3266894 A x s t u h1 h2) (fun h3 : False => @lem3266754 A t x h1)). Qed.
Lemma lem3266896 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : t x) (h2 : term164 A x s t u) : False.
Proof. exact (EQ_MP (@lem3266895 A x s t u h1 h2) (@lem3266754 A t x h1)). Qed.
Lemma lem3266897 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term164 A x s t u) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3266859 A x s t u h1 h2) (fun h3 : False => @lem3266738 A s x h1)). Qed.
Lemma lem3266898 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term164 A x s t u) : False.
Proof. exact (EQ_MP (@lem3266897 A x s t u h1 h2) (@lem3266738 A s x h1)). Qed.
Lemma lem3266899 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : t x) (h2 : term164 A x s t u) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3266896 A x s t u h1 h2) (fun h3 : False => @lem3266668 A t x h1)). Qed.
Lemma lem3266900 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : t x) (h2 : term164 A x s t u) : False.
Proof. exact (EQ_MP (@lem3266899 A x s t u h1 h2) (@lem3266668 A t x h1)). Qed.
Lemma lem3266901 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term164 A x s t u) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3266898 A x s t u h1 h2) (fun h3 : False => @lem3266634 A s x h1)). Qed.
Lemma lem3266902 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term164 A x s t u) : False.
Proof. exact (EQ_MP (@lem3266901 A x s t u h1 h2) (@lem3266634 A s x h1)). Qed.
Lemma lem3266903 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : t x) (h2 : term164 A x s t u) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3266900 A x s t u h1 h2) (fun h3 : False => @lem3266668 A t x h1)). Qed.
Lemma lem3266904 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : t x) (h2 : term164 A x s t u) : False.
Proof. exact (EQ_MP (@lem3266903 A x s t u h1 h2) (@lem3266668 A t x h1)). Qed.
Lemma lem3266905 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term164 A x s t u) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3266902 A x s t u h1 h2) (fun h3 : False => @lem3266634 A s x h1)). Qed.
Lemma lem3266906 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : s x) (h2 : term164 A x s t u) : False.
Proof. exact (EQ_MP (@lem3266905 A x s t u h1 h2) (@lem3266634 A s x h1)). Qed.
Lemma lem3266907 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A x s t u) : False.
Proof. exact (or_elim (@lem3266536 A x s t u h1) (fun h0 : s x => @lem3266906 A x s t u h0 h1) (fun h0 : t x => @lem3266904 A x s t u h0 h1)). Qed.
Lemma lem3266908 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term146 A s t u x) : False.
Proof. exact (or_elim (@lem3266523 A s t u x h1) (fun h0 : term44 A s u x => @lem3266789 A t s u x h1 h0) (fun h0 : term44 A t u x => @lem3266824 A s t u x h1 h0)). Qed.
Lemma lem3266909 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term183 A x s t u) : False.
Proof. exact (or_elim (@lem3266520 A x s t u h1) (fun h0 : term146 A s t u x => @lem3266908 A s t u x h0) (fun h0 : term164 A x s t u => @lem3266907 A x s t u h0)). Qed.
Lemma lem3266910 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term183 A x s t u) : (term183 A x s t u) = False.
Proof. exact (prop_ext (fun h2 : term183 A x s t u => @lem3266909 A x s t u h1) (fun h2 : False => @lem3266520 A x s t u h1)). Qed.
Lemma lem3266911 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term183 A x s t u) : False.
Proof. exact (EQ_MP (@lem3266910 A x s t u h1) (@lem3266520 A x s t u h1)). Qed.
Lemma lem3266912 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term68 A s t u) : False.
Proof. exact (ex_elim (@lem3266414 A s t u h1) (fun x : A => fun h0 : term185 A s t u x => @lem3266911 A x s t u h0)). Qed.
Lemma lem3266913 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term68 A s t u) : (term68 A s t u) = False.
Proof. exact (prop_ext (fun h2 : term68 A s t u => @lem3266912 A s t u h1) (fun h2 : False => @lem3265995 A s t u h1)). Qed.
Lemma lem3266914 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term68 A s t u) : False.
Proof. exact (EQ_MP (@lem3266913 A s t u h1) (@lem3265995 A s t u h1)). Qed.
Lemma lem3266915 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term67 A s t u.
Proof. exact (fun h0 : term68 A s t u => @lem3266914 A s t u h0). Qed.
Lemma lem3266916 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term40 A s t u) = (term52 A s t u).
Proof. exact (EQ_MP (@lem3265994 A s t u) (@lem3266915 A s t u)). Qed.
Lemma lem3266921 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term54 A s t.
Proof. exact (fun u : A -> Prop => @lem3266916 A s t u). Qed.
Lemma lem3266926 {A : Type'} (s : A -> Prop) : term56 A s.
Proof. exact (fun t : A -> Prop => @lem3266921 A s t). Qed.
Lemma lem3266931 {A : Type'} : term58 A.
Proof. exact (fun s : A -> Prop => @lem3266926 A s). Qed.
Lemma lem3266932 {A : Type'} : term60 A.
Proof. exact (EQ_MP (@lem3265990 A) (@lem3266931 A)). Qed.
Lemma lem3266934 {A : Type'} : term60 A.
Proof. exact (@lem3265846 A (@lem3266932 A)). Qed.
Lemma lem3266935 {A : Type'} (h1 : term61 A) : False.
Proof. exact (@lem3266934 A (@lem3265830 A h1)). Qed.
Lemma lem3266936 {A : Type'} (h1 : term61 A) : (term61 A) = False.
Proof. exact (prop_ext (fun h2 : term61 A => @lem3266935 A h1) (fun h2 : False => @lem3265830 A h1)). Qed.
Lemma lem3266937 {A : Type'} (h1 : term61 A) : False.
Proof. exact (EQ_MP (@lem3266936 A h1) (@lem3265830 A h1)). Qed.
Lemma lem3266938 {A : Type'} : term60 A.
Proof. exact (fun h0 : term61 A => @lem3266937 A h0). Qed.
Lemma lem3266939 {A : Type'} : term58 A.
Proof. exact (EQ_MP (@lem3265829 A) (@lem3266938 A)). Qed.
Lemma lem3266940 {A : Type'} : term22 A.
Proof. exact (EQ_MP (@lem3265825 A) (@lem3266939 A)). Qed.
Lemma lem3266941 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem3265625 A) (@lem3266940 A)). Qed.
