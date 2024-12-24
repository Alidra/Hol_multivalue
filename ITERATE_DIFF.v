Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_DIFF_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_SUBSET_spec.
Require Import FINITE_UNION_spec.
Require Import ITERATE_UNION_spec.
Require Import SUBSET_DIFF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211738_spec.
Require Import thm3211739_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem5764575 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5764576 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (@SUBSET _120712 s t) = (term0 _120712 s t).
Proof. exact (@lem5764575 _120712 s t). Qed.
Lemma lem5764577 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) : (@SUBSET _120712 t s) = (term0 _120712 t s).
Proof. exact (@lem5764576 _120712 t s). Qed.
Lemma lem5764584 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5764585 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) : (term1 _120712 t s) = (term2 _120712 t s).
Proof. exact (MK_COMB (@lem5764584) (@lem5764577 _120712 t s)). Qed.
Lemma lem5764591 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5764592 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (s = t) = (term3 _120712 s t).
Proof. exact (@lem5764591 _120712 s t). Qed.
Lemma lem5764593 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (s = (term4 _120712 s t)) = (term5 _120712 s t).
Proof. exact (@lem5764592 _120712 s (term4 _120712 s t)). Qed.
Lemma lem5764602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5764603 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term6 _120712 s t) = (term7 _120712 s t).
Proof. exact (MK_COMB (@lem5764602) (@lem5764593 _120712 s t)). Qed.
Lemma lem5764605 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem5764606 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (@DISJOINT _120712 s t) = ((@INTER _120712 s t) = (@EMPTY _120712)).
Proof. exact (@lem5764605 _120712 s t). Qed.
Lemma lem5764607 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term8 _120712 s t) = ((term9 _120712 s t) = (@EMPTY _120712)).
Proof. exact (@lem5764606 _120712 (@DIFF _120712 s t) t). Qed.
Lemma lem5764611 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5764612 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (s = t) = (term3 _120712 s t).
Proof. exact (@lem5764611 _120712 s t). Qed.
Lemma lem5764613 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : ((term9 _120712 s t) = (@EMPTY _120712)) = (term10 _120712 s t).
Proof. exact (@lem5764612 _120712 (term9 _120712 s t) (@EMPTY _120712)). Qed.
Lemma lem5764618 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term8 _120712 s t) = (term10 _120712 s t).
Proof. exact (TRANS (@lem5764607 _120712 s t) (@lem5764613 _120712 s t)). Qed.
Lemma lem5764623 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term11 _120712 s t) = (term12 _120712 s t).
Proof. exact (MK_COMB (@lem5764603 _120712 s t) (@lem5764618 _120712 s t)). Qed.
Lemma lem5764626 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term13 _120712 s t) = (term14 _120712 s t).
Proof. exact (MK_COMB (@lem5764585 _120712 t s) (@lem5764623 _120712 s t)). Qed.
Lemma lem5764629 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term14 _120712 s t) = (term13 _120712 s t).
Proof. exact (SYM (@lem5764626 _120712 s t)). Qed.
Lemma lem5764639 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5764640 {_120712 : Type'} (P : _120712 -> Prop) (x : _120712) : (@IN _120712 x P) = (P x).
Proof. exact (@lem5764639 _120712 P x). Qed.
Lemma lem5764641 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) : (@IN _120712 x t) = (t x).
Proof. exact (@lem5764640 _120712 t x). Qed.
Lemma lem5764642 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5764643 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) : (term15 _120712 x t) = (term16 _120712 t x).
Proof. exact (MK_COMB (@lem5764642) (@lem5764641 _120712 t x)). Qed.
Lemma lem5764645 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5764646 {_120712 : Type'} (P : _120712 -> Prop) (x : _120712) : (@IN _120712 x P) = (P x).
Proof. exact (@lem5764645 _120712 P x). Qed.
Lemma lem5764647 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) : (@IN _120712 x s) = (s x).
Proof. exact (@lem5764646 _120712 s x). Qed.
Lemma lem5764648 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) (x : _120712) : (term17 _120712 t x s) = (term18 _120712 t s x).
Proof. exact (MK_COMB (@lem5764643 _120712 t x) (@lem5764647 _120712 s x)). Qed.
Lemma lem5764651 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) : (term19 _120712 t s) = (term20 _120712 t s).
Proof. exact (fun_ext (fun x : _120712 => @lem5764648 _120712 t s x)). Qed.
Lemma lem5764652 {_120712 : Type'} : (@all _120712) = (@all _120712).
Proof. exact (eq_refl (@all _120712)). Qed.
Lemma lem5764653 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) : (term0 _120712 t s) = (term21 _120712 t s).
Proof. exact (MK_COMB (@lem5764652 _120712) (@lem5764651 _120712 t s)). Qed.
Lemma lem5764658 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5764659 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) : (term2 _120712 t s) = (term22 _120712 t s).
Proof. exact (MK_COMB (@lem5764658) (@lem5764653 _120712 t s)). Qed.
Lemma lem5764669 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5764670 {_120712 : Type'} (P : _120712 -> Prop) (x : _120712) : (@IN _120712 x P) = (P x).
Proof. exact (@lem5764669 _120712 P x). Qed.
Lemma lem5764671 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) : (@IN _120712 x s) = (s x).
Proof. exact (@lem5764670 _120712 s x). Qed.
Lemma lem5764672 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5764673 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) : (term23 _120712 x s) = (term24 _120712 s x).
Proof. exact (MK_COMB (@lem5764672) (@lem5764671 _120712 s x)). Qed.
Lemma lem5764675 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem5764676 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) (t : _120712 -> Prop) : (term25 _120712 x s t) = (term26 _120712 s x t).
Proof. exact (@lem5764675 _120712 s x t). Qed.
Lemma lem5764677 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) (t : _120712 -> Prop) : (term27 _120712 x s t) = (term28 _120712 s x t).
Proof. exact (@lem5764676 _120712 (@DIFF _120712 s t) x t). Qed.
Lemma lem5764681 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term29 A x s t) = (term30 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem5764682 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) (t : _120712 -> Prop) : (term29 _120712 x s t) = (term30 _120712 s x t).
Proof. exact (@lem5764681 _120712 s x t). Qed.
Lemma lem5764686 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5764687 {_120712 : Type'} (P : _120712 -> Prop) (x : _120712) : (@IN _120712 x P) = (P x).
Proof. exact (@lem5764686 _120712 P x). Qed.
Lemma lem5764688 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) : (@IN _120712 x s) = (s x).
Proof. exact (@lem5764687 _120712 s x). Qed.
Lemma lem5764689 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5764690 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) : (term31 _120712 x s) = (term32 _120712 s x).
Proof. exact (MK_COMB (@lem5764689) (@lem5764688 _120712 s x)). Qed.
Lemma lem5764692 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5764693 {_120712 : Type'} (P : _120712 -> Prop) (x : _120712) : (@IN _120712 x P) = (P x).
Proof. exact (@lem5764692 _120712 P x). Qed.
Lemma lem5764694 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) : (@IN _120712 x t) = (t x).
Proof. exact (@lem5764693 _120712 t x). Qed.
Lemma lem5764695 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5764696 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) : (term33 _120712 x t) = (term34 _120712 t x).
Proof. exact (MK_COMB (@lem5764695) (@lem5764694 _120712 t x)). Qed.
Lemma lem5764697 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term30 _120712 s x t) = (term35 _120712 s t x).
Proof. exact (MK_COMB (@lem5764690 _120712 s x) (@lem5764696 _120712 t x)). Qed.
Lemma lem5764700 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term29 _120712 x s t) = (term35 _120712 s t x).
Proof. exact (TRANS (@lem5764682 _120712 s x t) (@lem5764697 _120712 s t x)). Qed.
Lemma lem5764701 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5764702 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term36 _120712 x s t) = (term37 _120712 s t x).
Proof. exact (MK_COMB (@lem5764701) (@lem5764700 _120712 s t x)). Qed.
Lemma lem5764704 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5764705 {_120712 : Type'} (P : _120712 -> Prop) (x : _120712) : (@IN _120712 x P) = (P x).
Proof. exact (@lem5764704 _120712 P x). Qed.
Lemma lem5764706 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) : (@IN _120712 x t) = (t x).
Proof. exact (@lem5764705 _120712 t x). Qed.
Lemma lem5764707 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term28 _120712 s x t) = (term38 _120712 s t x).
Proof. exact (MK_COMB (@lem5764702 _120712 s t x) (@lem5764706 _120712 t x)). Qed.
Lemma lem5764710 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term27 _120712 x s t) = (term38 _120712 s t x).
Proof. exact (TRANS (@lem5764677 _120712 s x t) (@lem5764707 _120712 s t x)). Qed.
Lemma lem5764711 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : ((@IN _120712 x s) = (term27 _120712 x s t)) = ((s x) = (term38 _120712 s t x)).
Proof. exact (MK_COMB (@lem5764673 _120712 s x) (@lem5764710 _120712 s t x)). Qed.
Lemma lem5764714 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term39 _120712 s t) = (term40 _120712 s t).
Proof. exact (fun_ext (fun x : _120712 => @lem5764711 _120712 s t x)). Qed.
Lemma lem5764715 {_120712 : Type'} : (@all _120712) = (@all _120712).
Proof. exact (eq_refl (@all _120712)). Qed.
Lemma lem5764716 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term5 _120712 s t) = (term41 _120712 s t).
Proof. exact (MK_COMB (@lem5764715 _120712) (@lem5764714 _120712 s t)). Qed.
Lemma lem5764721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5764722 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term7 _120712 s t) = (term42 _120712 s t).
Proof. exact (MK_COMB (@lem5764721) (@lem5764716 _120712 s t)). Qed.
Lemma lem5764730 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term43 A x s t) = (term44 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem5764731 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) (t : _120712 -> Prop) : (term43 _120712 x s t) = (term44 _120712 s x t).
Proof. exact (@lem5764730 _120712 s x t). Qed.
Lemma lem5764732 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) (t : _120712 -> Prop) : (term45 _120712 x s t) = (term46 _120712 s x t).
Proof. exact (@lem5764731 _120712 (@DIFF _120712 s t) x t). Qed.
Lemma lem5764736 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term29 A x s t) = (term30 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem5764737 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) (t : _120712 -> Prop) : (term29 _120712 x s t) = (term30 _120712 s x t).
Proof. exact (@lem5764736 _120712 s x t). Qed.
Lemma lem5764741 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5764742 {_120712 : Type'} (P : _120712 -> Prop) (x : _120712) : (@IN _120712 x P) = (P x).
Proof. exact (@lem5764741 _120712 P x). Qed.
Lemma lem5764743 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) : (@IN _120712 x s) = (s x).
Proof. exact (@lem5764742 _120712 s x). Qed.
Lemma lem5764744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5764745 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) : (term31 _120712 x s) = (term32 _120712 s x).
Proof. exact (MK_COMB (@lem5764744) (@lem5764743 _120712 s x)). Qed.
Lemma lem5764747 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5764748 {_120712 : Type'} (P : _120712 -> Prop) (x : _120712) : (@IN _120712 x P) = (P x).
Proof. exact (@lem5764747 _120712 P x). Qed.
Lemma lem5764749 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) : (@IN _120712 x t) = (t x).
Proof. exact (@lem5764748 _120712 t x). Qed.
Lemma lem5764750 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5764751 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) : (term33 _120712 x t) = (term34 _120712 t x).
Proof. exact (MK_COMB (@lem5764750) (@lem5764749 _120712 t x)). Qed.
Lemma lem5764752 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term30 _120712 s x t) = (term35 _120712 s t x).
Proof. exact (MK_COMB (@lem5764745 _120712 s x) (@lem5764751 _120712 t x)). Qed.
Lemma lem5764755 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term29 _120712 x s t) = (term35 _120712 s t x).
Proof. exact (TRANS (@lem5764737 _120712 s x t) (@lem5764752 _120712 s t x)). Qed.
Lemma lem5764756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5764757 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term47 _120712 x s t) = (term48 _120712 s t x).
Proof. exact (MK_COMB (@lem5764756) (@lem5764755 _120712 s t x)). Qed.
Lemma lem5764759 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5764760 {_120712 : Type'} (P : _120712 -> Prop) (x : _120712) : (@IN _120712 x P) = (P x).
Proof. exact (@lem5764759 _120712 P x). Qed.
Lemma lem5764761 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) : (@IN _120712 x t) = (t x).
Proof. exact (@lem5764760 _120712 t x). Qed.
Lemma lem5764762 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term46 _120712 s x t) = (term49 _120712 s t x).
Proof. exact (MK_COMB (@lem5764757 _120712 s t x) (@lem5764761 _120712 t x)). Qed.
Lemma lem5764765 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term45 _120712 x s t) = (term49 _120712 s t x).
Proof. exact (TRANS (@lem5764732 _120712 s x t) (@lem5764762 _120712 s t x)). Qed.
Lemma lem5764766 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5764767 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term50 _120712 x s t) = (term51 _120712 s t x).
Proof. exact (MK_COMB (@lem5764766) (@lem5764765 _120712 s t x)). Qed.
Lemma lem5764769 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5764770 {_120712 : Type'} (x : _120712) : (@IN _120712 x (@EMPTY _120712)) = False.
Proof. exact (@lem5764769 _120712 x). Qed.
Lemma lem5764771 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : ((term45 _120712 x s t) = (@IN _120712 x (@EMPTY _120712))) = ((term49 _120712 s t x) = False).
Proof. exact (MK_COMB (@lem5764767 _120712 s t x) (@lem5764770 _120712 x)). Qed.
Lemma lem5764773 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5764774 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : ((term49 _120712 s t x) = False) = (term52 _120712 s t x).
Proof. exact (@lem5764773 (term49 _120712 s t x)). Qed.
Lemma lem5764779 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : ((term45 _120712 x s t) = (@IN _120712 x (@EMPTY _120712))) = (term52 _120712 s t x).
Proof. exact (TRANS (@lem5764771 _120712 s t x) (@lem5764774 _120712 s t x)). Qed.
Lemma lem5764780 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term53 _120712 s t) = (term54 _120712 s t).
Proof. exact (fun_ext (fun x : _120712 => @lem5764779 _120712 s t x)). Qed.
Lemma lem5764781 {_120712 : Type'} : (@all _120712) = (@all _120712).
Proof. exact (eq_refl (@all _120712)). Qed.
Lemma lem5764782 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term10 _120712 s t) = (term55 _120712 s t).
Proof. exact (MK_COMB (@lem5764781 _120712) (@lem5764780 _120712 s t)). Qed.
Lemma lem5764787 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term12 _120712 s t) = (term56 _120712 s t).
Proof. exact (MK_COMB (@lem5764722 _120712 s t) (@lem5764782 _120712 s t)). Qed.
Lemma lem5764790 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term14 _120712 s t) = (term57 _120712 s t).
Proof. exact (MK_COMB (@lem5764659 _120712 t s) (@lem5764787 _120712 s t)). Qed.
Lemma lem5764793 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term57 _120712 s t) = (term14 _120712 s t).
Proof. exact (SYM (@lem5764790 _120712 s t)). Qed.
Lemma lem5764795 (p : Prop) : p = (term58 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5764796 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term57 _120712 s t) = (term59 _120712 s t).
Proof. exact (@lem5764795 (term57 _120712 s t)). Qed.
Lemma lem5764797 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term59 _120712 s t) = (term57 _120712 s t).
Proof. exact (SYM (@lem5764796 _120712 s t)). Qed.
Lemma lem5764798 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term60 _120712 s t) : term60 _120712 s t.
Proof. exact (h1). Qed.
Lemma lem5764801 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term59 _120712 s t) : term59 _120712 s t.
Proof. exact (h1). Qed.
Lemma lem5764802 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : term61 _120712 s t.
Proof. exact (fun h0 : term59 _120712 s t => @lem5764801 _120712 s t h0). Qed.
Lemma lem5764803 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term61 _120712 s t) : term61 _120712 s t.
Proof. exact (h1). Qed.
Lemma lem5764804 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term59 _120712 s t) : term59 _120712 s t.
Proof. exact (h1). Qed.
Lemma lem5764805 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term59 _120712 s t) (h2 : term61 _120712 s t) : term59 _120712 s t.
Proof. exact (@lem5764803 _120712 s t h2 (@lem5764804 _120712 s t h1)). Qed.
Lemma lem5764806 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term59 _120712 s t) : term62 _120712 s t.
Proof. exact (fun h0 : term61 _120712 s t => @lem5764805 _120712 s t h1 h0). Qed.
Lemma lem5764807 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term61 _120712 s t) : term61 _120712 s t.
Proof. exact (h1). Qed.
Lemma lem5764808 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term59 _120712 s t) (h2 : term61 _120712 s t) : term59 _120712 s t.
Proof. exact (@lem5764806 _120712 s t h1 (@lem5764807 _120712 s t h2)). Qed.
Lemma lem5764809 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term61 _120712 s t) : term61 _120712 s t.
Proof. exact (fun h0 : term59 _120712 s t => @lem5764808 _120712 s t h0 h1). Qed.
Lemma lem5764810 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : term63 _120712 s t.
Proof. exact (fun h0 : term61 _120712 s t => @lem5764809 _120712 s t h0). Qed.
Lemma lem5764813 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : term61 _120712 s t.
Proof. exact (@lem5764810 _120712 s t (@lem5764802 _120712 s t)). Qed.
Lemma lem5764814 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : term61 _120712 s t.
Proof. exact (@lem5764813 _120712 s t). Qed.
Lemma lem5764824 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5764825 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term59 _120712 s t) = (term64 _120712 s t).
Proof. exact (@lem5764824 (term60 _120712 s t)). Qed.
Lemma lem5764827 (t : Prop) : (term65 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5764828 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term64 _120712 s t) = (term57 _120712 s t).
Proof. exact (@lem5764827 (term57 _120712 s t)). Qed.
Lemma lem5764831 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term59 _120712 s t) = (term57 _120712 s t).
Proof. exact (TRANS (@lem5764825 _120712 s t) (@lem5764828 _120712 s t)). Qed.
Lemma lem5764856 {_120712 : Type'} (t : _120712 -> Prop) : (term66 _120712 t) = (term67 _120712 t).
Proof. exact (fun_ext (fun s : _120712 -> Prop => @lem5764831 _120712 s t)). Qed.
Lemma lem5764857 {_120712 : Type'} : (@all (_120712 -> Prop)) = (@all (_120712 -> Prop)).
Proof. exact (eq_refl (@all (_120712 -> Prop))). Qed.
Lemma lem5764858 {_120712 : Type'} (t : _120712 -> Prop) : (term68 _120712 t) = (term69 _120712 t).
Proof. exact (MK_COMB (@lem5764857 _120712) (@lem5764856 _120712 t)). Qed.
Lemma lem5764863 {_120712 : Type'} : (term70 _120712) = (term71 _120712).
Proof. exact (fun_ext (fun t : _120712 -> Prop => @lem5764858 _120712 t)). Qed.
Lemma lem5764864 {_120712 : Type'} : (@all (_120712 -> Prop)) = (@all (_120712 -> Prop)).
Proof. exact (eq_refl (@all (_120712 -> Prop))). Qed.
Lemma lem5764873 {_120712 : Type'} : (term72 _120712) = (term73 _120712).
Proof. exact (MK_COMB (@lem5764864 _120712) (@lem5764863 _120712)). Qed.
Lemma lem5764886 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term52 _120712 s t x) = (term52 _120712 s t x).
Proof. exact (eq_refl (term52 _120712 s t x)). Qed.
Lemma lem5764887 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term54 _120712 s t) = (term54 _120712 s t).
Proof. exact (fun_ext (fun x : _120712 => @lem5764886 _120712 s t x)). Qed.
Lemma lem5764888 {_120712 : Type'} : (@all _120712) = (@all _120712).
Proof. exact (eq_refl (@all _120712)). Qed.
Lemma lem5764889 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term55 _120712 s t) = (term55 _120712 s t).
Proof. exact (MK_COMB (@lem5764888 _120712) (@lem5764887 _120712 s t)). Qed.
Lemma lem5764904 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : ((s x) = (term38 _120712 s t x)) = ((s x) = (term38 _120712 s t x)).
Proof. exact (eq_refl ((s x) = (term38 _120712 s t x))). Qed.
Lemma lem5764905 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term40 _120712 s t) = (term40 _120712 s t).
Proof. exact (fun_ext (fun x : _120712 => @lem5764904 _120712 s t x)). Qed.
Lemma lem5764906 {_120712 : Type'} : (@all _120712) = (@all _120712).
Proof. exact (eq_refl (@all _120712)). Qed.
Lemma lem5764907 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term41 _120712 s t) = (term41 _120712 s t).
Proof. exact (MK_COMB (@lem5764906 _120712) (@lem5764905 _120712 s t)). Qed.
Lemma lem5764908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5764909 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term42 _120712 s t) = (term42 _120712 s t).
Proof. exact (MK_COMB (@lem5764908) (@lem5764907 _120712 s t)). Qed.
Lemma lem5764910 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term56 _120712 s t) = (term56 _120712 s t).
Proof. exact (MK_COMB (@lem5764909 _120712 s t) (@lem5764889 _120712 s t)). Qed.
Lemma lem5764915 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) (x : _120712) : (term18 _120712 t s x) = (term18 _120712 t s x).
Proof. exact (eq_refl (term18 _120712 t s x)). Qed.
Lemma lem5764916 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) : (term20 _120712 t s) = (term20 _120712 t s).
Proof. exact (fun_ext (fun x : _120712 => @lem5764915 _120712 t s x)). Qed.
Lemma lem5764917 {_120712 : Type'} : (@all _120712) = (@all _120712).
Proof. exact (eq_refl (@all _120712)). Qed.
Lemma lem5764918 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) : (term21 _120712 t s) = (term21 _120712 t s).
Proof. exact (MK_COMB (@lem5764917 _120712) (@lem5764916 _120712 t s)). Qed.
Lemma lem5764919 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5764920 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) : (term22 _120712 t s) = (term22 _120712 t s).
Proof. exact (MK_COMB (@lem5764919) (@lem5764918 _120712 t s)). Qed.
Lemma lem5764921 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term57 _120712 s t) = (term57 _120712 s t).
Proof. exact (MK_COMB (@lem5764920 _120712 t s) (@lem5764910 _120712 s t)). Qed.
Lemma lem5764922 {_120712 : Type'} (t : _120712 -> Prop) : (term67 _120712 t) = (term67 _120712 t).
Proof. exact (fun_ext (fun s : _120712 -> Prop => @lem5764921 _120712 s t)). Qed.
Lemma lem5764923 {_120712 : Type'} : (@all (_120712 -> Prop)) = (@all (_120712 -> Prop)).
Proof. exact (eq_refl (@all (_120712 -> Prop))). Qed.
Lemma lem5764924 {_120712 : Type'} (t : _120712 -> Prop) : (term69 _120712 t) = (term69 _120712 t).
Proof. exact (MK_COMB (@lem5764923 _120712) (@lem5764922 _120712 t)). Qed.
Lemma lem5764925 {_120712 : Type'} : (term71 _120712) = (term71 _120712).
Proof. exact (fun_ext (fun t : _120712 -> Prop => @lem5764924 _120712 t)). Qed.
Lemma lem5764926 {_120712 : Type'} : (@all (_120712 -> Prop)) = (@all (_120712 -> Prop)).
Proof. exact (eq_refl (@all (_120712 -> Prop))). Qed.
Lemma lem5764927 {_120712 : Type'} : (term73 _120712) = (term73 _120712).
Proof. exact (MK_COMB (@lem5764926 _120712) (@lem5764925 _120712)). Qed.
Lemma lem5764974 {_120712 : Type'} : (term72 _120712) = (term73 _120712).
Proof. exact (TRANS (@lem5764873 _120712) (@lem5764927 _120712)). Qed.
Lemma lem5764975 {_120712 : Type'} : (term73 _120712) = (term72 _120712).
Proof. exact (SYM (@lem5764974 _120712)). Qed.
Lemma lem5764976 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) (h1 : term21 _120712 t s) : term21 _120712 t s.
Proof. exact (h1). Qed.
Lemma lem5764978 (p : Prop) : p = (term58 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5764979 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term56 _120712 s t) = (term74 _120712 s t).
Proof. exact (@lem5764978 (term56 _120712 s t)). Qed.
Lemma lem5764980 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term74 _120712 s t) = (term56 _120712 s t).
Proof. exact (SYM (@lem5764979 _120712 s t)). Qed.
Lemma lem5764981 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term75 _120712 s t) : term75 _120712 s t.
Proof. exact (h1). Qed.
Lemma lem5764988 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) (x : _120712) : (term18 _120712 t s x) = (term76 _120712 t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem5764989 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) : (term20 _120712 t s) = (term77 _120712 t s).
Proof. exact (fun_ext (fun x : _120712 => @lem5764988 _120712 t s x)). Qed.
Lemma lem5764990 {_120712 : Type'} : (@all _120712) = (@all _120712).
Proof. exact (eq_refl (@all _120712)). Qed.
Lemma lem5765027 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) : (term21 _120712 t s) = (term78 _120712 t s).
Proof. exact (MK_COMB (@lem5764990 _120712) (@lem5764989 _120712 t s)). Qed.
Lemma lem5765028 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) (h1 : term21 _120712 t s) : term78 _120712 t s.
Proof. exact (EQ_MP (@lem5765027 _120712 t s) (@lem5764976 _120712 t s h1)). Qed.
Lemma lem5765036 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) : (term79 _120712 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem5765038 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) : (term80 _120712 s x) = (term80 _120712 s x).
Proof. exact (eq_refl (term80 _120712 s x)). Qed.
Lemma lem5765039 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term81 _120712 s t x) = (term76 _120712 s t x).
Proof. exact (MK_COMB (@lem5765038 _120712 s x) (@lem5765036 _120712 t x)). Qed.
Lemma lem5765040 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term82 _120712 s t x) = (term81 _120712 s t x).
Proof. exact (@lem17045 (s x) (term34 _120712 t x)). Qed.
Lemma lem5765041 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term82 _120712 s t x) = (term76 _120712 s t x).
Proof. exact (TRANS (@lem5765040 _120712 s t x) (@lem5765039 _120712 s t x)). Qed.
Lemma lem5765045 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) : (term34 _120712 t x) = (term34 _120712 t x).
Proof. exact (eq_refl (term34 _120712 t x)). Qed.
Lemma lem5765047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5765048 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term83 _120712 s t x) = (term84 _120712 s t x).
Proof. exact (MK_COMB (@lem5765047) (@lem5765041 _120712 s t x)). Qed.
Lemma lem5765049 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term85 _120712 s t x) = (term86 _120712 s t x).
Proof. exact (MK_COMB (@lem5765048 _120712 s t x) (@lem5765045 _120712 t x)). Qed.
Lemma lem5765050 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term87 _120712 s t x) = (term85 _120712 s t x).
Proof. exact (@lem17160 (term35 _120712 s t x) (t x)). Qed.
Lemma lem5765051 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term87 _120712 s t x) = (term86 _120712 s t x).
Proof. exact (TRANS (@lem5765050 _120712 s t x) (@lem5765049 _120712 s t x)). Qed.
Lemma lem5765057 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term88 _120712 s t x) = (term88 _120712 s t x).
Proof. exact (eq_refl (term88 _120712 s t x)). Qed.
Lemma lem5765059 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) : (term32 _120712 s x) = (term32 _120712 s x).
Proof. exact (eq_refl (term32 _120712 s x)). Qed.
Lemma lem5765060 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term89 _120712 s t x) = (term90 _120712 s t x).
Proof. exact (MK_COMB (@lem5765059 _120712 s x) (@lem5765051 _120712 s t x)). Qed.
Lemma lem5765061 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5765062 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term91 _120712 s t x) = (term92 _120712 s t x).
Proof. exact (MK_COMB (@lem5765061) (@lem5765060 _120712 s t x)). Qed.
Lemma lem5765063 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term93 _120712 s t x) = (term94 _120712 s t x).
Proof. exact (MK_COMB (@lem5765062 _120712 s t x) (@lem5765057 _120712 s t x)). Qed.
Lemma lem5765064 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term95 _120712 s t x) = (term93 _120712 s t x).
Proof. exact (@lem17646 (s x) (term38 _120712 s t x)). Qed.
Lemma lem5765065 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term95 _120712 s t x) = (term94 _120712 s t x).
Proof. exact (TRANS (@lem5765064 _120712 s t x) (@lem5765063 _120712 s t x)). Qed.
Lemma lem5765066 {_120712 : Type'} (P : _120712 -> Prop) : (term96 _120712 P) = (term97 _120712 P).
Proof. exact (@lem18392 _120712 P). Qed.
Lemma lem5765067 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term98 _120712 s t) = (term99 _120712 s t).
Proof. exact (@lem5765066 _120712 (term40 _120712 s t)). Qed.
Lemma lem5765068 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term100 _120712 s t x) = ((s x) = (term38 _120712 s t x)).
Proof. exact (eq_refl (term100 _120712 s t x)). Qed.
Lemma lem5765069 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5765070 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term101 _120712 s t x) = (term95 _120712 s t x).
Proof. exact (MK_COMB (@lem5765069) (@lem5765068 _120712 s t x)). Qed.
Lemma lem5765071 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term101 _120712 s t x) = (term94 _120712 s t x).
Proof. exact (TRANS (@lem5765070 _120712 s t x) (@lem5765065 _120712 s t x)). Qed.
Lemma lem5765072 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term102 _120712 s t) = (term103 _120712 s t).
Proof. exact (fun_ext (fun x : _120712 => @lem5765071 _120712 s t x)). Qed.
Lemma lem5765073 {_120712 : Type'} : (@ex _120712) = (@ex _120712).
Proof. exact (eq_refl (@ex _120712)). Qed.
Lemma lem5765074 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term99 _120712 s t) = (term104 _120712 s t).
Proof. exact (MK_COMB (@lem5765073 _120712) (@lem5765072 _120712 s t)). Qed.
Lemma lem5765075 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term98 _120712 s t) = (term104 _120712 s t).
Proof. exact (TRANS (@lem5765067 _120712 s t) (@lem5765074 _120712 s t)). Qed.
Lemma lem5765086 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term105 _120712 s t x) = (term49 _120712 s t x).
Proof. exact (@lem16933 (term49 _120712 s t x)). Qed.
Lemma lem5765087 {_120712 : Type'} (P : _120712 -> Prop) : (term96 _120712 P) = (term97 _120712 P).
Proof. exact (@lem18392 _120712 P). Qed.
Lemma lem5765088 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term106 _120712 s t) = (term107 _120712 s t).
Proof. exact (@lem5765087 _120712 (term54 _120712 s t)). Qed.
Lemma lem5765089 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term108 _120712 s t x) = (term52 _120712 s t x).
Proof. exact (eq_refl (term108 _120712 s t x)). Qed.
Lemma lem5765090 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5765091 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term109 _120712 s t x) = (term105 _120712 s t x).
Proof. exact (MK_COMB (@lem5765090) (@lem5765089 _120712 s t x)). Qed.
Lemma lem5765092 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term109 _120712 s t x) = (term49 _120712 s t x).
Proof. exact (TRANS (@lem5765091 _120712 s t x) (@lem5765086 _120712 s t x)). Qed.
Lemma lem5765093 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term110 _120712 s t) = (term111 _120712 s t).
Proof. exact (fun_ext (fun x : _120712 => @lem5765092 _120712 s t x)). Qed.
Lemma lem5765094 {_120712 : Type'} : (@ex _120712) = (@ex _120712).
Proof. exact (eq_refl (@ex _120712)). Qed.
Lemma lem5765095 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term107 _120712 s t) = (term112 _120712 s t).
Proof. exact (MK_COMB (@lem5765094 _120712) (@lem5765093 _120712 s t)). Qed.
Lemma lem5765096 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term106 _120712 s t) = (term112 _120712 s t).
Proof. exact (TRANS (@lem5765088 _120712 s t) (@lem5765095 _120712 s t)). Qed.
Lemma lem5765097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5765098 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term113 _120712 s t) = (term114 _120712 s t).
Proof. exact (MK_COMB (@lem5765097) (@lem5765075 _120712 s t)). Qed.
Lemma lem5765099 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term115 _120712 s t) = (term116 _120712 s t).
Proof. exact (MK_COMB (@lem5765098 _120712 s t) (@lem5765096 _120712 s t)). Qed.
Lemma lem5765100 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term75 _120712 s t) = (term115 _120712 s t).
Proof. exact (@lem17045 (term41 _120712 s t) (term55 _120712 s t)). Qed.
Lemma lem5765101 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term75 _120712 s t) = (term116 _120712 s t).
Proof. exact (TRANS (@lem5765100 _120712 s t) (@lem5765099 _120712 s t)). Qed.
Lemma lem5765103 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term117 A P Q) = (term118 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5765104 {_120712 : Type'} (P : _120712 -> Prop) (Q : _120712 -> Prop) : (term117 _120712 P Q) = (term118 _120712 P Q).
Proof. exact (@lem5765103 _120712 P Q). Qed.
Lemma lem5765105 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term119 _120712 s t) = (term120 _120712 s t).
Proof. exact (@lem5765104 _120712 (term121 _120712 s t) (term122 _120712 s t)). Qed.
Lemma lem5765106 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term123 _120712 s t x) = (term90 _120712 s t x).
Proof. exact (eq_refl (term123 _120712 s t x)). Qed.
Lemma lem5765107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5765108 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term124 _120712 s t x) = (term92 _120712 s t x).
Proof. exact (MK_COMB (@lem5765107) (@lem5765106 _120712 s t x)). Qed.
Lemma lem5765109 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term125 _120712 s t x) = (term88 _120712 s t x).
Proof. exact (eq_refl (term125 _120712 s t x)). Qed.
Lemma lem5765110 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term126 _120712 s t x) = (term94 _120712 s t x).
Proof. exact (MK_COMB (@lem5765108 _120712 s t x) (@lem5765109 _120712 s t x)). Qed.
Lemma lem5765111 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term127 _120712 s t) = (term103 _120712 s t).
Proof. exact (fun_ext (fun x : _120712 => @lem5765110 _120712 s t x)). Qed.
Lemma lem5765112 {_120712 : Type'} : (@ex _120712) = (@ex _120712).
Proof. exact (eq_refl (@ex _120712)). Qed.
Lemma lem5765113 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term119 _120712 s t) = (term104 _120712 s t).
Proof. exact (MK_COMB (@lem5765112 _120712) (@lem5765111 _120712 s t)). Qed.
Lemma lem5765114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5765115 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term128 _120712 s t) = (term129 _120712 s t).
Proof. exact (MK_COMB (@lem5765114) (@lem5765113 _120712 s t)). Qed.
Lemma lem5765116 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term123 _120712 s t x) = (term90 _120712 s t x).
Proof. exact (eq_refl (term123 _120712 s t x)). Qed.
Lemma lem5765117 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term130 _120712 s t) = (term121 _120712 s t).
Proof. exact (fun_ext (fun x : _120712 => @lem5765116 _120712 s t x)). Qed.
Lemma lem5765118 {_120712 : Type'} : (@ex _120712) = (@ex _120712).
Proof. exact (eq_refl (@ex _120712)). Qed.
Lemma lem5765119 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term131 _120712 s t) = (term132 _120712 s t).
Proof. exact (MK_COMB (@lem5765118 _120712) (@lem5765117 _120712 s t)). Qed.
Lemma lem5765120 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5765121 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term133 _120712 s t) = (term134 _120712 s t).
Proof. exact (MK_COMB (@lem5765120) (@lem5765119 _120712 s t)). Qed.
Lemma lem5765122 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term125 _120712 s t x) = (term88 _120712 s t x).
Proof. exact (eq_refl (term125 _120712 s t x)). Qed.
Lemma lem5765123 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term135 _120712 s t) = (term122 _120712 s t).
Proof. exact (fun_ext (fun x : _120712 => @lem5765122 _120712 s t x)). Qed.
Lemma lem5765124 {_120712 : Type'} : (@ex _120712) = (@ex _120712).
Proof. exact (eq_refl (@ex _120712)). Qed.
Lemma lem5765125 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term136 _120712 s t) = (term137 _120712 s t).
Proof. exact (MK_COMB (@lem5765124 _120712) (@lem5765123 _120712 s t)). Qed.
Lemma lem5765126 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term120 _120712 s t) = (term138 _120712 s t).
Proof. exact (MK_COMB (@lem5765121 _120712 s t) (@lem5765125 _120712 s t)). Qed.
Lemma lem5765127 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : ((term119 _120712 s t) = (term120 _120712 s t)) = ((term104 _120712 s t) = (term138 _120712 s t)).
Proof. exact (MK_COMB (@lem5765115 _120712 s t) (@lem5765126 _120712 s t)). Qed.
Lemma lem5765128 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term104 _120712 s t) = (term138 _120712 s t).
Proof. exact (EQ_MP (@lem5765127 _120712 s t) (@lem5765105 _120712 s t)). Qed.
Lemma lem5765205 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5765206 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term114 _120712 s t) = (term139 _120712 s t).
Proof. exact (MK_COMB (@lem5765205) (@lem5765128 _120712 s t)). Qed.
Lemma lem5765239 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term112 _120712 s t) = (term112 _120712 s t).
Proof. exact (eq_refl (term112 _120712 s t)). Qed.
Lemma lem5765240 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term116 _120712 s t) = (term140 _120712 s t).
Proof. exact (MK_COMB (@lem5765206 _120712 s t) (@lem5765239 _120712 s t)). Qed.
Lemma lem5765242 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5765243 {_120712 : Type'} (P : _120712 -> Prop) (Q : _120712 -> Prop) : (term118 _120712 P Q) = (term117 _120712 P Q).
Proof. exact (@lem5765242 _120712 P Q). Qed.
Lemma lem5765244 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term120 _120712 s t) = (term119 _120712 s t).
Proof. exact (@lem5765243 _120712 (term121 _120712 s t) (term122 _120712 s t)). Qed.
Lemma lem5765245 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term123 _120712 s t x) = (term90 _120712 s t x).
Proof. exact (eq_refl (term123 _120712 s t x)). Qed.
Lemma lem5765246 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term130 _120712 s t) = (term121 _120712 s t).
Proof. exact (fun_ext (fun x : _120712 => @lem5765245 _120712 s t x)). Qed.
Lemma lem5765247 {_120712 : Type'} : (@ex _120712) = (@ex _120712).
Proof. exact (eq_refl (@ex _120712)). Qed.
Lemma lem5765248 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term131 _120712 s t) = (term132 _120712 s t).
Proof. exact (MK_COMB (@lem5765247 _120712) (@lem5765246 _120712 s t)). Qed.
Lemma lem5765249 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5765250 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term133 _120712 s t) = (term134 _120712 s t).
Proof. exact (MK_COMB (@lem5765249) (@lem5765248 _120712 s t)). Qed.
Lemma lem5765251 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term125 _120712 s t x) = (term88 _120712 s t x).
Proof. exact (eq_refl (term125 _120712 s t x)). Qed.
Lemma lem5765252 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term135 _120712 s t) = (term122 _120712 s t).
Proof. exact (fun_ext (fun x : _120712 => @lem5765251 _120712 s t x)). Qed.
Lemma lem5765253 {_120712 : Type'} : (@ex _120712) = (@ex _120712).
Proof. exact (eq_refl (@ex _120712)). Qed.
Lemma lem5765254 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term136 _120712 s t) = (term137 _120712 s t).
Proof. exact (MK_COMB (@lem5765253 _120712) (@lem5765252 _120712 s t)). Qed.
Lemma lem5765255 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term120 _120712 s t) = (term138 _120712 s t).
Proof. exact (MK_COMB (@lem5765250 _120712 s t) (@lem5765254 _120712 s t)). Qed.
Lemma lem5765256 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5765257 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term141 _120712 s t) = (term142 _120712 s t).
Proof. exact (MK_COMB (@lem5765256) (@lem5765255 _120712 s t)). Qed.
Lemma lem5765258 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term123 _120712 s t x) = (term90 _120712 s t x).
Proof. exact (eq_refl (term123 _120712 s t x)). Qed.
Lemma lem5765259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5765260 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term124 _120712 s t x) = (term92 _120712 s t x).
Proof. exact (MK_COMB (@lem5765259) (@lem5765258 _120712 s t x)). Qed.
Lemma lem5765261 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term125 _120712 s t x) = (term88 _120712 s t x).
Proof. exact (eq_refl (term125 _120712 s t x)). Qed.
Lemma lem5765262 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term126 _120712 s t x) = (term94 _120712 s t x).
Proof. exact (MK_COMB (@lem5765260 _120712 s t x) (@lem5765261 _120712 s t x)). Qed.
Lemma lem5765263 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term127 _120712 s t) = (term103 _120712 s t).
Proof. exact (fun_ext (fun x : _120712 => @lem5765262 _120712 s t x)). Qed.
Lemma lem5765264 {_120712 : Type'} : (@ex _120712) = (@ex _120712).
Proof. exact (eq_refl (@ex _120712)). Qed.
Lemma lem5765265 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term119 _120712 s t) = (term104 _120712 s t).
Proof. exact (MK_COMB (@lem5765264 _120712) (@lem5765263 _120712 s t)). Qed.
Lemma lem5765266 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : ((term120 _120712 s t) = (term119 _120712 s t)) = ((term138 _120712 s t) = (term104 _120712 s t)).
Proof. exact (MK_COMB (@lem5765257 _120712 s t) (@lem5765265 _120712 s t)). Qed.
Lemma lem5765267 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term138 _120712 s t) = (term104 _120712 s t).
Proof. exact (EQ_MP (@lem5765266 _120712 s t) (@lem5765244 _120712 s t)). Qed.
Lemma lem5765268 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5765269 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term139 _120712 s t) = (term114 _120712 s t).
Proof. exact (MK_COMB (@lem5765268) (@lem5765267 _120712 s t)). Qed.
Lemma lem5765270 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term112 _120712 s t) = (term112 _120712 s t).
Proof. exact (eq_refl (term112 _120712 s t)). Qed.
Lemma lem5765271 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term140 _120712 s t) = (term116 _120712 s t).
Proof. exact (MK_COMB (@lem5765269 _120712 s t) (@lem5765270 _120712 s t)). Qed.
Lemma lem5765273 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5765274 {_120712 : Type'} (P : _120712 -> Prop) (Q : _120712 -> Prop) : (term118 _120712 P Q) = (term117 _120712 P Q).
Proof. exact (@lem5765273 _120712 P Q). Qed.
Lemma lem5765275 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term143 _120712 s t) = (term144 _120712 s t).
Proof. exact (@lem5765274 _120712 (term103 _120712 s t) (term111 _120712 s t)). Qed.
Lemma lem5765276 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term145 _120712 s t x) = (term94 _120712 s t x).
Proof. exact (eq_refl (term145 _120712 s t x)). Qed.
Lemma lem5765277 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term146 _120712 s t) = (term103 _120712 s t).
Proof. exact (fun_ext (fun x : _120712 => @lem5765276 _120712 s t x)). Qed.
Lemma lem5765278 {_120712 : Type'} : (@ex _120712) = (@ex _120712).
Proof. exact (eq_refl (@ex _120712)). Qed.
Lemma lem5765279 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term147 _120712 s t) = (term104 _120712 s t).
Proof. exact (MK_COMB (@lem5765278 _120712) (@lem5765277 _120712 s t)). Qed.
Lemma lem5765280 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5765281 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term148 _120712 s t) = (term114 _120712 s t).
Proof. exact (MK_COMB (@lem5765280) (@lem5765279 _120712 s t)). Qed.
Lemma lem5765282 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term149 _120712 s t x) = (term49 _120712 s t x).
Proof. exact (eq_refl (term149 _120712 s t x)). Qed.
Lemma lem5765283 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term150 _120712 s t) = (term111 _120712 s t).
Proof. exact (fun_ext (fun x : _120712 => @lem5765282 _120712 s t x)). Qed.
Lemma lem5765284 {_120712 : Type'} : (@ex _120712) = (@ex _120712).
Proof. exact (eq_refl (@ex _120712)). Qed.
Lemma lem5765285 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term151 _120712 s t) = (term112 _120712 s t).
Proof. exact (MK_COMB (@lem5765284 _120712) (@lem5765283 _120712 s t)). Qed.
Lemma lem5765286 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term143 _120712 s t) = (term116 _120712 s t).
Proof. exact (MK_COMB (@lem5765281 _120712 s t) (@lem5765285 _120712 s t)). Qed.
Lemma lem5765287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5765288 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term152 _120712 s t) = (term153 _120712 s t).
Proof. exact (MK_COMB (@lem5765287) (@lem5765286 _120712 s t)). Qed.
Lemma lem5765289 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term145 _120712 s t x) = (term94 _120712 s t x).
Proof. exact (eq_refl (term145 _120712 s t x)). Qed.
Lemma lem5765290 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5765291 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term154 _120712 s t x) = (term155 _120712 s t x).
Proof. exact (MK_COMB (@lem5765290) (@lem5765289 _120712 s t x)). Qed.
Lemma lem5765292 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term149 _120712 s t x) = (term49 _120712 s t x).
Proof. exact (eq_refl (term149 _120712 s t x)). Qed.
Lemma lem5765293 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) : (term156 _120712 s t x) = (term157 _120712 s t x).
Proof. exact (MK_COMB (@lem5765291 _120712 s t x) (@lem5765292 _120712 s t x)). Qed.
Lemma lem5765294 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term158 _120712 s t) = (term159 _120712 s t).
Proof. exact (fun_ext (fun x : _120712 => @lem5765293 _120712 s t x)). Qed.
Lemma lem5765295 {_120712 : Type'} : (@ex _120712) = (@ex _120712).
Proof. exact (eq_refl (@ex _120712)). Qed.
Lemma lem5765296 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term144 _120712 s t) = (term160 _120712 s t).
Proof. exact (MK_COMB (@lem5765295 _120712) (@lem5765294 _120712 s t)). Qed.
Lemma lem5765297 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : ((term143 _120712 s t) = (term144 _120712 s t)) = ((term116 _120712 s t) = (term160 _120712 s t)).
Proof. exact (MK_COMB (@lem5765288 _120712 s t) (@lem5765296 _120712 s t)). Qed.
Lemma lem5765298 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term116 _120712 s t) = (term160 _120712 s t).
Proof. exact (EQ_MP (@lem5765297 _120712 s t) (@lem5765275 _120712 s t)). Qed.
Lemma lem5765299 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term140 _120712 s t) = (term160 _120712 s t).
Proof. exact (TRANS (@lem5765271 _120712 s t) (@lem5765298 _120712 s t)). Qed.
Lemma lem5765300 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term116 _120712 s t) = (term160 _120712 s t).
Proof. exact (TRANS (@lem5765240 _120712 s t) (@lem5765299 _120712 s t)). Qed.
Lemma lem5765301 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term75 _120712 s t) = (term160 _120712 s t).
Proof. exact (TRANS (@lem5765101 _120712 s t) (@lem5765300 _120712 s t)). Qed.
Lemma lem5765302 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term75 _120712 s t) : term160 _120712 s t.
Proof. exact (EQ_MP (@lem5765301 _120712 s t) (@lem5764981 _120712 s t h1)). Qed.
Lemma lem5765314 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) (x : _120712) : (term76 _120712 t s x) = (term76 _120712 t s x).
Proof. exact (eq_refl (term76 _120712 t s x)). Qed.
Lemma lem5765315 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) : (term77 _120712 t s) = (term77 _120712 t s).
Proof. exact (fun_ext (fun x : _120712 => @lem5765314 _120712 t s x)). Qed.
Lemma lem5765316 {_120712 : Type'} : (@all _120712) = (@all _120712).
Proof. exact (eq_refl (@all _120712)). Qed.
Lemma lem5765317 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) : (term78 _120712 t s) = (term78 _120712 t s).
Proof. exact (MK_COMB (@lem5765316 _120712) (@lem5765315 _120712 t s)). Qed.
Lemma lem5765318 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) (h1 : term21 _120712 t s) : term78 _120712 t s.
Proof. exact (EQ_MP (@lem5765317 _120712 t s) (@lem5765028 _120712 t s h1)). Qed.
Lemma lem5765392 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term157 _120712 s t x) : term157 _120712 s t x.
Proof. exact (h1). Qed.
Lemma lem5765393 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term94 _120712 s t x) : term94 _120712 s t x.
Proof. exact (h1). Qed.
Lemma lem5765394 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term49 _120712 s t x) : term49 _120712 s t x.
Proof. exact (h1). Qed.
Lemma lem5765395 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term90 _120712 s t x) : term90 _120712 s t x.
Proof. exact (h1). Qed.
Lemma lem5765396 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term88 _120712 s t x) : term88 _120712 s t x.
Proof. exact (h1). Qed.
Lemma lem5765397 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term90 _120712 s t x) : term86 _120712 s t x.
Proof. exact (proj2 (@lem5765395 _120712 s t x h1)). Qed.
Lemma lem5765400 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term90 _120712 s t x) : term76 _120712 s t x.
Proof. exact (proj1 (@lem5765397 _120712 s t x h1)). Qed.
Lemma lem5765403 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term88 _120712 s t x) : term38 _120712 s t x.
Proof. exact (proj2 (@lem5765396 _120712 s t x h1)). Qed.
Lemma lem5765405 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term35 _120712 s t x) : term35 _120712 s t x.
Proof. exact (h1). Qed.
Lemma lem5765410 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term49 _120712 s t x) : term35 _120712 s t x.
Proof. exact (proj1 (@lem5765394 _120712 s t x h1)). Qed.
Lemma lem5765437 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) (h1 : term34 _120712 s x) : term34 _120712 s x.
Proof. exact (h1). Qed.
Lemma lem5765462 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem5765495 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) (x : _120712) : (term76 _120712 t s x) = (term76 _120712 t s x).
Proof. exact (eq_refl (term76 _120712 t s x)). Qed.
Lemma lem5765496 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) : (term77 _120712 t s) = (term77 _120712 t s).
Proof. exact (fun_ext (fun x : _120712 => @lem5765495 _120712 t s x)). Qed.
Lemma lem5765497 {_120712 : Type'} : (@all _120712) = (@all _120712).
Proof. exact (eq_refl (@all _120712)). Qed.
Lemma lem5765499 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) : (term78 _120712 t s) = (term78 _120712 t s).
Proof. exact (MK_COMB (@lem5765497 _120712) (@lem5765496 _120712 t s)). Qed.
Lemma lem5765500 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) (h1 : term21 _120712 t s) : term78 _120712 t s.
Proof. exact (EQ_MP (@lem5765499 _120712 t s) (@lem5765318 _120712 t s h1)). Qed.
Lemma lem5765508 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem5765543 {_120712 : Type'} (_72725 : _120712) (t : _120712 -> Prop) (s : _120712 -> Prop) (h1 : term21 _120712 t s) : term161 _120712 t s _72725.
Proof. exact (@lem5765500 _120712 t s h1 _72725). Qed.
Lemma lem5765544 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) (_72725 : _120712) : (term161 _120712 t s _72725) = (term76 _120712 t s _72725).
Proof. exact (eq_refl (term161 _120712 t s _72725)). Qed.
Lemma lem5765560 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) (h1 : term34 _120712 s x) : term34 _120712 s x.
Proof. exact (h1). Qed.
Lemma lem5765570 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term90 _120712 s t x) : term34 _120712 t x.
Proof. exact (proj2 (@lem5765397 _120712 s t x h1)). Qed.
Lemma lem5765572 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem5765580 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term88 _120712 s t x) : term34 _120712 s x.
Proof. exact (proj1 (@lem5765396 _120712 s t x h1)). Qed.
Lemma lem5765590 {_120712 : Type'} (_72725 : _120712) (t : _120712 -> Prop) (s : _120712 -> Prop) (h1 : term21 _120712 t s) : term76 _120712 t s _72725.
Proof. exact (EQ_MP (@lem5765544 _120712 t s _72725) (@lem5765543 _120712 _72725 t s h1)). Qed.
Lemma lem5765592 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term88 _120712 s t x) : term34 _120712 s x.
Proof. exact (proj1 (@lem5765396 _120712 s t x h1)). Qed.
Lemma lem5765594 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem5765606 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term49 _120712 s t x) : term34 _120712 t x.
Proof. exact (proj2 (@lem5765410 _120712 s t x h1)). Qed.
Lemma lem5765608 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term90 _120712 s t x) : s x.
Proof. exact (proj1 (@lem5765395 _120712 s t x h1)). Qed.
Lemma lem5765609 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term90 _120712 s t x) : term162 _120712 s x.
Proof. exact (fun h0 : term34 _120712 s x => @lem5765608 _120712 s t x h1). Qed.
Lemma lem5765611 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5765612 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) : (term162 _120712 s x) = (s x).
Proof. exact (@lem5765611 (s x)). Qed.
Lemma lem5765613 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term90 _120712 s t x) : s x.
Proof. exact (EQ_MP (@lem5765612 _120712 s x) (@lem5765609 _120712 s t x h1)). Qed.
Lemma lem5765616 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5765618 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) : (term34 _120712 s x) = (term164 _120712 s x).
Proof. exact (@lem5765616 (s x)). Qed.
Lemma lem5765621 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) (h1 : term34 _120712 s x) : term164 _120712 s x.
Proof. exact (EQ_MP (@lem5765618 _120712 s x) (@lem5765560 _120712 s x h1)). Qed.
Lemma lem5765624 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term34 _120712 s x) (h2 : term90 _120712 s t x) : False.
Proof. exact (@lem5765621 _120712 s x h1 (@lem5765613 _120712 s t x h2)). Qed.
Lemma lem5765625 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term34 _120712 s x) (h2 : term90 _120712 s t x) : term165.
Proof. exact (fun h0 : ~ False => @lem5765624 _120712 s t x h1 h2). Qed.
Lemma lem5765627 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5765628 : term165 = False.
Proof. exact (@lem5765627 False). Qed.
Lemma lem5765629 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term34 _120712 s x) (h2 : term90 _120712 s t x) : False.
Proof. exact (EQ_MP (@lem5765628) (@lem5765625 _120712 s t x h1 h2)). Qed.
Lemma lem5765631 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem5765632 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) (h1 : t x) : term162 _120712 t x.
Proof. exact (fun h0 : term34 _120712 t x => @lem5765631 _120712 t x h1). Qed.
Lemma lem5765634 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5765635 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) : (term162 _120712 t x) = (t x).
Proof. exact (@lem5765634 (t x)). Qed.
Lemma lem5765636 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem5765635 _120712 t x) (@lem5765632 _120712 t x h1)). Qed.
Lemma lem5765639 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5765641 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) : (term34 _120712 t x) = (term164 _120712 t x).
Proof. exact (@lem5765639 (t x)). Qed.
Lemma lem5765644 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term90 _120712 s t x) : term164 _120712 t x.
Proof. exact (EQ_MP (@lem5765641 _120712 t x) (@lem5765570 _120712 s t x h1)). Qed.
Lemma lem5765647 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : t x) (h2 : term90 _120712 s t x) : False.
Proof. exact (@lem5765644 _120712 s t x h2 (@lem5765636 _120712 t x h1)). Qed.
Lemma lem5765648 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : t x) (h2 : term90 _120712 s t x) : term165.
Proof. exact (fun h0 : ~ False => @lem5765647 _120712 s t x h1 h2). Qed.
Lemma lem5765650 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5765651 : term165 = False.
Proof. exact (@lem5765650 False). Qed.
Lemma lem5765652 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : t x) (h2 : term90 _120712 s t x) : False.
Proof. exact (EQ_MP (@lem5765651) (@lem5765648 _120712 s t x h1 h2)). Qed.
Lemma lem5765654 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term35 _120712 s t x) : s x.
Proof. exact (proj1 (@lem5765405 _120712 s t x h1)). Qed.
Lemma lem5765655 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term35 _120712 s t x) : term162 _120712 s x.
Proof. exact (fun h0 : term34 _120712 s x => @lem5765654 _120712 s t x h1). Qed.
Lemma lem5765657 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5765658 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) : (term162 _120712 s x) = (s x).
Proof. exact (@lem5765657 (s x)). Qed.
Lemma lem5765659 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term35 _120712 s t x) : s x.
Proof. exact (EQ_MP (@lem5765658 _120712 s x) (@lem5765655 _120712 s t x h1)). Qed.
Lemma lem5765662 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5765664 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) : (term34 _120712 s x) = (term164 _120712 s x).
Proof. exact (@lem5765662 (s x)). Qed.
Lemma lem5765667 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term88 _120712 s t x) : term164 _120712 s x.
Proof. exact (EQ_MP (@lem5765664 _120712 s x) (@lem5765580 _120712 s t x h1)). Qed.
Lemma lem5765670 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term88 _120712 s t x) (h2 : term35 _120712 s t x) : False.
Proof. exact (@lem5765667 _120712 s t x h1 (@lem5765659 _120712 s t x h2)). Qed.
Lemma lem5765671 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term88 _120712 s t x) (h2 : term35 _120712 s t x) : term165.
Proof. exact (fun h0 : ~ False => @lem5765670 _120712 s t x h1 h2). Qed.
Lemma lem5765673 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5765674 : term165 = False.
Proof. exact (@lem5765673 False). Qed.
Lemma lem5765675 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term88 _120712 s t x) (h2 : term35 _120712 s t x) : False.
Proof. exact (EQ_MP (@lem5765674) (@lem5765671 _120712 s t x h1 h2)). Qed.
Lemma lem5765677 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem5765678 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) (h1 : t x) : term162 _120712 t x.
Proof. exact (fun h0 : term34 _120712 t x => @lem5765677 _120712 t x h1). Qed.
Lemma lem5765680 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5765681 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) : (term162 _120712 t x) = (t x).
Proof. exact (@lem5765680 (t x)). Qed.
Lemma lem5765682 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem5765681 _120712 t x) (@lem5765678 _120712 t x h1)). Qed.
Lemma lem5765688 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5765689 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (_72725 : _120712) : (term76 _120712 t s _72725) = (term166 _120712 s t _72725).
Proof. exact (@lem5765688 (s _72725) (term34 _120712 t _72725)). Qed.
Lemma lem5765695 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5765696 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (_72725 : _120712) : (term167 _120712 t s _72725) = (term168 _120712 s t _72725).
Proof. exact (MK_COMB (@lem5765695) (@lem5765689 _120712 s t _72725)). Qed.
Lemma lem5765702 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (_72725 : _120712) : (term166 _120712 s t _72725) = (term166 _120712 s t _72725).
Proof. exact (eq_refl (term166 _120712 s t _72725)). Qed.
Lemma lem5765703 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (_72725 : _120712) : ((term76 _120712 t s _72725) = (term166 _120712 s t _72725)) = ((term166 _120712 s t _72725) = (term166 _120712 s t _72725)).
Proof. exact (MK_COMB (@lem5765696 _120712 s t _72725) (@lem5765702 _120712 s t _72725)). Qed.
Lemma lem5765705 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5765706 (x : Prop) : (x = x) = True.
Proof. exact (@lem5765705 Prop x). Qed.
Lemma lem5765707 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (_72725 : _120712) : ((term166 _120712 s t _72725) = (term166 _120712 s t _72725)) = True.
Proof. exact (@lem5765706 (term166 _120712 s t _72725)). Qed.
Lemma lem5765708 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (_72725 : _120712) : ((term76 _120712 t s _72725) = (term166 _120712 s t _72725)) = True.
Proof. exact (TRANS (@lem5765703 _120712 s t _72725) (@lem5765707 _120712 s t _72725)). Qed.
Lemma lem5765709 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (_72725 : _120712) : True = ((term76 _120712 t s _72725) = (term166 _120712 s t _72725)).
Proof. exact (SYM (@lem5765708 _120712 s t _72725)). Qed.
Lemma lem5765710 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (_72725 : _120712) : (term76 _120712 t s _72725) = (term166 _120712 s t _72725).
Proof. exact (EQ_MP (@lem5765709 _120712 s t _72725) (@lem0)). Qed.
Lemma lem5765711 {_120712 : Type'} (_72725 : _120712) (t : _120712 -> Prop) (s : _120712 -> Prop) (h1 : term21 _120712 t s) : term166 _120712 s t _72725.
Proof. exact (EQ_MP (@lem5765710 _120712 s t _72725) (@lem5765590 _120712 _72725 t s h1)). Qed.
Lemma lem5765713 (b : Prop) (a : Prop) : (a \/ b) = (term169 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5765714 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) (_72725 : _120712) : (term166 _120712 s t _72725) = (term170 _120712 t s _72725).
Proof. exact (@lem5765713 (term34 _120712 t _72725) (s _72725)). Qed.
Lemma lem5765716 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5765717 {_120712 : Type'} (t : _120712 -> Prop) (_72725 : _120712) : (term79 _120712 t _72725) = (t _72725).
Proof. exact (@lem5765716 (t _72725)). Qed.
Lemma lem5765718 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5765719 {_120712 : Type'} (t : _120712 -> Prop) (_72725 : _120712) : (term171 _120712 t _72725) = (term16 _120712 t _72725).
Proof. exact (MK_COMB (@lem5765718) (@lem5765717 _120712 t _72725)). Qed.
Lemma lem5765720 {_120712 : Type'} (s : _120712 -> Prop) (_72725 : _120712) : (s _72725) = (s _72725).
Proof. exact (eq_refl (s _72725)). Qed.
Lemma lem5765721 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) (_72725 : _120712) : (term170 _120712 t s _72725) = (term18 _120712 t s _72725).
Proof. exact (MK_COMB (@lem5765719 _120712 t _72725) (@lem5765720 _120712 s _72725)). Qed.
Lemma lem5765722 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) (_72725 : _120712) : (term166 _120712 s t _72725) = (term18 _120712 t s _72725).
Proof. exact (TRANS (@lem5765714 _120712 t s _72725) (@lem5765721 _120712 t s _72725)). Qed.
Lemma lem5765725 {_120712 : Type'} (_72725 : _120712) (t : _120712 -> Prop) (s : _120712 -> Prop) (h1 : term21 _120712 t s) : term18 _120712 t s _72725.
Proof. exact (EQ_MP (@lem5765722 _120712 t s _72725) (@lem5765711 _120712 _72725 t s h1)). Qed.
Lemma lem5765726 {_120712 : Type'} (_72725 : _120712) (t : _120712 -> Prop) (s : _120712 -> Prop) (h1 : term21 _120712 t s) : term18 _120712 t s _72725.
Proof. exact (@lem5765725 _120712 _72725 t s h1). Qed.
Lemma lem5765727 {_120712 : Type'} (x : _120712) (t : _120712 -> Prop) (s : _120712 -> Prop) (h1 : term21 _120712 t s) : term18 _120712 t s x.
Proof. exact (@lem5765726 _120712 x t s h1). Qed.
Lemma lem5765730 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : t x) : s x.
Proof. exact (@lem5765727 _120712 x t s h1 (@lem5765682 _120712 t x h2)). Qed.
Lemma lem5765731 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : t x) : term162 _120712 s x.
Proof. exact (fun h0 : term34 _120712 s x => @lem5765730 _120712 s t x h1 h2). Qed.
Lemma lem5765733 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5765734 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) : (term162 _120712 s x) = (s x).
Proof. exact (@lem5765733 (s x)). Qed.
Lemma lem5765735 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : t x) : s x.
Proof. exact (EQ_MP (@lem5765734 _120712 s x) (@lem5765731 _120712 s t x h1 h2)). Qed.
Lemma lem5765738 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5765740 {_120712 : Type'} (s : _120712 -> Prop) (x : _120712) : (term34 _120712 s x) = (term164 _120712 s x).
Proof. exact (@lem5765738 (s x)). Qed.
Lemma lem5765743 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term88 _120712 s t x) : term164 _120712 s x.
Proof. exact (EQ_MP (@lem5765740 _120712 s x) (@lem5765592 _120712 s t x h1)). Qed.
Lemma lem5765746 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : t x) (h3 : term88 _120712 s t x) : False.
Proof. exact (@lem5765743 _120712 s t x h3 (@lem5765735 _120712 s t x h1 h2)). Qed.
Lemma lem5765747 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : t x) (h3 : term88 _120712 s t x) : term165.
Proof. exact (fun h0 : ~ False => @lem5765746 _120712 s t x h1 h2 h3). Qed.
Lemma lem5765749 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5765750 : term165 = False.
Proof. exact (@lem5765749 False). Qed.
Lemma lem5765751 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : t x) (h3 : term88 _120712 s t x) : False.
Proof. exact (EQ_MP (@lem5765750) (@lem5765747 _120712 s t x h1 h2 h3)). Qed.
Lemma lem5765753 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term49 _120712 s t x) : t x.
Proof. exact (proj2 (@lem5765394 _120712 s t x h1)). Qed.
Lemma lem5765754 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term49 _120712 s t x) : term162 _120712 t x.
Proof. exact (fun h0 : term34 _120712 t x => @lem5765753 _120712 s t x h1). Qed.
Lemma lem5765756 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5765757 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) : (term162 _120712 t x) = (t x).
Proof. exact (@lem5765756 (t x)). Qed.
Lemma lem5765758 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term49 _120712 s t x) : t x.
Proof. exact (EQ_MP (@lem5765757 _120712 t x) (@lem5765754 _120712 s t x h1)). Qed.
Lemma lem5765761 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5765763 {_120712 : Type'} (t : _120712 -> Prop) (x : _120712) : (term34 _120712 t x) = (term164 _120712 t x).
Proof. exact (@lem5765761 (t x)). Qed.
Lemma lem5765766 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term49 _120712 s t x) : term164 _120712 t x.
Proof. exact (EQ_MP (@lem5765763 _120712 t x) (@lem5765606 _120712 s t x h1)). Qed.
Lemma lem5765769 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term49 _120712 s t x) : False.
Proof. exact (@lem5765766 _120712 s t x h1 (@lem5765758 _120712 s t x h1)). Qed.
Lemma lem5765770 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term49 _120712 s t x) : term165.
Proof. exact (fun h0 : ~ False => @lem5765769 _120712 s t x h1). Qed.
Lemma lem5765772 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5765773 : term165 = False.
Proof. exact (@lem5765772 False). Qed.
Lemma lem5765774 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term49 _120712 s t x) : False.
Proof. exact (EQ_MP (@lem5765773) (@lem5765770 _120712 s t x h1)). Qed.
Lemma lem5765775 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : t x) (h3 : term88 _120712 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem5765751 _120712 s t x h1 h2 h3) (fun h4 : False => @lem5765594 _120712 t x h2)). Qed.
Lemma lem5765776 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : t x) (h3 : term88 _120712 s t x) : False.
Proof. exact (EQ_MP (@lem5765775 _120712 s t x h1 h2 h3) (@lem5765594 _120712 t x h2)). Qed.
Lemma lem5765777 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : t x) (h2 : term90 _120712 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem5765652 _120712 s t x h1 h2) (fun h3 : False => @lem5765572 _120712 t x h1)). Qed.
Lemma lem5765778 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : t x) (h2 : term90 _120712 s t x) : False.
Proof. exact (EQ_MP (@lem5765777 _120712 s t x h1 h2) (@lem5765572 _120712 t x h1)). Qed.
Lemma lem5765779 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term34 _120712 s x) (h2 : term90 _120712 s t x) : (term34 _120712 s x) = False.
Proof. exact (prop_ext (fun h3 : term34 _120712 s x => @lem5765629 _120712 s t x h1 h2) (fun h3 : False => @lem5765560 _120712 s x h1)). Qed.
Lemma lem5765780 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term34 _120712 s x) (h2 : term90 _120712 s t x) : False.
Proof. exact (EQ_MP (@lem5765779 _120712 s t x h1 h2) (@lem5765560 _120712 s x h1)). Qed.
Lemma lem5765781 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : t x) (h3 : term88 _120712 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem5765776 _120712 s t x h1 h2 h3) (fun h4 : False => @lem5765508 _120712 t x h2)). Qed.
Lemma lem5765782 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : t x) (h3 : term88 _120712 s t x) : False.
Proof. exact (EQ_MP (@lem5765781 _120712 s t x h1 h2 h3) (@lem5765508 _120712 t x h2)). Qed.
Lemma lem5765783 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : t x) (h2 : term90 _120712 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem5765778 _120712 s t x h1 h2) (fun h3 : False => @lem5765462 _120712 t x h1)). Qed.
Lemma lem5765784 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : t x) (h2 : term90 _120712 s t x) : False.
Proof. exact (EQ_MP (@lem5765783 _120712 s t x h1 h2) (@lem5765462 _120712 t x h1)). Qed.
Lemma lem5765785 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term34 _120712 s x) (h2 : term90 _120712 s t x) : (term34 _120712 s x) = False.
Proof. exact (prop_ext (fun h3 : term34 _120712 s x => @lem5765780 _120712 s t x h1 h2) (fun h3 : False => @lem5765437 _120712 s x h1)). Qed.
Lemma lem5765786 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term34 _120712 s x) (h2 : term90 _120712 s t x) : False.
Proof. exact (EQ_MP (@lem5765785 _120712 s t x h1 h2) (@lem5765437 _120712 s x h1)). Qed.
Lemma lem5765787 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : t x) (h3 : term88 _120712 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem5765782 _120712 s t x h1 h2 h3) (fun h4 : False => @lem5765508 _120712 t x h2)). Qed.
Lemma lem5765788 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : t x) (h3 : term88 _120712 s t x) : False.
Proof. exact (EQ_MP (@lem5765787 _120712 s t x h1 h2 h3) (@lem5765508 _120712 t x h2)). Qed.
Lemma lem5765789 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : t x) (h2 : term90 _120712 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem5765784 _120712 s t x h1 h2) (fun h3 : False => @lem5765462 _120712 t x h1)). Qed.
Lemma lem5765790 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : t x) (h2 : term90 _120712 s t x) : False.
Proof. exact (EQ_MP (@lem5765789 _120712 s t x h1 h2) (@lem5765462 _120712 t x h1)). Qed.
Lemma lem5765791 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term34 _120712 s x) (h2 : term90 _120712 s t x) : (term34 _120712 s x) = False.
Proof. exact (prop_ext (fun h3 : term34 _120712 s x => @lem5765786 _120712 s t x h1 h2) (fun h3 : False => @lem5765437 _120712 s x h1)). Qed.
Lemma lem5765792 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term34 _120712 s x) (h2 : term90 _120712 s t x) : False.
Proof. exact (EQ_MP (@lem5765791 _120712 s t x h1 h2) (@lem5765437 _120712 s x h1)). Qed.
Lemma lem5765793 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : term88 _120712 s t x) : False.
Proof. exact (or_elim (@lem5765403 _120712 s t x h2) (fun h0 : term35 _120712 s t x => @lem5765675 _120712 s t x h2 h0) (fun h0 : t x => @lem5765788 _120712 s t x h1 h0 h2)). Qed.
Lemma lem5765794 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term90 _120712 s t x) : False.
Proof. exact (or_elim (@lem5765400 _120712 s t x h1) (fun h0 : term34 _120712 s x => @lem5765792 _120712 s t x h0 h1) (fun h0 : t x => @lem5765790 _120712 s t x h0 h1)). Qed.
Lemma lem5765795 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : term94 _120712 s t x) : False.
Proof. exact (or_elim (@lem5765393 _120712 s t x h2) (fun h0 : term90 _120712 s t x => @lem5765794 _120712 s t x h0) (fun h0 : term88 _120712 s t x => @lem5765793 _120712 s t x h1 h0)). Qed.
Lemma lem5765796 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : term157 _120712 s t x) : False.
Proof. exact (or_elim (@lem5765392 _120712 s t x h2) (fun h0 : term94 _120712 s t x => @lem5765795 _120712 s t x h1 h0) (fun h0 : term49 _120712 s t x => @lem5765774 _120712 s t x h0)). Qed.
Lemma lem5765797 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : term157 _120712 s t x) : (term157 _120712 s t x) = False.
Proof. exact (prop_ext (fun h3 : term157 _120712 s t x => @lem5765796 _120712 s t x h1 h2) (fun h3 : False => @lem5765392 _120712 s t x h2)). Qed.
Lemma lem5765798 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (x : _120712) (h1 : term21 _120712 t s) (h2 : term157 _120712 s t x) : False.
Proof. exact (EQ_MP (@lem5765797 _120712 s t x h1 h2) (@lem5765392 _120712 s t x h2)). Qed.
Lemma lem5765799 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term21 _120712 t s) (h2 : term75 _120712 s t) : False.
Proof. exact (ex_elim (@lem5765302 _120712 s t h2) (fun x : _120712 => fun h0 : term159 _120712 s t x => @lem5765798 _120712 s t x h1 h0)). Qed.
Lemma lem5765800 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term21 _120712 t s) (h2 : term75 _120712 s t) : (term75 _120712 s t) = False.
Proof. exact (prop_ext (fun h3 : term75 _120712 s t => @lem5765799 _120712 s t h1 h2) (fun h3 : False => @lem5764981 _120712 s t h2)). Qed.
Lemma lem5765801 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term21 _120712 t s) (h2 : term75 _120712 s t) : False.
Proof. exact (EQ_MP (@lem5765800 _120712 s t h1 h2) (@lem5764981 _120712 s t h2)). Qed.
Lemma lem5765802 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) (h1 : term21 _120712 t s) : term74 _120712 s t.
Proof. exact (fun h0 : term75 _120712 s t => @lem5765801 _120712 s t h1 h0). Qed.
Lemma lem5765803 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) (h1 : term21 _120712 t s) : term56 _120712 s t.
Proof. exact (EQ_MP (@lem5764980 _120712 s t) (@lem5765802 _120712 t s h1)). Qed.
Lemma lem5765804 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : term57 _120712 s t.
Proof. exact (fun h0 : term21 _120712 t s => @lem5765803 _120712 t s h0). Qed.
Lemma lem5765809 {_120712 : Type'} (t : _120712 -> Prop) : term69 _120712 t.
Proof. exact (fun s : _120712 -> Prop => @lem5765804 _120712 s t). Qed.
Lemma lem5765814 {_120712 : Type'} : term73 _120712.
Proof. exact (fun t : _120712 -> Prop => @lem5765809 _120712 t). Qed.
Lemma lem5765815 {_120712 : Type'} : term72 _120712.
Proof. exact (EQ_MP (@lem5764975 _120712) (@lem5765814 _120712)). Qed.
Lemma lem5765816 {_120712 : Type'} (t : _120712 -> Prop) : term172 _120712 t.
Proof. exact (@lem5765815 _120712 t). Qed.
Lemma lem5765817 {_120712 : Type'} (t : _120712 -> Prop) : (term172 _120712 t) = (term68 _120712 t).
Proof. exact (eq_refl (term172 _120712 t)). Qed.
Lemma lem5765818 {_120712 : Type'} (t : _120712 -> Prop) : term68 _120712 t.
Proof. exact (EQ_MP (@lem5765817 _120712 t) (@lem5765816 _120712 t)). Qed.
Lemma lem5765819 {_120712 : Type'} (t : _120712 -> Prop) (s : _120712 -> Prop) : term173 _120712 t s.
Proof. exact (@lem5765818 _120712 t s). Qed.
Lemma lem5765820 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : (term173 _120712 t s) = (term59 _120712 s t).
Proof. exact (eq_refl (term173 _120712 t s)). Qed.
Lemma lem5765821 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : term59 _120712 s t.
Proof. exact (EQ_MP (@lem5765820 _120712 s t) (@lem5765819 _120712 t s)). Qed.
Lemma lem5765823 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : term59 _120712 s t.
Proof. exact (@lem5764814 _120712 s t (@lem5765821 _120712 s t)). Qed.
Lemma lem5765824 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term60 _120712 s t) : False.
Proof. exact (@lem5765823 _120712 s t (@lem5764798 _120712 s t h1)). Qed.
Lemma lem5765825 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term60 _120712 s t) : (term60 _120712 s t) = False.
Proof. exact (prop_ext (fun h2 : term60 _120712 s t => @lem5765824 _120712 s t h1) (fun h2 : False => @lem5764798 _120712 s t h1)). Qed.
Lemma lem5765826 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) (h1 : term60 _120712 s t) : False.
Proof. exact (EQ_MP (@lem5765825 _120712 s t h1) (@lem5764798 _120712 s t h1)). Qed.
Lemma lem5765827 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : term59 _120712 s t.
Proof. exact (fun h0 : term60 _120712 s t => @lem5765826 _120712 s t h0). Qed.
Lemma lem5765828 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : term57 _120712 s t.
Proof. exact (EQ_MP (@lem5764797 _120712 s t) (@lem5765827 _120712 s t)). Qed.
Lemma lem5765829 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : term14 _120712 s t.
Proof. exact (EQ_MP (@lem5764793 _120712 s t) (@lem5765828 _120712 s t)). Qed.
Lemma lem5765830 {_120712 : Type'} (s : _120712 -> Prop) (t : _120712 -> Prop) : term13 _120712 s t.
Proof. exact (EQ_MP (@lem5764629 _120712 s t) (@lem5765829 _120712 s t)). Qed.
Lemma lem5765831 (t1 : Prop) : term174 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5765832 (t1 : Prop) : (term174 t1) = (term175 t1).
Proof. exact (eq_refl (term174 t1)). Qed.
Lemma lem5765833 (t1 : Prop) : term175 t1.
Proof. exact (EQ_MP (@lem5765832 t1) (@lem5765831 t1)). Qed.
Lemma lem5765834 (t1 : Prop) (t2 : Prop) : term176 t1 t2.
Proof. exact (@lem5765833 t1 t2). Qed.
Lemma lem5765835 (t1 : Prop) (t2 : Prop) : (term176 t1 t2) = (term177 t1 t2).
Proof. exact (eq_refl (term176 t1 t2)). Qed.
Lemma lem5765836 (t1 : Prop) (t2 : Prop) : term177 t1 t2.
Proof. exact (EQ_MP (@lem5765835 t1 t2) (@lem5765834 t1 t2)). Qed.
Lemma lem5765837 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term178 t1 t2 t3.
Proof. exact (@lem5765836 t1 t2 t3). Qed.
Lemma lem5765838 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term178 t1 t2 t3) = ((term179 t1 t2 t3) = (term180 t1 t2 t3)).
Proof. exact (eq_refl (term178 t1 t2 t3)). Qed.
Lemma lem5765839 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term179 t1 t2 t3) = (term180 t1 t2 t3).
Proof. exact (EQ_MP (@lem5765838 t1 t2 t3) (@lem5765837 t1 t2 t3)). Qed.
Lemma lem5765840 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term180 t1 t2 t3) = (term179 t1 t2 t3).
Proof. exact (SYM (@lem5765839 t1 t2 t3)). Qed.
Lemma lem5765841 {_120712 : Type'} (s : _120712 -> Prop) : term181 _120712 s.
Proof. exact (fun t : _120712 -> Prop => @lem5765830 _120712 s t). Qed.
Lemma lem5765842 {_120712 : Type'} : term182 _120712.
Proof. exact (fun s : _120712 -> Prop => @lem5765841 _120712 s). Qed.
Lemma lem5765844 (p : Prop) : p = (term58 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5765845 {_120745 _120749 : Type'} : (term183 _120745 _120749) = (term184 _120745 _120749).
Proof. exact (@lem5765844 (term183 _120745 _120749)). Qed.
Lemma lem5765846 {_120745 _120749 : Type'} : (term184 _120745 _120749) = (term183 _120745 _120749).
Proof. exact (SYM (@lem5765845 _120745 _120749)). Qed.
Lemma lem5765847 {_120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term185 _120745 _120749.
Proof. exact (h1). Qed.
Lemma lem5765848 {_120745 : Type'} : term182 _120745.
Proof. exact (@lem5765842 _120745). Qed.
Lemma lem5765850 {_120592 _120749 : Type'} : term186 _120592 _120749.
Proof. exact (@lem5764203 _120592 _120749). Qed.
Lemma lem5765851 {_120607 _120745 : Type'} : term187 _120607 _120745.
Proof. exact (@lem5764203 _120745 _120607). Qed.
Lemma lem5765854 {_120592 _120745 : Type'} : term188 _120592 _120745.
Proof. exact (@lem5764203 _120592 (_120745 -> Prop)). Qed.
Lemma lem5765855 {_120745 _120749 : Type'} : term186 _120745 _120749.
Proof. exact (@lem5764203 _120745 _120749). Qed.
Lemma lem5765857 {_120745 : Type'} : term189 _120745.
Proof. exact (@lem3606772 _120745). Qed.
Lemma lem5765858 {_120592 : Type'} : term189 _120592.
Proof. exact (@lem3606772 _120592). Qed.
Lemma lem5765861 {_120745 : Type'} : term190 _120745.
Proof. exact (@lem3599924 _120745). Qed.
Lemma lem5765862 {_120592 : Type'} : term190 _120592.
Proof. exact (@lem3599924 _120592). Qed.
Lemma lem5765864 {_120745 : Type'} : term191 _120745.
Proof. exact (@lem3270702 _120745). Qed.
Lemma lem5765865 {_120592 : Type'} : term191 _120592.
Proof. exact (@lem3270702 _120592). Qed.
Lemma lem5765869 {_120592 _120607 _120745 _120749 : Type'} (h1 : term192 _120592 _120607 _120745 _120749) : term192 _120592 _120607 _120745 _120749.
Proof. exact (h1). Qed.
Lemma lem5765870 {_120592 _120607 _120745 _120749 : Type'} : term193 _120592 _120607 _120745 _120749.
Proof. exact (fun h0 : term192 _120592 _120607 _120745 _120749 => @lem5765869 _120592 _120607 _120745 _120749 h0). Qed.
Lemma lem5765871 {_120592 _120607 _120745 _120749 : Type'} (h1 : term193 _120592 _120607 _120745 _120749) : term193 _120592 _120607 _120745 _120749.
Proof. exact (h1). Qed.
Lemma lem5765872 {_120592 _120607 _120745 _120749 : Type'} (h1 : term192 _120592 _120607 _120745 _120749) : term192 _120592 _120607 _120745 _120749.
Proof. exact (h1). Qed.
Lemma lem5765873 {_120592 _120607 _120745 _120749 : Type'} (h1 : term192 _120592 _120607 _120745 _120749) (h2 : term193 _120592 _120607 _120745 _120749) : term192 _120592 _120607 _120745 _120749.
Proof. exact (@lem5765871 _120592 _120607 _120745 _120749 h2 (@lem5765872 _120592 _120607 _120745 _120749 h1)). Qed.
Lemma lem5765874 {_120592 _120607 _120745 _120749 : Type'} (h1 : term192 _120592 _120607 _120745 _120749) : term194 _120592 _120607 _120745 _120749.
Proof. exact (fun h0 : term193 _120592 _120607 _120745 _120749 => @lem5765873 _120592 _120607 _120745 _120749 h1 h0). Qed.
Lemma lem5765875 {_120592 _120607 _120745 _120749 : Type'} (h1 : term193 _120592 _120607 _120745 _120749) : term193 _120592 _120607 _120745 _120749.
Proof. exact (h1). Qed.
Lemma lem5765876 {_120592 _120607 _120745 _120749 : Type'} (h1 : term192 _120592 _120607 _120745 _120749) (h2 : term193 _120592 _120607 _120745 _120749) : term192 _120592 _120607 _120745 _120749.
Proof. exact (@lem5765874 _120592 _120607 _120745 _120749 h1 (@lem5765875 _120592 _120607 _120745 _120749 h2)). Qed.
Lemma lem5765877 {_120592 _120607 _120745 _120749 : Type'} (h1 : term193 _120592 _120607 _120745 _120749) : term193 _120592 _120607 _120745 _120749.
Proof. exact (fun h0 : term192 _120592 _120607 _120745 _120749 => @lem5765876 _120592 _120607 _120745 _120749 h0 h1). Qed.
Lemma lem5765878 {_120592 _120607 _120745 _120749 : Type'} : term195 _120592 _120607 _120745 _120749.
Proof. exact (fun h0 : term193 _120592 _120607 _120745 _120749 => @lem5765877 _120592 _120607 _120745 _120749 h0). Qed.
Lemma lem5765881 {_120592 _120607 _120745 _120749 : Type'} : term193 _120592 _120607 _120745 _120749.
Proof. exact (@lem5765878 _120592 _120607 _120745 _120749 (@lem5765870 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5765882 {_120592 _120607 _120745 _120749 : Type'} : term193 _120592 _120607 _120745 _120749.
Proof. exact (@lem5765881 _120592 _120607 _120745 _120749). Qed.
Lemma lem5766084 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5766085 {_120745 : Type'} : (term196 _120745) = (term197 _120745).
Proof. exact (@lem5766084 (term182 _120745)). Qed.
Lemma lem5766098 {_120592 _120745 : Type'} : (term198 _120592 _120745) = (term198 _120592 _120745).
Proof. exact (eq_refl (term198 _120592 _120745)). Qed.
Lemma lem5766099 {_120592 _120745 : Type'} : (term199 _120592 _120745) = (term200 _120592 _120745).
Proof. exact (MK_COMB (@lem5766098 _120592 _120745) (@lem5766085 _120745)). Qed.
Lemma lem5766102 {_120745 _120749 : Type'} : (term201 _120745 _120749) = (term201 _120745 _120749).
Proof. exact (eq_refl (term201 _120745 _120749)). Qed.
Lemma lem5766103 {_120592 _120745 _120749 : Type'} : (term202 _120592 _120745 _120749) = (term203 _120592 _120745 _120749).
Proof. exact (MK_COMB (@lem5766102 _120745 _120749) (@lem5766099 _120592 _120745)). Qed.
Lemma lem5766106 {_120592 _120749 : Type'} : (term201 _120592 _120749) = (term201 _120592 _120749).
Proof. exact (eq_refl (term201 _120592 _120749)). Qed.
Lemma lem5766107 {_120592 _120745 _120749 : Type'} : (term204 _120592 _120745 _120749) = (term205 _120592 _120745 _120749).
Proof. exact (MK_COMB (@lem5766106 _120592 _120749) (@lem5766103 _120592 _120745 _120749)). Qed.
Lemma lem5766110 {_120607 _120745 : Type'} : (term206 _120607 _120745) = (term206 _120607 _120745).
Proof. exact (eq_refl (term206 _120607 _120745)). Qed.
Lemma lem5766111 {_120592 _120607 _120745 _120749 : Type'} : (term207 _120592 _120607 _120745 _120749) = (term208 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766110 _120607 _120745) (@lem5766107 _120592 _120745 _120749)). Qed.
Lemma lem5766114 {_120745 : Type'} : (term209 _120745) = (term209 _120745).
Proof. exact (eq_refl (term209 _120745)). Qed.
Lemma lem5766115 {_120592 _120607 _120745 _120749 : Type'} : (term210 _120592 _120607 _120745 _120749) = (term211 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766114 _120745) (@lem5766111 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766118 {_120592 : Type'} : (term209 _120592) = (term209 _120592).
Proof. exact (eq_refl (term209 _120592)). Qed.
Lemma lem5766119 {_120592 _120607 _120745 _120749 : Type'} : (term212 _120592 _120607 _120745 _120749) = (term213 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766118 _120592) (@lem5766115 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766122 {_120745 : Type'} : (term214 _120745) = (term214 _120745).
Proof. exact (eq_refl (term214 _120745)). Qed.
Lemma lem5766123 {_120592 _120607 _120745 _120749 : Type'} : (term215 _120592 _120607 _120745 _120749) = (term216 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766122 _120745) (@lem5766119 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766126 {_120592 : Type'} : (term214 _120592) = (term214 _120592).
Proof. exact (eq_refl (term214 _120592)). Qed.
Lemma lem5766127 {_120592 _120607 _120745 _120749 : Type'} : (term217 _120592 _120607 _120745 _120749) = (term218 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766126 _120592) (@lem5766123 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766130 {_120745 : Type'} : (term219 _120745) = (term219 _120745).
Proof. exact (eq_refl (term219 _120745)). Qed.
Lemma lem5766131 {_120592 _120607 _120745 _120749 : Type'} : (term220 _120592 _120607 _120745 _120749) = (term221 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766130 _120745) (@lem5766127 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766134 {_120592 : Type'} : (term219 _120592) = (term219 _120592).
Proof. exact (eq_refl (term219 _120592)). Qed.
Lemma lem5766135 {_120592 _120607 _120745 _120749 : Type'} : (term222 _120592 _120607 _120745 _120749) = (term223 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766134 _120592) (@lem5766131 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766138 {_120745 _120749 : Type'} : (term224 _120745 _120749) = (term224 _120745 _120749).
Proof. exact (eq_refl (term224 _120745 _120749)). Qed.
Lemma lem5766145 {_120592 _120607 _120745 _120749 : Type'} : (term192 _120592 _120607 _120745 _120749) = (term225 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766138 _120745 _120749) (@lem5766135 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766154 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term13 _120745 s t) = (term13 _120745 s t).
Proof. exact (eq_refl (term13 _120745 s t)). Qed.
Lemma lem5766155 {_120745 : Type'} (s : _120745 -> Prop) : (term226 _120745 s) = (term226 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5766154 _120745 s t)). Qed.
Lemma lem5766156 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766157 {_120745 : Type'} (s : _120745 -> Prop) : (term181 _120745 s) = (term181 _120745 s).
Proof. exact (MK_COMB (@lem5766156 _120745) (@lem5766155 _120745 s)). Qed.
Lemma lem5766158 {_120745 : Type'} : (term227 _120745) = (term227 _120745).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5766157 _120745 s)). Qed.
Lemma lem5766159 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766160 {_120745 : Type'} : (term182 _120745) = (term182 _120745).
Proof. exact (MK_COMB (@lem5766159 _120745) (@lem5766158 _120745)). Qed.
Lemma lem5766161 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5766162 {_120745 : Type'} : (term197 _120745) = (term197 _120745).
Proof. exact (MK_COMB (@lem5766161) (@lem5766160 _120745)). Qed.
Lemma lem5766175 {_120592 _120745 : Type'} (s : _120592 -> Prop) (op : type636 _120745) (t : _120592 -> Prop) (f : type1413 _120592 _120745) : (term228 _120592 _120745 s op t f) = (term228 _120592 _120745 s op t f).
Proof. exact (eq_refl (term228 _120592 _120745 s op t f)). Qed.
Lemma lem5766176 {_120592 _120745 : Type'} (s : _120592 -> Prop) (op : type636 _120745) (f : type1413 _120592 _120745) : (term229 _120592 _120745 s op f) = (term229 _120592 _120745 s op f).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem5766175 _120592 _120745 s op t f)). Qed.
Lemma lem5766177 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5766178 {_120592 _120745 : Type'} (s : _120592 -> Prop) (op : type636 _120745) (f : type1413 _120592 _120745) : (term230 _120592 _120745 s op f) = (term230 _120592 _120745 s op f).
Proof. exact (MK_COMB (@lem5766177 _120592) (@lem5766176 _120592 _120745 s op f)). Qed.
Lemma lem5766179 {_120592 _120745 : Type'} (op : type636 _120745) (f : type1413 _120592 _120745) : (term231 _120592 _120745 op f) = (term231 _120592 _120745 op f).
Proof. exact (fun_ext (fun s : _120592 -> Prop => @lem5766178 _120592 _120745 s op f)). Qed.
Lemma lem5766180 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5766181 {_120592 _120745 : Type'} (op : type636 _120745) (f : type1413 _120592 _120745) : (term232 _120592 _120745 op f) = (term232 _120592 _120745 op f).
Proof. exact (MK_COMB (@lem5766180 _120592) (@lem5766179 _120592 _120745 op f)). Qed.
Lemma lem5766182 {_120592 _120745 : Type'} (op : type636 _120745) : (term233 _120592 _120745 op) = (term233 _120592 _120745 op).
Proof. exact (fun_ext (fun f : type1413 _120592 _120745 => @lem5766181 _120592 _120745 op f)). Qed.
Lemma lem5766183 {_120592 _120745 : Type'} : (@all (_120592 -> _120745 -> Prop)) = (@all (_120592 -> _120745 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> _120745 -> Prop))). Qed.
Lemma lem5766184 {_120592 _120745 : Type'} (op : type636 _120745) : (term234 _120592 _120745 op) = (term234 _120592 _120745 op).
Proof. exact (MK_COMB (@lem5766183 _120592 _120745) (@lem5766182 _120592 _120745 op)). Qed.
Lemma lem5766187 {_120745 : Type'} (op : type636 _120745) : (term235 _120745 op) = (term235 _120745 op).
Proof. exact (eq_refl (term235 _120745 op)). Qed.
Lemma lem5766188 {_120592 _120745 : Type'} (op : type636 _120745) : (term236 _120592 _120745 op) = (term236 _120592 _120745 op).
Proof. exact (MK_COMB (@lem5766187 _120745 op) (@lem5766184 _120592 _120745 op)). Qed.
Lemma lem5766189 {_120592 _120745 : Type'} : (term237 _120592 _120745) = (term237 _120592 _120745).
Proof. exact (fun_ext (fun op : type636 _120745 => @lem5766188 _120592 _120745 op)). Qed.
Lemma lem5766190 {_120745 : Type'} : (@all ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop)) = (@all ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop)).
Proof. exact (eq_refl (@all ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop))). Qed.
Lemma lem5766191 {_120592 _120745 : Type'} : (term188 _120592 _120745) = (term188 _120592 _120745).
Proof. exact (MK_COMB (@lem5766190 _120745) (@lem5766189 _120592 _120745)). Qed.
Lemma lem5766192 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5766193 {_120592 _120745 : Type'} : (term198 _120592 _120745) = (term198 _120592 _120745).
Proof. exact (MK_COMB (@lem5766192) (@lem5766191 _120592 _120745)). Qed.
Lemma lem5766194 {_120592 _120745 : Type'} : (term200 _120592 _120745) = (term200 _120592 _120745).
Proof. exact (MK_COMB (@lem5766193 _120592 _120745) (@lem5766162 _120745)). Qed.
Lemma lem5766207 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term238 _120745 _120749 s op t f) = (term238 _120745 _120749 s op t f).
Proof. exact (eq_refl (term238 _120745 _120749 s op t f)). Qed.
Lemma lem5766208 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term239 _120745 _120749 s op f) = (term239 _120745 _120749 s op f).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5766207 _120745 _120749 s op t f)). Qed.
Lemma lem5766209 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766210 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term240 _120745 _120749 s op f) = (term240 _120745 _120749 s op f).
Proof. exact (MK_COMB (@lem5766209 _120745) (@lem5766208 _120745 _120749 s op f)). Qed.
Lemma lem5766211 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term241 _120745 _120749 op f) = (term241 _120745 _120749 op f).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5766210 _120745 _120749 s op f)). Qed.
Lemma lem5766212 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766213 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term242 _120745 _120749 op f) = (term242 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5766212 _120745) (@lem5766211 _120745 _120749 op f)). Qed.
Lemma lem5766214 {_120745 _120749 : Type'} (op : type1400 _120749) : (term243 _120745 _120749 op) = (term243 _120745 _120749 op).
Proof. exact (fun_ext (fun f : _120745 -> _120749 => @lem5766213 _120745 _120749 op f)). Qed.
Lemma lem5766215 {_120745 _120749 : Type'} : (@all (_120745 -> _120749)) = (@all (_120745 -> _120749)).
Proof. exact (eq_refl (@all (_120745 -> _120749))). Qed.
Lemma lem5766216 {_120745 _120749 : Type'} (op : type1400 _120749) : (term244 _120745 _120749 op) = (term244 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5766215 _120745 _120749) (@lem5766214 _120745 _120749 op)). Qed.
Lemma lem5766219 {_120749 : Type'} (op : type1400 _120749) : (term245 _120749 op) = (term245 _120749 op).
Proof. exact (eq_refl (term245 _120749 op)). Qed.
Lemma lem5766220 {_120745 _120749 : Type'} (op : type1400 _120749) : (term246 _120745 _120749 op) = (term246 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5766219 _120749 op) (@lem5766216 _120745 _120749 op)). Qed.
Lemma lem5766221 {_120745 _120749 : Type'} : (term247 _120745 _120749) = (term247 _120745 _120749).
Proof. exact (fun_ext (fun op : type1400 _120749 => @lem5766220 _120745 _120749 op)). Qed.
Lemma lem5766222 {_120749 : Type'} : (@all (_120749 -> _120749 -> _120749)) = (@all (_120749 -> _120749 -> _120749)).
Proof. exact (eq_refl (@all (_120749 -> _120749 -> _120749))). Qed.
Lemma lem5766223 {_120745 _120749 : Type'} : (term186 _120745 _120749) = (term186 _120745 _120749).
Proof. exact (MK_COMB (@lem5766222 _120749) (@lem5766221 _120745 _120749)). Qed.
Lemma lem5766224 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5766225 {_120745 _120749 : Type'} : (term201 _120745 _120749) = (term201 _120745 _120749).
Proof. exact (MK_COMB (@lem5766224) (@lem5766223 _120745 _120749)). Qed.
Lemma lem5766226 {_120592 _120745 _120749 : Type'} : (term203 _120592 _120745 _120749) = (term203 _120592 _120745 _120749).
Proof. exact (MK_COMB (@lem5766225 _120745 _120749) (@lem5766194 _120592 _120745)). Qed.
Lemma lem5766239 {_120592 _120749 : Type'} (s : _120592 -> Prop) (op : type1400 _120749) (t : _120592 -> Prop) (f : _120592 -> _120749) : (term238 _120592 _120749 s op t f) = (term238 _120592 _120749 s op t f).
Proof. exact (eq_refl (term238 _120592 _120749 s op t f)). Qed.
Lemma lem5766240 {_120592 _120749 : Type'} (s : _120592 -> Prop) (op : type1400 _120749) (f : _120592 -> _120749) : (term239 _120592 _120749 s op f) = (term239 _120592 _120749 s op f).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem5766239 _120592 _120749 s op t f)). Qed.
Lemma lem5766241 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5766242 {_120592 _120749 : Type'} (s : _120592 -> Prop) (op : type1400 _120749) (f : _120592 -> _120749) : (term240 _120592 _120749 s op f) = (term240 _120592 _120749 s op f).
Proof. exact (MK_COMB (@lem5766241 _120592) (@lem5766240 _120592 _120749 s op f)). Qed.
Lemma lem5766243 {_120592 _120749 : Type'} (op : type1400 _120749) (f : _120592 -> _120749) : (term241 _120592 _120749 op f) = (term241 _120592 _120749 op f).
Proof. exact (fun_ext (fun s : _120592 -> Prop => @lem5766242 _120592 _120749 s op f)). Qed.
Lemma lem5766244 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5766245 {_120592 _120749 : Type'} (op : type1400 _120749) (f : _120592 -> _120749) : (term242 _120592 _120749 op f) = (term242 _120592 _120749 op f).
Proof. exact (MK_COMB (@lem5766244 _120592) (@lem5766243 _120592 _120749 op f)). Qed.
Lemma lem5766246 {_120592 _120749 : Type'} (op : type1400 _120749) : (term243 _120592 _120749 op) = (term243 _120592 _120749 op).
Proof. exact (fun_ext (fun f : _120592 -> _120749 => @lem5766245 _120592 _120749 op f)). Qed.
Lemma lem5766247 {_120592 _120749 : Type'} : (@all (_120592 -> _120749)) = (@all (_120592 -> _120749)).
Proof. exact (eq_refl (@all (_120592 -> _120749))). Qed.
Lemma lem5766248 {_120592 _120749 : Type'} (op : type1400 _120749) : (term244 _120592 _120749 op) = (term244 _120592 _120749 op).
Proof. exact (MK_COMB (@lem5766247 _120592 _120749) (@lem5766246 _120592 _120749 op)). Qed.
Lemma lem5766251 {_120749 : Type'} (op : type1400 _120749) : (term245 _120749 op) = (term245 _120749 op).
Proof. exact (eq_refl (term245 _120749 op)). Qed.
Lemma lem5766252 {_120592 _120749 : Type'} (op : type1400 _120749) : (term246 _120592 _120749 op) = (term246 _120592 _120749 op).
Proof. exact (MK_COMB (@lem5766251 _120749 op) (@lem5766248 _120592 _120749 op)). Qed.
Lemma lem5766253 {_120592 _120749 : Type'} : (term247 _120592 _120749) = (term247 _120592 _120749).
Proof. exact (fun_ext (fun op : type1400 _120749 => @lem5766252 _120592 _120749 op)). Qed.
Lemma lem5766254 {_120749 : Type'} : (@all (_120749 -> _120749 -> _120749)) = (@all (_120749 -> _120749 -> _120749)).
Proof. exact (eq_refl (@all (_120749 -> _120749 -> _120749))). Qed.
Lemma lem5766255 {_120592 _120749 : Type'} : (term186 _120592 _120749) = (term186 _120592 _120749).
Proof. exact (MK_COMB (@lem5766254 _120749) (@lem5766253 _120592 _120749)). Qed.
Lemma lem5766256 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5766257 {_120592 _120749 : Type'} : (term201 _120592 _120749) = (term201 _120592 _120749).
Proof. exact (MK_COMB (@lem5766256) (@lem5766255 _120592 _120749)). Qed.
Lemma lem5766258 {_120592 _120745 _120749 : Type'} : (term205 _120592 _120745 _120749) = (term205 _120592 _120745 _120749).
Proof. exact (MK_COMB (@lem5766257 _120592 _120749) (@lem5766226 _120592 _120745 _120749)). Qed.
Lemma lem5766271 {_120607 _120745 : Type'} (s : _120745 -> Prop) (op : type1400 _120607) (t : _120745 -> Prop) (f : _120745 -> _120607) : (term248 _120607 _120745 s op t f) = (term248 _120607 _120745 s op t f).
Proof. exact (eq_refl (term248 _120607 _120745 s op t f)). Qed.
Lemma lem5766272 {_120607 _120745 : Type'} (s : _120745 -> Prop) (op : type1400 _120607) (f : _120745 -> _120607) : (term249 _120607 _120745 s op f) = (term249 _120607 _120745 s op f).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5766271 _120607 _120745 s op t f)). Qed.
Lemma lem5766273 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766274 {_120607 _120745 : Type'} (s : _120745 -> Prop) (op : type1400 _120607) (f : _120745 -> _120607) : (term250 _120607 _120745 s op f) = (term250 _120607 _120745 s op f).
Proof. exact (MK_COMB (@lem5766273 _120745) (@lem5766272 _120607 _120745 s op f)). Qed.
Lemma lem5766275 {_120607 _120745 : Type'} (op : type1400 _120607) (f : _120745 -> _120607) : (term251 _120607 _120745 op f) = (term251 _120607 _120745 op f).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5766274 _120607 _120745 s op f)). Qed.
Lemma lem5766276 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766277 {_120607 _120745 : Type'} (op : type1400 _120607) (f : _120745 -> _120607) : (term252 _120607 _120745 op f) = (term252 _120607 _120745 op f).
Proof. exact (MK_COMB (@lem5766276 _120745) (@lem5766275 _120607 _120745 op f)). Qed.
Lemma lem5766278 {_120607 _120745 : Type'} (op : type1400 _120607) : (term253 _120607 _120745 op) = (term253 _120607 _120745 op).
Proof. exact (fun_ext (fun f : _120745 -> _120607 => @lem5766277 _120607 _120745 op f)). Qed.
Lemma lem5766279 {_120607 _120745 : Type'} : (@all (_120745 -> _120607)) = (@all (_120745 -> _120607)).
Proof. exact (eq_refl (@all (_120745 -> _120607))). Qed.
Lemma lem5766280 {_120607 _120745 : Type'} (op : type1400 _120607) : (term254 _120607 _120745 op) = (term254 _120607 _120745 op).
Proof. exact (MK_COMB (@lem5766279 _120607 _120745) (@lem5766278 _120607 _120745 op)). Qed.
Lemma lem5766283 {_120607 : Type'} (op : type1400 _120607) : (term245 _120607 op) = (term245 _120607 op).
Proof. exact (eq_refl (term245 _120607 op)). Qed.
Lemma lem5766284 {_120607 _120745 : Type'} (op : type1400 _120607) : (term255 _120607 _120745 op) = (term255 _120607 _120745 op).
Proof. exact (MK_COMB (@lem5766283 _120607 op) (@lem5766280 _120607 _120745 op)). Qed.
Lemma lem5766285 {_120607 _120745 : Type'} : (term256 _120607 _120745) = (term256 _120607 _120745).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5766284 _120607 _120745 op)). Qed.
Lemma lem5766286 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5766287 {_120607 _120745 : Type'} : (term187 _120607 _120745) = (term187 _120607 _120745).
Proof. exact (MK_COMB (@lem5766286 _120607) (@lem5766285 _120607 _120745)). Qed.
Lemma lem5766288 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5766289 {_120607 _120745 : Type'} : (term206 _120607 _120745) = (term206 _120607 _120745).
Proof. exact (MK_COMB (@lem5766288) (@lem5766287 _120607 _120745)). Qed.
Lemma lem5766290 {_120592 _120607 _120745 _120749 : Type'} : (term208 _120592 _120607 _120745 _120749) = (term208 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766289 _120607 _120745) (@lem5766258 _120592 _120745 _120749)). Qed.
Lemma lem5766299 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : ((term257 _120745 s t) = (term258 _120745 s t)) = ((term257 _120745 s t) = (term258 _120745 s t)).
Proof. exact (eq_refl ((term257 _120745 s t) = (term258 _120745 s t))). Qed.
Lemma lem5766300 {_120745 : Type'} (s : _120745 -> Prop) : (term259 _120745 s) = (term259 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5766299 _120745 s t)). Qed.
Lemma lem5766301 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766302 {_120745 : Type'} (s : _120745 -> Prop) : (term260 _120745 s) = (term260 _120745 s).
Proof. exact (MK_COMB (@lem5766301 _120745) (@lem5766300 _120745 s)). Qed.
Lemma lem5766303 {_120745 : Type'} : (term261 _120745) = (term261 _120745).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5766302 _120745 s)). Qed.
Lemma lem5766304 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766305 {_120745 : Type'} : (term189 _120745) = (term189 _120745).
Proof. exact (MK_COMB (@lem5766304 _120745) (@lem5766303 _120745)). Qed.
Lemma lem5766306 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5766307 {_120745 : Type'} : (term209 _120745) = (term209 _120745).
Proof. exact (MK_COMB (@lem5766306) (@lem5766305 _120745)). Qed.
Lemma lem5766308 {_120592 _120607 _120745 _120749 : Type'} : (term211 _120592 _120607 _120745 _120749) = (term211 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766307 _120745) (@lem5766290 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766317 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : ((term257 _120592 s t) = (term258 _120592 s t)) = ((term257 _120592 s t) = (term258 _120592 s t)).
Proof. exact (eq_refl ((term257 _120592 s t) = (term258 _120592 s t))). Qed.
Lemma lem5766318 {_120592 : Type'} (s : _120592 -> Prop) : (term259 _120592 s) = (term259 _120592 s).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem5766317 _120592 s t)). Qed.
Lemma lem5766319 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5766320 {_120592 : Type'} (s : _120592 -> Prop) : (term260 _120592 s) = (term260 _120592 s).
Proof. exact (MK_COMB (@lem5766319 _120592) (@lem5766318 _120592 s)). Qed.
Lemma lem5766321 {_120592 : Type'} : (term261 _120592) = (term261 _120592).
Proof. exact (fun_ext (fun s : _120592 -> Prop => @lem5766320 _120592 s)). Qed.
Lemma lem5766322 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5766323 {_120592 : Type'} : (term189 _120592) = (term189 _120592).
Proof. exact (MK_COMB (@lem5766322 _120592) (@lem5766321 _120592)). Qed.
Lemma lem5766324 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5766325 {_120592 : Type'} : (term209 _120592) = (term209 _120592).
Proof. exact (MK_COMB (@lem5766324) (@lem5766323 _120592)). Qed.
Lemma lem5766326 {_120592 _120607 _120745 _120749 : Type'} : (term213 _120592 _120607 _120745 _120749) = (term213 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766325 _120592) (@lem5766308 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766335 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term262 _120745 t s) = (term262 _120745 t s).
Proof. exact (eq_refl (term262 _120745 t s)). Qed.
Lemma lem5766336 {_120745 : Type'} (s : _120745 -> Prop) : (term263 _120745 s) = (term263 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5766335 _120745 t s)). Qed.
Lemma lem5766337 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766338 {_120745 : Type'} (s : _120745 -> Prop) : (term264 _120745 s) = (term264 _120745 s).
Proof. exact (MK_COMB (@lem5766337 _120745) (@lem5766336 _120745 s)). Qed.
Lemma lem5766339 {_120745 : Type'} : (term265 _120745) = (term265 _120745).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5766338 _120745 s)). Qed.
Lemma lem5766340 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766341 {_120745 : Type'} : (term190 _120745) = (term190 _120745).
Proof. exact (MK_COMB (@lem5766340 _120745) (@lem5766339 _120745)). Qed.
Lemma lem5766342 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5766343 {_120745 : Type'} : (term214 _120745) = (term214 _120745).
Proof. exact (MK_COMB (@lem5766342) (@lem5766341 _120745)). Qed.
Lemma lem5766344 {_120592 _120607 _120745 _120749 : Type'} : (term216 _120592 _120607 _120745 _120749) = (term216 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766343 _120745) (@lem5766326 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766353 {_120592 : Type'} (t : _120592 -> Prop) (s : _120592 -> Prop) : (term262 _120592 t s) = (term262 _120592 t s).
Proof. exact (eq_refl (term262 _120592 t s)). Qed.
Lemma lem5766354 {_120592 : Type'} (s : _120592 -> Prop) : (term263 _120592 s) = (term263 _120592 s).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem5766353 _120592 t s)). Qed.
Lemma lem5766355 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5766356 {_120592 : Type'} (s : _120592 -> Prop) : (term264 _120592 s) = (term264 _120592 s).
Proof. exact (MK_COMB (@lem5766355 _120592) (@lem5766354 _120592 s)). Qed.
Lemma lem5766357 {_120592 : Type'} : (term265 _120592) = (term265 _120592).
Proof. exact (fun_ext (fun s : _120592 -> Prop => @lem5766356 _120592 s)). Qed.
Lemma lem5766358 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5766359 {_120592 : Type'} : (term190 _120592) = (term190 _120592).
Proof. exact (MK_COMB (@lem5766358 _120592) (@lem5766357 _120592)). Qed.
Lemma lem5766360 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5766361 {_120592 : Type'} : (term214 _120592) = (term214 _120592).
Proof. exact (MK_COMB (@lem5766360) (@lem5766359 _120592)). Qed.
Lemma lem5766362 {_120592 _120607 _120745 _120749 : Type'} : (term218 _120592 _120607 _120745 _120749) = (term218 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766361 _120592) (@lem5766344 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766363 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term266 _120745 t s) = (term266 _120745 t s).
Proof. exact (eq_refl (term266 _120745 t s)). Qed.
Lemma lem5766364 {_120745 : Type'} (s : _120745 -> Prop) : (term267 _120745 s) = (term267 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5766363 _120745 t s)). Qed.
Lemma lem5766365 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766366 {_120745 : Type'} (s : _120745 -> Prop) : (term268 _120745 s) = (term268 _120745 s).
Proof. exact (MK_COMB (@lem5766365 _120745) (@lem5766364 _120745 s)). Qed.
Lemma lem5766367 {_120745 : Type'} : (term269 _120745) = (term269 _120745).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5766366 _120745 s)). Qed.
Lemma lem5766368 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766369 {_120745 : Type'} : (term191 _120745) = (term191 _120745).
Proof. exact (MK_COMB (@lem5766368 _120745) (@lem5766367 _120745)). Qed.
Lemma lem5766370 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5766371 {_120745 : Type'} : (term219 _120745) = (term219 _120745).
Proof. exact (MK_COMB (@lem5766370) (@lem5766369 _120745)). Qed.
Lemma lem5766372 {_120592 _120607 _120745 _120749 : Type'} : (term221 _120592 _120607 _120745 _120749) = (term221 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766371 _120745) (@lem5766362 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766373 {_120592 : Type'} (t : _120592 -> Prop) (s : _120592 -> Prop) : (term266 _120592 t s) = (term266 _120592 t s).
Proof. exact (eq_refl (term266 _120592 t s)). Qed.
Lemma lem5766374 {_120592 : Type'} (s : _120592 -> Prop) : (term267 _120592 s) = (term267 _120592 s).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem5766373 _120592 t s)). Qed.
Lemma lem5766375 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5766376 {_120592 : Type'} (s : _120592 -> Prop) : (term268 _120592 s) = (term268 _120592 s).
Proof. exact (MK_COMB (@lem5766375 _120592) (@lem5766374 _120592 s)). Qed.
Lemma lem5766377 {_120592 : Type'} : (term269 _120592) = (term269 _120592).
Proof. exact (fun_ext (fun s : _120592 -> Prop => @lem5766376 _120592 s)). Qed.
Lemma lem5766378 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5766379 {_120592 : Type'} : (term191 _120592) = (term191 _120592).
Proof. exact (MK_COMB (@lem5766378 _120592) (@lem5766377 _120592)). Qed.
Lemma lem5766380 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5766381 {_120592 : Type'} : (term219 _120592) = (term219 _120592).
Proof. exact (MK_COMB (@lem5766380) (@lem5766379 _120592)). Qed.
Lemma lem5766382 {_120592 _120607 _120745 _120749 : Type'} : (term223 _120592 _120607 _120745 _120749) = (term223 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766381 _120592) (@lem5766372 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766391 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term270 _120745 _120749 t op s f) = (term270 _120745 _120749 t op s f).
Proof. exact (eq_refl (term270 _120745 _120749 t op s f)). Qed.
Lemma lem5766392 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term271 _120745 _120749 op s f) = (term271 _120745 _120749 op s f).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5766391 _120745 _120749 t op s f)). Qed.
Lemma lem5766393 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766394 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term272 _120745 _120749 op s f) = (term272 _120745 _120749 op s f).
Proof. exact (MK_COMB (@lem5766393 _120745) (@lem5766392 _120745 _120749 op s f)). Qed.
Lemma lem5766395 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term273 _120745 _120749 op f) = (term273 _120745 _120749 op f).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5766394 _120745 _120749 op s f)). Qed.
Lemma lem5766396 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766397 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term274 _120745 _120749 op f) = (term274 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5766396 _120745) (@lem5766395 _120745 _120749 op f)). Qed.
Lemma lem5766398 {_120745 _120749 : Type'} (op : type1400 _120749) : (term275 _120745 _120749 op) = (term275 _120745 _120749 op).
Proof. exact (fun_ext (fun f : _120745 -> _120749 => @lem5766397 _120745 _120749 op f)). Qed.
Lemma lem5766399 {_120745 _120749 : Type'} : (@all (_120745 -> _120749)) = (@all (_120745 -> _120749)).
Proof. exact (eq_refl (@all (_120745 -> _120749))). Qed.
Lemma lem5766400 {_120745 _120749 : Type'} (op : type1400 _120749) : (term276 _120745 _120749 op) = (term276 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5766399 _120745 _120749) (@lem5766398 _120745 _120749 op)). Qed.
Lemma lem5766403 {_120749 : Type'} (op : type1400 _120749) : (term245 _120749 op) = (term245 _120749 op).
Proof. exact (eq_refl (term245 _120749 op)). Qed.
Lemma lem5766404 {_120745 _120749 : Type'} (op : type1400 _120749) : (term277 _120745 _120749 op) = (term277 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5766403 _120749 op) (@lem5766400 _120745 _120749 op)). Qed.
Lemma lem5766405 {_120745 _120749 : Type'} : (term278 _120745 _120749) = (term278 _120745 _120749).
Proof. exact (fun_ext (fun op : type1400 _120749 => @lem5766404 _120745 _120749 op)). Qed.
Lemma lem5766406 {_120749 : Type'} : (@all (_120749 -> _120749 -> _120749)) = (@all (_120749 -> _120749 -> _120749)).
Proof. exact (eq_refl (@all (_120749 -> _120749 -> _120749))). Qed.
Lemma lem5766407 {_120745 _120749 : Type'} : (term183 _120745 _120749) = (term183 _120745 _120749).
Proof. exact (MK_COMB (@lem5766406 _120749) (@lem5766405 _120745 _120749)). Qed.
Lemma lem5766408 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5766409 {_120745 _120749 : Type'} : (term185 _120745 _120749) = (term185 _120745 _120749).
Proof. exact (MK_COMB (@lem5766408) (@lem5766407 _120745 _120749)). Qed.
Lemma lem5766410 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5766411 {_120745 _120749 : Type'} : (term224 _120745 _120749) = (term224 _120745 _120749).
Proof. exact (MK_COMB (@lem5766410) (@lem5766409 _120745 _120749)). Qed.
Lemma lem5766412 {_120592 _120607 _120745 _120749 : Type'} : (term225 _120592 _120607 _120745 _120749) = (term225 _120592 _120607 _120745 _120749).
Proof. exact (MK_COMB (@lem5766411 _120745 _120749) (@lem5766382 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766695 {_120592 _120607 _120745 _120749 : Type'} : (term192 _120592 _120607 _120745 _120749) = (term225 _120592 _120607 _120745 _120749).
Proof. exact (TRANS (@lem5766145 _120592 _120607 _120745 _120749) (@lem5766412 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766696 {_120592 _120607 _120745 _120749 : Type'} : (term225 _120592 _120607 _120745 _120749) = (term192 _120592 _120607 _120745 _120749).
Proof. exact (SYM (@lem5766695 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5766697 {_120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term185 _120745 _120749.
Proof. exact (h1). Qed.
Lemma lem5766699 {_120745 : Type'} (h1 : term191 _120745) : term191 _120745.
Proof. exact (h1). Qed.
Lemma lem5766701 {_120745 : Type'} (h1 : term190 _120745) : term190 _120745.
Proof. exact (h1). Qed.
Lemma lem5766706 {_120745 _120749 : Type'} (h1 : term186 _120745 _120749) : term186 _120745 _120749.
Proof. exact (h1). Qed.
Lemma lem5766708 {_120745 : Type'} (h1 : term182 _120745) : term182 _120745.
Proof. exact (h1). Qed.
Lemma lem5766720 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term279 _120745 _120749 t op s f) = (term280 _120745 _120749 t op s f).
Proof. exact (@lem17362 (term281 _120745 t s) ((term282 _120745 _120749 s op t f) = (@iterate _120749 _120745 op s f))). Qed.
Lemma lem5766721 {_120745 : Type'} (P : type686 _120745) : (term283 _120745 P) = (term284 _120745 P).
Proof. exact (@lem18392 (_120745 -> Prop) P). Qed.
Lemma lem5766722 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term285 _120745 _120749 op s f) = (term286 _120745 _120749 op s f).
Proof. exact (@lem5766721 _120745 (term271 _120745 _120749 op s f)). Qed.
Lemma lem5766723 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term287 _120745 _120749 op s f t) = (term270 _120745 _120749 t op s f).
Proof. exact (eq_refl (term287 _120745 _120749 op s f t)). Qed.
Lemma lem5766724 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5766725 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term288 _120745 _120749 op s f t) = (term279 _120745 _120749 t op s f).
Proof. exact (MK_COMB (@lem5766724) (@lem5766723 _120745 _120749 t op s f)). Qed.
Lemma lem5766726 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term288 _120745 _120749 op s f t) = (term280 _120745 _120749 t op s f).
Proof. exact (TRANS (@lem5766725 _120745 _120749 t op s f) (@lem5766720 _120745 _120749 t op s f)). Qed.
Lemma lem5766727 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term289 _120745 _120749 op s f) = (term290 _120745 _120749 op s f).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5766726 _120745 _120749 t op s f)). Qed.
Lemma lem5766728 {_120745 : Type'} : (@ex (_120745 -> Prop)) = (@ex (_120745 -> Prop)).
Proof. exact (eq_refl (@ex (_120745 -> Prop))). Qed.
Lemma lem5766729 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term286 _120745 _120749 op s f) = (term291 _120745 _120749 op s f).
Proof. exact (MK_COMB (@lem5766728 _120745) (@lem5766727 _120745 _120749 op s f)). Qed.
Lemma lem5766730 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term285 _120745 _120749 op s f) = (term291 _120745 _120749 op s f).
Proof. exact (TRANS (@lem5766722 _120745 _120749 op s f) (@lem5766729 _120745 _120749 op s f)). Qed.
Lemma lem5766731 {_120745 : Type'} (P : type686 _120745) : (term283 _120745 P) = (term284 _120745 P).
Proof. exact (@lem18392 (_120745 -> Prop) P). Qed.
Lemma lem5766732 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term292 _120745 _120749 op f) = (term293 _120745 _120749 op f).
Proof. exact (@lem5766731 _120745 (term273 _120745 _120749 op f)). Qed.
Lemma lem5766733 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term294 _120745 _120749 op f s) = (term272 _120745 _120749 op s f).
Proof. exact (eq_refl (term294 _120745 _120749 op f s)). Qed.
Lemma lem5766734 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5766735 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term295 _120745 _120749 op f s) = (term285 _120745 _120749 op s f).
Proof. exact (MK_COMB (@lem5766734) (@lem5766733 _120745 _120749 op s f)). Qed.
Lemma lem5766736 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term295 _120745 _120749 op f s) = (term291 _120745 _120749 op s f).
Proof. exact (TRANS (@lem5766735 _120745 _120749 op s f) (@lem5766730 _120745 _120749 op s f)). Qed.
Lemma lem5766737 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term296 _120745 _120749 op f) = (term297 _120745 _120749 op f).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5766736 _120745 _120749 op s f)). Qed.
Lemma lem5766738 {_120745 : Type'} : (@ex (_120745 -> Prop)) = (@ex (_120745 -> Prop)).
Proof. exact (eq_refl (@ex (_120745 -> Prop))). Qed.
Lemma lem5766739 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term293 _120745 _120749 op f) = (term298 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5766738 _120745) (@lem5766737 _120745 _120749 op f)). Qed.
Lemma lem5766740 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term292 _120745 _120749 op f) = (term298 _120745 _120749 op f).
Proof. exact (TRANS (@lem5766732 _120745 _120749 op f) (@lem5766739 _120745 _120749 op f)). Qed.
Lemma lem5766741 {_120745 _120749 : Type'} (P : type572 _120745 _120749) : (term299 _120745 _120749 P) = (term300 _120745 _120749 P).
Proof. exact (@lem18392 (_120745 -> _120749) P). Qed.
Lemma lem5766742 {_120745 _120749 : Type'} (op : type1400 _120749) : (term301 _120745 _120749 op) = (term302 _120745 _120749 op).
Proof. exact (@lem5766741 _120745 _120749 (term275 _120745 _120749 op)). Qed.
Lemma lem5766743 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term303 _120745 _120749 op f) = (term274 _120745 _120749 op f).
Proof. exact (eq_refl (term303 _120745 _120749 op f)). Qed.
Lemma lem5766744 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5766745 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term304 _120745 _120749 op f) = (term292 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5766744) (@lem5766743 _120745 _120749 op f)). Qed.
Lemma lem5766746 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term304 _120745 _120749 op f) = (term298 _120745 _120749 op f).
Proof. exact (TRANS (@lem5766745 _120745 _120749 op f) (@lem5766740 _120745 _120749 op f)). Qed.
Lemma lem5766747 {_120745 _120749 : Type'} (op : type1400 _120749) : (term305 _120745 _120749 op) = (term306 _120745 _120749 op).
Proof. exact (fun_ext (fun f : _120745 -> _120749 => @lem5766746 _120745 _120749 op f)). Qed.
Lemma lem5766748 {_120745 _120749 : Type'} : (@ex (_120745 -> _120749)) = (@ex (_120745 -> _120749)).
Proof. exact (eq_refl (@ex (_120745 -> _120749))). Qed.
Lemma lem5766749 {_120745 _120749 : Type'} (op : type1400 _120749) : (term302 _120745 _120749 op) = (term307 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5766748 _120745 _120749) (@lem5766747 _120745 _120749 op)). Qed.
Lemma lem5766750 {_120745 _120749 : Type'} (op : type1400 _120749) : (term301 _120745 _120749 op) = (term307 _120745 _120749 op).
Proof. exact (TRANS (@lem5766742 _120745 _120749 op) (@lem5766749 _120745 _120749 op)). Qed.
Lemma lem5766752 {_120749 : Type'} (op : type1400 _120749) : (term308 _120749 op) = (term308 _120749 op).
Proof. exact (eq_refl (term308 _120749 op)). Qed.
Lemma lem5766753 {_120745 _120749 : Type'} (op : type1400 _120749) : (term309 _120745 _120749 op) = (term310 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5766752 _120749 op) (@lem5766750 _120745 _120749 op)). Qed.
Lemma lem5766754 {_120745 _120749 : Type'} (op : type1400 _120749) : (term311 _120745 _120749 op) = (term309 _120745 _120749 op).
Proof. exact (@lem17362 (@monoidal _120749 op) (term276 _120745 _120749 op)). Qed.
Lemma lem5766755 {_120745 _120749 : Type'} (op : type1400 _120749) : (term311 _120745 _120749 op) = (term310 _120745 _120749 op).
Proof. exact (TRANS (@lem5766754 _120745 _120749 op) (@lem5766753 _120745 _120749 op)). Qed.
Lemma lem5766756 {_120749 : Type'} (P : type403 _120749) : (term312 _120749 P) = (term313 _120749 P).
Proof. exact (@lem18392 (type1400 _120749) P). Qed.
Lemma lem5766757 {_120745 _120749 : Type'} : (term185 _120745 _120749) = (term314 _120745 _120749).
Proof. exact (@lem5766756 _120749 (term278 _120745 _120749)). Qed.
Lemma lem5766758 {_120745 _120749 : Type'} (op : type1400 _120749) : (term315 _120745 _120749 op) = (term277 _120745 _120749 op).
Proof. exact (eq_refl (term315 _120745 _120749 op)). Qed.
Lemma lem5766759 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5766760 {_120745 _120749 : Type'} (op : type1400 _120749) : (term316 _120745 _120749 op) = (term311 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5766759) (@lem5766758 _120745 _120749 op)). Qed.
Lemma lem5766761 {_120745 _120749 : Type'} (op : type1400 _120749) : (term316 _120745 _120749 op) = (term310 _120745 _120749 op).
Proof. exact (TRANS (@lem5766760 _120745 _120749 op) (@lem5766755 _120745 _120749 op)). Qed.
Lemma lem5766762 {_120745 _120749 : Type'} : (term317 _120745 _120749) = (term318 _120745 _120749).
Proof. exact (fun_ext (fun op : type1400 _120749 => @lem5766761 _120745 _120749 op)). Qed.
Lemma lem5766763 {_120749 : Type'} : (@ex (_120749 -> _120749 -> _120749)) = (@ex (_120749 -> _120749 -> _120749)).
Proof. exact (eq_refl (@ex (_120749 -> _120749 -> _120749))). Qed.
Lemma lem5766764 {_120745 _120749 : Type'} : (term314 _120745 _120749) = (term319 _120745 _120749).
Proof. exact (MK_COMB (@lem5766763 _120749) (@lem5766762 _120745 _120749)). Qed.
Lemma lem5766765 {_120745 _120749 : Type'} : (term185 _120745 _120749) = (term319 _120745 _120749).
Proof. exact (TRANS (@lem5766757 _120745 _120749) (@lem5766764 _120745 _120749)). Qed.
Lemma lem5766852 {A : Type'} (P : Prop) (Q : A -> Prop) : (term320 A P Q) = (term321 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5766853 {_120745 _120749 : Type'} (P : Prop) (Q : type572 _120745 _120749) : (term322 _120745 _120749 P Q) = (term323 _120745 _120749 P Q).
Proof. exact (@lem5766852 (_120745 -> _120749) P Q). Qed.
Lemma lem5766854 {_120745 _120749 : Type'} (op : type1400 _120749) : (term324 _120745 _120749 op) = (term325 _120745 _120749 op).
Proof. exact (@lem5766853 _120745 _120749 (@monoidal _120749 op) (term306 _120745 _120749 op)). Qed.
Lemma lem5766855 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term326 _120745 _120749 op f) = (term298 _120745 _120749 op f).
Proof. exact (eq_refl (term326 _120745 _120749 op f)). Qed.
Lemma lem5766856 {_120745 _120749 : Type'} (op : type1400 _120749) : (term327 _120745 _120749 op) = (term306 _120745 _120749 op).
Proof. exact (fun_ext (fun f : _120745 -> _120749 => @lem5766855 _120745 _120749 op f)). Qed.
Lemma lem5766857 {_120745 _120749 : Type'} : (@ex (_120745 -> _120749)) = (@ex (_120745 -> _120749)).
Proof. exact (eq_refl (@ex (_120745 -> _120749))). Qed.
Lemma lem5766858 {_120745 _120749 : Type'} (op : type1400 _120749) : (term328 _120745 _120749 op) = (term307 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5766857 _120745 _120749) (@lem5766856 _120745 _120749 op)). Qed.
Lemma lem5766859 {_120749 : Type'} (op : type1400 _120749) : (term308 _120749 op) = (term308 _120749 op).
Proof. exact (eq_refl (term308 _120749 op)). Qed.
Lemma lem5766860 {_120745 _120749 : Type'} (op : type1400 _120749) : (term324 _120745 _120749 op) = (term310 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5766859 _120749 op) (@lem5766858 _120745 _120749 op)). Qed.
Lemma lem5766861 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5766862 {_120745 _120749 : Type'} (op : type1400 _120749) : (term329 _120745 _120749 op) = (term330 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5766861) (@lem5766860 _120745 _120749 op)). Qed.
Lemma lem5766863 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term326 _120745 _120749 op f) = (term298 _120745 _120749 op f).
Proof. exact (eq_refl (term326 _120745 _120749 op f)). Qed.
Lemma lem5766864 {_120749 : Type'} (op : type1400 _120749) : (term308 _120749 op) = (term308 _120749 op).
Proof. exact (eq_refl (term308 _120749 op)). Qed.
Lemma lem5766865 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term331 _120745 _120749 op f) = (term332 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5766864 _120749 op) (@lem5766863 _120745 _120749 op f)). Qed.
Lemma lem5766866 {_120745 _120749 : Type'} (op : type1400 _120749) : (term333 _120745 _120749 op) = (term334 _120745 _120749 op).
Proof. exact (fun_ext (fun f : _120745 -> _120749 => @lem5766865 _120745 _120749 op f)). Qed.
Lemma lem5766867 {_120745 _120749 : Type'} : (@ex (_120745 -> _120749)) = (@ex (_120745 -> _120749)).
Proof. exact (eq_refl (@ex (_120745 -> _120749))). Qed.
Lemma lem5766868 {_120745 _120749 : Type'} (op : type1400 _120749) : (term325 _120745 _120749 op) = (term335 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5766867 _120745 _120749) (@lem5766866 _120745 _120749 op)). Qed.
Lemma lem5766869 {_120745 _120749 : Type'} (op : type1400 _120749) : ((term324 _120745 _120749 op) = (term325 _120745 _120749 op)) = ((term310 _120745 _120749 op) = (term335 _120745 _120749 op)).
Proof. exact (MK_COMB (@lem5766862 _120745 _120749 op) (@lem5766868 _120745 _120749 op)). Qed.
Lemma lem5766870 {_120745 _120749 : Type'} (op : type1400 _120749) : (term310 _120745 _120749 op) = (term335 _120745 _120749 op).
Proof. exact (EQ_MP (@lem5766869 _120745 _120749 op) (@lem5766854 _120745 _120749 op)). Qed.
Lemma lem5766872 {A : Type'} (P : Prop) (Q : A -> Prop) : (term320 A P Q) = (term321 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5766873 {_120745 : Type'} (P : Prop) (Q : type686 _120745) : (term336 _120745 P Q) = (term337 _120745 P Q).
Proof. exact (@lem5766872 (_120745 -> Prop) P Q). Qed.
Lemma lem5766874 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term338 _120745 _120749 op f) = (term339 _120745 _120749 op f).
Proof. exact (@lem5766873 _120745 (@monoidal _120749 op) (term297 _120745 _120749 op f)). Qed.
Lemma lem5766875 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term340 _120745 _120749 op f s) = (term291 _120745 _120749 op s f).
Proof. exact (eq_refl (term340 _120745 _120749 op f s)). Qed.
Lemma lem5766876 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term341 _120745 _120749 op f) = (term297 _120745 _120749 op f).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5766875 _120745 _120749 op s f)). Qed.
Lemma lem5766877 {_120745 : Type'} : (@ex (_120745 -> Prop)) = (@ex (_120745 -> Prop)).
Proof. exact (eq_refl (@ex (_120745 -> Prop))). Qed.
Lemma lem5766878 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term342 _120745 _120749 op f) = (term298 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5766877 _120745) (@lem5766876 _120745 _120749 op f)). Qed.
Lemma lem5766879 {_120749 : Type'} (op : type1400 _120749) : (term308 _120749 op) = (term308 _120749 op).
Proof. exact (eq_refl (term308 _120749 op)). Qed.
Lemma lem5766880 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term338 _120745 _120749 op f) = (term332 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5766879 _120749 op) (@lem5766878 _120745 _120749 op f)). Qed.
Lemma lem5766881 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5766882 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term343 _120745 _120749 op f) = (term344 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5766881) (@lem5766880 _120745 _120749 op f)). Qed.
Lemma lem5766883 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term340 _120745 _120749 op f s) = (term291 _120745 _120749 op s f).
Proof. exact (eq_refl (term340 _120745 _120749 op f s)). Qed.
Lemma lem5766884 {_120749 : Type'} (op : type1400 _120749) : (term308 _120749 op) = (term308 _120749 op).
Proof. exact (eq_refl (term308 _120749 op)). Qed.
Lemma lem5766885 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term345 _120745 _120749 op f s) = (term346 _120745 _120749 op s f).
Proof. exact (MK_COMB (@lem5766884 _120749 op) (@lem5766883 _120745 _120749 op s f)). Qed.
Lemma lem5766886 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term347 _120745 _120749 op f) = (term348 _120745 _120749 op f).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5766885 _120745 _120749 op s f)). Qed.
Lemma lem5766887 {_120745 : Type'} : (@ex (_120745 -> Prop)) = (@ex (_120745 -> Prop)).
Proof. exact (eq_refl (@ex (_120745 -> Prop))). Qed.
Lemma lem5766888 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term339 _120745 _120749 op f) = (term349 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5766887 _120745) (@lem5766886 _120745 _120749 op f)). Qed.
Lemma lem5766889 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : ((term338 _120745 _120749 op f) = (term339 _120745 _120749 op f)) = ((term332 _120745 _120749 op f) = (term349 _120745 _120749 op f)).
Proof. exact (MK_COMB (@lem5766882 _120745 _120749 op f) (@lem5766888 _120745 _120749 op f)). Qed.
Lemma lem5766890 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term332 _120745 _120749 op f) = (term349 _120745 _120749 op f).
Proof. exact (EQ_MP (@lem5766889 _120745 _120749 op f) (@lem5766874 _120745 _120749 op f)). Qed.
Lemma lem5766892 {A : Type'} (P : Prop) (Q : A -> Prop) : (term320 A P Q) = (term321 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5766893 {_120745 : Type'} (P : Prop) (Q : type686 _120745) : (term336 _120745 P Q) = (term337 _120745 P Q).
Proof. exact (@lem5766892 (_120745 -> Prop) P Q). Qed.
Lemma lem5766894 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term350 _120745 _120749 op s f) = (term351 _120745 _120749 op s f).
Proof. exact (@lem5766893 _120745 (@monoidal _120749 op) (term290 _120745 _120749 op s f)). Qed.
Lemma lem5766895 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term352 _120745 _120749 op s f t) = (term280 _120745 _120749 t op s f).
Proof. exact (eq_refl (term352 _120745 _120749 op s f t)). Qed.
Lemma lem5766896 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term353 _120745 _120749 op s f) = (term290 _120745 _120749 op s f).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5766895 _120745 _120749 t op s f)). Qed.
Lemma lem5766897 {_120745 : Type'} : (@ex (_120745 -> Prop)) = (@ex (_120745 -> Prop)).
Proof. exact (eq_refl (@ex (_120745 -> Prop))). Qed.
Lemma lem5766898 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term354 _120745 _120749 op s f) = (term291 _120745 _120749 op s f).
Proof. exact (MK_COMB (@lem5766897 _120745) (@lem5766896 _120745 _120749 op s f)). Qed.
Lemma lem5766899 {_120749 : Type'} (op : type1400 _120749) : (term308 _120749 op) = (term308 _120749 op).
Proof. exact (eq_refl (term308 _120749 op)). Qed.
Lemma lem5766900 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term350 _120745 _120749 op s f) = (term346 _120745 _120749 op s f).
Proof. exact (MK_COMB (@lem5766899 _120749 op) (@lem5766898 _120745 _120749 op s f)). Qed.
Lemma lem5766901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5766902 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term355 _120745 _120749 op s f) = (term356 _120745 _120749 op s f).
Proof. exact (MK_COMB (@lem5766901) (@lem5766900 _120745 _120749 op s f)). Qed.
Lemma lem5766903 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term352 _120745 _120749 op s f t) = (term280 _120745 _120749 t op s f).
Proof. exact (eq_refl (term352 _120745 _120749 op s f t)). Qed.
Lemma lem5766904 {_120749 : Type'} (op : type1400 _120749) : (term308 _120749 op) = (term308 _120749 op).
Proof. exact (eq_refl (term308 _120749 op)). Qed.
Lemma lem5766905 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term357 _120745 _120749 op s f t) = (term358 _120745 _120749 t op s f).
Proof. exact (MK_COMB (@lem5766904 _120749 op) (@lem5766903 _120745 _120749 t op s f)). Qed.
Lemma lem5766906 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term359 _120745 _120749 op s f) = (term360 _120745 _120749 op s f).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5766905 _120745 _120749 t op s f)). Qed.
Lemma lem5766907 {_120745 : Type'} : (@ex (_120745 -> Prop)) = (@ex (_120745 -> Prop)).
Proof. exact (eq_refl (@ex (_120745 -> Prop))). Qed.
Lemma lem5766908 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term351 _120745 _120749 op s f) = (term361 _120745 _120749 op s f).
Proof. exact (MK_COMB (@lem5766907 _120745) (@lem5766906 _120745 _120749 op s f)). Qed.
Lemma lem5766909 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : ((term350 _120745 _120749 op s f) = (term351 _120745 _120749 op s f)) = ((term346 _120745 _120749 op s f) = (term361 _120745 _120749 op s f)).
Proof. exact (MK_COMB (@lem5766902 _120745 _120749 op s f) (@lem5766908 _120745 _120749 op s f)). Qed.
Lemma lem5766910 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term346 _120745 _120749 op s f) = (term361 _120745 _120749 op s f).
Proof. exact (EQ_MP (@lem5766909 _120745 _120749 op s f) (@lem5766894 _120745 _120749 op s f)). Qed.
Lemma lem5766911 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term348 _120745 _120749 op f) = (term362 _120745 _120749 op f).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5766910 _120745 _120749 op s f)). Qed.
Lemma lem5766912 {_120745 : Type'} : (@ex (_120745 -> Prop)) = (@ex (_120745 -> Prop)).
Proof. exact (eq_refl (@ex (_120745 -> Prop))). Qed.
Lemma lem5766913 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term349 _120745 _120749 op f) = (term363 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5766912 _120745) (@lem5766911 _120745 _120749 op f)). Qed.
Lemma lem5766914 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term332 _120745 _120749 op f) = (term363 _120745 _120749 op f).
Proof. exact (TRANS (@lem5766890 _120745 _120749 op f) (@lem5766913 _120745 _120749 op f)). Qed.
Lemma lem5766915 {_120745 _120749 : Type'} (op : type1400 _120749) : (term334 _120745 _120749 op) = (term364 _120745 _120749 op).
Proof. exact (fun_ext (fun f : _120745 -> _120749 => @lem5766914 _120745 _120749 op f)). Qed.
Lemma lem5766916 {_120745 _120749 : Type'} : (@ex (_120745 -> _120749)) = (@ex (_120745 -> _120749)).
Proof. exact (eq_refl (@ex (_120745 -> _120749))). Qed.
Lemma lem5766917 {_120745 _120749 : Type'} (op : type1400 _120749) : (term335 _120745 _120749 op) = (term365 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5766916 _120745 _120749) (@lem5766915 _120745 _120749 op)). Qed.
Lemma lem5766918 {_120745 _120749 : Type'} (op : type1400 _120749) : (term310 _120745 _120749 op) = (term365 _120745 _120749 op).
Proof. exact (TRANS (@lem5766870 _120745 _120749 op) (@lem5766917 _120745 _120749 op)). Qed.
Lemma lem5766919 {_120745 _120749 : Type'} : (term318 _120745 _120749) = (term366 _120745 _120749).
Proof. exact (fun_ext (fun op : type1400 _120749 => @lem5766918 _120745 _120749 op)). Qed.
Lemma lem5766920 {_120749 : Type'} : (@ex (_120749 -> _120749 -> _120749)) = (@ex (_120749 -> _120749 -> _120749)).
Proof. exact (eq_refl (@ex (_120749 -> _120749 -> _120749))). Qed.
Lemma lem5766922 {_120745 _120749 : Type'} : (term319 _120745 _120749) = (term367 _120745 _120749).
Proof. exact (MK_COMB (@lem5766920 _120749) (@lem5766919 _120745 _120749)). Qed.
Lemma lem5766923 {_120745 _120749 : Type'} : (term185 _120745 _120749) = (term367 _120745 _120749).
Proof. exact (TRANS (@lem5766765 _120745 _120749) (@lem5766922 _120745 _120749)). Qed.
Lemma lem5766924 {_120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term367 _120745 _120749.
Proof. exact (EQ_MP (@lem5766923 _120745 _120749) (@lem5766697 _120745 _120749 h1)). Qed.
Lemma lem5766945 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term266 _120745 t s) = (term266 _120745 t s).
Proof. exact (eq_refl (term266 _120745 t s)). Qed.
Lemma lem5766946 {_120745 : Type'} (s : _120745 -> Prop) : (term267 _120745 s) = (term267 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5766945 _120745 t s)). Qed.
Lemma lem5766947 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766948 {_120745 : Type'} (s : _120745 -> Prop) : (term268 _120745 s) = (term268 _120745 s).
Proof. exact (MK_COMB (@lem5766947 _120745) (@lem5766946 _120745 s)). Qed.
Lemma lem5766949 {_120745 : Type'} : (term269 _120745) = (term269 _120745).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5766948 _120745 s)). Qed.
Lemma lem5766950 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5766963 {_120745 : Type'} : (term191 _120745) = (term191 _120745).
Proof. exact (MK_COMB (@lem5766950 _120745) (@lem5766949 _120745)). Qed.
Lemma lem5766964 {_120745 : Type'} (h1 : term191 _120745) : term191 _120745.
Proof. exact (EQ_MP (@lem5766963 _120745) (@lem5766699 _120745 h1)). Qed.
Lemma lem5767125 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term368 _120745 s t) = (term369 _120745 s t).
Proof. exact (@lem17045 (@FINITE _120745 t) (@SUBSET _120745 s t)). Qed.
Lemma lem5767126 {_120745 : Type'} (s : _120745 -> Prop) : (@FINITE _120745 s) = (@FINITE _120745 s).
Proof. exact (eq_refl (@FINITE _120745 s)). Qed.
Lemma lem5767127 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5767128 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term370 _120745 s t) = (term371 _120745 s t).
Proof. exact (MK_COMB (@lem5767127) (@lem5767125 _120745 s t)). Qed.
Lemma lem5767129 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term372 _120745 t s) = (term373 _120745 t s).
Proof. exact (MK_COMB (@lem5767128 _120745 s t) (@lem5767126 _120745 s)). Qed.
Lemma lem5767130 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term262 _120745 t s) = (term372 _120745 t s).
Proof. exact (@lem17265 (term281 _120745 s t) (@FINITE _120745 s)). Qed.
Lemma lem5767131 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term262 _120745 t s) = (term373 _120745 t s).
Proof. exact (TRANS (@lem5767130 _120745 t s) (@lem5767129 _120745 t s)). Qed.
Lemma lem5767132 {_120745 : Type'} (s : _120745 -> Prop) : (term263 _120745 s) = (term374 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5767131 _120745 t s)). Qed.
Lemma lem5767133 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5767134 {_120745 : Type'} (s : _120745 -> Prop) : (term264 _120745 s) = (term375 _120745 s).
Proof. exact (MK_COMB (@lem5767133 _120745) (@lem5767132 _120745 s)). Qed.
Lemma lem5767135 {_120745 : Type'} : (term265 _120745) = (term376 _120745).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5767134 _120745 s)). Qed.
Lemma lem5767136 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5767137 {_120745 : Type'} : (term190 _120745) = (term377 _120745).
Proof. exact (MK_COMB (@lem5767136 _120745) (@lem5767135 _120745)). Qed.
Lemma lem5767163 {A : Type'} (P : A -> Prop) (Q : Prop) : (term378 A P Q) = (term379 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem5767164 {_120745 : Type'} (P : type686 _120745) (Q : Prop) : (term380 _120745 P Q) = (term381 _120745 P Q).
Proof. exact (@lem5767163 (_120745 -> Prop) P Q). Qed.
Lemma lem5767165 {_120745 : Type'} (s : _120745 -> Prop) : (term382 _120745 s) = (term383 _120745 s).
Proof. exact (@lem5767164 _120745 (term384 _120745 s) (@FINITE _120745 s)). Qed.
Lemma lem5767166 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term385 _120745 s t) = (term369 _120745 s t).
Proof. exact (eq_refl (term385 _120745 s t)). Qed.
Lemma lem5767167 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5767168 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term386 _120745 s t) = (term371 _120745 s t).
Proof. exact (MK_COMB (@lem5767167) (@lem5767166 _120745 s t)). Qed.
Lemma lem5767169 {_120745 : Type'} (s : _120745 -> Prop) : (@FINITE _120745 s) = (@FINITE _120745 s).
Proof. exact (eq_refl (@FINITE _120745 s)). Qed.
Lemma lem5767170 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term387 _120745 t s) = (term373 _120745 t s).
Proof. exact (MK_COMB (@lem5767168 _120745 s t) (@lem5767169 _120745 s)). Qed.
Lemma lem5767171 {_120745 : Type'} (s : _120745 -> Prop) : (term388 _120745 s) = (term374 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5767170 _120745 t s)). Qed.
Lemma lem5767172 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5767173 {_120745 : Type'} (s : _120745 -> Prop) : (term382 _120745 s) = (term375 _120745 s).
Proof. exact (MK_COMB (@lem5767172 _120745) (@lem5767171 _120745 s)). Qed.
Lemma lem5767174 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5767175 {_120745 : Type'} (s : _120745 -> Prop) : (term389 _120745 s) = (term390 _120745 s).
Proof. exact (MK_COMB (@lem5767174) (@lem5767173 _120745 s)). Qed.
Lemma lem5767176 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term385 _120745 s t) = (term369 _120745 s t).
Proof. exact (eq_refl (term385 _120745 s t)). Qed.
Lemma lem5767177 {_120745 : Type'} (s : _120745 -> Prop) : (term391 _120745 s) = (term384 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5767176 _120745 s t)). Qed.
Lemma lem5767178 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5767179 {_120745 : Type'} (s : _120745 -> Prop) : (term392 _120745 s) = (term393 _120745 s).
Proof. exact (MK_COMB (@lem5767178 _120745) (@lem5767177 _120745 s)). Qed.
Lemma lem5767180 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5767181 {_120745 : Type'} (s : _120745 -> Prop) : (term394 _120745 s) = (term395 _120745 s).
Proof. exact (MK_COMB (@lem5767180) (@lem5767179 _120745 s)). Qed.
Lemma lem5767182 {_120745 : Type'} (s : _120745 -> Prop) : (@FINITE _120745 s) = (@FINITE _120745 s).
Proof. exact (eq_refl (@FINITE _120745 s)). Qed.
Lemma lem5767183 {_120745 : Type'} (s : _120745 -> Prop) : (term383 _120745 s) = (term396 _120745 s).
Proof. exact (MK_COMB (@lem5767181 _120745 s) (@lem5767182 _120745 s)). Qed.
Lemma lem5767184 {_120745 : Type'} (s : _120745 -> Prop) : ((term382 _120745 s) = (term383 _120745 s)) = ((term375 _120745 s) = (term396 _120745 s)).
Proof. exact (MK_COMB (@lem5767175 _120745 s) (@lem5767183 _120745 s)). Qed.
Lemma lem5767185 {_120745 : Type'} (s : _120745 -> Prop) : (term375 _120745 s) = (term396 _120745 s).
Proof. exact (EQ_MP (@lem5767184 _120745 s) (@lem5767165 _120745 s)). Qed.
Lemma lem5767234 {_120745 : Type'} : (term376 _120745) = (term397 _120745).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5767185 _120745 s)). Qed.
Lemma lem5767235 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5767270 {_120745 : Type'} : (term377 _120745) = (term398 _120745).
Proof. exact (MK_COMB (@lem5767235 _120745) (@lem5767234 _120745)). Qed.
Lemma lem5767271 {_120745 : Type'} : (term190 _120745) = (term398 _120745).
Proof. exact (TRANS (@lem5767137 _120745) (@lem5767270 _120745)). Qed.
Lemma lem5767272 {_120745 : Type'} (h1 : term190 _120745) : term398 _120745.
Proof. exact (EQ_MP (@lem5767271 _120745) (@lem5766701 _120745 h1)). Qed.
Lemma lem5768167 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term399 _120745 s t) = (term400 _120745 s t).
Proof. exact (@lem17045 (@FINITE _120745 t) (@DISJOINT _120745 s t)). Qed.
Lemma lem5768169 {_120745 : Type'} (s : _120745 -> Prop) : (term401 _120745 s) = (term401 _120745 s).
Proof. exact (eq_refl (term401 _120745 s)). Qed.
Lemma lem5768170 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term402 _120745 s t) = (term403 _120745 s t).
Proof. exact (MK_COMB (@lem5768169 _120745 s) (@lem5768167 _120745 s t)). Qed.
Lemma lem5768171 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term404 _120745 s t) = (term402 _120745 s t).
Proof. exact (@lem17045 (@FINITE _120745 s) (term405 _120745 s t)). Qed.
Lemma lem5768172 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term404 _120745 s t) = (term403 _120745 s t).
Proof. exact (TRANS (@lem5768171 _120745 s t) (@lem5768170 _120745 s t)). Qed.
Lemma lem5768173 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : ((term406 _120745 _120749 op s t f) = (term407 _120745 _120749 s op t f)) = ((term406 _120745 _120749 op s t f) = (term407 _120745 _120749 s op t f)).
Proof. exact (eq_refl ((term406 _120745 _120749 op s t f) = (term407 _120745 _120749 s op t f))). Qed.
Lemma lem5768174 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5768175 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term408 _120745 s t) = (term409 _120745 s t).
Proof. exact (MK_COMB (@lem5768174) (@lem5768172 _120745 s t)). Qed.
Lemma lem5768176 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term410 _120745 _120749 s op t f) = (term411 _120745 _120749 s op t f).
Proof. exact (MK_COMB (@lem5768175 _120745 s t) (@lem5768173 _120745 _120749 s op t f)). Qed.
Lemma lem5768177 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term238 _120745 _120749 s op t f) = (term410 _120745 _120749 s op t f).
Proof. exact (@lem17265 (term412 _120745 s t) ((term406 _120745 _120749 op s t f) = (term407 _120745 _120749 s op t f))). Qed.
Lemma lem5768178 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term238 _120745 _120749 s op t f) = (term411 _120745 _120749 s op t f).
Proof. exact (TRANS (@lem5768177 _120745 _120749 s op t f) (@lem5768176 _120745 _120749 s op t f)). Qed.
Lemma lem5768179 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term239 _120745 _120749 s op f) = (term413 _120745 _120749 s op f).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5768178 _120745 _120749 s op t f)). Qed.
Lemma lem5768180 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5768181 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term240 _120745 _120749 s op f) = (term414 _120745 _120749 s op f).
Proof. exact (MK_COMB (@lem5768180 _120745) (@lem5768179 _120745 _120749 s op f)). Qed.
Lemma lem5768182 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term241 _120745 _120749 op f) = (term415 _120745 _120749 op f).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5768181 _120745 _120749 s op f)). Qed.
Lemma lem5768183 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5768184 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term242 _120745 _120749 op f) = (term416 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5768183 _120745) (@lem5768182 _120745 _120749 op f)). Qed.
Lemma lem5768185 {_120745 _120749 : Type'} (op : type1400 _120749) : (term243 _120745 _120749 op) = (term417 _120745 _120749 op).
Proof. exact (fun_ext (fun f : _120745 -> _120749 => @lem5768184 _120745 _120749 op f)). Qed.
Lemma lem5768186 {_120745 _120749 : Type'} : (@all (_120745 -> _120749)) = (@all (_120745 -> _120749)).
Proof. exact (eq_refl (@all (_120745 -> _120749))). Qed.
Lemma lem5768187 {_120745 _120749 : Type'} (op : type1400 _120749) : (term244 _120745 _120749 op) = (term418 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5768186 _120745 _120749) (@lem5768185 _120745 _120749 op)). Qed.
Lemma lem5768189 {_120749 : Type'} (op : type1400 _120749) : (term419 _120749 op) = (term419 _120749 op).
Proof. exact (eq_refl (term419 _120749 op)). Qed.
Lemma lem5768190 {_120745 _120749 : Type'} (op : type1400 _120749) : (term420 _120745 _120749 op) = (term421 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5768189 _120749 op) (@lem5768187 _120745 _120749 op)). Qed.
Lemma lem5768191 {_120745 _120749 : Type'} (op : type1400 _120749) : (term246 _120745 _120749 op) = (term420 _120745 _120749 op).
Proof. exact (@lem17265 (@monoidal _120749 op) (term244 _120745 _120749 op)). Qed.
Lemma lem5768192 {_120745 _120749 : Type'} (op : type1400 _120749) : (term246 _120745 _120749 op) = (term421 _120745 _120749 op).
Proof. exact (TRANS (@lem5768191 _120745 _120749 op) (@lem5768190 _120745 _120749 op)). Qed.
Lemma lem5768193 {_120745 _120749 : Type'} : (term247 _120745 _120749) = (term422 _120745 _120749).
Proof. exact (fun_ext (fun op : type1400 _120749 => @lem5768192 _120745 _120749 op)). Qed.
Lemma lem5768194 {_120749 : Type'} : (@all (_120749 -> _120749 -> _120749)) = (@all (_120749 -> _120749 -> _120749)).
Proof. exact (eq_refl (@all (_120749 -> _120749 -> _120749))). Qed.
Lemma lem5768303 {_120745 _120749 : Type'} : (term186 _120745 _120749) = (term423 _120745 _120749).
Proof. exact (MK_COMB (@lem5768194 _120749) (@lem5768193 _120745 _120749)). Qed.
Lemma lem5768304 {_120745 _120749 : Type'} (h1 : term186 _120745 _120749) : term423 _120745 _120749.
Proof. exact (EQ_MP (@lem5768303 _120745 _120749) (@lem5766706 _120745 _120749 h1)). Qed.
Lemma lem5768461 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term13 _120745 s t) = (term424 _120745 s t).
Proof. exact (@lem17265 (@SUBSET _120745 t s) (term11 _120745 s t)). Qed.
Lemma lem5768462 {_120745 : Type'} (s : _120745 -> Prop) : (term226 _120745 s) = (term425 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5768461 _120745 s t)). Qed.
Lemma lem5768463 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5768464 {_120745 : Type'} (s : _120745 -> Prop) : (term181 _120745 s) = (term426 _120745 s).
Proof. exact (MK_COMB (@lem5768463 _120745) (@lem5768462 _120745 s)). Qed.
Lemma lem5768465 {_120745 : Type'} : (term227 _120745) = (term427 _120745).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5768464 _120745 s)). Qed.
Lemma lem5768466 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5768523 {_120745 : Type'} : (term182 _120745) = (term428 _120745).
Proof. exact (MK_COMB (@lem5768466 _120745) (@lem5768465 _120745)). Qed.
Lemma lem5768524 {_120745 : Type'} (h1 : term182 _120745) : term428 _120745.
Proof. exact (EQ_MP (@lem5768523 _120745) (@lem5766708 _120745 h1)). Qed.
Lemma lem5768525 {_120745 _120749 : Type'} (op : type1400 _120749) (h1 : term365 _120745 _120749 op) : term365 _120745 _120749 op.
Proof. exact (h1). Qed.
Lemma lem5768526 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) (h1 : term363 _120745 _120749 op f) : term363 _120745 _120749 op f.
Proof. exact (h1). Qed.
Lemma lem5768527 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term361 _120745 _120749 op s f) : term361 _120745 _120749 op s f.
Proof. exact (h1). Qed.
Lemma lem5768528 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term358 _120745 _120749 t op s f.
Proof. exact (h1). Qed.
Lemma lem5768569 {_120745 : Type'} : (@SUBSET _120745) = (@SUBSET _120745).
Proof. exact (eq_refl (@SUBSET _120745)). Qed.
Lemma lem5768576 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5768577 {_120745 : Type'} (f : type636 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) f x).
Proof. exact (@lem5768576 (_120745 -> Prop) (type672 _120745) f x). Qed.
Lemma lem5768578 {_120745 : Type'} (s : _120745 -> Prop) : (@DIFF _120745 s) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s).
Proof. exact (@lem5768577 _120745 (@DIFF _120745) s). Qed.
Lemma lem5768579 {_120745 : Type'} (t : _120745 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5768580 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@DIFF _120745 s t) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s t).
Proof. exact (MK_COMB (@lem5768578 _120745 s) (@lem5768579 _120745 t)). Qed.
Lemma lem5768582 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5768583 {_120745 : Type'} (f : type672 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> _120745 -> Prop) f x).
Proof. exact (@lem5768582 (_120745 -> Prop) (_120745 -> Prop) f x). Qed.
Lemma lem5768584 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s t) = (term429 _120745 s t).
Proof. exact (@lem5768583 _120745 (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s) t). Qed.
Lemma lem5768586 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@DIFF _120745 s t) = (term429 _120745 s t).
Proof. exact (TRANS (@lem5768580 _120745 s t) (@lem5768584 _120745 s t)). Qed.
Lemma lem5768587 {_120745 : Type'} (s : _120745 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5768588 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term430 _120745 s t) = (term431 _120745 s t).
Proof. exact (MK_COMB (@lem5768569 _120745) (@lem5768586 _120745 s t)). Qed.
Lemma lem5768589 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term266 _120745 t s) = (term432 _120745 t s).
Proof. exact (MK_COMB (@lem5768588 _120745 s t) (@lem5768587 _120745 s)). Qed.
Lemma lem5768591 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5768592 {_120745 : Type'} (f : type639 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5768591 (_120745 -> Prop) (type686 _120745) f x). Qed.
Lemma lem5768593 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term431 _120745 s t) = (term433 _120745 s t).
Proof. exact (@lem5768592 _120745 (@SUBSET _120745) (term429 _120745 s t)). Qed.
Lemma lem5768594 {_120745 : Type'} (s : _120745 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5768595 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term432 _120745 t s) = (term434 _120745 t s).
Proof. exact (MK_COMB (@lem5768593 _120745 s t) (@lem5768594 _120745 s)). Qed.
Lemma lem5768597 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5768598 {_120745 : Type'} (f : type686 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5768597 (_120745 -> Prop) Prop f x). Qed.
Lemma lem5768599 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term434 _120745 t s) = (term435 _120745 t s).
Proof. exact (@lem5768598 _120745 (term433 _120745 s t) s). Qed.
Lemma lem5768600 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term432 _120745 t s) = (term435 _120745 t s).
Proof. exact (TRANS (@lem5768595 _120745 t s) (@lem5768599 _120745 t s)). Qed.
Lemma lem5768601 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term266 _120745 t s) = (term435 _120745 t s).
Proof. exact (TRANS (@lem5768589 _120745 t s) (@lem5768600 _120745 t s)). Qed.
Lemma lem5768602 {_120745 : Type'} (s : _120745 -> Prop) : (term267 _120745 s) = (term436 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5768601 _120745 t s)). Qed.
Lemma lem5768603 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5768604 {_120745 : Type'} (s : _120745 -> Prop) : (term268 _120745 s) = (term437 _120745 s).
Proof. exact (MK_COMB (@lem5768603 _120745) (@lem5768602 _120745 s)). Qed.
Lemma lem5768605 {_120745 : Type'} : (term269 _120745) = (term438 _120745).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5768604 _120745 s)). Qed.
Lemma lem5768606 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5768607 {_120745 : Type'} : (term191 _120745) = (term439 _120745).
Proof. exact (MK_COMB (@lem5768606 _120745) (@lem5768605 _120745)). Qed.
Lemma lem5768608 {_120745 : Type'} (h1 : term191 _120745) : term439 _120745.
Proof. exact (EQ_MP (@lem5768607 _120745) (@lem5766964 _120745 h1)). Qed.
Lemma lem5768663 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5768664 {_120745 : Type'} (f : type686 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5768663 (_120745 -> Prop) Prop f x). Qed.
Lemma lem5768666 {_120745 : Type'} (s : _120745 -> Prop) : (@FINITE _120745 s) = (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s).
Proof. exact (@lem5768664 _120745 (@FINITE _120745) s). Qed.
Lemma lem5768667 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5768674 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5768675 {_120745 : Type'} (f : type639 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5768674 (_120745 -> Prop) (type686 _120745) f x). Qed.
Lemma lem5768676 {_120745 : Type'} (s : _120745 -> Prop) : (@SUBSET _120745 s) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@SUBSET _120745) s).
Proof. exact (@lem5768675 _120745 (@SUBSET _120745) s). Qed.
Lemma lem5768677 {_120745 : Type'} (t : _120745 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5768678 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@SUBSET _120745 s t) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@SUBSET _120745) s t).
Proof. exact (MK_COMB (@lem5768676 _120745 s) (@lem5768677 _120745 t)). Qed.
Lemma lem5768680 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5768681 {_120745 : Type'} (f : type686 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5768680 (_120745 -> Prop) Prop f x). Qed.
Lemma lem5768682 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@SUBSET _120745) s t) = (term440 _120745 s t).
Proof. exact (@lem5768681 _120745 (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@SUBSET _120745) s) t). Qed.
Lemma lem5768684 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@SUBSET _120745 s t) = (term440 _120745 s t).
Proof. exact (TRANS (@lem5768678 _120745 s t) (@lem5768682 _120745 s t)). Qed.
Lemma lem5768685 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term441 _120745 s t) = (term442 _120745 s t).
Proof. exact (MK_COMB (@lem5768667) (@lem5768684 _120745 s t)). Qed.
Lemma lem5768686 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5768691 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5768692 {_120745 : Type'} (f : type686 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5768691 (_120745 -> Prop) Prop f x). Qed.
Lemma lem5768694 {_120745 : Type'} (t : _120745 -> Prop) : (@FINITE _120745 t) = (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) t).
Proof. exact (@lem5768692 _120745 (@FINITE _120745) t). Qed.
Lemma lem5768695 {_120745 : Type'} (t : _120745 -> Prop) : (term443 _120745 t) = (term444 _120745 t).
Proof. exact (MK_COMB (@lem5768686) (@lem5768694 _120745 t)). Qed.
Lemma lem5768696 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5768697 {_120745 : Type'} (t : _120745 -> Prop) : (term401 _120745 t) = (term445 _120745 t).
Proof. exact (MK_COMB (@lem5768696) (@lem5768695 _120745 t)). Qed.
Lemma lem5768698 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term369 _120745 s t) = (term446 _120745 s t).
Proof. exact (MK_COMB (@lem5768697 _120745 t) (@lem5768685 _120745 s t)). Qed.
Lemma lem5768699 {_120745 : Type'} (s : _120745 -> Prop) : (term384 _120745 s) = (term447 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5768698 _120745 s t)). Qed.
Lemma lem5768700 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5768701 {_120745 : Type'} (s : _120745 -> Prop) : (term393 _120745 s) = (term448 _120745 s).
Proof. exact (MK_COMB (@lem5768700 _120745) (@lem5768699 _120745 s)). Qed.
Lemma lem5768702 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5768703 {_120745 : Type'} (s : _120745 -> Prop) : (term395 _120745 s) = (term449 _120745 s).
Proof. exact (MK_COMB (@lem5768702) (@lem5768701 _120745 s)). Qed.
Lemma lem5768704 {_120745 : Type'} (s : _120745 -> Prop) : (term396 _120745 s) = (term450 _120745 s).
Proof. exact (MK_COMB (@lem5768703 _120745 s) (@lem5768666 _120745 s)). Qed.
Lemma lem5768705 {_120745 : Type'} : (term397 _120745) = (term451 _120745).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5768704 _120745 s)). Qed.
Lemma lem5768706 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5768707 {_120745 : Type'} : (term398 _120745) = (term452 _120745).
Proof. exact (MK_COMB (@lem5768706 _120745) (@lem5768705 _120745)). Qed.
Lemma lem5768708 {_120745 : Type'} (h1 : term190 _120745) : term452 _120745.
Proof. exact (EQ_MP (@lem5768707 _120745) (@lem5767272 _120745 h1)). Qed.
Lemma lem5769309 {_120749 : Type'} : (@eq _120749) = (@eq _120749).
Proof. exact (eq_refl (@eq _120749)). Qed.
Lemma lem5769318 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769319 {_120745 : Type'} (f : type636 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) f x).
Proof. exact (@lem5769318 (_120745 -> Prop) (type672 _120745) f x). Qed.
Lemma lem5769320 {_120745 : Type'} (s : _120745 -> Prop) : (@UNION _120745 s) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@UNION _120745) s).
Proof. exact (@lem5769319 _120745 (@UNION _120745) s). Qed.
Lemma lem5769321 {_120745 : Type'} (t : _120745 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5769322 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@UNION _120745 s t) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@UNION _120745) s t).
Proof. exact (MK_COMB (@lem5769320 _120745 s) (@lem5769321 _120745 t)). Qed.
Lemma lem5769324 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769325 {_120745 : Type'} (f : type672 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> _120745 -> Prop) f x).
Proof. exact (@lem5769324 (_120745 -> Prop) (_120745 -> Prop) f x). Qed.
Lemma lem5769326 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@UNION _120745) s t) = (term453 _120745 s t).
Proof. exact (@lem5769325 _120745 (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@UNION _120745) s) t). Qed.
Lemma lem5769328 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@UNION _120745 s t) = (term453 _120745 s t).
Proof. exact (TRANS (@lem5769322 _120745 s t) (@lem5769326 _120745 s t)). Qed.
Lemma lem5769329 {_120745 _120749 : Type'} (f : _120745 -> _120749) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5769330 {_120745 _120749 : Type'} (op : type1400 _120749) : (@iterate _120749 _120745 op) = (@iterate _120749 _120745 op).
Proof. exact (eq_refl (@iterate _120749 _120745 op)). Qed.
Lemma lem5769331 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) : (term454 _120745 _120749 op s t) = (term455 _120745 _120749 op s t).
Proof. exact (MK_COMB (@lem5769330 _120745 _120749 op) (@lem5769328 _120745 s t)). Qed.
Lemma lem5769332 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term406 _120745 _120749 op s t f) = (term456 _120745 _120749 op s t f).
Proof. exact (MK_COMB (@lem5769331 _120745 _120749 op s t) (@lem5769329 _120745 _120749 f)). Qed.
Lemma lem5769334 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769335 {_120745 _120749 : Type'} (f : type750 _120745 _120749) (x : type1400 _120749) : (f x) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769334 (type1400 _120749) (type632 _120745 _120749) f x). Qed.
Lemma lem5769336 {_120745 _120749 : Type'} (op : type1400 _120749) : (@iterate _120749 _120745 op) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op).
Proof. exact (@lem5769335 _120745 _120749 (@iterate _120749 _120745) op). Qed.
Lemma lem5769337 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term453 _120745 s t) = (term453 _120745 s t).
Proof. exact (eq_refl (term453 _120745 s t)). Qed.
Lemma lem5769338 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) : (term455 _120745 _120749 op s t) = (term457 _120745 _120749 op s t).
Proof. exact (MK_COMB (@lem5769336 _120745 _120749 op) (@lem5769337 _120745 s t)). Qed.
Lemma lem5769340 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769341 {_120745 _120749 : Type'} (f : type632 _120745 _120749) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769340 (_120745 -> Prop) (type570 _120745 _120749) f x). Qed.
Lemma lem5769342 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) : (term457 _120745 _120749 op s t) = (term458 _120745 _120749 op s t).
Proof. exact (@lem5769341 _120745 _120749 (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op) (term453 _120745 s t)). Qed.
Lemma lem5769343 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) : (term455 _120745 _120749 op s t) = (term458 _120745 _120749 op s t).
Proof. exact (TRANS (@lem5769338 _120745 _120749 op s t) (@lem5769342 _120745 _120749 op s t)). Qed.
Lemma lem5769344 {_120745 _120749 : Type'} (f : _120745 -> _120749) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5769345 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term456 _120745 _120749 op s t f) = (term459 _120745 _120749 op s t f).
Proof. exact (MK_COMB (@lem5769343 _120745 _120749 op s t) (@lem5769344 _120745 _120749 f)). Qed.
Lemma lem5769347 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769348 {_120745 _120749 : Type'} (f : type570 _120745 _120749) (x : _120745 -> _120749) : (f x) = (@I ((_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769347 (_120745 -> _120749) _120749 f x). Qed.
Lemma lem5769349 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term459 _120745 _120749 op s t f) = (term460 _120745 _120749 op s t f).
Proof. exact (@lem5769348 _120745 _120749 (term458 _120745 _120749 op s t) f). Qed.
Lemma lem5769350 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term456 _120745 _120749 op s t f) = (term460 _120745 _120749 op s t f).
Proof. exact (TRANS (@lem5769345 _120745 _120749 op s t f) (@lem5769349 _120745 _120749 op s t f)). Qed.
Lemma lem5769351 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term406 _120745 _120749 op s t f) = (term460 _120745 _120749 op s t f).
Proof. exact (TRANS (@lem5769332 _120745 _120749 op s t f) (@lem5769350 _120745 _120749 op s t f)). Qed.
Lemma lem5769352 {_120749 : Type'} (op : type1400 _120749) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5769361 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769362 {_120745 _120749 : Type'} (f : type750 _120745 _120749) (x : type1400 _120749) : (f x) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769361 (type1400 _120749) (type632 _120745 _120749) f x). Qed.
Lemma lem5769363 {_120745 _120749 : Type'} (op : type1400 _120749) : (@iterate _120749 _120745 op) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op).
Proof. exact (@lem5769362 _120745 _120749 (@iterate _120749 _120745) op). Qed.
Lemma lem5769364 {_120745 : Type'} (s : _120745 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5769365 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) : (@iterate _120749 _120745 op s) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op s).
Proof. exact (MK_COMB (@lem5769363 _120745 _120749 op) (@lem5769364 _120745 s)). Qed.
Lemma lem5769367 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769368 {_120745 _120749 : Type'} (f : type632 _120745 _120749) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769367 (_120745 -> Prop) (type570 _120745 _120749) f x). Qed.
Lemma lem5769369 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) : (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op s) = (term461 _120745 _120749 op s).
Proof. exact (@lem5769368 _120745 _120749 (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op) s). Qed.
Lemma lem5769370 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) : (@iterate _120749 _120745 op s) = (term461 _120745 _120749 op s).
Proof. exact (TRANS (@lem5769365 _120745 _120749 op s) (@lem5769369 _120745 _120749 op s)). Qed.
Lemma lem5769371 {_120745 _120749 : Type'} (f : _120745 -> _120749) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5769372 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (@iterate _120749 _120745 op s f) = (term462 _120745 _120749 op s f).
Proof. exact (MK_COMB (@lem5769370 _120745 _120749 op s) (@lem5769371 _120745 _120749 f)). Qed.
Lemma lem5769374 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769375 {_120745 _120749 : Type'} (f : type570 _120745 _120749) (x : _120745 -> _120749) : (f x) = (@I ((_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769374 (_120745 -> _120749) _120749 f x). Qed.
Lemma lem5769376 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term462 _120745 _120749 op s f) = (term463 _120745 _120749 op s f).
Proof. exact (@lem5769375 _120745 _120749 (term461 _120745 _120749 op s) f). Qed.
Lemma lem5769378 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (@iterate _120749 _120745 op s f) = (term463 _120745 _120749 op s f).
Proof. exact (TRANS (@lem5769372 _120745 _120749 op s f) (@lem5769376 _120745 _120749 op s f)). Qed.
Lemma lem5769387 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769388 {_120745 _120749 : Type'} (f : type750 _120745 _120749) (x : type1400 _120749) : (f x) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769387 (type1400 _120749) (type632 _120745 _120749) f x). Qed.
Lemma lem5769389 {_120745 _120749 : Type'} (op : type1400 _120749) : (@iterate _120749 _120745 op) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op).
Proof. exact (@lem5769388 _120745 _120749 (@iterate _120749 _120745) op). Qed.
Lemma lem5769390 {_120745 : Type'} (t : _120745 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5769391 {_120745 _120749 : Type'} (op : type1400 _120749) (t : _120745 -> Prop) : (@iterate _120749 _120745 op t) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op t).
Proof. exact (MK_COMB (@lem5769389 _120745 _120749 op) (@lem5769390 _120745 t)). Qed.
Lemma lem5769393 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769394 {_120745 _120749 : Type'} (f : type632 _120745 _120749) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769393 (_120745 -> Prop) (type570 _120745 _120749) f x). Qed.
Lemma lem5769395 {_120745 _120749 : Type'} (op : type1400 _120749) (t : _120745 -> Prop) : (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op t) = (term461 _120745 _120749 op t).
Proof. exact (@lem5769394 _120745 _120749 (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op) t). Qed.
Lemma lem5769396 {_120745 _120749 : Type'} (op : type1400 _120749) (t : _120745 -> Prop) : (@iterate _120749 _120745 op t) = (term461 _120745 _120749 op t).
Proof. exact (TRANS (@lem5769391 _120745 _120749 op t) (@lem5769395 _120745 _120749 op t)). Qed.
Lemma lem5769397 {_120745 _120749 : Type'} (f : _120745 -> _120749) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5769398 {_120745 _120749 : Type'} (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (@iterate _120749 _120745 op t f) = (term462 _120745 _120749 op t f).
Proof. exact (MK_COMB (@lem5769396 _120745 _120749 op t) (@lem5769397 _120745 _120749 f)). Qed.
Lemma lem5769400 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769401 {_120745 _120749 : Type'} (f : type570 _120745 _120749) (x : _120745 -> _120749) : (f x) = (@I ((_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769400 (_120745 -> _120749) _120749 f x). Qed.
Lemma lem5769402 {_120745 _120749 : Type'} (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term462 _120745 _120749 op t f) = (term463 _120745 _120749 op t f).
Proof. exact (@lem5769401 _120745 _120749 (term461 _120745 _120749 op t) f). Qed.
Lemma lem5769404 {_120745 _120749 : Type'} (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (@iterate _120749 _120745 op t f) = (term463 _120745 _120749 op t f).
Proof. exact (TRANS (@lem5769398 _120745 _120749 op t f) (@lem5769402 _120745 _120749 op t f)). Qed.
Lemma lem5769405 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term464 _120745 _120749 op s f) = (term465 _120745 _120749 op s f).
Proof. exact (MK_COMB (@lem5769352 _120749 op) (@lem5769378 _120745 _120749 op s f)). Qed.
Lemma lem5769406 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term407 _120745 _120749 s op t f) = (term466 _120745 _120749 s op t f).
Proof. exact (MK_COMB (@lem5769405 _120745 _120749 op s f) (@lem5769404 _120745 _120749 op t f)). Qed.
Lemma lem5769408 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769409 {_120749 : Type'} (f : type1400 _120749) (x : _120749) : (f x) = (@I (_120749 -> _120749 -> _120749) f x).
Proof. exact (@lem5769408 _120749 (_120749 -> _120749) f x). Qed.
Lemma lem5769410 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term465 _120745 _120749 op s f) = (term467 _120745 _120749 op s f).
Proof. exact (@lem5769409 _120749 op (term463 _120745 _120749 op s f)). Qed.
Lemma lem5769411 {_120745 _120749 : Type'} (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term463 _120745 _120749 op t f) = (term463 _120745 _120749 op t f).
Proof. exact (eq_refl (term463 _120745 _120749 op t f)). Qed.
Lemma lem5769412 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term466 _120745 _120749 s op t f) = (term468 _120745 _120749 s op t f).
Proof. exact (MK_COMB (@lem5769410 _120745 _120749 op s f) (@lem5769411 _120745 _120749 op t f)). Qed.
Lemma lem5769414 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769415 {_120749 : Type'} (f : _120749 -> _120749) (x : _120749) : (f x) = (@I (_120749 -> _120749) f x).
Proof. exact (@lem5769414 _120749 _120749 f x). Qed.
Lemma lem5769416 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term468 _120745 _120749 s op t f) = (term469 _120745 _120749 s op t f).
Proof. exact (@lem5769415 _120749 (term467 _120745 _120749 op s f) (term463 _120745 _120749 op t f)). Qed.
Lemma lem5769417 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term466 _120745 _120749 s op t f) = (term469 _120745 _120749 s op t f).
Proof. exact (TRANS (@lem5769412 _120745 _120749 s op t f) (@lem5769416 _120745 _120749 s op t f)). Qed.
Lemma lem5769418 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term407 _120745 _120749 s op t f) = (term469 _120745 _120749 s op t f).
Proof. exact (TRANS (@lem5769406 _120745 _120749 s op t f) (@lem5769417 _120745 _120749 s op t f)). Qed.
Lemma lem5769419 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term470 _120745 _120749 op s t f) = (term471 _120745 _120749 op s t f).
Proof. exact (MK_COMB (@lem5769309 _120749) (@lem5769351 _120745 _120749 op s t f)). Qed.
Lemma lem5769420 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : ((term406 _120745 _120749 op s t f) = (term407 _120745 _120749 s op t f)) = ((term460 _120745 _120749 op s t f) = (term469 _120745 _120749 s op t f)).
Proof. exact (MK_COMB (@lem5769419 _120745 _120749 op s t f) (@lem5769418 _120745 _120749 s op t f)). Qed.
Lemma lem5769421 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5769428 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769429 {_120745 : Type'} (f : type639 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5769428 (_120745 -> Prop) (type686 _120745) f x). Qed.
Lemma lem5769430 {_120745 : Type'} (s : _120745 -> Prop) : (@DISJOINT _120745 s) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@DISJOINT _120745) s).
Proof. exact (@lem5769429 _120745 (@DISJOINT _120745) s). Qed.
Lemma lem5769431 {_120745 : Type'} (t : _120745 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5769432 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@DISJOINT _120745 s t) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@DISJOINT _120745) s t).
Proof. exact (MK_COMB (@lem5769430 _120745 s) (@lem5769431 _120745 t)). Qed.
Lemma lem5769434 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769435 {_120745 : Type'} (f : type686 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5769434 (_120745 -> Prop) Prop f x). Qed.
Lemma lem5769436 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@DISJOINT _120745) s t) = (term472 _120745 s t).
Proof. exact (@lem5769435 _120745 (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@DISJOINT _120745) s) t). Qed.
Lemma lem5769438 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@DISJOINT _120745 s t) = (term472 _120745 s t).
Proof. exact (TRANS (@lem5769432 _120745 s t) (@lem5769436 _120745 s t)). Qed.
Lemma lem5769439 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term473 _120745 s t) = (term474 _120745 s t).
Proof. exact (MK_COMB (@lem5769421) (@lem5769438 _120745 s t)). Qed.
Lemma lem5769440 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5769445 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769446 {_120745 : Type'} (f : type686 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5769445 (_120745 -> Prop) Prop f x). Qed.
Lemma lem5769448 {_120745 : Type'} (t : _120745 -> Prop) : (@FINITE _120745 t) = (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) t).
Proof. exact (@lem5769446 _120745 (@FINITE _120745) t). Qed.
Lemma lem5769449 {_120745 : Type'} (t : _120745 -> Prop) : (term443 _120745 t) = (term444 _120745 t).
Proof. exact (MK_COMB (@lem5769440) (@lem5769448 _120745 t)). Qed.
Lemma lem5769450 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5769451 {_120745 : Type'} (t : _120745 -> Prop) : (term401 _120745 t) = (term445 _120745 t).
Proof. exact (MK_COMB (@lem5769450) (@lem5769449 _120745 t)). Qed.
Lemma lem5769452 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term400 _120745 s t) = (term475 _120745 s t).
Proof. exact (MK_COMB (@lem5769451 _120745 t) (@lem5769439 _120745 s t)). Qed.
Lemma lem5769453 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5769458 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769459 {_120745 : Type'} (f : type686 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5769458 (_120745 -> Prop) Prop f x). Qed.
Lemma lem5769461 {_120745 : Type'} (s : _120745 -> Prop) : (@FINITE _120745 s) = (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s).
Proof. exact (@lem5769459 _120745 (@FINITE _120745) s). Qed.
Lemma lem5769462 {_120745 : Type'} (s : _120745 -> Prop) : (term443 _120745 s) = (term444 _120745 s).
Proof. exact (MK_COMB (@lem5769453) (@lem5769461 _120745 s)). Qed.
Lemma lem5769463 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5769464 {_120745 : Type'} (s : _120745 -> Prop) : (term401 _120745 s) = (term445 _120745 s).
Proof. exact (MK_COMB (@lem5769463) (@lem5769462 _120745 s)). Qed.
Lemma lem5769465 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term403 _120745 s t) = (term476 _120745 s t).
Proof. exact (MK_COMB (@lem5769464 _120745 s) (@lem5769452 _120745 s t)). Qed.
Lemma lem5769466 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5769467 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term409 _120745 s t) = (term477 _120745 s t).
Proof. exact (MK_COMB (@lem5769466) (@lem5769465 _120745 s t)). Qed.
Lemma lem5769468 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term411 _120745 _120749 s op t f) = (term478 _120745 _120749 s op t f).
Proof. exact (MK_COMB (@lem5769467 _120745 s t) (@lem5769420 _120745 _120749 s op t f)). Qed.
Lemma lem5769469 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term413 _120745 _120749 s op f) = (term479 _120745 _120749 s op f).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5769468 _120745 _120749 s op t f)). Qed.
Lemma lem5769470 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5769471 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term414 _120745 _120749 s op f) = (term480 _120745 _120749 s op f).
Proof. exact (MK_COMB (@lem5769470 _120745) (@lem5769469 _120745 _120749 s op f)). Qed.
Lemma lem5769472 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term415 _120745 _120749 op f) = (term481 _120745 _120749 op f).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5769471 _120745 _120749 s op f)). Qed.
Lemma lem5769473 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5769474 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term416 _120745 _120749 op f) = (term482 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5769473 _120745) (@lem5769472 _120745 _120749 op f)). Qed.
Lemma lem5769475 {_120745 _120749 : Type'} (op : type1400 _120749) : (term417 _120745 _120749 op) = (term483 _120745 _120749 op).
Proof. exact (fun_ext (fun f : _120745 -> _120749 => @lem5769474 _120745 _120749 op f)). Qed.
Lemma lem5769476 {_120745 _120749 : Type'} : (@all (_120745 -> _120749)) = (@all (_120745 -> _120749)).
Proof. exact (eq_refl (@all (_120745 -> _120749))). Qed.
Lemma lem5769477 {_120745 _120749 : Type'} (op : type1400 _120749) : (term418 _120745 _120749 op) = (term484 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5769476 _120745 _120749) (@lem5769475 _120745 _120749 op)). Qed.
Lemma lem5769478 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5769483 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769484 {_120749 : Type'} (f : type403 _120749) (x : type1400 _120749) : (f x) = (@I ((_120749 -> _120749 -> _120749) -> Prop) f x).
Proof. exact (@lem5769483 (type1400 _120749) Prop f x). Qed.
Lemma lem5769486 {_120749 : Type'} (op : type1400 _120749) : (@monoidal _120749 op) = (@I ((_120749 -> _120749 -> _120749) -> Prop) (@monoidal _120749) op).
Proof. exact (@lem5769484 _120749 (@monoidal _120749) op). Qed.
Lemma lem5769487 {_120749 : Type'} (op : type1400 _120749) : (term485 _120749 op) = (term486 _120749 op).
Proof. exact (MK_COMB (@lem5769478) (@lem5769486 _120749 op)). Qed.
Lemma lem5769488 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5769489 {_120749 : Type'} (op : type1400 _120749) : (term419 _120749 op) = (term487 _120749 op).
Proof. exact (MK_COMB (@lem5769488) (@lem5769487 _120749 op)). Qed.
Lemma lem5769490 {_120745 _120749 : Type'} (op : type1400 _120749) : (term421 _120745 _120749 op) = (term488 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5769489 _120749 op) (@lem5769477 _120745 _120749 op)). Qed.
Lemma lem5769491 {_120745 _120749 : Type'} : (term422 _120745 _120749) = (term489 _120745 _120749).
Proof. exact (fun_ext (fun op : type1400 _120749 => @lem5769490 _120745 _120749 op)). Qed.
Lemma lem5769492 {_120749 : Type'} : (@all (_120749 -> _120749 -> _120749)) = (@all (_120749 -> _120749 -> _120749)).
Proof. exact (eq_refl (@all (_120749 -> _120749 -> _120749))). Qed.
Lemma lem5769493 {_120745 _120749 : Type'} : (term423 _120745 _120749) = (term490 _120745 _120749).
Proof. exact (MK_COMB (@lem5769492 _120749) (@lem5769491 _120745 _120749)). Qed.
Lemma lem5769494 {_120745 _120749 : Type'} (h1 : term186 _120745 _120749) : term490 _120745 _120749.
Proof. exact (EQ_MP (@lem5769493 _120745 _120749) (@lem5768304 _120745 _120749 h1)). Qed.
Lemma lem5769681 {_120745 : Type'} : (@DISJOINT _120745) = (@DISJOINT _120745).
Proof. exact (eq_refl (@DISJOINT _120745)). Qed.
Lemma lem5769688 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769689 {_120745 : Type'} (f : type636 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) f x).
Proof. exact (@lem5769688 (_120745 -> Prop) (type672 _120745) f x). Qed.
Lemma lem5769690 {_120745 : Type'} (s : _120745 -> Prop) : (@DIFF _120745 s) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s).
Proof. exact (@lem5769689 _120745 (@DIFF _120745) s). Qed.
Lemma lem5769691 {_120745 : Type'} (t : _120745 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5769692 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@DIFF _120745 s t) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s t).
Proof. exact (MK_COMB (@lem5769690 _120745 s) (@lem5769691 _120745 t)). Qed.
Lemma lem5769694 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769695 {_120745 : Type'} (f : type672 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> _120745 -> Prop) f x).
Proof. exact (@lem5769694 (_120745 -> Prop) (_120745 -> Prop) f x). Qed.
Lemma lem5769696 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s t) = (term429 _120745 s t).
Proof. exact (@lem5769695 _120745 (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s) t). Qed.
Lemma lem5769698 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@DIFF _120745 s t) = (term429 _120745 s t).
Proof. exact (TRANS (@lem5769692 _120745 s t) (@lem5769696 _120745 s t)). Qed.
Lemma lem5769699 {_120745 : Type'} (t : _120745 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5769700 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term491 _120745 s t) = (term492 _120745 s t).
Proof. exact (MK_COMB (@lem5769681 _120745) (@lem5769698 _120745 s t)). Qed.
Lemma lem5769701 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term8 _120745 s t) = (term493 _120745 s t).
Proof. exact (MK_COMB (@lem5769700 _120745 s t) (@lem5769699 _120745 t)). Qed.
Lemma lem5769703 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769704 {_120745 : Type'} (f : type639 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5769703 (_120745 -> Prop) (type686 _120745) f x). Qed.
Lemma lem5769705 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term492 _120745 s t) = (term494 _120745 s t).
Proof. exact (@lem5769704 _120745 (@DISJOINT _120745) (term429 _120745 s t)). Qed.
Lemma lem5769706 {_120745 : Type'} (t : _120745 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5769707 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term493 _120745 s t) = (term495 _120745 s t).
Proof. exact (MK_COMB (@lem5769705 _120745 s t) (@lem5769706 _120745 t)). Qed.
Lemma lem5769709 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769710 {_120745 : Type'} (f : type686 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5769709 (_120745 -> Prop) Prop f x). Qed.
Lemma lem5769711 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term495 _120745 s t) = (term496 _120745 s t).
Proof. exact (@lem5769710 _120745 (term494 _120745 s t) t). Qed.
Lemma lem5769712 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term493 _120745 s t) = (term496 _120745 s t).
Proof. exact (TRANS (@lem5769707 _120745 s t) (@lem5769711 _120745 s t)). Qed.
Lemma lem5769713 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term8 _120745 s t) = (term496 _120745 s t).
Proof. exact (TRANS (@lem5769701 _120745 s t) (@lem5769712 _120745 s t)). Qed.
Lemma lem5769716 {_120745 : Type'} : (@UNION _120745) = (@UNION _120745).
Proof. exact (eq_refl (@UNION _120745)). Qed.
Lemma lem5769723 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769724 {_120745 : Type'} (f : type636 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) f x).
Proof. exact (@lem5769723 (_120745 -> Prop) (type672 _120745) f x). Qed.
Lemma lem5769725 {_120745 : Type'} (s : _120745 -> Prop) : (@DIFF _120745 s) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s).
Proof. exact (@lem5769724 _120745 (@DIFF _120745) s). Qed.
Lemma lem5769726 {_120745 : Type'} (t : _120745 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5769727 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@DIFF _120745 s t) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s t).
Proof. exact (MK_COMB (@lem5769725 _120745 s) (@lem5769726 _120745 t)). Qed.
Lemma lem5769729 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769730 {_120745 : Type'} (f : type672 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> _120745 -> Prop) f x).
Proof. exact (@lem5769729 (_120745 -> Prop) (_120745 -> Prop) f x). Qed.
Lemma lem5769731 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s t) = (term429 _120745 s t).
Proof. exact (@lem5769730 _120745 (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s) t). Qed.
Lemma lem5769733 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@DIFF _120745 s t) = (term429 _120745 s t).
Proof. exact (TRANS (@lem5769727 _120745 s t) (@lem5769731 _120745 s t)). Qed.
Lemma lem5769734 {_120745 : Type'} (t : _120745 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5769735 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term497 _120745 s t) = (term498 _120745 s t).
Proof. exact (MK_COMB (@lem5769716 _120745) (@lem5769733 _120745 s t)). Qed.
Lemma lem5769736 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term4 _120745 s t) = (term499 _120745 s t).
Proof. exact (MK_COMB (@lem5769735 _120745 s t) (@lem5769734 _120745 t)). Qed.
Lemma lem5769738 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769739 {_120745 : Type'} (f : type636 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) f x).
Proof. exact (@lem5769738 (_120745 -> Prop) (type672 _120745) f x). Qed.
Lemma lem5769740 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term498 _120745 s t) = (term500 _120745 s t).
Proof. exact (@lem5769739 _120745 (@UNION _120745) (term429 _120745 s t)). Qed.
Lemma lem5769741 {_120745 : Type'} (t : _120745 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5769742 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term499 _120745 s t) = (term501 _120745 s t).
Proof. exact (MK_COMB (@lem5769740 _120745 s t) (@lem5769741 _120745 t)). Qed.
Lemma lem5769744 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769745 {_120745 : Type'} (f : type672 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> _120745 -> Prop) f x).
Proof. exact (@lem5769744 (_120745 -> Prop) (_120745 -> Prop) f x). Qed.
Lemma lem5769746 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term501 _120745 s t) = (term502 _120745 s t).
Proof. exact (@lem5769745 _120745 (term500 _120745 s t) t). Qed.
Lemma lem5769747 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term499 _120745 s t) = (term502 _120745 s t).
Proof. exact (TRANS (@lem5769742 _120745 s t) (@lem5769746 _120745 s t)). Qed.
Lemma lem5769748 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term4 _120745 s t) = (term502 _120745 s t).
Proof. exact (TRANS (@lem5769736 _120745 s t) (@lem5769747 _120745 s t)). Qed.
Lemma lem5769749 {_120745 : Type'} (s : _120745 -> Prop) : (@eq (_120745 -> Prop) s) = (@eq (_120745 -> Prop) s).
Proof. exact (eq_refl (@eq (_120745 -> Prop) s)). Qed.
Lemma lem5769750 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (s = (term4 _120745 s t)) = (s = (term502 _120745 s t)).
Proof. exact (MK_COMB (@lem5769749 _120745 s) (@lem5769748 _120745 s t)). Qed.
Lemma lem5769751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5769752 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term6 _120745 s t) = (term503 _120745 s t).
Proof. exact (MK_COMB (@lem5769751) (@lem5769750 _120745 s t)). Qed.
Lemma lem5769753 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term11 _120745 s t) = (term504 _120745 s t).
Proof. exact (MK_COMB (@lem5769752 _120745 s t) (@lem5769713 _120745 s t)). Qed.
Lemma lem5769754 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5769761 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769762 {_120745 : Type'} (f : type639 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5769761 (_120745 -> Prop) (type686 _120745) f x). Qed.
Lemma lem5769763 {_120745 : Type'} (t : _120745 -> Prop) : (@SUBSET _120745 t) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@SUBSET _120745) t).
Proof. exact (@lem5769762 _120745 (@SUBSET _120745) t). Qed.
Lemma lem5769764 {_120745 : Type'} (s : _120745 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5769765 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (@SUBSET _120745 t s) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@SUBSET _120745) t s).
Proof. exact (MK_COMB (@lem5769763 _120745 t) (@lem5769764 _120745 s)). Qed.
Lemma lem5769767 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769768 {_120745 : Type'} (f : type686 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5769767 (_120745 -> Prop) Prop f x). Qed.
Lemma lem5769769 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@SUBSET _120745) t s) = (term440 _120745 t s).
Proof. exact (@lem5769768 _120745 (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@SUBSET _120745) t) s). Qed.
Lemma lem5769771 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (@SUBSET _120745 t s) = (term440 _120745 t s).
Proof. exact (TRANS (@lem5769765 _120745 t s) (@lem5769769 _120745 t s)). Qed.
Lemma lem5769772 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term441 _120745 t s) = (term442 _120745 t s).
Proof. exact (MK_COMB (@lem5769754) (@lem5769771 _120745 t s)). Qed.
Lemma lem5769773 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5769774 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term505 _120745 t s) = (term506 _120745 t s).
Proof. exact (MK_COMB (@lem5769773) (@lem5769772 _120745 t s)). Qed.
Lemma lem5769775 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term424 _120745 s t) = (term507 _120745 s t).
Proof. exact (MK_COMB (@lem5769774 _120745 t s) (@lem5769753 _120745 s t)). Qed.
Lemma lem5769776 {_120745 : Type'} (s : _120745 -> Prop) : (term425 _120745 s) = (term508 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5769775 _120745 s t)). Qed.
Lemma lem5769777 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5769778 {_120745 : Type'} (s : _120745 -> Prop) : (term426 _120745 s) = (term509 _120745 s).
Proof. exact (MK_COMB (@lem5769777 _120745) (@lem5769776 _120745 s)). Qed.
Lemma lem5769779 {_120745 : Type'} : (term427 _120745) = (term510 _120745).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5769778 _120745 s)). Qed.
Lemma lem5769780 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5769781 {_120745 : Type'} : (term428 _120745) = (term511 _120745).
Proof. exact (MK_COMB (@lem5769780 _120745) (@lem5769779 _120745)). Qed.
Lemma lem5769782 {_120745 : Type'} (h1 : term182 _120745) : term511 _120745.
Proof. exact (EQ_MP (@lem5769781 _120745) (@lem5768524 _120745 h1)). Qed.
Lemma lem5769783 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5769784 {_120749 : Type'} : (@eq _120749) = (@eq _120749).
Proof. exact (eq_refl (@eq _120749)). Qed.
Lemma lem5769785 {_120749 : Type'} (op : type1400 _120749) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5769794 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769795 {_120745 : Type'} (f : type636 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) f x).
Proof. exact (@lem5769794 (_120745 -> Prop) (type672 _120745) f x). Qed.
Lemma lem5769796 {_120745 : Type'} (s : _120745 -> Prop) : (@DIFF _120745 s) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s).
Proof. exact (@lem5769795 _120745 (@DIFF _120745) s). Qed.
Lemma lem5769797 {_120745 : Type'} (t : _120745 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5769798 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@DIFF _120745 s t) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s t).
Proof. exact (MK_COMB (@lem5769796 _120745 s) (@lem5769797 _120745 t)). Qed.
Lemma lem5769800 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769801 {_120745 : Type'} (f : type672 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> _120745 -> Prop) f x).
Proof. exact (@lem5769800 (_120745 -> Prop) (_120745 -> Prop) f x). Qed.
Lemma lem5769802 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s t) = (term429 _120745 s t).
Proof. exact (@lem5769801 _120745 (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> _120745 -> Prop) (@DIFF _120745) s) t). Qed.
Lemma lem5769804 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (@DIFF _120745 s t) = (term429 _120745 s t).
Proof. exact (TRANS (@lem5769798 _120745 s t) (@lem5769802 _120745 s t)). Qed.
Lemma lem5769805 {_120745 _120749 : Type'} (f : _120745 -> _120749) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5769806 {_120745 _120749 : Type'} (op : type1400 _120749) : (@iterate _120749 _120745 op) = (@iterate _120749 _120745 op).
Proof. exact (eq_refl (@iterate _120749 _120745 op)). Qed.
Lemma lem5769807 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) : (term512 _120745 _120749 op s t) = (term513 _120745 _120749 op s t).
Proof. exact (MK_COMB (@lem5769806 _120745 _120749 op) (@lem5769804 _120745 s t)). Qed.
Lemma lem5769808 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term514 _120745 _120749 op s t f) = (term515 _120745 _120749 op s t f).
Proof. exact (MK_COMB (@lem5769807 _120745 _120749 op s t) (@lem5769805 _120745 _120749 f)). Qed.
Lemma lem5769810 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769811 {_120745 _120749 : Type'} (f : type750 _120745 _120749) (x : type1400 _120749) : (f x) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769810 (type1400 _120749) (type632 _120745 _120749) f x). Qed.
Lemma lem5769812 {_120745 _120749 : Type'} (op : type1400 _120749) : (@iterate _120749 _120745 op) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op).
Proof. exact (@lem5769811 _120745 _120749 (@iterate _120749 _120745) op). Qed.
Lemma lem5769813 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term429 _120745 s t) = (term429 _120745 s t).
Proof. exact (eq_refl (term429 _120745 s t)). Qed.
Lemma lem5769814 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) : (term513 _120745 _120749 op s t) = (term516 _120745 _120749 op s t).
Proof. exact (MK_COMB (@lem5769812 _120745 _120749 op) (@lem5769813 _120745 s t)). Qed.
Lemma lem5769816 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769817 {_120745 _120749 : Type'} (f : type632 _120745 _120749) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769816 (_120745 -> Prop) (type570 _120745 _120749) f x). Qed.
Lemma lem5769818 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) : (term516 _120745 _120749 op s t) = (term517 _120745 _120749 op s t).
Proof. exact (@lem5769817 _120745 _120749 (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op) (term429 _120745 s t)). Qed.
Lemma lem5769819 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) : (term513 _120745 _120749 op s t) = (term517 _120745 _120749 op s t).
Proof. exact (TRANS (@lem5769814 _120745 _120749 op s t) (@lem5769818 _120745 _120749 op s t)). Qed.
Lemma lem5769820 {_120745 _120749 : Type'} (f : _120745 -> _120749) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5769821 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term515 _120745 _120749 op s t f) = (term518 _120745 _120749 op s t f).
Proof. exact (MK_COMB (@lem5769819 _120745 _120749 op s t) (@lem5769820 _120745 _120749 f)). Qed.
Lemma lem5769823 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769824 {_120745 _120749 : Type'} (f : type570 _120745 _120749) (x : _120745 -> _120749) : (f x) = (@I ((_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769823 (_120745 -> _120749) _120749 f x). Qed.
Lemma lem5769825 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term518 _120745 _120749 op s t f) = (term519 _120745 _120749 op s t f).
Proof. exact (@lem5769824 _120745 _120749 (term517 _120745 _120749 op s t) f). Qed.
Lemma lem5769826 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term515 _120745 _120749 op s t f) = (term519 _120745 _120749 op s t f).
Proof. exact (TRANS (@lem5769821 _120745 _120749 op s t f) (@lem5769825 _120745 _120749 op s t f)). Qed.
Lemma lem5769827 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term514 _120745 _120749 op s t f) = (term519 _120745 _120749 op s t f).
Proof. exact (TRANS (@lem5769808 _120745 _120749 op s t f) (@lem5769826 _120745 _120749 op s t f)). Qed.
Lemma lem5769836 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769837 {_120745 _120749 : Type'} (f : type750 _120745 _120749) (x : type1400 _120749) : (f x) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769836 (type1400 _120749) (type632 _120745 _120749) f x). Qed.
Lemma lem5769838 {_120745 _120749 : Type'} (op : type1400 _120749) : (@iterate _120749 _120745 op) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op).
Proof. exact (@lem5769837 _120745 _120749 (@iterate _120749 _120745) op). Qed.
Lemma lem5769839 {_120745 : Type'} (t : _120745 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5769840 {_120745 _120749 : Type'} (op : type1400 _120749) (t : _120745 -> Prop) : (@iterate _120749 _120745 op t) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op t).
Proof. exact (MK_COMB (@lem5769838 _120745 _120749 op) (@lem5769839 _120745 t)). Qed.
Lemma lem5769842 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769843 {_120745 _120749 : Type'} (f : type632 _120745 _120749) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769842 (_120745 -> Prop) (type570 _120745 _120749) f x). Qed.
Lemma lem5769844 {_120745 _120749 : Type'} (op : type1400 _120749) (t : _120745 -> Prop) : (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op t) = (term461 _120745 _120749 op t).
Proof. exact (@lem5769843 _120745 _120749 (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op) t). Qed.
Lemma lem5769845 {_120745 _120749 : Type'} (op : type1400 _120749) (t : _120745 -> Prop) : (@iterate _120749 _120745 op t) = (term461 _120745 _120749 op t).
Proof. exact (TRANS (@lem5769840 _120745 _120749 op t) (@lem5769844 _120745 _120749 op t)). Qed.
Lemma lem5769846 {_120745 _120749 : Type'} (f : _120745 -> _120749) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5769847 {_120745 _120749 : Type'} (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (@iterate _120749 _120745 op t f) = (term462 _120745 _120749 op t f).
Proof. exact (MK_COMB (@lem5769845 _120745 _120749 op t) (@lem5769846 _120745 _120749 f)). Qed.
Lemma lem5769849 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769850 {_120745 _120749 : Type'} (f : type570 _120745 _120749) (x : _120745 -> _120749) : (f x) = (@I ((_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769849 (_120745 -> _120749) _120749 f x). Qed.
Lemma lem5769851 {_120745 _120749 : Type'} (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term462 _120745 _120749 op t f) = (term463 _120745 _120749 op t f).
Proof. exact (@lem5769850 _120745 _120749 (term461 _120745 _120749 op t) f). Qed.
Lemma lem5769853 {_120745 _120749 : Type'} (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (@iterate _120749 _120745 op t f) = (term463 _120745 _120749 op t f).
Proof. exact (TRANS (@lem5769847 _120745 _120749 op t f) (@lem5769851 _120745 _120749 op t f)). Qed.
Lemma lem5769854 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term520 _120745 _120749 op s t f) = (term521 _120745 _120749 op s t f).
Proof. exact (MK_COMB (@lem5769785 _120749 op) (@lem5769827 _120745 _120749 op s t f)). Qed.
Lemma lem5769855 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term282 _120745 _120749 s op t f) = (term522 _120745 _120749 s op t f).
Proof. exact (MK_COMB (@lem5769854 _120745 _120749 op s t f) (@lem5769853 _120745 _120749 op t f)). Qed.
Lemma lem5769857 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769858 {_120749 : Type'} (f : type1400 _120749) (x : _120749) : (f x) = (@I (_120749 -> _120749 -> _120749) f x).
Proof. exact (@lem5769857 _120749 (_120749 -> _120749) f x). Qed.
Lemma lem5769859 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term521 _120745 _120749 op s t f) = (term523 _120745 _120749 op s t f).
Proof. exact (@lem5769858 _120749 op (term519 _120745 _120749 op s t f)). Qed.
Lemma lem5769860 {_120745 _120749 : Type'} (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term463 _120745 _120749 op t f) = (term463 _120745 _120749 op t f).
Proof. exact (eq_refl (term463 _120745 _120749 op t f)). Qed.
Lemma lem5769861 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term522 _120745 _120749 s op t f) = (term524 _120745 _120749 s op t f).
Proof. exact (MK_COMB (@lem5769859 _120745 _120749 op s t f) (@lem5769860 _120745 _120749 op t f)). Qed.
Lemma lem5769863 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769864 {_120749 : Type'} (f : _120749 -> _120749) (x : _120749) : (f x) = (@I (_120749 -> _120749) f x).
Proof. exact (@lem5769863 _120749 _120749 f x). Qed.
Lemma lem5769865 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term524 _120745 _120749 s op t f) = (term525 _120745 _120749 s op t f).
Proof. exact (@lem5769864 _120749 (term523 _120745 _120749 op s t f) (term463 _120745 _120749 op t f)). Qed.
Lemma lem5769866 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term522 _120745 _120749 s op t f) = (term525 _120745 _120749 s op t f).
Proof. exact (TRANS (@lem5769861 _120745 _120749 s op t f) (@lem5769865 _120745 _120749 s op t f)). Qed.
Lemma lem5769867 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term282 _120745 _120749 s op t f) = (term525 _120745 _120749 s op t f).
Proof. exact (TRANS (@lem5769855 _120745 _120749 s op t f) (@lem5769866 _120745 _120749 s op t f)). Qed.
Lemma lem5769876 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769877 {_120745 _120749 : Type'} (f : type750 _120745 _120749) (x : type1400 _120749) : (f x) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769876 (type1400 _120749) (type632 _120745 _120749) f x). Qed.
Lemma lem5769878 {_120745 _120749 : Type'} (op : type1400 _120749) : (@iterate _120749 _120745 op) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op).
Proof. exact (@lem5769877 _120745 _120749 (@iterate _120749 _120745) op). Qed.
Lemma lem5769879 {_120745 : Type'} (s : _120745 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5769880 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) : (@iterate _120749 _120745 op s) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op s).
Proof. exact (MK_COMB (@lem5769878 _120745 _120749 op) (@lem5769879 _120745 s)). Qed.
Lemma lem5769882 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769883 {_120745 _120749 : Type'} (f : type632 _120745 _120749) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769882 (_120745 -> Prop) (type570 _120745 _120749) f x). Qed.
Lemma lem5769884 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) : (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op s) = (term461 _120745 _120749 op s).
Proof. exact (@lem5769883 _120745 _120749 (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op) s). Qed.
Lemma lem5769885 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) : (@iterate _120749 _120745 op s) = (term461 _120745 _120749 op s).
Proof. exact (TRANS (@lem5769880 _120745 _120749 op s) (@lem5769884 _120745 _120749 op s)). Qed.
Lemma lem5769886 {_120745 _120749 : Type'} (f : _120745 -> _120749) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5769887 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (@iterate _120749 _120745 op s f) = (term462 _120745 _120749 op s f).
Proof. exact (MK_COMB (@lem5769885 _120745 _120749 op s) (@lem5769886 _120745 _120749 f)). Qed.
Lemma lem5769889 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769890 {_120745 _120749 : Type'} (f : type570 _120745 _120749) (x : _120745 -> _120749) : (f x) = (@I ((_120745 -> _120749) -> _120749) f x).
Proof. exact (@lem5769889 (_120745 -> _120749) _120749 f x). Qed.
Lemma lem5769891 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term462 _120745 _120749 op s f) = (term463 _120745 _120749 op s f).
Proof. exact (@lem5769890 _120745 _120749 (term461 _120745 _120749 op s) f). Qed.
Lemma lem5769893 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (@iterate _120749 _120745 op s f) = (term463 _120745 _120749 op s f).
Proof. exact (TRANS (@lem5769887 _120745 _120749 op s f) (@lem5769891 _120745 _120749 op s f)). Qed.
Lemma lem5769894 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term526 _120745 _120749 s op t f) = (term527 _120745 _120749 s op t f).
Proof. exact (MK_COMB (@lem5769784 _120749) (@lem5769867 _120745 _120749 s op t f)). Qed.
Lemma lem5769895 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : ((term282 _120745 _120749 s op t f) = (@iterate _120749 _120745 op s f)) = ((term525 _120745 _120749 s op t f) = (term463 _120745 _120749 op s f)).
Proof. exact (MK_COMB (@lem5769894 _120745 _120749 s op t f) (@lem5769893 _120745 _120749 op s f)). Qed.
Lemma lem5769896 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term528 _120745 _120749 t op s f) = (term529 _120745 _120749 t op s f).
Proof. exact (MK_COMB (@lem5769783) (@lem5769895 _120745 _120749 t op s f)). Qed.
Lemma lem5769903 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769904 {_120745 : Type'} (f : type639 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5769903 (_120745 -> Prop) (type686 _120745) f x). Qed.
Lemma lem5769905 {_120745 : Type'} (t : _120745 -> Prop) : (@SUBSET _120745 t) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@SUBSET _120745) t).
Proof. exact (@lem5769904 _120745 (@SUBSET _120745) t). Qed.
Lemma lem5769906 {_120745 : Type'} (s : _120745 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5769907 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (@SUBSET _120745 t s) = (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@SUBSET _120745) t s).
Proof. exact (MK_COMB (@lem5769905 _120745 t) (@lem5769906 _120745 s)). Qed.
Lemma lem5769909 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769910 {_120745 : Type'} (f : type686 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5769909 (_120745 -> Prop) Prop f x). Qed.
Lemma lem5769911 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@SUBSET _120745) t s) = (term440 _120745 t s).
Proof. exact (@lem5769910 _120745 (@I ((_120745 -> Prop) -> (_120745 -> Prop) -> Prop) (@SUBSET _120745) t) s). Qed.
Lemma lem5769913 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (@SUBSET _120745 t s) = (term440 _120745 t s).
Proof. exact (TRANS (@lem5769907 _120745 t s) (@lem5769911 _120745 t s)). Qed.
Lemma lem5769918 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769919 {_120745 : Type'} (f : type686 _120745) (x : _120745 -> Prop) : (f x) = (@I ((_120745 -> Prop) -> Prop) f x).
Proof. exact (@lem5769918 (_120745 -> Prop) Prop f x). Qed.
Lemma lem5769921 {_120745 : Type'} (s : _120745 -> Prop) : (@FINITE _120745 s) = (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s).
Proof. exact (@lem5769919 _120745 (@FINITE _120745) s). Qed.
Lemma lem5769922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5769923 {_120745 : Type'} (s : _120745 -> Prop) : (term530 _120745 s) = (term531 _120745 s).
Proof. exact (MK_COMB (@lem5769922) (@lem5769921 _120745 s)). Qed.
Lemma lem5769924 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term281 _120745 t s) = (term532 _120745 t s).
Proof. exact (MK_COMB (@lem5769923 _120745 s) (@lem5769913 _120745 t s)). Qed.
Lemma lem5769925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5769926 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term533 _120745 t s) = (term534 _120745 t s).
Proof. exact (MK_COMB (@lem5769925) (@lem5769924 _120745 t s)). Qed.
Lemma lem5769927 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term280 _120745 _120749 t op s f) = (term535 _120745 _120749 t op s f).
Proof. exact (MK_COMB (@lem5769926 _120745 t s) (@lem5769896 _120745 _120749 t op s f)). Qed.
Lemma lem5769932 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5769933 {_120749 : Type'} (f : type403 _120749) (x : type1400 _120749) : (f x) = (@I ((_120749 -> _120749 -> _120749) -> Prop) f x).
Proof. exact (@lem5769932 (type1400 _120749) Prop f x). Qed.
Lemma lem5769935 {_120749 : Type'} (op : type1400 _120749) : (@monoidal _120749 op) = (@I ((_120749 -> _120749 -> _120749) -> Prop) (@monoidal _120749) op).
Proof. exact (@lem5769933 _120749 (@monoidal _120749) op). Qed.
Lemma lem5769936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5769937 {_120749 : Type'} (op : type1400 _120749) : (term308 _120749 op) = (term536 _120749 op).
Proof. exact (MK_COMB (@lem5769936) (@lem5769935 _120749 op)). Qed.
Lemma lem5769938 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term358 _120745 _120749 t op s f) = (term537 _120745 _120749 t op s f).
Proof. exact (MK_COMB (@lem5769937 _120749 op) (@lem5769927 _120745 _120749 t op s f)). Qed.
Lemma lem5769939 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term537 _120745 _120749 t op s f.
Proof. exact (EQ_MP (@lem5769938 _120745 _120749 t op s f) (@lem5768528 _120745 _120749 t op s f h1)). Qed.
Lemma lem5769940 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term535 _120745 _120749 t op s f.
Proof. exact (proj2 (@lem5769939 _120745 _120749 t op s f h1)). Qed.
Lemma lem5769943 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term532 _120745 t s.
Proof. exact (proj1 (@lem5769940 _120745 _120749 t op s f h1)). Qed.
Lemma lem5769961 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term435 _120745 t s) = (term435 _120745 t s).
Proof. exact (eq_refl (term435 _120745 t s)). Qed.
Lemma lem5769962 {_120745 : Type'} (s : _120745 -> Prop) : (term436 _120745 s) = (term436 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5769961 _120745 t s)). Qed.
Lemma lem5769963 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5769964 {_120745 : Type'} (s : _120745 -> Prop) : (term437 _120745 s) = (term437 _120745 s).
Proof. exact (MK_COMB (@lem5769963 _120745) (@lem5769962 _120745 s)). Qed.
Lemma lem5769965 {_120745 : Type'} : (term438 _120745) = (term438 _120745).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5769964 _120745 s)). Qed.
Lemma lem5769966 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5769968 {_120745 : Type'} : (term439 _120745) = (term439 _120745).
Proof. exact (MK_COMB (@lem5769966 _120745) (@lem5769965 _120745)). Qed.
Lemma lem5769969 {_120745 : Type'} (h1 : term191 _120745) : term439 _120745.
Proof. exact (EQ_MP (@lem5769968 _120745) (@lem5768608 _120745 h1)). Qed.
Lemma lem5770019 {A : Type'} (P : A -> Prop) (Q : Prop) : (term379 A P Q) = (term378 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5770020 {_120745 : Type'} (P : type686 _120745) (Q : Prop) : (term381 _120745 P Q) = (term380 _120745 P Q).
Proof. exact (@lem5770019 (_120745 -> Prop) P Q). Qed.
Lemma lem5770021 {_120745 : Type'} (s : _120745 -> Prop) : (term538 _120745 s) = (term539 _120745 s).
Proof. exact (@lem5770020 _120745 (term447 _120745 s) (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s)). Qed.
Lemma lem5770022 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term540 _120745 s t) = (term446 _120745 s t).
Proof. exact (eq_refl (term540 _120745 s t)). Qed.
Lemma lem5770023 {_120745 : Type'} (s : _120745 -> Prop) : (term541 _120745 s) = (term447 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5770022 _120745 s t)). Qed.
Lemma lem5770024 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5770025 {_120745 : Type'} (s : _120745 -> Prop) : (term542 _120745 s) = (term448 _120745 s).
Proof. exact (MK_COMB (@lem5770024 _120745) (@lem5770023 _120745 s)). Qed.
Lemma lem5770026 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5770027 {_120745 : Type'} (s : _120745 -> Prop) : (term543 _120745 s) = (term449 _120745 s).
Proof. exact (MK_COMB (@lem5770026) (@lem5770025 _120745 s)). Qed.
Lemma lem5770028 {_120745 : Type'} (s : _120745 -> Prop) : (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s) = (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s).
Proof. exact (eq_refl (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s)). Qed.
Lemma lem5770029 {_120745 : Type'} (s : _120745 -> Prop) : (term538 _120745 s) = (term450 _120745 s).
Proof. exact (MK_COMB (@lem5770027 _120745 s) (@lem5770028 _120745 s)). Qed.
Lemma lem5770030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5770031 {_120745 : Type'} (s : _120745 -> Prop) : (term544 _120745 s) = (term545 _120745 s).
Proof. exact (MK_COMB (@lem5770030) (@lem5770029 _120745 s)). Qed.
Lemma lem5770032 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term540 _120745 s t) = (term446 _120745 s t).
Proof. exact (eq_refl (term540 _120745 s t)). Qed.
Lemma lem5770033 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5770034 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term546 _120745 s t) = (term547 _120745 s t).
Proof. exact (MK_COMB (@lem5770033) (@lem5770032 _120745 s t)). Qed.
Lemma lem5770035 {_120745 : Type'} (s : _120745 -> Prop) : (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s) = (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s).
Proof. exact (eq_refl (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s)). Qed.
Lemma lem5770036 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term548 _120745 t s) = (term549 _120745 t s).
Proof. exact (MK_COMB (@lem5770034 _120745 s t) (@lem5770035 _120745 s)). Qed.
Lemma lem5770037 {_120745 : Type'} (s : _120745 -> Prop) : (term550 _120745 s) = (term551 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5770036 _120745 t s)). Qed.
Lemma lem5770038 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5770039 {_120745 : Type'} (s : _120745 -> Prop) : (term539 _120745 s) = (term552 _120745 s).
Proof. exact (MK_COMB (@lem5770038 _120745) (@lem5770037 _120745 s)). Qed.
Lemma lem5770040 {_120745 : Type'} (s : _120745 -> Prop) : ((term538 _120745 s) = (term539 _120745 s)) = ((term450 _120745 s) = (term552 _120745 s)).
Proof. exact (MK_COMB (@lem5770031 _120745 s) (@lem5770039 _120745 s)). Qed.
Lemma lem5770041 {_120745 : Type'} (s : _120745 -> Prop) : (term450 _120745 s) = (term552 _120745 s).
Proof. exact (EQ_MP (@lem5770040 _120745 s) (@lem5770021 _120745 s)). Qed.
Lemma lem5770042 {_120745 : Type'} : (term451 _120745) = (term553 _120745).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5770041 _120745 s)). Qed.
Lemma lem5770043 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5770044 {_120745 : Type'} : (term452 _120745) = (term554 _120745).
Proof. exact (MK_COMB (@lem5770043 _120745) (@lem5770042 _120745)). Qed.
Lemma lem5770057 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term549 _120745 t s) = (term549 _120745 t s).
Proof. exact (eq_refl (term549 _120745 t s)). Qed.
Lemma lem5770058 {_120745 : Type'} (s : _120745 -> Prop) : (term551 _120745 s) = (term551 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5770057 _120745 t s)). Qed.
Lemma lem5770059 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5770060 {_120745 : Type'} (s : _120745 -> Prop) : (term552 _120745 s) = (term552 _120745 s).
Proof. exact (MK_COMB (@lem5770059 _120745) (@lem5770058 _120745 s)). Qed.
Lemma lem5770061 {_120745 : Type'} : (term553 _120745) = (term553 _120745).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5770060 _120745 s)). Qed.
Lemma lem5770062 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5770063 {_120745 : Type'} : (term554 _120745) = (term554 _120745).
Proof. exact (MK_COMB (@lem5770062 _120745) (@lem5770061 _120745)). Qed.
Lemma lem5770064 {_120745 : Type'} : (term452 _120745) = (term554 _120745).
Proof. exact (TRANS (@lem5770044 _120745) (@lem5770063 _120745)). Qed.
Lemma lem5770065 {_120745 : Type'} (h1 : term190 _120745) : term554 _120745.
Proof. exact (EQ_MP (@lem5770064 _120745) (@lem5768708 _120745 h1)). Qed.
Lemma lem5770287 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5770288 {_120745 _120749 : Type'} (P : Prop) (Q : type572 _120745 _120749) : (term557 _120745 _120749 P Q) = (term558 _120745 _120749 P Q).
Proof. exact (@lem5770287 (_120745 -> _120749) P Q). Qed.
Lemma lem5770289 {_120745 _120749 : Type'} (op : type1400 _120749) : (term559 _120745 _120749 op) = (term560 _120745 _120749 op).
Proof. exact (@lem5770288 _120745 _120749 (term486 _120749 op) (term483 _120745 _120749 op)). Qed.
Lemma lem5770290 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term561 _120745 _120749 op f) = (term482 _120745 _120749 op f).
Proof. exact (eq_refl (term561 _120745 _120749 op f)). Qed.
Lemma lem5770291 {_120745 _120749 : Type'} (op : type1400 _120749) : (term562 _120745 _120749 op) = (term483 _120745 _120749 op).
Proof. exact (fun_ext (fun f : _120745 -> _120749 => @lem5770290 _120745 _120749 op f)). Qed.
Lemma lem5770292 {_120745 _120749 : Type'} : (@all (_120745 -> _120749)) = (@all (_120745 -> _120749)).
Proof. exact (eq_refl (@all (_120745 -> _120749))). Qed.
Lemma lem5770293 {_120745 _120749 : Type'} (op : type1400 _120749) : (term563 _120745 _120749 op) = (term484 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5770292 _120745 _120749) (@lem5770291 _120745 _120749 op)). Qed.
Lemma lem5770294 {_120749 : Type'} (op : type1400 _120749) : (term487 _120749 op) = (term487 _120749 op).
Proof. exact (eq_refl (term487 _120749 op)). Qed.
Lemma lem5770295 {_120745 _120749 : Type'} (op : type1400 _120749) : (term559 _120745 _120749 op) = (term488 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5770294 _120749 op) (@lem5770293 _120745 _120749 op)). Qed.
Lemma lem5770296 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5770297 {_120745 _120749 : Type'} (op : type1400 _120749) : (term564 _120745 _120749 op) = (term565 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5770296) (@lem5770295 _120745 _120749 op)). Qed.
Lemma lem5770298 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term561 _120745 _120749 op f) = (term482 _120745 _120749 op f).
Proof. exact (eq_refl (term561 _120745 _120749 op f)). Qed.
Lemma lem5770299 {_120749 : Type'} (op : type1400 _120749) : (term487 _120749 op) = (term487 _120749 op).
Proof. exact (eq_refl (term487 _120749 op)). Qed.
Lemma lem5770300 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term566 _120745 _120749 op f) = (term567 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5770299 _120749 op) (@lem5770298 _120745 _120749 op f)). Qed.
Lemma lem5770301 {_120745 _120749 : Type'} (op : type1400 _120749) : (term568 _120745 _120749 op) = (term569 _120745 _120749 op).
Proof. exact (fun_ext (fun f : _120745 -> _120749 => @lem5770300 _120745 _120749 op f)). Qed.
Lemma lem5770302 {_120745 _120749 : Type'} : (@all (_120745 -> _120749)) = (@all (_120745 -> _120749)).
Proof. exact (eq_refl (@all (_120745 -> _120749))). Qed.
Lemma lem5770303 {_120745 _120749 : Type'} (op : type1400 _120749) : (term560 _120745 _120749 op) = (term570 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5770302 _120745 _120749) (@lem5770301 _120745 _120749 op)). Qed.
Lemma lem5770304 {_120745 _120749 : Type'} (op : type1400 _120749) : ((term559 _120745 _120749 op) = (term560 _120745 _120749 op)) = ((term488 _120745 _120749 op) = (term570 _120745 _120749 op)).
Proof. exact (MK_COMB (@lem5770297 _120745 _120749 op) (@lem5770303 _120745 _120749 op)). Qed.
Lemma lem5770305 {_120745 _120749 : Type'} (op : type1400 _120749) : (term488 _120745 _120749 op) = (term570 _120745 _120749 op).
Proof. exact (EQ_MP (@lem5770304 _120745 _120749 op) (@lem5770289 _120745 _120749 op)). Qed.
Lemma lem5770307 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5770308 {_120745 : Type'} (P : Prop) (Q : type686 _120745) : (term571 _120745 P Q) = (term572 _120745 P Q).
Proof. exact (@lem5770307 (_120745 -> Prop) P Q). Qed.
Lemma lem5770309 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term573 _120745 _120749 op f) = (term574 _120745 _120749 op f).
Proof. exact (@lem5770308 _120745 (term486 _120749 op) (term481 _120745 _120749 op f)). Qed.
Lemma lem5770310 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term575 _120745 _120749 op f s) = (term480 _120745 _120749 s op f).
Proof. exact (eq_refl (term575 _120745 _120749 op f s)). Qed.
Lemma lem5770311 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term576 _120745 _120749 op f) = (term481 _120745 _120749 op f).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5770310 _120745 _120749 s op f)). Qed.
Lemma lem5770312 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5770313 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term577 _120745 _120749 op f) = (term482 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5770312 _120745) (@lem5770311 _120745 _120749 op f)). Qed.
Lemma lem5770314 {_120749 : Type'} (op : type1400 _120749) : (term487 _120749 op) = (term487 _120749 op).
Proof. exact (eq_refl (term487 _120749 op)). Qed.
Lemma lem5770315 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term573 _120745 _120749 op f) = (term567 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5770314 _120749 op) (@lem5770313 _120745 _120749 op f)). Qed.
Lemma lem5770316 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5770317 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term578 _120745 _120749 op f) = (term579 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5770316) (@lem5770315 _120745 _120749 op f)). Qed.
Lemma lem5770318 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term575 _120745 _120749 op f s) = (term480 _120745 _120749 s op f).
Proof. exact (eq_refl (term575 _120745 _120749 op f s)). Qed.
Lemma lem5770319 {_120749 : Type'} (op : type1400 _120749) : (term487 _120749 op) = (term487 _120749 op).
Proof. exact (eq_refl (term487 _120749 op)). Qed.
Lemma lem5770320 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term580 _120745 _120749 op f s) = (term581 _120745 _120749 s op f).
Proof. exact (MK_COMB (@lem5770319 _120749 op) (@lem5770318 _120745 _120749 s op f)). Qed.
Lemma lem5770321 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term582 _120745 _120749 op f) = (term583 _120745 _120749 op f).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5770320 _120745 _120749 s op f)). Qed.
Lemma lem5770322 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5770323 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term574 _120745 _120749 op f) = (term584 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5770322 _120745) (@lem5770321 _120745 _120749 op f)). Qed.
Lemma lem5770324 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : ((term573 _120745 _120749 op f) = (term574 _120745 _120749 op f)) = ((term567 _120745 _120749 op f) = (term584 _120745 _120749 op f)).
Proof. exact (MK_COMB (@lem5770317 _120745 _120749 op f) (@lem5770323 _120745 _120749 op f)). Qed.
Lemma lem5770325 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term567 _120745 _120749 op f) = (term584 _120745 _120749 op f).
Proof. exact (EQ_MP (@lem5770324 _120745 _120749 op f) (@lem5770309 _120745 _120749 op f)). Qed.
Lemma lem5770327 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5770328 {_120745 : Type'} (P : Prop) (Q : type686 _120745) : (term571 _120745 P Q) = (term572 _120745 P Q).
Proof. exact (@lem5770327 (_120745 -> Prop) P Q). Qed.
Lemma lem5770329 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term585 _120745 _120749 s op f) = (term586 _120745 _120749 s op f).
Proof. exact (@lem5770328 _120745 (term486 _120749 op) (term479 _120745 _120749 s op f)). Qed.
Lemma lem5770330 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term587 _120745 _120749 s op f t) = (term478 _120745 _120749 s op t f).
Proof. exact (eq_refl (term587 _120745 _120749 s op f t)). Qed.
Lemma lem5770331 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term588 _120745 _120749 s op f) = (term479 _120745 _120749 s op f).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5770330 _120745 _120749 s op t f)). Qed.
Lemma lem5770332 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5770333 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term589 _120745 _120749 s op f) = (term480 _120745 _120749 s op f).
Proof. exact (MK_COMB (@lem5770332 _120745) (@lem5770331 _120745 _120749 s op f)). Qed.
Lemma lem5770334 {_120749 : Type'} (op : type1400 _120749) : (term487 _120749 op) = (term487 _120749 op).
Proof. exact (eq_refl (term487 _120749 op)). Qed.
Lemma lem5770335 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term585 _120745 _120749 s op f) = (term581 _120745 _120749 s op f).
Proof. exact (MK_COMB (@lem5770334 _120749 op) (@lem5770333 _120745 _120749 s op f)). Qed.
Lemma lem5770336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5770337 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term590 _120745 _120749 s op f) = (term591 _120745 _120749 s op f).
Proof. exact (MK_COMB (@lem5770336) (@lem5770335 _120745 _120749 s op f)). Qed.
Lemma lem5770338 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term587 _120745 _120749 s op f t) = (term478 _120745 _120749 s op t f).
Proof. exact (eq_refl (term587 _120745 _120749 s op f t)). Qed.
Lemma lem5770339 {_120749 : Type'} (op : type1400 _120749) : (term487 _120749 op) = (term487 _120749 op).
Proof. exact (eq_refl (term487 _120749 op)). Qed.
Lemma lem5770340 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term592 _120745 _120749 s op f t) = (term593 _120745 _120749 s op t f).
Proof. exact (MK_COMB (@lem5770339 _120749 op) (@lem5770338 _120745 _120749 s op t f)). Qed.
Lemma lem5770341 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term594 _120745 _120749 s op f) = (term595 _120745 _120749 s op f).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5770340 _120745 _120749 s op t f)). Qed.
Lemma lem5770342 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5770343 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term586 _120745 _120749 s op f) = (term596 _120745 _120749 s op f).
Proof. exact (MK_COMB (@lem5770342 _120745) (@lem5770341 _120745 _120749 s op f)). Qed.
Lemma lem5770344 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : ((term585 _120745 _120749 s op f) = (term586 _120745 _120749 s op f)) = ((term581 _120745 _120749 s op f) = (term596 _120745 _120749 s op f)).
Proof. exact (MK_COMB (@lem5770337 _120745 _120749 s op f) (@lem5770343 _120745 _120749 s op f)). Qed.
Lemma lem5770345 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term581 _120745 _120749 s op f) = (term596 _120745 _120749 s op f).
Proof. exact (EQ_MP (@lem5770344 _120745 _120749 s op f) (@lem5770329 _120745 _120749 s op f)). Qed.
Lemma lem5770346 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term583 _120745 _120749 op f) = (term597 _120745 _120749 op f).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5770345 _120745 _120749 s op f)). Qed.
Lemma lem5770347 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5770348 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term584 _120745 _120749 op f) = (term598 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5770347 _120745) (@lem5770346 _120745 _120749 op f)). Qed.
Lemma lem5770349 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term567 _120745 _120749 op f) = (term598 _120745 _120749 op f).
Proof. exact (TRANS (@lem5770325 _120745 _120749 op f) (@lem5770348 _120745 _120749 op f)). Qed.
Lemma lem5770350 {_120745 _120749 : Type'} (op : type1400 _120749) : (term569 _120745 _120749 op) = (term599 _120745 _120749 op).
Proof. exact (fun_ext (fun f : _120745 -> _120749 => @lem5770349 _120745 _120749 op f)). Qed.
Lemma lem5770351 {_120745 _120749 : Type'} : (@all (_120745 -> _120749)) = (@all (_120745 -> _120749)).
Proof. exact (eq_refl (@all (_120745 -> _120749))). Qed.
Lemma lem5770352 {_120745 _120749 : Type'} (op : type1400 _120749) : (term570 _120745 _120749 op) = (term600 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5770351 _120745 _120749) (@lem5770350 _120745 _120749 op)). Qed.
Lemma lem5770353 {_120745 _120749 : Type'} (op : type1400 _120749) : (term488 _120745 _120749 op) = (term600 _120745 _120749 op).
Proof. exact (TRANS (@lem5770305 _120745 _120749 op) (@lem5770352 _120745 _120749 op)). Qed.
Lemma lem5770354 {_120745 _120749 : Type'} : (term489 _120745 _120749) = (term601 _120745 _120749).
Proof. exact (fun_ext (fun op : type1400 _120749 => @lem5770353 _120745 _120749 op)). Qed.
Lemma lem5770355 {_120749 : Type'} : (@all (_120749 -> _120749 -> _120749)) = (@all (_120749 -> _120749 -> _120749)).
Proof. exact (eq_refl (@all (_120749 -> _120749 -> _120749))). Qed.
Lemma lem5770356 {_120745 _120749 : Type'} : (term490 _120745 _120749) = (term602 _120745 _120749).
Proof. exact (MK_COMB (@lem5770355 _120749) (@lem5770354 _120745 _120749)). Qed.
Lemma lem5770381 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term593 _120745 _120749 s op t f) = (term593 _120745 _120749 s op t f).
Proof. exact (eq_refl (term593 _120745 _120749 s op t f)). Qed.
Lemma lem5770382 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term595 _120745 _120749 s op f) = (term595 _120745 _120749 s op f).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5770381 _120745 _120749 s op t f)). Qed.
Lemma lem5770383 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5770384 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (f : _120745 -> _120749) : (term596 _120745 _120749 s op f) = (term596 _120745 _120749 s op f).
Proof. exact (MK_COMB (@lem5770383 _120745) (@lem5770382 _120745 _120749 s op f)). Qed.
Lemma lem5770385 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term597 _120745 _120749 op f) = (term597 _120745 _120749 op f).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5770384 _120745 _120749 s op f)). Qed.
Lemma lem5770386 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5770387 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term598 _120745 _120749 op f) = (term598 _120745 _120749 op f).
Proof. exact (MK_COMB (@lem5770386 _120745) (@lem5770385 _120745 _120749 op f)). Qed.
Lemma lem5770388 {_120745 _120749 : Type'} (op : type1400 _120749) : (term599 _120745 _120749 op) = (term599 _120745 _120749 op).
Proof. exact (fun_ext (fun f : _120745 -> _120749 => @lem5770387 _120745 _120749 op f)). Qed.
Lemma lem5770389 {_120745 _120749 : Type'} : (@all (_120745 -> _120749)) = (@all (_120745 -> _120749)).
Proof. exact (eq_refl (@all (_120745 -> _120749))). Qed.
Lemma lem5770390 {_120745 _120749 : Type'} (op : type1400 _120749) : (term600 _120745 _120749 op) = (term600 _120745 _120749 op).
Proof. exact (MK_COMB (@lem5770389 _120745 _120749) (@lem5770388 _120745 _120749 op)). Qed.
Lemma lem5770391 {_120745 _120749 : Type'} : (term601 _120745 _120749) = (term601 _120745 _120749).
Proof. exact (fun_ext (fun op : type1400 _120749 => @lem5770390 _120745 _120749 op)). Qed.
Lemma lem5770392 {_120749 : Type'} : (@all (_120749 -> _120749 -> _120749)) = (@all (_120749 -> _120749 -> _120749)).
Proof. exact (eq_refl (@all (_120749 -> _120749 -> _120749))). Qed.
Lemma lem5770393 {_120745 _120749 : Type'} : (term602 _120745 _120749) = (term602 _120745 _120749).
Proof. exact (MK_COMB (@lem5770392 _120749) (@lem5770391 _120745 _120749)). Qed.
Lemma lem5770394 {_120745 _120749 : Type'} : (term490 _120745 _120749) = (term602 _120745 _120749).
Proof. exact (TRANS (@lem5770356 _120745 _120749) (@lem5770393 _120745 _120749)). Qed.
Lemma lem5770395 {_120745 _120749 : Type'} (h1 : term186 _120745 _120749) : term602 _120745 _120749.
Proof. exact (EQ_MP (@lem5770394 _120745 _120749) (@lem5769494 _120745 _120749 h1)). Qed.
Lemma lem5770523 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term507 _120745 s t) = (term603 _120745 s t).
Proof. exact (@lem19490 (s = (term502 _120745 s t)) (term442 _120745 t s) (term496 _120745 s t)). Qed.
Lemma lem5770524 {_120745 : Type'} (s : _120745 -> Prop) : (term508 _120745 s) = (term604 _120745 s).
Proof. exact (fun_ext (fun t : _120745 -> Prop => @lem5770523 _120745 s t)). Qed.
Lemma lem5770525 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5770526 {_120745 : Type'} (s : _120745 -> Prop) : (term509 _120745 s) = (term605 _120745 s).
Proof. exact (MK_COMB (@lem5770525 _120745) (@lem5770524 _120745 s)). Qed.
Lemma lem5770527 {_120745 : Type'} : (term510 _120745) = (term606 _120745).
Proof. exact (fun_ext (fun s : _120745 -> Prop => @lem5770526 _120745 s)). Qed.
Lemma lem5770528 {_120745 : Type'} : (@all (_120745 -> Prop)) = (@all (_120745 -> Prop)).
Proof. exact (eq_refl (@all (_120745 -> Prop))). Qed.
Lemma lem5770530 {_120745 : Type'} : (term511 _120745) = (term607 _120745).
Proof. exact (MK_COMB (@lem5770528 _120745) (@lem5770527 _120745)). Qed.
Lemma lem5770531 {_120745 : Type'} (h1 : term182 _120745) : term607 _120745.
Proof. exact (EQ_MP (@lem5770530 _120745) (@lem5769782 _120745 h1)). Qed.
Lemma lem5770650 {_120745 : Type'} (_72729 : _120745 -> Prop) (h1 : term191 _120745) : term608 _120745 _72729.
Proof. exact (@lem5769969 _120745 h1 _72729). Qed.
Lemma lem5770651 {_120745 : Type'} (_72729 : _120745 -> Prop) : (term608 _120745 _72729) = (term437 _120745 _72729).
Proof. exact (eq_refl (term608 _120745 _72729)). Qed.
Lemma lem5770652 {_120745 : Type'} (_72729 : _120745 -> Prop) (h1 : term191 _120745) : term437 _120745 _72729.
Proof. exact (EQ_MP (@lem5770651 _120745 _72729) (@lem5770650 _120745 _72729 h1)). Qed.
Lemma lem5770653 {_120745 : Type'} (_72729 : _120745 -> Prop) (_72730 : _120745 -> Prop) (h1 : term191 _120745) : term609 _120745 _72729 _72730.
Proof. exact (@lem5770652 _120745 _72729 h1 _72730). Qed.
Lemma lem5770654 {_120745 : Type'} (_72730 : _120745 -> Prop) (_72729 : _120745 -> Prop) : (term609 _120745 _72729 _72730) = (term435 _120745 _72730 _72729).
Proof. exact (eq_refl (term609 _120745 _72729 _72730)). Qed.
Lemma lem5770662 {_120745 : Type'} (_72733 : _120745 -> Prop) (h1 : term190 _120745) : term610 _120745 _72733.
Proof. exact (@lem5770065 _120745 h1 _72733). Qed.
Lemma lem5770663 {_120745 : Type'} (_72733 : _120745 -> Prop) : (term610 _120745 _72733) = (term552 _120745 _72733).
Proof. exact (eq_refl (term610 _120745 _72733)). Qed.
Lemma lem5770664 {_120745 : Type'} (_72733 : _120745 -> Prop) (h1 : term190 _120745) : term552 _120745 _72733.
Proof. exact (EQ_MP (@lem5770663 _120745 _72733) (@lem5770662 _120745 _72733 h1)). Qed.
Lemma lem5770665 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) (h1 : term190 _120745) : term611 _120745 _72733 _72734.
Proof. exact (@lem5770664 _120745 _72733 h1 _72734). Qed.
Lemma lem5770666 {_120745 : Type'} (_72734 : _120745 -> Prop) (_72733 : _120745 -> Prop) : (term611 _120745 _72733 _72734) = (term549 _120745 _72734 _72733).
Proof. exact (eq_refl (term611 _120745 _72733 _72734)). Qed.
Lemma lem5770667 {_120745 : Type'} (_72734 : _120745 -> Prop) (_72733 : _120745 -> Prop) (h1 : term190 _120745) : term549 _120745 _72734 _72733.
Proof. exact (EQ_MP (@lem5770666 _120745 _72734 _72733) (@lem5770665 _120745 _72733 _72734 h1)). Qed.
Lemma lem5770692 {_120745 _120749 : Type'} (_72743 : type1400 _120749) (h1 : term186 _120745 _120749) : term612 _120745 _120749 _72743.
Proof. exact (@lem5770395 _120745 _120749 h1 _72743). Qed.
Lemma lem5770693 {_120745 _120749 : Type'} (_72743 : type1400 _120749) : (term612 _120745 _120749 _72743) = (term600 _120745 _120749 _72743).
Proof. exact (eq_refl (term612 _120745 _120749 _72743)). Qed.
Lemma lem5770694 {_120745 _120749 : Type'} (_72743 : type1400 _120749) (h1 : term186 _120745 _120749) : term600 _120745 _120749 _72743.
Proof. exact (EQ_MP (@lem5770693 _120745 _120749 _72743) (@lem5770692 _120745 _120749 _72743 h1)). Qed.
Lemma lem5770695 {_120745 _120749 : Type'} (_72743 : type1400 _120749) (_72744 : _120745 -> _120749) (h1 : term186 _120745 _120749) : term613 _120745 _120749 _72743 _72744.
Proof. exact (@lem5770694 _120745 _120749 _72743 h1 _72744). Qed.
Lemma lem5770696 {_120745 _120749 : Type'} (_72743 : type1400 _120749) (_72744 : _120745 -> _120749) : (term613 _120745 _120749 _72743 _72744) = (term598 _120745 _120749 _72743 _72744).
Proof. exact (eq_refl (term613 _120745 _120749 _72743 _72744)). Qed.
Lemma lem5770697 {_120745 _120749 : Type'} (_72743 : type1400 _120749) (_72744 : _120745 -> _120749) (h1 : term186 _120745 _120749) : term598 _120745 _120749 _72743 _72744.
Proof. exact (EQ_MP (@lem5770696 _120745 _120749 _72743 _72744) (@lem5770695 _120745 _120749 _72743 _72744 h1)). Qed.
Lemma lem5770698 {_120745 _120749 : Type'} (_72743 : type1400 _120749) (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (h1 : term186 _120745 _120749) : term614 _120745 _120749 _72743 _72744 _72745.
Proof. exact (@lem5770697 _120745 _120749 _72743 _72744 h1 _72745). Qed.
Lemma lem5770699 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72744 : _120745 -> _120749) : (term614 _120745 _120749 _72743 _72744 _72745) = (term596 _120745 _120749 _72745 _72743 _72744).
Proof. exact (eq_refl (term614 _120745 _120749 _72743 _72744 _72745)). Qed.
Lemma lem5770700 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72744 : _120745 -> _120749) (h1 : term186 _120745 _120749) : term596 _120745 _120749 _72745 _72743 _72744.
Proof. exact (EQ_MP (@lem5770699 _120745 _120749 _72745 _72743 _72744) (@lem5770698 _120745 _120749 _72743 _72744 _72745 h1)). Qed.
Lemma lem5770701 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72744 : _120745 -> _120749) (_72746 : _120745 -> Prop) (h1 : term186 _120745 _120749) : term615 _120745 _120749 _72745 _72743 _72744 _72746.
Proof. exact (@lem5770700 _120745 _120749 _72745 _72743 _72744 h1 _72746). Qed.
Lemma lem5770702 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) : (term615 _120745 _120749 _72745 _72743 _72744 _72746) = (term593 _120745 _120749 _72745 _72743 _72746 _72744).
Proof. exact (eq_refl (term615 _120745 _120749 _72745 _72743 _72744 _72746)). Qed.
Lemma lem5770703 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) (h1 : term186 _120745 _120749) : term593 _120745 _120749 _72745 _72743 _72746 _72744.
Proof. exact (EQ_MP (@lem5770702 _120745 _120749 _72745 _72743 _72746 _72744) (@lem5770701 _120745 _120749 _72745 _72743 _72744 _72746 h1)). Qed.
Lemma lem5770716 {_120745 : Type'} (_72751 : _120745 -> Prop) (h1 : term182 _120745) : term616 _120745 _72751.
Proof. exact (@lem5770531 _120745 h1 _72751). Qed.
Lemma lem5770717 {_120745 : Type'} (_72751 : _120745 -> Prop) : (term616 _120745 _72751) = (term605 _120745 _72751).
Proof. exact (eq_refl (term616 _120745 _72751)). Qed.
Lemma lem5770718 {_120745 : Type'} (_72751 : _120745 -> Prop) (h1 : term182 _120745) : term605 _120745 _72751.
Proof. exact (EQ_MP (@lem5770717 _120745 _72751) (@lem5770716 _120745 _72751 h1)). Qed.
Lemma lem5770719 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) (h1 : term182 _120745) : term617 _120745 _72751 _72752.
Proof. exact (@lem5770718 _120745 _72751 h1 _72752). Qed.
Lemma lem5770720 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) : (term617 _120745 _72751 _72752) = (term603 _120745 _72751 _72752).
Proof. exact (eq_refl (term617 _120745 _72751 _72752)). Qed.
Lemma lem5770721 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) (h1 : term182 _120745) : term603 _120745 _72751 _72752.
Proof. exact (EQ_MP (@lem5770720 _120745 _72751 _72752) (@lem5770719 _120745 _72751 _72752 h1)). Qed.
Lemma lem5770778 {_120745 : Type'} (_72734 : _120745 -> Prop) (_72733 : _120745 -> Prop) : (term549 _120745 _72734 _72733) = (term618 _120745 _72734 _72733).
Proof. exact (@lem5765840 (term444 _120745 _72734) (term442 _120745 _72733 _72734) (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) _72733)). Qed.
Lemma lem5770779 {_120745 : Type'} (_72734 : _120745 -> Prop) (_72733 : _120745 -> Prop) (h1 : term190 _120745) : term618 _120745 _72734 _72733.
Proof. exact (EQ_MP (@lem5770778 _120745 _72734 _72733) (@lem5770667 _120745 _72734 _72733 h1)). Qed.
Lemma lem5770827 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) : (term478 _120745 _120749 _72745 _72743 _72746 _72744) = (term619 _120745 _120749 _72745 _72743 _72746 _72744).
Proof. exact (@lem5765840 (term444 _120745 _72745) (term475 _120745 _72745 _72746) ((term460 _120745 _120749 _72743 _72745 _72746 _72744) = (term469 _120745 _120749 _72745 _72743 _72746 _72744))). Qed.
Lemma lem5770834 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) : (term620 _120745 _120749 _72745 _72743 _72746 _72744) = (term621 _120745 _120749 _72745 _72743 _72746 _72744).
Proof. exact (@lem5765840 (term444 _120745 _72746) (term474 _120745 _72745 _72746) ((term460 _120745 _120749 _72743 _72745 _72746 _72744) = (term469 _120745 _120749 _72745 _72743 _72746 _72744))). Qed.
Lemma lem5770835 {_120745 : Type'} (_72745 : _120745 -> Prop) : (term445 _120745 _72745) = (term445 _120745 _72745).
Proof. exact (eq_refl (term445 _120745 _72745)). Qed.
Lemma lem5770838 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) : (term619 _120745 _120749 _72745 _72743 _72746 _72744) = (term622 _120745 _120749 _72745 _72743 _72746 _72744).
Proof. exact (MK_COMB (@lem5770835 _120745 _72745) (@lem5770834 _120745 _120749 _72745 _72743 _72746 _72744)). Qed.
Lemma lem5770840 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) : (term478 _120745 _120749 _72745 _72743 _72746 _72744) = (term622 _120745 _120749 _72745 _72743 _72746 _72744).
Proof. exact (TRANS (@lem5770827 _120745 _120749 _72745 _72743 _72746 _72744) (@lem5770838 _120745 _120749 _72745 _72743 _72746 _72744)). Qed.
Lemma lem5770841 {_120749 : Type'} (_72743 : type1400 _120749) : (term487 _120749 _72743) = (term487 _120749 _72743).
Proof. exact (eq_refl (term487 _120749 _72743)). Qed.
Lemma lem5770844 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) : (term593 _120745 _120749 _72745 _72743 _72746 _72744) = (term623 _120745 _120749 _72745 _72743 _72746 _72744).
Proof. exact (MK_COMB (@lem5770841 _120749 _72743) (@lem5770840 _120745 _120749 _72745 _72743 _72746 _72744)). Qed.
Lemma lem5770845 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) (h1 : term186 _120745 _120749) : term623 _120745 _120749 _72745 _72743 _72746 _72744.
Proof. exact (EQ_MP (@lem5770844 _120745 _120749 _72745 _72743 _72746 _72744) (@lem5770703 _120745 _120749 _72745 _72743 _72746 _72744 h1)). Qed.
Lemma lem5770871 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term529 _120745 _120749 t op s f.
Proof. exact (proj2 (@lem5769940 _120745 _120749 t op s f h1)). Qed.
Lemma lem5770925 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) (h1 : term182 _120745) : term624 _120745 _72751 _72752.
Proof. exact (proj1 (@lem5770721 _120745 _72751 _72752 h1)). Qed.
Lemma lem5770931 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) (h1 : term182 _120745) : term625 _120745 _72751 _72752.
Proof. exact (proj2 (@lem5770721 _120745 _72751 _72752 h1)). Qed.
Lemma lem5771087 {_120745 _120749 : Type'} : (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749)) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749)).
Proof. exact (eq_refl (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749))). Qed.
Lemma lem5771088 {_120745 _120749 : Type'} (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) (h1 : _72797 = _72799) : _72797 = _72799.
Proof. exact (h1). Qed.
Lemma lem5771089 {_120745 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (h1 : _72798 = _72800) : _72798 = _72800.
Proof. exact (h1). Qed.
Lemma lem5771090 {_120745 _120749 : Type'} (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) (h1 : _72797 = _72799) : (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72797) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72799).
Proof. exact (MK_COMB (@lem5771087 _120745 _120749) (@lem5771088 _120745 _120749 _72797 _72799 h1)). Qed.
Lemma lem5771091 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) (h1 : _72798 = _72800) (h2 : _72797 = _72799) : (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72797 _72798) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72799 _72800).
Proof. exact (MK_COMB (@lem5771090 _120745 _120749 _72797 _72799 h2) (@lem5771089 _120745 _72798 _72800 h1)). Qed.
Lemma lem5771092 {_120745 _120749 : Type'} (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (h1 : _72798 = _72800) : term626 _120745 _120749 _72797 _72798 _72799 _72800.
Proof. exact (fun h0 : _72797 = _72799 => @lem5771091 _120745 _120749 _72798 _72800 _72797 _72799 h1 h0). Qed.
Lemma lem5771094 (a : Prop) (b : Prop) : (a -> b) = (term627 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5771095 {_120745 _120749 : Type'} (_72797 : type632 _120745 _120749) (_72798 : _120745 -> Prop) (_72799 : type632 _120745 _120749) (_72800 : _120745 -> Prop) : (term626 _120745 _120749 _72797 _72798 _72799 _72800) = (term628 _120745 _120749 _72797 _72798 _72799 _72800).
Proof. exact (@lem5771094 (_72797 = _72799) ((@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72797 _72798) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72799 _72800))). Qed.
Lemma lem5771096 {_120745 _120749 : Type'} (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (h1 : _72798 = _72800) : term628 _120745 _120749 _72797 _72798 _72799 _72800.
Proof. exact (EQ_MP (@lem5771095 _120745 _120749 _72797 _72798 _72799 _72800) (@lem5771092 _120745 _120749 _72797 _72799 _72798 _72800 h1)). Qed.
Lemma lem5771097 {_120745 _120749 : Type'} (_72797 : type632 _120745 _120749) (_72798 : _120745 -> Prop) (_72799 : type632 _120745 _120749) (_72800 : _120745 -> Prop) : term629 _120745 _120749 _72797 _72798 _72799 _72800.
Proof. exact (fun h0 : _72798 = _72800 => @lem5771096 _120745 _120749 _72797 _72799 _72798 _72800 h0). Qed.
Lemma lem5771099 (a : Prop) (b : Prop) : (a -> b) = (term627 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5771100 {_120745 _120749 : Type'} (_72797 : type632 _120745 _120749) (_72798 : _120745 -> Prop) (_72799 : type632 _120745 _120749) (_72800 : _120745 -> Prop) : (term629 _120745 _120749 _72797 _72798 _72799 _72800) = (term630 _120745 _120749 _72797 _72798 _72799 _72800).
Proof. exact (@lem5771099 (_72798 = _72800) (term628 _120745 _120749 _72797 _72798 _72799 _72800)). Qed.
Lemma lem5771101 {_120745 _120749 : Type'} (_72797 : type632 _120745 _120749) (_72798 : _120745 -> Prop) (_72799 : type632 _120745 _120749) (_72800 : _120745 -> Prop) : term630 _120745 _120749 _72797 _72798 _72799 _72800.
Proof. exact (EQ_MP (@lem5771100 _120745 _120749 _72797 _72798 _72799 _72800) (@lem5771097 _120745 _120749 _72797 _72798 _72799 _72800)). Qed.
Lemma lem5771102 {_120745 _120749 : Type'} : (@I ((_120745 -> _120749) -> _120749)) = (@I ((_120745 -> _120749) -> _120749)).
Proof. exact (eq_refl (@I ((_120745 -> _120749) -> _120749))). Qed.
Lemma lem5771103 {_120745 _120749 : Type'} (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) (h1 : _72801 = _72803) : _72801 = _72803.
Proof. exact (h1). Qed.
Lemma lem5771104 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (h1 : _72802 = _72804) : _72802 = _72804.
Proof. exact (h1). Qed.
Lemma lem5771105 {_120745 _120749 : Type'} (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) (h1 : _72801 = _72803) : (@I ((_120745 -> _120749) -> _120749) _72801) = (@I ((_120745 -> _120749) -> _120749) _72803).
Proof. exact (MK_COMB (@lem5771102 _120745 _120749) (@lem5771103 _120745 _120749 _72801 _72803 h1)). Qed.
Lemma lem5771106 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) (h1 : _72802 = _72804) (h2 : _72801 = _72803) : (@I ((_120745 -> _120749) -> _120749) _72801 _72802) = (@I ((_120745 -> _120749) -> _120749) _72803 _72804).
Proof. exact (MK_COMB (@lem5771105 _120745 _120749 _72801 _72803 h2) (@lem5771104 _120745 _120749 _72802 _72804 h1)). Qed.
Lemma lem5771107 {_120745 _120749 : Type'} (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (h1 : _72802 = _72804) : term631 _120745 _120749 _72801 _72802 _72803 _72804.
Proof. exact (fun h0 : _72801 = _72803 => @lem5771106 _120745 _120749 _72802 _72804 _72801 _72803 h1 h0). Qed.
Lemma lem5771109 (a : Prop) (b : Prop) : (a -> b) = (term627 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5771110 {_120745 _120749 : Type'} (_72801 : type570 _120745 _120749) (_72802 : _120745 -> _120749) (_72803 : type570 _120745 _120749) (_72804 : _120745 -> _120749) : (term631 _120745 _120749 _72801 _72802 _72803 _72804) = (term632 _120745 _120749 _72801 _72802 _72803 _72804).
Proof. exact (@lem5771109 (_72801 = _72803) ((@I ((_120745 -> _120749) -> _120749) _72801 _72802) = (@I ((_120745 -> _120749) -> _120749) _72803 _72804))). Qed.
Lemma lem5771111 {_120745 _120749 : Type'} (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (h1 : _72802 = _72804) : term632 _120745 _120749 _72801 _72802 _72803 _72804.
Proof. exact (EQ_MP (@lem5771110 _120745 _120749 _72801 _72802 _72803 _72804) (@lem5771107 _120745 _120749 _72801 _72803 _72802 _72804 h1)). Qed.
Lemma lem5771112 {_120745 _120749 : Type'} (_72801 : type570 _120745 _120749) (_72802 : _120745 -> _120749) (_72803 : type570 _120745 _120749) (_72804 : _120745 -> _120749) : term633 _120745 _120749 _72801 _72802 _72803 _72804.
Proof. exact (fun h0 : _72802 = _72804 => @lem5771111 _120745 _120749 _72801 _72803 _72802 _72804 h0). Qed.
Lemma lem5771114 (a : Prop) (b : Prop) : (a -> b) = (term627 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5771115 {_120745 _120749 : Type'} (_72801 : type570 _120745 _120749) (_72802 : _120745 -> _120749) (_72803 : type570 _120745 _120749) (_72804 : _120745 -> _120749) : (term633 _120745 _120749 _72801 _72802 _72803 _72804) = (term634 _120745 _120749 _72801 _72802 _72803 _72804).
Proof. exact (@lem5771114 (_72802 = _72804) (term632 _120745 _120749 _72801 _72802 _72803 _72804)). Qed.
Lemma lem5771116 {_120745 _120749 : Type'} (_72801 : type570 _120745 _120749) (_72802 : _120745 -> _120749) (_72803 : type570 _120745 _120749) (_72804 : _120745 -> _120749) : term634 _120745 _120749 _72801 _72802 _72803 _72804.
Proof. exact (EQ_MP (@lem5771115 _120745 _120749 _72801 _72802 _72803 _72804) (@lem5771112 _120745 _120749 _72801 _72802 _72803 _72804)). Qed.
Lemma lem5771392 {_120749 : Type'} (x : _120749) (y : _120749) (z : _120749) : term635 _120749 x y z.
Proof. exact (@lem21385 _120749 x y z). Qed.
Lemma lem5771428 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : @I ((_120749 -> _120749 -> _120749) -> Prop) (@monoidal _120749) op.
Proof. exact (proj1 (@lem5769939 _120745 _120749 t op s f h1)). Qed.
Lemma lem5771429 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term636 _120749 op.
Proof. exact (fun h0 : term486 _120749 op => @lem5771428 _120745 _120749 t op s f h1). Qed.
Lemma lem5771431 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5771432 {_120749 : Type'} (op : type1400 _120749) : (term636 _120749 op) = (@I ((_120749 -> _120749 -> _120749) -> Prop) (@monoidal _120749) op).
Proof. exact (@lem5771431 (@I ((_120749 -> _120749 -> _120749) -> Prop) (@monoidal _120749) op)). Qed.
Lemma lem5771433 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : @I ((_120749 -> _120749 -> _120749) -> Prop) (@monoidal _120749) op.
Proof. exact (EQ_MP (@lem5771432 _120749 op) (@lem5771429 _120745 _120749 t op s f h1)). Qed.
Lemma lem5771435 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : @I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s.
Proof. exact (proj1 (@lem5769943 _120745 _120749 t op s f h1)). Qed.
Lemma lem5771436 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term637 _120745 s.
Proof. exact (fun h0 : term444 _120745 s => @lem5771435 _120745 _120749 t op s f h1). Qed.
Lemma lem5771438 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5771439 {_120745 : Type'} (s : _120745 -> Prop) : (term637 _120745 s) = (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s).
Proof. exact (@lem5771438 (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s)). Qed.
Lemma lem5771440 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : @I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s.
Proof. exact (EQ_MP (@lem5771439 _120745 s) (@lem5771436 _120745 _120749 t op s f h1)). Qed.
Lemma lem5771442 {_120745 : Type'} (_72730 : _120745 -> Prop) (_72729 : _120745 -> Prop) (h1 : term191 _120745) : term435 _120745 _72730 _72729.
Proof. exact (EQ_MP (@lem5770654 _120745 _72730 _72729) (@lem5770653 _120745 _72729 _72730 h1)). Qed.
Lemma lem5771443 {_120745 : Type'} (_72730 : _120745 -> Prop) (_72729 : _120745 -> Prop) (h1 : term191 _120745) : term435 _120745 _72730 _72729.
Proof. exact (@lem5771442 _120745 _72730 _72729 h1). Qed.
Lemma lem5771444 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) (h1 : term191 _120745) : term435 _120745 t s.
Proof. exact (@lem5771443 _120745 t s h1). Qed.
Lemma lem5771445 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) (h1 : term191 _120745) : term638 _120745 t s.
Proof. exact (fun h0 : term639 _120745 t s => @lem5771444 _120745 t s h1). Qed.
Lemma lem5771447 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5771448 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term638 _120745 t s) = (term435 _120745 t s).
Proof. exact (@lem5771447 (term435 _120745 t s)). Qed.
Lemma lem5771449 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) (h1 : term191 _120745) : term435 _120745 t s.
Proof. exact (EQ_MP (@lem5771448 _120745 t s) (@lem5771445 _120745 t s h1)). Qed.
Lemma lem5771465 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5771466 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : (term640 _120745 _72734 _72733) = (term641 _120745 _72733 _72734).
Proof. exact (@lem5771465 (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) _72733) (term442 _120745 _72733 _72734)). Qed.
Lemma lem5771472 {_120745 : Type'} (_72734 : _120745 -> Prop) : (term445 _120745 _72734) = (term445 _120745 _72734).
Proof. exact (eq_refl (term445 _120745 _72734)). Qed.
Lemma lem5771473 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : (term618 _120745 _72734 _72733) = (term642 _120745 _72733 _72734).
Proof. exact (MK_COMB (@lem5771472 _120745 _72734) (@lem5771466 _120745 _72733 _72734)). Qed.
Lemma lem5771477 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5771478 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : (term642 _120745 _72733 _72734) = (term643 _120745 _72733 _72734).
Proof. exact (@lem5771477 (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) _72733) (term444 _120745 _72734) (term442 _120745 _72733 _72734)). Qed.
Lemma lem5771494 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : (term618 _120745 _72734 _72733) = (term643 _120745 _72733 _72734).
Proof. exact (TRANS (@lem5771473 _120745 _72733 _72734) (@lem5771478 _120745 _72733 _72734)). Qed.
Lemma lem5771495 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5771496 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : (term644 _120745 _72734 _72733) = (term645 _120745 _72733 _72734).
Proof. exact (MK_COMB (@lem5771495) (@lem5771494 _120745 _72733 _72734)). Qed.
Lemma lem5771512 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : (term643 _120745 _72733 _72734) = (term643 _120745 _72733 _72734).
Proof. exact (eq_refl (term643 _120745 _72733 _72734)). Qed.
Lemma lem5771513 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : ((term618 _120745 _72734 _72733) = (term643 _120745 _72733 _72734)) = ((term643 _120745 _72733 _72734) = (term643 _120745 _72733 _72734)).
Proof. exact (MK_COMB (@lem5771496 _120745 _72733 _72734) (@lem5771512 _120745 _72733 _72734)). Qed.
Lemma lem5771515 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5771516 (x : Prop) : (x = x) = True.
Proof. exact (@lem5771515 Prop x). Qed.
Lemma lem5771517 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : ((term643 _120745 _72733 _72734) = (term643 _120745 _72733 _72734)) = True.
Proof. exact (@lem5771516 (term643 _120745 _72733 _72734)). Qed.
Lemma lem5771518 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : ((term618 _120745 _72734 _72733) = (term643 _120745 _72733 _72734)) = True.
Proof. exact (TRANS (@lem5771513 _120745 _72733 _72734) (@lem5771517 _120745 _72733 _72734)). Qed.
Lemma lem5771519 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : True = ((term618 _120745 _72734 _72733) = (term643 _120745 _72733 _72734)).
Proof. exact (SYM (@lem5771518 _120745 _72733 _72734)). Qed.
Lemma lem5771520 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : (term618 _120745 _72734 _72733) = (term643 _120745 _72733 _72734).
Proof. exact (EQ_MP (@lem5771519 _120745 _72733 _72734) (@lem0)). Qed.
Lemma lem5771521 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) (h1 : term190 _120745) : term643 _120745 _72733 _72734.
Proof. exact (EQ_MP (@lem5771520 _120745 _72733 _72734) (@lem5770779 _120745 _72734 _72733 h1)). Qed.
Lemma lem5771523 (b : Prop) (a : Prop) : (a \/ b) = (term169 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5771524 {_120745 : Type'} (_72734 : _120745 -> Prop) (_72733 : _120745 -> Prop) : (term643 _120745 _72733 _72734) = (term646 _120745 _72734 _72733).
Proof. exact (@lem5771523 (term446 _120745 _72733 _72734) (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) _72733)). Qed.
Lemma lem5771526 (a : Prop) (b : Prop) : (term647 a b) = (term648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5771527 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : (term649 _120745 _72733 _72734) = (term650 _120745 _72733 _72734).
Proof. exact (@lem5771526 (term444 _120745 _72734) (term442 _120745 _72733 _72734)). Qed.
Lemma lem5771529 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5771530 {_120745 : Type'} (_72734 : _120745 -> Prop) : (term651 _120745 _72734) = (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) _72734).
Proof. exact (@lem5771529 (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) _72734)). Qed.
Lemma lem5771531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5771532 {_120745 : Type'} (_72734 : _120745 -> Prop) : (term652 _120745 _72734) = (term531 _120745 _72734).
Proof. exact (MK_COMB (@lem5771531) (@lem5771530 _120745 _72734)). Qed.
Lemma lem5771534 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5771535 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : (term653 _120745 _72733 _72734) = (term440 _120745 _72733 _72734).
Proof. exact (@lem5771534 (term440 _120745 _72733 _72734)). Qed.
Lemma lem5771536 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : (term650 _120745 _72733 _72734) = (term532 _120745 _72733 _72734).
Proof. exact (MK_COMB (@lem5771532 _120745 _72734) (@lem5771535 _120745 _72733 _72734)). Qed.
Lemma lem5771537 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : (term649 _120745 _72733 _72734) = (term532 _120745 _72733 _72734).
Proof. exact (TRANS (@lem5771527 _120745 _72733 _72734) (@lem5771536 _120745 _72733 _72734)). Qed.
Lemma lem5771538 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5771539 {_120745 : Type'} (_72733 : _120745 -> Prop) (_72734 : _120745 -> Prop) : (term654 _120745 _72733 _72734) = (term655 _120745 _72733 _72734).
Proof. exact (MK_COMB (@lem5771538) (@lem5771537 _120745 _72733 _72734)). Qed.
Lemma lem5771540 {_120745 : Type'} (_72733 : _120745 -> Prop) : (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) _72733) = (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) _72733).
Proof. exact (eq_refl (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) _72733)). Qed.
Lemma lem5771541 {_120745 : Type'} (_72734 : _120745 -> Prop) (_72733 : _120745 -> Prop) : (term646 _120745 _72734 _72733) = (term656 _120745 _72734 _72733).
Proof. exact (MK_COMB (@lem5771539 _120745 _72733 _72734) (@lem5771540 _120745 _72733)). Qed.
Lemma lem5771542 {_120745 : Type'} (_72734 : _120745 -> Prop) (_72733 : _120745 -> Prop) : (term643 _120745 _72733 _72734) = (term656 _120745 _72734 _72733).
Proof. exact (TRANS (@lem5771524 _120745 _72734 _72733) (@lem5771541 _120745 _72734 _72733)). Qed.
Lemma lem5771544 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term191 _120745) (h2 : term358 _120745 _120749 t op s f) : term657 _120745 t s.
Proof. exact (conj (@lem5771440 _120745 _120749 t op s f h2) (@lem5771449 _120745 t s h1)). Qed.
Lemma lem5771546 {_120745 : Type'} (_72734 : _120745 -> Prop) (_72733 : _120745 -> Prop) (h1 : term190 _120745) : term656 _120745 _72734 _72733.
Proof. exact (EQ_MP (@lem5771542 _120745 _72734 _72733) (@lem5771521 _120745 _72733 _72734 h1)). Qed.
Lemma lem5771547 {_120745 : Type'} (_72734 : _120745 -> Prop) (_72733 : _120745 -> Prop) (h1 : term190 _120745) : term656 _120745 _72734 _72733.
Proof. exact (@lem5771546 _120745 _72734 _72733 h1). Qed.
Lemma lem5771548 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) (h1 : term190 _120745) : term658 _120745 s t.
Proof. exact (@lem5771547 _120745 s (term429 _120745 s t) h1). Qed.
Lemma lem5771551 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term191 _120745) (h3 : term358 _120745 _120749 t op s f) : term659 _120745 s t.
Proof. exact (@lem5771548 _120745 s t h1 (@lem5771544 _120745 _120749 t op s f h2 h3)). Qed.
Lemma lem5771552 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term191 _120745) (h3 : term358 _120745 _120749 t op s f) : term660 _120745 s t.
Proof. exact (fun h0 : term661 _120745 s t => @lem5771551 _120745 _120749 t op s f h1 h2 h3). Qed.
Lemma lem5771554 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5771555 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term660 _120745 s t) = (term659 _120745 s t).
Proof. exact (@lem5771554 (term659 _120745 s t)). Qed.
Lemma lem5771556 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term191 _120745) (h3 : term358 _120745 _120749 t op s f) : term659 _120745 s t.
Proof. exact (EQ_MP (@lem5771555 _120745 s t) (@lem5771552 _120745 _120749 t op s f h1 h2 h3)). Qed.
Lemma lem5771558 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : @I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s.
Proof. exact (proj1 (@lem5769943 _120745 _120749 t op s f h1)). Qed.
Lemma lem5771559 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term637 _120745 s.
Proof. exact (fun h0 : term444 _120745 s => @lem5771558 _120745 _120749 t op s f h1). Qed.
Lemma lem5771561 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5771562 {_120745 : Type'} (s : _120745 -> Prop) : (term637 _120745 s) = (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s).
Proof. exact (@lem5771561 (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s)). Qed.
Lemma lem5771563 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : @I ((_120745 -> Prop) -> Prop) (@FINITE _120745) s.
Proof. exact (EQ_MP (@lem5771562 _120745 s) (@lem5771559 _120745 _120749 t op s f h1)). Qed.
Lemma lem5771565 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term440 _120745 t s.
Proof. exact (proj2 (@lem5769943 _120745 _120749 t op s f h1)). Qed.
Lemma lem5771566 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term662 _120745 t s.
Proof. exact (fun h0 : term442 _120745 t s => @lem5771565 _120745 _120749 t op s f h1). Qed.
Lemma lem5771568 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5771569 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term662 _120745 t s) = (term440 _120745 t s).
Proof. exact (@lem5771568 (term440 _120745 t s)). Qed.
Lemma lem5771570 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term440 _120745 t s.
Proof. exact (EQ_MP (@lem5771569 _120745 t s) (@lem5771566 _120745 _120749 t op s f h1)). Qed.
Lemma lem5771571 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term532 _120745 t s.
Proof. exact (conj (@lem5771563 _120745 _120749 t op s f h1) (@lem5771570 _120745 _120749 t op s f h1)). Qed.
Lemma lem5771573 {_120745 : Type'} (_72734 : _120745 -> Prop) (_72733 : _120745 -> Prop) (h1 : term190 _120745) : term656 _120745 _72734 _72733.
Proof. exact (EQ_MP (@lem5771542 _120745 _72734 _72733) (@lem5771521 _120745 _72733 _72734 h1)). Qed.
Lemma lem5771574 {_120745 : Type'} (_72734 : _120745 -> Prop) (_72733 : _120745 -> Prop) (h1 : term190 _120745) : term656 _120745 _72734 _72733.
Proof. exact (@lem5771573 _120745 _72734 _72733 h1). Qed.
Lemma lem5771575 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) (h1 : term190 _120745) : term656 _120745 s t.
Proof. exact (@lem5771574 _120745 s t h1). Qed.
Lemma lem5771578 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term358 _120745 _120749 t op s f) : @I ((_120745 -> Prop) -> Prop) (@FINITE _120745) t.
Proof. exact (@lem5771575 _120745 s t h1 (@lem5771571 _120745 _120749 t op s f h2)). Qed.
Lemma lem5771579 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term358 _120745 _120749 t op s f) : term637 _120745 t.
Proof. exact (fun h0 : term444 _120745 t => @lem5771578 _120745 _120749 t op s f h1 h2). Qed.
Lemma lem5771581 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5771582 {_120745 : Type'} (t : _120745 -> Prop) : (term637 _120745 t) = (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) t).
Proof. exact (@lem5771581 (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) t)). Qed.
Lemma lem5771583 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term358 _120745 _120749 t op s f) : @I ((_120745 -> Prop) -> Prop) (@FINITE _120745) t.
Proof. exact (EQ_MP (@lem5771582 _120745 t) (@lem5771579 _120745 _120749 t op s f h1 h2)). Qed.
Lemma lem5771585 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term440 _120745 t s.
Proof. exact (proj2 (@lem5769943 _120745 _120749 t op s f h1)). Qed.
Lemma lem5771586 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term662 _120745 t s.
Proof. exact (fun h0 : term442 _120745 t s => @lem5771585 _120745 _120749 t op s f h1). Qed.
Lemma lem5771588 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5771589 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term662 _120745 t s) = (term440 _120745 t s).
Proof. exact (@lem5771588 (term440 _120745 t s)). Qed.
Lemma lem5771590 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term440 _120745 t s.
Proof. exact (EQ_MP (@lem5771589 _120745 t s) (@lem5771586 _120745 _120749 t op s f h1)). Qed.
Lemma lem5771596 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5771597 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : (term625 _120745 _72751 _72752) = (term663 _120745 _72752 _72751).
Proof. exact (@lem5771596 (term496 _120745 _72751 _72752) (term442 _120745 _72752 _72751)). Qed.
Lemma lem5771603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5771604 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : (term664 _120745 _72751 _72752) = (term665 _120745 _72752 _72751).
Proof. exact (MK_COMB (@lem5771603) (@lem5771597 _120745 _72752 _72751)). Qed.
Lemma lem5771610 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : (term663 _120745 _72752 _72751) = (term663 _120745 _72752 _72751).
Proof. exact (eq_refl (term663 _120745 _72752 _72751)). Qed.
Lemma lem5771611 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : ((term625 _120745 _72751 _72752) = (term663 _120745 _72752 _72751)) = ((term663 _120745 _72752 _72751) = (term663 _120745 _72752 _72751)).
Proof. exact (MK_COMB (@lem5771604 _120745 _72752 _72751) (@lem5771610 _120745 _72752 _72751)). Qed.
Lemma lem5771613 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5771614 (x : Prop) : (x = x) = True.
Proof. exact (@lem5771613 Prop x). Qed.
Lemma lem5771615 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : ((term663 _120745 _72752 _72751) = (term663 _120745 _72752 _72751)) = True.
Proof. exact (@lem5771614 (term663 _120745 _72752 _72751)). Qed.
Lemma lem5771616 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : ((term625 _120745 _72751 _72752) = (term663 _120745 _72752 _72751)) = True.
Proof. exact (TRANS (@lem5771611 _120745 _72752 _72751) (@lem5771615 _120745 _72752 _72751)). Qed.
Lemma lem5771617 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : True = ((term625 _120745 _72751 _72752) = (term663 _120745 _72752 _72751)).
Proof. exact (SYM (@lem5771616 _120745 _72752 _72751)). Qed.
Lemma lem5771618 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : (term625 _120745 _72751 _72752) = (term663 _120745 _72752 _72751).
Proof. exact (EQ_MP (@lem5771617 _120745 _72752 _72751) (@lem0)). Qed.
Lemma lem5771619 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) (h1 : term182 _120745) : term663 _120745 _72752 _72751.
Proof. exact (EQ_MP (@lem5771618 _120745 _72752 _72751) (@lem5770931 _120745 _72751 _72752 h1)). Qed.
Lemma lem5771621 (b : Prop) (a : Prop) : (a \/ b) = (term169 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5771622 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) : (term663 _120745 _72752 _72751) = (term666 _120745 _72751 _72752).
Proof. exact (@lem5771621 (term442 _120745 _72752 _72751) (term496 _120745 _72751 _72752)). Qed.
Lemma lem5771624 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5771625 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : (term653 _120745 _72752 _72751) = (term440 _120745 _72752 _72751).
Proof. exact (@lem5771624 (term440 _120745 _72752 _72751)). Qed.
Lemma lem5771626 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5771627 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : (term667 _120745 _72752 _72751) = (term668 _120745 _72752 _72751).
Proof. exact (MK_COMB (@lem5771626) (@lem5771625 _120745 _72752 _72751)). Qed.
Lemma lem5771628 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) : (term496 _120745 _72751 _72752) = (term496 _120745 _72751 _72752).
Proof. exact (eq_refl (term496 _120745 _72751 _72752)). Qed.
Lemma lem5771629 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) : (term666 _120745 _72751 _72752) = (term669 _120745 _72751 _72752).
Proof. exact (MK_COMB (@lem5771627 _120745 _72752 _72751) (@lem5771628 _120745 _72751 _72752)). Qed.
Lemma lem5771630 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) : (term663 _120745 _72752 _72751) = (term669 _120745 _72751 _72752).
Proof. exact (TRANS (@lem5771622 _120745 _72751 _72752) (@lem5771629 _120745 _72751 _72752)). Qed.
Lemma lem5771633 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) (h1 : term182 _120745) : term669 _120745 _72751 _72752.
Proof. exact (EQ_MP (@lem5771630 _120745 _72751 _72752) (@lem5771619 _120745 _72752 _72751 h1)). Qed.
Lemma lem5771634 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) (h1 : term182 _120745) : term669 _120745 _72751 _72752.
Proof. exact (@lem5771633 _120745 _72751 _72752 h1). Qed.
Lemma lem5771635 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) (h1 : term182 _120745) : term669 _120745 s t.
Proof. exact (@lem5771634 _120745 s t h1). Qed.
Lemma lem5771638 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : term496 _120745 s t.
Proof. exact (@lem5771635 _120745 s t h1 (@lem5771590 _120745 _120749 t op s f h2)). Qed.
Lemma lem5771639 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : term670 _120745 s t.
Proof. exact (fun h0 : term671 _120745 s t => @lem5771638 _120745 _120749 t op s f h1 h2). Qed.
Lemma lem5771641 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5771642 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term670 _120745 s t) = (term496 _120745 s t).
Proof. exact (@lem5771641 (term496 _120745 s t)). Qed.
Lemma lem5771643 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : term496 _120745 s t.
Proof. exact (EQ_MP (@lem5771642 _120745 s t) (@lem5771639 _120745 _120749 t op s f h1 h2)). Qed.
Lemma lem5771649 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5771650 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) : (term623 _120745 _120749 _72745 _72743 _72746 _72744) = (term672 _120745 _120749 _72745 _72743 _72746 _72744).
Proof. exact (@lem5771649 (term444 _120745 _72745) (term486 _120749 _72743) (term621 _120745 _120749 _72745 _72743 _72746 _72744)). Qed.
Lemma lem5771664 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5771665 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) : (term673 _120745 _120749 _72745 _72743 _72746 _72744) = (term674 _120745 _120749 _72745 _72743 _72746 _72744).
Proof. exact (@lem5771664 (term444 _120745 _72746) (term486 _120749 _72743) (term675 _120745 _120749 _72745 _72743 _72746 _72744)). Qed.
Lemma lem5771679 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5771680 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) : (term676 _120745 _120749 _72745 _72743 _72746 _72744) = (term677 _120745 _120749 _72745 _72743 _72746 _72744).
Proof. exact (@lem5771679 (term474 _120745 _72745 _72746) (term486 _120749 _72743) ((term460 _120745 _120749 _72743 _72745 _72746 _72744) = (term469 _120745 _120749 _72745 _72743 _72746 _72744))). Qed.
Lemma lem5771694 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5771695 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) (_72743 : type1400 _120749) : (term678 _120745 _120749 _72745 _72743 _72746 _72744) = (term679 _120745 _120749 _72745 _72746 _72744 _72743).
Proof. exact (@lem5771694 ((term460 _120745 _120749 _72743 _72745 _72746 _72744) = (term469 _120745 _120749 _72745 _72743 _72746 _72744)) (term486 _120749 _72743)). Qed.
Lemma lem5771703 {_120745 : Type'} (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : (term680 _120745 _72745 _72746) = (term680 _120745 _72745 _72746).
Proof. exact (eq_refl (term680 _120745 _72745 _72746)). Qed.
Lemma lem5771704 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) (_72743 : type1400 _120749) : (term677 _120745 _120749 _72745 _72743 _72746 _72744) = (term681 _120745 _120749 _72745 _72746 _72744 _72743).
Proof. exact (MK_COMB (@lem5771703 _120745 _72745 _72746) (@lem5771695 _120745 _120749 _72745 _72746 _72744 _72743)). Qed.
Lemma lem5771708 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5771709 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term681 _120745 _120749 _72745 _72746 _72744 _72743) = (term682 _120745 _120749 _72744 _72745 _72746 _72743).
Proof. exact (@lem5771708 ((term460 _120745 _120749 _72743 _72745 _72746 _72744) = (term469 _120745 _120749 _72745 _72743 _72746 _72744)) (term474 _120745 _72745 _72746) (term486 _120749 _72743)). Qed.
Lemma lem5771727 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term677 _120745 _120749 _72745 _72743 _72746 _72744) = (term682 _120745 _120749 _72744 _72745 _72746 _72743).
Proof. exact (TRANS (@lem5771704 _120745 _120749 _72745 _72746 _72744 _72743) (@lem5771709 _120745 _120749 _72744 _72745 _72746 _72743)). Qed.
Lemma lem5771728 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term676 _120745 _120749 _72745 _72743 _72746 _72744) = (term682 _120745 _120749 _72744 _72745 _72746 _72743).
Proof. exact (TRANS (@lem5771680 _120745 _120749 _72745 _72743 _72746 _72744) (@lem5771727 _120745 _120749 _72744 _72745 _72746 _72743)). Qed.
Lemma lem5771729 {_120745 : Type'} (_72746 : _120745 -> Prop) : (term445 _120745 _72746) = (term445 _120745 _72746).
Proof. exact (eq_refl (term445 _120745 _72746)). Qed.
Lemma lem5771730 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term674 _120745 _120749 _72745 _72743 _72746 _72744) = (term683 _120745 _120749 _72744 _72745 _72746 _72743).
Proof. exact (MK_COMB (@lem5771729 _120745 _72746) (@lem5771728 _120745 _120749 _72744 _72745 _72746 _72743)). Qed.
Lemma lem5771734 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5771735 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term683 _120745 _120749 _72744 _72745 _72746 _72743) = (term684 _120745 _120749 _72744 _72745 _72746 _72743).
Proof. exact (@lem5771734 ((term460 _120745 _120749 _72743 _72745 _72746 _72744) = (term469 _120745 _120749 _72745 _72743 _72746 _72744)) (term444 _120745 _72746) (term685 _120745 _120749 _72745 _72746 _72743)). Qed.
Lemma lem5771763 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term674 _120745 _120749 _72745 _72743 _72746 _72744) = (term684 _120745 _120749 _72744 _72745 _72746 _72743).
Proof. exact (TRANS (@lem5771730 _120745 _120749 _72744 _72745 _72746 _72743) (@lem5771735 _120745 _120749 _72744 _72745 _72746 _72743)). Qed.
Lemma lem5771764 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term673 _120745 _120749 _72745 _72743 _72746 _72744) = (term684 _120745 _120749 _72744 _72745 _72746 _72743).
Proof. exact (TRANS (@lem5771665 _120745 _120749 _72745 _72743 _72746 _72744) (@lem5771763 _120745 _120749 _72744 _72745 _72746 _72743)). Qed.
Lemma lem5771765 {_120745 : Type'} (_72745 : _120745 -> Prop) : (term445 _120745 _72745) = (term445 _120745 _72745).
Proof. exact (eq_refl (term445 _120745 _72745)). Qed.
Lemma lem5771766 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term672 _120745 _120749 _72745 _72743 _72746 _72744) = (term686 _120745 _120749 _72744 _72745 _72746 _72743).
Proof. exact (MK_COMB (@lem5771765 _120745 _72745) (@lem5771764 _120745 _120749 _72744 _72745 _72746 _72743)). Qed.
Lemma lem5771770 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5771771 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term686 _120745 _120749 _72744 _72745 _72746 _72743) = (term687 _120745 _120749 _72744 _72745 _72746 _72743).
Proof. exact (@lem5771770 ((term460 _120745 _120749 _72743 _72745 _72746 _72744) = (term469 _120745 _120749 _72745 _72743 _72746 _72744)) (term444 _120745 _72745) (term688 _120745 _120749 _72745 _72746 _72743)). Qed.
Lemma lem5771809 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term672 _120745 _120749 _72745 _72743 _72746 _72744) = (term687 _120745 _120749 _72744 _72745 _72746 _72743).
Proof. exact (TRANS (@lem5771766 _120745 _120749 _72744 _72745 _72746 _72743) (@lem5771771 _120745 _120749 _72744 _72745 _72746 _72743)). Qed.
Lemma lem5771810 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term623 _120745 _120749 _72745 _72743 _72746 _72744) = (term687 _120745 _120749 _72744 _72745 _72746 _72743).
Proof. exact (TRANS (@lem5771650 _120745 _120749 _72745 _72743 _72746 _72744) (@lem5771809 _120745 _120749 _72744 _72745 _72746 _72743)). Qed.
Lemma lem5771811 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5771812 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term689 _120745 _120749 _72745 _72743 _72746 _72744) = (term690 _120745 _120749 _72744 _72745 _72746 _72743).
Proof. exact (MK_COMB (@lem5771811) (@lem5771810 _120745 _120749 _72744 _72745 _72746 _72743)). Qed.
Lemma lem5771828 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5771829 {_120745 _120749 : Type'} (_72743 : type1400 _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : (term691 _120745 _120749 _72743 _72745 _72746) = (term692 _120745 _120749 _72743 _72745 _72746).
Proof. exact (@lem5771828 (term444 _120745 _72745) (term486 _120749 _72743) (term475 _120745 _72745 _72746)). Qed.
Lemma lem5771843 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5771844 {_120745 _120749 : Type'} (_72743 : type1400 _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : (term693 _120745 _120749 _72743 _72745 _72746) = (term694 _120745 _120749 _72743 _72745 _72746).
Proof. exact (@lem5771843 (term444 _120745 _72746) (term486 _120749 _72743) (term474 _120745 _72745 _72746)). Qed.
Lemma lem5771858 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5771859 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term695 _120745 _120749 _72743 _72745 _72746) = (term685 _120745 _120749 _72745 _72746 _72743).
Proof. exact (@lem5771858 (term474 _120745 _72745 _72746) (term486 _120749 _72743)). Qed.
Lemma lem5771865 {_120745 : Type'} (_72746 : _120745 -> Prop) : (term445 _120745 _72746) = (term445 _120745 _72746).
Proof. exact (eq_refl (term445 _120745 _72746)). Qed.
Lemma lem5771866 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term694 _120745 _120749 _72743 _72745 _72746) = (term688 _120745 _120749 _72745 _72746 _72743).
Proof. exact (MK_COMB (@lem5771865 _120745 _72746) (@lem5771859 _120745 _120749 _72745 _72746 _72743)). Qed.
Lemma lem5771877 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term693 _120745 _120749 _72743 _72745 _72746) = (term688 _120745 _120749 _72745 _72746 _72743).
Proof. exact (TRANS (@lem5771844 _120745 _120749 _72743 _72745 _72746) (@lem5771866 _120745 _120749 _72745 _72746 _72743)). Qed.
Lemma lem5771878 {_120745 : Type'} (_72745 : _120745 -> Prop) : (term445 _120745 _72745) = (term445 _120745 _72745).
Proof. exact (eq_refl (term445 _120745 _72745)). Qed.
Lemma lem5771879 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term692 _120745 _120749 _72743 _72745 _72746) = (term696 _120745 _120749 _72745 _72746 _72743).
Proof. exact (MK_COMB (@lem5771878 _120745 _72745) (@lem5771877 _120745 _120749 _72745 _72746 _72743)). Qed.
Lemma lem5771890 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term691 _120745 _120749 _72743 _72745 _72746) = (term696 _120745 _120749 _72745 _72746 _72743).
Proof. exact (TRANS (@lem5771829 _120745 _120749 _72743 _72745 _72746) (@lem5771879 _120745 _120749 _72745 _72746 _72743)). Qed.
Lemma lem5771891 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) : (term697 _120745 _120749 _72745 _72743 _72746 _72744) = (term697 _120745 _120749 _72745 _72743 _72746 _72744).
Proof. exact (eq_refl (term697 _120745 _120749 _72745 _72743 _72746 _72744)). Qed.
Lemma lem5771892 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : (term698 _120745 _120749 _72744 _72743 _72745 _72746) = (term687 _120745 _120749 _72744 _72745 _72746 _72743).
Proof. exact (MK_COMB (@lem5771891 _120745 _120749 _72745 _72743 _72746 _72744) (@lem5771890 _120745 _120749 _72745 _72746 _72743)). Qed.
Lemma lem5771903 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : ((term623 _120745 _120749 _72745 _72743 _72746 _72744) = (term698 _120745 _120749 _72744 _72743 _72745 _72746)) = ((term687 _120745 _120749 _72744 _72745 _72746 _72743) = (term687 _120745 _120749 _72744 _72745 _72746 _72743)).
Proof. exact (MK_COMB (@lem5771812 _120745 _120749 _72744 _72745 _72746 _72743) (@lem5771892 _120745 _120749 _72744 _72745 _72746 _72743)). Qed.
Lemma lem5771905 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5771906 (x : Prop) : (x = x) = True.
Proof. exact (@lem5771905 Prop x). Qed.
Lemma lem5771907 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (_72743 : type1400 _120749) : ((term687 _120745 _120749 _72744 _72745 _72746 _72743) = (term687 _120745 _120749 _72744 _72745 _72746 _72743)) = True.
Proof. exact (@lem5771906 (term687 _120745 _120749 _72744 _72745 _72746 _72743)). Qed.
Lemma lem5771908 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72743 : type1400 _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : ((term623 _120745 _120749 _72745 _72743 _72746 _72744) = (term698 _120745 _120749 _72744 _72743 _72745 _72746)) = True.
Proof. exact (TRANS (@lem5771903 _120745 _120749 _72744 _72745 _72746 _72743) (@lem5771907 _120745 _120749 _72744 _72745 _72746 _72743)). Qed.
Lemma lem5771909 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72743 : type1400 _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : True = ((term623 _120745 _120749 _72745 _72743 _72746 _72744) = (term698 _120745 _120749 _72744 _72743 _72745 _72746)).
Proof. exact (SYM (@lem5771908 _120745 _120749 _72744 _72743 _72745 _72746)). Qed.
Lemma lem5771910 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72743 : type1400 _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : (term623 _120745 _120749 _72745 _72743 _72746 _72744) = (term698 _120745 _120749 _72744 _72743 _72745 _72746).
Proof. exact (EQ_MP (@lem5771909 _120745 _120749 _72744 _72743 _72745 _72746) (@lem0)). Qed.
Lemma lem5771911 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (_72743 : type1400 _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) (h1 : term186 _120745 _120749) : term698 _120745 _120749 _72744 _72743 _72745 _72746.
Proof. exact (EQ_MP (@lem5771910 _120745 _120749 _72744 _72743 _72745 _72746) (@lem5770845 _120745 _120749 _72745 _72743 _72746 _72744 h1)). Qed.
Lemma lem5771913 (b : Prop) (a : Prop) : (a \/ b) = (term169 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5771914 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) : (term698 _120745 _120749 _72744 _72743 _72745 _72746) = (term699 _120745 _120749 _72745 _72743 _72746 _72744).
Proof. exact (@lem5771913 (term691 _120745 _120749 _72743 _72745 _72746) ((term460 _120745 _120749 _72743 _72745 _72746 _72744) = (term469 _120745 _120749 _72745 _72743 _72746 _72744))). Qed.
Lemma lem5771916 (a : Prop) (b : Prop) : (term647 a b) = (term648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5771917 {_120745 _120749 : Type'} (_72743 : type1400 _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : (term700 _120745 _120749 _72743 _72745 _72746) = (term701 _120745 _120749 _72743 _72745 _72746).
Proof. exact (@lem5771916 (term486 _120749 _72743) (term476 _120745 _72745 _72746)). Qed.
Lemma lem5771919 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5771920 {_120749 : Type'} (_72743 : type1400 _120749) : (term702 _120749 _72743) = (@I ((_120749 -> _120749 -> _120749) -> Prop) (@monoidal _120749) _72743).
Proof. exact (@lem5771919 (@I ((_120749 -> _120749 -> _120749) -> Prop) (@monoidal _120749) _72743)). Qed.
Lemma lem5771921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5771922 {_120749 : Type'} (_72743 : type1400 _120749) : (term703 _120749 _72743) = (term536 _120749 _72743).
Proof. exact (MK_COMB (@lem5771921) (@lem5771920 _120749 _72743)). Qed.
Lemma lem5771924 (a : Prop) (b : Prop) : (term647 a b) = (term648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5771925 {_120745 : Type'} (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : (term704 _120745 _72745 _72746) = (term705 _120745 _72745 _72746).
Proof. exact (@lem5771924 (term444 _120745 _72745) (term475 _120745 _72745 _72746)). Qed.
Lemma lem5771927 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5771928 {_120745 : Type'} (_72745 : _120745 -> Prop) : (term651 _120745 _72745) = (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) _72745).
Proof. exact (@lem5771927 (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) _72745)). Qed.
Lemma lem5771929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5771930 {_120745 : Type'} (_72745 : _120745 -> Prop) : (term652 _120745 _72745) = (term531 _120745 _72745).
Proof. exact (MK_COMB (@lem5771929) (@lem5771928 _120745 _72745)). Qed.
Lemma lem5771932 (a : Prop) (b : Prop) : (term647 a b) = (term648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5771933 {_120745 : Type'} (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : (term706 _120745 _72745 _72746) = (term707 _120745 _72745 _72746).
Proof. exact (@lem5771932 (term444 _120745 _72746) (term474 _120745 _72745 _72746)). Qed.
Lemma lem5771935 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5771936 {_120745 : Type'} (_72746 : _120745 -> Prop) : (term651 _120745 _72746) = (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) _72746).
Proof. exact (@lem5771935 (@I ((_120745 -> Prop) -> Prop) (@FINITE _120745) _72746)). Qed.
Lemma lem5771937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5771938 {_120745 : Type'} (_72746 : _120745 -> Prop) : (term652 _120745 _72746) = (term531 _120745 _72746).
Proof. exact (MK_COMB (@lem5771937) (@lem5771936 _120745 _72746)). Qed.
Lemma lem5771940 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5771941 {_120745 : Type'} (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : (term708 _120745 _72745 _72746) = (term472 _120745 _72745 _72746).
Proof. exact (@lem5771940 (term472 _120745 _72745 _72746)). Qed.
Lemma lem5771942 {_120745 : Type'} (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : (term707 _120745 _72745 _72746) = (term709 _120745 _72745 _72746).
Proof. exact (MK_COMB (@lem5771938 _120745 _72746) (@lem5771941 _120745 _72745 _72746)). Qed.
Lemma lem5771943 {_120745 : Type'} (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : (term706 _120745 _72745 _72746) = (term709 _120745 _72745 _72746).
Proof. exact (TRANS (@lem5771933 _120745 _72745 _72746) (@lem5771942 _120745 _72745 _72746)). Qed.
Lemma lem5771944 {_120745 : Type'} (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : (term705 _120745 _72745 _72746) = (term710 _120745 _72745 _72746).
Proof. exact (MK_COMB (@lem5771930 _120745 _72745) (@lem5771943 _120745 _72745 _72746)). Qed.
Lemma lem5771945 {_120745 : Type'} (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : (term704 _120745 _72745 _72746) = (term710 _120745 _72745 _72746).
Proof. exact (TRANS (@lem5771925 _120745 _72745 _72746) (@lem5771944 _120745 _72745 _72746)). Qed.
Lemma lem5771946 {_120745 _120749 : Type'} (_72743 : type1400 _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : (term701 _120745 _120749 _72743 _72745 _72746) = (term711 _120745 _120749 _72743 _72745 _72746).
Proof. exact (MK_COMB (@lem5771922 _120749 _72743) (@lem5771945 _120745 _72745 _72746)). Qed.
Lemma lem5771947 {_120745 _120749 : Type'} (_72743 : type1400 _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : (term700 _120745 _120749 _72743 _72745 _72746) = (term711 _120745 _120749 _72743 _72745 _72746).
Proof. exact (TRANS (@lem5771917 _120745 _120749 _72743 _72745 _72746) (@lem5771946 _120745 _120749 _72743 _72745 _72746)). Qed.
Lemma lem5771948 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5771949 {_120745 _120749 : Type'} (_72743 : type1400 _120749) (_72745 : _120745 -> Prop) (_72746 : _120745 -> Prop) : (term712 _120745 _120749 _72743 _72745 _72746) = (term713 _120745 _120749 _72743 _72745 _72746).
Proof. exact (MK_COMB (@lem5771948) (@lem5771947 _120745 _120749 _72743 _72745 _72746)). Qed.
Lemma lem5771950 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) : ((term460 _120745 _120749 _72743 _72745 _72746 _72744) = (term469 _120745 _120749 _72745 _72743 _72746 _72744)) = ((term460 _120745 _120749 _72743 _72745 _72746 _72744) = (term469 _120745 _120749 _72745 _72743 _72746 _72744)).
Proof. exact (eq_refl ((term460 _120745 _120749 _72743 _72745 _72746 _72744) = (term469 _120745 _120749 _72745 _72743 _72746 _72744))). Qed.
Lemma lem5771951 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) : (term699 _120745 _120749 _72745 _72743 _72746 _72744) = (term714 _120745 _120749 _72745 _72743 _72746 _72744).
Proof. exact (MK_COMB (@lem5771949 _120745 _120749 _72743 _72745 _72746) (@lem5771950 _120745 _120749 _72745 _72743 _72746 _72744)). Qed.
Lemma lem5771952 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) : (term698 _120745 _120749 _72744 _72743 _72745 _72746) = (term714 _120745 _120749 _72745 _72743 _72746 _72744).
Proof. exact (TRANS (@lem5771914 _120745 _120749 _72745 _72743 _72746 _72744) (@lem5771951 _120745 _120749 _72745 _72743 _72746 _72744)). Qed.
Lemma lem5771954 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term358 _120745 _120749 t op s f) : term715 _120745 s t.
Proof. exact (conj (@lem5771583 _120745 _120749 t op s f h1 h3) (@lem5771643 _120745 _120749 t op s f h2 h3)). Qed.
Lemma lem5771955 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term358 _120745 _120749 t op s f) : term716 _120745 s t.
Proof. exact (conj (@lem5771556 _120745 _120749 t op s f h1 h3 h4) (@lem5771954 _120745 _120749 t op s f h1 h2 h4)). Qed.
Lemma lem5771956 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term358 _120745 _120749 t op s f) : term717 _120745 _120749 op s t.
Proof. exact (conj (@lem5771433 _120745 _120749 t op s f h4) (@lem5771955 _120745 _120749 t op s f h1 h2 h3 h4)). Qed.
Lemma lem5771958 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) (h1 : term186 _120745 _120749) : term714 _120745 _120749 _72745 _72743 _72746 _72744.
Proof. exact (EQ_MP (@lem5771952 _120745 _120749 _72745 _72743 _72746 _72744) (@lem5771911 _120745 _120749 _72744 _72743 _72745 _72746 h1)). Qed.
Lemma lem5771959 {_120745 _120749 : Type'} (_72745 : _120745 -> Prop) (_72743 : type1400 _120749) (_72746 : _120745 -> Prop) (_72744 : _120745 -> _120749) (h1 : term186 _120745 _120749) : term714 _120745 _120749 _72745 _72743 _72746 _72744.
Proof. exact (@lem5771958 _120745 _120749 _72745 _72743 _72746 _72744 h1). Qed.
Lemma lem5771960 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (_72744 : _120745 -> _120749) (h1 : term186 _120745 _120749) : term718 _120745 _120749 s op t _72744.
Proof. exact (@lem5771959 _120745 _120749 (term429 _120745 s t) op t _72744 h1). Qed.
Lemma lem5771963 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term358 _120745 _120749 t op s f) : (term719 _120745 _120749 op s t _72744) = (term525 _120745 _120749 s op t _72744).
Proof. exact (@lem5771960 _120745 _120749 s op t _72744 h4 (@lem5771956 _120745 _120749 t op s f h1 h2 h3 h5)). Qed.
Lemma lem5771964 {_120745 _120749 : Type'} (_72744 : _120745 -> _120749) (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term358 _120745 _120749 t op s f) : (term719 _120745 _120749 op s t _72744) = (term525 _120745 _120749 s op t _72744).
Proof. exact (@lem5771963 _120745 _120749 _72744 t op s f h1 h2 h3 h4 h5). Qed.
Lemma lem5771965 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term358 _120745 _120749 t op s f) : (term719 _120745 _120749 op s t f) = (term525 _120745 _120749 s op t f).
Proof. exact (@lem5771964 _120745 _120749 f t op s f h1 h2 h3 h4 h5). Qed.
Lemma lem5771966 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term358 _120745 _120749 t op s f) : term720 _120745 _120749 s op t f.
Proof. exact (fun h0 : term721 _120745 _120749 s op t f => @lem5771965 _120745 _120749 t op s f h1 h2 h3 h4 h5). Qed.
Lemma lem5771968 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5771969 {_120745 _120749 : Type'} (s : _120745 -> Prop) (op : type1400 _120749) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term720 _120745 _120749 s op t f) = ((term719 _120745 _120749 op s t f) = (term525 _120745 _120749 s op t f)).
Proof. exact (@lem5771968 ((term719 _120745 _120749 op s t f) = (term525 _120745 _120749 s op t f))). Qed.
Lemma lem5771970 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term358 _120745 _120749 t op s f) : (term719 _120745 _120749 op s t f) = (term525 _120745 _120749 s op t f).
Proof. exact (EQ_MP (@lem5771969 _120745 _120749 s op t f) (@lem5771966 _120745 _120749 t op s f h1 h2 h3 h4 h5)). Qed.
Lemma lem5771972 {_120745 _120749 : Type'} (x : _120745 -> _120749) : x = x.
Proof. exact (@lem21386 (_120745 -> _120749) x). Qed.
Lemma lem5771973 {_120745 _120749 : Type'} (x : _120745 -> _120749) : x = x.
Proof. exact (@lem5771972 _120745 _120749 x). Qed.
Lemma lem5771974 {_120745 _120749 : Type'} (f : _120745 -> _120749) : f = f.
Proof. exact (@lem5771973 _120745 _120749 f). Qed.
Lemma lem5771975 {_120745 _120749 : Type'} (f : _120745 -> _120749) : term722 _120745 _120749 f.
Proof. exact (fun h0 : term723 _120745 _120749 f => @lem5771974 _120745 _120749 f). Qed.
Lemma lem5771977 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5771978 {_120745 _120749 : Type'} (f : _120745 -> _120749) : (term722 _120745 _120749 f) = (f = f).
Proof. exact (@lem5771977 (f = f)). Qed.
Lemma lem5771979 {_120745 _120749 : Type'} (f : _120745 -> _120749) : f = f.
Proof. exact (EQ_MP (@lem5771978 _120745 _120749 f) (@lem5771975 _120745 _120749 f)). Qed.
Lemma lem5771981 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term440 _120745 t s.
Proof. exact (proj2 (@lem5769943 _120745 _120749 t op s f h1)). Qed.
Lemma lem5771982 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term662 _120745 t s.
Proof. exact (fun h0 : term442 _120745 t s => @lem5771981 _120745 _120749 t op s f h1). Qed.
Lemma lem5771984 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5771985 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) : (term662 _120745 t s) = (term440 _120745 t s).
Proof. exact (@lem5771984 (term440 _120745 t s)). Qed.
Lemma lem5771986 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term440 _120745 t s.
Proof. exact (EQ_MP (@lem5771985 _120745 t s) (@lem5771982 _120745 _120749 t op s f h1)). Qed.
Lemma lem5771992 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5771993 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : (term624 _120745 _72751 _72752) = (term724 _120745 _72752 _72751).
Proof. exact (@lem5771992 (_72751 = (term502 _120745 _72751 _72752)) (term442 _120745 _72752 _72751)). Qed.
Lemma lem5772001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5772002 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : (term725 _120745 _72751 _72752) = (term726 _120745 _72752 _72751).
Proof. exact (MK_COMB (@lem5772001) (@lem5771993 _120745 _72752 _72751)). Qed.
Lemma lem5772010 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : (term724 _120745 _72752 _72751) = (term724 _120745 _72752 _72751).
Proof. exact (eq_refl (term724 _120745 _72752 _72751)). Qed.
Lemma lem5772011 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : ((term624 _120745 _72751 _72752) = (term724 _120745 _72752 _72751)) = ((term724 _120745 _72752 _72751) = (term724 _120745 _72752 _72751)).
Proof. exact (MK_COMB (@lem5772002 _120745 _72752 _72751) (@lem5772010 _120745 _72752 _72751)). Qed.
Lemma lem5772013 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5772014 (x : Prop) : (x = x) = True.
Proof. exact (@lem5772013 Prop x). Qed.
Lemma lem5772015 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : ((term724 _120745 _72752 _72751) = (term724 _120745 _72752 _72751)) = True.
Proof. exact (@lem5772014 (term724 _120745 _72752 _72751)). Qed.
Lemma lem5772016 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : ((term624 _120745 _72751 _72752) = (term724 _120745 _72752 _72751)) = True.
Proof. exact (TRANS (@lem5772011 _120745 _72752 _72751) (@lem5772015 _120745 _72752 _72751)). Qed.
Lemma lem5772017 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : True = ((term624 _120745 _72751 _72752) = (term724 _120745 _72752 _72751)).
Proof. exact (SYM (@lem5772016 _120745 _72752 _72751)). Qed.
Lemma lem5772018 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : (term624 _120745 _72751 _72752) = (term724 _120745 _72752 _72751).
Proof. exact (EQ_MP (@lem5772017 _120745 _72752 _72751) (@lem0)). Qed.
Lemma lem5772019 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) (h1 : term182 _120745) : term724 _120745 _72752 _72751.
Proof. exact (EQ_MP (@lem5772018 _120745 _72752 _72751) (@lem5770925 _120745 _72751 _72752 h1)). Qed.
Lemma lem5772021 (b : Prop) (a : Prop) : (a \/ b) = (term169 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5772022 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) : (term724 _120745 _72752 _72751) = (term727 _120745 _72751 _72752).
Proof. exact (@lem5772021 (term442 _120745 _72752 _72751) (_72751 = (term502 _120745 _72751 _72752))). Qed.
Lemma lem5772024 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5772025 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : (term653 _120745 _72752 _72751) = (term440 _120745 _72752 _72751).
Proof. exact (@lem5772024 (term440 _120745 _72752 _72751)). Qed.
Lemma lem5772026 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5772027 {_120745 : Type'} (_72752 : _120745 -> Prop) (_72751 : _120745 -> Prop) : (term667 _120745 _72752 _72751) = (term668 _120745 _72752 _72751).
Proof. exact (MK_COMB (@lem5772026) (@lem5772025 _120745 _72752 _72751)). Qed.
Lemma lem5772028 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) : (_72751 = (term502 _120745 _72751 _72752)) = (_72751 = (term502 _120745 _72751 _72752)).
Proof. exact (eq_refl (_72751 = (term502 _120745 _72751 _72752))). Qed.
Lemma lem5772029 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) : (term727 _120745 _72751 _72752) = (term728 _120745 _72751 _72752).
Proof. exact (MK_COMB (@lem5772027 _120745 _72752 _72751) (@lem5772028 _120745 _72751 _72752)). Qed.
Lemma lem5772030 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) : (term724 _120745 _72752 _72751) = (term728 _120745 _72751 _72752).
Proof. exact (TRANS (@lem5772022 _120745 _72751 _72752) (@lem5772029 _120745 _72751 _72752)). Qed.
Lemma lem5772033 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) (h1 : term182 _120745) : term728 _120745 _72751 _72752.
Proof. exact (EQ_MP (@lem5772030 _120745 _72751 _72752) (@lem5772019 _120745 _72752 _72751 h1)). Qed.
Lemma lem5772034 {_120745 : Type'} (_72751 : _120745 -> Prop) (_72752 : _120745 -> Prop) (h1 : term182 _120745) : term728 _120745 _72751 _72752.
Proof. exact (@lem5772033 _120745 _72751 _72752 h1). Qed.
Lemma lem5772035 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) (h1 : term182 _120745) : term728 _120745 s t.
Proof. exact (@lem5772034 _120745 s t h1). Qed.
Lemma lem5772038 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : s = (term502 _120745 s t).
Proof. exact (@lem5772035 _120745 s t h1 (@lem5771986 _120745 _120749 t op s f h2)). Qed.
Lemma lem5772039 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : term729 _120745 s t.
Proof. exact (fun h0 : term730 _120745 s t => @lem5772038 _120745 _120749 t op s f h1 h2). Qed.
Lemma lem5772041 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5772042 {_120745 : Type'} (s : _120745 -> Prop) (t : _120745 -> Prop) : (term729 _120745 s t) = (s = (term502 _120745 s t)).
Proof. exact (@lem5772041 (s = (term502 _120745 s t))). Qed.
Lemma lem5772043 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : s = (term502 _120745 s t).
Proof. exact (EQ_MP (@lem5772042 _120745 s t) (@lem5772039 _120745 _120749 t op s f h1 h2)). Qed.
Lemma lem5772045 {_120745 _120749 : Type'} (x : type632 _120745 _120749) : x = x.
Proof. exact (@lem21386 (type632 _120745 _120749) x). Qed.
Lemma lem5772046 {_120745 _120749 : Type'} (x : type632 _120745 _120749) : x = x.
Proof. exact (@lem5772045 _120745 _120749 x). Qed.
Lemma lem5772047 {_120745 _120749 : Type'} (op : type1400 _120749) : (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op).
Proof. exact (@lem5772046 _120745 _120749 (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op)). Qed.
Lemma lem5772048 {_120745 _120749 : Type'} (op : type1400 _120749) : term731 _120745 _120749 op.
Proof. exact (fun h0 : term732 _120745 _120749 op => @lem5772047 _120745 _120749 op). Qed.
Lemma lem5772050 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5772051 {_120745 _120749 : Type'} (op : type1400 _120749) : (term731 _120745 _120749 op) = ((@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op)).
Proof. exact (@lem5772050 ((@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op))). Qed.
Lemma lem5772052 {_120745 _120749 : Type'} (op : type1400 _120749) : (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op) = (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op).
Proof. exact (EQ_MP (@lem5772051 _120745 _120749 op) (@lem5772048 _120745 _120749 op)). Qed.
Lemma lem5772070 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5772071 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : (term628 _120745 _120749 _72797 _72798 _72799 _72800) = (term733 _120745 _120749 _72798 _72800 _72797 _72799).
Proof. exact (@lem5772070 ((@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72797 _72798) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72799 _72800)) (term734 _120745 _120749 _72797 _72799)). Qed.
Lemma lem5772081 {_120745 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) : (term735 _120745 _72798 _72800) = (term735 _120745 _72798 _72800).
Proof. exact (eq_refl (term735 _120745 _72798 _72800)). Qed.
Lemma lem5772082 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : (term630 _120745 _120749 _72797 _72798 _72799 _72800) = (term736 _120745 _120749 _72798 _72800 _72797 _72799).
Proof. exact (MK_COMB (@lem5772081 _120745 _72798 _72800) (@lem5772071 _120745 _120749 _72798 _72800 _72797 _72799)). Qed.
Lemma lem5772086 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5772087 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : (term736 _120745 _120749 _72798 _72800 _72797 _72799) = (term737 _120745 _120749 _72798 _72800 _72797 _72799).
Proof. exact (@lem5772086 ((@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72797 _72798) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72799 _72800)) (term738 _120745 _72798 _72800) (term734 _120745 _120749 _72797 _72799)). Qed.
Lemma lem5772109 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : (term630 _120745 _120749 _72797 _72798 _72799 _72800) = (term737 _120745 _120749 _72798 _72800 _72797 _72799).
Proof. exact (TRANS (@lem5772082 _120745 _120749 _72798 _72800 _72797 _72799) (@lem5772087 _120745 _120749 _72798 _72800 _72797 _72799)). Qed.
Lemma lem5772110 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5772111 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : (term739 _120745 _120749 _72797 _72798 _72799 _72800) = (term740 _120745 _120749 _72798 _72800 _72797 _72799).
Proof. exact (MK_COMB (@lem5772110) (@lem5772109 _120745 _120749 _72798 _72800 _72797 _72799)). Qed.
Lemma lem5772133 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : (term737 _120745 _120749 _72798 _72800 _72797 _72799) = (term737 _120745 _120749 _72798 _72800 _72797 _72799).
Proof. exact (eq_refl (term737 _120745 _120749 _72798 _72800 _72797 _72799)). Qed.
Lemma lem5772134 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : ((term630 _120745 _120749 _72797 _72798 _72799 _72800) = (term737 _120745 _120749 _72798 _72800 _72797 _72799)) = ((term737 _120745 _120749 _72798 _72800 _72797 _72799) = (term737 _120745 _120749 _72798 _72800 _72797 _72799)).
Proof. exact (MK_COMB (@lem5772111 _120745 _120749 _72798 _72800 _72797 _72799) (@lem5772133 _120745 _120749 _72798 _72800 _72797 _72799)). Qed.
Lemma lem5772136 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5772137 (x : Prop) : (x = x) = True.
Proof. exact (@lem5772136 Prop x). Qed.
Lemma lem5772138 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : ((term737 _120745 _120749 _72798 _72800 _72797 _72799) = (term737 _120745 _120749 _72798 _72800 _72797 _72799)) = True.
Proof. exact (@lem5772137 (term737 _120745 _120749 _72798 _72800 _72797 _72799)). Qed.
Lemma lem5772139 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : ((term630 _120745 _120749 _72797 _72798 _72799 _72800) = (term737 _120745 _120749 _72798 _72800 _72797 _72799)) = True.
Proof. exact (TRANS (@lem5772134 _120745 _120749 _72798 _72800 _72797 _72799) (@lem5772138 _120745 _120749 _72798 _72800 _72797 _72799)). Qed.
Lemma lem5772140 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : True = ((term630 _120745 _120749 _72797 _72798 _72799 _72800) = (term737 _120745 _120749 _72798 _72800 _72797 _72799)).
Proof. exact (SYM (@lem5772139 _120745 _120749 _72798 _72800 _72797 _72799)). Qed.
Lemma lem5772141 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : (term630 _120745 _120749 _72797 _72798 _72799 _72800) = (term737 _120745 _120749 _72798 _72800 _72797 _72799).
Proof. exact (EQ_MP (@lem5772140 _120745 _120749 _72798 _72800 _72797 _72799) (@lem0)). Qed.
Lemma lem5772142 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : term737 _120745 _120749 _72798 _72800 _72797 _72799.
Proof. exact (EQ_MP (@lem5772141 _120745 _120749 _72798 _72800 _72797 _72799) (@lem5771101 _120745 _120749 _72797 _72798 _72799 _72800)). Qed.
Lemma lem5772144 (b : Prop) (a : Prop) : (a \/ b) = (term169 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5772145 {_120745 _120749 : Type'} (_72797 : type632 _120745 _120749) (_72798 : _120745 -> Prop) (_72799 : type632 _120745 _120749) (_72800 : _120745 -> Prop) : (term737 _120745 _120749 _72798 _72800 _72797 _72799) = (term741 _120745 _120749 _72797 _72798 _72799 _72800).
Proof. exact (@lem5772144 (term742 _120745 _120749 _72798 _72800 _72797 _72799) ((@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72797 _72798) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72799 _72800))). Qed.
Lemma lem5772147 (a : Prop) (b : Prop) : (term647 a b) = (term648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5772148 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : (term743 _120745 _120749 _72798 _72800 _72797 _72799) = (term744 _120745 _120749 _72798 _72800 _72797 _72799).
Proof. exact (@lem5772147 (term738 _120745 _72798 _72800) (term734 _120745 _120749 _72797 _72799)). Qed.
Lemma lem5772150 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5772151 {_120745 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) : (term745 _120745 _72798 _72800) = (_72798 = _72800).
Proof. exact (@lem5772150 (_72798 = _72800)). Qed.
Lemma lem5772152 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5772153 {_120745 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) : (term746 _120745 _72798 _72800) = (term747 _120745 _72798 _72800).
Proof. exact (MK_COMB (@lem5772152) (@lem5772151 _120745 _72798 _72800)). Qed.
Lemma lem5772155 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5772156 {_120745 _120749 : Type'} (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : (term748 _120745 _120749 _72797 _72799) = (_72797 = _72799).
Proof. exact (@lem5772155 (_72797 = _72799)). Qed.
Lemma lem5772157 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : (term744 _120745 _120749 _72798 _72800 _72797 _72799) = (term749 _120745 _120749 _72798 _72800 _72797 _72799).
Proof. exact (MK_COMB (@lem5772153 _120745 _72798 _72800) (@lem5772156 _120745 _120749 _72797 _72799)). Qed.
Lemma lem5772158 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : (term743 _120745 _120749 _72798 _72800 _72797 _72799) = (term749 _120745 _120749 _72798 _72800 _72797 _72799).
Proof. exact (TRANS (@lem5772148 _120745 _120749 _72798 _72800 _72797 _72799) (@lem5772157 _120745 _120749 _72798 _72800 _72797 _72799)). Qed.
Lemma lem5772159 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5772160 {_120745 _120749 : Type'} (_72798 : _120745 -> Prop) (_72800 : _120745 -> Prop) (_72797 : type632 _120745 _120749) (_72799 : type632 _120745 _120749) : (term750 _120745 _120749 _72798 _72800 _72797 _72799) = (term751 _120745 _120749 _72798 _72800 _72797 _72799).
Proof. exact (MK_COMB (@lem5772159) (@lem5772158 _120745 _120749 _72798 _72800 _72797 _72799)). Qed.
Lemma lem5772161 {_120745 _120749 : Type'} (_72797 : type632 _120745 _120749) (_72798 : _120745 -> Prop) (_72799 : type632 _120745 _120749) (_72800 : _120745 -> Prop) : ((@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72797 _72798) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72799 _72800)) = ((@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72797 _72798) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72799 _72800)).
Proof. exact (eq_refl ((@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72797 _72798) = (@I ((_120745 -> Prop) -> (_120745 -> _120749) -> _120749) _72799 _72800))). Qed.
Lemma lem5772162 {_120745 _120749 : Type'} (_72797 : type632 _120745 _120749) (_72798 : _120745 -> Prop) (_72799 : type632 _120745 _120749) (_72800 : _120745 -> Prop) : (term741 _120745 _120749 _72797 _72798 _72799 _72800) = (term752 _120745 _120749 _72797 _72798 _72799 _72800).
Proof. exact (MK_COMB (@lem5772160 _120745 _120749 _72798 _72800 _72797 _72799) (@lem5772161 _120745 _120749 _72797 _72798 _72799 _72800)). Qed.
Lemma lem5772163 {_120745 _120749 : Type'} (_72797 : type632 _120745 _120749) (_72798 : _120745 -> Prop) (_72799 : type632 _120745 _120749) (_72800 : _120745 -> Prop) : (term737 _120745 _120749 _72798 _72800 _72797 _72799) = (term752 _120745 _120749 _72797 _72798 _72799 _72800).
Proof. exact (TRANS (@lem5772145 _120745 _120749 _72797 _72798 _72799 _72800) (@lem5772162 _120745 _120749 _72797 _72798 _72799 _72800)). Qed.
Lemma lem5772165 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : term753 _120745 _120749 s t op.
Proof. exact (conj (@lem5772043 _120745 _120749 t op s f h1 h2) (@lem5772052 _120745 _120749 op)). Qed.
Lemma lem5772167 {_120745 _120749 : Type'} (_72797 : type632 _120745 _120749) (_72798 : _120745 -> Prop) (_72799 : type632 _120745 _120749) (_72800 : _120745 -> Prop) : term752 _120745 _120749 _72797 _72798 _72799 _72800.
Proof. exact (EQ_MP (@lem5772163 _120745 _120749 _72797 _72798 _72799 _72800) (@lem5772142 _120745 _120749 _72798 _72800 _72797 _72799)). Qed.
Lemma lem5772168 {_120745 _120749 : Type'} (_72797 : type632 _120745 _120749) (_72798 : _120745 -> Prop) (_72799 : type632 _120745 _120749) (_72800 : _120745 -> Prop) : term752 _120745 _120749 _72797 _72798 _72799 _72800.
Proof. exact (@lem5772167 _120745 _120749 _72797 _72798 _72799 _72800). Qed.
Lemma lem5772169 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) : term754 _120745 _120749 op s t.
Proof. exact (@lem5772168 _120745 _120749 (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op) s (@I ((_120749 -> _120749 -> _120749) -> (_120745 -> Prop) -> (_120745 -> _120749) -> _120749) (@iterate _120749 _120745) op) (term502 _120745 s t)). Qed.
Lemma lem5772172 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : (term461 _120745 _120749 op s) = (term755 _120745 _120749 op s t).
Proof. exact (@lem5772169 _120745 _120749 op s t (@lem5772165 _120745 _120749 t op s f h1 h2)). Qed.
Lemma lem5772173 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : term756 _120745 _120749 op s t.
Proof. exact (fun h0 : term757 _120745 _120749 op s t => @lem5772172 _120745 _120749 t op s f h1 h2). Qed.
Lemma lem5772175 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5772176 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) : (term756 _120745 _120749 op s t) = ((term461 _120745 _120749 op s) = (term755 _120745 _120749 op s t)).
Proof. exact (@lem5772175 ((term461 _120745 _120749 op s) = (term755 _120745 _120749 op s t))). Qed.
Lemma lem5772177 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : (term461 _120745 _120749 op s) = (term755 _120745 _120749 op s t).
Proof. exact (EQ_MP (@lem5772176 _120745 _120749 op s t) (@lem5772173 _120745 _120749 t op s f h1 h2)). Qed.
Lemma lem5772195 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5772196 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : (term632 _120745 _120749 _72801 _72802 _72803 _72804) = (term758 _120745 _120749 _72802 _72804 _72801 _72803).
Proof. exact (@lem5772195 ((@I ((_120745 -> _120749) -> _120749) _72801 _72802) = (@I ((_120745 -> _120749) -> _120749) _72803 _72804)) (term759 _120745 _120749 _72801 _72803)). Qed.
Lemma lem5772206 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) : (term760 _120745 _120749 _72802 _72804) = (term760 _120745 _120749 _72802 _72804).
Proof. exact (eq_refl (term760 _120745 _120749 _72802 _72804)). Qed.
Lemma lem5772207 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : (term634 _120745 _120749 _72801 _72802 _72803 _72804) = (term761 _120745 _120749 _72802 _72804 _72801 _72803).
Proof. exact (MK_COMB (@lem5772206 _120745 _120749 _72802 _72804) (@lem5772196 _120745 _120749 _72802 _72804 _72801 _72803)). Qed.
Lemma lem5772211 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5772212 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : (term761 _120745 _120749 _72802 _72804 _72801 _72803) = (term762 _120745 _120749 _72802 _72804 _72801 _72803).
Proof. exact (@lem5772211 ((@I ((_120745 -> _120749) -> _120749) _72801 _72802) = (@I ((_120745 -> _120749) -> _120749) _72803 _72804)) (term763 _120745 _120749 _72802 _72804) (term759 _120745 _120749 _72801 _72803)). Qed.
Lemma lem5772234 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : (term634 _120745 _120749 _72801 _72802 _72803 _72804) = (term762 _120745 _120749 _72802 _72804 _72801 _72803).
Proof. exact (TRANS (@lem5772207 _120745 _120749 _72802 _72804 _72801 _72803) (@lem5772212 _120745 _120749 _72802 _72804 _72801 _72803)). Qed.
Lemma lem5772235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5772236 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : (term764 _120745 _120749 _72801 _72802 _72803 _72804) = (term765 _120745 _120749 _72802 _72804 _72801 _72803).
Proof. exact (MK_COMB (@lem5772235) (@lem5772234 _120745 _120749 _72802 _72804 _72801 _72803)). Qed.
Lemma lem5772258 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : (term762 _120745 _120749 _72802 _72804 _72801 _72803) = (term762 _120745 _120749 _72802 _72804 _72801 _72803).
Proof. exact (eq_refl (term762 _120745 _120749 _72802 _72804 _72801 _72803)). Qed.
Lemma lem5772259 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : ((term634 _120745 _120749 _72801 _72802 _72803 _72804) = (term762 _120745 _120749 _72802 _72804 _72801 _72803)) = ((term762 _120745 _120749 _72802 _72804 _72801 _72803) = (term762 _120745 _120749 _72802 _72804 _72801 _72803)).
Proof. exact (MK_COMB (@lem5772236 _120745 _120749 _72802 _72804 _72801 _72803) (@lem5772258 _120745 _120749 _72802 _72804 _72801 _72803)). Qed.
Lemma lem5772261 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5772262 (x : Prop) : (x = x) = True.
Proof. exact (@lem5772261 Prop x). Qed.
Lemma lem5772263 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : ((term762 _120745 _120749 _72802 _72804 _72801 _72803) = (term762 _120745 _120749 _72802 _72804 _72801 _72803)) = True.
Proof. exact (@lem5772262 (term762 _120745 _120749 _72802 _72804 _72801 _72803)). Qed.
Lemma lem5772264 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : ((term634 _120745 _120749 _72801 _72802 _72803 _72804) = (term762 _120745 _120749 _72802 _72804 _72801 _72803)) = True.
Proof. exact (TRANS (@lem5772259 _120745 _120749 _72802 _72804 _72801 _72803) (@lem5772263 _120745 _120749 _72802 _72804 _72801 _72803)). Qed.
Lemma lem5772265 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : True = ((term634 _120745 _120749 _72801 _72802 _72803 _72804) = (term762 _120745 _120749 _72802 _72804 _72801 _72803)).
Proof. exact (SYM (@lem5772264 _120745 _120749 _72802 _72804 _72801 _72803)). Qed.
Lemma lem5772266 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : (term634 _120745 _120749 _72801 _72802 _72803 _72804) = (term762 _120745 _120749 _72802 _72804 _72801 _72803).
Proof. exact (EQ_MP (@lem5772265 _120745 _120749 _72802 _72804 _72801 _72803) (@lem0)). Qed.
Lemma lem5772267 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : term762 _120745 _120749 _72802 _72804 _72801 _72803.
Proof. exact (EQ_MP (@lem5772266 _120745 _120749 _72802 _72804 _72801 _72803) (@lem5771116 _120745 _120749 _72801 _72802 _72803 _72804)). Qed.
Lemma lem5772269 (b : Prop) (a : Prop) : (a \/ b) = (term169 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5772270 {_120745 _120749 : Type'} (_72801 : type570 _120745 _120749) (_72802 : _120745 -> _120749) (_72803 : type570 _120745 _120749) (_72804 : _120745 -> _120749) : (term762 _120745 _120749 _72802 _72804 _72801 _72803) = (term766 _120745 _120749 _72801 _72802 _72803 _72804).
Proof. exact (@lem5772269 (term767 _120745 _120749 _72802 _72804 _72801 _72803) ((@I ((_120745 -> _120749) -> _120749) _72801 _72802) = (@I ((_120745 -> _120749) -> _120749) _72803 _72804))). Qed.
Lemma lem5772272 (a : Prop) (b : Prop) : (term647 a b) = (term648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5772273 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : (term768 _120745 _120749 _72802 _72804 _72801 _72803) = (term769 _120745 _120749 _72802 _72804 _72801 _72803).
Proof. exact (@lem5772272 (term763 _120745 _120749 _72802 _72804) (term759 _120745 _120749 _72801 _72803)). Qed.
Lemma lem5772275 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5772276 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) : (term770 _120745 _120749 _72802 _72804) = (_72802 = _72804).
Proof. exact (@lem5772275 (_72802 = _72804)). Qed.
Lemma lem5772277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5772278 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) : (term771 _120745 _120749 _72802 _72804) = (term772 _120745 _120749 _72802 _72804).
Proof. exact (MK_COMB (@lem5772277) (@lem5772276 _120745 _120749 _72802 _72804)). Qed.
Lemma lem5772280 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5772281 {_120745 _120749 : Type'} (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : (term773 _120745 _120749 _72801 _72803) = (_72801 = _72803).
Proof. exact (@lem5772280 (_72801 = _72803)). Qed.
Lemma lem5772282 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : (term769 _120745 _120749 _72802 _72804 _72801 _72803) = (term774 _120745 _120749 _72802 _72804 _72801 _72803).
Proof. exact (MK_COMB (@lem5772278 _120745 _120749 _72802 _72804) (@lem5772281 _120745 _120749 _72801 _72803)). Qed.
Lemma lem5772283 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : (term768 _120745 _120749 _72802 _72804 _72801 _72803) = (term774 _120745 _120749 _72802 _72804 _72801 _72803).
Proof. exact (TRANS (@lem5772273 _120745 _120749 _72802 _72804 _72801 _72803) (@lem5772282 _120745 _120749 _72802 _72804 _72801 _72803)). Qed.
Lemma lem5772284 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5772285 {_120745 _120749 : Type'} (_72802 : _120745 -> _120749) (_72804 : _120745 -> _120749) (_72801 : type570 _120745 _120749) (_72803 : type570 _120745 _120749) : (term775 _120745 _120749 _72802 _72804 _72801 _72803) = (term776 _120745 _120749 _72802 _72804 _72801 _72803).
Proof. exact (MK_COMB (@lem5772284) (@lem5772283 _120745 _120749 _72802 _72804 _72801 _72803)). Qed.
Lemma lem5772286 {_120745 _120749 : Type'} (_72801 : type570 _120745 _120749) (_72802 : _120745 -> _120749) (_72803 : type570 _120745 _120749) (_72804 : _120745 -> _120749) : ((@I ((_120745 -> _120749) -> _120749) _72801 _72802) = (@I ((_120745 -> _120749) -> _120749) _72803 _72804)) = ((@I ((_120745 -> _120749) -> _120749) _72801 _72802) = (@I ((_120745 -> _120749) -> _120749) _72803 _72804)).
Proof. exact (eq_refl ((@I ((_120745 -> _120749) -> _120749) _72801 _72802) = (@I ((_120745 -> _120749) -> _120749) _72803 _72804))). Qed.
Lemma lem5772287 {_120745 _120749 : Type'} (_72801 : type570 _120745 _120749) (_72802 : _120745 -> _120749) (_72803 : type570 _120745 _120749) (_72804 : _120745 -> _120749) : (term766 _120745 _120749 _72801 _72802 _72803 _72804) = (term777 _120745 _120749 _72801 _72802 _72803 _72804).
Proof. exact (MK_COMB (@lem5772285 _120745 _120749 _72802 _72804 _72801 _72803) (@lem5772286 _120745 _120749 _72801 _72802 _72803 _72804)). Qed.
Lemma lem5772288 {_120745 _120749 : Type'} (_72801 : type570 _120745 _120749) (_72802 : _120745 -> _120749) (_72803 : type570 _120745 _120749) (_72804 : _120745 -> _120749) : (term762 _120745 _120749 _72802 _72804 _72801 _72803) = (term777 _120745 _120749 _72801 _72802 _72803 _72804).
Proof. exact (TRANS (@lem5772270 _120745 _120749 _72801 _72802 _72803 _72804) (@lem5772287 _120745 _120749 _72801 _72802 _72803 _72804)). Qed.
Lemma lem5772290 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : term778 _120745 _120749 f op s t.
Proof. exact (conj (@lem5771979 _120745 _120749 f) (@lem5772177 _120745 _120749 t op s f h1 h2)). Qed.
Lemma lem5772292 {_120745 _120749 : Type'} (_72801 : type570 _120745 _120749) (_72802 : _120745 -> _120749) (_72803 : type570 _120745 _120749) (_72804 : _120745 -> _120749) : term777 _120745 _120749 _72801 _72802 _72803 _72804.
Proof. exact (EQ_MP (@lem5772288 _120745 _120749 _72801 _72802 _72803 _72804) (@lem5772267 _120745 _120749 _72802 _72804 _72801 _72803)). Qed.
Lemma lem5772293 {_120745 _120749 : Type'} (_72801 : type570 _120745 _120749) (_72802 : _120745 -> _120749) (_72803 : type570 _120745 _120749) (_72804 : _120745 -> _120749) : term777 _120745 _120749 _72801 _72802 _72803 _72804.
Proof. exact (@lem5772292 _120745 _120749 _72801 _72802 _72803 _72804). Qed.
Lemma lem5772294 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) (f : _120745 -> _120749) : term779 _120745 _120749 op s t f.
Proof. exact (@lem5772293 _120745 _120749 (term461 _120745 _120749 op s) f (term755 _120745 _120749 op s t) f). Qed.
Lemma lem5772297 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : (term463 _120745 _120749 op s f) = (term719 _120745 _120749 op s t f).
Proof. exact (@lem5772294 _120745 _120749 op s t f (@lem5772290 _120745 _120749 t op s f h1 h2)). Qed.
Lemma lem5772298 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : term780 _120745 _120749 op s t f.
Proof. exact (fun h0 : term781 _120745 _120749 op s t f => @lem5772297 _120745 _120749 t op s f h1 h2). Qed.
Lemma lem5772300 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5772301 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (t : _120745 -> Prop) (f : _120745 -> _120749) : (term780 _120745 _120749 op s t f) = ((term463 _120745 _120749 op s f) = (term719 _120745 _120749 op s t f)).
Proof. exact (@lem5772300 ((term463 _120745 _120749 op s f) = (term719 _120745 _120749 op s t f))). Qed.
Lemma lem5772302 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : (term463 _120745 _120749 op s f) = (term719 _120745 _120749 op s t f).
Proof. exact (EQ_MP (@lem5772301 _120745 _120749 op s t f) (@lem5772298 _120745 _120749 t op s f h1 h2)). Qed.
Lemma lem5772304 {_120749 : Type'} (x : _120749) : x = x.
Proof. exact (@lem21386 _120749 x). Qed.
Lemma lem5772305 {_120749 : Type'} (x : _120749) : x = x.
Proof. exact (@lem5772304 _120749 x). Qed.
Lemma lem5772306 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term463 _120745 _120749 op s f) = (term463 _120745 _120749 op s f).
Proof. exact (@lem5772305 _120749 (term463 _120745 _120749 op s f)). Qed.
Lemma lem5772307 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : term782 _120745 _120749 op s f.
Proof. exact (fun h0 : term783 _120745 _120749 op s f => @lem5772306 _120745 _120749 op s f). Qed.
Lemma lem5772309 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5772310 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term782 _120745 _120749 op s f) = ((term463 _120745 _120749 op s f) = (term463 _120745 _120749 op s f)).
Proof. exact (@lem5772309 ((term463 _120745 _120749 op s f) = (term463 _120745 _120749 op s f))). Qed.
Lemma lem5772311 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term463 _120745 _120749 op s f) = (term463 _120745 _120749 op s f).
Proof. exact (EQ_MP (@lem5772310 _120745 _120749 op s f) (@lem5772307 _120745 _120749 op s f)). Qed.
Lemma lem5772329 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5772330 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : (term784 _120749 x y z) = (term785 _120749 y x z).
Proof. exact (@lem5772329 (y = z) (term786 _120749 x z)). Qed.
Lemma lem5772340 {_120749 : Type'} (x : _120749) (y : _120749) : (term787 _120749 x y) = (term787 _120749 x y).
Proof. exact (eq_refl (term787 _120749 x y)). Qed.
Lemma lem5772341 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : (term635 _120749 x y z) = (term788 _120749 y x z).
Proof. exact (MK_COMB (@lem5772340 _120749 x y) (@lem5772330 _120749 y x z)). Qed.
Lemma lem5772345 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5772346 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : (term788 _120749 y x z) = (term789 _120749 y x z).
Proof. exact (@lem5772345 (y = z) (term786 _120749 x y) (term786 _120749 x z)). Qed.
Lemma lem5772368 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : (term635 _120749 x y z) = (term789 _120749 y x z).
Proof. exact (TRANS (@lem5772341 _120749 y x z) (@lem5772346 _120749 y x z)). Qed.
Lemma lem5772369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5772370 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : (term790 _120749 x y z) = (term791 _120749 y x z).
Proof. exact (MK_COMB (@lem5772369) (@lem5772368 _120749 y x z)). Qed.
Lemma lem5772392 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : (term789 _120749 y x z) = (term789 _120749 y x z).
Proof. exact (eq_refl (term789 _120749 y x z)). Qed.
Lemma lem5772393 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : ((term635 _120749 x y z) = (term789 _120749 y x z)) = ((term789 _120749 y x z) = (term789 _120749 y x z)).
Proof. exact (MK_COMB (@lem5772370 _120749 y x z) (@lem5772392 _120749 y x z)). Qed.
Lemma lem5772395 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5772396 (x : Prop) : (x = x) = True.
Proof. exact (@lem5772395 Prop x). Qed.
Lemma lem5772397 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : ((term789 _120749 y x z) = (term789 _120749 y x z)) = True.
Proof. exact (@lem5772396 (term789 _120749 y x z)). Qed.
Lemma lem5772398 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : ((term635 _120749 x y z) = (term789 _120749 y x z)) = True.
Proof. exact (TRANS (@lem5772393 _120749 y x z) (@lem5772397 _120749 y x z)). Qed.
Lemma lem5772399 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : True = ((term635 _120749 x y z) = (term789 _120749 y x z)).
Proof. exact (SYM (@lem5772398 _120749 y x z)). Qed.
Lemma lem5772400 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : (term635 _120749 x y z) = (term789 _120749 y x z).
Proof. exact (EQ_MP (@lem5772399 _120749 y x z) (@lem0)). Qed.
Lemma lem5772401 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : term789 _120749 y x z.
Proof. exact (EQ_MP (@lem5772400 _120749 y x z) (@lem5771392 _120749 x y z)). Qed.
Lemma lem5772403 (b : Prop) (a : Prop) : (a \/ b) = (term169 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5772404 {_120749 : Type'} (x : _120749) (y : _120749) (z : _120749) : (term789 _120749 y x z) = (term792 _120749 x y z).
Proof. exact (@lem5772403 (term793 _120749 y x z) (y = z)). Qed.
Lemma lem5772406 (a : Prop) (b : Prop) : (term647 a b) = (term648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5772407 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : (term794 _120749 y x z) = (term795 _120749 y x z).
Proof. exact (@lem5772406 (term786 _120749 x y) (term786 _120749 x z)). Qed.
Lemma lem5772409 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5772410 {_120749 : Type'} (x : _120749) (y : _120749) : (term796 _120749 x y) = (x = y).
Proof. exact (@lem5772409 (x = y)). Qed.
Lemma lem5772411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5772412 {_120749 : Type'} (x : _120749) (y : _120749) : (term797 _120749 x y) = (term798 _120749 x y).
Proof. exact (MK_COMB (@lem5772411) (@lem5772410 _120749 x y)). Qed.
Lemma lem5772414 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5772415 {_120749 : Type'} (x : _120749) (z : _120749) : (term796 _120749 x z) = (x = z).
Proof. exact (@lem5772414 (x = z)). Qed.
Lemma lem5772416 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : (term795 _120749 y x z) = (term799 _120749 y x z).
Proof. exact (MK_COMB (@lem5772412 _120749 x y) (@lem5772415 _120749 x z)). Qed.
Lemma lem5772417 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : (term794 _120749 y x z) = (term799 _120749 y x z).
Proof. exact (TRANS (@lem5772407 _120749 y x z) (@lem5772416 _120749 y x z)). Qed.
Lemma lem5772418 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5772419 {_120749 : Type'} (y : _120749) (x : _120749) (z : _120749) : (term800 _120749 y x z) = (term801 _120749 y x z).
Proof. exact (MK_COMB (@lem5772418) (@lem5772417 _120749 y x z)). Qed.
Lemma lem5772420 {_120749 : Type'} (y : _120749) (z : _120749) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5772421 {_120749 : Type'} (x : _120749) (y : _120749) (z : _120749) : (term792 _120749 x y z) = (term802 _120749 x y z).
Proof. exact (MK_COMB (@lem5772419 _120749 y x z) (@lem5772420 _120749 y z)). Qed.
Lemma lem5772422 {_120749 : Type'} (x : _120749) (y : _120749) (z : _120749) : (term789 _120749 y x z) = (term802 _120749 x y z).
Proof. exact (TRANS (@lem5772404 _120749 x y z) (@lem5772421 _120749 x y z)). Qed.
Lemma lem5772424 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : term803 _120745 _120749 t op s f.
Proof. exact (conj (@lem5772302 _120745 _120749 t op s f h1 h2) (@lem5772311 _120745 _120749 op s f)). Qed.
Lemma lem5772426 {_120749 : Type'} (x : _120749) (y : _120749) (z : _120749) : term802 _120749 x y z.
Proof. exact (EQ_MP (@lem5772422 _120749 x y z) (@lem5772401 _120749 y x z)). Qed.
Lemma lem5772427 {_120749 : Type'} (x : _120749) (y : _120749) (z : _120749) : term802 _120749 x y z.
Proof. exact (@lem5772426 _120749 x y z). Qed.
Lemma lem5772428 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : term804 _120745 _120749 t op s f.
Proof. exact (@lem5772427 _120749 (term463 _120745 _120749 op s f) (term719 _120745 _120749 op s t f) (term463 _120745 _120749 op s f)). Qed.
Lemma lem5772431 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : (term719 _120745 _120749 op s t f) = (term463 _120745 _120749 op s f).
Proof. exact (@lem5772428 _120745 _120749 t op s f (@lem5772424 _120745 _120749 t op s f h1 h2)). Qed.
Lemma lem5772432 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : term805 _120745 _120749 t op s f.
Proof. exact (fun h0 : term806 _120745 _120749 t op s f => @lem5772431 _120745 _120749 t op s f h1 h2). Qed.
Lemma lem5772434 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5772435 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term805 _120745 _120749 t op s f) = ((term719 _120745 _120749 op s t f) = (term463 _120745 _120749 op s f)).
Proof. exact (@lem5772434 ((term719 _120745 _120749 op s t f) = (term463 _120745 _120749 op s f))). Qed.
Lemma lem5772436 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term182 _120745) (h2 : term358 _120745 _120749 t op s f) : (term719 _120745 _120749 op s t f) = (term463 _120745 _120749 op s f).
Proof. exact (EQ_MP (@lem5772435 _120745 _120749 t op s f) (@lem5772432 _120745 _120749 t op s f h1 h2)). Qed.
Lemma lem5772437 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term358 _120745 _120749 t op s f) : term807 _120745 _120749 t op s f.
Proof. exact (conj (@lem5771970 _120745 _120749 t op s f h1 h2 h3 h4 h5) (@lem5772436 _120745 _120749 t op s f h2 h5)). Qed.
Lemma lem5772439 {_120749 : Type'} (x : _120749) (y : _120749) (z : _120749) : term802 _120749 x y z.
Proof. exact (EQ_MP (@lem5772422 _120749 x y z) (@lem5772401 _120749 y x z)). Qed.
Lemma lem5772440 {_120749 : Type'} (x : _120749) (y : _120749) (z : _120749) : term802 _120749 x y z.
Proof. exact (@lem5772439 _120749 x y z). Qed.
Lemma lem5772441 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : term808 _120745 _120749 t op s f.
Proof. exact (@lem5772440 _120749 (term719 _120745 _120749 op s t f) (term525 _120745 _120749 s op t f) (term463 _120745 _120749 op s f)). Qed.
Lemma lem5772444 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term358 _120745 _120749 t op s f) : (term525 _120745 _120749 s op t f) = (term463 _120745 _120749 op s f).
Proof. exact (@lem5772441 _120745 _120749 t op s f (@lem5772437 _120745 _120749 t op s f h1 h2 h3 h4 h5)). Qed.
Lemma lem5772445 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term358 _120745 _120749 t op s f) : term809 _120745 _120749 t op s f.
Proof. exact (fun h0 : term529 _120745 _120749 t op s f => @lem5772444 _120745 _120749 t op s f h1 h2 h3 h4 h5). Qed.
Lemma lem5772447 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5772448 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term809 _120745 _120749 t op s f) = ((term525 _120745 _120749 s op t f) = (term463 _120745 _120749 op s f)).
Proof. exact (@lem5772447 ((term525 _120745 _120749 s op t f) = (term463 _120745 _120749 op s f))). Qed.
Lemma lem5772449 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term358 _120745 _120749 t op s f) : (term525 _120745 _120749 s op t f) = (term463 _120745 _120749 op s f).
Proof. exact (EQ_MP (@lem5772448 _120745 _120749 t op s f) (@lem5772445 _120745 _120749 t op s f h1 h2 h3 h4 h5)). Qed.
Lemma lem5772452 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5772454 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term529 _120745 _120749 t op s f) = (term810 _120745 _120749 t op s f).
Proof. exact (@lem5772452 ((term525 _120745 _120749 s op t f) = (term463 _120745 _120749 op s f))). Qed.
Lemma lem5772457 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term358 _120745 _120749 t op s f) : term810 _120745 _120749 t op s f.
Proof. exact (EQ_MP (@lem5772454 _120745 _120749 t op s f) (@lem5770871 _120745 _120749 t op s f h1)). Qed.
Lemma lem5772460 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term358 _120745 _120749 t op s f) : False.
Proof. exact (@lem5772457 _120745 _120749 t op s f h5 (@lem5772449 _120745 _120749 t op s f h1 h2 h3 h4 h5)). Qed.
Lemma lem5772461 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term358 _120745 _120749 t op s f) : term165.
Proof. exact (fun h0 : ~ False => @lem5772460 _120745 _120749 t op s f h1 h2 h3 h4 h5). Qed.
Lemma lem5772463 (p : Prop) : (term163 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5772464 : term165 = False.
Proof. exact (@lem5772463 False). Qed.
Lemma lem5772465 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term358 _120745 _120749 t op s f) : False.
Proof. exact (EQ_MP (@lem5772464) (@lem5772461 _120745 _120749 t op s f h1 h2 h3 h4 h5)). Qed.
Lemma lem5772466 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term361 _120745 _120749 op s f) : False.
Proof. exact (ex_elim (@lem5768527 _120745 _120749 op s f h5) (fun t : _120745 -> Prop => fun h0 : term360 _120745 _120749 op s f t => @lem5772465 _120745 _120749 t op s f h1 h2 h3 h4 h0)). Qed.
Lemma lem5772467 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term363 _120745 _120749 op f) : False.
Proof. exact (ex_elim (@lem5768526 _120745 _120749 op f h5) (fun s : _120745 -> Prop => fun h0 : term362 _120745 _120749 op f s => @lem5772466 _120745 _120749 op s f h1 h2 h3 h4 h0)). Qed.
Lemma lem5772468 {_120745 _120749 : Type'} (op : type1400 _120749) (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term365 _120745 _120749 op) : False.
Proof. exact (ex_elim (@lem5768525 _120745 _120749 op h5) (fun f : _120745 -> _120749 => fun h0 : term364 _120745 _120749 op f => @lem5772467 _120745 _120749 op f h1 h2 h3 h4 h0)). Qed.
Lemma lem5772469 {_120745 _120749 : Type'} (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term185 _120745 _120749) : False.
Proof. exact (ex_elim (@lem5766924 _120745 _120749 h5) (fun op : type1400 _120749 => fun h0 : term366 _120745 _120749 op => @lem5772468 _120745 _120749 op h1 h2 h3 h4 h0)). Qed.
Lemma lem5772470 {_120745 _120749 : Type'} (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term185 _120745 _120749) : (term191 _120745) = False.
Proof. exact (prop_ext (fun h6 : term191 _120745 => @lem5772469 _120745 _120749 h1 h2 h3 h4 h5) (fun h6 : False => @lem5766964 _120745 h3)). Qed.
Lemma lem5772471 {_120745 _120749 : Type'} (h1 : term190 _120745) (h2 : term182 _120745) (h3 : term191 _120745) (h4 : term186 _120745 _120749) (h5 : term185 _120745 _120749) : False.
Proof. exact (EQ_MP (@lem5772470 _120745 _120749 h1 h2 h3 h4 h5) (@lem5766964 _120745 h3)). Qed.
Lemma lem5772472 {_120745 _120749 : Type'} (h1 : term190 _120745) (h2 : term191 _120745) (h3 : term186 _120745 _120749) (h4 : term185 _120745 _120749) : term196 _120745.
Proof. exact (fun h0 : term182 _120745 => @lem5772471 _120745 _120749 h1 h0 h2 h3 h4). Qed.
Lemma lem5772473 {_120745 : Type'} : (term196 _120745) = (term197 _120745).
Proof. exact (@lem69 (term182 _120745)). Qed.
Lemma lem5772474 {_120745 _120749 : Type'} (h1 : term190 _120745) (h2 : term191 _120745) (h3 : term186 _120745 _120749) (h4 : term185 _120745 _120749) : term197 _120745.
Proof. exact (EQ_MP (@lem5772473 _120745) (@lem5772472 _120745 _120749 h1 h2 h3 h4)). Qed.
Lemma lem5772475 {_120592 _120745 _120749 : Type'} (h1 : term190 _120745) (h2 : term191 _120745) (h3 : term186 _120745 _120749) (h4 : term185 _120745 _120749) : term200 _120592 _120745.
Proof. exact (fun h0 : term188 _120592 _120745 => @lem5772474 _120745 _120749 h1 h2 h3 h4). Qed.
Lemma lem5772476 {_120592 _120745 _120749 : Type'} (h1 : term190 _120745) (h2 : term191 _120745) (h3 : term185 _120745 _120749) : term203 _120592 _120745 _120749.
Proof. exact (fun h0 : term186 _120745 _120749 => @lem5772475 _120592 _120745 _120749 h1 h2 h0 h3). Qed.
Lemma lem5772477 {_120592 _120745 _120749 : Type'} (h1 : term190 _120745) (h2 : term191 _120745) (h3 : term185 _120745 _120749) : term205 _120592 _120745 _120749.
Proof. exact (fun h0 : term186 _120592 _120749 => @lem5772476 _120592 _120745 _120749 h1 h2 h3). Qed.
Lemma lem5772478 {_120592 _120607 _120745 _120749 : Type'} (h1 : term190 _120745) (h2 : term191 _120745) (h3 : term185 _120745 _120749) : term208 _120592 _120607 _120745 _120749.
Proof. exact (fun h0 : term187 _120607 _120745 => @lem5772477 _120592 _120745 _120749 h1 h2 h3). Qed.
Lemma lem5772479 {_120592 _120607 _120745 _120749 : Type'} (h1 : term190 _120745) (h2 : term191 _120745) (h3 : term185 _120745 _120749) : term211 _120592 _120607 _120745 _120749.
Proof. exact (fun h0 : term189 _120745 => @lem5772478 _120592 _120607 _120745 _120749 h1 h2 h3). Qed.
Lemma lem5772480 {_120592 _120607 _120745 _120749 : Type'} (h1 : term190 _120745) (h2 : term191 _120745) (h3 : term185 _120745 _120749) : term213 _120592 _120607 _120745 _120749.
Proof. exact (fun h0 : term189 _120592 => @lem5772479 _120592 _120607 _120745 _120749 h1 h2 h3). Qed.
Lemma lem5772481 {_120592 _120607 _120745 _120749 : Type'} (h1 : term191 _120745) (h2 : term185 _120745 _120749) : term216 _120592 _120607 _120745 _120749.
Proof. exact (fun h0 : term190 _120745 => @lem5772480 _120592 _120607 _120745 _120749 h0 h1 h2). Qed.
Lemma lem5772482 {_120592 _120607 _120745 _120749 : Type'} (h1 : term191 _120745) (h2 : term185 _120745 _120749) : term218 _120592 _120607 _120745 _120749.
Proof. exact (fun h0 : term190 _120592 => @lem5772481 _120592 _120607 _120745 _120749 h1 h2). Qed.
Lemma lem5772483 {_120592 _120607 _120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term221 _120592 _120607 _120745 _120749.
Proof. exact (fun h0 : term191 _120745 => @lem5772482 _120592 _120607 _120745 _120749 h0 h1). Qed.
Lemma lem5772484 {_120592 _120607 _120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term223 _120592 _120607 _120745 _120749.
Proof. exact (fun h0 : term191 _120592 => @lem5772483 _120592 _120607 _120745 _120749 h1). Qed.
Lemma lem5772485 {_120592 _120607 _120745 _120749 : Type'} : term225 _120592 _120607 _120745 _120749.
Proof. exact (fun h0 : term185 _120745 _120749 => @lem5772484 _120592 _120607 _120745 _120749 h0). Qed.
Lemma lem5772486 {_120592 _120607 _120745 _120749 : Type'} : term192 _120592 _120607 _120745 _120749.
Proof. exact (EQ_MP (@lem5766696 _120592 _120607 _120745 _120749) (@lem5772485 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5772488 {_120592 _120607 _120745 _120749 : Type'} : term192 _120592 _120607 _120745 _120749.
Proof. exact (@lem5765882 _120592 _120607 _120745 _120749 (@lem5772486 _120592 _120607 _120745 _120749)). Qed.
Lemma lem5772489 {_120592 _120607 _120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term222 _120592 _120607 _120745 _120749.
Proof. exact (@lem5772488 _120592 _120607 _120745 _120749 (@lem5765847 _120745 _120749 h1)). Qed.
Lemma lem5772490 {_120592 _120607 _120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term220 _120592 _120607 _120745 _120749.
Proof. exact (@lem5772489 _120592 _120607 _120745 _120749 h1 (@lem5765865 _120592)). Qed.
Lemma lem5772491 {_120592 _120607 _120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term217 _120592 _120607 _120745 _120749.
Proof. exact (@lem5772490 _120592 _120607 _120745 _120749 h1 (@lem5765864 _120745)). Qed.
Lemma lem5772492 {_120592 _120607 _120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term215 _120592 _120607 _120745 _120749.
Proof. exact (@lem5772491 _120592 _120607 _120745 _120749 h1 (@lem5765862 _120592)). Qed.
Lemma lem5772493 {_120592 _120607 _120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term212 _120592 _120607 _120745 _120749.
Proof. exact (@lem5772492 _120592 _120607 _120745 _120749 h1 (@lem5765861 _120745)). Qed.
Lemma lem5772494 {_120592 _120607 _120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term210 _120592 _120607 _120745 _120749.
Proof. exact (@lem5772493 _120592 _120607 _120745 _120749 h1 (@lem5765858 _120592)). Qed.
Lemma lem5772495 {_120592 _120607 _120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term207 _120592 _120607 _120745 _120749.
Proof. exact (@lem5772494 _120592 _120607 _120745 _120749 h1 (@lem5765857 _120745)). Qed.
Lemma lem5772496 {_120592 _120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term204 _120592 _120745 _120749.
Proof. exact (@lem5772495 _120592 Prop _120745 _120749 h1 (@lem5765851 Prop _120745)). Qed.
Lemma lem5772497 {_120592 _120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term202 _120592 _120745 _120749.
Proof. exact (@lem5772496 _120592 _120745 _120749 h1 (@lem5765850 _120592 _120749)). Qed.
Lemma lem5772498 {_120592 _120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term199 _120592 _120745.
Proof. exact (@lem5772497 _120592 _120745 _120749 h1 (@lem5765855 _120745 _120749)). Qed.
Lemma lem5772499 {_120745 _120749 : Type'} (h1 : term185 _120745 _120749) : term196 _120745.
Proof. exact (@lem5772498 Prop _120745 _120749 h1 (@lem5765854 Prop _120745)). Qed.
Lemma lem5772500 {_120745 _120749 : Type'} (h1 : term185 _120745 _120749) : False.
Proof. exact (@lem5772499 _120745 _120749 h1 (@lem5765848 _120745)). Qed.
Lemma lem5772501 {_120745 _120749 : Type'} (h1 : term185 _120745 _120749) : (term185 _120745 _120749) = False.
Proof. exact (prop_ext (fun h2 : term185 _120745 _120749 => @lem5772500 _120745 _120749 h1) (fun h2 : False => @lem5765847 _120745 _120749 h1)). Qed.
Lemma lem5772502 {_120745 _120749 : Type'} (h1 : term185 _120745 _120749) : False.
Proof. exact (EQ_MP (@lem5772501 _120745 _120749 h1) (@lem5765847 _120745 _120749 h1)). Qed.
Lemma lem5772503 {_120745 _120749 : Type'} : term184 _120745 _120749.
Proof. exact (fun h0 : term185 _120745 _120749 => @lem5772502 _120745 _120749 h0). Qed.
Lemma lem5772504 {_120745 _120749 : Type'} : term183 _120745 _120749.
Proof. exact (EQ_MP (@lem5765846 _120745 _120749) (@lem5772503 _120745 _120749)). Qed.
