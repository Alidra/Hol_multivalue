Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_INTER_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3258596 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3258597 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (@SUBSET _85366 s t) = (term0 _85366 s t).
Proof. exact (@lem3258596 _85366 s t). Qed.
Lemma lem3258598 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term1 _85366 s t u) = (term2 _85366 s t u).
Proof. exact (@lem3258597 _85366 s (@INTER _85366 t u)). Qed.
Lemma lem3258605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3258606 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term3 _85366 s t u) = (term4 _85366 s t u).
Proof. exact (MK_COMB (@lem3258605) (@lem3258598 _85366 s t u)). Qed.
Lemma lem3258610 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3258611 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (@SUBSET _85366 s t) = (term0 _85366 s t).
Proof. exact (@lem3258610 _85366 s t). Qed.
Lemma lem3258618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3258619 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term5 _85366 s t) = (term6 _85366 s t).
Proof. exact (MK_COMB (@lem3258618) (@lem3258611 _85366 s t)). Qed.
Lemma lem3258621 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3258622 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (@SUBSET _85366 s t) = (term0 _85366 s t).
Proof. exact (@lem3258621 _85366 s t). Qed.
Lemma lem3258623 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (@SUBSET _85366 s u) = (term0 _85366 s u).
Proof. exact (@lem3258622 _85366 s u). Qed.
Lemma lem3258630 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term7 _85366 t s u) = (term8 _85366 t s u).
Proof. exact (MK_COMB (@lem3258619 _85366 s t) (@lem3258623 _85366 s u)). Qed.
Lemma lem3258633 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : ((term1 _85366 s t u) = (term7 _85366 t s u)) = ((term2 _85366 s t u) = (term8 _85366 t s u)).
Proof. exact (MK_COMB (@lem3258606 _85366 s t u) (@lem3258630 _85366 t s u)). Qed.
Lemma lem3258638 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) : (term9 _85366 t s) = (term10 _85366 t s).
Proof. exact (fun_ext (fun u : _85366 -> Prop => @lem3258633 _85366 t s u)). Qed.
Lemma lem3258639 {_85366 : Type'} : (@all (_85366 -> Prop)) = (@all (_85366 -> Prop)).
Proof. exact (eq_refl (@all (_85366 -> Prop))). Qed.
Lemma lem3258640 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) : (term11 _85366 t s) = (term12 _85366 t s).
Proof. exact (MK_COMB (@lem3258639 _85366) (@lem3258638 _85366 t s)). Qed.
Lemma lem3258645 {_85366 : Type'} (s : _85366 -> Prop) : (term13 _85366 s) = (term14 _85366 s).
Proof. exact (fun_ext (fun t : _85366 -> Prop => @lem3258640 _85366 t s)). Qed.
Lemma lem3258646 {_85366 : Type'} : (@all (_85366 -> Prop)) = (@all (_85366 -> Prop)).
Proof. exact (eq_refl (@all (_85366 -> Prop))). Qed.
Lemma lem3258647 {_85366 : Type'} (s : _85366 -> Prop) : (term15 _85366 s) = (term16 _85366 s).
Proof. exact (MK_COMB (@lem3258646 _85366) (@lem3258645 _85366 s)). Qed.
Lemma lem3258652 {_85366 : Type'} : (term17 _85366) = (term18 _85366).
Proof. exact (fun_ext (fun s : _85366 -> Prop => @lem3258647 _85366 s)). Qed.
Lemma lem3258653 {_85366 : Type'} : (@all (_85366 -> Prop)) = (@all (_85366 -> Prop)).
Proof. exact (eq_refl (@all (_85366 -> Prop))). Qed.
Lemma lem3258654 {_85366 : Type'} : (term19 _85366) = (term20 _85366).
Proof. exact (MK_COMB (@lem3258653 _85366) (@lem3258652 _85366)). Qed.
Lemma lem3258659 {_85366 : Type'} : (term20 _85366) = (term19 _85366).
Proof. exact (SYM (@lem3258654 _85366)). Qed.
Lemma lem3258681 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3258682 {_85366 : Type'} (P : _85366 -> Prop) (x : _85366) : (@IN _85366 x P) = (P x).
Proof. exact (@lem3258681 _85366 P x). Qed.
Lemma lem3258683 {_85366 : Type'} (s : _85366 -> Prop) (x : _85366) : (@IN _85366 x s) = (s x).
Proof. exact (@lem3258682 _85366 s x). Qed.
Lemma lem3258684 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3258685 {_85366 : Type'} (s : _85366 -> Prop) (x : _85366) : (term21 _85366 x s) = (term22 _85366 s x).
Proof. exact (MK_COMB (@lem3258684) (@lem3258683 _85366 s x)). Qed.
Lemma lem3258687 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term23 A x s t) = (term24 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3258688 {_85366 : Type'} (s : _85366 -> Prop) (x : _85366) (t : _85366 -> Prop) : (term23 _85366 x s t) = (term24 _85366 s x t).
Proof. exact (@lem3258687 _85366 s x t). Qed.
Lemma lem3258689 {_85366 : Type'} (t : _85366 -> Prop) (x : _85366) (u : _85366 -> Prop) : (term23 _85366 x t u) = (term24 _85366 t x u).
Proof. exact (@lem3258688 _85366 t x u). Qed.
Lemma lem3258693 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3258694 {_85366 : Type'} (P : _85366 -> Prop) (x : _85366) : (@IN _85366 x P) = (P x).
Proof. exact (@lem3258693 _85366 P x). Qed.
Lemma lem3258695 {_85366 : Type'} (t : _85366 -> Prop) (x : _85366) : (@IN _85366 x t) = (t x).
Proof. exact (@lem3258694 _85366 t x). Qed.
Lemma lem3258696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3258697 {_85366 : Type'} (t : _85366 -> Prop) (x : _85366) : (term25 _85366 x t) = (term26 _85366 t x).
Proof. exact (MK_COMB (@lem3258696) (@lem3258695 _85366 t x)). Qed.
Lemma lem3258699 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3258700 {_85366 : Type'} (P : _85366 -> Prop) (x : _85366) : (@IN _85366 x P) = (P x).
Proof. exact (@lem3258699 _85366 P x). Qed.
Lemma lem3258701 {_85366 : Type'} (u : _85366 -> Prop) (x : _85366) : (@IN _85366 x u) = (u x).
Proof. exact (@lem3258700 _85366 u x). Qed.
Lemma lem3258702 {_85366 : Type'} (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term24 _85366 t x u) = (term27 _85366 t u x).
Proof. exact (MK_COMB (@lem3258697 _85366 t x) (@lem3258701 _85366 u x)). Qed.
Lemma lem3258705 {_85366 : Type'} (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term23 _85366 x t u) = (term27 _85366 t u x).
Proof. exact (TRANS (@lem3258689 _85366 t x u) (@lem3258702 _85366 t u x)). Qed.
Lemma lem3258706 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term28 _85366 s x t u) = (term29 _85366 s t u x).
Proof. exact (MK_COMB (@lem3258685 _85366 s x) (@lem3258705 _85366 t u x)). Qed.
Lemma lem3258709 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term30 _85366 s t u) = (term31 _85366 s t u).
Proof. exact (fun_ext (fun x : _85366 => @lem3258706 _85366 s t u x)). Qed.
Lemma lem3258710 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3258711 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term2 _85366 s t u) = (term32 _85366 s t u).
Proof. exact (MK_COMB (@lem3258710 _85366) (@lem3258709 _85366 s t u)). Qed.
Lemma lem3258716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3258717 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term4 _85366 s t u) = (term33 _85366 s t u).
Proof. exact (MK_COMB (@lem3258716) (@lem3258711 _85366 s t u)). Qed.
Lemma lem3258727 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3258728 {_85366 : Type'} (P : _85366 -> Prop) (x : _85366) : (@IN _85366 x P) = (P x).
Proof. exact (@lem3258727 _85366 P x). Qed.
Lemma lem3258729 {_85366 : Type'} (s : _85366 -> Prop) (x : _85366) : (@IN _85366 x s) = (s x).
Proof. exact (@lem3258728 _85366 s x). Qed.
Lemma lem3258730 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3258731 {_85366 : Type'} (s : _85366 -> Prop) (x : _85366) : (term21 _85366 x s) = (term22 _85366 s x).
Proof. exact (MK_COMB (@lem3258730) (@lem3258729 _85366 s x)). Qed.
Lemma lem3258733 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3258734 {_85366 : Type'} (P : _85366 -> Prop) (x : _85366) : (@IN _85366 x P) = (P x).
Proof. exact (@lem3258733 _85366 P x). Qed.
Lemma lem3258735 {_85366 : Type'} (t : _85366 -> Prop) (x : _85366) : (@IN _85366 x t) = (t x).
Proof. exact (@lem3258734 _85366 t x). Qed.
Lemma lem3258736 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) : (term34 _85366 s x t) = (term35 _85366 s t x).
Proof. exact (MK_COMB (@lem3258731 _85366 s x) (@lem3258735 _85366 t x)). Qed.
Lemma lem3258739 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term36 _85366 s t) = (term37 _85366 s t).
Proof. exact (fun_ext (fun x : _85366 => @lem3258736 _85366 s t x)). Qed.
Lemma lem3258740 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3258741 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term0 _85366 s t) = (term38 _85366 s t).
Proof. exact (MK_COMB (@lem3258740 _85366) (@lem3258739 _85366 s t)). Qed.
Lemma lem3258746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3258747 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term6 _85366 s t) = (term39 _85366 s t).
Proof. exact (MK_COMB (@lem3258746) (@lem3258741 _85366 s t)). Qed.
Lemma lem3258755 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3258756 {_85366 : Type'} (P : _85366 -> Prop) (x : _85366) : (@IN _85366 x P) = (P x).
Proof. exact (@lem3258755 _85366 P x). Qed.
Lemma lem3258757 {_85366 : Type'} (s : _85366 -> Prop) (x : _85366) : (@IN _85366 x s) = (s x).
Proof. exact (@lem3258756 _85366 s x). Qed.
Lemma lem3258758 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3258759 {_85366 : Type'} (s : _85366 -> Prop) (x : _85366) : (term21 _85366 x s) = (term22 _85366 s x).
Proof. exact (MK_COMB (@lem3258758) (@lem3258757 _85366 s x)). Qed.
Lemma lem3258761 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3258762 {_85366 : Type'} (P : _85366 -> Prop) (x : _85366) : (@IN _85366 x P) = (P x).
Proof. exact (@lem3258761 _85366 P x). Qed.
Lemma lem3258763 {_85366 : Type'} (u : _85366 -> Prop) (x : _85366) : (@IN _85366 x u) = (u x).
Proof. exact (@lem3258762 _85366 u x). Qed.
Lemma lem3258764 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term34 _85366 s x u) = (term35 _85366 s u x).
Proof. exact (MK_COMB (@lem3258759 _85366 s x) (@lem3258763 _85366 u x)). Qed.
Lemma lem3258767 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term36 _85366 s u) = (term37 _85366 s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3258764 _85366 s u x)). Qed.
Lemma lem3258768 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3258769 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term0 _85366 s u) = (term38 _85366 s u).
Proof. exact (MK_COMB (@lem3258768 _85366) (@lem3258767 _85366 s u)). Qed.
Lemma lem3258774 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term8 _85366 t s u) = (term40 _85366 t s u).
Proof. exact (MK_COMB (@lem3258747 _85366 s t) (@lem3258769 _85366 s u)). Qed.
Lemma lem3258777 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : ((term2 _85366 s t u) = (term8 _85366 t s u)) = ((term32 _85366 s t u) = (term40 _85366 t s u)).
Proof. exact (MK_COMB (@lem3258717 _85366 s t u) (@lem3258774 _85366 t s u)). Qed.
Lemma lem3258780 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) : (term10 _85366 t s) = (term41 _85366 t s).
Proof. exact (fun_ext (fun u : _85366 -> Prop => @lem3258777 _85366 t s u)). Qed.
Lemma lem3258781 {_85366 : Type'} : (@all (_85366 -> Prop)) = (@all (_85366 -> Prop)).
Proof. exact (eq_refl (@all (_85366 -> Prop))). Qed.
Lemma lem3258782 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) : (term12 _85366 t s) = (term42 _85366 t s).
Proof. exact (MK_COMB (@lem3258781 _85366) (@lem3258780 _85366 t s)). Qed.
Lemma lem3258787 {_85366 : Type'} (s : _85366 -> Prop) : (term14 _85366 s) = (term43 _85366 s).
Proof. exact (fun_ext (fun t : _85366 -> Prop => @lem3258782 _85366 t s)). Qed.
Lemma lem3258788 {_85366 : Type'} : (@all (_85366 -> Prop)) = (@all (_85366 -> Prop)).
Proof. exact (eq_refl (@all (_85366 -> Prop))). Qed.
Lemma lem3258789 {_85366 : Type'} (s : _85366 -> Prop) : (term16 _85366 s) = (term44 _85366 s).
Proof. exact (MK_COMB (@lem3258788 _85366) (@lem3258787 _85366 s)). Qed.
Lemma lem3258794 {_85366 : Type'} : (term18 _85366) = (term45 _85366).
Proof. exact (fun_ext (fun s : _85366 -> Prop => @lem3258789 _85366 s)). Qed.
Lemma lem3258795 {_85366 : Type'} : (@all (_85366 -> Prop)) = (@all (_85366 -> Prop)).
Proof. exact (eq_refl (@all (_85366 -> Prop))). Qed.
Lemma lem3258796 {_85366 : Type'} : (term20 _85366) = (term46 _85366).
Proof. exact (MK_COMB (@lem3258795 _85366) (@lem3258794 _85366)). Qed.
Lemma lem3258801 {_85366 : Type'} : (term46 _85366) = (term20 _85366).
Proof. exact (SYM (@lem3258796 _85366)). Qed.
Lemma lem3258803 (p : Prop) : p = (term47 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3258804 {_85366 : Type'} : (term46 _85366) = (term48 _85366).
Proof. exact (@lem3258803 (term46 _85366)). Qed.
Lemma lem3258805 {_85366 : Type'} : (term48 _85366) = (term46 _85366).
Proof. exact (SYM (@lem3258804 _85366)). Qed.
Lemma lem3258806 {_85366 : Type'} (h1 : term49 _85366) : term49 _85366.
Proof. exact (h1). Qed.
Lemma lem3258809 {_85366 : Type'} (h1 : term48 _85366) : term48 _85366.
Proof. exact (h1). Qed.
Lemma lem3258810 {_85366 : Type'} : term50 _85366.
Proof. exact (fun h0 : term48 _85366 => @lem3258809 _85366 h0). Qed.
Lemma lem3258811 {_85366 : Type'} (h1 : term50 _85366) : term50 _85366.
Proof. exact (h1). Qed.
Lemma lem3258812 {_85366 : Type'} (h1 : term48 _85366) : term48 _85366.
Proof. exact (h1). Qed.
Lemma lem3258813 {_85366 : Type'} (h1 : term48 _85366) (h2 : term50 _85366) : term48 _85366.
Proof. exact (@lem3258811 _85366 h2 (@lem3258812 _85366 h1)). Qed.
Lemma lem3258814 {_85366 : Type'} (h1 : term48 _85366) : term51 _85366.
Proof. exact (fun h0 : term50 _85366 => @lem3258813 _85366 h1 h0). Qed.
Lemma lem3258815 {_85366 : Type'} (h1 : term50 _85366) : term50 _85366.
Proof. exact (h1). Qed.
Lemma lem3258816 {_85366 : Type'} (h1 : term48 _85366) (h2 : term50 _85366) : term48 _85366.
Proof. exact (@lem3258814 _85366 h1 (@lem3258815 _85366 h2)). Qed.
Lemma lem3258817 {_85366 : Type'} (h1 : term50 _85366) : term50 _85366.
Proof. exact (fun h0 : term48 _85366 => @lem3258816 _85366 h0 h1). Qed.
Lemma lem3258818 {_85366 : Type'} : term52 _85366.
Proof. exact (fun h0 : term50 _85366 => @lem3258817 _85366 h0). Qed.
Lemma lem3258821 {_85366 : Type'} : term50 _85366.
Proof. exact (@lem3258818 _85366 (@lem3258810 _85366)). Qed.
Lemma lem3258822 {_85366 : Type'} : term50 _85366.
Proof. exact (@lem3258821 _85366). Qed.
Lemma lem3258824 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3258825 {_85366 : Type'} : (term48 _85366) = (term53 _85366).
Proof. exact (@lem3258824 (term49 _85366)). Qed.
Lemma lem3258827 (t : Prop) : (term54 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3258828 {_85366 : Type'} : (term53 _85366) = (term46 _85366).
Proof. exact (@lem3258827 (term46 _85366)). Qed.
Lemma lem3258867 {_85366 : Type'} : (term48 _85366) = (term46 _85366).
Proof. exact (TRANS (@lem3258825 _85366) (@lem3258828 _85366)). Qed.
Lemma lem3258872 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term35 _85366 s u x) = (term35 _85366 s u x).
Proof. exact (eq_refl (term35 _85366 s u x)). Qed.
Lemma lem3258873 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term37 _85366 s u) = (term37 _85366 s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3258872 _85366 s u x)). Qed.
Lemma lem3258874 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3258875 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term38 _85366 s u) = (term38 _85366 s u).
Proof. exact (MK_COMB (@lem3258874 _85366) (@lem3258873 _85366 s u)). Qed.
Lemma lem3258880 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) : (term35 _85366 s t x) = (term35 _85366 s t x).
Proof. exact (eq_refl (term35 _85366 s t x)). Qed.
Lemma lem3258881 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term37 _85366 s t) = (term37 _85366 s t).
Proof. exact (fun_ext (fun x : _85366 => @lem3258880 _85366 s t x)). Qed.
Lemma lem3258882 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3258883 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term38 _85366 s t) = (term38 _85366 s t).
Proof. exact (MK_COMB (@lem3258882 _85366) (@lem3258881 _85366 s t)). Qed.
Lemma lem3258884 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3258885 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term39 _85366 s t) = (term39 _85366 s t).
Proof. exact (MK_COMB (@lem3258884) (@lem3258883 _85366 s t)). Qed.
Lemma lem3258886 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term40 _85366 t s u) = (term40 _85366 t s u).
Proof. exact (MK_COMB (@lem3258885 _85366 s t) (@lem3258875 _85366 s u)). Qed.
Lemma lem3258895 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term29 _85366 s t u x) = (term29 _85366 s t u x).
Proof. exact (eq_refl (term29 _85366 s t u x)). Qed.
Lemma lem3258896 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term31 _85366 s t u) = (term31 _85366 s t u).
Proof. exact (fun_ext (fun x : _85366 => @lem3258895 _85366 s t u x)). Qed.
Lemma lem3258897 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3258898 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term32 _85366 s t u) = (term32 _85366 s t u).
Proof. exact (MK_COMB (@lem3258897 _85366) (@lem3258896 _85366 s t u)). Qed.
Lemma lem3258899 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3258900 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term33 _85366 s t u) = (term33 _85366 s t u).
Proof. exact (MK_COMB (@lem3258899) (@lem3258898 _85366 s t u)). Qed.
Lemma lem3258901 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : ((term32 _85366 s t u) = (term40 _85366 t s u)) = ((term32 _85366 s t u) = (term40 _85366 t s u)).
Proof. exact (MK_COMB (@lem3258900 _85366 s t u) (@lem3258886 _85366 t s u)). Qed.
Lemma lem3258902 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) : (term41 _85366 t s) = (term41 _85366 t s).
Proof. exact (fun_ext (fun u : _85366 -> Prop => @lem3258901 _85366 t s u)). Qed.
Lemma lem3258903 {_85366 : Type'} : (@all (_85366 -> Prop)) = (@all (_85366 -> Prop)).
Proof. exact (eq_refl (@all (_85366 -> Prop))). Qed.
Lemma lem3258904 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) : (term42 _85366 t s) = (term42 _85366 t s).
Proof. exact (MK_COMB (@lem3258903 _85366) (@lem3258902 _85366 t s)). Qed.
Lemma lem3258905 {_85366 : Type'} (s : _85366 -> Prop) : (term43 _85366 s) = (term43 _85366 s).
Proof. exact (fun_ext (fun t : _85366 -> Prop => @lem3258904 _85366 t s)). Qed.
Lemma lem3258906 {_85366 : Type'} : (@all (_85366 -> Prop)) = (@all (_85366 -> Prop)).
Proof. exact (eq_refl (@all (_85366 -> Prop))). Qed.
Lemma lem3258907 {_85366 : Type'} (s : _85366 -> Prop) : (term44 _85366 s) = (term44 _85366 s).
Proof. exact (MK_COMB (@lem3258906 _85366) (@lem3258905 _85366 s)). Qed.
Lemma lem3258908 {_85366 : Type'} : (term45 _85366) = (term45 _85366).
Proof. exact (fun_ext (fun s : _85366 -> Prop => @lem3258907 _85366 s)). Qed.
Lemma lem3258909 {_85366 : Type'} : (@all (_85366 -> Prop)) = (@all (_85366 -> Prop)).
Proof. exact (eq_refl (@all (_85366 -> Prop))). Qed.
Lemma lem3258910 {_85366 : Type'} : (term46 _85366) = (term46 _85366).
Proof. exact (MK_COMB (@lem3258909 _85366) (@lem3258908 _85366)). Qed.
Lemma lem3258959 {_85366 : Type'} : (term48 _85366) = (term46 _85366).
Proof. exact (TRANS (@lem3258867 _85366) (@lem3258910 _85366)). Qed.
Lemma lem3258960 {_85366 : Type'} : (term46 _85366) = (term48 _85366).
Proof. exact (SYM (@lem3258959 _85366)). Qed.
Lemma lem3258962 (p : Prop) : p = (term47 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3258963 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : ((term32 _85366 s t u) = (term40 _85366 t s u)) = (term55 _85366 t s u).
Proof. exact (@lem3258962 ((term32 _85366 s t u) = (term40 _85366 t s u))). Qed.
Lemma lem3258964 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term55 _85366 t s u) = ((term32 _85366 s t u) = (term40 _85366 t s u)).
Proof. exact (SYM (@lem3258963 _85366 t s u)). Qed.
Lemma lem3258965 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term56 _85366 t s u) : term56 _85366 t s u.
Proof. exact (h1). Qed.
Lemma lem3258976 {_85366 : Type'} (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term57 _85366 t u x) = (term58 _85366 t u x).
Proof. exact (@lem17045 (t x) (u x)). Qed.
Lemma lem3258981 {_85366 : Type'} (s : _85366 -> Prop) (x : _85366) : (term26 _85366 s x) = (term26 _85366 s x).
Proof. exact (eq_refl (term26 _85366 s x)). Qed.
Lemma lem3258982 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term59 _85366 s t u x) = (term60 _85366 s t u x).
Proof. exact (MK_COMB (@lem3258981 _85366 s x) (@lem3258976 _85366 t u x)). Qed.
Lemma lem3258983 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term61 _85366 s t u x) = (term59 _85366 s t u x).
Proof. exact (@lem17362 (s x) (term27 _85366 t u x)). Qed.
Lemma lem3258984 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term61 _85366 s t u x) = (term60 _85366 s t u x).
Proof. exact (TRANS (@lem3258983 _85366 s t u x) (@lem3258982 _85366 s t u x)). Qed.
Lemma lem3258989 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term29 _85366 s t u x) = (term62 _85366 s t u x).
Proof. exact (@lem17265 (s x) (term27 _85366 t u x)). Qed.
Lemma lem3258990 {_85366 : Type'} (P : _85366 -> Prop) : (term63 _85366 P) = (term64 _85366 P).
Proof. exact (@lem18392 _85366 P). Qed.
Lemma lem3258991 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term65 _85366 s t u) = (term66 _85366 s t u).
Proof. exact (@lem3258990 _85366 (term31 _85366 s t u)). Qed.
Lemma lem3258992 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term67 _85366 s t u x) = (term29 _85366 s t u x).
Proof. exact (eq_refl (term67 _85366 s t u x)). Qed.
Lemma lem3258993 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3258994 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term68 _85366 s t u x) = (term61 _85366 s t u x).
Proof. exact (MK_COMB (@lem3258993) (@lem3258992 _85366 s t u x)). Qed.
Lemma lem3258995 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term68 _85366 s t u x) = (term60 _85366 s t u x).
Proof. exact (TRANS (@lem3258994 _85366 s t u x) (@lem3258984 _85366 s t u x)). Qed.
Lemma lem3258996 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term69 _85366 s t u) = (term70 _85366 s t u).
Proof. exact (fun_ext (fun x : _85366 => @lem3258995 _85366 s t u x)). Qed.
Lemma lem3258997 {_85366 : Type'} : (@ex _85366) = (@ex _85366).
Proof. exact (eq_refl (@ex _85366)). Qed.
Lemma lem3258998 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term66 _85366 s t u) = (term71 _85366 s t u).
Proof. exact (MK_COMB (@lem3258997 _85366) (@lem3258996 _85366 s t u)). Qed.
Lemma lem3258999 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term65 _85366 s t u) = (term71 _85366 s t u).
Proof. exact (TRANS (@lem3258991 _85366 s t u) (@lem3258998 _85366 s t u)). Qed.
Lemma lem3259000 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term31 _85366 s t u) = (term72 _85366 s t u).
Proof. exact (fun_ext (fun x : _85366 => @lem3258989 _85366 s t u x)). Qed.
Lemma lem3259001 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3259002 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term32 _85366 s t u) = (term73 _85366 s t u).
Proof. exact (MK_COMB (@lem3259001 _85366) (@lem3259000 _85366 s t u)). Qed.
Lemma lem3259011 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) : (term74 _85366 s t x) = (term75 _85366 s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem3259016 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) : (term35 _85366 s t x) = (term76 _85366 s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3259017 {_85366 : Type'} (P : _85366 -> Prop) : (term63 _85366 P) = (term64 _85366 P).
Proof. exact (@lem18392 _85366 P). Qed.
Lemma lem3259018 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term77 _85366 s t) = (term78 _85366 s t).
Proof. exact (@lem3259017 _85366 (term37 _85366 s t)). Qed.
Lemma lem3259019 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) : (term79 _85366 s t x) = (term35 _85366 s t x).
Proof. exact (eq_refl (term79 _85366 s t x)). Qed.
Lemma lem3259020 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3259021 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) : (term80 _85366 s t x) = (term74 _85366 s t x).
Proof. exact (MK_COMB (@lem3259020) (@lem3259019 _85366 s t x)). Qed.
Lemma lem3259022 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) : (term80 _85366 s t x) = (term75 _85366 s t x).
Proof. exact (TRANS (@lem3259021 _85366 s t x) (@lem3259011 _85366 s t x)). Qed.
Lemma lem3259023 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term81 _85366 s t) = (term82 _85366 s t).
Proof. exact (fun_ext (fun x : _85366 => @lem3259022 _85366 s t x)). Qed.
Lemma lem3259024 {_85366 : Type'} : (@ex _85366) = (@ex _85366).
Proof. exact (eq_refl (@ex _85366)). Qed.
Lemma lem3259025 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term78 _85366 s t) = (term83 _85366 s t).
Proof. exact (MK_COMB (@lem3259024 _85366) (@lem3259023 _85366 s t)). Qed.
Lemma lem3259026 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term77 _85366 s t) = (term83 _85366 s t).
Proof. exact (TRANS (@lem3259018 _85366 s t) (@lem3259025 _85366 s t)). Qed.
Lemma lem3259027 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term37 _85366 s t) = (term84 _85366 s t).
Proof. exact (fun_ext (fun x : _85366 => @lem3259016 _85366 s t x)). Qed.
Lemma lem3259028 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3259029 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term38 _85366 s t) = (term85 _85366 s t).
Proof. exact (MK_COMB (@lem3259028 _85366) (@lem3259027 _85366 s t)). Qed.
Lemma lem3259038 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term74 _85366 s u x) = (term75 _85366 s u x).
Proof. exact (@lem17362 (s x) (u x)). Qed.
Lemma lem3259043 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term35 _85366 s u x) = (term76 _85366 s u x).
Proof. exact (@lem17265 (s x) (u x)). Qed.
Lemma lem3259044 {_85366 : Type'} (P : _85366 -> Prop) : (term63 _85366 P) = (term64 _85366 P).
Proof. exact (@lem18392 _85366 P). Qed.
Lemma lem3259045 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term77 _85366 s u) = (term78 _85366 s u).
Proof. exact (@lem3259044 _85366 (term37 _85366 s u)). Qed.
Lemma lem3259046 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term79 _85366 s u x) = (term35 _85366 s u x).
Proof. exact (eq_refl (term79 _85366 s u x)). Qed.
Lemma lem3259047 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3259048 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term80 _85366 s u x) = (term74 _85366 s u x).
Proof. exact (MK_COMB (@lem3259047) (@lem3259046 _85366 s u x)). Qed.
Lemma lem3259049 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term80 _85366 s u x) = (term75 _85366 s u x).
Proof. exact (TRANS (@lem3259048 _85366 s u x) (@lem3259038 _85366 s u x)). Qed.
Lemma lem3259050 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term81 _85366 s u) = (term82 _85366 s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259049 _85366 s u x)). Qed.
Lemma lem3259051 {_85366 : Type'} : (@ex _85366) = (@ex _85366).
Proof. exact (eq_refl (@ex _85366)). Qed.
Lemma lem3259052 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term78 _85366 s u) = (term83 _85366 s u).
Proof. exact (MK_COMB (@lem3259051 _85366) (@lem3259050 _85366 s u)). Qed.
Lemma lem3259053 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term77 _85366 s u) = (term83 _85366 s u).
Proof. exact (TRANS (@lem3259045 _85366 s u) (@lem3259052 _85366 s u)). Qed.
Lemma lem3259054 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term37 _85366 s u) = (term84 _85366 s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259043 _85366 s u x)). Qed.
Lemma lem3259055 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3259056 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term38 _85366 s u) = (term85 _85366 s u).
Proof. exact (MK_COMB (@lem3259055 _85366) (@lem3259054 _85366 s u)). Qed.
Lemma lem3259057 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3259058 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term86 _85366 s t) = (term87 _85366 s t).
Proof. exact (MK_COMB (@lem3259057) (@lem3259026 _85366 s t)). Qed.
Lemma lem3259059 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term88 _85366 t s u) = (term89 _85366 t s u).
Proof. exact (MK_COMB (@lem3259058 _85366 s t) (@lem3259053 _85366 s u)). Qed.
Lemma lem3259060 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term90 _85366 t s u) = (term88 _85366 t s u).
Proof. exact (@lem17045 (term38 _85366 s t) (term38 _85366 s u)). Qed.
Lemma lem3259061 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term90 _85366 t s u) = (term89 _85366 t s u).
Proof. exact (TRANS (@lem3259060 _85366 t s u) (@lem3259059 _85366 t s u)). Qed.
Lemma lem3259062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3259063 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term39 _85366 s t) = (term91 _85366 s t).
Proof. exact (MK_COMB (@lem3259062) (@lem3259029 _85366 s t)). Qed.
Lemma lem3259064 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term40 _85366 t s u) = (term92 _85366 t s u).
Proof. exact (MK_COMB (@lem3259063 _85366 s t) (@lem3259056 _85366 s u)). Qed.
Lemma lem3259065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3259066 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term93 _85366 s t u) = (term94 _85366 s t u).
Proof. exact (MK_COMB (@lem3259065) (@lem3258999 _85366 s t u)). Qed.
Lemma lem3259067 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term95 _85366 t s u) = (term96 _85366 t s u).
Proof. exact (MK_COMB (@lem3259066 _85366 s t u) (@lem3259064 _85366 t s u)). Qed.
Lemma lem3259068 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3259069 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term97 _85366 s t u) = (term98 _85366 s t u).
Proof. exact (MK_COMB (@lem3259068) (@lem3259002 _85366 s t u)). Qed.
Lemma lem3259070 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term99 _85366 t s u) = (term100 _85366 t s u).
Proof. exact (MK_COMB (@lem3259069 _85366 s t u) (@lem3259061 _85366 t s u)). Qed.
Lemma lem3259071 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3259072 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term101 _85366 t s u) = (term102 _85366 t s u).
Proof. exact (MK_COMB (@lem3259071) (@lem3259070 _85366 t s u)). Qed.
Lemma lem3259073 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term103 _85366 t s u) = (term104 _85366 t s u).
Proof. exact (MK_COMB (@lem3259072 _85366 t s u) (@lem3259067 _85366 t s u)). Qed.
Lemma lem3259074 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term56 _85366 t s u) = (term103 _85366 t s u).
Proof. exact (@lem17646 (term32 _85366 s t u) (term40 _85366 t s u)). Qed.
Lemma lem3259075 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term56 _85366 t s u) = (term104 _85366 t s u).
Proof. exact (TRANS (@lem3259074 _85366 t s u) (@lem3259073 _85366 t s u)). Qed.
Lemma lem3259274 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term105 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3259275 {_85366 : Type'} (P : _85366 -> Prop) (Q : _85366 -> Prop) : (term105 _85366 P Q) = (term106 _85366 P Q).
Proof. exact (@lem3259274 _85366 P Q). Qed.
Lemma lem3259276 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term107 _85366 t s u) = (term108 _85366 t s u).
Proof. exact (@lem3259275 _85366 (term82 _85366 s t) (term82 _85366 s u)). Qed.
Lemma lem3259277 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) : (term109 _85366 s t x) = (term75 _85366 s t x).
Proof. exact (eq_refl (term109 _85366 s t x)). Qed.
Lemma lem3259278 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term110 _85366 s t) = (term82 _85366 s t).
Proof. exact (fun_ext (fun x : _85366 => @lem3259277 _85366 s t x)). Qed.
Lemma lem3259279 {_85366 : Type'} : (@ex _85366) = (@ex _85366).
Proof. exact (eq_refl (@ex _85366)). Qed.
Lemma lem3259280 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term111 _85366 s t) = (term83 _85366 s t).
Proof. exact (MK_COMB (@lem3259279 _85366) (@lem3259278 _85366 s t)). Qed.
Lemma lem3259281 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3259282 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term112 _85366 s t) = (term87 _85366 s t).
Proof. exact (MK_COMB (@lem3259281) (@lem3259280 _85366 s t)). Qed.
Lemma lem3259283 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term109 _85366 s u x) = (term75 _85366 s u x).
Proof. exact (eq_refl (term109 _85366 s u x)). Qed.
Lemma lem3259284 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term110 _85366 s u) = (term82 _85366 s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259283 _85366 s u x)). Qed.
Lemma lem3259285 {_85366 : Type'} : (@ex _85366) = (@ex _85366).
Proof. exact (eq_refl (@ex _85366)). Qed.
Lemma lem3259286 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term111 _85366 s u) = (term83 _85366 s u).
Proof. exact (MK_COMB (@lem3259285 _85366) (@lem3259284 _85366 s u)). Qed.
Lemma lem3259287 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term107 _85366 t s u) = (term89 _85366 t s u).
Proof. exact (MK_COMB (@lem3259282 _85366 s t) (@lem3259286 _85366 s u)). Qed.
Lemma lem3259288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3259289 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term113 _85366 t s u) = (term114 _85366 t s u).
Proof. exact (MK_COMB (@lem3259288) (@lem3259287 _85366 t s u)). Qed.
Lemma lem3259290 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) : (term109 _85366 s t x) = (term75 _85366 s t x).
Proof. exact (eq_refl (term109 _85366 s t x)). Qed.
Lemma lem3259291 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3259292 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) : (term115 _85366 s t x) = (term116 _85366 s t x).
Proof. exact (MK_COMB (@lem3259291) (@lem3259290 _85366 s t x)). Qed.
Lemma lem3259293 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term109 _85366 s u x) = (term75 _85366 s u x).
Proof. exact (eq_refl (term109 _85366 s u x)). Qed.
Lemma lem3259294 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term117 _85366 t s u x) = (term118 _85366 t s u x).
Proof. exact (MK_COMB (@lem3259292 _85366 s t x) (@lem3259293 _85366 s u x)). Qed.
Lemma lem3259295 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term119 _85366 t s u) = (term120 _85366 t s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259294 _85366 t s u x)). Qed.
Lemma lem3259296 {_85366 : Type'} : (@ex _85366) = (@ex _85366).
Proof. exact (eq_refl (@ex _85366)). Qed.
Lemma lem3259297 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term108 _85366 t s u) = (term121 _85366 t s u).
Proof. exact (MK_COMB (@lem3259296 _85366) (@lem3259295 _85366 t s u)). Qed.
Lemma lem3259298 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : ((term107 _85366 t s u) = (term108 _85366 t s u)) = ((term89 _85366 t s u) = (term121 _85366 t s u)).
Proof. exact (MK_COMB (@lem3259289 _85366 t s u) (@lem3259297 _85366 t s u)). Qed.
Lemma lem3259299 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term89 _85366 t s u) = (term121 _85366 t s u).
Proof. exact (EQ_MP (@lem3259298 _85366 t s u) (@lem3259276 _85366 t s u)). Qed.
Lemma lem3259300 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term98 _85366 s t u) = (term98 _85366 s t u).
Proof. exact (eq_refl (term98 _85366 s t u)). Qed.
Lemma lem3259301 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term100 _85366 t s u) = (term122 _85366 t s u).
Proof. exact (MK_COMB (@lem3259300 _85366 s t u) (@lem3259299 _85366 t s u)). Qed.
Lemma lem3259303 {A : Type'} (P : Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3259304 {_85366 : Type'} (P : Prop) (Q : _85366 -> Prop) : (term123 _85366 P Q) = (term124 _85366 P Q).
Proof. exact (@lem3259303 _85366 P Q). Qed.
Lemma lem3259305 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term125 _85366 t s u) = (term126 _85366 t s u).
Proof. exact (@lem3259304 _85366 (term73 _85366 s t u) (term120 _85366 t s u)). Qed.
Lemma lem3259306 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term127 _85366 t s u x) = (term118 _85366 t s u x).
Proof. exact (eq_refl (term127 _85366 t s u x)). Qed.
Lemma lem3259307 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term128 _85366 t s u) = (term120 _85366 t s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259306 _85366 t s u x)). Qed.
Lemma lem3259308 {_85366 : Type'} : (@ex _85366) = (@ex _85366).
Proof. exact (eq_refl (@ex _85366)). Qed.
Lemma lem3259309 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term129 _85366 t s u) = (term121 _85366 t s u).
Proof. exact (MK_COMB (@lem3259308 _85366) (@lem3259307 _85366 t s u)). Qed.
Lemma lem3259310 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term98 _85366 s t u) = (term98 _85366 s t u).
Proof. exact (eq_refl (term98 _85366 s t u)). Qed.
Lemma lem3259311 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term125 _85366 t s u) = (term122 _85366 t s u).
Proof. exact (MK_COMB (@lem3259310 _85366 s t u) (@lem3259309 _85366 t s u)). Qed.
Lemma lem3259312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3259313 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term130 _85366 t s u) = (term131 _85366 t s u).
Proof. exact (MK_COMB (@lem3259312) (@lem3259311 _85366 t s u)). Qed.
Lemma lem3259314 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term127 _85366 t s u x) = (term118 _85366 t s u x).
Proof. exact (eq_refl (term127 _85366 t s u x)). Qed.
Lemma lem3259315 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term98 _85366 s t u) = (term98 _85366 s t u).
Proof. exact (eq_refl (term98 _85366 s t u)). Qed.
Lemma lem3259316 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term132 _85366 t s u x) = (term133 _85366 t s u x).
Proof. exact (MK_COMB (@lem3259315 _85366 s t u) (@lem3259314 _85366 t s u x)). Qed.
Lemma lem3259317 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term134 _85366 t s u) = (term135 _85366 t s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259316 _85366 t s u x)). Qed.
Lemma lem3259318 {_85366 : Type'} : (@ex _85366) = (@ex _85366).
Proof. exact (eq_refl (@ex _85366)). Qed.
Lemma lem3259319 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term126 _85366 t s u) = (term136 _85366 t s u).
Proof. exact (MK_COMB (@lem3259318 _85366) (@lem3259317 _85366 t s u)). Qed.
Lemma lem3259320 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : ((term125 _85366 t s u) = (term126 _85366 t s u)) = ((term122 _85366 t s u) = (term136 _85366 t s u)).
Proof. exact (MK_COMB (@lem3259313 _85366 t s u) (@lem3259319 _85366 t s u)). Qed.
Lemma lem3259321 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term122 _85366 t s u) = (term136 _85366 t s u).
Proof. exact (EQ_MP (@lem3259320 _85366 t s u) (@lem3259305 _85366 t s u)). Qed.
Lemma lem3259322 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term100 _85366 t s u) = (term136 _85366 t s u).
Proof. exact (TRANS (@lem3259301 _85366 t s u) (@lem3259321 _85366 t s u)). Qed.
Lemma lem3259323 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3259324 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term102 _85366 t s u) = (term137 _85366 t s u).
Proof. exact (MK_COMB (@lem3259323) (@lem3259322 _85366 t s u)). Qed.
Lemma lem3259326 {A : Type'} (P : A -> Prop) (Q : Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3259327 {_85366 : Type'} (P : _85366 -> Prop) (Q : Prop) : (term138 _85366 P Q) = (term139 _85366 P Q).
Proof. exact (@lem3259326 _85366 P Q). Qed.
Lemma lem3259328 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term140 _85366 t s u) = (term141 _85366 t s u).
Proof. exact (@lem3259327 _85366 (term70 _85366 s t u) (term92 _85366 t s u)). Qed.
Lemma lem3259329 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term142 _85366 s t u x) = (term60 _85366 s t u x).
Proof. exact (eq_refl (term142 _85366 s t u x)). Qed.
Lemma lem3259330 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term143 _85366 s t u) = (term70 _85366 s t u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259329 _85366 s t u x)). Qed.
Lemma lem3259331 {_85366 : Type'} : (@ex _85366) = (@ex _85366).
Proof. exact (eq_refl (@ex _85366)). Qed.
Lemma lem3259332 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term144 _85366 s t u) = (term71 _85366 s t u).
Proof. exact (MK_COMB (@lem3259331 _85366) (@lem3259330 _85366 s t u)). Qed.
Lemma lem3259333 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3259334 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term145 _85366 s t u) = (term94 _85366 s t u).
Proof. exact (MK_COMB (@lem3259333) (@lem3259332 _85366 s t u)). Qed.
Lemma lem3259335 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term92 _85366 t s u) = (term92 _85366 t s u).
Proof. exact (eq_refl (term92 _85366 t s u)). Qed.
Lemma lem3259336 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term140 _85366 t s u) = (term96 _85366 t s u).
Proof. exact (MK_COMB (@lem3259334 _85366 s t u) (@lem3259335 _85366 t s u)). Qed.
Lemma lem3259337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3259338 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term146 _85366 t s u) = (term147 _85366 t s u).
Proof. exact (MK_COMB (@lem3259337) (@lem3259336 _85366 t s u)). Qed.
Lemma lem3259339 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term142 _85366 s t u x) = (term60 _85366 s t u x).
Proof. exact (eq_refl (term142 _85366 s t u x)). Qed.
Lemma lem3259340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3259341 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term148 _85366 s t u x) = (term149 _85366 s t u x).
Proof. exact (MK_COMB (@lem3259340) (@lem3259339 _85366 s t u x)). Qed.
Lemma lem3259342 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term92 _85366 t s u) = (term92 _85366 t s u).
Proof. exact (eq_refl (term92 _85366 t s u)). Qed.
Lemma lem3259343 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term150 _85366 x t s u) = (term151 _85366 x t s u).
Proof. exact (MK_COMB (@lem3259341 _85366 s t u x) (@lem3259342 _85366 t s u)). Qed.
Lemma lem3259344 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term152 _85366 t s u) = (term153 _85366 t s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259343 _85366 x t s u)). Qed.
Lemma lem3259345 {_85366 : Type'} : (@ex _85366) = (@ex _85366).
Proof. exact (eq_refl (@ex _85366)). Qed.
Lemma lem3259346 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term141 _85366 t s u) = (term154 _85366 t s u).
Proof. exact (MK_COMB (@lem3259345 _85366) (@lem3259344 _85366 t s u)). Qed.
Lemma lem3259347 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : ((term140 _85366 t s u) = (term141 _85366 t s u)) = ((term96 _85366 t s u) = (term154 _85366 t s u)).
Proof. exact (MK_COMB (@lem3259338 _85366 t s u) (@lem3259346 _85366 t s u)). Qed.
Lemma lem3259348 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term96 _85366 t s u) = (term154 _85366 t s u).
Proof. exact (EQ_MP (@lem3259347 _85366 t s u) (@lem3259328 _85366 t s u)). Qed.
Lemma lem3259349 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term104 _85366 t s u) = (term155 _85366 t s u).
Proof. exact (MK_COMB (@lem3259324 _85366 t s u) (@lem3259348 _85366 t s u)). Qed.
Lemma lem3259351 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term105 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3259352 {_85366 : Type'} (P : _85366 -> Prop) (Q : _85366 -> Prop) : (term105 _85366 P Q) = (term106 _85366 P Q).
Proof. exact (@lem3259351 _85366 P Q). Qed.
Lemma lem3259353 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term156 _85366 t s u) = (term157 _85366 t s u).
Proof. exact (@lem3259352 _85366 (term135 _85366 t s u) (term153 _85366 t s u)). Qed.
Lemma lem3259354 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term158 _85366 t s u x) = (term133 _85366 t s u x).
Proof. exact (eq_refl (term158 _85366 t s u x)). Qed.
Lemma lem3259355 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term159 _85366 t s u) = (term135 _85366 t s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259354 _85366 t s u x)). Qed.
Lemma lem3259356 {_85366 : Type'} : (@ex _85366) = (@ex _85366).
Proof. exact (eq_refl (@ex _85366)). Qed.
Lemma lem3259357 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term160 _85366 t s u) = (term136 _85366 t s u).
Proof. exact (MK_COMB (@lem3259356 _85366) (@lem3259355 _85366 t s u)). Qed.
Lemma lem3259358 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3259359 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term161 _85366 t s u) = (term137 _85366 t s u).
Proof. exact (MK_COMB (@lem3259358) (@lem3259357 _85366 t s u)). Qed.
Lemma lem3259360 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term162 _85366 t s u x) = (term151 _85366 x t s u).
Proof. exact (eq_refl (term162 _85366 t s u x)). Qed.
Lemma lem3259361 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term163 _85366 t s u) = (term153 _85366 t s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259360 _85366 x t s u)). Qed.
Lemma lem3259362 {_85366 : Type'} : (@ex _85366) = (@ex _85366).
Proof. exact (eq_refl (@ex _85366)). Qed.
Lemma lem3259363 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term164 _85366 t s u) = (term154 _85366 t s u).
Proof. exact (MK_COMB (@lem3259362 _85366) (@lem3259361 _85366 t s u)). Qed.
Lemma lem3259364 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term156 _85366 t s u) = (term155 _85366 t s u).
Proof. exact (MK_COMB (@lem3259359 _85366 t s u) (@lem3259363 _85366 t s u)). Qed.
Lemma lem3259365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3259366 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term165 _85366 t s u) = (term166 _85366 t s u).
Proof. exact (MK_COMB (@lem3259365) (@lem3259364 _85366 t s u)). Qed.
Lemma lem3259367 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term158 _85366 t s u x) = (term133 _85366 t s u x).
Proof. exact (eq_refl (term158 _85366 t s u x)). Qed.
Lemma lem3259368 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3259369 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term167 _85366 t s u x) = (term168 _85366 t s u x).
Proof. exact (MK_COMB (@lem3259368) (@lem3259367 _85366 t s u x)). Qed.
Lemma lem3259370 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term162 _85366 t s u x) = (term151 _85366 x t s u).
Proof. exact (eq_refl (term162 _85366 t s u x)). Qed.
Lemma lem3259371 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term169 _85366 t s u x) = (term170 _85366 x t s u).
Proof. exact (MK_COMB (@lem3259369 _85366 t s u x) (@lem3259370 _85366 x t s u)). Qed.
Lemma lem3259372 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term171 _85366 t s u) = (term172 _85366 t s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259371 _85366 x t s u)). Qed.
Lemma lem3259373 {_85366 : Type'} : (@ex _85366) = (@ex _85366).
Proof. exact (eq_refl (@ex _85366)). Qed.
Lemma lem3259374 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term157 _85366 t s u) = (term173 _85366 t s u).
Proof. exact (MK_COMB (@lem3259373 _85366) (@lem3259372 _85366 t s u)). Qed.
Lemma lem3259375 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : ((term156 _85366 t s u) = (term157 _85366 t s u)) = ((term155 _85366 t s u) = (term173 _85366 t s u)).
Proof. exact (MK_COMB (@lem3259366 _85366 t s u) (@lem3259374 _85366 t s u)). Qed.
Lemma lem3259376 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term155 _85366 t s u) = (term173 _85366 t s u).
Proof. exact (EQ_MP (@lem3259375 _85366 t s u) (@lem3259353 _85366 t s u)). Qed.
Lemma lem3259378 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term104 _85366 t s u) = (term173 _85366 t s u).
Proof. exact (TRANS (@lem3259349 _85366 t s u) (@lem3259376 _85366 t s u)). Qed.
Lemma lem3259379 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term56 _85366 t s u) = (term173 _85366 t s u).
Proof. exact (TRANS (@lem3259075 _85366 t s u) (@lem3259378 _85366 t s u)). Qed.
Lemma lem3259380 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term56 _85366 t s u) : term173 _85366 t s u.
Proof. exact (EQ_MP (@lem3259379 _85366 t s u) (@lem3258965 _85366 t s u h1)). Qed.
Lemma lem3259381 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term170 _85366 x t s u) : term170 _85366 x t s u.
Proof. exact (h1). Qed.
Lemma lem3259392 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term76 _85366 s u x) = (term76 _85366 s u x).
Proof. exact (eq_refl (term76 _85366 s u x)). Qed.
Lemma lem3259393 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term84 _85366 s u) = (term84 _85366 s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259392 _85366 s u x)). Qed.
Lemma lem3259394 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3259395 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term85 _85366 s u) = (term85 _85366 s u).
Proof. exact (MK_COMB (@lem3259394 _85366) (@lem3259393 _85366 s u)). Qed.
Lemma lem3259406 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) : (term76 _85366 s t x) = (term76 _85366 s t x).
Proof. exact (eq_refl (term76 _85366 s t x)). Qed.
Lemma lem3259407 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term84 _85366 s t) = (term84 _85366 s t).
Proof. exact (fun_ext (fun x : _85366 => @lem3259406 _85366 s t x)). Qed.
Lemma lem3259408 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3259409 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term85 _85366 s t) = (term85 _85366 s t).
Proof. exact (MK_COMB (@lem3259408 _85366) (@lem3259407 _85366 s t)). Qed.
Lemma lem3259410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3259411 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term91 _85366 s t) = (term91 _85366 s t).
Proof. exact (MK_COMB (@lem3259410) (@lem3259409 _85366 s t)). Qed.
Lemma lem3259412 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term92 _85366 t s u) = (term92 _85366 t s u).
Proof. exact (MK_COMB (@lem3259411 _85366 s t) (@lem3259395 _85366 s u)). Qed.
Lemma lem3259433 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term149 _85366 s t u x) = (term149 _85366 s t u x).
Proof. exact (eq_refl (term149 _85366 s t u x)). Qed.
Lemma lem3259434 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term151 _85366 x t s u) = (term151 _85366 x t s u).
Proof. exact (MK_COMB (@lem3259433 _85366 s t u x) (@lem3259412 _85366 t s u)). Qed.
Lemma lem3259459 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term118 _85366 t s u x) = (term118 _85366 t s u x).
Proof. exact (eq_refl (term118 _85366 t s u x)). Qed.
Lemma lem3259476 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term62 _85366 s t u x) = (term62 _85366 s t u x).
Proof. exact (eq_refl (term62 _85366 s t u x)). Qed.
Lemma lem3259477 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term72 _85366 s t u) = (term72 _85366 s t u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259476 _85366 s t u x)). Qed.
Lemma lem3259478 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3259479 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term73 _85366 s t u) = (term73 _85366 s t u).
Proof. exact (MK_COMB (@lem3259478 _85366) (@lem3259477 _85366 s t u)). Qed.
Lemma lem3259480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3259481 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (u : _85366 -> Prop) : (term98 _85366 s t u) = (term98 _85366 s t u).
Proof. exact (MK_COMB (@lem3259480) (@lem3259479 _85366 s t u)). Qed.
Lemma lem3259482 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term133 _85366 t s u x) = (term133 _85366 t s u x).
Proof. exact (MK_COMB (@lem3259481 _85366 s t u) (@lem3259459 _85366 t s u x)). Qed.
Lemma lem3259483 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3259484 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term168 _85366 t s u x) = (term168 _85366 t s u x).
Proof. exact (MK_COMB (@lem3259483) (@lem3259482 _85366 t s u x)). Qed.
Lemma lem3259485 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term170 _85366 x t s u) = (term170 _85366 x t s u).
Proof. exact (MK_COMB (@lem3259484 _85366 t s u x) (@lem3259434 _85366 x t s u)). Qed.
Lemma lem3259486 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term170 _85366 x t s u) : term170 _85366 x t s u.
Proof. exact (EQ_MP (@lem3259485 _85366 x t s u) (@lem3259381 _85366 x t s u h1)). Qed.
Lemma lem3259487 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term133 _85366 t s u x.
Proof. exact (h1). Qed.
Lemma lem3259488 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term151 _85366 x t s u.
Proof. exact (h1). Qed.
Lemma lem3259489 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term118 _85366 t s u x.
Proof. exact (proj2 (@lem3259487 _85366 t s u x h1)). Qed.
Lemma lem3259490 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term73 _85366 s t u.
Proof. exact (proj1 (@lem3259487 _85366 t s u x h1)). Qed.
Lemma lem3259491 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) (h1 : term75 _85366 s t x) : term75 _85366 s t x.
Proof. exact (h1). Qed.
Lemma lem3259492 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term75 _85366 s u x) : term75 _85366 s u x.
Proof. exact (h1). Qed.
Lemma lem3259497 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term92 _85366 t s u.
Proof. exact (proj2 (@lem3259488 _85366 x t s u h1)). Qed.
Lemma lem3259498 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term60 _85366 s t u x.
Proof. exact (proj1 (@lem3259488 _85366 x t s u h1)). Qed.
Lemma lem3259499 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term85 _85366 s u.
Proof. exact (proj2 (@lem3259497 _85366 x t s u h1)). Qed.
Lemma lem3259500 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term85 _85366 s t.
Proof. exact (proj1 (@lem3259497 _85366 x t s u h1)). Qed.
Lemma lem3259501 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term58 _85366 t u x.
Proof. exact (proj2 (@lem3259498 _85366 x t s u h1)). Qed.
Lemma lem3259522 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term62 _85366 s t u x) = (term174 _85366 t s u x).
Proof. exact (@lem19490 (t x) (term175 _85366 s x) (u x)). Qed.
Lemma lem3259523 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term72 _85366 s t u) = (term176 _85366 t s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259522 _85366 t s u x)). Qed.
Lemma lem3259524 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3259526 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term73 _85366 s t u) = (term177 _85366 t s u).
Proof. exact (MK_COMB (@lem3259524 _85366) (@lem3259523 _85366 t s u)). Qed.
Lemma lem3259527 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term177 _85366 t s u.
Proof. exact (EQ_MP (@lem3259526 _85366 t s u) (@lem3259490 _85366 t s u x h1)). Qed.
Lemma lem3259553 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term62 _85366 s t u x) = (term174 _85366 t s u x).
Proof. exact (@lem19490 (t x) (term175 _85366 s x) (u x)). Qed.
Lemma lem3259554 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term72 _85366 s t u) = (term176 _85366 t s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259553 _85366 t s u x)). Qed.
Lemma lem3259555 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3259557 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term73 _85366 s t u) = (term177 _85366 t s u).
Proof. exact (MK_COMB (@lem3259555 _85366) (@lem3259554 _85366 t s u)). Qed.
Lemma lem3259558 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term177 _85366 t s u.
Proof. exact (EQ_MP (@lem3259557 _85366 t s u) (@lem3259490 _85366 t s u x h1)). Qed.
Lemma lem3259574 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) : (term76 _85366 s t x) = (term76 _85366 s t x).
Proof. exact (eq_refl (term76 _85366 s t x)). Qed.
Lemma lem3259575 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term84 _85366 s t) = (term84 _85366 s t).
Proof. exact (fun_ext (fun x : _85366 => @lem3259574 _85366 s t x)). Qed.
Lemma lem3259576 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3259578 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) : (term85 _85366 s t) = (term85 _85366 s t).
Proof. exact (MK_COMB (@lem3259576 _85366) (@lem3259575 _85366 s t)). Qed.
Lemma lem3259579 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term85 _85366 s t.
Proof. exact (EQ_MP (@lem3259578 _85366 s t) (@lem3259500 _85366 x t s u h1)). Qed.
Lemma lem3259600 {_85366 : Type'} (t : _85366 -> Prop) (x : _85366) (h1 : term175 _85366 t x) : term175 _85366 t x.
Proof. exact (h1). Qed.
Lemma lem3259621 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) : (term76 _85366 s u x) = (term76 _85366 s u x).
Proof. exact (eq_refl (term76 _85366 s u x)). Qed.
Lemma lem3259622 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term84 _85366 s u) = (term84 _85366 s u).
Proof. exact (fun_ext (fun x : _85366 => @lem3259621 _85366 s u x)). Qed.
Lemma lem3259623 {_85366 : Type'} : (@all _85366) = (@all _85366).
Proof. exact (eq_refl (@all _85366)). Qed.
Lemma lem3259625 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) : (term85 _85366 s u) = (term85 _85366 s u).
Proof. exact (MK_COMB (@lem3259623 _85366) (@lem3259622 _85366 s u)). Qed.
Lemma lem3259626 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term85 _85366 s u.
Proof. exact (EQ_MP (@lem3259625 _85366 s u) (@lem3259499 _85366 x t s u h1)). Qed.
Lemma lem3259634 {_85366 : Type'} (u : _85366 -> Prop) (x : _85366) (h1 : term175 _85366 u x) : term175 _85366 u x.
Proof. exact (h1). Qed.
Lemma lem3259635 {_85366 : Type'} (_33402 : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term178 _85366 t s u _33402.
Proof. exact (@lem3259527 _85366 t s u x h1 _33402). Qed.
Lemma lem3259636 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (_33402 : _85366) : (term178 _85366 t s u _33402) = (term174 _85366 t s u _33402).
Proof. exact (eq_refl (term178 _85366 t s u _33402)). Qed.
Lemma lem3259637 {_85366 : Type'} (_33402 : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term174 _85366 t s u _33402.
Proof. exact (EQ_MP (@lem3259636 _85366 t s u _33402) (@lem3259635 _85366 _33402 t s u x h1)). Qed.
Lemma lem3259638 {_85366 : Type'} (_33403 : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term178 _85366 t s u _33403.
Proof. exact (@lem3259558 _85366 t s u x h1 _33403). Qed.
Lemma lem3259639 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (_33403 : _85366) : (term178 _85366 t s u _33403) = (term174 _85366 t s u _33403).
Proof. exact (eq_refl (term178 _85366 t s u _33403)). Qed.
Lemma lem3259640 {_85366 : Type'} (_33403 : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term174 _85366 t s u _33403.
Proof. exact (EQ_MP (@lem3259639 _85366 t s u _33403) (@lem3259638 _85366 _33403 t s u x h1)). Qed.
Lemma lem3259641 {_85366 : Type'} (_33404 : _85366) (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term179 _85366 s t _33404.
Proof. exact (@lem3259579 _85366 x t s u h1 _33404). Qed.
Lemma lem3259642 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (_33404 : _85366) : (term179 _85366 s t _33404) = (term76 _85366 s t _33404).
Proof. exact (eq_refl (term179 _85366 s t _33404)). Qed.
Lemma lem3259650 {_85366 : Type'} (_33407 : _85366) (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term179 _85366 s u _33407.
Proof. exact (@lem3259626 _85366 x t s u h1 _33407). Qed.
Lemma lem3259651 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (_33407 : _85366) : (term179 _85366 s u _33407) = (term76 _85366 s u _33407).
Proof. exact (eq_refl (term179 _85366 s u _33407)). Qed.
Lemma lem3259660 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) (h1 : term75 _85366 s t x) : term175 _85366 t x.
Proof. exact (proj2 (@lem3259491 _85366 s t x h1)). Qed.
Lemma lem3259666 {_85366 : Type'} (_33402 : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term76 _85366 s t _33402.
Proof. exact (proj1 (@lem3259637 _85366 _33402 t s u x h1)). Qed.
Lemma lem3259676 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term75 _85366 s u x) : term175 _85366 u x.
Proof. exact (proj2 (@lem3259492 _85366 s u x h1)). Qed.
Lemma lem3259688 {_85366 : Type'} (_33403 : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term76 _85366 s u _33403.
Proof. exact (proj2 (@lem3259640 _85366 _33403 t s u x h1)). Qed.
Lemma lem3259694 {_85366 : Type'} (_33404 : _85366) (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term76 _85366 s t _33404.
Proof. exact (EQ_MP (@lem3259642 _85366 s t _33404) (@lem3259641 _85366 _33404 x t s u h1)). Qed.
Lemma lem3259704 {_85366 : Type'} (t : _85366 -> Prop) (x : _85366) (h1 : term175 _85366 t x) : term175 _85366 t x.
Proof. exact (h1). Qed.
Lemma lem3259716 {_85366 : Type'} (_33407 : _85366) (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term76 _85366 s u _33407.
Proof. exact (EQ_MP (@lem3259651 _85366 s u _33407) (@lem3259650 _85366 _33407 x t s u h1)). Qed.
Lemma lem3259720 {_85366 : Type'} (u : _85366 -> Prop) (x : _85366) (h1 : term175 _85366 u x) : term175 _85366 u x.
Proof. exact (h1). Qed.
Lemma lem3259722 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) (h1 : term75 _85366 s t x) : s x.
Proof. exact (proj1 (@lem3259491 _85366 s t x h1)). Qed.
Lemma lem3259723 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) (h1 : term75 _85366 s t x) : term180 _85366 s x.
Proof. exact (fun h0 : term175 _85366 s x => @lem3259722 _85366 s t x h1). Qed.
Lemma lem3259725 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3259726 {_85366 : Type'} (s : _85366 -> Prop) (x : _85366) : (term180 _85366 s x) = (s x).
Proof. exact (@lem3259725 (s x)). Qed.
Lemma lem3259727 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) (h1 : term75 _85366 s t x) : s x.
Proof. exact (EQ_MP (@lem3259726 _85366 s x) (@lem3259723 _85366 s t x h1)). Qed.
Lemma lem3259733 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3259734 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33402 : _85366) : (term76 _85366 s t _33402) = (term182 _85366 t s _33402).
Proof. exact (@lem3259733 (t _33402) (term175 _85366 s _33402)). Qed.
Lemma lem3259740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3259741 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33402 : _85366) : (term183 _85366 s t _33402) = (term184 _85366 t s _33402).
Proof. exact (MK_COMB (@lem3259740) (@lem3259734 _85366 t s _33402)). Qed.
Lemma lem3259747 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33402 : _85366) : (term182 _85366 t s _33402) = (term182 _85366 t s _33402).
Proof. exact (eq_refl (term182 _85366 t s _33402)). Qed.
Lemma lem3259748 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33402 : _85366) : ((term76 _85366 s t _33402) = (term182 _85366 t s _33402)) = ((term182 _85366 t s _33402) = (term182 _85366 t s _33402)).
Proof. exact (MK_COMB (@lem3259741 _85366 t s _33402) (@lem3259747 _85366 t s _33402)). Qed.
Lemma lem3259750 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3259751 (x : Prop) : (x = x) = True.
Proof. exact (@lem3259750 Prop x). Qed.
Lemma lem3259752 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33402 : _85366) : ((term182 _85366 t s _33402) = (term182 _85366 t s _33402)) = True.
Proof. exact (@lem3259751 (term182 _85366 t s _33402)). Qed.
Lemma lem3259753 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33402 : _85366) : ((term76 _85366 s t _33402) = (term182 _85366 t s _33402)) = True.
Proof. exact (TRANS (@lem3259748 _85366 t s _33402) (@lem3259752 _85366 t s _33402)). Qed.
Lemma lem3259754 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33402 : _85366) : True = ((term76 _85366 s t _33402) = (term182 _85366 t s _33402)).
Proof. exact (SYM (@lem3259753 _85366 t s _33402)). Qed.
Lemma lem3259755 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33402 : _85366) : (term76 _85366 s t _33402) = (term182 _85366 t s _33402).
Proof. exact (EQ_MP (@lem3259754 _85366 t s _33402) (@lem0)). Qed.
Lemma lem3259756 {_85366 : Type'} (_33402 : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term182 _85366 t s _33402.
Proof. exact (EQ_MP (@lem3259755 _85366 t s _33402) (@lem3259666 _85366 _33402 t s u x h1)). Qed.
Lemma lem3259758 (b : Prop) (a : Prop) : (a \/ b) = (term185 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3259759 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (_33402 : _85366) : (term182 _85366 t s _33402) = (term186 _85366 s t _33402).
Proof. exact (@lem3259758 (term175 _85366 s _33402) (t _33402)). Qed.
Lemma lem3259761 (a : Prop) : (term54 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3259762 {_85366 : Type'} (s : _85366 -> Prop) (_33402 : _85366) : (term187 _85366 s _33402) = (s _33402).
Proof. exact (@lem3259761 (s _33402)). Qed.
Lemma lem3259763 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3259764 {_85366 : Type'} (s : _85366 -> Prop) (_33402 : _85366) : (term188 _85366 s _33402) = (term22 _85366 s _33402).
Proof. exact (MK_COMB (@lem3259763) (@lem3259762 _85366 s _33402)). Qed.
Lemma lem3259765 {_85366 : Type'} (t : _85366 -> Prop) (_33402 : _85366) : (t _33402) = (t _33402).
Proof. exact (eq_refl (t _33402)). Qed.
Lemma lem3259766 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (_33402 : _85366) : (term186 _85366 s t _33402) = (term35 _85366 s t _33402).
Proof. exact (MK_COMB (@lem3259764 _85366 s _33402) (@lem3259765 _85366 t _33402)). Qed.
Lemma lem3259767 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (_33402 : _85366) : (term182 _85366 t s _33402) = (term35 _85366 s t _33402).
Proof. exact (TRANS (@lem3259759 _85366 s t _33402) (@lem3259766 _85366 s t _33402)). Qed.
Lemma lem3259770 {_85366 : Type'} (_33402 : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term35 _85366 s t _33402.
Proof. exact (EQ_MP (@lem3259767 _85366 s t _33402) (@lem3259756 _85366 _33402 t s u x h1)). Qed.
Lemma lem3259771 {_85366 : Type'} (_33402 : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term35 _85366 s t _33402.
Proof. exact (@lem3259770 _85366 _33402 t s u x h1). Qed.
Lemma lem3259772 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term35 _85366 s t x.
Proof. exact (@lem3259771 _85366 x t s u x h1). Qed.
Lemma lem3259775 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) (h2 : term75 _85366 s t x) : t x.
Proof. exact (@lem3259772 _85366 t s u x h1 (@lem3259727 _85366 s t x h2)). Qed.
Lemma lem3259776 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) (h2 : term75 _85366 s t x) : term180 _85366 t x.
Proof. exact (fun h0 : term175 _85366 t x => @lem3259775 _85366 u s t x h1 h2). Qed.
Lemma lem3259778 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3259779 {_85366 : Type'} (t : _85366 -> Prop) (x : _85366) : (term180 _85366 t x) = (t x).
Proof. exact (@lem3259778 (t x)). Qed.
Lemma lem3259780 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) (h2 : term75 _85366 s t x) : t x.
Proof. exact (EQ_MP (@lem3259779 _85366 t x) (@lem3259776 _85366 u s t x h1 h2)). Qed.
Lemma lem3259783 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3259785 {_85366 : Type'} (t : _85366 -> Prop) (x : _85366) : (term175 _85366 t x) = (term189 _85366 t x).
Proof. exact (@lem3259783 (t x)). Qed.
Lemma lem3259788 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) (h1 : term75 _85366 s t x) : term189 _85366 t x.
Proof. exact (EQ_MP (@lem3259785 _85366 t x) (@lem3259660 _85366 s t x h1)). Qed.
Lemma lem3259791 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) (h2 : term75 _85366 s t x) : False.
Proof. exact (@lem3259788 _85366 s t x h2 (@lem3259780 _85366 u s t x h1 h2)). Qed.
Lemma lem3259792 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) (h2 : term75 _85366 s t x) : term190.
Proof. exact (fun h0 : ~ False => @lem3259791 _85366 u s t x h1 h2). Qed.
Lemma lem3259794 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3259795 : term190 = False.
Proof. exact (@lem3259794 False). Qed.
Lemma lem3259796 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (t : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) (h2 : term75 _85366 s t x) : False.
Proof. exact (EQ_MP (@lem3259795) (@lem3259792 _85366 u s t x h1 h2)). Qed.
Lemma lem3259798 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term75 _85366 s u x) : s x.
Proof. exact (proj1 (@lem3259492 _85366 s u x h1)). Qed.
Lemma lem3259799 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term75 _85366 s u x) : term180 _85366 s x.
Proof. exact (fun h0 : term175 _85366 s x => @lem3259798 _85366 s u x h1). Qed.
Lemma lem3259801 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3259802 {_85366 : Type'} (s : _85366 -> Prop) (x : _85366) : (term180 _85366 s x) = (s x).
Proof. exact (@lem3259801 (s x)). Qed.
Lemma lem3259803 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term75 _85366 s u x) : s x.
Proof. exact (EQ_MP (@lem3259802 _85366 s x) (@lem3259799 _85366 s u x h1)). Qed.
Lemma lem3259809 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3259810 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33403 : _85366) : (term76 _85366 s u _33403) = (term182 _85366 u s _33403).
Proof. exact (@lem3259809 (u _33403) (term175 _85366 s _33403)). Qed.
Lemma lem3259816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3259817 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33403 : _85366) : (term183 _85366 s u _33403) = (term184 _85366 u s _33403).
Proof. exact (MK_COMB (@lem3259816) (@lem3259810 _85366 u s _33403)). Qed.
Lemma lem3259823 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33403 : _85366) : (term182 _85366 u s _33403) = (term182 _85366 u s _33403).
Proof. exact (eq_refl (term182 _85366 u s _33403)). Qed.
Lemma lem3259824 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33403 : _85366) : ((term76 _85366 s u _33403) = (term182 _85366 u s _33403)) = ((term182 _85366 u s _33403) = (term182 _85366 u s _33403)).
Proof. exact (MK_COMB (@lem3259817 _85366 u s _33403) (@lem3259823 _85366 u s _33403)). Qed.
Lemma lem3259826 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3259827 (x : Prop) : (x = x) = True.
Proof. exact (@lem3259826 Prop x). Qed.
Lemma lem3259828 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33403 : _85366) : ((term182 _85366 u s _33403) = (term182 _85366 u s _33403)) = True.
Proof. exact (@lem3259827 (term182 _85366 u s _33403)). Qed.
Lemma lem3259829 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33403 : _85366) : ((term76 _85366 s u _33403) = (term182 _85366 u s _33403)) = True.
Proof. exact (TRANS (@lem3259824 _85366 u s _33403) (@lem3259828 _85366 u s _33403)). Qed.
Lemma lem3259830 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33403 : _85366) : True = ((term76 _85366 s u _33403) = (term182 _85366 u s _33403)).
Proof. exact (SYM (@lem3259829 _85366 u s _33403)). Qed.
Lemma lem3259831 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33403 : _85366) : (term76 _85366 s u _33403) = (term182 _85366 u s _33403).
Proof. exact (EQ_MP (@lem3259830 _85366 u s _33403) (@lem0)). Qed.
Lemma lem3259832 {_85366 : Type'} (_33403 : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term182 _85366 u s _33403.
Proof. exact (EQ_MP (@lem3259831 _85366 u s _33403) (@lem3259688 _85366 _33403 t s u x h1)). Qed.
Lemma lem3259834 (b : Prop) (a : Prop) : (a \/ b) = (term185 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3259835 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (_33403 : _85366) : (term182 _85366 u s _33403) = (term186 _85366 s u _33403).
Proof. exact (@lem3259834 (term175 _85366 s _33403) (u _33403)). Qed.
Lemma lem3259837 (a : Prop) : (term54 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3259838 {_85366 : Type'} (s : _85366 -> Prop) (_33403 : _85366) : (term187 _85366 s _33403) = (s _33403).
Proof. exact (@lem3259837 (s _33403)). Qed.
Lemma lem3259839 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3259840 {_85366 : Type'} (s : _85366 -> Prop) (_33403 : _85366) : (term188 _85366 s _33403) = (term22 _85366 s _33403).
Proof. exact (MK_COMB (@lem3259839) (@lem3259838 _85366 s _33403)). Qed.
Lemma lem3259841 {_85366 : Type'} (u : _85366 -> Prop) (_33403 : _85366) : (u _33403) = (u _33403).
Proof. exact (eq_refl (u _33403)). Qed.
Lemma lem3259842 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (_33403 : _85366) : (term186 _85366 s u _33403) = (term35 _85366 s u _33403).
Proof. exact (MK_COMB (@lem3259840 _85366 s _33403) (@lem3259841 _85366 u _33403)). Qed.
Lemma lem3259843 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (_33403 : _85366) : (term182 _85366 u s _33403) = (term35 _85366 s u _33403).
Proof. exact (TRANS (@lem3259835 _85366 s u _33403) (@lem3259842 _85366 s u _33403)). Qed.
Lemma lem3259846 {_85366 : Type'} (_33403 : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term35 _85366 s u _33403.
Proof. exact (EQ_MP (@lem3259843 _85366 s u _33403) (@lem3259832 _85366 _33403 t s u x h1)). Qed.
Lemma lem3259847 {_85366 : Type'} (_33403 : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term35 _85366 s u _33403.
Proof. exact (@lem3259846 _85366 _33403 t s u x h1). Qed.
Lemma lem3259848 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : term35 _85366 s u x.
Proof. exact (@lem3259847 _85366 x t s u x h1). Qed.
Lemma lem3259851 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) (h2 : term75 _85366 s u x) : u x.
Proof. exact (@lem3259848 _85366 t s u x h1 (@lem3259803 _85366 s u x h2)). Qed.
Lemma lem3259852 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) (h2 : term75 _85366 s u x) : term180 _85366 u x.
Proof. exact (fun h0 : term175 _85366 u x => @lem3259851 _85366 t s u x h1 h2). Qed.
Lemma lem3259854 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3259855 {_85366 : Type'} (u : _85366 -> Prop) (x : _85366) : (term180 _85366 u x) = (u x).
Proof. exact (@lem3259854 (u x)). Qed.
Lemma lem3259856 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) (h2 : term75 _85366 s u x) : u x.
Proof. exact (EQ_MP (@lem3259855 _85366 u x) (@lem3259852 _85366 t s u x h1 h2)). Qed.
Lemma lem3259859 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3259861 {_85366 : Type'} (u : _85366 -> Prop) (x : _85366) : (term175 _85366 u x) = (term189 _85366 u x).
Proof. exact (@lem3259859 (u x)). Qed.
Lemma lem3259864 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term75 _85366 s u x) : term189 _85366 u x.
Proof. exact (EQ_MP (@lem3259861 _85366 u x) (@lem3259676 _85366 s u x h1)). Qed.
Lemma lem3259867 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) (h2 : term75 _85366 s u x) : False.
Proof. exact (@lem3259864 _85366 s u x h2 (@lem3259856 _85366 t s u x h1 h2)). Qed.
Lemma lem3259868 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) (h2 : term75 _85366 s u x) : term190.
Proof. exact (fun h0 : ~ False => @lem3259867 _85366 t s u x h1 h2). Qed.
Lemma lem3259870 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3259871 : term190 = False.
Proof. exact (@lem3259870 False). Qed.
Lemma lem3259872 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) (h2 : term75 _85366 s u x) : False.
Proof. exact (EQ_MP (@lem3259871) (@lem3259868 _85366 t s u x h1 h2)). Qed.
Lemma lem3259874 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : s x.
Proof. exact (proj1 (@lem3259498 _85366 x t s u h1)). Qed.
Lemma lem3259875 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term180 _85366 s x.
Proof. exact (fun h0 : term175 _85366 s x => @lem3259874 _85366 x t s u h1). Qed.
Lemma lem3259877 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3259878 {_85366 : Type'} (s : _85366 -> Prop) (x : _85366) : (term180 _85366 s x) = (s x).
Proof. exact (@lem3259877 (s x)). Qed.
Lemma lem3259879 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : s x.
Proof. exact (EQ_MP (@lem3259878 _85366 s x) (@lem3259875 _85366 x t s u h1)). Qed.
Lemma lem3259885 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3259886 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33404 : _85366) : (term76 _85366 s t _33404) = (term182 _85366 t s _33404).
Proof. exact (@lem3259885 (t _33404) (term175 _85366 s _33404)). Qed.
Lemma lem3259892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3259893 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33404 : _85366) : (term183 _85366 s t _33404) = (term184 _85366 t s _33404).
Proof. exact (MK_COMB (@lem3259892) (@lem3259886 _85366 t s _33404)). Qed.
Lemma lem3259899 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33404 : _85366) : (term182 _85366 t s _33404) = (term182 _85366 t s _33404).
Proof. exact (eq_refl (term182 _85366 t s _33404)). Qed.
Lemma lem3259900 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33404 : _85366) : ((term76 _85366 s t _33404) = (term182 _85366 t s _33404)) = ((term182 _85366 t s _33404) = (term182 _85366 t s _33404)).
Proof. exact (MK_COMB (@lem3259893 _85366 t s _33404) (@lem3259899 _85366 t s _33404)). Qed.
Lemma lem3259902 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3259903 (x : Prop) : (x = x) = True.
Proof. exact (@lem3259902 Prop x). Qed.
Lemma lem3259904 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33404 : _85366) : ((term182 _85366 t s _33404) = (term182 _85366 t s _33404)) = True.
Proof. exact (@lem3259903 (term182 _85366 t s _33404)). Qed.
Lemma lem3259905 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33404 : _85366) : ((term76 _85366 s t _33404) = (term182 _85366 t s _33404)) = True.
Proof. exact (TRANS (@lem3259900 _85366 t s _33404) (@lem3259904 _85366 t s _33404)). Qed.
Lemma lem3259906 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33404 : _85366) : True = ((term76 _85366 s t _33404) = (term182 _85366 t s _33404)).
Proof. exact (SYM (@lem3259905 _85366 t s _33404)). Qed.
Lemma lem3259907 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (_33404 : _85366) : (term76 _85366 s t _33404) = (term182 _85366 t s _33404).
Proof. exact (EQ_MP (@lem3259906 _85366 t s _33404) (@lem0)). Qed.
Lemma lem3259908 {_85366 : Type'} (_33404 : _85366) (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term182 _85366 t s _33404.
Proof. exact (EQ_MP (@lem3259907 _85366 t s _33404) (@lem3259694 _85366 _33404 x t s u h1)). Qed.
Lemma lem3259910 (b : Prop) (a : Prop) : (a \/ b) = (term185 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3259911 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (_33404 : _85366) : (term182 _85366 t s _33404) = (term186 _85366 s t _33404).
Proof. exact (@lem3259910 (term175 _85366 s _33404) (t _33404)). Qed.
Lemma lem3259913 (a : Prop) : (term54 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3259914 {_85366 : Type'} (s : _85366 -> Prop) (_33404 : _85366) : (term187 _85366 s _33404) = (s _33404).
Proof. exact (@lem3259913 (s _33404)). Qed.
Lemma lem3259915 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3259916 {_85366 : Type'} (s : _85366 -> Prop) (_33404 : _85366) : (term188 _85366 s _33404) = (term22 _85366 s _33404).
Proof. exact (MK_COMB (@lem3259915) (@lem3259914 _85366 s _33404)). Qed.
Lemma lem3259917 {_85366 : Type'} (t : _85366 -> Prop) (_33404 : _85366) : (t _33404) = (t _33404).
Proof. exact (eq_refl (t _33404)). Qed.
Lemma lem3259918 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (_33404 : _85366) : (term186 _85366 s t _33404) = (term35 _85366 s t _33404).
Proof. exact (MK_COMB (@lem3259916 _85366 s _33404) (@lem3259917 _85366 t _33404)). Qed.
Lemma lem3259919 {_85366 : Type'} (s : _85366 -> Prop) (t : _85366 -> Prop) (_33404 : _85366) : (term182 _85366 t s _33404) = (term35 _85366 s t _33404).
Proof. exact (TRANS (@lem3259911 _85366 s t _33404) (@lem3259918 _85366 s t _33404)). Qed.
Lemma lem3259922 {_85366 : Type'} (_33404 : _85366) (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term35 _85366 s t _33404.
Proof. exact (EQ_MP (@lem3259919 _85366 s t _33404) (@lem3259908 _85366 _33404 x t s u h1)). Qed.
Lemma lem3259923 {_85366 : Type'} (_33404 : _85366) (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term35 _85366 s t _33404.
Proof. exact (@lem3259922 _85366 _33404 x t s u h1). Qed.
Lemma lem3259924 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term35 _85366 s t x.
Proof. exact (@lem3259923 _85366 x x t s u h1). Qed.
Lemma lem3259927 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : t x.
Proof. exact (@lem3259924 _85366 x t s u h1 (@lem3259879 _85366 x t s u h1)). Qed.
Lemma lem3259928 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term180 _85366 t x.
Proof. exact (fun h0 : term175 _85366 t x => @lem3259927 _85366 x t s u h1). Qed.
Lemma lem3259930 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3259931 {_85366 : Type'} (t : _85366 -> Prop) (x : _85366) : (term180 _85366 t x) = (t x).
Proof. exact (@lem3259930 (t x)). Qed.
Lemma lem3259932 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : t x.
Proof. exact (EQ_MP (@lem3259931 _85366 t x) (@lem3259928 _85366 x t s u h1)). Qed.
Lemma lem3259935 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3259937 {_85366 : Type'} (t : _85366 -> Prop) (x : _85366) : (term175 _85366 t x) = (term189 _85366 t x).
Proof. exact (@lem3259935 (t x)). Qed.
Lemma lem3259940 {_85366 : Type'} (t : _85366 -> Prop) (x : _85366) (h1 : term175 _85366 t x) : term189 _85366 t x.
Proof. exact (EQ_MP (@lem3259937 _85366 t x) (@lem3259704 _85366 t x h1)). Qed.
Lemma lem3259943 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 t x) (h2 : term151 _85366 x t s u) : False.
Proof. exact (@lem3259940 _85366 t x h1 (@lem3259932 _85366 x t s u h2)). Qed.
Lemma lem3259944 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 t x) (h2 : term151 _85366 x t s u) : term190.
Proof. exact (fun h0 : ~ False => @lem3259943 _85366 x t s u h1 h2). Qed.
Lemma lem3259946 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3259947 : term190 = False.
Proof. exact (@lem3259946 False). Qed.
Lemma lem3259948 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 t x) (h2 : term151 _85366 x t s u) : False.
Proof. exact (EQ_MP (@lem3259947) (@lem3259944 _85366 x t s u h1 h2)). Qed.
Lemma lem3259950 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : s x.
Proof. exact (proj1 (@lem3259498 _85366 x t s u h1)). Qed.
Lemma lem3259951 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term180 _85366 s x.
Proof. exact (fun h0 : term175 _85366 s x => @lem3259950 _85366 x t s u h1). Qed.
Lemma lem3259953 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3259954 {_85366 : Type'} (s : _85366 -> Prop) (x : _85366) : (term180 _85366 s x) = (s x).
Proof. exact (@lem3259953 (s x)). Qed.
Lemma lem3259955 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : s x.
Proof. exact (EQ_MP (@lem3259954 _85366 s x) (@lem3259951 _85366 x t s u h1)). Qed.
Lemma lem3259961 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3259962 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33407 : _85366) : (term76 _85366 s u _33407) = (term182 _85366 u s _33407).
Proof. exact (@lem3259961 (u _33407) (term175 _85366 s _33407)). Qed.
Lemma lem3259968 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3259969 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33407 : _85366) : (term183 _85366 s u _33407) = (term184 _85366 u s _33407).
Proof. exact (MK_COMB (@lem3259968) (@lem3259962 _85366 u s _33407)). Qed.
Lemma lem3259975 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33407 : _85366) : (term182 _85366 u s _33407) = (term182 _85366 u s _33407).
Proof. exact (eq_refl (term182 _85366 u s _33407)). Qed.
Lemma lem3259976 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33407 : _85366) : ((term76 _85366 s u _33407) = (term182 _85366 u s _33407)) = ((term182 _85366 u s _33407) = (term182 _85366 u s _33407)).
Proof. exact (MK_COMB (@lem3259969 _85366 u s _33407) (@lem3259975 _85366 u s _33407)). Qed.
Lemma lem3259978 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3259979 (x : Prop) : (x = x) = True.
Proof. exact (@lem3259978 Prop x). Qed.
Lemma lem3259980 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33407 : _85366) : ((term182 _85366 u s _33407) = (term182 _85366 u s _33407)) = True.
Proof. exact (@lem3259979 (term182 _85366 u s _33407)). Qed.
Lemma lem3259981 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33407 : _85366) : ((term76 _85366 s u _33407) = (term182 _85366 u s _33407)) = True.
Proof. exact (TRANS (@lem3259976 _85366 u s _33407) (@lem3259980 _85366 u s _33407)). Qed.
Lemma lem3259982 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33407 : _85366) : True = ((term76 _85366 s u _33407) = (term182 _85366 u s _33407)).
Proof. exact (SYM (@lem3259981 _85366 u s _33407)). Qed.
Lemma lem3259983 {_85366 : Type'} (u : _85366 -> Prop) (s : _85366 -> Prop) (_33407 : _85366) : (term76 _85366 s u _33407) = (term182 _85366 u s _33407).
Proof. exact (EQ_MP (@lem3259982 _85366 u s _33407) (@lem0)). Qed.
Lemma lem3259984 {_85366 : Type'} (_33407 : _85366) (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term182 _85366 u s _33407.
Proof. exact (EQ_MP (@lem3259983 _85366 u s _33407) (@lem3259716 _85366 _33407 x t s u h1)). Qed.
Lemma lem3259986 (b : Prop) (a : Prop) : (a \/ b) = (term185 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3259987 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (_33407 : _85366) : (term182 _85366 u s _33407) = (term186 _85366 s u _33407).
Proof. exact (@lem3259986 (term175 _85366 s _33407) (u _33407)). Qed.
Lemma lem3259989 (a : Prop) : (term54 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3259990 {_85366 : Type'} (s : _85366 -> Prop) (_33407 : _85366) : (term187 _85366 s _33407) = (s _33407).
Proof. exact (@lem3259989 (s _33407)). Qed.
Lemma lem3259991 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3259992 {_85366 : Type'} (s : _85366 -> Prop) (_33407 : _85366) : (term188 _85366 s _33407) = (term22 _85366 s _33407).
Proof. exact (MK_COMB (@lem3259991) (@lem3259990 _85366 s _33407)). Qed.
Lemma lem3259993 {_85366 : Type'} (u : _85366 -> Prop) (_33407 : _85366) : (u _33407) = (u _33407).
Proof. exact (eq_refl (u _33407)). Qed.
Lemma lem3259994 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (_33407 : _85366) : (term186 _85366 s u _33407) = (term35 _85366 s u _33407).
Proof. exact (MK_COMB (@lem3259992 _85366 s _33407) (@lem3259993 _85366 u _33407)). Qed.
Lemma lem3259995 {_85366 : Type'} (s : _85366 -> Prop) (u : _85366 -> Prop) (_33407 : _85366) : (term182 _85366 u s _33407) = (term35 _85366 s u _33407).
Proof. exact (TRANS (@lem3259987 _85366 s u _33407) (@lem3259994 _85366 s u _33407)). Qed.
Lemma lem3259998 {_85366 : Type'} (_33407 : _85366) (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term35 _85366 s u _33407.
Proof. exact (EQ_MP (@lem3259995 _85366 s u _33407) (@lem3259984 _85366 _33407 x t s u h1)). Qed.
Lemma lem3259999 {_85366 : Type'} (_33407 : _85366) (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term35 _85366 s u _33407.
Proof. exact (@lem3259998 _85366 _33407 x t s u h1). Qed.
Lemma lem3260000 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term35 _85366 s u x.
Proof. exact (@lem3259999 _85366 x x t s u h1). Qed.
Lemma lem3260003 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : u x.
Proof. exact (@lem3260000 _85366 x t s u h1 (@lem3259955 _85366 x t s u h1)). Qed.
Lemma lem3260004 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : term180 _85366 u x.
Proof. exact (fun h0 : term175 _85366 u x => @lem3260003 _85366 x t s u h1). Qed.
Lemma lem3260006 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3260007 {_85366 : Type'} (u : _85366 -> Prop) (x : _85366) : (term180 _85366 u x) = (u x).
Proof. exact (@lem3260006 (u x)). Qed.
Lemma lem3260008 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : u x.
Proof. exact (EQ_MP (@lem3260007 _85366 u x) (@lem3260004 _85366 x t s u h1)). Qed.
Lemma lem3260011 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3260013 {_85366 : Type'} (u : _85366 -> Prop) (x : _85366) : (term175 _85366 u x) = (term189 _85366 u x).
Proof. exact (@lem3260011 (u x)). Qed.
Lemma lem3260016 {_85366 : Type'} (u : _85366 -> Prop) (x : _85366) (h1 : term175 _85366 u x) : term189 _85366 u x.
Proof. exact (EQ_MP (@lem3260013 _85366 u x) (@lem3259720 _85366 u x h1)). Qed.
Lemma lem3260019 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 u x) (h2 : term151 _85366 x t s u) : False.
Proof. exact (@lem3260016 _85366 u x h1 (@lem3260008 _85366 x t s u h2)). Qed.
Lemma lem3260020 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 u x) (h2 : term151 _85366 x t s u) : term190.
Proof. exact (fun h0 : ~ False => @lem3260019 _85366 x t s u h1 h2). Qed.
Lemma lem3260022 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3260023 : term190 = False.
Proof. exact (@lem3260022 False). Qed.
Lemma lem3260024 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 u x) (h2 : term151 _85366 x t s u) : False.
Proof. exact (EQ_MP (@lem3260023) (@lem3260020 _85366 x t s u h1 h2)). Qed.
Lemma lem3260025 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 u x) (h2 : term151 _85366 x t s u) : (term175 _85366 u x) = False.
Proof. exact (prop_ext (fun h3 : term175 _85366 u x => @lem3260024 _85366 x t s u h1 h2) (fun h3 : False => @lem3259720 _85366 u x h1)). Qed.
Lemma lem3260026 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 u x) (h2 : term151 _85366 x t s u) : False.
Proof. exact (EQ_MP (@lem3260025 _85366 x t s u h1 h2) (@lem3259720 _85366 u x h1)). Qed.
Lemma lem3260027 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 t x) (h2 : term151 _85366 x t s u) : (term175 _85366 t x) = False.
Proof. exact (prop_ext (fun h3 : term175 _85366 t x => @lem3259948 _85366 x t s u h1 h2) (fun h3 : False => @lem3259704 _85366 t x h1)). Qed.
Lemma lem3260028 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 t x) (h2 : term151 _85366 x t s u) : False.
Proof. exact (EQ_MP (@lem3260027 _85366 x t s u h1 h2) (@lem3259704 _85366 t x h1)). Qed.
Lemma lem3260029 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 u x) (h2 : term151 _85366 x t s u) : (term175 _85366 u x) = False.
Proof. exact (prop_ext (fun h3 : term175 _85366 u x => @lem3260026 _85366 x t s u h1 h2) (fun h3 : False => @lem3259634 _85366 u x h1)). Qed.
Lemma lem3260030 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 u x) (h2 : term151 _85366 x t s u) : False.
Proof. exact (EQ_MP (@lem3260029 _85366 x t s u h1 h2) (@lem3259634 _85366 u x h1)). Qed.
Lemma lem3260031 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 t x) (h2 : term151 _85366 x t s u) : (term175 _85366 t x) = False.
Proof. exact (prop_ext (fun h3 : term175 _85366 t x => @lem3260028 _85366 x t s u h1 h2) (fun h3 : False => @lem3259600 _85366 t x h1)). Qed.
Lemma lem3260032 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 t x) (h2 : term151 _85366 x t s u) : False.
Proof. exact (EQ_MP (@lem3260031 _85366 x t s u h1 h2) (@lem3259600 _85366 t x h1)). Qed.
Lemma lem3260033 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 u x) (h2 : term151 _85366 x t s u) : (term175 _85366 u x) = False.
Proof. exact (prop_ext (fun h3 : term175 _85366 u x => @lem3260030 _85366 x t s u h1 h2) (fun h3 : False => @lem3259634 _85366 u x h1)). Qed.
Lemma lem3260034 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 u x) (h2 : term151 _85366 x t s u) : False.
Proof. exact (EQ_MP (@lem3260033 _85366 x t s u h1 h2) (@lem3259634 _85366 u x h1)). Qed.
Lemma lem3260035 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 t x) (h2 : term151 _85366 x t s u) : (term175 _85366 t x) = False.
Proof. exact (prop_ext (fun h3 : term175 _85366 t x => @lem3260032 _85366 x t s u h1 h2) (fun h3 : False => @lem3259600 _85366 t x h1)). Qed.
Lemma lem3260036 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term175 _85366 t x) (h2 : term151 _85366 x t s u) : False.
Proof. exact (EQ_MP (@lem3260035 _85366 x t s u h1 h2) (@lem3259600 _85366 t x h1)). Qed.
Lemma lem3260037 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term151 _85366 x t s u) : False.
Proof. exact (or_elim (@lem3259501 _85366 x t s u h1) (fun h0 : term175 _85366 t x => @lem3260036 _85366 x t s u h0 h1) (fun h0 : term175 _85366 u x => @lem3260034 _85366 x t s u h0 h1)). Qed.
Lemma lem3260038 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (x : _85366) (h1 : term133 _85366 t s u x) : False.
Proof. exact (or_elim (@lem3259489 _85366 t s u x h1) (fun h0 : term75 _85366 s t x => @lem3259796 _85366 u s t x h1 h0) (fun h0 : term75 _85366 s u x => @lem3259872 _85366 t s u x h1 h0)). Qed.
Lemma lem3260039 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term170 _85366 x t s u) : False.
Proof. exact (or_elim (@lem3259486 _85366 x t s u h1) (fun h0 : term133 _85366 t s u x => @lem3260038 _85366 t s u x h0) (fun h0 : term151 _85366 x t s u => @lem3260037 _85366 x t s u h0)). Qed.
Lemma lem3260040 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term170 _85366 x t s u) : (term170 _85366 x t s u) = False.
Proof. exact (prop_ext (fun h2 : term170 _85366 x t s u => @lem3260039 _85366 x t s u h1) (fun h2 : False => @lem3259486 _85366 x t s u h1)). Qed.
Lemma lem3260041 {_85366 : Type'} (x : _85366) (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term170 _85366 x t s u) : False.
Proof. exact (EQ_MP (@lem3260040 _85366 x t s u h1) (@lem3259486 _85366 x t s u h1)). Qed.
Lemma lem3260042 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term56 _85366 t s u) : False.
Proof. exact (ex_elim (@lem3259380 _85366 t s u h1) (fun x : _85366 => fun h0 : term172 _85366 t s u x => @lem3260041 _85366 x t s u h0)). Qed.
Lemma lem3260043 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term56 _85366 t s u) : (term56 _85366 t s u) = False.
Proof. exact (prop_ext (fun h2 : term56 _85366 t s u => @lem3260042 _85366 t s u h1) (fun h2 : False => @lem3258965 _85366 t s u h1)). Qed.
Lemma lem3260044 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) (h1 : term56 _85366 t s u) : False.
Proof. exact (EQ_MP (@lem3260043 _85366 t s u h1) (@lem3258965 _85366 t s u h1)). Qed.
Lemma lem3260045 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : term55 _85366 t s u.
Proof. exact (fun h0 : term56 _85366 t s u => @lem3260044 _85366 t s u h0). Qed.
Lemma lem3260046 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) (u : _85366 -> Prop) : (term32 _85366 s t u) = (term40 _85366 t s u).
Proof. exact (EQ_MP (@lem3258964 _85366 t s u) (@lem3260045 _85366 t s u)). Qed.
Lemma lem3260051 {_85366 : Type'} (t : _85366 -> Prop) (s : _85366 -> Prop) : term42 _85366 t s.
Proof. exact (fun u : _85366 -> Prop => @lem3260046 _85366 t s u). Qed.
Lemma lem3260056 {_85366 : Type'} (s : _85366 -> Prop) : term44 _85366 s.
Proof. exact (fun t : _85366 -> Prop => @lem3260051 _85366 t s). Qed.
Lemma lem3260061 {_85366 : Type'} : term46 _85366.
Proof. exact (fun s : _85366 -> Prop => @lem3260056 _85366 s). Qed.
Lemma lem3260062 {_85366 : Type'} : term48 _85366.
Proof. exact (EQ_MP (@lem3258960 _85366) (@lem3260061 _85366)). Qed.
Lemma lem3260064 {_85366 : Type'} : term48 _85366.
Proof. exact (@lem3258822 _85366 (@lem3260062 _85366)). Qed.
Lemma lem3260065 {_85366 : Type'} (h1 : term49 _85366) : False.
Proof. exact (@lem3260064 _85366 (@lem3258806 _85366 h1)). Qed.
Lemma lem3260066 {_85366 : Type'} (h1 : term49 _85366) : (term49 _85366) = False.
Proof. exact (prop_ext (fun h2 : term49 _85366 => @lem3260065 _85366 h1) (fun h2 : False => @lem3258806 _85366 h1)). Qed.
Lemma lem3260067 {_85366 : Type'} (h1 : term49 _85366) : False.
Proof. exact (EQ_MP (@lem3260066 _85366 h1) (@lem3258806 _85366 h1)). Qed.
Lemma lem3260068 {_85366 : Type'} : term48 _85366.
Proof. exact (fun h0 : term49 _85366 => @lem3260067 _85366 h0). Qed.
Lemma lem3260069 {_85366 : Type'} : term46 _85366.
Proof. exact (EQ_MP (@lem3258805 _85366) (@lem3260068 _85366)). Qed.
Lemma lem3260070 {_85366 : Type'} : term20 _85366.
Proof. exact (EQ_MP (@lem3258801 _85366) (@lem3260069 _85366)). Qed.
Lemma lem3260071 {_85366 : Type'} : term19 _85366.
Proof. exact (EQ_MP (@lem3258659 _85366) (@lem3260070 _85366)). Qed.
