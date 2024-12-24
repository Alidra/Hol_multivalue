Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERS_ANTIMONO_GEN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3363605 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3363606 {_87451 : Type'} (s : _87451 -> Prop) (t : _87451 -> Prop) : (@SUBSET _87451 s t) = (term0 _87451 s t).
Proof. exact (@lem3363605 _87451 s t). Qed.
Lemma lem3363607 {_87451 : Type'} (x : _87451 -> Prop) (y : _87451 -> Prop) : (@SUBSET _87451 x y) = (term0 _87451 x y).
Proof. exact (@lem3363606 _87451 x y). Qed.
Lemma lem3363614 {_87451 : Type'} (x : _87451 -> Prop) (s : type686 _87451) : (term1 _87451 x s) = (term1 _87451 x s).
Proof. exact (eq_refl (term1 _87451 x s)). Qed.
Lemma lem3363615 {_87451 : Type'} (s : type686 _87451) (x : _87451 -> Prop) (y : _87451 -> Prop) : (term2 _87451 s x y) = (term3 _87451 s x y).
Proof. exact (MK_COMB (@lem3363614 _87451 x s) (@lem3363607 _87451 x y)). Qed.
Lemma lem3363618 {_87451 : Type'} (s : type686 _87451) (y : _87451 -> Prop) : (term4 _87451 s y) = (term5 _87451 s y).
Proof. exact (fun_ext (fun x : _87451 -> Prop => @lem3363615 _87451 s x y)). Qed.
Lemma lem3363619 {_87451 : Type'} : (@ex (_87451 -> Prop)) = (@ex (_87451 -> Prop)).
Proof. exact (eq_refl (@ex (_87451 -> Prop))). Qed.
Lemma lem3363620 {_87451 : Type'} (s : type686 _87451) (y : _87451 -> Prop) : (term6 _87451 s y) = (term7 _87451 s y).
Proof. exact (MK_COMB (@lem3363619 _87451) (@lem3363618 _87451 s y)). Qed.
Lemma lem3363625 {_87451 : Type'} (y : _87451 -> Prop) (t : type686 _87451) : (term8 _87451 y t) = (term8 _87451 y t).
Proof. exact (eq_refl (term8 _87451 y t)). Qed.
Lemma lem3363626 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term9 _87451 t s y) = (term10 _87451 t s y).
Proof. exact (MK_COMB (@lem3363625 _87451 y t) (@lem3363620 _87451 s y)). Qed.
Lemma lem3363629 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term11 _87451 t s) = (term12 _87451 t s).
Proof. exact (fun_ext (fun y : _87451 -> Prop => @lem3363626 _87451 t s y)). Qed.
Lemma lem3363630 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3363631 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term13 _87451 t s) = (term14 _87451 t s).
Proof. exact (MK_COMB (@lem3363630 _87451) (@lem3363629 _87451 t s)). Qed.
Lemma lem3363636 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3363637 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term15 _87451 t s) = (term16 _87451 t s).
Proof. exact (MK_COMB (@lem3363636) (@lem3363631 _87451 t s)). Qed.
Lemma lem3363639 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3363640 {_87451 : Type'} (s : _87451 -> Prop) (t : _87451 -> Prop) : (@SUBSET _87451 s t) = (term0 _87451 s t).
Proof. exact (@lem3363639 _87451 s t). Qed.
Lemma lem3363641 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) : (term17 _87451 s t) = (term18 _87451 s t).
Proof. exact (@lem3363640 _87451 (@INTERS _87451 s) (@INTERS _87451 t)). Qed.
Lemma lem3363648 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) : (term19 _87451 s t) = (term20 _87451 s t).
Proof. exact (MK_COMB (@lem3363637 _87451 t s) (@lem3363641 _87451 s t)). Qed.
Lemma lem3363651 {_87451 : Type'} (s : type686 _87451) : (term21 _87451 s) = (term22 _87451 s).
Proof. exact (fun_ext (fun t : type686 _87451 => @lem3363648 _87451 s t)). Qed.
Lemma lem3363652 {_87451 : Type'} : (@all ((_87451 -> Prop) -> Prop)) = (@all ((_87451 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87451 -> Prop) -> Prop))). Qed.
Lemma lem3363653 {_87451 : Type'} (s : type686 _87451) : (term23 _87451 s) = (term24 _87451 s).
Proof. exact (MK_COMB (@lem3363652 _87451) (@lem3363651 _87451 s)). Qed.
Lemma lem3363658 {_87451 : Type'} : (term25 _87451) = (term26 _87451).
Proof. exact (fun_ext (fun s : type686 _87451 => @lem3363653 _87451 s)). Qed.
Lemma lem3363659 {_87451 : Type'} : (@all ((_87451 -> Prop) -> Prop)) = (@all ((_87451 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87451 -> Prop) -> Prop))). Qed.
Lemma lem3363660 {_87451 : Type'} : (term27 _87451) = (term28 _87451).
Proof. exact (MK_COMB (@lem3363659 _87451) (@lem3363658 _87451)). Qed.
Lemma lem3363665 {_87451 : Type'} : (term28 _87451) = (term27 _87451).
Proof. exact (SYM (@lem3363660 _87451)). Qed.
Lemma lem3363683 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3363684 {_87451 : Type'} (P : type686 _87451) (x : _87451 -> Prop) : (@IN (_87451 -> Prop) x P) = (P x).
Proof. exact (@lem3363683 (_87451 -> Prop) P x). Qed.
Lemma lem3363685 {_87451 : Type'} (t : type686 _87451) (y : _87451 -> Prop) : (@IN (_87451 -> Prop) y t) = (t y).
Proof. exact (@lem3363684 _87451 t y). Qed.
Lemma lem3363686 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3363687 {_87451 : Type'} (t : type686 _87451) (y : _87451 -> Prop) : (term8 _87451 y t) = (term29 _87451 t y).
Proof. exact (MK_COMB (@lem3363686) (@lem3363685 _87451 t y)). Qed.
Lemma lem3363695 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3363696 {_87451 : Type'} (P : type686 _87451) (x : _87451 -> Prop) : (@IN (_87451 -> Prop) x P) = (P x).
Proof. exact (@lem3363695 (_87451 -> Prop) P x). Qed.
Lemma lem3363697 {_87451 : Type'} (s : type686 _87451) (x : _87451 -> Prop) : (@IN (_87451 -> Prop) x s) = (s x).
Proof. exact (@lem3363696 _87451 s x). Qed.
Lemma lem3363698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3363699 {_87451 : Type'} (s : type686 _87451) (x : _87451 -> Prop) : (term1 _87451 x s) = (term30 _87451 s x).
Proof. exact (MK_COMB (@lem3363698) (@lem3363697 _87451 s x)). Qed.
Lemma lem3363707 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3363708 {_87451 : Type'} (P : _87451 -> Prop) (x : _87451) : (@IN _87451 x P) = (P x).
Proof. exact (@lem3363707 _87451 P x). Qed.
Lemma lem3363709 {_87451 : Type'} (x : _87451 -> Prop) (x' : _87451) : (@IN _87451 x' x) = (x x').
Proof. exact (@lem3363708 _87451 x x'). Qed.
Lemma lem3363710 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3363711 {_87451 : Type'} (x : _87451 -> Prop) (x' : _87451) : (term31 _87451 x' x) = (term32 _87451 x x').
Proof. exact (MK_COMB (@lem3363710) (@lem3363709 _87451 x x')). Qed.
Lemma lem3363713 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3363714 {_87451 : Type'} (P : _87451 -> Prop) (x : _87451) : (@IN _87451 x P) = (P x).
Proof. exact (@lem3363713 _87451 P x). Qed.
Lemma lem3363715 {_87451 : Type'} (y : _87451 -> Prop) (x : _87451) : (@IN _87451 x y) = (y x).
Proof. exact (@lem3363714 _87451 y x). Qed.
Lemma lem3363716 {_87451 : Type'} (x : _87451 -> Prop) (y : _87451 -> Prop) (x' : _87451) : (term33 _87451 x x' y) = (term34 _87451 x y x').
Proof. exact (MK_COMB (@lem3363711 _87451 x x') (@lem3363715 _87451 y x')). Qed.
Lemma lem3363719 {_87451 : Type'} (x : _87451 -> Prop) (y : _87451 -> Prop) : (term35 _87451 x y) = (term36 _87451 x y).
Proof. exact (fun_ext (fun x' : _87451 => @lem3363716 _87451 x y x')). Qed.
Lemma lem3363720 {_87451 : Type'} : (@all _87451) = (@all _87451).
Proof. exact (eq_refl (@all _87451)). Qed.
Lemma lem3363721 {_87451 : Type'} (x : _87451 -> Prop) (y : _87451 -> Prop) : (term0 _87451 x y) = (term37 _87451 x y).
Proof. exact (MK_COMB (@lem3363720 _87451) (@lem3363719 _87451 x y)). Qed.
Lemma lem3363726 {_87451 : Type'} (s : type686 _87451) (x : _87451 -> Prop) (y : _87451 -> Prop) : (term3 _87451 s x y) = (term38 _87451 s x y).
Proof. exact (MK_COMB (@lem3363699 _87451 s x) (@lem3363721 _87451 x y)). Qed.
Lemma lem3363729 {_87451 : Type'} (s : type686 _87451) (y : _87451 -> Prop) : (term5 _87451 s y) = (term39 _87451 s y).
Proof. exact (fun_ext (fun x : _87451 -> Prop => @lem3363726 _87451 s x y)). Qed.
Lemma lem3363730 {_87451 : Type'} : (@ex (_87451 -> Prop)) = (@ex (_87451 -> Prop)).
Proof. exact (eq_refl (@ex (_87451 -> Prop))). Qed.
Lemma lem3363731 {_87451 : Type'} (s : type686 _87451) (y : _87451 -> Prop) : (term7 _87451 s y) = (term40 _87451 s y).
Proof. exact (MK_COMB (@lem3363730 _87451) (@lem3363729 _87451 s y)). Qed.
Lemma lem3363736 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term10 _87451 t s y) = (term41 _87451 t s y).
Proof. exact (MK_COMB (@lem3363687 _87451 t y) (@lem3363731 _87451 s y)). Qed.
Lemma lem3363739 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term12 _87451 t s) = (term42 _87451 t s).
Proof. exact (fun_ext (fun y : _87451 -> Prop => @lem3363736 _87451 t s y)). Qed.
Lemma lem3363740 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3363741 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term14 _87451 t s) = (term43 _87451 t s).
Proof. exact (MK_COMB (@lem3363740 _87451) (@lem3363739 _87451 t s)). Qed.
Lemma lem3363746 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3363747 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term16 _87451 t s) = (term44 _87451 t s).
Proof. exact (MK_COMB (@lem3363746) (@lem3363741 _87451 t s)). Qed.
Lemma lem3363755 {A : Type'} (s : type686 A) (x : A) : (term45 A x s) = (term46 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3363756 {_87451 : Type'} (s : type686 _87451) (x : _87451) : (term45 _87451 x s) = (term46 _87451 s x).
Proof. exact (@lem3363755 _87451 s x). Qed.
Lemma lem3363764 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3363765 {_87451 : Type'} (P : type686 _87451) (x : _87451 -> Prop) : (@IN (_87451 -> Prop) x P) = (P x).
Proof. exact (@lem3363764 (_87451 -> Prop) P x). Qed.
Lemma lem3363766 {_87451 : Type'} (s : type686 _87451) (t : _87451 -> Prop) : (@IN (_87451 -> Prop) t s) = (s t).
Proof. exact (@lem3363765 _87451 s t). Qed.
Lemma lem3363767 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3363768 {_87451 : Type'} (s : type686 _87451) (t : _87451 -> Prop) : (term8 _87451 t s) = (term29 _87451 s t).
Proof. exact (MK_COMB (@lem3363767) (@lem3363766 _87451 s t)). Qed.
Lemma lem3363770 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3363771 {_87451 : Type'} (P : _87451 -> Prop) (x : _87451) : (@IN _87451 x P) = (P x).
Proof. exact (@lem3363770 _87451 P x). Qed.
Lemma lem3363772 {_87451 : Type'} (t : _87451 -> Prop) (x : _87451) : (@IN _87451 x t) = (t x).
Proof. exact (@lem3363771 _87451 t x). Qed.
Lemma lem3363773 {_87451 : Type'} (s : type686 _87451) (t : _87451 -> Prop) (x : _87451) : (term47 _87451 s x t) = (term48 _87451 s t x).
Proof. exact (MK_COMB (@lem3363768 _87451 s t) (@lem3363772 _87451 t x)). Qed.
Lemma lem3363776 {_87451 : Type'} (s : type686 _87451) (x : _87451) : (term49 _87451 s x) = (term50 _87451 s x).
Proof. exact (fun_ext (fun t : _87451 -> Prop => @lem3363773 _87451 s t x)). Qed.
Lemma lem3363777 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3363778 {_87451 : Type'} (s : type686 _87451) (x : _87451) : (term46 _87451 s x) = (term51 _87451 s x).
Proof. exact (MK_COMB (@lem3363777 _87451) (@lem3363776 _87451 s x)). Qed.
Lemma lem3363783 {_87451 : Type'} (s : type686 _87451) (x : _87451) : (term45 _87451 x s) = (term51 _87451 s x).
Proof. exact (TRANS (@lem3363756 _87451 s x) (@lem3363778 _87451 s x)). Qed.
Lemma lem3363784 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3363785 {_87451 : Type'} (s : type686 _87451) (x : _87451) : (term52 _87451 x s) = (term53 _87451 s x).
Proof. exact (MK_COMB (@lem3363784) (@lem3363783 _87451 s x)). Qed.
Lemma lem3363787 {A : Type'} (s : type686 A) (x : A) : (term45 A x s) = (term46 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3363788 {_87451 : Type'} (s : type686 _87451) (x : _87451) : (term45 _87451 x s) = (term46 _87451 s x).
Proof. exact (@lem3363787 _87451 s x). Qed.
Lemma lem3363789 {_87451 : Type'} (t : type686 _87451) (x : _87451) : (term45 _87451 x t) = (term46 _87451 t x).
Proof. exact (@lem3363788 _87451 t x). Qed.
Lemma lem3363797 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3363798 {_87451 : Type'} (P : type686 _87451) (x : _87451 -> Prop) : (@IN (_87451 -> Prop) x P) = (P x).
Proof. exact (@lem3363797 (_87451 -> Prop) P x). Qed.
Lemma lem3363799 {_87451 : Type'} (t : type686 _87451) (t' : _87451 -> Prop) : (@IN (_87451 -> Prop) t' t) = (t t').
Proof. exact (@lem3363798 _87451 t t'). Qed.
Lemma lem3363800 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3363801 {_87451 : Type'} (t : type686 _87451) (t' : _87451 -> Prop) : (term8 _87451 t' t) = (term29 _87451 t t').
Proof. exact (MK_COMB (@lem3363800) (@lem3363799 _87451 t t')). Qed.
Lemma lem3363803 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3363804 {_87451 : Type'} (P : _87451 -> Prop) (x : _87451) : (@IN _87451 x P) = (P x).
Proof. exact (@lem3363803 _87451 P x). Qed.
Lemma lem3363805 {_87451 : Type'} (t : _87451 -> Prop) (x : _87451) : (@IN _87451 x t) = (t x).
Proof. exact (@lem3363804 _87451 t x). Qed.
Lemma lem3363806 {_87451 : Type'} (t : type686 _87451) (t' : _87451 -> Prop) (x : _87451) : (term47 _87451 t x t') = (term48 _87451 t t' x).
Proof. exact (MK_COMB (@lem3363801 _87451 t t') (@lem3363805 _87451 t' x)). Qed.
Lemma lem3363809 {_87451 : Type'} (t : type686 _87451) (x : _87451) : (term49 _87451 t x) = (term50 _87451 t x).
Proof. exact (fun_ext (fun t' : _87451 -> Prop => @lem3363806 _87451 t t' x)). Qed.
Lemma lem3363810 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3363811 {_87451 : Type'} (t : type686 _87451) (x : _87451) : (term46 _87451 t x) = (term51 _87451 t x).
Proof. exact (MK_COMB (@lem3363810 _87451) (@lem3363809 _87451 t x)). Qed.
Lemma lem3363816 {_87451 : Type'} (t : type686 _87451) (x : _87451) : (term45 _87451 x t) = (term51 _87451 t x).
Proof. exact (TRANS (@lem3363789 _87451 t x) (@lem3363811 _87451 t x)). Qed.
Lemma lem3363817 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) (x : _87451) : (term54 _87451 s x t) = (term55 _87451 s t x).
Proof. exact (MK_COMB (@lem3363785 _87451 s x) (@lem3363816 _87451 t x)). Qed.
Lemma lem3363820 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) : (term56 _87451 s t) = (term57 _87451 s t).
Proof. exact (fun_ext (fun x : _87451 => @lem3363817 _87451 s t x)). Qed.
Lemma lem3363821 {_87451 : Type'} : (@all _87451) = (@all _87451).
Proof. exact (eq_refl (@all _87451)). Qed.
Lemma lem3363822 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) : (term18 _87451 s t) = (term58 _87451 s t).
Proof. exact (MK_COMB (@lem3363821 _87451) (@lem3363820 _87451 s t)). Qed.
Lemma lem3363827 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) : (term20 _87451 s t) = (term59 _87451 s t).
Proof. exact (MK_COMB (@lem3363747 _87451 t s) (@lem3363822 _87451 s t)). Qed.
Lemma lem3363830 {_87451 : Type'} (s : type686 _87451) : (term22 _87451 s) = (term60 _87451 s).
Proof. exact (fun_ext (fun t : type686 _87451 => @lem3363827 _87451 s t)). Qed.
Lemma lem3363831 {_87451 : Type'} : (@all ((_87451 -> Prop) -> Prop)) = (@all ((_87451 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87451 -> Prop) -> Prop))). Qed.
Lemma lem3363832 {_87451 : Type'} (s : type686 _87451) : (term24 _87451 s) = (term61 _87451 s).
Proof. exact (MK_COMB (@lem3363831 _87451) (@lem3363830 _87451 s)). Qed.
Lemma lem3363837 {_87451 : Type'} : (term26 _87451) = (term62 _87451).
Proof. exact (fun_ext (fun s : type686 _87451 => @lem3363832 _87451 s)). Qed.
Lemma lem3363838 {_87451 : Type'} : (@all ((_87451 -> Prop) -> Prop)) = (@all ((_87451 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87451 -> Prop) -> Prop))). Qed.
Lemma lem3363839 {_87451 : Type'} : (term28 _87451) = (term63 _87451).
Proof. exact (MK_COMB (@lem3363838 _87451) (@lem3363837 _87451)). Qed.
Lemma lem3363844 {_87451 : Type'} : (term63 _87451) = (term28 _87451).
Proof. exact (SYM (@lem3363839 _87451)). Qed.
Lemma lem3363846 (p : Prop) : p = (term64 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3363847 {_87451 : Type'} : (term63 _87451) = (term65 _87451).
Proof. exact (@lem3363846 (term63 _87451)). Qed.
Lemma lem3363848 {_87451 : Type'} : (term65 _87451) = (term63 _87451).
Proof. exact (SYM (@lem3363847 _87451)). Qed.
Lemma lem3363849 {_87451 : Type'} (h1 : term66 _87451) : term66 _87451.
Proof. exact (h1). Qed.
Lemma lem3363852 {_87451 : Type'} (h1 : term65 _87451) : term65 _87451.
Proof. exact (h1). Qed.
Lemma lem3363853 {_87451 : Type'} : term67 _87451.
Proof. exact (fun h0 : term65 _87451 => @lem3363852 _87451 h0). Qed.
Lemma lem3363854 {_87451 : Type'} (h1 : term67 _87451) : term67 _87451.
Proof. exact (h1). Qed.
Lemma lem3363855 {_87451 : Type'} (h1 : term65 _87451) : term65 _87451.
Proof. exact (h1). Qed.
Lemma lem3363856 {_87451 : Type'} (h1 : term65 _87451) (h2 : term67 _87451) : term65 _87451.
Proof. exact (@lem3363854 _87451 h2 (@lem3363855 _87451 h1)). Qed.
Lemma lem3363857 {_87451 : Type'} (h1 : term65 _87451) : term68 _87451.
Proof. exact (fun h0 : term67 _87451 => @lem3363856 _87451 h1 h0). Qed.
Lemma lem3363858 {_87451 : Type'} (h1 : term67 _87451) : term67 _87451.
Proof. exact (h1). Qed.
Lemma lem3363859 {_87451 : Type'} (h1 : term65 _87451) (h2 : term67 _87451) : term65 _87451.
Proof. exact (@lem3363857 _87451 h1 (@lem3363858 _87451 h2)). Qed.
Lemma lem3363860 {_87451 : Type'} (h1 : term67 _87451) : term67 _87451.
Proof. exact (fun h0 : term65 _87451 => @lem3363859 _87451 h0 h1). Qed.
Lemma lem3363861 {_87451 : Type'} : term69 _87451.
Proof. exact (fun h0 : term67 _87451 => @lem3363860 _87451 h0). Qed.
Lemma lem3363864 {_87451 : Type'} : term67 _87451.
Proof. exact (@lem3363861 _87451 (@lem3363853 _87451)). Qed.
Lemma lem3363865 {_87451 : Type'} : term67 _87451.
Proof. exact (@lem3363864 _87451). Qed.
Lemma lem3363867 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3363868 {_87451 : Type'} : (term65 _87451) = (term70 _87451).
Proof. exact (@lem3363867 (term66 _87451)). Qed.
Lemma lem3363870 (t : Prop) : (term71 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3363871 {_87451 : Type'} : (term70 _87451) = (term63 _87451).
Proof. exact (@lem3363870 (term63 _87451)). Qed.
Lemma lem3363946 {_87451 : Type'} : (term65 _87451) = (term63 _87451).
Proof. exact (TRANS (@lem3363868 _87451) (@lem3363871 _87451)). Qed.
Lemma lem3363951 {_87451 : Type'} (t : type686 _87451) (t' : _87451 -> Prop) (x : _87451) : (term48 _87451 t t' x) = (term48 _87451 t t' x).
Proof. exact (eq_refl (term48 _87451 t t' x)). Qed.
Lemma lem3363952 {_87451 : Type'} (t : type686 _87451) (x : _87451) : (term50 _87451 t x) = (term50 _87451 t x).
Proof. exact (fun_ext (fun t' : _87451 -> Prop => @lem3363951 _87451 t t' x)). Qed.
Lemma lem3363953 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3363954 {_87451 : Type'} (t : type686 _87451) (x : _87451) : (term51 _87451 t x) = (term51 _87451 t x).
Proof. exact (MK_COMB (@lem3363953 _87451) (@lem3363952 _87451 t x)). Qed.
Lemma lem3363959 {_87451 : Type'} (s : type686 _87451) (t : _87451 -> Prop) (x : _87451) : (term48 _87451 s t x) = (term48 _87451 s t x).
Proof. exact (eq_refl (term48 _87451 s t x)). Qed.
Lemma lem3363960 {_87451 : Type'} (s : type686 _87451) (x : _87451) : (term50 _87451 s x) = (term50 _87451 s x).
Proof. exact (fun_ext (fun t : _87451 -> Prop => @lem3363959 _87451 s t x)). Qed.
Lemma lem3363961 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3363962 {_87451 : Type'} (s : type686 _87451) (x : _87451) : (term51 _87451 s x) = (term51 _87451 s x).
Proof. exact (MK_COMB (@lem3363961 _87451) (@lem3363960 _87451 s x)). Qed.
Lemma lem3363963 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3363964 {_87451 : Type'} (s : type686 _87451) (x : _87451) : (term53 _87451 s x) = (term53 _87451 s x).
Proof. exact (MK_COMB (@lem3363963) (@lem3363962 _87451 s x)). Qed.
Lemma lem3363965 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) (x : _87451) : (term55 _87451 s t x) = (term55 _87451 s t x).
Proof. exact (MK_COMB (@lem3363964 _87451 s x) (@lem3363954 _87451 t x)). Qed.
Lemma lem3363966 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) : (term57 _87451 s t) = (term57 _87451 s t).
Proof. exact (fun_ext (fun x : _87451 => @lem3363965 _87451 s t x)). Qed.
Lemma lem3363967 {_87451 : Type'} : (@all _87451) = (@all _87451).
Proof. exact (eq_refl (@all _87451)). Qed.
Lemma lem3363968 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) : (term58 _87451 s t) = (term58 _87451 s t).
Proof. exact (MK_COMB (@lem3363967 _87451) (@lem3363966 _87451 s t)). Qed.
Lemma lem3363973 {_87451 : Type'} (x : _87451 -> Prop) (y : _87451 -> Prop) (x' : _87451) : (term34 _87451 x y x') = (term34 _87451 x y x').
Proof. exact (eq_refl (term34 _87451 x y x')). Qed.
Lemma lem3363974 {_87451 : Type'} (x : _87451 -> Prop) (y : _87451 -> Prop) : (term36 _87451 x y) = (term36 _87451 x y).
Proof. exact (fun_ext (fun x' : _87451 => @lem3363973 _87451 x y x')). Qed.
Lemma lem3363975 {_87451 : Type'} : (@all _87451) = (@all _87451).
Proof. exact (eq_refl (@all _87451)). Qed.
Lemma lem3363976 {_87451 : Type'} (x : _87451 -> Prop) (y : _87451 -> Prop) : (term37 _87451 x y) = (term37 _87451 x y).
Proof. exact (MK_COMB (@lem3363975 _87451) (@lem3363974 _87451 x y)). Qed.
Lemma lem3363979 {_87451 : Type'} (s : type686 _87451) (x : _87451 -> Prop) : (term30 _87451 s x) = (term30 _87451 s x).
Proof. exact (eq_refl (term30 _87451 s x)). Qed.
Lemma lem3363980 {_87451 : Type'} (s : type686 _87451) (x : _87451 -> Prop) (y : _87451 -> Prop) : (term38 _87451 s x y) = (term38 _87451 s x y).
Proof. exact (MK_COMB (@lem3363979 _87451 s x) (@lem3363976 _87451 x y)). Qed.
Lemma lem3363981 {_87451 : Type'} (s : type686 _87451) (y : _87451 -> Prop) : (term39 _87451 s y) = (term39 _87451 s y).
Proof. exact (fun_ext (fun x : _87451 -> Prop => @lem3363980 _87451 s x y)). Qed.
Lemma lem3363982 {_87451 : Type'} : (@ex (_87451 -> Prop)) = (@ex (_87451 -> Prop)).
Proof. exact (eq_refl (@ex (_87451 -> Prop))). Qed.
Lemma lem3363983 {_87451 : Type'} (s : type686 _87451) (y : _87451 -> Prop) : (term40 _87451 s y) = (term40 _87451 s y).
Proof. exact (MK_COMB (@lem3363982 _87451) (@lem3363981 _87451 s y)). Qed.
Lemma lem3363986 {_87451 : Type'} (t : type686 _87451) (y : _87451 -> Prop) : (term29 _87451 t y) = (term29 _87451 t y).
Proof. exact (eq_refl (term29 _87451 t y)). Qed.
Lemma lem3363987 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term41 _87451 t s y) = (term41 _87451 t s y).
Proof. exact (MK_COMB (@lem3363986 _87451 t y) (@lem3363983 _87451 s y)). Qed.
Lemma lem3363988 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term42 _87451 t s) = (term42 _87451 t s).
Proof. exact (fun_ext (fun y : _87451 -> Prop => @lem3363987 _87451 t s y)). Qed.
Lemma lem3363989 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3363990 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term43 _87451 t s) = (term43 _87451 t s).
Proof. exact (MK_COMB (@lem3363989 _87451) (@lem3363988 _87451 t s)). Qed.
Lemma lem3363991 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3363992 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term44 _87451 t s) = (term44 _87451 t s).
Proof. exact (MK_COMB (@lem3363991) (@lem3363990 _87451 t s)). Qed.
Lemma lem3363993 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) : (term59 _87451 s t) = (term59 _87451 s t).
Proof. exact (MK_COMB (@lem3363992 _87451 t s) (@lem3363968 _87451 s t)). Qed.
Lemma lem3363994 {_87451 : Type'} (s : type686 _87451) : (term60 _87451 s) = (term60 _87451 s).
Proof. exact (fun_ext (fun t : type686 _87451 => @lem3363993 _87451 s t)). Qed.
Lemma lem3363995 {_87451 : Type'} : (@all ((_87451 -> Prop) -> Prop)) = (@all ((_87451 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87451 -> Prop) -> Prop))). Qed.
Lemma lem3363996 {_87451 : Type'} (s : type686 _87451) : (term61 _87451 s) = (term61 _87451 s).
Proof. exact (MK_COMB (@lem3363995 _87451) (@lem3363994 _87451 s)). Qed.
Lemma lem3363997 {_87451 : Type'} : (term62 _87451) = (term62 _87451).
Proof. exact (fun_ext (fun s : type686 _87451 => @lem3363996 _87451 s)). Qed.
Lemma lem3363998 {_87451 : Type'} : (@all ((_87451 -> Prop) -> Prop)) = (@all ((_87451 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87451 -> Prop) -> Prop))). Qed.
Lemma lem3363999 {_87451 : Type'} : (term63 _87451) = (term63 _87451).
Proof. exact (MK_COMB (@lem3363998 _87451) (@lem3363997 _87451)). Qed.
Lemma lem3364064 {_87451 : Type'} : (term65 _87451) = (term63 _87451).
Proof. exact (TRANS (@lem3363946 _87451) (@lem3363999 _87451)). Qed.
Lemma lem3364065 {_87451 : Type'} : (term63 _87451) = (term65 _87451).
Proof. exact (SYM (@lem3364064 _87451)). Qed.
Lemma lem3364066 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (h1 : term43 _87451 t s) : term43 _87451 t s.
Proof. exact (h1). Qed.
Lemma lem3364067 {_87451 : Type'} (s : type686 _87451) (x : _87451) (h1 : term51 _87451 s x) : term51 _87451 s x.
Proof. exact (h1). Qed.
Lemma lem3364070 (p : Prop) : p = (term64 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3364071 {_87451 : Type'} (t' : _87451 -> Prop) (x : _87451) : (t' x) = (term72 _87451 t' x).
Proof. exact (@lem3364070 (t' x)). Qed.
Lemma lem3364072 {_87451 : Type'} (t' : _87451 -> Prop) (x : _87451) : (term72 _87451 t' x) = (t' x).
Proof. exact (SYM (@lem3364071 _87451 t' x)). Qed.
Lemma lem3364073 {_87451 : Type'} (t' : _87451 -> Prop) (x : _87451) (h1 : term73 _87451 t' x) : term73 _87451 t' x.
Proof. exact (h1). Qed.
Lemma lem3364082 {_87451 : Type'} (x : _87451 -> Prop) (y : _87451 -> Prop) (x' : _87451) : (term34 _87451 x y x') = (term74 _87451 x y x').
Proof. exact (@lem17265 (x x') (y x')). Qed.
Lemma lem3364083 {_87451 : Type'} (x : _87451 -> Prop) (y : _87451 -> Prop) : (term36 _87451 x y) = (term75 _87451 x y).
Proof. exact (fun_ext (fun x' : _87451 => @lem3364082 _87451 x y x')). Qed.
Lemma lem3364084 {_87451 : Type'} : (@all _87451) = (@all _87451).
Proof. exact (eq_refl (@all _87451)). Qed.
Lemma lem3364085 {_87451 : Type'} (x : _87451 -> Prop) (y : _87451 -> Prop) : (term37 _87451 x y) = (term76 _87451 x y).
Proof. exact (MK_COMB (@lem3364084 _87451) (@lem3364083 _87451 x y)). Qed.
Lemma lem3364087 {_87451 : Type'} (s : type686 _87451) (x : _87451 -> Prop) : (term30 _87451 s x) = (term30 _87451 s x).
Proof. exact (eq_refl (term30 _87451 s x)). Qed.
Lemma lem3364088 {_87451 : Type'} (s : type686 _87451) (x : _87451 -> Prop) (y : _87451 -> Prop) : (term38 _87451 s x y) = (term77 _87451 s x y).
Proof. exact (MK_COMB (@lem3364087 _87451 s x) (@lem3364085 _87451 x y)). Qed.
Lemma lem3364089 {_87451 : Type'} (s : type686 _87451) (y : _87451 -> Prop) : (term39 _87451 s y) = (term78 _87451 s y).
Proof. exact (fun_ext (fun x : _87451 -> Prop => @lem3364088 _87451 s x y)). Qed.
Lemma lem3364090 {_87451 : Type'} : (@ex (_87451 -> Prop)) = (@ex (_87451 -> Prop)).
Proof. exact (eq_refl (@ex (_87451 -> Prop))). Qed.
Lemma lem3364091 {_87451 : Type'} (s : type686 _87451) (y : _87451 -> Prop) : (term40 _87451 s y) = (term79 _87451 s y).
Proof. exact (MK_COMB (@lem3364090 _87451) (@lem3364089 _87451 s y)). Qed.
Lemma lem3364093 {_87451 : Type'} (t : type686 _87451) (y : _87451 -> Prop) : (term80 _87451 t y) = (term80 _87451 t y).
Proof. exact (eq_refl (term80 _87451 t y)). Qed.
Lemma lem3364094 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term81 _87451 t s y) = (term82 _87451 t s y).
Proof. exact (MK_COMB (@lem3364093 _87451 t y) (@lem3364091 _87451 s y)). Qed.
Lemma lem3364095 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term41 _87451 t s y) = (term81 _87451 t s y).
Proof. exact (@lem17265 (t y) (term40 _87451 s y)). Qed.
Lemma lem3364096 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term41 _87451 t s y) = (term82 _87451 t s y).
Proof. exact (TRANS (@lem3364095 _87451 t s y) (@lem3364094 _87451 t s y)). Qed.
Lemma lem3364097 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term42 _87451 t s) = (term83 _87451 t s).
Proof. exact (fun_ext (fun y : _87451 -> Prop => @lem3364096 _87451 t s y)). Qed.
Lemma lem3364098 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3364099 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term43 _87451 t s) = (term84 _87451 t s).
Proof. exact (MK_COMB (@lem3364098 _87451) (@lem3364097 _87451 t s)). Qed.
Lemma lem3364210 {A : Type'} (P : Prop) (Q : A -> Prop) : (term85 A P Q) = (term86 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3364211 {_87451 : Type'} (P : Prop) (Q : type686 _87451) : (term87 _87451 P Q) = (term88 _87451 P Q).
Proof. exact (@lem3364210 (_87451 -> Prop) P Q). Qed.
Lemma lem3364212 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term89 _87451 t s y) = (term90 _87451 t s y).
Proof. exact (@lem3364211 _87451 (term91 _87451 t y) (term78 _87451 s y)). Qed.
Lemma lem3364213 {_87451 : Type'} (s : type686 _87451) (x : _87451 -> Prop) (y : _87451 -> Prop) : (term92 _87451 s y x) = (term77 _87451 s x y).
Proof. exact (eq_refl (term92 _87451 s y x)). Qed.
Lemma lem3364214 {_87451 : Type'} (s : type686 _87451) (y : _87451 -> Prop) : (term93 _87451 s y) = (term78 _87451 s y).
Proof. exact (fun_ext (fun x : _87451 -> Prop => @lem3364213 _87451 s x y)). Qed.
Lemma lem3364215 {_87451 : Type'} : (@ex (_87451 -> Prop)) = (@ex (_87451 -> Prop)).
Proof. exact (eq_refl (@ex (_87451 -> Prop))). Qed.
Lemma lem3364216 {_87451 : Type'} (s : type686 _87451) (y : _87451 -> Prop) : (term94 _87451 s y) = (term79 _87451 s y).
Proof. exact (MK_COMB (@lem3364215 _87451) (@lem3364214 _87451 s y)). Qed.
Lemma lem3364217 {_87451 : Type'} (t : type686 _87451) (y : _87451 -> Prop) : (term80 _87451 t y) = (term80 _87451 t y).
Proof. exact (eq_refl (term80 _87451 t y)). Qed.
Lemma lem3364218 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term89 _87451 t s y) = (term82 _87451 t s y).
Proof. exact (MK_COMB (@lem3364217 _87451 t y) (@lem3364216 _87451 s y)). Qed.
Lemma lem3364219 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3364220 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term95 _87451 t s y) = (term96 _87451 t s y).
Proof. exact (MK_COMB (@lem3364219) (@lem3364218 _87451 t s y)). Qed.
Lemma lem3364221 {_87451 : Type'} (s : type686 _87451) (x : _87451 -> Prop) (y : _87451 -> Prop) : (term92 _87451 s y x) = (term77 _87451 s x y).
Proof. exact (eq_refl (term92 _87451 s y x)). Qed.
Lemma lem3364222 {_87451 : Type'} (t : type686 _87451) (y : _87451 -> Prop) : (term80 _87451 t y) = (term80 _87451 t y).
Proof. exact (eq_refl (term80 _87451 t y)). Qed.
Lemma lem3364223 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x : _87451 -> Prop) (y : _87451 -> Prop) : (term97 _87451 t s y x) = (term98 _87451 t s x y).
Proof. exact (MK_COMB (@lem3364222 _87451 t y) (@lem3364221 _87451 s x y)). Qed.
Lemma lem3364224 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term99 _87451 t s y) = (term100 _87451 t s y).
Proof. exact (fun_ext (fun x : _87451 -> Prop => @lem3364223 _87451 t s x y)). Qed.
Lemma lem3364225 {_87451 : Type'} : (@ex (_87451 -> Prop)) = (@ex (_87451 -> Prop)).
Proof. exact (eq_refl (@ex (_87451 -> Prop))). Qed.
Lemma lem3364226 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term90 _87451 t s y) = (term101 _87451 t s y).
Proof. exact (MK_COMB (@lem3364225 _87451) (@lem3364224 _87451 t s y)). Qed.
Lemma lem3364227 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : ((term89 _87451 t s y) = (term90 _87451 t s y)) = ((term82 _87451 t s y) = (term101 _87451 t s y)).
Proof. exact (MK_COMB (@lem3364220 _87451 t s y) (@lem3364226 _87451 t s y)). Qed.
Lemma lem3364228 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term82 _87451 t s y) = (term101 _87451 t s y).
Proof. exact (EQ_MP (@lem3364227 _87451 t s y) (@lem3364212 _87451 t s y)). Qed.
Lemma lem3364229 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term83 _87451 t s) = (term102 _87451 t s).
Proof. exact (fun_ext (fun y : _87451 -> Prop => @lem3364228 _87451 t s y)). Qed.
Lemma lem3364230 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3364231 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term84 _87451 t s) = (term103 _87451 t s).
Proof. exact (MK_COMB (@lem3364230 _87451) (@lem3364229 _87451 t s)). Qed.
Lemma lem3364233 {A B : Type'} (P : type1413 A B) : (term104 A B P) = (term105 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3364234 {_87451 : Type'} (P : type639 _87451) : (term106 _87451 P) = (term107 _87451 P).
Proof. exact (@lem3364233 (_87451 -> Prop) (_87451 -> Prop) P). Qed.
Lemma lem3364235 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term108 _87451 t s) = (term109 _87451 t s).
Proof. exact (@lem3364234 _87451 (term110 _87451 t s)). Qed.
Lemma lem3364236 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term111 _87451 t s y) = (term100 _87451 t s y).
Proof. exact (eq_refl (term111 _87451 t s y)). Qed.
Lemma lem3364237 {_87451 : Type'} (x : _87451 -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3364238 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) (x : _87451 -> Prop) : (term112 _87451 t s y x) = (term113 _87451 t s y x).
Proof. exact (MK_COMB (@lem3364236 _87451 t s y) (@lem3364237 _87451 x)). Qed.
Lemma lem3364239 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x : _87451 -> Prop) (y : _87451 -> Prop) : (term113 _87451 t s y x) = (term98 _87451 t s x y).
Proof. exact (eq_refl (term113 _87451 t s y x)). Qed.
Lemma lem3364240 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x : _87451 -> Prop) (y : _87451 -> Prop) : (term112 _87451 t s y x) = (term98 _87451 t s x y).
Proof. exact (TRANS (@lem3364238 _87451 t s y x) (@lem3364239 _87451 t s x y)). Qed.
Lemma lem3364241 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term114 _87451 t s y) = (term100 _87451 t s y).
Proof. exact (fun_ext (fun x : _87451 -> Prop => @lem3364240 _87451 t s x y)). Qed.
Lemma lem3364242 {_87451 : Type'} : (@ex (_87451 -> Prop)) = (@ex (_87451 -> Prop)).
Proof. exact (eq_refl (@ex (_87451 -> Prop))). Qed.
Lemma lem3364243 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term115 _87451 t s y) = (term101 _87451 t s y).
Proof. exact (MK_COMB (@lem3364242 _87451) (@lem3364241 _87451 t s y)). Qed.
Lemma lem3364244 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term116 _87451 t s) = (term102 _87451 t s).
Proof. exact (fun_ext (fun y : _87451 -> Prop => @lem3364243 _87451 t s y)). Qed.
Lemma lem3364245 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3364246 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term108 _87451 t s) = (term103 _87451 t s).
Proof. exact (MK_COMB (@lem3364245 _87451) (@lem3364244 _87451 t s)). Qed.
Lemma lem3364247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3364248 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term117 _87451 t s) = (term118 _87451 t s).
Proof. exact (MK_COMB (@lem3364247) (@lem3364246 _87451 t s)). Qed.
Lemma lem3364249 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (y : _87451 -> Prop) : (term111 _87451 t s y) = (term100 _87451 t s y).
Proof. exact (eq_refl (term111 _87451 t s y)). Qed.
Lemma lem3364250 {_87451 : Type'} (x : type672 _87451) (y : _87451 -> Prop) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem3364251 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x : type672 _87451) (y : _87451 -> Prop) : (term119 _87451 t s x y) = (term120 _87451 t s x y).
Proof. exact (MK_COMB (@lem3364249 _87451 t s y) (@lem3364250 _87451 x y)). Qed.
Lemma lem3364252 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x : type672 _87451) (y : _87451 -> Prop) : (term120 _87451 t s x y) = (term121 _87451 t s x y).
Proof. exact (eq_refl (term120 _87451 t s x y)). Qed.
Lemma lem3364253 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x : type672 _87451) (y : _87451 -> Prop) : (term119 _87451 t s x y) = (term121 _87451 t s x y).
Proof. exact (TRANS (@lem3364251 _87451 t s x y) (@lem3364252 _87451 t s x y)). Qed.
Lemma lem3364254 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x : type672 _87451) : (term122 _87451 t s x) = (term123 _87451 t s x).
Proof. exact (fun_ext (fun y : _87451 -> Prop => @lem3364253 _87451 t s x y)). Qed.
Lemma lem3364255 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3364256 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x : type672 _87451) : (term124 _87451 t s x) = (term125 _87451 t s x).
Proof. exact (MK_COMB (@lem3364255 _87451) (@lem3364254 _87451 t s x)). Qed.
Lemma lem3364257 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term126 _87451 t s) = (term127 _87451 t s).
Proof. exact (fun_ext (fun x : type672 _87451 => @lem3364256 _87451 t s x)). Qed.
Lemma lem3364258 {_87451 : Type'} : (@ex ((_87451 -> Prop) -> _87451 -> Prop)) = (@ex ((_87451 -> Prop) -> _87451 -> Prop)).
Proof. exact (eq_refl (@ex ((_87451 -> Prop) -> _87451 -> Prop))). Qed.
Lemma lem3364259 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term109 _87451 t s) = (term128 _87451 t s).
Proof. exact (MK_COMB (@lem3364258 _87451) (@lem3364257 _87451 t s)). Qed.
Lemma lem3364260 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : ((term108 _87451 t s) = (term109 _87451 t s)) = ((term103 _87451 t s) = (term128 _87451 t s)).
Proof. exact (MK_COMB (@lem3364248 _87451 t s) (@lem3364259 _87451 t s)). Qed.
Lemma lem3364261 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term103 _87451 t s) = (term128 _87451 t s).
Proof. exact (EQ_MP (@lem3364260 _87451 t s) (@lem3364235 _87451 t s)). Qed.
Lemma lem3364263 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term84 _87451 t s) = (term128 _87451 t s).
Proof. exact (TRANS (@lem3364231 _87451 t s) (@lem3364261 _87451 t s)). Qed.
Lemma lem3364264 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) : (term43 _87451 t s) = (term128 _87451 t s).
Proof. exact (TRANS (@lem3364099 _87451 t s) (@lem3364263 _87451 t s)). Qed.
Lemma lem3364265 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (h1 : term43 _87451 t s) : term128 _87451 t s.
Proof. exact (EQ_MP (@lem3364264 _87451 t s) (@lem3364066 _87451 t s h1)). Qed.
Lemma lem3364272 {_87451 : Type'} (s : type686 _87451) (t : _87451 -> Prop) (x : _87451) : (term48 _87451 s t x) = (term129 _87451 s t x).
Proof. exact (@lem17265 (s t) (t x)). Qed.
Lemma lem3364273 {_87451 : Type'} (s : type686 _87451) (x : _87451) : (term50 _87451 s x) = (term130 _87451 s x).
Proof. exact (fun_ext (fun t : _87451 -> Prop => @lem3364272 _87451 s t x)). Qed.
Lemma lem3364274 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3364327 {_87451 : Type'} (s : type686 _87451) (x : _87451) : (term51 _87451 s x) = (term131 _87451 s x).
Proof. exact (MK_COMB (@lem3364274 _87451) (@lem3364273 _87451 s x)). Qed.
Lemma lem3364328 {_87451 : Type'} (s : type686 _87451) (x : _87451) (h1 : term51 _87451 s x) : term131 _87451 s x.
Proof. exact (EQ_MP (@lem3364327 _87451 s x) (@lem3364067 _87451 s x h1)). Qed.
Lemma lem3364334 {_87451 : Type'} (t : type686 _87451) (t' : _87451 -> Prop) (h1 : t t') : t t'.
Proof. exact (h1). Qed.
Lemma lem3364340 {_87451 : Type'} (t' : _87451 -> Prop) (x : _87451) (h1 : term73 _87451 t' x) : term73 _87451 t' x.
Proof. exact (h1). Qed.
Lemma lem3364341 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term125 _87451 t s x'.
Proof. exact (h1). Qed.
Lemma lem3364346 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3364347 {_87451 : Type'} (f : _87451 -> Prop) (x : _87451) : (f x) = (@I (_87451 -> Prop) f x).
Proof. exact (@lem3364346 _87451 Prop f x). Qed.
Lemma lem3364349 {_87451 : Type'} (t : _87451 -> Prop) (x : _87451) : (t x) = (@I (_87451 -> Prop) t x).
Proof. exact (@lem3364347 _87451 t x). Qed.
Lemma lem3364350 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3364355 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3364356 {_87451 : Type'} (f : type686 _87451) (x : _87451 -> Prop) : (f x) = (@I ((_87451 -> Prop) -> Prop) f x).
Proof. exact (@lem3364355 (_87451 -> Prop) Prop f x). Qed.
Lemma lem3364358 {_87451 : Type'} (s : type686 _87451) (t : _87451 -> Prop) : (s t) = (@I ((_87451 -> Prop) -> Prop) s t).
Proof. exact (@lem3364356 _87451 s t). Qed.
Lemma lem3364359 {_87451 : Type'} (s : type686 _87451) (t : _87451 -> Prop) : (term91 _87451 s t) = (term132 _87451 s t).
Proof. exact (MK_COMB (@lem3364350) (@lem3364358 _87451 s t)). Qed.
Lemma lem3364360 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3364361 {_87451 : Type'} (s : type686 _87451) (t : _87451 -> Prop) : (term80 _87451 s t) = (term133 _87451 s t).
Proof. exact (MK_COMB (@lem3364360) (@lem3364359 _87451 s t)). Qed.
Lemma lem3364362 {_87451 : Type'} (s : type686 _87451) (t : _87451 -> Prop) (x : _87451) : (term129 _87451 s t x) = (term134 _87451 s t x).
Proof. exact (MK_COMB (@lem3364361 _87451 s t) (@lem3364349 _87451 t x)). Qed.
Lemma lem3364363 {_87451 : Type'} (s : type686 _87451) (x : _87451) : (term130 _87451 s x) = (term135 _87451 s x).
Proof. exact (fun_ext (fun t : _87451 -> Prop => @lem3364362 _87451 s t x)). Qed.
Lemma lem3364364 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3364365 {_87451 : Type'} (s : type686 _87451) (x : _87451) : (term131 _87451 s x) = (term136 _87451 s x).
Proof. exact (MK_COMB (@lem3364364 _87451) (@lem3364363 _87451 s x)). Qed.
Lemma lem3364366 {_87451 : Type'} (s : type686 _87451) (x : _87451) (h1 : term51 _87451 s x) : term136 _87451 s x.
Proof. exact (EQ_MP (@lem3364365 _87451 s x) (@lem3364328 _87451 s x h1)). Qed.
Lemma lem3364371 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3364372 {_87451 : Type'} (f : type686 _87451) (x : _87451 -> Prop) : (f x) = (@I ((_87451 -> Prop) -> Prop) f x).
Proof. exact (@lem3364371 (_87451 -> Prop) Prop f x). Qed.
Lemma lem3364374 {_87451 : Type'} (t : type686 _87451) (t' : _87451 -> Prop) : (t t') = (@I ((_87451 -> Prop) -> Prop) t t').
Proof. exact (@lem3364372 _87451 t t'). Qed.
Lemma lem3364376 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3364381 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3364382 {_87451 : Type'} (f : _87451 -> Prop) (x : _87451) : (f x) = (@I (_87451 -> Prop) f x).
Proof. exact (@lem3364381 _87451 Prop f x). Qed.
Lemma lem3364384 {_87451 : Type'} (t' : _87451 -> Prop) (x : _87451) : (t' x) = (@I (_87451 -> Prop) t' x).
Proof. exact (@lem3364382 _87451 t' x). Qed.
Lemma lem3364385 {_87451 : Type'} (t' : _87451 -> Prop) (x : _87451) : (term73 _87451 t' x) = (term137 _87451 t' x).
Proof. exact (MK_COMB (@lem3364376) (@lem3364384 _87451 t' x)). Qed.
Lemma lem3364391 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3364392 {_87451 : Type'} (f : _87451 -> Prop) (x : _87451) : (f x) = (@I (_87451 -> Prop) f x).
Proof. exact (@lem3364391 _87451 Prop f x). Qed.
Lemma lem3364394 {_87451 : Type'} (y : _87451 -> Prop) (x : _87451) : (y x) = (@I (_87451 -> Prop) y x).
Proof. exact (@lem3364392 _87451 y x). Qed.
Lemma lem3364395 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3364402 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3364403 {_87451 : Type'} (f : type672 _87451) (x : _87451 -> Prop) : (f x) = (@I ((_87451 -> Prop) -> _87451 -> Prop) f x).
Proof. exact (@lem3364402 (_87451 -> Prop) (_87451 -> Prop) f x). Qed.
Lemma lem3364404 {_87451 : Type'} (x' : type672 _87451) (y : _87451 -> Prop) : (x' y) = (@I ((_87451 -> Prop) -> _87451 -> Prop) x' y).
Proof. exact (@lem3364403 _87451 x' y). Qed.
Lemma lem3364405 {_87451 : Type'} (x : _87451) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3364406 {_87451 : Type'} (x' : type672 _87451) (y : _87451 -> Prop) (x : _87451) : (x' y x) = (@I ((_87451 -> Prop) -> _87451 -> Prop) x' y x).
Proof. exact (MK_COMB (@lem3364404 _87451 x' y) (@lem3364405 _87451 x)). Qed.
Lemma lem3364408 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3364409 {_87451 : Type'} (f : _87451 -> Prop) (x : _87451) : (f x) = (@I (_87451 -> Prop) f x).
Proof. exact (@lem3364408 _87451 Prop f x). Qed.
Lemma lem3364410 {_87451 : Type'} (x' : type672 _87451) (y : _87451 -> Prop) (x : _87451) : (@I ((_87451 -> Prop) -> _87451 -> Prop) x' y x) = (term138 _87451 x' y x).
Proof. exact (@lem3364409 _87451 (@I ((_87451 -> Prop) -> _87451 -> Prop) x' y) x). Qed.
Lemma lem3364412 {_87451 : Type'} (x' : type672 _87451) (y : _87451 -> Prop) (x : _87451) : (x' y x) = (term138 _87451 x' y x).
Proof. exact (TRANS (@lem3364406 _87451 x' y x) (@lem3364410 _87451 x' y x)). Qed.
Lemma lem3364413 {_87451 : Type'} (x' : type672 _87451) (y : _87451 -> Prop) (x : _87451) : (term139 _87451 x' y x) = (term140 _87451 x' y x).
Proof. exact (MK_COMB (@lem3364395) (@lem3364412 _87451 x' y x)). Qed.
Lemma lem3364414 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3364415 {_87451 : Type'} (x' : type672 _87451) (y : _87451 -> Prop) (x : _87451) : (term141 _87451 x' y x) = (term142 _87451 x' y x).
Proof. exact (MK_COMB (@lem3364414) (@lem3364413 _87451 x' y x)). Qed.
Lemma lem3364416 {_87451 : Type'} (x' : type672 _87451) (y : _87451 -> Prop) (x : _87451) : (term143 _87451 x' y x) = (term144 _87451 x' y x).
Proof. exact (MK_COMB (@lem3364415 _87451 x' y x) (@lem3364394 _87451 y x)). Qed.
Lemma lem3364417 {_87451 : Type'} (x' : type672 _87451) (y : _87451 -> Prop) : (term145 _87451 x' y) = (term146 _87451 x' y).
Proof. exact (fun_ext (fun x : _87451 => @lem3364416 _87451 x' y x)). Qed.
Lemma lem3364418 {_87451 : Type'} : (@all _87451) = (@all _87451).
Proof. exact (eq_refl (@all _87451)). Qed.
Lemma lem3364419 {_87451 : Type'} (x' : type672 _87451) (y : _87451 -> Prop) : (term147 _87451 x' y) = (term148 _87451 x' y).
Proof. exact (MK_COMB (@lem3364418 _87451) (@lem3364417 _87451 x' y)). Qed.
Lemma lem3364420 {_87451 : Type'} (s : type686 _87451) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3364425 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3364426 {_87451 : Type'} (f : type672 _87451) (x : _87451 -> Prop) : (f x) = (@I ((_87451 -> Prop) -> _87451 -> Prop) f x).
Proof. exact (@lem3364425 (_87451 -> Prop) (_87451 -> Prop) f x). Qed.
Lemma lem3364428 {_87451 : Type'} (x' : type672 _87451) (y : _87451 -> Prop) : (x' y) = (@I ((_87451 -> Prop) -> _87451 -> Prop) x' y).
Proof. exact (@lem3364426 _87451 x' y). Qed.
Lemma lem3364429 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term149 _87451 s x' y) = (term150 _87451 s x' y).
Proof. exact (MK_COMB (@lem3364420 _87451 s) (@lem3364428 _87451 x' y)). Qed.
Lemma lem3364431 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3364432 {_87451 : Type'} (f : type686 _87451) (x : _87451 -> Prop) : (f x) = (@I ((_87451 -> Prop) -> Prop) f x).
Proof. exact (@lem3364431 (_87451 -> Prop) Prop f x). Qed.
Lemma lem3364433 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term150 _87451 s x' y) = (term151 _87451 s x' y).
Proof. exact (@lem3364432 _87451 s (@I ((_87451 -> Prop) -> _87451 -> Prop) x' y)). Qed.
Lemma lem3364434 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term149 _87451 s x' y) = (term151 _87451 s x' y).
Proof. exact (TRANS (@lem3364429 _87451 s x' y) (@lem3364433 _87451 s x' y)). Qed.
Lemma lem3364435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3364436 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term152 _87451 s x' y) = (term153 _87451 s x' y).
Proof. exact (MK_COMB (@lem3364435) (@lem3364434 _87451 s x' y)). Qed.
Lemma lem3364437 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term154 _87451 s x' y) = (term155 _87451 s x' y).
Proof. exact (MK_COMB (@lem3364436 _87451 s x' y) (@lem3364419 _87451 x' y)). Qed.
Lemma lem3364438 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3364443 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3364444 {_87451 : Type'} (f : type686 _87451) (x : _87451 -> Prop) : (f x) = (@I ((_87451 -> Prop) -> Prop) f x).
Proof. exact (@lem3364443 (_87451 -> Prop) Prop f x). Qed.
Lemma lem3364446 {_87451 : Type'} (t : type686 _87451) (y : _87451 -> Prop) : (t y) = (@I ((_87451 -> Prop) -> Prop) t y).
Proof. exact (@lem3364444 _87451 t y). Qed.
Lemma lem3364447 {_87451 : Type'} (t : type686 _87451) (y : _87451 -> Prop) : (term91 _87451 t y) = (term132 _87451 t y).
Proof. exact (MK_COMB (@lem3364438) (@lem3364446 _87451 t y)). Qed.
Lemma lem3364448 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3364449 {_87451 : Type'} (t : type686 _87451) (y : _87451 -> Prop) : (term80 _87451 t y) = (term133 _87451 t y).
Proof. exact (MK_COMB (@lem3364448) (@lem3364447 _87451 t y)). Qed.
Lemma lem3364450 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term121 _87451 t s x' y) = (term156 _87451 t s x' y).
Proof. exact (MK_COMB (@lem3364449 _87451 t y) (@lem3364437 _87451 s x' y)). Qed.
Lemma lem3364451 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) : (term123 _87451 t s x') = (term157 _87451 t s x').
Proof. exact (fun_ext (fun y : _87451 -> Prop => @lem3364450 _87451 t s x' y)). Qed.
Lemma lem3364452 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3364453 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) : (term125 _87451 t s x') = (term158 _87451 t s x').
Proof. exact (MK_COMB (@lem3364452 _87451) (@lem3364451 _87451 t s x')). Qed.
Lemma lem3364454 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term158 _87451 t s x'.
Proof. exact (EQ_MP (@lem3364453 _87451 t s x') (@lem3364341 _87451 t s x' h1)). Qed.
Lemma lem3364462 {_87451 : Type'} (s : type686 _87451) (t : _87451 -> Prop) (x : _87451) : (term134 _87451 s t x) = (term134 _87451 s t x).
Proof. exact (eq_refl (term134 _87451 s t x)). Qed.
Lemma lem3364463 {_87451 : Type'} (s : type686 _87451) (x : _87451) : (term135 _87451 s x) = (term135 _87451 s x).
Proof. exact (fun_ext (fun t : _87451 -> Prop => @lem3364462 _87451 s t x)). Qed.
Lemma lem3364464 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3364466 {_87451 : Type'} (s : type686 _87451) (x : _87451) : (term136 _87451 s x) = (term136 _87451 s x).
Proof. exact (MK_COMB (@lem3364464 _87451) (@lem3364463 _87451 s x)). Qed.
Lemma lem3364467 {_87451 : Type'} (s : type686 _87451) (x : _87451) (h1 : term51 _87451 s x) : term136 _87451 s x.
Proof. exact (EQ_MP (@lem3364466 _87451 s x) (@lem3364366 _87451 s x h1)). Qed.
Lemma lem3364477 {A : Type'} (P : Prop) (Q : A -> Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem3364478 {_87451 : Type'} (P : Prop) (Q : _87451 -> Prop) : (term159 _87451 P Q) = (term160 _87451 P Q).
Proof. exact (@lem3364477 _87451 P Q). Qed.
Lemma lem3364479 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term161 _87451 s x' y) = (term162 _87451 s x' y).
Proof. exact (@lem3364478 _87451 (term151 _87451 s x' y) (term146 _87451 x' y)). Qed.
Lemma lem3364480 {_87451 : Type'} (x' : type672 _87451) (y : _87451 -> Prop) (x : _87451) : (term163 _87451 x' y x) = (term144 _87451 x' y x).
Proof. exact (eq_refl (term163 _87451 x' y x)). Qed.
Lemma lem3364481 {_87451 : Type'} (x' : type672 _87451) (y : _87451 -> Prop) : (term164 _87451 x' y) = (term146 _87451 x' y).
Proof. exact (fun_ext (fun x : _87451 => @lem3364480 _87451 x' y x)). Qed.
Lemma lem3364482 {_87451 : Type'} : (@all _87451) = (@all _87451).
Proof. exact (eq_refl (@all _87451)). Qed.
Lemma lem3364483 {_87451 : Type'} (x' : type672 _87451) (y : _87451 -> Prop) : (term165 _87451 x' y) = (term148 _87451 x' y).
Proof. exact (MK_COMB (@lem3364482 _87451) (@lem3364481 _87451 x' y)). Qed.
Lemma lem3364484 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term153 _87451 s x' y) = (term153 _87451 s x' y).
Proof. exact (eq_refl (term153 _87451 s x' y)). Qed.
Lemma lem3364485 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term161 _87451 s x' y) = (term155 _87451 s x' y).
Proof. exact (MK_COMB (@lem3364484 _87451 s x' y) (@lem3364483 _87451 x' y)). Qed.
Lemma lem3364486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3364487 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term166 _87451 s x' y) = (term167 _87451 s x' y).
Proof. exact (MK_COMB (@lem3364486) (@lem3364485 _87451 s x' y)). Qed.
Lemma lem3364488 {_87451 : Type'} (x' : type672 _87451) (y : _87451 -> Prop) (x : _87451) : (term163 _87451 x' y x) = (term144 _87451 x' y x).
Proof. exact (eq_refl (term163 _87451 x' y x)). Qed.
Lemma lem3364489 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term153 _87451 s x' y) = (term153 _87451 s x' y).
Proof. exact (eq_refl (term153 _87451 s x' y)). Qed.
Lemma lem3364490 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) (x : _87451) : (term168 _87451 s x' y x) = (term169 _87451 s x' y x).
Proof. exact (MK_COMB (@lem3364489 _87451 s x' y) (@lem3364488 _87451 x' y x)). Qed.
Lemma lem3364491 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term170 _87451 s x' y) = (term171 _87451 s x' y).
Proof. exact (fun_ext (fun x : _87451 => @lem3364490 _87451 s x' y x)). Qed.
Lemma lem3364492 {_87451 : Type'} : (@all _87451) = (@all _87451).
Proof. exact (eq_refl (@all _87451)). Qed.
Lemma lem3364493 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term162 _87451 s x' y) = (term172 _87451 s x' y).
Proof. exact (MK_COMB (@lem3364492 _87451) (@lem3364491 _87451 s x' y)). Qed.
Lemma lem3364494 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : ((term161 _87451 s x' y) = (term162 _87451 s x' y)) = ((term155 _87451 s x' y) = (term172 _87451 s x' y)).
Proof. exact (MK_COMB (@lem3364487 _87451 s x' y) (@lem3364493 _87451 s x' y)). Qed.
Lemma lem3364495 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term155 _87451 s x' y) = (term172 _87451 s x' y).
Proof. exact (EQ_MP (@lem3364494 _87451 s x' y) (@lem3364479 _87451 s x' y)). Qed.
Lemma lem3364496 {_87451 : Type'} (t : type686 _87451) (y : _87451 -> Prop) : (term133 _87451 t y) = (term133 _87451 t y).
Proof. exact (eq_refl (term133 _87451 t y)). Qed.
Lemma lem3364497 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term156 _87451 t s x' y) = (term173 _87451 t s x' y).
Proof. exact (MK_COMB (@lem3364496 _87451 t y) (@lem3364495 _87451 s x' y)). Qed.
Lemma lem3364499 {A : Type'} (P : Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3364500 {_87451 : Type'} (P : Prop) (Q : _87451 -> Prop) : (term174 _87451 P Q) = (term175 _87451 P Q).
Proof. exact (@lem3364499 _87451 P Q). Qed.
Lemma lem3364501 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term176 _87451 t s x' y) = (term177 _87451 t s x' y).
Proof. exact (@lem3364500 _87451 (term132 _87451 t y) (term171 _87451 s x' y)). Qed.
Lemma lem3364502 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) (x : _87451) : (term178 _87451 s x' y x) = (term169 _87451 s x' y x).
Proof. exact (eq_refl (term178 _87451 s x' y x)). Qed.
Lemma lem3364503 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term179 _87451 s x' y) = (term171 _87451 s x' y).
Proof. exact (fun_ext (fun x : _87451 => @lem3364502 _87451 s x' y x)). Qed.
Lemma lem3364504 {_87451 : Type'} : (@all _87451) = (@all _87451).
Proof. exact (eq_refl (@all _87451)). Qed.
Lemma lem3364505 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term180 _87451 s x' y) = (term172 _87451 s x' y).
Proof. exact (MK_COMB (@lem3364504 _87451) (@lem3364503 _87451 s x' y)). Qed.
Lemma lem3364506 {_87451 : Type'} (t : type686 _87451) (y : _87451 -> Prop) : (term133 _87451 t y) = (term133 _87451 t y).
Proof. exact (eq_refl (term133 _87451 t y)). Qed.
Lemma lem3364507 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term176 _87451 t s x' y) = (term173 _87451 t s x' y).
Proof. exact (MK_COMB (@lem3364506 _87451 t y) (@lem3364505 _87451 s x' y)). Qed.
Lemma lem3364508 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3364509 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term181 _87451 t s x' y) = (term182 _87451 t s x' y).
Proof. exact (MK_COMB (@lem3364508) (@lem3364507 _87451 t s x' y)). Qed.
Lemma lem3364510 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) (x : _87451) : (term178 _87451 s x' y x) = (term169 _87451 s x' y x).
Proof. exact (eq_refl (term178 _87451 s x' y x)). Qed.
Lemma lem3364511 {_87451 : Type'} (t : type686 _87451) (y : _87451 -> Prop) : (term133 _87451 t y) = (term133 _87451 t y).
Proof. exact (eq_refl (term133 _87451 t y)). Qed.
Lemma lem3364512 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) (x : _87451) : (term183 _87451 t s x' y x) = (term184 _87451 t s x' y x).
Proof. exact (MK_COMB (@lem3364511 _87451 t y) (@lem3364510 _87451 s x' y x)). Qed.
Lemma lem3364513 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term185 _87451 t s x' y) = (term186 _87451 t s x' y).
Proof. exact (fun_ext (fun x : _87451 => @lem3364512 _87451 t s x' y x)). Qed.
Lemma lem3364514 {_87451 : Type'} : (@all _87451) = (@all _87451).
Proof. exact (eq_refl (@all _87451)). Qed.
Lemma lem3364515 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term177 _87451 t s x' y) = (term187 _87451 t s x' y).
Proof. exact (MK_COMB (@lem3364514 _87451) (@lem3364513 _87451 t s x' y)). Qed.
Lemma lem3364516 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : ((term176 _87451 t s x' y) = (term177 _87451 t s x' y)) = ((term173 _87451 t s x' y) = (term187 _87451 t s x' y)).
Proof. exact (MK_COMB (@lem3364509 _87451 t s x' y) (@lem3364515 _87451 t s x' y)). Qed.
Lemma lem3364517 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term173 _87451 t s x' y) = (term187 _87451 t s x' y).
Proof. exact (EQ_MP (@lem3364516 _87451 t s x' y) (@lem3364501 _87451 t s x' y)). Qed.
Lemma lem3364518 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term156 _87451 t s x' y) = (term187 _87451 t s x' y).
Proof. exact (TRANS (@lem3364497 _87451 t s x' y) (@lem3364517 _87451 t s x' y)). Qed.
Lemma lem3364519 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) : (term157 _87451 t s x') = (term188 _87451 t s x').
Proof. exact (fun_ext (fun y : _87451 -> Prop => @lem3364518 _87451 t s x' y)). Qed.
Lemma lem3364520 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3364521 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) : (term158 _87451 t s x') = (term189 _87451 t s x').
Proof. exact (MK_COMB (@lem3364520 _87451) (@lem3364519 _87451 t s x')). Qed.
Lemma lem3364544 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) (x : _87451) : (term184 _87451 t s x' y x) = (term190 _87451 s t x' y x).
Proof. exact (@lem19490 (term151 _87451 s x' y) (term132 _87451 t y) (term144 _87451 x' y x)). Qed.
Lemma lem3364545 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term186 _87451 t s x' y) = (term191 _87451 s t x' y).
Proof. exact (fun_ext (fun x : _87451 => @lem3364544 _87451 s t x' y x)). Qed.
Lemma lem3364546 {_87451 : Type'} : (@all _87451) = (@all _87451).
Proof. exact (eq_refl (@all _87451)). Qed.
Lemma lem3364547 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) (x' : type672 _87451) (y : _87451 -> Prop) : (term187 _87451 t s x' y) = (term192 _87451 s t x' y).
Proof. exact (MK_COMB (@lem3364546 _87451) (@lem3364545 _87451 s t x' y)). Qed.
Lemma lem3364548 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) (x' : type672 _87451) : (term188 _87451 t s x') = (term193 _87451 s t x').
Proof. exact (fun_ext (fun y : _87451 -> Prop => @lem3364547 _87451 s t x' y)). Qed.
Lemma lem3364549 {_87451 : Type'} : (@all (_87451 -> Prop)) = (@all (_87451 -> Prop)).
Proof. exact (eq_refl (@all (_87451 -> Prop))). Qed.
Lemma lem3364550 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) (x' : type672 _87451) : (term189 _87451 t s x') = (term194 _87451 s t x').
Proof. exact (MK_COMB (@lem3364549 _87451) (@lem3364548 _87451 s t x')). Qed.
Lemma lem3364551 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) (x' : type672 _87451) : (term158 _87451 t s x') = (term194 _87451 s t x').
Proof. exact (TRANS (@lem3364521 _87451 t s x') (@lem3364550 _87451 s t x')). Qed.
Lemma lem3364552 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term194 _87451 s t x'.
Proof. exact (EQ_MP (@lem3364551 _87451 s t x') (@lem3364454 _87451 t s x' h1)). Qed.
Lemma lem3364553 {_87451 : Type'} (_35076 : _87451 -> Prop) (s : type686 _87451) (x : _87451) (h1 : term51 _87451 s x) : term195 _87451 s x _35076.
Proof. exact (@lem3364467 _87451 s x h1 _35076). Qed.
Lemma lem3364554 {_87451 : Type'} (s : type686 _87451) (_35076 : _87451 -> Prop) (x : _87451) : (term195 _87451 s x _35076) = (term134 _87451 s _35076 x).
Proof. exact (eq_refl (term195 _87451 s x _35076)). Qed.
Lemma lem3364556 {_87451 : Type'} (_35077 : _87451 -> Prop) (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term196 _87451 s t x' _35077.
Proof. exact (@lem3364552 _87451 t s x' h1 _35077). Qed.
Lemma lem3364557 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) : (term196 _87451 s t x' _35077) = (term192 _87451 s t x' _35077).
Proof. exact (eq_refl (term196 _87451 s t x' _35077)). Qed.
Lemma lem3364558 {_87451 : Type'} (_35077 : _87451 -> Prop) (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term192 _87451 s t x' _35077.
Proof. exact (EQ_MP (@lem3364557 _87451 s t x' _35077) (@lem3364556 _87451 _35077 t s x' h1)). Qed.
Lemma lem3364559 {_87451 : Type'} (_35077 : _87451 -> Prop) (_35078 : _87451) (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term197 _87451 s t x' _35077 _35078.
Proof. exact (@lem3364558 _87451 _35077 t s x' h1 _35078). Qed.
Lemma lem3364560 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) (_35078 : _87451) : (term197 _87451 s t x' _35077 _35078) = (term190 _87451 s t x' _35077 _35078).
Proof. exact (eq_refl (term197 _87451 s t x' _35077 _35078)). Qed.
Lemma lem3364561 {_87451 : Type'} (_35077 : _87451 -> Prop) (_35078 : _87451) (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term190 _87451 s t x' _35077 _35078.
Proof. exact (EQ_MP (@lem3364560 _87451 s t x' _35077 _35078) (@lem3364559 _87451 _35077 _35078 t s x' h1)). Qed.
Lemma lem3364569 {_87451 : Type'} (_35076 : _87451 -> Prop) (s : type686 _87451) (x : _87451) (h1 : term51 _87451 s x) : term134 _87451 s _35076 x.
Proof. exact (EQ_MP (@lem3364554 _87451 s _35076 x) (@lem3364553 _87451 _35076 s x h1)). Qed.
Lemma lem3364573 {_87451 : Type'} (t' : _87451 -> Prop) (x : _87451) (h1 : term73 _87451 t' x) : term137 _87451 t' x.
Proof. exact (EQ_MP (@lem3364385 _87451 t' x) (@lem3364340 _87451 t' x h1)). Qed.
Lemma lem3364579 {_87451 : Type'} (_35077 : _87451 -> Prop) (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term198 _87451 t s x' _35077.
Proof. exact (proj1 (@lem3364561 _87451 _35077 (@el _87451) t s x' h1)). Qed.
Lemma lem3364589 {_87451 : Type'} (_35077 : _87451 -> Prop) (_35078 : _87451) (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term199 _87451 t x' _35077 _35078.
Proof. exact (proj2 (@lem3364561 _87451 _35077 _35078 t s x' h1)). Qed.
Lemma lem3364591 {_87451 : Type'} (t : type686 _87451) (t' : _87451 -> Prop) (h1 : t t') : @I ((_87451 -> Prop) -> Prop) t t'.
Proof. exact (EQ_MP (@lem3364374 _87451 t t') (@lem3364334 _87451 t t' h1)). Qed.
Lemma lem3364592 {_87451 : Type'} (t : type686 _87451) (t' : _87451 -> Prop) (h1 : t t') : term200 _87451 t t'.
Proof. exact (fun h0 : term132 _87451 t t' => @lem3364591 _87451 t t' h1). Qed.
Lemma lem3364594 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3364595 {_87451 : Type'} (t : type686 _87451) (t' : _87451 -> Prop) : (term200 _87451 t t') = (@I ((_87451 -> Prop) -> Prop) t t').
Proof. exact (@lem3364594 (@I ((_87451 -> Prop) -> Prop) t t')). Qed.
Lemma lem3364596 {_87451 : Type'} (t : type686 _87451) (t' : _87451 -> Prop) (h1 : t t') : @I ((_87451 -> Prop) -> Prop) t t'.
Proof. exact (EQ_MP (@lem3364595 _87451 t t') (@lem3364592 _87451 t t' h1)). Qed.
Lemma lem3364598 {_87451 : Type'} (t : type686 _87451) (t' : _87451 -> Prop) (h1 : t t') : @I ((_87451 -> Prop) -> Prop) t t'.
Proof. exact (EQ_MP (@lem3364374 _87451 t t') (@lem3364334 _87451 t t' h1)). Qed.
Lemma lem3364599 {_87451 : Type'} (t : type686 _87451) (t' : _87451 -> Prop) (h1 : t t') : term200 _87451 t t'.
Proof. exact (fun h0 : term132 _87451 t t' => @lem3364598 _87451 t t' h1). Qed.
Lemma lem3364601 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3364602 {_87451 : Type'} (t : type686 _87451) (t' : _87451 -> Prop) : (term200 _87451 t t') = (@I ((_87451 -> Prop) -> Prop) t t').
Proof. exact (@lem3364601 (@I ((_87451 -> Prop) -> Prop) t t')). Qed.
Lemma lem3364603 {_87451 : Type'} (t : type686 _87451) (t' : _87451 -> Prop) (h1 : t t') : @I ((_87451 -> Prop) -> Prop) t t'.
Proof. exact (EQ_MP (@lem3364602 _87451 t t') (@lem3364599 _87451 t t' h1)). Qed.
Lemma lem3364609 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3364610 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : (term198 _87451 t s x' _35077) = (term202 _87451 s x' t _35077).
Proof. exact (@lem3364609 (term151 _87451 s x' _35077) (term132 _87451 t _35077)). Qed.
Lemma lem3364616 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3364617 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : (term203 _87451 t s x' _35077) = (term204 _87451 s x' t _35077).
Proof. exact (MK_COMB (@lem3364616) (@lem3364610 _87451 s x' t _35077)). Qed.
Lemma lem3364623 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : (term202 _87451 s x' t _35077) = (term202 _87451 s x' t _35077).
Proof. exact (eq_refl (term202 _87451 s x' t _35077)). Qed.
Lemma lem3364624 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : ((term198 _87451 t s x' _35077) = (term202 _87451 s x' t _35077)) = ((term202 _87451 s x' t _35077) = (term202 _87451 s x' t _35077)).
Proof. exact (MK_COMB (@lem3364617 _87451 s x' t _35077) (@lem3364623 _87451 s x' t _35077)). Qed.
Lemma lem3364626 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3364627 (x : Prop) : (x = x) = True.
Proof. exact (@lem3364626 Prop x). Qed.
Lemma lem3364628 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : ((term202 _87451 s x' t _35077) = (term202 _87451 s x' t _35077)) = True.
Proof. exact (@lem3364627 (term202 _87451 s x' t _35077)). Qed.
Lemma lem3364629 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : ((term198 _87451 t s x' _35077) = (term202 _87451 s x' t _35077)) = True.
Proof. exact (TRANS (@lem3364624 _87451 s x' t _35077) (@lem3364628 _87451 s x' t _35077)). Qed.
Lemma lem3364630 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : True = ((term198 _87451 t s x' _35077) = (term202 _87451 s x' t _35077)).
Proof. exact (SYM (@lem3364629 _87451 s x' t _35077)). Qed.
Lemma lem3364631 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : (term198 _87451 t s x' _35077) = (term202 _87451 s x' t _35077).
Proof. exact (EQ_MP (@lem3364630 _87451 s x' t _35077) (@lem0)). Qed.
Lemma lem3364632 {_87451 : Type'} (_35077 : _87451 -> Prop) (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term202 _87451 s x' t _35077.
Proof. exact (EQ_MP (@lem3364631 _87451 s x' t _35077) (@lem3364579 _87451 _35077 t s x' h1)). Qed.
Lemma lem3364634 (b : Prop) (a : Prop) : (a \/ b) = (term205 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3364635 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) : (term202 _87451 s x' t _35077) = (term206 _87451 t s x' _35077).
Proof. exact (@lem3364634 (term132 _87451 t _35077) (term151 _87451 s x' _35077)). Qed.
Lemma lem3364637 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3364638 {_87451 : Type'} (t : type686 _87451) (_35077 : _87451 -> Prop) : (term207 _87451 t _35077) = (@I ((_87451 -> Prop) -> Prop) t _35077).
Proof. exact (@lem3364637 (@I ((_87451 -> Prop) -> Prop) t _35077)). Qed.
Lemma lem3364639 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3364640 {_87451 : Type'} (t : type686 _87451) (_35077 : _87451 -> Prop) : (term208 _87451 t _35077) = (term209 _87451 t _35077).
Proof. exact (MK_COMB (@lem3364639) (@lem3364638 _87451 t _35077)). Qed.
Lemma lem3364641 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) : (term151 _87451 s x' _35077) = (term151 _87451 s x' _35077).
Proof. exact (eq_refl (term151 _87451 s x' _35077)). Qed.
Lemma lem3364642 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) : (term206 _87451 t s x' _35077) = (term210 _87451 t s x' _35077).
Proof. exact (MK_COMB (@lem3364640 _87451 t _35077) (@lem3364641 _87451 s x' _35077)). Qed.
Lemma lem3364643 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) : (term202 _87451 s x' t _35077) = (term210 _87451 t s x' _35077).
Proof. exact (TRANS (@lem3364635 _87451 t s x' _35077) (@lem3364642 _87451 t s x' _35077)). Qed.
Lemma lem3364646 {_87451 : Type'} (_35077 : _87451 -> Prop) (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term210 _87451 t s x' _35077.
Proof. exact (EQ_MP (@lem3364643 _87451 t s x' _35077) (@lem3364632 _87451 _35077 t s x' h1)). Qed.
Lemma lem3364647 {_87451 : Type'} (_35077 : _87451 -> Prop) (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term210 _87451 t s x' _35077.
Proof. exact (@lem3364646 _87451 _35077 t s x' h1). Qed.
Lemma lem3364648 {_87451 : Type'} (t' : _87451 -> Prop) (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term210 _87451 t s x' t'.
Proof. exact (@lem3364647 _87451 t' t s x' h1). Qed.
Lemma lem3364651 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term125 _87451 t s x') (h2 : t t') : term151 _87451 s x' t'.
Proof. exact (@lem3364648 _87451 t' t s x' h1 (@lem3364603 _87451 t t' h2)). Qed.
Lemma lem3364652 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term125 _87451 t s x') (h2 : t t') : term211 _87451 s x' t'.
Proof. exact (fun h0 : term212 _87451 s x' t' => @lem3364651 _87451 s x' t t' h1 h2). Qed.
Lemma lem3364654 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3364655 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (t' : _87451 -> Prop) : (term211 _87451 s x' t') = (term151 _87451 s x' t').
Proof. exact (@lem3364654 (term151 _87451 s x' t')). Qed.
Lemma lem3364656 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term125 _87451 t s x') (h2 : t t') : term151 _87451 s x' t'.
Proof. exact (EQ_MP (@lem3364655 _87451 s x' t') (@lem3364652 _87451 s x' t t' h1 h2)). Qed.
Lemma lem3364662 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3364663 {_87451 : Type'} (x : _87451) (s : type686 _87451) (_35076 : _87451 -> Prop) : (term134 _87451 s _35076 x) = (term213 _87451 x s _35076).
Proof. exact (@lem3364662 (@I (_87451 -> Prop) _35076 x) (term132 _87451 s _35076)). Qed.
Lemma lem3364669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3364670 {_87451 : Type'} (x : _87451) (s : type686 _87451) (_35076 : _87451 -> Prop) : (term214 _87451 s _35076 x) = (term215 _87451 x s _35076).
Proof. exact (MK_COMB (@lem3364669) (@lem3364663 _87451 x s _35076)). Qed.
Lemma lem3364676 {_87451 : Type'} (x : _87451) (s : type686 _87451) (_35076 : _87451 -> Prop) : (term213 _87451 x s _35076) = (term213 _87451 x s _35076).
Proof. exact (eq_refl (term213 _87451 x s _35076)). Qed.
Lemma lem3364677 {_87451 : Type'} (x : _87451) (s : type686 _87451) (_35076 : _87451 -> Prop) : ((term134 _87451 s _35076 x) = (term213 _87451 x s _35076)) = ((term213 _87451 x s _35076) = (term213 _87451 x s _35076)).
Proof. exact (MK_COMB (@lem3364670 _87451 x s _35076) (@lem3364676 _87451 x s _35076)). Qed.
Lemma lem3364679 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3364680 (x : Prop) : (x = x) = True.
Proof. exact (@lem3364679 Prop x). Qed.
Lemma lem3364681 {_87451 : Type'} (x : _87451) (s : type686 _87451) (_35076 : _87451 -> Prop) : ((term213 _87451 x s _35076) = (term213 _87451 x s _35076)) = True.
Proof. exact (@lem3364680 (term213 _87451 x s _35076)). Qed.
Lemma lem3364682 {_87451 : Type'} (x : _87451) (s : type686 _87451) (_35076 : _87451 -> Prop) : ((term134 _87451 s _35076 x) = (term213 _87451 x s _35076)) = True.
Proof. exact (TRANS (@lem3364677 _87451 x s _35076) (@lem3364681 _87451 x s _35076)). Qed.
Lemma lem3364683 {_87451 : Type'} (x : _87451) (s : type686 _87451) (_35076 : _87451 -> Prop) : True = ((term134 _87451 s _35076 x) = (term213 _87451 x s _35076)).
Proof. exact (SYM (@lem3364682 _87451 x s _35076)). Qed.
Lemma lem3364684 {_87451 : Type'} (x : _87451) (s : type686 _87451) (_35076 : _87451 -> Prop) : (term134 _87451 s _35076 x) = (term213 _87451 x s _35076).
Proof. exact (EQ_MP (@lem3364683 _87451 x s _35076) (@lem0)). Qed.
Lemma lem3364685 {_87451 : Type'} (_35076 : _87451 -> Prop) (s : type686 _87451) (x : _87451) (h1 : term51 _87451 s x) : term213 _87451 x s _35076.
Proof. exact (EQ_MP (@lem3364684 _87451 x s _35076) (@lem3364569 _87451 _35076 s x h1)). Qed.
Lemma lem3364687 (b : Prop) (a : Prop) : (a \/ b) = (term205 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3364688 {_87451 : Type'} (s : type686 _87451) (_35076 : _87451 -> Prop) (x : _87451) : (term213 _87451 x s _35076) = (term216 _87451 s _35076 x).
Proof. exact (@lem3364687 (term132 _87451 s _35076) (@I (_87451 -> Prop) _35076 x)). Qed.
Lemma lem3364690 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3364691 {_87451 : Type'} (s : type686 _87451) (_35076 : _87451 -> Prop) : (term207 _87451 s _35076) = (@I ((_87451 -> Prop) -> Prop) s _35076).
Proof. exact (@lem3364690 (@I ((_87451 -> Prop) -> Prop) s _35076)). Qed.
Lemma lem3364692 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3364693 {_87451 : Type'} (s : type686 _87451) (_35076 : _87451 -> Prop) : (term208 _87451 s _35076) = (term209 _87451 s _35076).
Proof. exact (MK_COMB (@lem3364692) (@lem3364691 _87451 s _35076)). Qed.
Lemma lem3364694 {_87451 : Type'} (_35076 : _87451 -> Prop) (x : _87451) : (@I (_87451 -> Prop) _35076 x) = (@I (_87451 -> Prop) _35076 x).
Proof. exact (eq_refl (@I (_87451 -> Prop) _35076 x)). Qed.
Lemma lem3364695 {_87451 : Type'} (s : type686 _87451) (_35076 : _87451 -> Prop) (x : _87451) : (term216 _87451 s _35076 x) = (term217 _87451 s _35076 x).
Proof. exact (MK_COMB (@lem3364693 _87451 s _35076) (@lem3364694 _87451 _35076 x)). Qed.
Lemma lem3364696 {_87451 : Type'} (s : type686 _87451) (_35076 : _87451 -> Prop) (x : _87451) : (term213 _87451 x s _35076) = (term217 _87451 s _35076 x).
Proof. exact (TRANS (@lem3364688 _87451 s _35076 x) (@lem3364695 _87451 s _35076 x)). Qed.
Lemma lem3364699 {_87451 : Type'} (_35076 : _87451 -> Prop) (s : type686 _87451) (x : _87451) (h1 : term51 _87451 s x) : term217 _87451 s _35076 x.
Proof. exact (EQ_MP (@lem3364696 _87451 s _35076 x) (@lem3364685 _87451 _35076 s x h1)). Qed.
Lemma lem3364700 {_87451 : Type'} (_35076 : _87451 -> Prop) (s : type686 _87451) (x : _87451) (h1 : term51 _87451 s x) : term217 _87451 s _35076 x.
Proof. exact (@lem3364699 _87451 _35076 s x h1). Qed.
Lemma lem3364701 {_87451 : Type'} (x' : type672 _87451) (t' : _87451 -> Prop) (s : type686 _87451) (x : _87451) (h1 : term51 _87451 s x) : term218 _87451 s x' t' x.
Proof. exact (@lem3364700 _87451 (@I ((_87451 -> Prop) -> _87451 -> Prop) x' t') s x h1). Qed.
Lemma lem3364704 {_87451 : Type'} (x : _87451) (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term125 _87451 t s x') (h3 : t t') : term138 _87451 x' t' x.
Proof. exact (@lem3364701 _87451 x' t' s x h1 (@lem3364656 _87451 s x' t t' h2 h3)). Qed.
Lemma lem3364705 {_87451 : Type'} (x : _87451) (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term125 _87451 t s x') (h3 : t t') : term219 _87451 x' t' x.
Proof. exact (fun h0 : term140 _87451 x' t' x => @lem3364704 _87451 x s x' t t' h1 h2 h3). Qed.
Lemma lem3364707 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3364708 {_87451 : Type'} (x' : type672 _87451) (t' : _87451 -> Prop) (x : _87451) : (term219 _87451 x' t' x) = (term138 _87451 x' t' x).
Proof. exact (@lem3364707 (term138 _87451 x' t' x)). Qed.
Lemma lem3364709 {_87451 : Type'} (x : _87451) (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term125 _87451 t s x') (h3 : t t') : term138 _87451 x' t' x.
Proof. exact (EQ_MP (@lem3364708 _87451 x' t' x) (@lem3364705 _87451 x s x' t t' h1 h2 h3)). Qed.
Lemma lem3364715 (q : Prop) (p : Prop) (r : Prop) : (term220 p q r) = (term220 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3364716 {_87451 : Type'} (x' : type672 _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) (_35078 : _87451) : (term199 _87451 t x' _35077 _35078) = (term221 _87451 x' t _35077 _35078).
Proof. exact (@lem3364715 (term140 _87451 x' _35077 _35078) (term132 _87451 t _35077) (@I (_87451 -> Prop) _35077 _35078)). Qed.
Lemma lem3364730 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3364731 {_87451 : Type'} (_35078 : _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : (term134 _87451 t _35077 _35078) = (term213 _87451 _35078 t _35077).
Proof. exact (@lem3364730 (@I (_87451 -> Prop) _35077 _35078) (term132 _87451 t _35077)). Qed.
Lemma lem3364737 {_87451 : Type'} (x' : type672 _87451) (_35077 : _87451 -> Prop) (_35078 : _87451) : (term142 _87451 x' _35077 _35078) = (term142 _87451 x' _35077 _35078).
Proof. exact (eq_refl (term142 _87451 x' _35077 _35078)). Qed.
Lemma lem3364738 {_87451 : Type'} (x' : type672 _87451) (_35078 : _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : (term221 _87451 x' t _35077 _35078) = (term222 _87451 x' _35078 t _35077).
Proof. exact (MK_COMB (@lem3364737 _87451 x' _35077 _35078) (@lem3364731 _87451 _35078 t _35077)). Qed.
Lemma lem3364742 (q : Prop) (p : Prop) (r : Prop) : (term220 p q r) = (term220 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3364743 {_87451 : Type'} (x' : type672 _87451) (_35078 : _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : (term222 _87451 x' _35078 t _35077) = (term223 _87451 x' _35078 t _35077).
Proof. exact (@lem3364742 (@I (_87451 -> Prop) _35077 _35078) (term140 _87451 x' _35077 _35078) (term132 _87451 t _35077)). Qed.
Lemma lem3364759 {_87451 : Type'} (x' : type672 _87451) (_35078 : _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : (term221 _87451 x' t _35077 _35078) = (term223 _87451 x' _35078 t _35077).
Proof. exact (TRANS (@lem3364738 _87451 x' _35078 t _35077) (@lem3364743 _87451 x' _35078 t _35077)). Qed.
Lemma lem3364760 {_87451 : Type'} (x' : type672 _87451) (_35078 : _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : (term199 _87451 t x' _35077 _35078) = (term223 _87451 x' _35078 t _35077).
Proof. exact (TRANS (@lem3364716 _87451 x' t _35077 _35078) (@lem3364759 _87451 x' _35078 t _35077)). Qed.
Lemma lem3364761 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3364762 {_87451 : Type'} (x' : type672 _87451) (_35078 : _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : (term224 _87451 t x' _35077 _35078) = (term225 _87451 x' _35078 t _35077).
Proof. exact (MK_COMB (@lem3364761) (@lem3364760 _87451 x' _35078 t _35077)). Qed.
Lemma lem3364776 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3364777 {_87451 : Type'} (x' : type672 _87451) (_35078 : _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : (term226 _87451 t x' _35077 _35078) = (term227 _87451 x' _35078 t _35077).
Proof. exact (@lem3364776 (term140 _87451 x' _35077 _35078) (term132 _87451 t _35077)). Qed.
Lemma lem3364783 {_87451 : Type'} (_35077 : _87451 -> Prop) (_35078 : _87451) : (term228 _87451 _35077 _35078) = (term228 _87451 _35077 _35078).
Proof. exact (eq_refl (term228 _87451 _35077 _35078)). Qed.
Lemma lem3364784 {_87451 : Type'} (x' : type672 _87451) (_35078 : _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : (term229 _87451 t x' _35077 _35078) = (term223 _87451 x' _35078 t _35077).
Proof. exact (MK_COMB (@lem3364783 _87451 _35077 _35078) (@lem3364777 _87451 x' _35078 t _35077)). Qed.
Lemma lem3364795 {_87451 : Type'} (x' : type672 _87451) (_35078 : _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : ((term199 _87451 t x' _35077 _35078) = (term229 _87451 t x' _35077 _35078)) = ((term223 _87451 x' _35078 t _35077) = (term223 _87451 x' _35078 t _35077)).
Proof. exact (MK_COMB (@lem3364762 _87451 x' _35078 t _35077) (@lem3364784 _87451 x' _35078 t _35077)). Qed.
Lemma lem3364797 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3364798 (x : Prop) : (x = x) = True.
Proof. exact (@lem3364797 Prop x). Qed.
Lemma lem3364799 {_87451 : Type'} (x' : type672 _87451) (_35078 : _87451) (t : type686 _87451) (_35077 : _87451 -> Prop) : ((term223 _87451 x' _35078 t _35077) = (term223 _87451 x' _35078 t _35077)) = True.
Proof. exact (@lem3364798 (term223 _87451 x' _35078 t _35077)). Qed.
Lemma lem3364800 {_87451 : Type'} (t : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) (_35078 : _87451) : ((term199 _87451 t x' _35077 _35078) = (term229 _87451 t x' _35077 _35078)) = True.
Proof. exact (TRANS (@lem3364795 _87451 x' _35078 t _35077) (@lem3364799 _87451 x' _35078 t _35077)). Qed.
Lemma lem3364801 {_87451 : Type'} (t : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) (_35078 : _87451) : True = ((term199 _87451 t x' _35077 _35078) = (term229 _87451 t x' _35077 _35078)).
Proof. exact (SYM (@lem3364800 _87451 t x' _35077 _35078)). Qed.
Lemma lem3364802 {_87451 : Type'} (t : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) (_35078 : _87451) : (term199 _87451 t x' _35077 _35078) = (term229 _87451 t x' _35077 _35078).
Proof. exact (EQ_MP (@lem3364801 _87451 t x' _35077 _35078) (@lem0)). Qed.
Lemma lem3364803 {_87451 : Type'} (_35077 : _87451 -> Prop) (_35078 : _87451) (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term229 _87451 t x' _35077 _35078.
Proof. exact (EQ_MP (@lem3364802 _87451 t x' _35077 _35078) (@lem3364589 _87451 _35077 _35078 t s x' h1)). Qed.
Lemma lem3364805 (b : Prop) (a : Prop) : (a \/ b) = (term205 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3364806 {_87451 : Type'} (t : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) (_35078 : _87451) : (term229 _87451 t x' _35077 _35078) = (term230 _87451 t x' _35077 _35078).
Proof. exact (@lem3364805 (term226 _87451 t x' _35077 _35078) (@I (_87451 -> Prop) _35077 _35078)). Qed.
Lemma lem3364808 (a : Prop) (b : Prop) : (term231 a b) = (term232 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3364809 {_87451 : Type'} (t : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) (_35078 : _87451) : (term233 _87451 t x' _35077 _35078) = (term234 _87451 t x' _35077 _35078).
Proof. exact (@lem3364808 (term132 _87451 t _35077) (term140 _87451 x' _35077 _35078)). Qed.
Lemma lem3364811 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3364812 {_87451 : Type'} (t : type686 _87451) (_35077 : _87451 -> Prop) : (term207 _87451 t _35077) = (@I ((_87451 -> Prop) -> Prop) t _35077).
Proof. exact (@lem3364811 (@I ((_87451 -> Prop) -> Prop) t _35077)). Qed.
Lemma lem3364813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3364814 {_87451 : Type'} (t : type686 _87451) (_35077 : _87451 -> Prop) : (term235 _87451 t _35077) = (term236 _87451 t _35077).
Proof. exact (MK_COMB (@lem3364813) (@lem3364812 _87451 t _35077)). Qed.
Lemma lem3364816 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3364817 {_87451 : Type'} (x' : type672 _87451) (_35077 : _87451 -> Prop) (_35078 : _87451) : (term237 _87451 x' _35077 _35078) = (term138 _87451 x' _35077 _35078).
Proof. exact (@lem3364816 (term138 _87451 x' _35077 _35078)). Qed.
Lemma lem3364818 {_87451 : Type'} (t : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) (_35078 : _87451) : (term234 _87451 t x' _35077 _35078) = (term238 _87451 t x' _35077 _35078).
Proof. exact (MK_COMB (@lem3364814 _87451 t _35077) (@lem3364817 _87451 x' _35077 _35078)). Qed.
Lemma lem3364819 {_87451 : Type'} (t : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) (_35078 : _87451) : (term233 _87451 t x' _35077 _35078) = (term238 _87451 t x' _35077 _35078).
Proof. exact (TRANS (@lem3364809 _87451 t x' _35077 _35078) (@lem3364818 _87451 t x' _35077 _35078)). Qed.
Lemma lem3364820 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3364821 {_87451 : Type'} (t : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) (_35078 : _87451) : (term239 _87451 t x' _35077 _35078) = (term240 _87451 t x' _35077 _35078).
Proof. exact (MK_COMB (@lem3364820) (@lem3364819 _87451 t x' _35077 _35078)). Qed.
Lemma lem3364822 {_87451 : Type'} (_35077 : _87451 -> Prop) (_35078 : _87451) : (@I (_87451 -> Prop) _35077 _35078) = (@I (_87451 -> Prop) _35077 _35078).
Proof. exact (eq_refl (@I (_87451 -> Prop) _35077 _35078)). Qed.
Lemma lem3364823 {_87451 : Type'} (t : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) (_35078 : _87451) : (term230 _87451 t x' _35077 _35078) = (term241 _87451 t x' _35077 _35078).
Proof. exact (MK_COMB (@lem3364821 _87451 t x' _35077 _35078) (@lem3364822 _87451 _35077 _35078)). Qed.
Lemma lem3364824 {_87451 : Type'} (t : type686 _87451) (x' : type672 _87451) (_35077 : _87451 -> Prop) (_35078 : _87451) : (term229 _87451 t x' _35077 _35078) = (term241 _87451 t x' _35077 _35078).
Proof. exact (TRANS (@lem3364806 _87451 t x' _35077 _35078) (@lem3364823 _87451 t x' _35077 _35078)). Qed.
Lemma lem3364826 {_87451 : Type'} (x : _87451) (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term125 _87451 t s x') (h3 : t t') : term238 _87451 t x' t' x.
Proof. exact (conj (@lem3364596 _87451 t t' h3) (@lem3364709 _87451 x s x' t t' h1 h2 h3)). Qed.
Lemma lem3364828 {_87451 : Type'} (_35077 : _87451 -> Prop) (_35078 : _87451) (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term241 _87451 t x' _35077 _35078.
Proof. exact (EQ_MP (@lem3364824 _87451 t x' _35077 _35078) (@lem3364803 _87451 _35077 _35078 t s x' h1)). Qed.
Lemma lem3364829 {_87451 : Type'} (_35077 : _87451 -> Prop) (_35078 : _87451) (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term241 _87451 t x' _35077 _35078.
Proof. exact (@lem3364828 _87451 _35077 _35078 t s x' h1). Qed.
Lemma lem3364830 {_87451 : Type'} (t' : _87451 -> Prop) (x : _87451) (t : type686 _87451) (s : type686 _87451) (x' : type672 _87451) (h1 : term125 _87451 t s x') : term241 _87451 t x' t' x.
Proof. exact (@lem3364829 _87451 t' x t s x' h1). Qed.
Lemma lem3364833 {_87451 : Type'} (x : _87451) (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term125 _87451 t s x') (h3 : t t') : @I (_87451 -> Prop) t' x.
Proof. exact (@lem3364830 _87451 t' x t s x' h2 (@lem3364826 _87451 x s x' t t' h1 h2 h3)). Qed.
Lemma lem3364834 {_87451 : Type'} (x : _87451) (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term125 _87451 t s x') (h3 : t t') : term242 _87451 t' x.
Proof. exact (fun h0 : term137 _87451 t' x => @lem3364833 _87451 x s x' t t' h1 h2 h3). Qed.
Lemma lem3364836 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3364837 {_87451 : Type'} (t' : _87451 -> Prop) (x : _87451) : (term242 _87451 t' x) = (@I (_87451 -> Prop) t' x).
Proof. exact (@lem3364836 (@I (_87451 -> Prop) t' x)). Qed.
Lemma lem3364838 {_87451 : Type'} (x : _87451) (s : type686 _87451) (x' : type672 _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term125 _87451 t s x') (h3 : t t') : @I (_87451 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3364837 _87451 t' x) (@lem3364834 _87451 x s x' t t' h1 h2 h3)). Qed.
Lemma lem3364841 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3364843 {_87451 : Type'} (t' : _87451 -> Prop) (x : _87451) : (term137 _87451 t' x) = (term243 _87451 t' x).
Proof. exact (@lem3364841 (@I (_87451 -> Prop) t' x)). Qed.
Lemma lem3364846 {_87451 : Type'} (t' : _87451 -> Prop) (x : _87451) (h1 : term73 _87451 t' x) : term243 _87451 t' x.
Proof. exact (EQ_MP (@lem3364843 _87451 t' x) (@lem3364573 _87451 t' x h1)). Qed.
Lemma lem3364849 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (x : _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term125 _87451 t s x') (h3 : term73 _87451 t' x) (h4 : t t') : False.
Proof. exact (@lem3364846 _87451 t' x h3 (@lem3364838 _87451 x s x' t t' h1 h2 h4)). Qed.
Lemma lem3364850 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (x : _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term125 _87451 t s x') (h3 : term73 _87451 t' x) (h4 : t t') : term244.
Proof. exact (fun h0 : ~ False => @lem3364849 _87451 s x' x t t' h1 h2 h3 h4). Qed.
Lemma lem3364852 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3364853 : term244 = False.
Proof. exact (@lem3364852 False). Qed.
Lemma lem3364854 {_87451 : Type'} (s : type686 _87451) (x' : type672 _87451) (x : _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term125 _87451 t s x') (h3 : term73 _87451 t' x) (h4 : t t') : False.
Proof. exact (EQ_MP (@lem3364853) (@lem3364850 _87451 s x' x t t' h1 h2 h3 h4)). Qed.
Lemma lem3364855 {_87451 : Type'} (s : type686 _87451) (x : _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term43 _87451 t s) (h3 : term73 _87451 t' x) (h4 : t t') : False.
Proof. exact (ex_elim (@lem3364265 _87451 t s h2) (fun x' : type672 _87451 => fun h0 : term127 _87451 t s x' => @lem3364854 _87451 s x' x t t' h1 h0 h3 h4)). Qed.
Lemma lem3364856 {_87451 : Type'} (s : type686 _87451) (x : _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term43 _87451 t s) (h3 : term73 _87451 t' x) (h4 : t t') : (term73 _87451 t' x) = False.
Proof. exact (prop_ext (fun h5 : term73 _87451 t' x => @lem3364855 _87451 s x t t' h1 h2 h3 h4) (fun h5 : False => @lem3364340 _87451 t' x h3)). Qed.
Lemma lem3364857 {_87451 : Type'} (s : type686 _87451) (x : _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term43 _87451 t s) (h3 : term73 _87451 t' x) (h4 : t t') : False.
Proof. exact (EQ_MP (@lem3364856 _87451 s x t t' h1 h2 h3 h4) (@lem3364340 _87451 t' x h3)). Qed.
Lemma lem3364858 {_87451 : Type'} (s : type686 _87451) (x : _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term43 _87451 t s) (h3 : term73 _87451 t' x) (h4 : t t') : (t t') = False.
Proof. exact (prop_ext (fun h5 : t t' => @lem3364857 _87451 s x t t' h1 h2 h3 h4) (fun h5 : False => @lem3364334 _87451 t t' h4)). Qed.
Lemma lem3364859 {_87451 : Type'} (s : type686 _87451) (x : _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term43 _87451 t s) (h3 : term73 _87451 t' x) (h4 : t t') : False.
Proof. exact (EQ_MP (@lem3364858 _87451 s x t t' h1 h2 h3 h4) (@lem3364334 _87451 t t' h4)). Qed.
Lemma lem3364860 {_87451 : Type'} (s : type686 _87451) (x : _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term43 _87451 t s) (h3 : term73 _87451 t' x) (h4 : t t') : (term73 _87451 t' x) = False.
Proof. exact (prop_ext (fun h5 : term73 _87451 t' x => @lem3364859 _87451 s x t t' h1 h2 h3 h4) (fun h5 : False => @lem3364073 _87451 t' x h3)). Qed.
Lemma lem3364861 {_87451 : Type'} (s : type686 _87451) (x : _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term43 _87451 t s) (h3 : term73 _87451 t' x) (h4 : t t') : False.
Proof. exact (EQ_MP (@lem3364860 _87451 s x t t' h1 h2 h3 h4) (@lem3364073 _87451 t' x h3)). Qed.
Lemma lem3364862 {_87451 : Type'} (x : _87451) (s : type686 _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term43 _87451 t s) (h3 : t t') : term72 _87451 t' x.
Proof. exact (fun h0 : term73 _87451 t' x => @lem3364861 _87451 s x t t' h1 h2 h0 h3). Qed.
Lemma lem3364863 {_87451 : Type'} (x : _87451) (s : type686 _87451) (t : type686 _87451) (t' : _87451 -> Prop) (h1 : term51 _87451 s x) (h2 : term43 _87451 t s) (h3 : t t') : t' x.
Proof. exact (EQ_MP (@lem3364072 _87451 t' x) (@lem3364862 _87451 x s t t' h1 h2 h3)). Qed.
Lemma lem3364864 {_87451 : Type'} (t' : _87451 -> Prop) (x : _87451) (t : type686 _87451) (s : type686 _87451) (h1 : term51 _87451 s x) (h2 : term43 _87451 t s) : term48 _87451 t t' x.
Proof. exact (fun h0 : t t' => @lem3364863 _87451 x s t t' h1 h2 h0). Qed.
Lemma lem3364869 {_87451 : Type'} (x : _87451) (t : type686 _87451) (s : type686 _87451) (h1 : term51 _87451 s x) (h2 : term43 _87451 t s) : term51 _87451 t x.
Proof. exact (fun t' : _87451 -> Prop => @lem3364864 _87451 t' x t s h1 h2). Qed.
Lemma lem3364870 {_87451 : Type'} (x : _87451) (t : type686 _87451) (s : type686 _87451) (h1 : term43 _87451 t s) : term55 _87451 s t x.
Proof. exact (fun h0 : term51 _87451 s x => @lem3364869 _87451 x t s h0 h1). Qed.
Lemma lem3364875 {_87451 : Type'} (t : type686 _87451) (s : type686 _87451) (h1 : term43 _87451 t s) : term58 _87451 s t.
Proof. exact (fun x : _87451 => @lem3364870 _87451 x t s h1). Qed.
Lemma lem3364876 {_87451 : Type'} (s : type686 _87451) (t : type686 _87451) : term59 _87451 s t.
Proof. exact (fun h0 : term43 _87451 t s => @lem3364875 _87451 t s h0). Qed.
Lemma lem3364881 {_87451 : Type'} (s : type686 _87451) : term61 _87451 s.
Proof. exact (fun t : type686 _87451 => @lem3364876 _87451 s t). Qed.
Lemma lem3364886 {_87451 : Type'} : term63 _87451.
Proof. exact (fun s : type686 _87451 => @lem3364881 _87451 s). Qed.
Lemma lem3364887 {_87451 : Type'} : term65 _87451.
Proof. exact (EQ_MP (@lem3364065 _87451) (@lem3364886 _87451)). Qed.
Lemma lem3364889 {_87451 : Type'} : term65 _87451.
Proof. exact (@lem3363865 _87451 (@lem3364887 _87451)). Qed.
Lemma lem3364890 {_87451 : Type'} (h1 : term66 _87451) : False.
Proof. exact (@lem3364889 _87451 (@lem3363849 _87451 h1)). Qed.
Lemma lem3364891 {_87451 : Type'} (h1 : term66 _87451) : (term66 _87451) = False.
Proof. exact (prop_ext (fun h2 : term66 _87451 => @lem3364890 _87451 h1) (fun h2 : False => @lem3363849 _87451 h1)). Qed.
Lemma lem3364892 {_87451 : Type'} (h1 : term66 _87451) : False.
Proof. exact (EQ_MP (@lem3364891 _87451 h1) (@lem3363849 _87451 h1)). Qed.
Lemma lem3364893 {_87451 : Type'} : term65 _87451.
Proof. exact (fun h0 : term66 _87451 => @lem3364892 _87451 h0). Qed.
Lemma lem3364894 {_87451 : Type'} : term63 _87451.
Proof. exact (EQ_MP (@lem3363848 _87451) (@lem3364893 _87451)). Qed.
Lemma lem3364895 {_87451 : Type'} : term28 _87451.
Proof. exact (EQ_MP (@lem3363844 _87451) (@lem3364894 _87451)). Qed.
Lemma lem3364896 {_87451 : Type'} : term27 _87451.
Proof. exact (EQ_MP (@lem3363665 _87451) (@lem3364895 _87451)). Qed.
