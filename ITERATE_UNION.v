Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_UNION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FINITE_UNION_spec.
Require Import IN_UNION_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import UNION_EMPTY_spec.
Require Import monoidal_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1833_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19024_spec.
Require Import thm19025_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm196_spec.
Require Import thm197_spec.
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
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
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
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem5753581 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5753582 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (s = t) = (term0 _120557 s t).
Proof. exact (@lem5753581 _120557 s t). Qed.
Lemma lem5753583 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term1 _120557 s x t) = (term2 _120557 x s t)) = (term3 _120557 x s t).
Proof. exact (@lem5753582 _120557 (term1 _120557 s x t) (term2 _120557 x s t)). Qed.
Lemma lem5753592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5753593 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term4 _120557 x s t) = (term5 _120557 x s t).
Proof. exact (MK_COMB (@lem5753592) (@lem5753583 _120557 x s t)). Qed.
Lemma lem5753599 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem5753600 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (@DISJOINT _120557 s t) = ((@INTER _120557 s t) = (@EMPTY _120557)).
Proof. exact (@lem5753599 _120557 s t). Qed.
Lemma lem5753601 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term6 _120557 s x t) = ((term7 _120557 s x t) = (@EMPTY _120557)).
Proof. exact (@lem5753600 _120557 s (@INSERT _120557 x t)). Qed.
Lemma lem5753605 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5753606 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (s = t) = (term0 _120557 s t).
Proof. exact (@lem5753605 _120557 s t). Qed.
Lemma lem5753607 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : ((term7 _120557 s x t) = (@EMPTY _120557)) = (term8 _120557 s x t).
Proof. exact (@lem5753606 _120557 (term7 _120557 s x t) (@EMPTY _120557)). Qed.
Lemma lem5753612 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term6 _120557 s x t) = (term8 _120557 s x t).
Proof. exact (TRANS (@lem5753601 _120557 s x t) (@lem5753607 _120557 s x t)). Qed.
Lemma lem5753617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5753618 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term9 _120557 s x t) = (term10 _120557 s x t).
Proof. exact (MK_COMB (@lem5753617) (@lem5753612 _120557 s x t)). Qed.
Lemma lem5753622 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem5753623 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (@DISJOINT _120557 s t) = ((@INTER _120557 s t) = (@EMPTY _120557)).
Proof. exact (@lem5753622 _120557 s t). Qed.
Lemma lem5753627 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5753628 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (s = t) = (term0 _120557 s t).
Proof. exact (@lem5753627 _120557 s t). Qed.
Lemma lem5753629 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : ((@INTER _120557 s t) = (@EMPTY _120557)) = (term11 _120557 s t).
Proof. exact (@lem5753628 _120557 (@INTER _120557 s t) (@EMPTY _120557)). Qed.
Lemma lem5753634 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (@DISJOINT _120557 s t) = (term11 _120557 s t).
Proof. exact (TRANS (@lem5753623 _120557 s t) (@lem5753629 _120557 s t)). Qed.
Lemma lem5753639 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) : (term12 _120557 x s) = (term12 _120557 x s).
Proof. exact (eq_refl (term12 _120557 x s)). Qed.
Lemma lem5753640 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term13 _120557 x s t) = (term14 _120557 x s t).
Proof. exact (MK_COMB (@lem5753639 _120557 x s) (@lem5753634 _120557 s t)). Qed.
Lemma lem5753643 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term6 _120557 s x t) = (term13 _120557 x s t)) = ((term8 _120557 s x t) = (term14 _120557 x s t)).
Proof. exact (MK_COMB (@lem5753618 _120557 s x t) (@lem5753640 _120557 x s t)). Qed.
Lemma lem5753648 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term15 _120557 x s t) = (term16 _120557 x s t).
Proof. exact (MK_COMB (@lem5753593 _120557 x s t) (@lem5753643 _120557 x s t)). Qed.
Lemma lem5753651 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term16 _120557 x s t) = (term15 _120557 x s t).
Proof. exact (SYM (@lem5753648 _120557 x s t)). Qed.
Lemma lem5753661 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term17 A x s t) = (term18 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem5753662 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term17 _120557 x s t) = (term18 _120557 s x t).
Proof. exact (@lem5753661 _120557 s x t). Qed.
Lemma lem5753663 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) (x : _120557) (t : _120557 -> Prop) : (term19 _120557 x' s x t) = (term20 _120557 s x' x t).
Proof. exact (@lem5753662 _120557 s x' (@INSERT _120557 x t)). Qed.
Lemma lem5753667 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5753668 {_120557 : Type'} (P : _120557 -> Prop) (x : _120557) : (@IN _120557 x P) = (P x).
Proof. exact (@lem5753667 _120557 P x). Qed.
Lemma lem5753669 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (@IN _120557 x' s) = (s x').
Proof. exact (@lem5753668 _120557 s x'). Qed.
Lemma lem5753670 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5753671 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (term21 _120557 x' s) = (term22 _120557 s x').
Proof. exact (MK_COMB (@lem5753670) (@lem5753669 _120557 s x')). Qed.
Lemma lem5753673 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term23 A x y s) = (term24 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5753674 {_120557 : Type'} (y : _120557) (x : _120557) (s : _120557 -> Prop) : (term23 _120557 x y s) = (term24 _120557 y x s).
Proof. exact (@lem5753673 _120557 y x s). Qed.
Lemma lem5753675 {_120557 : Type'} (x : _120557) (x' : _120557) (t : _120557 -> Prop) : (term23 _120557 x' x t) = (term24 _120557 x x' t).
Proof. exact (@lem5753674 _120557 x x' t). Qed.
Lemma lem5753681 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5753682 {_120557 : Type'} (P : _120557 -> Prop) (x : _120557) : (@IN _120557 x P) = (P x).
Proof. exact (@lem5753681 _120557 P x). Qed.
Lemma lem5753683 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) : (@IN _120557 x' t) = (t x').
Proof. exact (@lem5753682 _120557 t x'). Qed.
Lemma lem5753684 {_120557 : Type'} (x' : _120557) (x : _120557) : (term25 _120557 x' x) = (term25 _120557 x' x).
Proof. exact (eq_refl (term25 _120557 x' x)). Qed.
Lemma lem5753685 {_120557 : Type'} (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term24 _120557 x x' t) = (term26 _120557 x t x').
Proof. exact (MK_COMB (@lem5753684 _120557 x' x) (@lem5753683 _120557 t x')). Qed.
Lemma lem5753688 {_120557 : Type'} (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term23 _120557 x' x t) = (term26 _120557 x t x').
Proof. exact (TRANS (@lem5753675 _120557 x x' t) (@lem5753685 _120557 x t x')). Qed.
Lemma lem5753689 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term20 _120557 s x' x t) = (term27 _120557 s x t x').
Proof. exact (MK_COMB (@lem5753671 _120557 s x') (@lem5753688 _120557 x t x')). Qed.
Lemma lem5753692 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term19 _120557 x' s x t) = (term27 _120557 s x t x').
Proof. exact (TRANS (@lem5753663 _120557 s x' x t) (@lem5753689 _120557 s x t x')). Qed.
Lemma lem5753693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5753694 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term28 _120557 x' s x t) = (term29 _120557 s x t x').
Proof. exact (MK_COMB (@lem5753693) (@lem5753692 _120557 s x t x')). Qed.
Lemma lem5753696 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term23 A x y s) = (term24 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5753697 {_120557 : Type'} (y : _120557) (x : _120557) (s : _120557 -> Prop) : (term23 _120557 x y s) = (term24 _120557 y x s).
Proof. exact (@lem5753696 _120557 y x s). Qed.
Lemma lem5753698 {_120557 : Type'} (x : _120557) (x' : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term30 _120557 x' x s t) = (term31 _120557 x x' s t).
Proof. exact (@lem5753697 _120557 x x' (@UNION _120557 s t)). Qed.
Lemma lem5753704 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term17 A x s t) = (term18 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem5753705 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term17 _120557 x s t) = (term18 _120557 s x t).
Proof. exact (@lem5753704 _120557 s x t). Qed.
Lemma lem5753706 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) (t : _120557 -> Prop) : (term17 _120557 x' s t) = (term18 _120557 s x' t).
Proof. exact (@lem5753705 _120557 s x' t). Qed.
Lemma lem5753710 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5753711 {_120557 : Type'} (P : _120557 -> Prop) (x : _120557) : (@IN _120557 x P) = (P x).
Proof. exact (@lem5753710 _120557 P x). Qed.
Lemma lem5753712 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (@IN _120557 x' s) = (s x').
Proof. exact (@lem5753711 _120557 s x'). Qed.
Lemma lem5753713 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5753714 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (term21 _120557 x' s) = (term22 _120557 s x').
Proof. exact (MK_COMB (@lem5753713) (@lem5753712 _120557 s x')). Qed.
Lemma lem5753716 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5753717 {_120557 : Type'} (P : _120557 -> Prop) (x : _120557) : (@IN _120557 x P) = (P x).
Proof. exact (@lem5753716 _120557 P x). Qed.
Lemma lem5753718 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) : (@IN _120557 x' t) = (t x').
Proof. exact (@lem5753717 _120557 t x'). Qed.
Lemma lem5753719 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term18 _120557 s x' t) = (term32 _120557 s t x').
Proof. exact (MK_COMB (@lem5753714 _120557 s x') (@lem5753718 _120557 t x')). Qed.
Lemma lem5753722 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term17 _120557 x' s t) = (term32 _120557 s t x').
Proof. exact (TRANS (@lem5753706 _120557 s x' t) (@lem5753719 _120557 s t x')). Qed.
Lemma lem5753723 {_120557 : Type'} (x' : _120557) (x : _120557) : (term25 _120557 x' x) = (term25 _120557 x' x).
Proof. exact (eq_refl (term25 _120557 x' x)). Qed.
Lemma lem5753724 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term31 _120557 x x' s t) = (term33 _120557 x s t x').
Proof. exact (MK_COMB (@lem5753723 _120557 x' x) (@lem5753722 _120557 s t x')). Qed.
Lemma lem5753727 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term30 _120557 x' x s t) = (term33 _120557 x s t x').
Proof. exact (TRANS (@lem5753698 _120557 x x' s t) (@lem5753724 _120557 x s t x')). Qed.
Lemma lem5753728 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : ((term19 _120557 x' s x t) = (term30 _120557 x' x s t)) = ((term27 _120557 s x t x') = (term33 _120557 x s t x')).
Proof. exact (MK_COMB (@lem5753694 _120557 s x t x') (@lem5753727 _120557 x s t x')). Qed.
Lemma lem5753731 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term34 _120557 x s t) = (term35 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5753728 _120557 x s t x')). Qed.
Lemma lem5753732 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5753733 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term3 _120557 x s t) = (term36 _120557 x s t).
Proof. exact (MK_COMB (@lem5753732 _120557) (@lem5753731 _120557 x s t)). Qed.
Lemma lem5753738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5753739 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term5 _120557 x s t) = (term37 _120557 x s t).
Proof. exact (MK_COMB (@lem5753738) (@lem5753733 _120557 x s t)). Qed.
Lemma lem5753749 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term38 A x s t) = (term39 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem5753750 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term38 _120557 x s t) = (term39 _120557 s x t).
Proof. exact (@lem5753749 _120557 s x t). Qed.
Lemma lem5753751 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) (x : _120557) (t : _120557 -> Prop) : (term40 _120557 x' s x t) = (term41 _120557 s x' x t).
Proof. exact (@lem5753750 _120557 s x' (@INSERT _120557 x t)). Qed.
Lemma lem5753755 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5753756 {_120557 : Type'} (P : _120557 -> Prop) (x : _120557) : (@IN _120557 x P) = (P x).
Proof. exact (@lem5753755 _120557 P x). Qed.
Lemma lem5753757 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (@IN _120557 x' s) = (s x').
Proof. exact (@lem5753756 _120557 s x'). Qed.
Lemma lem5753758 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5753759 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (term42 _120557 x' s) = (term43 _120557 s x').
Proof. exact (MK_COMB (@lem5753758) (@lem5753757 _120557 s x')). Qed.
Lemma lem5753761 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term23 A x y s) = (term24 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5753762 {_120557 : Type'} (y : _120557) (x : _120557) (s : _120557 -> Prop) : (term23 _120557 x y s) = (term24 _120557 y x s).
Proof. exact (@lem5753761 _120557 y x s). Qed.
Lemma lem5753763 {_120557 : Type'} (x : _120557) (x' : _120557) (t : _120557 -> Prop) : (term23 _120557 x' x t) = (term24 _120557 x x' t).
Proof. exact (@lem5753762 _120557 x x' t). Qed.
Lemma lem5753769 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5753770 {_120557 : Type'} (P : _120557 -> Prop) (x : _120557) : (@IN _120557 x P) = (P x).
Proof. exact (@lem5753769 _120557 P x). Qed.
Lemma lem5753771 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) : (@IN _120557 x' t) = (t x').
Proof. exact (@lem5753770 _120557 t x'). Qed.
Lemma lem5753772 {_120557 : Type'} (x' : _120557) (x : _120557) : (term25 _120557 x' x) = (term25 _120557 x' x).
Proof. exact (eq_refl (term25 _120557 x' x)). Qed.
Lemma lem5753773 {_120557 : Type'} (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term24 _120557 x x' t) = (term26 _120557 x t x').
Proof. exact (MK_COMB (@lem5753772 _120557 x' x) (@lem5753771 _120557 t x')). Qed.
Lemma lem5753776 {_120557 : Type'} (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term23 _120557 x' x t) = (term26 _120557 x t x').
Proof. exact (TRANS (@lem5753763 _120557 x x' t) (@lem5753773 _120557 x t x')). Qed.
Lemma lem5753777 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term41 _120557 s x' x t) = (term44 _120557 s x t x').
Proof. exact (MK_COMB (@lem5753759 _120557 s x') (@lem5753776 _120557 x t x')). Qed.
Lemma lem5753780 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term40 _120557 x' s x t) = (term44 _120557 s x t x').
Proof. exact (TRANS (@lem5753751 _120557 s x' x t) (@lem5753777 _120557 s x t x')). Qed.
Lemma lem5753781 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5753782 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term45 _120557 x' s x t) = (term46 _120557 s x t x').
Proof. exact (MK_COMB (@lem5753781) (@lem5753780 _120557 s x t x')). Qed.
Lemma lem5753784 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5753785 {_120557 : Type'} (x : _120557) : (@IN _120557 x (@EMPTY _120557)) = False.
Proof. exact (@lem5753784 _120557 x). Qed.
Lemma lem5753786 {_120557 : Type'} (x' : _120557) : (@IN _120557 x' (@EMPTY _120557)) = False.
Proof. exact (@lem5753785 _120557 x'). Qed.
Lemma lem5753787 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : ((term40 _120557 x' s x t) = (@IN _120557 x' (@EMPTY _120557))) = ((term44 _120557 s x t x') = False).
Proof. exact (MK_COMB (@lem5753782 _120557 s x t x') (@lem5753786 _120557 x')). Qed.
Lemma lem5753789 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5753790 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : ((term44 _120557 s x t x') = False) = (term47 _120557 s x t x').
Proof. exact (@lem5753789 (term44 _120557 s x t x')). Qed.
Lemma lem5753797 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : ((term40 _120557 x' s x t) = (@IN _120557 x' (@EMPTY _120557))) = (term47 _120557 s x t x').
Proof. exact (TRANS (@lem5753787 _120557 s x t x') (@lem5753790 _120557 s x t x')). Qed.
Lemma lem5753798 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term48 _120557 s x t) = (term49 _120557 s x t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5753797 _120557 s x t x')). Qed.
Lemma lem5753799 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5753800 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term8 _120557 s x t) = (term50 _120557 s x t).
Proof. exact (MK_COMB (@lem5753799 _120557) (@lem5753798 _120557 s x t)). Qed.
Lemma lem5753805 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5753806 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term10 _120557 s x t) = (term51 _120557 s x t).
Proof. exact (MK_COMB (@lem5753805) (@lem5753800 _120557 s x t)). Qed.
Lemma lem5753810 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5753811 {_120557 : Type'} (P : _120557 -> Prop) (x : _120557) : (@IN _120557 x P) = (P x).
Proof. exact (@lem5753810 _120557 P x). Qed.
Lemma lem5753812 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (@IN _120557 x s) = (s x).
Proof. exact (@lem5753811 _120557 s x). Qed.
Lemma lem5753813 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5753814 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (term52 _120557 x s) = (term53 _120557 s x).
Proof. exact (MK_COMB (@lem5753813) (@lem5753812 _120557 s x)). Qed.
Lemma lem5753815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5753816 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (term12 _120557 x s) = (term54 _120557 s x).
Proof. exact (MK_COMB (@lem5753815) (@lem5753814 _120557 s x)). Qed.
Lemma lem5753824 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term38 A x s t) = (term39 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem5753825 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term38 _120557 x s t) = (term39 _120557 s x t).
Proof. exact (@lem5753824 _120557 s x t). Qed.
Lemma lem5753829 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5753830 {_120557 : Type'} (P : _120557 -> Prop) (x : _120557) : (@IN _120557 x P) = (P x).
Proof. exact (@lem5753829 _120557 P x). Qed.
Lemma lem5753831 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (@IN _120557 x s) = (s x).
Proof. exact (@lem5753830 _120557 s x). Qed.
Lemma lem5753832 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5753833 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (term42 _120557 x s) = (term43 _120557 s x).
Proof. exact (MK_COMB (@lem5753832) (@lem5753831 _120557 s x)). Qed.
Lemma lem5753835 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5753836 {_120557 : Type'} (P : _120557 -> Prop) (x : _120557) : (@IN _120557 x P) = (P x).
Proof. exact (@lem5753835 _120557 P x). Qed.
Lemma lem5753837 {_120557 : Type'} (t : _120557 -> Prop) (x : _120557) : (@IN _120557 x t) = (t x).
Proof. exact (@lem5753836 _120557 t x). Qed.
Lemma lem5753838 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : (term39 _120557 s x t) = (term55 _120557 s t x).
Proof. exact (MK_COMB (@lem5753833 _120557 s x) (@lem5753837 _120557 t x)). Qed.
Lemma lem5753841 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : (term38 _120557 x s t) = (term55 _120557 s t x).
Proof. exact (TRANS (@lem5753825 _120557 s x t) (@lem5753838 _120557 s t x)). Qed.
Lemma lem5753842 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5753843 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : (term56 _120557 x s t) = (term57 _120557 s t x).
Proof. exact (MK_COMB (@lem5753842) (@lem5753841 _120557 s t x)). Qed.
Lemma lem5753845 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5753846 {_120557 : Type'} (x : _120557) : (@IN _120557 x (@EMPTY _120557)) = False.
Proof. exact (@lem5753845 _120557 x). Qed.
Lemma lem5753847 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : ((term38 _120557 x s t) = (@IN _120557 x (@EMPTY _120557))) = ((term55 _120557 s t x) = False).
Proof. exact (MK_COMB (@lem5753843 _120557 s t x) (@lem5753846 _120557 x)). Qed.
Lemma lem5753849 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5753850 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : ((term55 _120557 s t x) = False) = (term58 _120557 s t x).
Proof. exact (@lem5753849 (term55 _120557 s t x)). Qed.
Lemma lem5753853 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : ((term38 _120557 x s t) = (@IN _120557 x (@EMPTY _120557))) = (term58 _120557 s t x).
Proof. exact (TRANS (@lem5753847 _120557 s t x) (@lem5753850 _120557 s t x)). Qed.
Lemma lem5753854 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term59 _120557 s t) = (term60 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5753853 _120557 s t x)). Qed.
Lemma lem5753855 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5753856 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term11 _120557 s t) = (term61 _120557 s t).
Proof. exact (MK_COMB (@lem5753855 _120557) (@lem5753854 _120557 s t)). Qed.
Lemma lem5753861 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term14 _120557 x s t) = (term62 _120557 x s t).
Proof. exact (MK_COMB (@lem5753816 _120557 s x) (@lem5753856 _120557 s t)). Qed.
Lemma lem5753864 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term8 _120557 s x t) = (term14 _120557 x s t)) = ((term50 _120557 s x t) = (term62 _120557 x s t)).
Proof. exact (MK_COMB (@lem5753806 _120557 s x t) (@lem5753861 _120557 x s t)). Qed.
Lemma lem5753867 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term16 _120557 x s t) = (term63 _120557 x s t).
Proof. exact (MK_COMB (@lem5753739 _120557 x s t) (@lem5753864 _120557 x s t)). Qed.
Lemma lem5753870 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term63 _120557 x s t) = (term16 _120557 x s t).
Proof. exact (SYM (@lem5753867 _120557 x s t)). Qed.
Lemma lem5753872 (p : Prop) : p = (term64 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5753873 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term63 _120557 x s t) = (term65 _120557 x s t).
Proof. exact (@lem5753872 (term63 _120557 x s t)). Qed.
Lemma lem5753874 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term65 _120557 x s t) = (term63 _120557 x s t).
Proof. exact (SYM (@lem5753873 _120557 x s t)). Qed.
Lemma lem5753875 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term66 _120557 x s t) : term66 _120557 x s t.
Proof. exact (h1). Qed.
Lemma lem5753878 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term65 _120557 x s t) : term65 _120557 x s t.
Proof. exact (h1). Qed.
Lemma lem5753879 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : term67 _120557 x s t.
Proof. exact (fun h0 : term65 _120557 x s t => @lem5753878 _120557 x s t h0). Qed.
Lemma lem5753880 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term67 _120557 x s t) : term67 _120557 x s t.
Proof. exact (h1). Qed.
Lemma lem5753881 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term65 _120557 x s t) : term65 _120557 x s t.
Proof. exact (h1). Qed.
Lemma lem5753882 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term65 _120557 x s t) (h2 : term67 _120557 x s t) : term65 _120557 x s t.
Proof. exact (@lem5753880 _120557 x s t h2 (@lem5753881 _120557 x s t h1)). Qed.
Lemma lem5753883 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term65 _120557 x s t) : term68 _120557 x s t.
Proof. exact (fun h0 : term67 _120557 x s t => @lem5753882 _120557 x s t h1 h0). Qed.
Lemma lem5753884 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term67 _120557 x s t) : term67 _120557 x s t.
Proof. exact (h1). Qed.
Lemma lem5753885 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term65 _120557 x s t) (h2 : term67 _120557 x s t) : term65 _120557 x s t.
Proof. exact (@lem5753883 _120557 x s t h1 (@lem5753884 _120557 x s t h2)). Qed.
Lemma lem5753886 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term67 _120557 x s t) : term67 _120557 x s t.
Proof. exact (fun h0 : term65 _120557 x s t => @lem5753885 _120557 x s t h0 h1). Qed.
Lemma lem5753887 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : term69 _120557 x s t.
Proof. exact (fun h0 : term67 _120557 x s t => @lem5753886 _120557 x s t h0). Qed.
Lemma lem5753890 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : term67 _120557 x s t.
Proof. exact (@lem5753887 _120557 x s t (@lem5753879 _120557 x s t)). Qed.
Lemma lem5753891 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : term67 _120557 x s t.
Proof. exact (@lem5753890 _120557 x s t). Qed.
Lemma lem5753905 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5753906 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term65 _120557 x s t) = (term70 _120557 x s t).
Proof. exact (@lem5753905 (term66 _120557 x s t)). Qed.
Lemma lem5753908 (t : Prop) : (term71 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5753909 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term70 _120557 x s t) = (term63 _120557 x s t).
Proof. exact (@lem5753908 (term63 _120557 x s t)). Qed.
Lemma lem5753912 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term65 _120557 x s t) = (term63 _120557 x s t).
Proof. exact (TRANS (@lem5753906 _120557 x s t) (@lem5753909 _120557 x s t)). Qed.
Lemma lem5753941 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term72 _120557 s t) = (term73 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5753912 _120557 x s t)). Qed.
Lemma lem5753942 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5753943 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term74 _120557 s t) = (term75 _120557 s t).
Proof. exact (MK_COMB (@lem5753942 _120557) (@lem5753941 _120557 s t)). Qed.
Lemma lem5753945 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem5753946 {_120557 : Type'} (P : _120557 -> Prop) (Q : _120557 -> Prop) : (term76 _120557 P Q) = (term77 _120557 P Q).
Proof. exact (@lem5753945 _120557 P Q). Qed.
Lemma lem5753947 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term78 _120557 s t) = (term79 _120557 s t).
Proof. exact (@lem5753946 _120557 (term80 _120557 s t) (term81 _120557 s t)). Qed.
Lemma lem5753948 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term82 _120557 s t x) = (term36 _120557 x s t).
Proof. exact (eq_refl (term82 _120557 s t x)). Qed.
Lemma lem5753949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5753950 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term83 _120557 s t x) = (term37 _120557 x s t).
Proof. exact (MK_COMB (@lem5753949) (@lem5753948 _120557 x s t)). Qed.
Lemma lem5753951 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term84 _120557 s t x) = ((term50 _120557 s x t) = (term62 _120557 x s t)).
Proof. exact (eq_refl (term84 _120557 s t x)). Qed.
Lemma lem5753952 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term85 _120557 s t x) = (term63 _120557 x s t).
Proof. exact (MK_COMB (@lem5753950 _120557 x s t) (@lem5753951 _120557 x s t)). Qed.
Lemma lem5753953 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term86 _120557 s t) = (term73 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5753952 _120557 x s t)). Qed.
Lemma lem5753954 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5753955 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term78 _120557 s t) = (term75 _120557 s t).
Proof. exact (MK_COMB (@lem5753954 _120557) (@lem5753953 _120557 s t)). Qed.
Lemma lem5753956 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5753957 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term87 _120557 s t) = (term88 _120557 s t).
Proof. exact (MK_COMB (@lem5753956) (@lem5753955 _120557 s t)). Qed.
Lemma lem5753958 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term82 _120557 s t x) = (term36 _120557 x s t).
Proof. exact (eq_refl (term82 _120557 s t x)). Qed.
Lemma lem5753959 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term89 _120557 s t) = (term80 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5753958 _120557 x s t)). Qed.
Lemma lem5753960 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5753961 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term90 _120557 s t) = (term91 _120557 s t).
Proof. exact (MK_COMB (@lem5753960 _120557) (@lem5753959 _120557 s t)). Qed.
Lemma lem5753962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5753963 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term92 _120557 s t) = (term93 _120557 s t).
Proof. exact (MK_COMB (@lem5753962) (@lem5753961 _120557 s t)). Qed.
Lemma lem5753964 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term84 _120557 s t x) = ((term50 _120557 s x t) = (term62 _120557 x s t)).
Proof. exact (eq_refl (term84 _120557 s t x)). Qed.
Lemma lem5753965 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term94 _120557 s t) = (term81 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5753964 _120557 x s t)). Qed.
Lemma lem5753966 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5753967 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term95 _120557 s t) = (term96 _120557 s t).
Proof. exact (MK_COMB (@lem5753966 _120557) (@lem5753965 _120557 s t)). Qed.
Lemma lem5753968 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term79 _120557 s t) = (term97 _120557 s t).
Proof. exact (MK_COMB (@lem5753963 _120557 s t) (@lem5753967 _120557 s t)). Qed.
Lemma lem5753969 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term78 _120557 s t) = (term79 _120557 s t)) = ((term75 _120557 s t) = (term97 _120557 s t)).
Proof. exact (MK_COMB (@lem5753957 _120557 s t) (@lem5753968 _120557 s t)). Qed.
Lemma lem5753970 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term75 _120557 s t) = (term97 _120557 s t).
Proof. exact (EQ_MP (@lem5753969 _120557 s t) (@lem5753947 _120557 s t)). Qed.
Lemma lem5754009 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term74 _120557 s t) = (term97 _120557 s t).
Proof. exact (TRANS (@lem5753943 _120557 s t) (@lem5753970 _120557 s t)). Qed.
Lemma lem5754010 {_120557 : Type'} (t : _120557 -> Prop) : (term98 _120557 t) = (term99 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5754009 _120557 s t)). Qed.
Lemma lem5754011 {_120557 : Type'} : (@all (_120557 -> Prop)) = (@all (_120557 -> Prop)).
Proof. exact (eq_refl (@all (_120557 -> Prop))). Qed.
Lemma lem5754012 {_120557 : Type'} (t : _120557 -> Prop) : (term100 _120557 t) = (term101 _120557 t).
Proof. exact (MK_COMB (@lem5754011 _120557) (@lem5754010 _120557 t)). Qed.
Lemma lem5754014 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem5754015 {_120557 : Type'} (P : type686 _120557) (Q : type686 _120557) : (term102 _120557 P Q) = (term103 _120557 P Q).
Proof. exact (@lem5754014 (_120557 -> Prop) P Q). Qed.
Lemma lem5754016 {_120557 : Type'} (t : _120557 -> Prop) : (term104 _120557 t) = (term105 _120557 t).
Proof. exact (@lem5754015 _120557 (term106 _120557 t) (term107 _120557 t)). Qed.
Lemma lem5754017 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term108 _120557 t s) = (term91 _120557 s t).
Proof. exact (eq_refl (term108 _120557 t s)). Qed.
Lemma lem5754018 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5754019 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term109 _120557 t s) = (term93 _120557 s t).
Proof. exact (MK_COMB (@lem5754018) (@lem5754017 _120557 s t)). Qed.
Lemma lem5754020 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term110 _120557 t s) = (term96 _120557 s t).
Proof. exact (eq_refl (term110 _120557 t s)). Qed.
Lemma lem5754021 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term111 _120557 t s) = (term97 _120557 s t).
Proof. exact (MK_COMB (@lem5754019 _120557 s t) (@lem5754020 _120557 s t)). Qed.
Lemma lem5754022 {_120557 : Type'} (t : _120557 -> Prop) : (term112 _120557 t) = (term99 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5754021 _120557 s t)). Qed.
Lemma lem5754023 {_120557 : Type'} : (@all (_120557 -> Prop)) = (@all (_120557 -> Prop)).
Proof. exact (eq_refl (@all (_120557 -> Prop))). Qed.
Lemma lem5754024 {_120557 : Type'} (t : _120557 -> Prop) : (term104 _120557 t) = (term101 _120557 t).
Proof. exact (MK_COMB (@lem5754023 _120557) (@lem5754022 _120557 t)). Qed.
Lemma lem5754025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5754026 {_120557 : Type'} (t : _120557 -> Prop) : (term113 _120557 t) = (term114 _120557 t).
Proof. exact (MK_COMB (@lem5754025) (@lem5754024 _120557 t)). Qed.
Lemma lem5754027 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term108 _120557 t s) = (term91 _120557 s t).
Proof. exact (eq_refl (term108 _120557 t s)). Qed.
Lemma lem5754028 {_120557 : Type'} (t : _120557 -> Prop) : (term115 _120557 t) = (term106 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5754027 _120557 s t)). Qed.
Lemma lem5754029 {_120557 : Type'} : (@all (_120557 -> Prop)) = (@all (_120557 -> Prop)).
Proof. exact (eq_refl (@all (_120557 -> Prop))). Qed.
Lemma lem5754030 {_120557 : Type'} (t : _120557 -> Prop) : (term116 _120557 t) = (term117 _120557 t).
Proof. exact (MK_COMB (@lem5754029 _120557) (@lem5754028 _120557 t)). Qed.
Lemma lem5754031 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5754032 {_120557 : Type'} (t : _120557 -> Prop) : (term118 _120557 t) = (term119 _120557 t).
Proof. exact (MK_COMB (@lem5754031) (@lem5754030 _120557 t)). Qed.
Lemma lem5754033 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term110 _120557 t s) = (term96 _120557 s t).
Proof. exact (eq_refl (term110 _120557 t s)). Qed.
Lemma lem5754034 {_120557 : Type'} (t : _120557 -> Prop) : (term120 _120557 t) = (term107 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5754033 _120557 s t)). Qed.
Lemma lem5754035 {_120557 : Type'} : (@all (_120557 -> Prop)) = (@all (_120557 -> Prop)).
Proof. exact (eq_refl (@all (_120557 -> Prop))). Qed.
Lemma lem5754036 {_120557 : Type'} (t : _120557 -> Prop) : (term121 _120557 t) = (term122 _120557 t).
Proof. exact (MK_COMB (@lem5754035 _120557) (@lem5754034 _120557 t)). Qed.
Lemma lem5754037 {_120557 : Type'} (t : _120557 -> Prop) : (term105 _120557 t) = (term123 _120557 t).
Proof. exact (MK_COMB (@lem5754032 _120557 t) (@lem5754036 _120557 t)). Qed.
Lemma lem5754038 {_120557 : Type'} (t : _120557 -> Prop) : ((term104 _120557 t) = (term105 _120557 t)) = ((term101 _120557 t) = (term123 _120557 t)).
Proof. exact (MK_COMB (@lem5754026 _120557 t) (@lem5754037 _120557 t)). Qed.
Lemma lem5754039 {_120557 : Type'} (t : _120557 -> Prop) : (term101 _120557 t) = (term123 _120557 t).
Proof. exact (EQ_MP (@lem5754038 _120557 t) (@lem5754016 _120557 t)). Qed.
Lemma lem5754086 {_120557 : Type'} (t : _120557 -> Prop) : (term100 _120557 t) = (term123 _120557 t).
Proof. exact (TRANS (@lem5754012 _120557 t) (@lem5754039 _120557 t)). Qed.
Lemma lem5754087 {_120557 : Type'} : (term124 _120557) = (term125 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5754086 _120557 t)). Qed.
Lemma lem5754088 {_120557 : Type'} : (@all (_120557 -> Prop)) = (@all (_120557 -> Prop)).
Proof. exact (eq_refl (@all (_120557 -> Prop))). Qed.
Lemma lem5754089 {_120557 : Type'} : (term126 _120557) = (term127 _120557).
Proof. exact (MK_COMB (@lem5754088 _120557) (@lem5754087 _120557)). Qed.
Lemma lem5754091 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem5754092 {_120557 : Type'} (P : type686 _120557) (Q : type686 _120557) : (term102 _120557 P Q) = (term103 _120557 P Q).
Proof. exact (@lem5754091 (_120557 -> Prop) P Q). Qed.
Lemma lem5754093 {_120557 : Type'} : (term128 _120557) = (term129 _120557).
Proof. exact (@lem5754092 _120557 (term130 _120557) (term131 _120557)). Qed.
Lemma lem5754094 {_120557 : Type'} (t : _120557 -> Prop) : (term132 _120557 t) = (term117 _120557 t).
Proof. exact (eq_refl (term132 _120557 t)). Qed.
Lemma lem5754095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5754096 {_120557 : Type'} (t : _120557 -> Prop) : (term133 _120557 t) = (term119 _120557 t).
Proof. exact (MK_COMB (@lem5754095) (@lem5754094 _120557 t)). Qed.
Lemma lem5754097 {_120557 : Type'} (t : _120557 -> Prop) : (term134 _120557 t) = (term122 _120557 t).
Proof. exact (eq_refl (term134 _120557 t)). Qed.
Lemma lem5754098 {_120557 : Type'} (t : _120557 -> Prop) : (term135 _120557 t) = (term123 _120557 t).
Proof. exact (MK_COMB (@lem5754096 _120557 t) (@lem5754097 _120557 t)). Qed.
Lemma lem5754099 {_120557 : Type'} : (term136 _120557) = (term125 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5754098 _120557 t)). Qed.
Lemma lem5754100 {_120557 : Type'} : (@all (_120557 -> Prop)) = (@all (_120557 -> Prop)).
Proof. exact (eq_refl (@all (_120557 -> Prop))). Qed.
Lemma lem5754101 {_120557 : Type'} : (term128 _120557) = (term127 _120557).
Proof. exact (MK_COMB (@lem5754100 _120557) (@lem5754099 _120557)). Qed.
Lemma lem5754102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5754103 {_120557 : Type'} : (term137 _120557) = (term138 _120557).
Proof. exact (MK_COMB (@lem5754102) (@lem5754101 _120557)). Qed.
Lemma lem5754104 {_120557 : Type'} (t : _120557 -> Prop) : (term132 _120557 t) = (term117 _120557 t).
Proof. exact (eq_refl (term132 _120557 t)). Qed.
Lemma lem5754105 {_120557 : Type'} : (term139 _120557) = (term130 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5754104 _120557 t)). Qed.
Lemma lem5754106 {_120557 : Type'} : (@all (_120557 -> Prop)) = (@all (_120557 -> Prop)).
Proof. exact (eq_refl (@all (_120557 -> Prop))). Qed.
Lemma lem5754107 {_120557 : Type'} : (term140 _120557) = (term141 _120557).
Proof. exact (MK_COMB (@lem5754106 _120557) (@lem5754105 _120557)). Qed.
Lemma lem5754108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5754109 {_120557 : Type'} : (term142 _120557) = (term143 _120557).
Proof. exact (MK_COMB (@lem5754108) (@lem5754107 _120557)). Qed.
Lemma lem5754110 {_120557 : Type'} (t : _120557 -> Prop) : (term134 _120557 t) = (term122 _120557 t).
Proof. exact (eq_refl (term134 _120557 t)). Qed.
Lemma lem5754111 {_120557 : Type'} : (term144 _120557) = (term131 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5754110 _120557 t)). Qed.
Lemma lem5754112 {_120557 : Type'} : (@all (_120557 -> Prop)) = (@all (_120557 -> Prop)).
Proof. exact (eq_refl (@all (_120557 -> Prop))). Qed.
Lemma lem5754113 {_120557 : Type'} : (term145 _120557) = (term146 _120557).
Proof. exact (MK_COMB (@lem5754112 _120557) (@lem5754111 _120557)). Qed.
Lemma lem5754114 {_120557 : Type'} : (term129 _120557) = (term147 _120557).
Proof. exact (MK_COMB (@lem5754109 _120557) (@lem5754113 _120557)). Qed.
Lemma lem5754115 {_120557 : Type'} : ((term128 _120557) = (term129 _120557)) = ((term127 _120557) = (term147 _120557)).
Proof. exact (MK_COMB (@lem5754103 _120557) (@lem5754114 _120557)). Qed.
Lemma lem5754116 {_120557 : Type'} : (term127 _120557) = (term147 _120557).
Proof. exact (EQ_MP (@lem5754115 _120557) (@lem5754093 _120557)). Qed.
Lemma lem5754175 {_120557 : Type'} : (term126 _120557) = (term147 _120557).
Proof. exact (TRANS (@lem5754089 _120557) (@lem5754116 _120557)). Qed.
Lemma lem5754182 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : (term58 _120557 s t x) = (term58 _120557 s t x).
Proof. exact (eq_refl (term58 _120557 s t x)). Qed.
Lemma lem5754183 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term60 _120557 s t) = (term60 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5754182 _120557 s t x)). Qed.
Lemma lem5754184 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5754185 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term61 _120557 s t) = (term61 _120557 s t).
Proof. exact (MK_COMB (@lem5754184 _120557) (@lem5754183 _120557 s t)). Qed.
Lemma lem5754190 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (term54 _120557 s x) = (term54 _120557 s x).
Proof. exact (eq_refl (term54 _120557 s x)). Qed.
Lemma lem5754191 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term62 _120557 x s t) = (term62 _120557 x s t).
Proof. exact (MK_COMB (@lem5754190 _120557 s x) (@lem5754185 _120557 s t)). Qed.
Lemma lem5754202 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term47 _120557 s x t x') = (term47 _120557 s x t x').
Proof. exact (eq_refl (term47 _120557 s x t x')). Qed.
Lemma lem5754203 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term49 _120557 s x t) = (term49 _120557 s x t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5754202 _120557 s x t x')). Qed.
Lemma lem5754204 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5754205 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term50 _120557 s x t) = (term50 _120557 s x t).
Proof. exact (MK_COMB (@lem5754204 _120557) (@lem5754203 _120557 s x t)). Qed.
Lemma lem5754206 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5754207 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term51 _120557 s x t) = (term51 _120557 s x t).
Proof. exact (MK_COMB (@lem5754206) (@lem5754205 _120557 s x t)). Qed.
Lemma lem5754208 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term50 _120557 s x t) = (term62 _120557 x s t)) = ((term50 _120557 s x t) = (term62 _120557 x s t)).
Proof. exact (MK_COMB (@lem5754207 _120557 s x t) (@lem5754191 _120557 x s t)). Qed.
Lemma lem5754209 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term81 _120557 s t) = (term81 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5754208 _120557 x s t)). Qed.
Lemma lem5754210 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5754211 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term96 _120557 s t) = (term96 _120557 s t).
Proof. exact (MK_COMB (@lem5754210 _120557) (@lem5754209 _120557 s t)). Qed.
Lemma lem5754212 {_120557 : Type'} (t : _120557 -> Prop) : (term107 _120557 t) = (term107 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5754211 _120557 s t)). Qed.
Lemma lem5754213 {_120557 : Type'} : (@all (_120557 -> Prop)) = (@all (_120557 -> Prop)).
Proof. exact (eq_refl (@all (_120557 -> Prop))). Qed.
Lemma lem5754214 {_120557 : Type'} (t : _120557 -> Prop) : (term122 _120557 t) = (term122 _120557 t).
Proof. exact (MK_COMB (@lem5754213 _120557) (@lem5754212 _120557 t)). Qed.
Lemma lem5754215 {_120557 : Type'} : (term131 _120557) = (term131 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5754214 _120557 t)). Qed.
Lemma lem5754216 {_120557 : Type'} : (@all (_120557 -> Prop)) = (@all (_120557 -> Prop)).
Proof. exact (eq_refl (@all (_120557 -> Prop))). Qed.
Lemma lem5754217 {_120557 : Type'} : (term146 _120557) = (term146 _120557).
Proof. exact (MK_COMB (@lem5754216 _120557) (@lem5754215 _120557)). Qed.
Lemma lem5754238 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : ((term27 _120557 s x t x') = (term33 _120557 x s t x')) = ((term27 _120557 s x t x') = (term33 _120557 x s t x')).
Proof. exact (eq_refl ((term27 _120557 s x t x') = (term33 _120557 x s t x'))). Qed.
Lemma lem5754239 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term35 _120557 x s t) = (term35 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5754238 _120557 x s t x')). Qed.
Lemma lem5754240 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5754241 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term36 _120557 x s t) = (term36 _120557 x s t).
Proof. exact (MK_COMB (@lem5754240 _120557) (@lem5754239 _120557 x s t)). Qed.
Lemma lem5754242 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term80 _120557 s t) = (term80 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5754241 _120557 x s t)). Qed.
Lemma lem5754243 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5754244 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term91 _120557 s t) = (term91 _120557 s t).
Proof. exact (MK_COMB (@lem5754243 _120557) (@lem5754242 _120557 s t)). Qed.
Lemma lem5754245 {_120557 : Type'} (t : _120557 -> Prop) : (term106 _120557 t) = (term106 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5754244 _120557 s t)). Qed.
Lemma lem5754246 {_120557 : Type'} : (@all (_120557 -> Prop)) = (@all (_120557 -> Prop)).
Proof. exact (eq_refl (@all (_120557 -> Prop))). Qed.
Lemma lem5754247 {_120557 : Type'} (t : _120557 -> Prop) : (term117 _120557 t) = (term117 _120557 t).
Proof. exact (MK_COMB (@lem5754246 _120557) (@lem5754245 _120557 t)). Qed.
Lemma lem5754248 {_120557 : Type'} : (term130 _120557) = (term130 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5754247 _120557 t)). Qed.
Lemma lem5754249 {_120557 : Type'} : (@all (_120557 -> Prop)) = (@all (_120557 -> Prop)).
Proof. exact (eq_refl (@all (_120557 -> Prop))). Qed.
Lemma lem5754250 {_120557 : Type'} : (term141 _120557) = (term141 _120557).
Proof. exact (MK_COMB (@lem5754249 _120557) (@lem5754248 _120557)). Qed.
Lemma lem5754251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5754252 {_120557 : Type'} : (term143 _120557) = (term143 _120557).
Proof. exact (MK_COMB (@lem5754251) (@lem5754250 _120557)). Qed.
Lemma lem5754253 {_120557 : Type'} : (term147 _120557) = (term147 _120557).
Proof. exact (MK_COMB (@lem5754252 _120557) (@lem5754217 _120557)). Qed.
Lemma lem5754328 {_120557 : Type'} : (term126 _120557) = (term147 _120557).
Proof. exact (TRANS (@lem5754175 _120557) (@lem5754253 _120557)). Qed.
Lemma lem5754329 {_120557 : Type'} : (term147 _120557) = (term126 _120557).
Proof. exact (SYM (@lem5754328 _120557)). Qed.
Lemma lem5754331 (p : Prop) : p = (term64 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5754332 {_120557 : Type'} : (term147 _120557) = (term148 _120557).
Proof. exact (@lem5754331 (term147 _120557)). Qed.
Lemma lem5754333 {_120557 : Type'} : (term148 _120557) = (term147 _120557).
Proof. exact (SYM (@lem5754332 _120557)). Qed.
Lemma lem5754334 {_120557 : Type'} (h1 : term149 _120557) : term149 _120557.
Proof. exact (h1). Qed.
Lemma lem5754345 {_120557 : Type'} (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term150 _120557 x t x') = (term151 _120557 x t x').
Proof. exact (@lem17160 (x' = x) (t x')). Qed.
Lemma lem5754350 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (term54 _120557 s x') = (term54 _120557 s x').
Proof. exact (eq_refl (term54 _120557 s x')). Qed.
Lemma lem5754351 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term152 _120557 s x t x') = (term153 _120557 s x t x').
Proof. exact (MK_COMB (@lem5754350 _120557 s x') (@lem5754345 _120557 x t x')). Qed.
Lemma lem5754352 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term154 _120557 s x t x') = (term152 _120557 s x t x').
Proof. exact (@lem17160 (s x') (term26 _120557 x t x')). Qed.
Lemma lem5754353 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term154 _120557 s x t x') = (term153 _120557 s x t x').
Proof. exact (TRANS (@lem5754352 _120557 s x t x') (@lem5754351 _120557 s x t x')). Qed.
Lemma lem5754367 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term155 _120557 s t x') = (term156 _120557 s t x').
Proof. exact (@lem17160 (s x') (t x')). Qed.
Lemma lem5754372 {_120557 : Type'} (x' : _120557) (x : _120557) : (term157 _120557 x' x) = (term157 _120557 x' x).
Proof. exact (eq_refl (term157 _120557 x' x)). Qed.
Lemma lem5754373 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term158 _120557 x s t x') = (term159 _120557 x s t x').
Proof. exact (MK_COMB (@lem5754372 _120557 x' x) (@lem5754367 _120557 s t x')). Qed.
Lemma lem5754374 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term160 _120557 x s t x') = (term158 _120557 x s t x').
Proof. exact (@lem17160 (x' = x) (term32 _120557 s t x')). Qed.
Lemma lem5754375 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term160 _120557 x s t x') = (term159 _120557 x s t x').
Proof. exact (TRANS (@lem5754374 _120557 x s t x') (@lem5754373 _120557 x s t x')). Qed.
Lemma lem5754378 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term33 _120557 x s t x') = (term33 _120557 x s t x').
Proof. exact (eq_refl (term33 _120557 x s t x')). Qed.
Lemma lem5754379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5754380 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term161 _120557 s x t x') = (term162 _120557 s x t x').
Proof. exact (MK_COMB (@lem5754379) (@lem5754353 _120557 s x t x')). Qed.
Lemma lem5754381 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term163 _120557 x s t x') = (term164 _120557 x s t x').
Proof. exact (MK_COMB (@lem5754380 _120557 s x t x') (@lem5754378 _120557 x s t x')). Qed.
Lemma lem5754383 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term165 _120557 s x t x') = (term165 _120557 s x t x').
Proof. exact (eq_refl (term165 _120557 s x t x')). Qed.
Lemma lem5754384 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term166 _120557 x s t x') = (term167 _120557 x s t x').
Proof. exact (MK_COMB (@lem5754383 _120557 s x t x') (@lem5754375 _120557 x s t x')). Qed.
Lemma lem5754385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5754386 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term168 _120557 x s t x') = (term169 _120557 x s t x').
Proof. exact (MK_COMB (@lem5754385) (@lem5754384 _120557 x s t x')). Qed.
Lemma lem5754387 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term170 _120557 x s t x') = (term171 _120557 x s t x').
Proof. exact (MK_COMB (@lem5754386 _120557 x s t x') (@lem5754381 _120557 x s t x')). Qed.
Lemma lem5754388 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term172 _120557 x s t x') = (term170 _120557 x s t x').
Proof. exact (@lem17646 (term27 _120557 s x t x') (term33 _120557 x s t x')). Qed.
Lemma lem5754389 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term172 _120557 x s t x') = (term171 _120557 x s t x').
Proof. exact (TRANS (@lem5754388 _120557 x s t x') (@lem5754387 _120557 x s t x')). Qed.
Lemma lem5754390 {_120557 : Type'} (P : _120557 -> Prop) : (term173 _120557 P) = (term174 _120557 P).
Proof. exact (@lem18392 _120557 P). Qed.
Lemma lem5754391 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term175 _120557 x s t) = (term176 _120557 x s t).
Proof. exact (@lem5754390 _120557 (term35 _120557 x s t)). Qed.
Lemma lem5754392 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term177 _120557 x s t x') = ((term27 _120557 s x t x') = (term33 _120557 x s t x')).
Proof. exact (eq_refl (term177 _120557 x s t x')). Qed.
Lemma lem5754393 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5754394 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term178 _120557 x s t x') = (term172 _120557 x s t x').
Proof. exact (MK_COMB (@lem5754393) (@lem5754392 _120557 x s t x')). Qed.
Lemma lem5754395 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term178 _120557 x s t x') = (term171 _120557 x s t x').
Proof. exact (TRANS (@lem5754394 _120557 x s t x') (@lem5754389 _120557 x s t x')). Qed.
Lemma lem5754396 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term179 _120557 x s t) = (term180 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5754395 _120557 x s t x')). Qed.
Lemma lem5754397 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5754398 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term176 _120557 x s t) = (term181 _120557 x s t).
Proof. exact (MK_COMB (@lem5754397 _120557) (@lem5754396 _120557 x s t)). Qed.
Lemma lem5754399 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term175 _120557 x s t) = (term181 _120557 x s t).
Proof. exact (TRANS (@lem5754391 _120557 x s t) (@lem5754398 _120557 x s t)). Qed.
Lemma lem5754400 {_120557 : Type'} (P : _120557 -> Prop) : (term173 _120557 P) = (term174 _120557 P).
Proof. exact (@lem18392 _120557 P). Qed.
Lemma lem5754401 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term182 _120557 s t) = (term183 _120557 s t).
Proof. exact (@lem5754400 _120557 (term80 _120557 s t)). Qed.
Lemma lem5754402 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term82 _120557 s t x) = (term36 _120557 x s t).
Proof. exact (eq_refl (term82 _120557 s t x)). Qed.
Lemma lem5754403 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5754404 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term184 _120557 s t x) = (term175 _120557 x s t).
Proof. exact (MK_COMB (@lem5754403) (@lem5754402 _120557 x s t)). Qed.
Lemma lem5754405 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term184 _120557 s t x) = (term181 _120557 x s t).
Proof. exact (TRANS (@lem5754404 _120557 x s t) (@lem5754399 _120557 x s t)). Qed.
Lemma lem5754406 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term185 _120557 s t) = (term186 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5754405 _120557 x s t)). Qed.
Lemma lem5754407 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5754408 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term183 _120557 s t) = (term187 _120557 s t).
Proof. exact (MK_COMB (@lem5754407 _120557) (@lem5754406 _120557 s t)). Qed.
Lemma lem5754409 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term182 _120557 s t) = (term187 _120557 s t).
Proof. exact (TRANS (@lem5754401 _120557 s t) (@lem5754408 _120557 s t)). Qed.
Lemma lem5754410 {_120557 : Type'} (P : type686 _120557) : (term188 _120557 P) = (term189 _120557 P).
Proof. exact (@lem18392 (_120557 -> Prop) P). Qed.
Lemma lem5754411 {_120557 : Type'} (t : _120557 -> Prop) : (term190 _120557 t) = (term191 _120557 t).
Proof. exact (@lem5754410 _120557 (term106 _120557 t)). Qed.
Lemma lem5754412 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term108 _120557 t s) = (term91 _120557 s t).
Proof. exact (eq_refl (term108 _120557 t s)). Qed.
Lemma lem5754413 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5754414 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term192 _120557 t s) = (term182 _120557 s t).
Proof. exact (MK_COMB (@lem5754413) (@lem5754412 _120557 s t)). Qed.
Lemma lem5754415 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term192 _120557 t s) = (term187 _120557 s t).
Proof. exact (TRANS (@lem5754414 _120557 s t) (@lem5754409 _120557 s t)). Qed.
Lemma lem5754416 {_120557 : Type'} (t : _120557 -> Prop) : (term193 _120557 t) = (term194 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5754415 _120557 s t)). Qed.
Lemma lem5754417 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5754418 {_120557 : Type'} (t : _120557 -> Prop) : (term191 _120557 t) = (term195 _120557 t).
Proof. exact (MK_COMB (@lem5754417 _120557) (@lem5754416 _120557 t)). Qed.
Lemma lem5754419 {_120557 : Type'} (t : _120557 -> Prop) : (term190 _120557 t) = (term195 _120557 t).
Proof. exact (TRANS (@lem5754411 _120557 t) (@lem5754418 _120557 t)). Qed.
Lemma lem5754420 {_120557 : Type'} (P : type686 _120557) : (term188 _120557 P) = (term189 _120557 P).
Proof. exact (@lem18392 (_120557 -> Prop) P). Qed.
Lemma lem5754421 {_120557 : Type'} : (term196 _120557) = (term197 _120557).
Proof. exact (@lem5754420 _120557 (term130 _120557)). Qed.
Lemma lem5754422 {_120557 : Type'} (t : _120557 -> Prop) : (term132 _120557 t) = (term117 _120557 t).
Proof. exact (eq_refl (term132 _120557 t)). Qed.
Lemma lem5754423 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5754424 {_120557 : Type'} (t : _120557 -> Prop) : (term198 _120557 t) = (term190 _120557 t).
Proof. exact (MK_COMB (@lem5754423) (@lem5754422 _120557 t)). Qed.
Lemma lem5754425 {_120557 : Type'} (t : _120557 -> Prop) : (term198 _120557 t) = (term195 _120557 t).
Proof. exact (TRANS (@lem5754424 _120557 t) (@lem5754419 _120557 t)). Qed.
Lemma lem5754426 {_120557 : Type'} : (term199 _120557) = (term200 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5754425 _120557 t)). Qed.
Lemma lem5754427 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5754428 {_120557 : Type'} : (term197 _120557) = (term201 _120557).
Proof. exact (MK_COMB (@lem5754427 _120557) (@lem5754426 _120557)). Qed.
Lemma lem5754429 {_120557 : Type'} : (term196 _120557) = (term201 _120557).
Proof. exact (TRANS (@lem5754421 _120557) (@lem5754428 _120557)). Qed.
Lemma lem5754440 {_120557 : Type'} (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term150 _120557 x t x') = (term151 _120557 x t x').
Proof. exact (@lem17160 (x' = x) (t x')). Qed.
Lemma lem5754445 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (term202 _120557 s x') = (term202 _120557 s x').
Proof. exact (eq_refl (term202 _120557 s x')). Qed.
Lemma lem5754446 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term203 _120557 s x t x') = (term204 _120557 s x t x').
Proof. exact (MK_COMB (@lem5754445 _120557 s x') (@lem5754440 _120557 x t x')). Qed.
Lemma lem5754447 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term47 _120557 s x t x') = (term203 _120557 s x t x').
Proof. exact (@lem17045 (s x') (term26 _120557 x t x')). Qed.
Lemma lem5754448 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term47 _120557 s x t x') = (term204 _120557 s x t x').
Proof. exact (TRANS (@lem5754447 _120557 s x t x') (@lem5754446 _120557 s x t x')). Qed.
Lemma lem5754453 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term205 _120557 s x t x') = (term44 _120557 s x t x').
Proof. exact (@lem16933 (term44 _120557 s x t x')). Qed.
Lemma lem5754454 {_120557 : Type'} (P : _120557 -> Prop) : (term173 _120557 P) = (term174 _120557 P).
Proof. exact (@lem18392 _120557 P). Qed.
Lemma lem5754455 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term206 _120557 s x t) = (term207 _120557 s x t).
Proof. exact (@lem5754454 _120557 (term49 _120557 s x t)). Qed.
Lemma lem5754456 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term208 _120557 s x t x') = (term47 _120557 s x t x').
Proof. exact (eq_refl (term208 _120557 s x t x')). Qed.
Lemma lem5754457 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5754458 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term209 _120557 s x t x') = (term205 _120557 s x t x').
Proof. exact (MK_COMB (@lem5754457) (@lem5754456 _120557 s x t x')). Qed.
Lemma lem5754459 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term209 _120557 s x t x') = (term44 _120557 s x t x').
Proof. exact (TRANS (@lem5754458 _120557 s x t x') (@lem5754453 _120557 s x t x')). Qed.
Lemma lem5754460 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term210 _120557 s x t) = (term211 _120557 s x t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5754459 _120557 s x t x')). Qed.
Lemma lem5754461 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5754462 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term207 _120557 s x t) = (term212 _120557 s x t).
Proof. exact (MK_COMB (@lem5754461 _120557) (@lem5754460 _120557 s x t)). Qed.
Lemma lem5754463 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term206 _120557 s x t) = (term212 _120557 s x t).
Proof. exact (TRANS (@lem5754455 _120557 s x t) (@lem5754462 _120557 s x t)). Qed.
Lemma lem5754464 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term49 _120557 s x t) = (term213 _120557 s x t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5754448 _120557 s x t x')). Qed.
Lemma lem5754465 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5754466 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term50 _120557 s x t) = (term214 _120557 s x t).
Proof. exact (MK_COMB (@lem5754465 _120557) (@lem5754464 _120557 s x t)). Qed.
Lemma lem5754470 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (term215 _120557 s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem5754479 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : (term58 _120557 s t x) = (term216 _120557 s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem5754484 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : (term217 _120557 s t x) = (term55 _120557 s t x).
Proof. exact (@lem16933 (term55 _120557 s t x)). Qed.
Lemma lem5754485 {_120557 : Type'} (P : _120557 -> Prop) : (term173 _120557 P) = (term174 _120557 P).
Proof. exact (@lem18392 _120557 P). Qed.
Lemma lem5754486 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term218 _120557 s t) = (term219 _120557 s t).
Proof. exact (@lem5754485 _120557 (term60 _120557 s t)). Qed.
Lemma lem5754487 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : (term220 _120557 s t x) = (term58 _120557 s t x).
Proof. exact (eq_refl (term220 _120557 s t x)). Qed.
Lemma lem5754488 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5754489 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : (term221 _120557 s t x) = (term217 _120557 s t x).
Proof. exact (MK_COMB (@lem5754488) (@lem5754487 _120557 s t x)). Qed.
Lemma lem5754490 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : (term221 _120557 s t x) = (term55 _120557 s t x).
Proof. exact (TRANS (@lem5754489 _120557 s t x) (@lem5754484 _120557 s t x)). Qed.
Lemma lem5754491 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term222 _120557 s t) = (term223 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5754490 _120557 s t x)). Qed.
Lemma lem5754492 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5754493 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term219 _120557 s t) = (term224 _120557 s t).
Proof. exact (MK_COMB (@lem5754492 _120557) (@lem5754491 _120557 s t)). Qed.
Lemma lem5754494 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term218 _120557 s t) = (term224 _120557 s t).
Proof. exact (TRANS (@lem5754486 _120557 s t) (@lem5754493 _120557 s t)). Qed.
Lemma lem5754495 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term60 _120557 s t) = (term225 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5754479 _120557 s t x)). Qed.
Lemma lem5754496 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5754497 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term61 _120557 s t) = (term226 _120557 s t).
Proof. exact (MK_COMB (@lem5754496 _120557) (@lem5754495 _120557 s t)). Qed.
Lemma lem5754498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5754499 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (term227 _120557 s x) = (term22 _120557 s x).
Proof. exact (MK_COMB (@lem5754498) (@lem5754470 _120557 s x)). Qed.
Lemma lem5754500 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term228 _120557 x s t) = (term229 _120557 x s t).
Proof. exact (MK_COMB (@lem5754499 _120557 s x) (@lem5754494 _120557 s t)). Qed.
Lemma lem5754501 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term230 _120557 x s t) = (term228 _120557 x s t).
Proof. exact (@lem17045 (term53 _120557 s x) (term61 _120557 s t)). Qed.
Lemma lem5754502 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term230 _120557 x s t) = (term229 _120557 x s t).
Proof. exact (TRANS (@lem5754501 _120557 x s t) (@lem5754500 _120557 x s t)). Qed.
Lemma lem5754504 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (term54 _120557 s x) = (term54 _120557 s x).
Proof. exact (eq_refl (term54 _120557 s x)). Qed.
Lemma lem5754505 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term62 _120557 x s t) = (term231 _120557 x s t).
Proof. exact (MK_COMB (@lem5754504 _120557 s x) (@lem5754497 _120557 s t)). Qed.
Lemma lem5754506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5754507 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term232 _120557 s x t) = (term233 _120557 s x t).
Proof. exact (MK_COMB (@lem5754506) (@lem5754463 _120557 s x t)). Qed.
Lemma lem5754508 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term234 _120557 x s t) = (term235 _120557 x s t).
Proof. exact (MK_COMB (@lem5754507 _120557 s x t) (@lem5754505 _120557 x s t)). Qed.
Lemma lem5754509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5754510 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term236 _120557 s x t) = (term237 _120557 s x t).
Proof. exact (MK_COMB (@lem5754509) (@lem5754466 _120557 s x t)). Qed.
Lemma lem5754511 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term238 _120557 x s t) = (term239 _120557 x s t).
Proof. exact (MK_COMB (@lem5754510 _120557 s x t) (@lem5754502 _120557 x s t)). Qed.
Lemma lem5754512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5754513 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term240 _120557 x s t) = (term241 _120557 x s t).
Proof. exact (MK_COMB (@lem5754512) (@lem5754511 _120557 x s t)). Qed.
Lemma lem5754514 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term242 _120557 x s t) = (term243 _120557 x s t).
Proof. exact (MK_COMB (@lem5754513 _120557 x s t) (@lem5754508 _120557 x s t)). Qed.
Lemma lem5754515 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term244 _120557 x s t) = (term242 _120557 x s t).
Proof. exact (@lem17646 (term50 _120557 s x t) (term62 _120557 x s t)). Qed.
Lemma lem5754516 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term244 _120557 x s t) = (term243 _120557 x s t).
Proof. exact (TRANS (@lem5754515 _120557 x s t) (@lem5754514 _120557 x s t)). Qed.
Lemma lem5754517 {_120557 : Type'} (P : _120557 -> Prop) : (term173 _120557 P) = (term174 _120557 P).
Proof. exact (@lem18392 _120557 P). Qed.
Lemma lem5754518 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term245 _120557 s t) = (term246 _120557 s t).
Proof. exact (@lem5754517 _120557 (term81 _120557 s t)). Qed.
Lemma lem5754519 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term84 _120557 s t x) = ((term50 _120557 s x t) = (term62 _120557 x s t)).
Proof. exact (eq_refl (term84 _120557 s t x)). Qed.
Lemma lem5754520 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5754521 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term247 _120557 s t x) = (term244 _120557 x s t).
Proof. exact (MK_COMB (@lem5754520) (@lem5754519 _120557 x s t)). Qed.
Lemma lem5754522 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term247 _120557 s t x) = (term243 _120557 x s t).
Proof. exact (TRANS (@lem5754521 _120557 x s t) (@lem5754516 _120557 x s t)). Qed.
Lemma lem5754523 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term248 _120557 s t) = (term249 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5754522 _120557 x s t)). Qed.
Lemma lem5754524 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5754525 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term246 _120557 s t) = (term250 _120557 s t).
Proof. exact (MK_COMB (@lem5754524 _120557) (@lem5754523 _120557 s t)). Qed.
Lemma lem5754526 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term245 _120557 s t) = (term250 _120557 s t).
Proof. exact (TRANS (@lem5754518 _120557 s t) (@lem5754525 _120557 s t)). Qed.
Lemma lem5754527 {_120557 : Type'} (P : type686 _120557) : (term188 _120557 P) = (term189 _120557 P).
Proof. exact (@lem18392 (_120557 -> Prop) P). Qed.
Lemma lem5754528 {_120557 : Type'} (t : _120557 -> Prop) : (term251 _120557 t) = (term252 _120557 t).
Proof. exact (@lem5754527 _120557 (term107 _120557 t)). Qed.
Lemma lem5754529 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term110 _120557 t s) = (term96 _120557 s t).
Proof. exact (eq_refl (term110 _120557 t s)). Qed.
Lemma lem5754530 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5754531 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term253 _120557 t s) = (term245 _120557 s t).
Proof. exact (MK_COMB (@lem5754530) (@lem5754529 _120557 s t)). Qed.
Lemma lem5754532 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term253 _120557 t s) = (term250 _120557 s t).
Proof. exact (TRANS (@lem5754531 _120557 s t) (@lem5754526 _120557 s t)). Qed.
Lemma lem5754533 {_120557 : Type'} (t : _120557 -> Prop) : (term254 _120557 t) = (term255 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5754532 _120557 s t)). Qed.
Lemma lem5754534 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5754535 {_120557 : Type'} (t : _120557 -> Prop) : (term252 _120557 t) = (term256 _120557 t).
Proof. exact (MK_COMB (@lem5754534 _120557) (@lem5754533 _120557 t)). Qed.
Lemma lem5754536 {_120557 : Type'} (t : _120557 -> Prop) : (term251 _120557 t) = (term256 _120557 t).
Proof. exact (TRANS (@lem5754528 _120557 t) (@lem5754535 _120557 t)). Qed.
Lemma lem5754537 {_120557 : Type'} (P : type686 _120557) : (term188 _120557 P) = (term189 _120557 P).
Proof. exact (@lem18392 (_120557 -> Prop) P). Qed.
Lemma lem5754538 {_120557 : Type'} : (term257 _120557) = (term258 _120557).
Proof. exact (@lem5754537 _120557 (term131 _120557)). Qed.
Lemma lem5754539 {_120557 : Type'} (t : _120557 -> Prop) : (term134 _120557 t) = (term122 _120557 t).
Proof. exact (eq_refl (term134 _120557 t)). Qed.
Lemma lem5754540 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5754541 {_120557 : Type'} (t : _120557 -> Prop) : (term259 _120557 t) = (term251 _120557 t).
Proof. exact (MK_COMB (@lem5754540) (@lem5754539 _120557 t)). Qed.
Lemma lem5754542 {_120557 : Type'} (t : _120557 -> Prop) : (term259 _120557 t) = (term256 _120557 t).
Proof. exact (TRANS (@lem5754541 _120557 t) (@lem5754536 _120557 t)). Qed.
Lemma lem5754543 {_120557 : Type'} : (term260 _120557) = (term261 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5754542 _120557 t)). Qed.
Lemma lem5754544 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5754545 {_120557 : Type'} : (term258 _120557) = (term262 _120557).
Proof. exact (MK_COMB (@lem5754544 _120557) (@lem5754543 _120557)). Qed.
Lemma lem5754546 {_120557 : Type'} : (term257 _120557) = (term262 _120557).
Proof. exact (TRANS (@lem5754538 _120557) (@lem5754545 _120557)). Qed.
Lemma lem5754547 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5754548 {_120557 : Type'} : (term263 _120557) = (term264 _120557).
Proof. exact (MK_COMB (@lem5754547) (@lem5754429 _120557)). Qed.
Lemma lem5754549 {_120557 : Type'} : (term265 _120557) = (term266 _120557).
Proof. exact (MK_COMB (@lem5754548 _120557) (@lem5754546 _120557)). Qed.
Lemma lem5754550 {_120557 : Type'} : (term149 _120557) = (term265 _120557).
Proof. exact (@lem17045 (term141 _120557) (term146 _120557)). Qed.
Lemma lem5754551 {_120557 : Type'} : (term149 _120557) = (term266 _120557).
Proof. exact (TRANS (@lem5754550 _120557) (@lem5754549 _120557)). Qed.
Lemma lem5754565 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5754566 {_120557 : Type'} (P : _120557 -> Prop) (Q : _120557 -> Prop) : (term267 _120557 P Q) = (term268 _120557 P Q).
Proof. exact (@lem5754565 _120557 P Q). Qed.
Lemma lem5754567 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term269 _120557 x s t) = (term270 _120557 x s t).
Proof. exact (@lem5754566 _120557 (term271 _120557 x s t) (term272 _120557 x s t)). Qed.
Lemma lem5754568 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term273 _120557 x s t x') = (term167 _120557 x s t x').
Proof. exact (eq_refl (term273 _120557 x s t x')). Qed.
Lemma lem5754569 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5754570 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term274 _120557 x s t x') = (term169 _120557 x s t x').
Proof. exact (MK_COMB (@lem5754569) (@lem5754568 _120557 x s t x')). Qed.
Lemma lem5754571 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term275 _120557 x s t x') = (term164 _120557 x s t x').
Proof. exact (eq_refl (term275 _120557 x s t x')). Qed.
Lemma lem5754572 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term276 _120557 x s t x') = (term171 _120557 x s t x').
Proof. exact (MK_COMB (@lem5754570 _120557 x s t x') (@lem5754571 _120557 x s t x')). Qed.
Lemma lem5754573 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term277 _120557 x s t) = (term180 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5754572 _120557 x s t x')). Qed.
Lemma lem5754574 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5754575 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term269 _120557 x s t) = (term181 _120557 x s t).
Proof. exact (MK_COMB (@lem5754574 _120557) (@lem5754573 _120557 x s t)). Qed.
Lemma lem5754576 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5754577 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term278 _120557 x s t) = (term279 _120557 x s t).
Proof. exact (MK_COMB (@lem5754576) (@lem5754575 _120557 x s t)). Qed.
Lemma lem5754578 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term273 _120557 x s t x') = (term167 _120557 x s t x').
Proof. exact (eq_refl (term273 _120557 x s t x')). Qed.
Lemma lem5754579 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term280 _120557 x s t) = (term271 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5754578 _120557 x s t x')). Qed.
Lemma lem5754580 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5754581 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term281 _120557 x s t) = (term282 _120557 x s t).
Proof. exact (MK_COMB (@lem5754580 _120557) (@lem5754579 _120557 x s t)). Qed.
Lemma lem5754582 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5754583 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term283 _120557 x s t) = (term284 _120557 x s t).
Proof. exact (MK_COMB (@lem5754582) (@lem5754581 _120557 x s t)). Qed.
Lemma lem5754584 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term275 _120557 x s t x') = (term164 _120557 x s t x').
Proof. exact (eq_refl (term275 _120557 x s t x')). Qed.
Lemma lem5754585 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term285 _120557 x s t) = (term272 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5754584 _120557 x s t x')). Qed.
Lemma lem5754586 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5754587 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term286 _120557 x s t) = (term287 _120557 x s t).
Proof. exact (MK_COMB (@lem5754586 _120557) (@lem5754585 _120557 x s t)). Qed.
Lemma lem5754588 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term270 _120557 x s t) = (term288 _120557 x s t).
Proof. exact (MK_COMB (@lem5754583 _120557 x s t) (@lem5754587 _120557 x s t)). Qed.
Lemma lem5754589 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term269 _120557 x s t) = (term270 _120557 x s t)) = ((term181 _120557 x s t) = (term288 _120557 x s t)).
Proof. exact (MK_COMB (@lem5754577 _120557 x s t) (@lem5754588 _120557 x s t)). Qed.
Lemma lem5754590 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term181 _120557 x s t) = (term288 _120557 x s t).
Proof. exact (EQ_MP (@lem5754589 _120557 x s t) (@lem5754567 _120557 x s t)). Qed.
Lemma lem5754687 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term186 _120557 s t) = (term289 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5754590 _120557 x s t)). Qed.
Lemma lem5754688 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5754689 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term187 _120557 s t) = (term290 _120557 s t).
Proof. exact (MK_COMB (@lem5754688 _120557) (@lem5754687 _120557 s t)). Qed.
Lemma lem5754691 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5754692 {_120557 : Type'} (P : _120557 -> Prop) (Q : _120557 -> Prop) : (term267 _120557 P Q) = (term268 _120557 P Q).
Proof. exact (@lem5754691 _120557 P Q). Qed.
Lemma lem5754693 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term291 _120557 s t) = (term292 _120557 s t).
Proof. exact (@lem5754692 _120557 (term293 _120557 s t) (term294 _120557 s t)). Qed.
Lemma lem5754694 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term295 _120557 s t x) = (term282 _120557 x s t).
Proof. exact (eq_refl (term295 _120557 s t x)). Qed.
Lemma lem5754695 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5754696 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term296 _120557 s t x) = (term284 _120557 x s t).
Proof. exact (MK_COMB (@lem5754695) (@lem5754694 _120557 x s t)). Qed.
Lemma lem5754697 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term297 _120557 s t x) = (term287 _120557 x s t).
Proof. exact (eq_refl (term297 _120557 s t x)). Qed.
Lemma lem5754698 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term298 _120557 s t x) = (term288 _120557 x s t).
Proof. exact (MK_COMB (@lem5754696 _120557 x s t) (@lem5754697 _120557 x s t)). Qed.
Lemma lem5754699 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term299 _120557 s t) = (term289 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5754698 _120557 x s t)). Qed.
Lemma lem5754700 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5754701 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term291 _120557 s t) = (term290 _120557 s t).
Proof. exact (MK_COMB (@lem5754700 _120557) (@lem5754699 _120557 s t)). Qed.
Lemma lem5754702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5754703 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term300 _120557 s t) = (term301 _120557 s t).
Proof. exact (MK_COMB (@lem5754702) (@lem5754701 _120557 s t)). Qed.
Lemma lem5754704 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term295 _120557 s t x) = (term282 _120557 x s t).
Proof. exact (eq_refl (term295 _120557 s t x)). Qed.
Lemma lem5754705 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term302 _120557 s t) = (term293 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5754704 _120557 x s t)). Qed.
Lemma lem5754706 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5754707 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term303 _120557 s t) = (term304 _120557 s t).
Proof. exact (MK_COMB (@lem5754706 _120557) (@lem5754705 _120557 s t)). Qed.
Lemma lem5754708 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5754709 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term305 _120557 s t) = (term306 _120557 s t).
Proof. exact (MK_COMB (@lem5754708) (@lem5754707 _120557 s t)). Qed.
Lemma lem5754710 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term297 _120557 s t x) = (term287 _120557 x s t).
Proof. exact (eq_refl (term297 _120557 s t x)). Qed.
Lemma lem5754711 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term307 _120557 s t) = (term294 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5754710 _120557 x s t)). Qed.
Lemma lem5754712 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5754713 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term308 _120557 s t) = (term309 _120557 s t).
Proof. exact (MK_COMB (@lem5754712 _120557) (@lem5754711 _120557 s t)). Qed.
Lemma lem5754714 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term292 _120557 s t) = (term310 _120557 s t).
Proof. exact (MK_COMB (@lem5754709 _120557 s t) (@lem5754713 _120557 s t)). Qed.
Lemma lem5754715 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term291 _120557 s t) = (term292 _120557 s t)) = ((term290 _120557 s t) = (term310 _120557 s t)).
Proof. exact (MK_COMB (@lem5754703 _120557 s t) (@lem5754714 _120557 s t)). Qed.
Lemma lem5754716 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term290 _120557 s t) = (term310 _120557 s t).
Proof. exact (EQ_MP (@lem5754715 _120557 s t) (@lem5754693 _120557 s t)). Qed.
Lemma lem5754821 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term187 _120557 s t) = (term310 _120557 s t).
Proof. exact (TRANS (@lem5754689 _120557 s t) (@lem5754716 _120557 s t)). Qed.
Lemma lem5754822 {_120557 : Type'} (t : _120557 -> Prop) : (term194 _120557 t) = (term311 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5754821 _120557 s t)). Qed.
Lemma lem5754823 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5754824 {_120557 : Type'} (t : _120557 -> Prop) : (term195 _120557 t) = (term312 _120557 t).
Proof. exact (MK_COMB (@lem5754823 _120557) (@lem5754822 _120557 t)). Qed.
Lemma lem5754826 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5754827 {_120557 : Type'} (P : type686 _120557) (Q : type686 _120557) : (term313 _120557 P Q) = (term314 _120557 P Q).
Proof. exact (@lem5754826 (_120557 -> Prop) P Q). Qed.
Lemma lem5754828 {_120557 : Type'} (t : _120557 -> Prop) : (term315 _120557 t) = (term316 _120557 t).
Proof. exact (@lem5754827 _120557 (term317 _120557 t) (term318 _120557 t)). Qed.
Lemma lem5754829 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term319 _120557 t s) = (term304 _120557 s t).
Proof. exact (eq_refl (term319 _120557 t s)). Qed.
Lemma lem5754830 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5754831 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term320 _120557 t s) = (term306 _120557 s t).
Proof. exact (MK_COMB (@lem5754830) (@lem5754829 _120557 s t)). Qed.
Lemma lem5754832 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term321 _120557 t s) = (term309 _120557 s t).
Proof. exact (eq_refl (term321 _120557 t s)). Qed.
Lemma lem5754833 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term322 _120557 t s) = (term310 _120557 s t).
Proof. exact (MK_COMB (@lem5754831 _120557 s t) (@lem5754832 _120557 s t)). Qed.
Lemma lem5754834 {_120557 : Type'} (t : _120557 -> Prop) : (term323 _120557 t) = (term311 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5754833 _120557 s t)). Qed.
Lemma lem5754835 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5754836 {_120557 : Type'} (t : _120557 -> Prop) : (term315 _120557 t) = (term312 _120557 t).
Proof. exact (MK_COMB (@lem5754835 _120557) (@lem5754834 _120557 t)). Qed.
Lemma lem5754837 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5754838 {_120557 : Type'} (t : _120557 -> Prop) : (term324 _120557 t) = (term325 _120557 t).
Proof. exact (MK_COMB (@lem5754837) (@lem5754836 _120557 t)). Qed.
Lemma lem5754839 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term319 _120557 t s) = (term304 _120557 s t).
Proof. exact (eq_refl (term319 _120557 t s)). Qed.
Lemma lem5754840 {_120557 : Type'} (t : _120557 -> Prop) : (term326 _120557 t) = (term317 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5754839 _120557 s t)). Qed.
Lemma lem5754841 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5754842 {_120557 : Type'} (t : _120557 -> Prop) : (term327 _120557 t) = (term328 _120557 t).
Proof. exact (MK_COMB (@lem5754841 _120557) (@lem5754840 _120557 t)). Qed.
Lemma lem5754843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5754844 {_120557 : Type'} (t : _120557 -> Prop) : (term329 _120557 t) = (term330 _120557 t).
Proof. exact (MK_COMB (@lem5754843) (@lem5754842 _120557 t)). Qed.
Lemma lem5754845 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term321 _120557 t s) = (term309 _120557 s t).
Proof. exact (eq_refl (term321 _120557 t s)). Qed.
Lemma lem5754846 {_120557 : Type'} (t : _120557 -> Prop) : (term331 _120557 t) = (term318 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5754845 _120557 s t)). Qed.
Lemma lem5754847 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5754848 {_120557 : Type'} (t : _120557 -> Prop) : (term332 _120557 t) = (term333 _120557 t).
Proof. exact (MK_COMB (@lem5754847 _120557) (@lem5754846 _120557 t)). Qed.
Lemma lem5754849 {_120557 : Type'} (t : _120557 -> Prop) : (term316 _120557 t) = (term334 _120557 t).
Proof. exact (MK_COMB (@lem5754844 _120557 t) (@lem5754848 _120557 t)). Qed.
Lemma lem5754850 {_120557 : Type'} (t : _120557 -> Prop) : ((term315 _120557 t) = (term316 _120557 t)) = ((term312 _120557 t) = (term334 _120557 t)).
Proof. exact (MK_COMB (@lem5754838 _120557 t) (@lem5754849 _120557 t)). Qed.
Lemma lem5754851 {_120557 : Type'} (t : _120557 -> Prop) : (term312 _120557 t) = (term334 _120557 t).
Proof. exact (EQ_MP (@lem5754850 _120557 t) (@lem5754828 _120557 t)). Qed.
Lemma lem5754964 {_120557 : Type'} (t : _120557 -> Prop) : (term195 _120557 t) = (term334 _120557 t).
Proof. exact (TRANS (@lem5754824 _120557 t) (@lem5754851 _120557 t)). Qed.
Lemma lem5754965 {_120557 : Type'} : (term200 _120557) = (term335 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5754964 _120557 t)). Qed.
Lemma lem5754966 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5754967 {_120557 : Type'} : (term201 _120557) = (term336 _120557).
Proof. exact (MK_COMB (@lem5754966 _120557) (@lem5754965 _120557)). Qed.
Lemma lem5754969 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5754970 {_120557 : Type'} (P : type686 _120557) (Q : type686 _120557) : (term313 _120557 P Q) = (term314 _120557 P Q).
Proof. exact (@lem5754969 (_120557 -> Prop) P Q). Qed.
Lemma lem5754971 {_120557 : Type'} : (term337 _120557) = (term338 _120557).
Proof. exact (@lem5754970 _120557 (term339 _120557) (term340 _120557)). Qed.
Lemma lem5754972 {_120557 : Type'} (t : _120557 -> Prop) : (term341 _120557 t) = (term328 _120557 t).
Proof. exact (eq_refl (term341 _120557 t)). Qed.
Lemma lem5754973 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5754974 {_120557 : Type'} (t : _120557 -> Prop) : (term342 _120557 t) = (term330 _120557 t).
Proof. exact (MK_COMB (@lem5754973) (@lem5754972 _120557 t)). Qed.
Lemma lem5754975 {_120557 : Type'} (t : _120557 -> Prop) : (term343 _120557 t) = (term333 _120557 t).
Proof. exact (eq_refl (term343 _120557 t)). Qed.
Lemma lem5754976 {_120557 : Type'} (t : _120557 -> Prop) : (term344 _120557 t) = (term334 _120557 t).
Proof. exact (MK_COMB (@lem5754974 _120557 t) (@lem5754975 _120557 t)). Qed.
Lemma lem5754977 {_120557 : Type'} : (term345 _120557) = (term335 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5754976 _120557 t)). Qed.
Lemma lem5754978 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5754979 {_120557 : Type'} : (term337 _120557) = (term336 _120557).
Proof. exact (MK_COMB (@lem5754978 _120557) (@lem5754977 _120557)). Qed.
Lemma lem5754980 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5754981 {_120557 : Type'} : (term346 _120557) = (term347 _120557).
Proof. exact (MK_COMB (@lem5754980) (@lem5754979 _120557)). Qed.
Lemma lem5754982 {_120557 : Type'} (t : _120557 -> Prop) : (term341 _120557 t) = (term328 _120557 t).
Proof. exact (eq_refl (term341 _120557 t)). Qed.
Lemma lem5754983 {_120557 : Type'} : (term348 _120557) = (term339 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5754982 _120557 t)). Qed.
Lemma lem5754984 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5754985 {_120557 : Type'} : (term349 _120557) = (term350 _120557).
Proof. exact (MK_COMB (@lem5754984 _120557) (@lem5754983 _120557)). Qed.
Lemma lem5754986 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5754987 {_120557 : Type'} : (term351 _120557) = (term352 _120557).
Proof. exact (MK_COMB (@lem5754986) (@lem5754985 _120557)). Qed.
Lemma lem5754988 {_120557 : Type'} (t : _120557 -> Prop) : (term343 _120557 t) = (term333 _120557 t).
Proof. exact (eq_refl (term343 _120557 t)). Qed.
Lemma lem5754989 {_120557 : Type'} : (term353 _120557) = (term340 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5754988 _120557 t)). Qed.
Lemma lem5754990 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5754991 {_120557 : Type'} : (term354 _120557) = (term355 _120557).
Proof. exact (MK_COMB (@lem5754990 _120557) (@lem5754989 _120557)). Qed.
Lemma lem5754992 {_120557 : Type'} : (term338 _120557) = (term356 _120557).
Proof. exact (MK_COMB (@lem5754987 _120557) (@lem5754991 _120557)). Qed.
Lemma lem5754993 {_120557 : Type'} : ((term337 _120557) = (term338 _120557)) = ((term336 _120557) = (term356 _120557)).
Proof. exact (MK_COMB (@lem5754981 _120557) (@lem5754992 _120557)). Qed.
Lemma lem5754994 {_120557 : Type'} : (term336 _120557) = (term356 _120557).
Proof. exact (EQ_MP (@lem5754993 _120557) (@lem5754971 _120557)). Qed.
Lemma lem5755115 {_120557 : Type'} : (term201 _120557) = (term356 _120557).
Proof. exact (TRANS (@lem5754967 _120557) (@lem5754994 _120557)). Qed.
Lemma lem5755116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5755117 {_120557 : Type'} : (term264 _120557) = (term357 _120557).
Proof. exact (MK_COMB (@lem5755116) (@lem5755115 _120557)). Qed.
Lemma lem5755127 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5755128 {_120557 : Type'} (P : _120557 -> Prop) (Q : _120557 -> Prop) : (term267 _120557 P Q) = (term268 _120557 P Q).
Proof. exact (@lem5755127 _120557 P Q). Qed.
Lemma lem5755129 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term358 _120557 s t) = (term359 _120557 s t).
Proof. exact (@lem5755128 _120557 (term360 _120557 s t) (term361 _120557 s t)). Qed.
Lemma lem5755130 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term362 _120557 s t x) = (term239 _120557 x s t).
Proof. exact (eq_refl (term362 _120557 s t x)). Qed.
Lemma lem5755131 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5755132 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term363 _120557 s t x) = (term241 _120557 x s t).
Proof. exact (MK_COMB (@lem5755131) (@lem5755130 _120557 x s t)). Qed.
Lemma lem5755133 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term364 _120557 s t x) = (term235 _120557 x s t).
Proof. exact (eq_refl (term364 _120557 s t x)). Qed.
Lemma lem5755134 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term365 _120557 s t x) = (term243 _120557 x s t).
Proof. exact (MK_COMB (@lem5755132 _120557 x s t) (@lem5755133 _120557 x s t)). Qed.
Lemma lem5755135 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term366 _120557 s t) = (term249 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5755134 _120557 x s t)). Qed.
Lemma lem5755136 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5755137 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term358 _120557 s t) = (term250 _120557 s t).
Proof. exact (MK_COMB (@lem5755136 _120557) (@lem5755135 _120557 s t)). Qed.
Lemma lem5755138 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5755139 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term367 _120557 s t) = (term368 _120557 s t).
Proof. exact (MK_COMB (@lem5755138) (@lem5755137 _120557 s t)). Qed.
Lemma lem5755140 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term362 _120557 s t x) = (term239 _120557 x s t).
Proof. exact (eq_refl (term362 _120557 s t x)). Qed.
Lemma lem5755141 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term369 _120557 s t) = (term360 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5755140 _120557 x s t)). Qed.
Lemma lem5755142 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5755143 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term370 _120557 s t) = (term371 _120557 s t).
Proof. exact (MK_COMB (@lem5755142 _120557) (@lem5755141 _120557 s t)). Qed.
Lemma lem5755144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5755145 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term372 _120557 s t) = (term373 _120557 s t).
Proof. exact (MK_COMB (@lem5755144) (@lem5755143 _120557 s t)). Qed.
Lemma lem5755146 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term364 _120557 s t x) = (term235 _120557 x s t).
Proof. exact (eq_refl (term364 _120557 s t x)). Qed.
Lemma lem5755147 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term374 _120557 s t) = (term361 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5755146 _120557 x s t)). Qed.
Lemma lem5755148 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5755149 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term375 _120557 s t) = (term376 _120557 s t).
Proof. exact (MK_COMB (@lem5755148 _120557) (@lem5755147 _120557 s t)). Qed.
Lemma lem5755150 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term359 _120557 s t) = (term377 _120557 s t).
Proof. exact (MK_COMB (@lem5755145 _120557 s t) (@lem5755149 _120557 s t)). Qed.
Lemma lem5755151 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term358 _120557 s t) = (term359 _120557 s t)) = ((term250 _120557 s t) = (term377 _120557 s t)).
Proof. exact (MK_COMB (@lem5755139 _120557 s t) (@lem5755150 _120557 s t)). Qed.
Lemma lem5755152 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term250 _120557 s t) = (term377 _120557 s t).
Proof. exact (EQ_MP (@lem5755151 _120557 s t) (@lem5755129 _120557 s t)). Qed.
Lemma lem5755385 {_120557 : Type'} (t : _120557 -> Prop) : (term255 _120557 t) = (term378 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5755152 _120557 s t)). Qed.
Lemma lem5755386 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5755387 {_120557 : Type'} (t : _120557 -> Prop) : (term256 _120557 t) = (term379 _120557 t).
Proof. exact (MK_COMB (@lem5755386 _120557) (@lem5755385 _120557 t)). Qed.
Lemma lem5755389 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5755390 {_120557 : Type'} (P : type686 _120557) (Q : type686 _120557) : (term313 _120557 P Q) = (term314 _120557 P Q).
Proof. exact (@lem5755389 (_120557 -> Prop) P Q). Qed.
Lemma lem5755391 {_120557 : Type'} (t : _120557 -> Prop) : (term380 _120557 t) = (term381 _120557 t).
Proof. exact (@lem5755390 _120557 (term382 _120557 t) (term383 _120557 t)). Qed.
Lemma lem5755392 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term384 _120557 t s) = (term371 _120557 s t).
Proof. exact (eq_refl (term384 _120557 t s)). Qed.
Lemma lem5755393 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5755394 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term385 _120557 t s) = (term373 _120557 s t).
Proof. exact (MK_COMB (@lem5755393) (@lem5755392 _120557 s t)). Qed.
Lemma lem5755395 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term386 _120557 t s) = (term376 _120557 s t).
Proof. exact (eq_refl (term386 _120557 t s)). Qed.
Lemma lem5755396 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term387 _120557 t s) = (term377 _120557 s t).
Proof. exact (MK_COMB (@lem5755394 _120557 s t) (@lem5755395 _120557 s t)). Qed.
Lemma lem5755397 {_120557 : Type'} (t : _120557 -> Prop) : (term388 _120557 t) = (term378 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5755396 _120557 s t)). Qed.
Lemma lem5755398 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5755399 {_120557 : Type'} (t : _120557 -> Prop) : (term380 _120557 t) = (term379 _120557 t).
Proof. exact (MK_COMB (@lem5755398 _120557) (@lem5755397 _120557 t)). Qed.
Lemma lem5755400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5755401 {_120557 : Type'} (t : _120557 -> Prop) : (term389 _120557 t) = (term390 _120557 t).
Proof. exact (MK_COMB (@lem5755400) (@lem5755399 _120557 t)). Qed.
Lemma lem5755402 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term384 _120557 t s) = (term371 _120557 s t).
Proof. exact (eq_refl (term384 _120557 t s)). Qed.
Lemma lem5755403 {_120557 : Type'} (t : _120557 -> Prop) : (term391 _120557 t) = (term382 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5755402 _120557 s t)). Qed.
Lemma lem5755404 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5755405 {_120557 : Type'} (t : _120557 -> Prop) : (term392 _120557 t) = (term393 _120557 t).
Proof. exact (MK_COMB (@lem5755404 _120557) (@lem5755403 _120557 t)). Qed.
Lemma lem5755406 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5755407 {_120557 : Type'} (t : _120557 -> Prop) : (term394 _120557 t) = (term395 _120557 t).
Proof. exact (MK_COMB (@lem5755406) (@lem5755405 _120557 t)). Qed.
Lemma lem5755408 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term386 _120557 t s) = (term376 _120557 s t).
Proof. exact (eq_refl (term386 _120557 t s)). Qed.
Lemma lem5755409 {_120557 : Type'} (t : _120557 -> Prop) : (term396 _120557 t) = (term383 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5755408 _120557 s t)). Qed.
Lemma lem5755410 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5755411 {_120557 : Type'} (t : _120557 -> Prop) : (term397 _120557 t) = (term398 _120557 t).
Proof. exact (MK_COMB (@lem5755410 _120557) (@lem5755409 _120557 t)). Qed.
Lemma lem5755412 {_120557 : Type'} (t : _120557 -> Prop) : (term381 _120557 t) = (term399 _120557 t).
Proof. exact (MK_COMB (@lem5755407 _120557 t) (@lem5755411 _120557 t)). Qed.
Lemma lem5755413 {_120557 : Type'} (t : _120557 -> Prop) : ((term380 _120557 t) = (term381 _120557 t)) = ((term379 _120557 t) = (term399 _120557 t)).
Proof. exact (MK_COMB (@lem5755401 _120557 t) (@lem5755412 _120557 t)). Qed.
Lemma lem5755414 {_120557 : Type'} (t : _120557 -> Prop) : (term379 _120557 t) = (term399 _120557 t).
Proof. exact (EQ_MP (@lem5755413 _120557 t) (@lem5755391 _120557 t)). Qed.
Lemma lem5755655 {_120557 : Type'} (t : _120557 -> Prop) : (term256 _120557 t) = (term399 _120557 t).
Proof. exact (TRANS (@lem5755387 _120557 t) (@lem5755414 _120557 t)). Qed.
Lemma lem5755656 {_120557 : Type'} : (term261 _120557) = (term400 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5755655 _120557 t)). Qed.
Lemma lem5755657 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5755658 {_120557 : Type'} : (term262 _120557) = (term401 _120557).
Proof. exact (MK_COMB (@lem5755657 _120557) (@lem5755656 _120557)). Qed.
Lemma lem5755660 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5755661 {_120557 : Type'} (P : type686 _120557) (Q : type686 _120557) : (term313 _120557 P Q) = (term314 _120557 P Q).
Proof. exact (@lem5755660 (_120557 -> Prop) P Q). Qed.
Lemma lem5755662 {_120557 : Type'} : (term402 _120557) = (term403 _120557).
Proof. exact (@lem5755661 _120557 (term404 _120557) (term405 _120557)). Qed.
Lemma lem5755663 {_120557 : Type'} (t : _120557 -> Prop) : (term406 _120557 t) = (term393 _120557 t).
Proof. exact (eq_refl (term406 _120557 t)). Qed.
Lemma lem5755664 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5755665 {_120557 : Type'} (t : _120557 -> Prop) : (term407 _120557 t) = (term395 _120557 t).
Proof. exact (MK_COMB (@lem5755664) (@lem5755663 _120557 t)). Qed.
Lemma lem5755666 {_120557 : Type'} (t : _120557 -> Prop) : (term408 _120557 t) = (term398 _120557 t).
Proof. exact (eq_refl (term408 _120557 t)). Qed.
Lemma lem5755667 {_120557 : Type'} (t : _120557 -> Prop) : (term409 _120557 t) = (term399 _120557 t).
Proof. exact (MK_COMB (@lem5755665 _120557 t) (@lem5755666 _120557 t)). Qed.
Lemma lem5755668 {_120557 : Type'} : (term410 _120557) = (term400 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5755667 _120557 t)). Qed.
Lemma lem5755669 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5755670 {_120557 : Type'} : (term402 _120557) = (term401 _120557).
Proof. exact (MK_COMB (@lem5755669 _120557) (@lem5755668 _120557)). Qed.
Lemma lem5755671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5755672 {_120557 : Type'} : (term411 _120557) = (term412 _120557).
Proof. exact (MK_COMB (@lem5755671) (@lem5755670 _120557)). Qed.
Lemma lem5755673 {_120557 : Type'} (t : _120557 -> Prop) : (term406 _120557 t) = (term393 _120557 t).
Proof. exact (eq_refl (term406 _120557 t)). Qed.
Lemma lem5755674 {_120557 : Type'} : (term413 _120557) = (term404 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5755673 _120557 t)). Qed.
Lemma lem5755675 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5755676 {_120557 : Type'} : (term414 _120557) = (term415 _120557).
Proof. exact (MK_COMB (@lem5755675 _120557) (@lem5755674 _120557)). Qed.
Lemma lem5755677 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5755678 {_120557 : Type'} : (term416 _120557) = (term417 _120557).
Proof. exact (MK_COMB (@lem5755677) (@lem5755676 _120557)). Qed.
Lemma lem5755679 {_120557 : Type'} (t : _120557 -> Prop) : (term408 _120557 t) = (term398 _120557 t).
Proof. exact (eq_refl (term408 _120557 t)). Qed.
Lemma lem5755680 {_120557 : Type'} : (term418 _120557) = (term405 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5755679 _120557 t)). Qed.
Lemma lem5755681 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5755682 {_120557 : Type'} : (term419 _120557) = (term420 _120557).
Proof. exact (MK_COMB (@lem5755681 _120557) (@lem5755680 _120557)). Qed.
Lemma lem5755683 {_120557 : Type'} : (term403 _120557) = (term421 _120557).
Proof. exact (MK_COMB (@lem5755678 _120557) (@lem5755682 _120557)). Qed.
Lemma lem5755684 {_120557 : Type'} : ((term402 _120557) = (term403 _120557)) = ((term401 _120557) = (term421 _120557)).
Proof. exact (MK_COMB (@lem5755672 _120557) (@lem5755683 _120557)). Qed.
Lemma lem5755685 {_120557 : Type'} : (term401 _120557) = (term421 _120557).
Proof. exact (EQ_MP (@lem5755684 _120557) (@lem5755662 _120557)). Qed.
Lemma lem5755934 {_120557 : Type'} : (term262 _120557) = (term421 _120557).
Proof. exact (TRANS (@lem5755658 _120557) (@lem5755685 _120557)). Qed.
Lemma lem5755935 {_120557 : Type'} : (term266 _120557) = (term422 _120557).
Proof. exact (MK_COMB (@lem5755117 _120557) (@lem5755934 _120557)). Qed.
Lemma lem5755937 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term268 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5755938 {_120557 : Type'} (P : type686 _120557) (Q : type686 _120557) : (term314 _120557 P Q) = (term313 _120557 P Q).
Proof. exact (@lem5755937 (_120557 -> Prop) P Q). Qed.
Lemma lem5755939 {_120557 : Type'} : (term338 _120557) = (term337 _120557).
Proof. exact (@lem5755938 _120557 (term339 _120557) (term340 _120557)). Qed.
Lemma lem5755940 {_120557 : Type'} (t : _120557 -> Prop) : (term341 _120557 t) = (term328 _120557 t).
Proof. exact (eq_refl (term341 _120557 t)). Qed.
Lemma lem5755941 {_120557 : Type'} : (term348 _120557) = (term339 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5755940 _120557 t)). Qed.
Lemma lem5755942 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5755943 {_120557 : Type'} : (term349 _120557) = (term350 _120557).
Proof. exact (MK_COMB (@lem5755942 _120557) (@lem5755941 _120557)). Qed.
Lemma lem5755944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5755945 {_120557 : Type'} : (term351 _120557) = (term352 _120557).
Proof. exact (MK_COMB (@lem5755944) (@lem5755943 _120557)). Qed.
Lemma lem5755946 {_120557 : Type'} (t : _120557 -> Prop) : (term343 _120557 t) = (term333 _120557 t).
Proof. exact (eq_refl (term343 _120557 t)). Qed.
Lemma lem5755947 {_120557 : Type'} : (term353 _120557) = (term340 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5755946 _120557 t)). Qed.
Lemma lem5755948 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5755949 {_120557 : Type'} : (term354 _120557) = (term355 _120557).
Proof. exact (MK_COMB (@lem5755948 _120557) (@lem5755947 _120557)). Qed.
Lemma lem5755950 {_120557 : Type'} : (term338 _120557) = (term356 _120557).
Proof. exact (MK_COMB (@lem5755945 _120557) (@lem5755949 _120557)). Qed.
Lemma lem5755951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5755952 {_120557 : Type'} : (term423 _120557) = (term424 _120557).
Proof. exact (MK_COMB (@lem5755951) (@lem5755950 _120557)). Qed.
Lemma lem5755953 {_120557 : Type'} (t : _120557 -> Prop) : (term341 _120557 t) = (term328 _120557 t).
Proof. exact (eq_refl (term341 _120557 t)). Qed.
Lemma lem5755954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5755955 {_120557 : Type'} (t : _120557 -> Prop) : (term342 _120557 t) = (term330 _120557 t).
Proof. exact (MK_COMB (@lem5755954) (@lem5755953 _120557 t)). Qed.
Lemma lem5755956 {_120557 : Type'} (t : _120557 -> Prop) : (term343 _120557 t) = (term333 _120557 t).
Proof. exact (eq_refl (term343 _120557 t)). Qed.
Lemma lem5755957 {_120557 : Type'} (t : _120557 -> Prop) : (term344 _120557 t) = (term334 _120557 t).
Proof. exact (MK_COMB (@lem5755955 _120557 t) (@lem5755956 _120557 t)). Qed.
Lemma lem5755958 {_120557 : Type'} : (term345 _120557) = (term335 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5755957 _120557 t)). Qed.
Lemma lem5755959 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5755960 {_120557 : Type'} : (term337 _120557) = (term336 _120557).
Proof. exact (MK_COMB (@lem5755959 _120557) (@lem5755958 _120557)). Qed.
Lemma lem5755961 {_120557 : Type'} : ((term338 _120557) = (term337 _120557)) = ((term356 _120557) = (term336 _120557)).
Proof. exact (MK_COMB (@lem5755952 _120557) (@lem5755960 _120557)). Qed.
Lemma lem5755962 {_120557 : Type'} : (term356 _120557) = (term336 _120557).
Proof. exact (EQ_MP (@lem5755961 _120557) (@lem5755939 _120557)). Qed.
Lemma lem5755964 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term268 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5755965 {_120557 : Type'} (P : type686 _120557) (Q : type686 _120557) : (term314 _120557 P Q) = (term313 _120557 P Q).
Proof. exact (@lem5755964 (_120557 -> Prop) P Q). Qed.
Lemma lem5755966 {_120557 : Type'} (t : _120557 -> Prop) : (term316 _120557 t) = (term315 _120557 t).
Proof. exact (@lem5755965 _120557 (term317 _120557 t) (term318 _120557 t)). Qed.
Lemma lem5755967 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term319 _120557 t s) = (term304 _120557 s t).
Proof. exact (eq_refl (term319 _120557 t s)). Qed.
Lemma lem5755968 {_120557 : Type'} (t : _120557 -> Prop) : (term326 _120557 t) = (term317 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5755967 _120557 s t)). Qed.
Lemma lem5755969 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5755970 {_120557 : Type'} (t : _120557 -> Prop) : (term327 _120557 t) = (term328 _120557 t).
Proof. exact (MK_COMB (@lem5755969 _120557) (@lem5755968 _120557 t)). Qed.
Lemma lem5755971 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5755972 {_120557 : Type'} (t : _120557 -> Prop) : (term329 _120557 t) = (term330 _120557 t).
Proof. exact (MK_COMB (@lem5755971) (@lem5755970 _120557 t)). Qed.
Lemma lem5755973 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term321 _120557 t s) = (term309 _120557 s t).
Proof. exact (eq_refl (term321 _120557 t s)). Qed.
Lemma lem5755974 {_120557 : Type'} (t : _120557 -> Prop) : (term331 _120557 t) = (term318 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5755973 _120557 s t)). Qed.
Lemma lem5755975 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5755976 {_120557 : Type'} (t : _120557 -> Prop) : (term332 _120557 t) = (term333 _120557 t).
Proof. exact (MK_COMB (@lem5755975 _120557) (@lem5755974 _120557 t)). Qed.
Lemma lem5755977 {_120557 : Type'} (t : _120557 -> Prop) : (term316 _120557 t) = (term334 _120557 t).
Proof. exact (MK_COMB (@lem5755972 _120557 t) (@lem5755976 _120557 t)). Qed.
Lemma lem5755978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5755979 {_120557 : Type'} (t : _120557 -> Prop) : (term425 _120557 t) = (term426 _120557 t).
Proof. exact (MK_COMB (@lem5755978) (@lem5755977 _120557 t)). Qed.
Lemma lem5755980 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term319 _120557 t s) = (term304 _120557 s t).
Proof. exact (eq_refl (term319 _120557 t s)). Qed.
Lemma lem5755981 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5755982 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term320 _120557 t s) = (term306 _120557 s t).
Proof. exact (MK_COMB (@lem5755981) (@lem5755980 _120557 s t)). Qed.
Lemma lem5755983 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term321 _120557 t s) = (term309 _120557 s t).
Proof. exact (eq_refl (term321 _120557 t s)). Qed.
Lemma lem5755984 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term322 _120557 t s) = (term310 _120557 s t).
Proof. exact (MK_COMB (@lem5755982 _120557 s t) (@lem5755983 _120557 s t)). Qed.
Lemma lem5755985 {_120557 : Type'} (t : _120557 -> Prop) : (term323 _120557 t) = (term311 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5755984 _120557 s t)). Qed.
Lemma lem5755986 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5755987 {_120557 : Type'} (t : _120557 -> Prop) : (term315 _120557 t) = (term312 _120557 t).
Proof. exact (MK_COMB (@lem5755986 _120557) (@lem5755985 _120557 t)). Qed.
Lemma lem5755988 {_120557 : Type'} (t : _120557 -> Prop) : ((term316 _120557 t) = (term315 _120557 t)) = ((term334 _120557 t) = (term312 _120557 t)).
Proof. exact (MK_COMB (@lem5755979 _120557 t) (@lem5755987 _120557 t)). Qed.
Lemma lem5755989 {_120557 : Type'} (t : _120557 -> Prop) : (term334 _120557 t) = (term312 _120557 t).
Proof. exact (EQ_MP (@lem5755988 _120557 t) (@lem5755966 _120557 t)). Qed.
Lemma lem5755991 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term268 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5755992 {_120557 : Type'} (P : _120557 -> Prop) (Q : _120557 -> Prop) : (term268 _120557 P Q) = (term267 _120557 P Q).
Proof. exact (@lem5755991 _120557 P Q). Qed.
Lemma lem5755993 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term292 _120557 s t) = (term291 _120557 s t).
Proof. exact (@lem5755992 _120557 (term293 _120557 s t) (term294 _120557 s t)). Qed.
Lemma lem5755994 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term295 _120557 s t x) = (term282 _120557 x s t).
Proof. exact (eq_refl (term295 _120557 s t x)). Qed.
Lemma lem5755995 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term302 _120557 s t) = (term293 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5755994 _120557 x s t)). Qed.
Lemma lem5755996 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5755997 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term303 _120557 s t) = (term304 _120557 s t).
Proof. exact (MK_COMB (@lem5755996 _120557) (@lem5755995 _120557 s t)). Qed.
Lemma lem5755998 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5755999 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term305 _120557 s t) = (term306 _120557 s t).
Proof. exact (MK_COMB (@lem5755998) (@lem5755997 _120557 s t)). Qed.
Lemma lem5756000 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term297 _120557 s t x) = (term287 _120557 x s t).
Proof. exact (eq_refl (term297 _120557 s t x)). Qed.
Lemma lem5756001 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term307 _120557 s t) = (term294 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756000 _120557 x s t)). Qed.
Lemma lem5756002 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756003 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term308 _120557 s t) = (term309 _120557 s t).
Proof. exact (MK_COMB (@lem5756002 _120557) (@lem5756001 _120557 s t)). Qed.
Lemma lem5756004 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term292 _120557 s t) = (term310 _120557 s t).
Proof. exact (MK_COMB (@lem5755999 _120557 s t) (@lem5756003 _120557 s t)). Qed.
Lemma lem5756005 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5756006 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term427 _120557 s t) = (term428 _120557 s t).
Proof. exact (MK_COMB (@lem5756005) (@lem5756004 _120557 s t)). Qed.
Lemma lem5756007 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term295 _120557 s t x) = (term282 _120557 x s t).
Proof. exact (eq_refl (term295 _120557 s t x)). Qed.
Lemma lem5756008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756009 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term296 _120557 s t x) = (term284 _120557 x s t).
Proof. exact (MK_COMB (@lem5756008) (@lem5756007 _120557 x s t)). Qed.
Lemma lem5756010 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term297 _120557 s t x) = (term287 _120557 x s t).
Proof. exact (eq_refl (term297 _120557 s t x)). Qed.
Lemma lem5756011 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term298 _120557 s t x) = (term288 _120557 x s t).
Proof. exact (MK_COMB (@lem5756009 _120557 x s t) (@lem5756010 _120557 x s t)). Qed.
Lemma lem5756012 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term299 _120557 s t) = (term289 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756011 _120557 x s t)). Qed.
Lemma lem5756013 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756014 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term291 _120557 s t) = (term290 _120557 s t).
Proof. exact (MK_COMB (@lem5756013 _120557) (@lem5756012 _120557 s t)). Qed.
Lemma lem5756015 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term292 _120557 s t) = (term291 _120557 s t)) = ((term310 _120557 s t) = (term290 _120557 s t)).
Proof. exact (MK_COMB (@lem5756006 _120557 s t) (@lem5756014 _120557 s t)). Qed.
Lemma lem5756016 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term310 _120557 s t) = (term290 _120557 s t).
Proof. exact (EQ_MP (@lem5756015 _120557 s t) (@lem5755993 _120557 s t)). Qed.
Lemma lem5756018 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term268 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5756019 {_120557 : Type'} (P : _120557 -> Prop) (Q : _120557 -> Prop) : (term268 _120557 P Q) = (term267 _120557 P Q).
Proof. exact (@lem5756018 _120557 P Q). Qed.
Lemma lem5756020 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term270 _120557 x s t) = (term269 _120557 x s t).
Proof. exact (@lem5756019 _120557 (term271 _120557 x s t) (term272 _120557 x s t)). Qed.
Lemma lem5756021 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term273 _120557 x s t x') = (term167 _120557 x s t x').
Proof. exact (eq_refl (term273 _120557 x s t x')). Qed.
Lemma lem5756022 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term280 _120557 x s t) = (term271 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756021 _120557 x s t x')). Qed.
Lemma lem5756023 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756024 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term281 _120557 x s t) = (term282 _120557 x s t).
Proof. exact (MK_COMB (@lem5756023 _120557) (@lem5756022 _120557 x s t)). Qed.
Lemma lem5756025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756026 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term283 _120557 x s t) = (term284 _120557 x s t).
Proof. exact (MK_COMB (@lem5756025) (@lem5756024 _120557 x s t)). Qed.
Lemma lem5756027 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term275 _120557 x s t x') = (term164 _120557 x s t x').
Proof. exact (eq_refl (term275 _120557 x s t x')). Qed.
Lemma lem5756028 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term285 _120557 x s t) = (term272 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756027 _120557 x s t x')). Qed.
Lemma lem5756029 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756030 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term286 _120557 x s t) = (term287 _120557 x s t).
Proof. exact (MK_COMB (@lem5756029 _120557) (@lem5756028 _120557 x s t)). Qed.
Lemma lem5756031 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term270 _120557 x s t) = (term288 _120557 x s t).
Proof. exact (MK_COMB (@lem5756026 _120557 x s t) (@lem5756030 _120557 x s t)). Qed.
Lemma lem5756032 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5756033 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term429 _120557 x s t) = (term430 _120557 x s t).
Proof. exact (MK_COMB (@lem5756032) (@lem5756031 _120557 x s t)). Qed.
Lemma lem5756034 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term273 _120557 x s t x') = (term167 _120557 x s t x').
Proof. exact (eq_refl (term273 _120557 x s t x')). Qed.
Lemma lem5756035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756036 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term274 _120557 x s t x') = (term169 _120557 x s t x').
Proof. exact (MK_COMB (@lem5756035) (@lem5756034 _120557 x s t x')). Qed.
Lemma lem5756037 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term275 _120557 x s t x') = (term164 _120557 x s t x').
Proof. exact (eq_refl (term275 _120557 x s t x')). Qed.
Lemma lem5756038 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term276 _120557 x s t x') = (term171 _120557 x s t x').
Proof. exact (MK_COMB (@lem5756036 _120557 x s t x') (@lem5756037 _120557 x s t x')). Qed.
Lemma lem5756039 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term277 _120557 x s t) = (term180 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756038 _120557 x s t x')). Qed.
Lemma lem5756040 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756041 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term269 _120557 x s t) = (term181 _120557 x s t).
Proof. exact (MK_COMB (@lem5756040 _120557) (@lem5756039 _120557 x s t)). Qed.
Lemma lem5756042 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term270 _120557 x s t) = (term269 _120557 x s t)) = ((term288 _120557 x s t) = (term181 _120557 x s t)).
Proof. exact (MK_COMB (@lem5756033 _120557 x s t) (@lem5756041 _120557 x s t)). Qed.
Lemma lem5756043 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term288 _120557 x s t) = (term181 _120557 x s t).
Proof. exact (EQ_MP (@lem5756042 _120557 x s t) (@lem5756020 _120557 x s t)). Qed.
Lemma lem5756044 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term289 _120557 s t) = (term186 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756043 _120557 x s t)). Qed.
Lemma lem5756045 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756046 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term290 _120557 s t) = (term187 _120557 s t).
Proof. exact (MK_COMB (@lem5756045 _120557) (@lem5756044 _120557 s t)). Qed.
Lemma lem5756047 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term310 _120557 s t) = (term187 _120557 s t).
Proof. exact (TRANS (@lem5756016 _120557 s t) (@lem5756046 _120557 s t)). Qed.
Lemma lem5756048 {_120557 : Type'} (t : _120557 -> Prop) : (term311 _120557 t) = (term194 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5756047 _120557 s t)). Qed.
Lemma lem5756049 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756050 {_120557 : Type'} (t : _120557 -> Prop) : (term312 _120557 t) = (term195 _120557 t).
Proof. exact (MK_COMB (@lem5756049 _120557) (@lem5756048 _120557 t)). Qed.
Lemma lem5756051 {_120557 : Type'} (t : _120557 -> Prop) : (term334 _120557 t) = (term195 _120557 t).
Proof. exact (TRANS (@lem5755989 _120557 t) (@lem5756050 _120557 t)). Qed.
Lemma lem5756052 {_120557 : Type'} : (term335 _120557) = (term200 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5756051 _120557 t)). Qed.
Lemma lem5756053 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756054 {_120557 : Type'} : (term336 _120557) = (term201 _120557).
Proof. exact (MK_COMB (@lem5756053 _120557) (@lem5756052 _120557)). Qed.
Lemma lem5756055 {_120557 : Type'} : (term356 _120557) = (term201 _120557).
Proof. exact (TRANS (@lem5755962 _120557) (@lem5756054 _120557)). Qed.
Lemma lem5756056 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756057 {_120557 : Type'} : (term357 _120557) = (term264 _120557).
Proof. exact (MK_COMB (@lem5756056) (@lem5756055 _120557)). Qed.
Lemma lem5756059 {A : Type'} (P : Prop) (Q : A -> Prop) : (term431 A P Q) = (term432 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5756060 {_120557 : Type'} (P : Prop) (Q : _120557 -> Prop) : (term431 _120557 P Q) = (term432 _120557 P Q).
Proof. exact (@lem5756059 _120557 P Q). Qed.
Lemma lem5756061 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term433 _120557 x s t) = (term434 _120557 x s t).
Proof. exact (@lem5756060 _120557 (s x) (term223 _120557 s t)). Qed.
Lemma lem5756062 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : (term435 _120557 s t x) = (term55 _120557 s t x).
Proof. exact (eq_refl (term435 _120557 s t x)). Qed.
Lemma lem5756063 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term436 _120557 s t) = (term223 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756062 _120557 s t x)). Qed.
Lemma lem5756064 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756065 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term437 _120557 s t) = (term224 _120557 s t).
Proof. exact (MK_COMB (@lem5756064 _120557) (@lem5756063 _120557 s t)). Qed.
Lemma lem5756066 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (term22 _120557 s x) = (term22 _120557 s x).
Proof. exact (eq_refl (term22 _120557 s x)). Qed.
Lemma lem5756067 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term433 _120557 x s t) = (term229 _120557 x s t).
Proof. exact (MK_COMB (@lem5756066 _120557 s x) (@lem5756065 _120557 s t)). Qed.
Lemma lem5756068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5756069 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term438 _120557 x s t) = (term439 _120557 x s t).
Proof. exact (MK_COMB (@lem5756068) (@lem5756067 _120557 x s t)). Qed.
Lemma lem5756070 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term435 _120557 s t x') = (term55 _120557 s t x').
Proof. exact (eq_refl (term435 _120557 s t x')). Qed.
Lemma lem5756071 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (term22 _120557 s x) = (term22 _120557 s x).
Proof. exact (eq_refl (term22 _120557 s x)). Qed.
Lemma lem5756072 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term440 _120557 x s t x') = (term441 _120557 x s t x').
Proof. exact (MK_COMB (@lem5756071 _120557 s x) (@lem5756070 _120557 s t x')). Qed.
Lemma lem5756073 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term442 _120557 x s t) = (term443 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756072 _120557 x s t x')). Qed.
Lemma lem5756074 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756075 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term434 _120557 x s t) = (term444 _120557 x s t).
Proof. exact (MK_COMB (@lem5756074 _120557) (@lem5756073 _120557 x s t)). Qed.
Lemma lem5756076 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term433 _120557 x s t) = (term434 _120557 x s t)) = ((term229 _120557 x s t) = (term444 _120557 x s t)).
Proof. exact (MK_COMB (@lem5756069 _120557 x s t) (@lem5756075 _120557 x s t)). Qed.
Lemma lem5756077 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term229 _120557 x s t) = (term444 _120557 x s t).
Proof. exact (EQ_MP (@lem5756076 _120557 x s t) (@lem5756061 _120557 x s t)). Qed.
Lemma lem5756078 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term237 _120557 s x t) = (term237 _120557 s x t).
Proof. exact (eq_refl (term237 _120557 s x t)). Qed.
Lemma lem5756079 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term239 _120557 x s t) = (term445 _120557 x s t).
Proof. exact (MK_COMB (@lem5756078 _120557 s x t) (@lem5756077 _120557 x s t)). Qed.
Lemma lem5756081 {A : Type'} (P : Prop) (Q : A -> Prop) : (term446 A P Q) = (term447 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5756082 {_120557 : Type'} (P : Prop) (Q : _120557 -> Prop) : (term446 _120557 P Q) = (term447 _120557 P Q).
Proof. exact (@lem5756081 _120557 P Q). Qed.
Lemma lem5756083 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term448 _120557 x s t) = (term449 _120557 x s t).
Proof. exact (@lem5756082 _120557 (term214 _120557 s x t) (term443 _120557 x s t)). Qed.
Lemma lem5756084 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term450 _120557 x s t x') = (term441 _120557 x s t x').
Proof. exact (eq_refl (term450 _120557 x s t x')). Qed.
Lemma lem5756085 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term451 _120557 x s t) = (term443 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756084 _120557 x s t x')). Qed.
Lemma lem5756086 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756087 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term452 _120557 x s t) = (term444 _120557 x s t).
Proof. exact (MK_COMB (@lem5756086 _120557) (@lem5756085 _120557 x s t)). Qed.
Lemma lem5756088 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term237 _120557 s x t) = (term237 _120557 s x t).
Proof. exact (eq_refl (term237 _120557 s x t)). Qed.
Lemma lem5756089 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term448 _120557 x s t) = (term445 _120557 x s t).
Proof. exact (MK_COMB (@lem5756088 _120557 s x t) (@lem5756087 _120557 x s t)). Qed.
Lemma lem5756090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5756091 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term453 _120557 x s t) = (term454 _120557 x s t).
Proof. exact (MK_COMB (@lem5756090) (@lem5756089 _120557 x s t)). Qed.
Lemma lem5756092 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term450 _120557 x s t x') = (term441 _120557 x s t x').
Proof. exact (eq_refl (term450 _120557 x s t x')). Qed.
Lemma lem5756093 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term237 _120557 s x t) = (term237 _120557 s x t).
Proof. exact (eq_refl (term237 _120557 s x t)). Qed.
Lemma lem5756094 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term455 _120557 x s t x') = (term456 _120557 x s t x').
Proof. exact (MK_COMB (@lem5756093 _120557 s x t) (@lem5756092 _120557 x s t x')). Qed.
Lemma lem5756095 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term457 _120557 x s t) = (term458 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756094 _120557 x s t x')). Qed.
Lemma lem5756096 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756097 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term449 _120557 x s t) = (term459 _120557 x s t).
Proof. exact (MK_COMB (@lem5756096 _120557) (@lem5756095 _120557 x s t)). Qed.
Lemma lem5756098 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term448 _120557 x s t) = (term449 _120557 x s t)) = ((term445 _120557 x s t) = (term459 _120557 x s t)).
Proof. exact (MK_COMB (@lem5756091 _120557 x s t) (@lem5756097 _120557 x s t)). Qed.
Lemma lem5756099 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term445 _120557 x s t) = (term459 _120557 x s t).
Proof. exact (EQ_MP (@lem5756098 _120557 x s t) (@lem5756083 _120557 x s t)). Qed.
Lemma lem5756100 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term239 _120557 x s t) = (term459 _120557 x s t).
Proof. exact (TRANS (@lem5756079 _120557 x s t) (@lem5756099 _120557 x s t)). Qed.
Lemma lem5756101 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term360 _120557 s t) = (term460 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756100 _120557 x s t)). Qed.
Lemma lem5756102 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756103 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term371 _120557 s t) = (term461 _120557 s t).
Proof. exact (MK_COMB (@lem5756102 _120557) (@lem5756101 _120557 s t)). Qed.
Lemma lem5756104 {_120557 : Type'} (t : _120557 -> Prop) : (term382 _120557 t) = (term462 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5756103 _120557 s t)). Qed.
Lemma lem5756105 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756106 {_120557 : Type'} (t : _120557 -> Prop) : (term393 _120557 t) = (term463 _120557 t).
Proof. exact (MK_COMB (@lem5756105 _120557) (@lem5756104 _120557 t)). Qed.
Lemma lem5756107 {_120557 : Type'} : (term404 _120557) = (term464 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5756106 _120557 t)). Qed.
Lemma lem5756108 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756109 {_120557 : Type'} : (term415 _120557) = (term465 _120557).
Proof. exact (MK_COMB (@lem5756108 _120557) (@lem5756107 _120557)). Qed.
Lemma lem5756110 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756111 {_120557 : Type'} : (term417 _120557) = (term466 _120557).
Proof. exact (MK_COMB (@lem5756110) (@lem5756109 _120557)). Qed.
Lemma lem5756113 {A : Type'} (P : A -> Prop) (Q : Prop) : (term467 A P Q) = (term468 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5756114 {_120557 : Type'} (P : _120557 -> Prop) (Q : Prop) : (term467 _120557 P Q) = (term468 _120557 P Q).
Proof. exact (@lem5756113 _120557 P Q). Qed.
Lemma lem5756115 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term469 _120557 x s t) = (term470 _120557 x s t).
Proof. exact (@lem5756114 _120557 (term211 _120557 s x t) (term231 _120557 x s t)). Qed.
Lemma lem5756116 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term471 _120557 s x t x') = (term44 _120557 s x t x').
Proof. exact (eq_refl (term471 _120557 s x t x')). Qed.
Lemma lem5756117 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term472 _120557 s x t) = (term211 _120557 s x t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756116 _120557 s x t x')). Qed.
Lemma lem5756118 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756119 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term473 _120557 s x t) = (term212 _120557 s x t).
Proof. exact (MK_COMB (@lem5756118 _120557) (@lem5756117 _120557 s x t)). Qed.
Lemma lem5756120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5756121 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term474 _120557 s x t) = (term233 _120557 s x t).
Proof. exact (MK_COMB (@lem5756120) (@lem5756119 _120557 s x t)). Qed.
Lemma lem5756122 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term231 _120557 x s t) = (term231 _120557 x s t).
Proof. exact (eq_refl (term231 _120557 x s t)). Qed.
Lemma lem5756123 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term469 _120557 x s t) = (term235 _120557 x s t).
Proof. exact (MK_COMB (@lem5756121 _120557 s x t) (@lem5756122 _120557 x s t)). Qed.
Lemma lem5756124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5756125 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term475 _120557 x s t) = (term476 _120557 x s t).
Proof. exact (MK_COMB (@lem5756124) (@lem5756123 _120557 x s t)). Qed.
Lemma lem5756126 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term471 _120557 s x t x') = (term44 _120557 s x t x').
Proof. exact (eq_refl (term471 _120557 s x t x')). Qed.
Lemma lem5756127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5756128 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term477 _120557 s x t x') = (term478 _120557 s x t x').
Proof. exact (MK_COMB (@lem5756127) (@lem5756126 _120557 s x t x')). Qed.
Lemma lem5756129 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term231 _120557 x s t) = (term231 _120557 x s t).
Proof. exact (eq_refl (term231 _120557 x s t)). Qed.
Lemma lem5756130 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term479 _120557 x' x s t) = (term480 _120557 x' x s t).
Proof. exact (MK_COMB (@lem5756128 _120557 s x t x') (@lem5756129 _120557 x s t)). Qed.
Lemma lem5756131 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term481 _120557 x s t) = (term482 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756130 _120557 x' x s t)). Qed.
Lemma lem5756132 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756133 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term470 _120557 x s t) = (term483 _120557 x s t).
Proof. exact (MK_COMB (@lem5756132 _120557) (@lem5756131 _120557 x s t)). Qed.
Lemma lem5756134 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term469 _120557 x s t) = (term470 _120557 x s t)) = ((term235 _120557 x s t) = (term483 _120557 x s t)).
Proof. exact (MK_COMB (@lem5756125 _120557 x s t) (@lem5756133 _120557 x s t)). Qed.
Lemma lem5756135 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term235 _120557 x s t) = (term483 _120557 x s t).
Proof. exact (EQ_MP (@lem5756134 _120557 x s t) (@lem5756115 _120557 x s t)). Qed.
Lemma lem5756136 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term361 _120557 s t) = (term484 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756135 _120557 x s t)). Qed.
Lemma lem5756137 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756138 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term376 _120557 s t) = (term485 _120557 s t).
Proof. exact (MK_COMB (@lem5756137 _120557) (@lem5756136 _120557 s t)). Qed.
Lemma lem5756139 {_120557 : Type'} (t : _120557 -> Prop) : (term383 _120557 t) = (term486 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5756138 _120557 s t)). Qed.
Lemma lem5756140 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756141 {_120557 : Type'} (t : _120557 -> Prop) : (term398 _120557 t) = (term487 _120557 t).
Proof. exact (MK_COMB (@lem5756140 _120557) (@lem5756139 _120557 t)). Qed.
Lemma lem5756142 {_120557 : Type'} : (term405 _120557) = (term488 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5756141 _120557 t)). Qed.
Lemma lem5756143 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756144 {_120557 : Type'} : (term420 _120557) = (term489 _120557).
Proof. exact (MK_COMB (@lem5756143 _120557) (@lem5756142 _120557)). Qed.
Lemma lem5756145 {_120557 : Type'} : (term421 _120557) = (term490 _120557).
Proof. exact (MK_COMB (@lem5756111 _120557) (@lem5756144 _120557)). Qed.
Lemma lem5756147 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term268 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5756148 {_120557 : Type'} (P : type686 _120557) (Q : type686 _120557) : (term314 _120557 P Q) = (term313 _120557 P Q).
Proof. exact (@lem5756147 (_120557 -> Prop) P Q). Qed.
Lemma lem5756149 {_120557 : Type'} : (term491 _120557) = (term492 _120557).
Proof. exact (@lem5756148 _120557 (term464 _120557) (term488 _120557)). Qed.
Lemma lem5756150 {_120557 : Type'} (t : _120557 -> Prop) : (term493 _120557 t) = (term463 _120557 t).
Proof. exact (eq_refl (term493 _120557 t)). Qed.
Lemma lem5756151 {_120557 : Type'} : (term494 _120557) = (term464 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5756150 _120557 t)). Qed.
Lemma lem5756152 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756153 {_120557 : Type'} : (term495 _120557) = (term465 _120557).
Proof. exact (MK_COMB (@lem5756152 _120557) (@lem5756151 _120557)). Qed.
Lemma lem5756154 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756155 {_120557 : Type'} : (term496 _120557) = (term466 _120557).
Proof. exact (MK_COMB (@lem5756154) (@lem5756153 _120557)). Qed.
Lemma lem5756156 {_120557 : Type'} (t : _120557 -> Prop) : (term497 _120557 t) = (term487 _120557 t).
Proof. exact (eq_refl (term497 _120557 t)). Qed.
Lemma lem5756157 {_120557 : Type'} : (term498 _120557) = (term488 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5756156 _120557 t)). Qed.
Lemma lem5756158 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756159 {_120557 : Type'} : (term499 _120557) = (term489 _120557).
Proof. exact (MK_COMB (@lem5756158 _120557) (@lem5756157 _120557)). Qed.
Lemma lem5756160 {_120557 : Type'} : (term491 _120557) = (term490 _120557).
Proof. exact (MK_COMB (@lem5756155 _120557) (@lem5756159 _120557)). Qed.
Lemma lem5756161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5756162 {_120557 : Type'} : (term500 _120557) = (term501 _120557).
Proof. exact (MK_COMB (@lem5756161) (@lem5756160 _120557)). Qed.
Lemma lem5756163 {_120557 : Type'} (t : _120557 -> Prop) : (term493 _120557 t) = (term463 _120557 t).
Proof. exact (eq_refl (term493 _120557 t)). Qed.
Lemma lem5756164 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756165 {_120557 : Type'} (t : _120557 -> Prop) : (term502 _120557 t) = (term503 _120557 t).
Proof. exact (MK_COMB (@lem5756164) (@lem5756163 _120557 t)). Qed.
Lemma lem5756166 {_120557 : Type'} (t : _120557 -> Prop) : (term497 _120557 t) = (term487 _120557 t).
Proof. exact (eq_refl (term497 _120557 t)). Qed.
Lemma lem5756167 {_120557 : Type'} (t : _120557 -> Prop) : (term504 _120557 t) = (term505 _120557 t).
Proof. exact (MK_COMB (@lem5756165 _120557 t) (@lem5756166 _120557 t)). Qed.
Lemma lem5756168 {_120557 : Type'} : (term506 _120557) = (term507 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5756167 _120557 t)). Qed.
Lemma lem5756169 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756170 {_120557 : Type'} : (term492 _120557) = (term508 _120557).
Proof. exact (MK_COMB (@lem5756169 _120557) (@lem5756168 _120557)). Qed.
Lemma lem5756171 {_120557 : Type'} : ((term491 _120557) = (term492 _120557)) = ((term490 _120557) = (term508 _120557)).
Proof. exact (MK_COMB (@lem5756162 _120557) (@lem5756170 _120557)). Qed.
Lemma lem5756172 {_120557 : Type'} : (term490 _120557) = (term508 _120557).
Proof. exact (EQ_MP (@lem5756171 _120557) (@lem5756149 _120557)). Qed.
Lemma lem5756174 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term268 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5756175 {_120557 : Type'} (P : type686 _120557) (Q : type686 _120557) : (term314 _120557 P Q) = (term313 _120557 P Q).
Proof. exact (@lem5756174 (_120557 -> Prop) P Q). Qed.
Lemma lem5756176 {_120557 : Type'} (t : _120557 -> Prop) : (term509 _120557 t) = (term510 _120557 t).
Proof. exact (@lem5756175 _120557 (term462 _120557 t) (term486 _120557 t)). Qed.
Lemma lem5756177 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term511 _120557 t s) = (term461 _120557 s t).
Proof. exact (eq_refl (term511 _120557 t s)). Qed.
Lemma lem5756178 {_120557 : Type'} (t : _120557 -> Prop) : (term512 _120557 t) = (term462 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5756177 _120557 s t)). Qed.
Lemma lem5756179 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756180 {_120557 : Type'} (t : _120557 -> Prop) : (term513 _120557 t) = (term463 _120557 t).
Proof. exact (MK_COMB (@lem5756179 _120557) (@lem5756178 _120557 t)). Qed.
Lemma lem5756181 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756182 {_120557 : Type'} (t : _120557 -> Prop) : (term514 _120557 t) = (term503 _120557 t).
Proof. exact (MK_COMB (@lem5756181) (@lem5756180 _120557 t)). Qed.
Lemma lem5756183 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term515 _120557 t s) = (term485 _120557 s t).
Proof. exact (eq_refl (term515 _120557 t s)). Qed.
Lemma lem5756184 {_120557 : Type'} (t : _120557 -> Prop) : (term516 _120557 t) = (term486 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5756183 _120557 s t)). Qed.
Lemma lem5756185 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756186 {_120557 : Type'} (t : _120557 -> Prop) : (term517 _120557 t) = (term487 _120557 t).
Proof. exact (MK_COMB (@lem5756185 _120557) (@lem5756184 _120557 t)). Qed.
Lemma lem5756187 {_120557 : Type'} (t : _120557 -> Prop) : (term509 _120557 t) = (term505 _120557 t).
Proof. exact (MK_COMB (@lem5756182 _120557 t) (@lem5756186 _120557 t)). Qed.
Lemma lem5756188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5756189 {_120557 : Type'} (t : _120557 -> Prop) : (term518 _120557 t) = (term519 _120557 t).
Proof. exact (MK_COMB (@lem5756188) (@lem5756187 _120557 t)). Qed.
Lemma lem5756190 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term511 _120557 t s) = (term461 _120557 s t).
Proof. exact (eq_refl (term511 _120557 t s)). Qed.
Lemma lem5756191 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756192 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term520 _120557 t s) = (term521 _120557 s t).
Proof. exact (MK_COMB (@lem5756191) (@lem5756190 _120557 s t)). Qed.
Lemma lem5756193 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term515 _120557 t s) = (term485 _120557 s t).
Proof. exact (eq_refl (term515 _120557 t s)). Qed.
Lemma lem5756194 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term522 _120557 t s) = (term523 _120557 s t).
Proof. exact (MK_COMB (@lem5756192 _120557 s t) (@lem5756193 _120557 s t)). Qed.
Lemma lem5756195 {_120557 : Type'} (t : _120557 -> Prop) : (term524 _120557 t) = (term525 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5756194 _120557 s t)). Qed.
Lemma lem5756196 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756197 {_120557 : Type'} (t : _120557 -> Prop) : (term510 _120557 t) = (term526 _120557 t).
Proof. exact (MK_COMB (@lem5756196 _120557) (@lem5756195 _120557 t)). Qed.
Lemma lem5756198 {_120557 : Type'} (t : _120557 -> Prop) : ((term509 _120557 t) = (term510 _120557 t)) = ((term505 _120557 t) = (term526 _120557 t)).
Proof. exact (MK_COMB (@lem5756189 _120557 t) (@lem5756197 _120557 t)). Qed.
Lemma lem5756199 {_120557 : Type'} (t : _120557 -> Prop) : (term505 _120557 t) = (term526 _120557 t).
Proof. exact (EQ_MP (@lem5756198 _120557 t) (@lem5756176 _120557 t)). Qed.
Lemma lem5756201 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term268 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5756202 {_120557 : Type'} (P : _120557 -> Prop) (Q : _120557 -> Prop) : (term268 _120557 P Q) = (term267 _120557 P Q).
Proof. exact (@lem5756201 _120557 P Q). Qed.
Lemma lem5756203 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term527 _120557 s t) = (term528 _120557 s t).
Proof. exact (@lem5756202 _120557 (term460 _120557 s t) (term484 _120557 s t)). Qed.
Lemma lem5756204 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term529 _120557 s t x) = (term459 _120557 x s t).
Proof. exact (eq_refl (term529 _120557 s t x)). Qed.
Lemma lem5756205 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term530 _120557 s t) = (term460 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756204 _120557 x s t)). Qed.
Lemma lem5756206 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756207 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term531 _120557 s t) = (term461 _120557 s t).
Proof. exact (MK_COMB (@lem5756206 _120557) (@lem5756205 _120557 s t)). Qed.
Lemma lem5756208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756209 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term532 _120557 s t) = (term521 _120557 s t).
Proof. exact (MK_COMB (@lem5756208) (@lem5756207 _120557 s t)). Qed.
Lemma lem5756210 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term533 _120557 s t x) = (term483 _120557 x s t).
Proof. exact (eq_refl (term533 _120557 s t x)). Qed.
Lemma lem5756211 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term534 _120557 s t) = (term484 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756210 _120557 x s t)). Qed.
Lemma lem5756212 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756213 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term535 _120557 s t) = (term485 _120557 s t).
Proof. exact (MK_COMB (@lem5756212 _120557) (@lem5756211 _120557 s t)). Qed.
Lemma lem5756214 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term527 _120557 s t) = (term523 _120557 s t).
Proof. exact (MK_COMB (@lem5756209 _120557 s t) (@lem5756213 _120557 s t)). Qed.
Lemma lem5756215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5756216 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term536 _120557 s t) = (term537 _120557 s t).
Proof. exact (MK_COMB (@lem5756215) (@lem5756214 _120557 s t)). Qed.
Lemma lem5756217 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term529 _120557 s t x) = (term459 _120557 x s t).
Proof. exact (eq_refl (term529 _120557 s t x)). Qed.
Lemma lem5756218 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756219 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term538 _120557 s t x) = (term539 _120557 x s t).
Proof. exact (MK_COMB (@lem5756218) (@lem5756217 _120557 x s t)). Qed.
Lemma lem5756220 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term533 _120557 s t x) = (term483 _120557 x s t).
Proof. exact (eq_refl (term533 _120557 s t x)). Qed.
Lemma lem5756221 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term540 _120557 s t x) = (term541 _120557 x s t).
Proof. exact (MK_COMB (@lem5756219 _120557 x s t) (@lem5756220 _120557 x s t)). Qed.
Lemma lem5756222 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term542 _120557 s t) = (term543 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756221 _120557 x s t)). Qed.
Lemma lem5756223 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756224 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term528 _120557 s t) = (term544 _120557 s t).
Proof. exact (MK_COMB (@lem5756223 _120557) (@lem5756222 _120557 s t)). Qed.
Lemma lem5756225 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term527 _120557 s t) = (term528 _120557 s t)) = ((term523 _120557 s t) = (term544 _120557 s t)).
Proof. exact (MK_COMB (@lem5756216 _120557 s t) (@lem5756224 _120557 s t)). Qed.
Lemma lem5756226 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term523 _120557 s t) = (term544 _120557 s t).
Proof. exact (EQ_MP (@lem5756225 _120557 s t) (@lem5756203 _120557 s t)). Qed.
Lemma lem5756228 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term268 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5756229 {_120557 : Type'} (P : _120557 -> Prop) (Q : _120557 -> Prop) : (term268 _120557 P Q) = (term267 _120557 P Q).
Proof. exact (@lem5756228 _120557 P Q). Qed.
Lemma lem5756230 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term545 _120557 x s t) = (term546 _120557 x s t).
Proof. exact (@lem5756229 _120557 (term458 _120557 x s t) (term482 _120557 x s t)). Qed.
Lemma lem5756231 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term547 _120557 x s t x') = (term456 _120557 x s t x').
Proof. exact (eq_refl (term547 _120557 x s t x')). Qed.
Lemma lem5756232 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term548 _120557 x s t) = (term458 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756231 _120557 x s t x')). Qed.
Lemma lem5756233 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756234 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term549 _120557 x s t) = (term459 _120557 x s t).
Proof. exact (MK_COMB (@lem5756233 _120557) (@lem5756232 _120557 x s t)). Qed.
Lemma lem5756235 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756236 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term550 _120557 x s t) = (term539 _120557 x s t).
Proof. exact (MK_COMB (@lem5756235) (@lem5756234 _120557 x s t)). Qed.
Lemma lem5756237 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term551 _120557 x s t x') = (term480 _120557 x' x s t).
Proof. exact (eq_refl (term551 _120557 x s t x')). Qed.
Lemma lem5756238 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term552 _120557 x s t) = (term482 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756237 _120557 x' x s t)). Qed.
Lemma lem5756239 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756240 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term553 _120557 x s t) = (term483 _120557 x s t).
Proof. exact (MK_COMB (@lem5756239 _120557) (@lem5756238 _120557 x s t)). Qed.
Lemma lem5756241 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term545 _120557 x s t) = (term541 _120557 x s t).
Proof. exact (MK_COMB (@lem5756236 _120557 x s t) (@lem5756240 _120557 x s t)). Qed.
Lemma lem5756242 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5756243 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term554 _120557 x s t) = (term555 _120557 x s t).
Proof. exact (MK_COMB (@lem5756242) (@lem5756241 _120557 x s t)). Qed.
Lemma lem5756244 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term547 _120557 x s t x') = (term456 _120557 x s t x').
Proof. exact (eq_refl (term547 _120557 x s t x')). Qed.
Lemma lem5756245 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756246 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term556 _120557 x s t x') = (term557 _120557 x s t x').
Proof. exact (MK_COMB (@lem5756245) (@lem5756244 _120557 x s t x')). Qed.
Lemma lem5756247 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term551 _120557 x s t x') = (term480 _120557 x' x s t).
Proof. exact (eq_refl (term551 _120557 x s t x')). Qed.
Lemma lem5756248 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term558 _120557 x s t x') = (term559 _120557 x' x s t).
Proof. exact (MK_COMB (@lem5756246 _120557 x s t x') (@lem5756247 _120557 x' x s t)). Qed.
Lemma lem5756249 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term560 _120557 x s t) = (term561 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756248 _120557 x' x s t)). Qed.
Lemma lem5756250 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756251 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term546 _120557 x s t) = (term562 _120557 x s t).
Proof. exact (MK_COMB (@lem5756250 _120557) (@lem5756249 _120557 x s t)). Qed.
Lemma lem5756252 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term545 _120557 x s t) = (term546 _120557 x s t)) = ((term541 _120557 x s t) = (term562 _120557 x s t)).
Proof. exact (MK_COMB (@lem5756243 _120557 x s t) (@lem5756251 _120557 x s t)). Qed.
Lemma lem5756253 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term541 _120557 x s t) = (term562 _120557 x s t).
Proof. exact (EQ_MP (@lem5756252 _120557 x s t) (@lem5756230 _120557 x s t)). Qed.
Lemma lem5756254 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term543 _120557 s t) = (term563 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756253 _120557 x s t)). Qed.
Lemma lem5756255 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756256 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term544 _120557 s t) = (term564 _120557 s t).
Proof. exact (MK_COMB (@lem5756255 _120557) (@lem5756254 _120557 s t)). Qed.
Lemma lem5756257 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term523 _120557 s t) = (term564 _120557 s t).
Proof. exact (TRANS (@lem5756226 _120557 s t) (@lem5756256 _120557 s t)). Qed.
Lemma lem5756258 {_120557 : Type'} (t : _120557 -> Prop) : (term525 _120557 t) = (term565 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5756257 _120557 s t)). Qed.
Lemma lem5756259 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756260 {_120557 : Type'} (t : _120557 -> Prop) : (term526 _120557 t) = (term566 _120557 t).
Proof. exact (MK_COMB (@lem5756259 _120557) (@lem5756258 _120557 t)). Qed.
Lemma lem5756261 {_120557 : Type'} (t : _120557 -> Prop) : (term505 _120557 t) = (term566 _120557 t).
Proof. exact (TRANS (@lem5756199 _120557 t) (@lem5756260 _120557 t)). Qed.
Lemma lem5756262 {_120557 : Type'} : (term507 _120557) = (term567 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5756261 _120557 t)). Qed.
Lemma lem5756263 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756264 {_120557 : Type'} : (term508 _120557) = (term568 _120557).
Proof. exact (MK_COMB (@lem5756263 _120557) (@lem5756262 _120557)). Qed.
Lemma lem5756265 {_120557 : Type'} : (term490 _120557) = (term568 _120557).
Proof. exact (TRANS (@lem5756172 _120557) (@lem5756264 _120557)). Qed.
Lemma lem5756266 {_120557 : Type'} : (term421 _120557) = (term568 _120557).
Proof. exact (TRANS (@lem5756145 _120557) (@lem5756265 _120557)). Qed.
Lemma lem5756267 {_120557 : Type'} : (term422 _120557) = (term569 _120557).
Proof. exact (MK_COMB (@lem5756057 _120557) (@lem5756266 _120557)). Qed.
Lemma lem5756269 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term268 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5756270 {_120557 : Type'} (P : type686 _120557) (Q : type686 _120557) : (term314 _120557 P Q) = (term313 _120557 P Q).
Proof. exact (@lem5756269 (_120557 -> Prop) P Q). Qed.
Lemma lem5756271 {_120557 : Type'} : (term570 _120557) = (term571 _120557).
Proof. exact (@lem5756270 _120557 (term200 _120557) (term567 _120557)). Qed.
Lemma lem5756272 {_120557 : Type'} (t : _120557 -> Prop) : (term572 _120557 t) = (term195 _120557 t).
Proof. exact (eq_refl (term572 _120557 t)). Qed.
Lemma lem5756273 {_120557 : Type'} : (term573 _120557) = (term200 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5756272 _120557 t)). Qed.
Lemma lem5756274 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756275 {_120557 : Type'} : (term574 _120557) = (term201 _120557).
Proof. exact (MK_COMB (@lem5756274 _120557) (@lem5756273 _120557)). Qed.
Lemma lem5756276 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756277 {_120557 : Type'} : (term575 _120557) = (term264 _120557).
Proof. exact (MK_COMB (@lem5756276) (@lem5756275 _120557)). Qed.
Lemma lem5756278 {_120557 : Type'} (t : _120557 -> Prop) : (term576 _120557 t) = (term566 _120557 t).
Proof. exact (eq_refl (term576 _120557 t)). Qed.
Lemma lem5756279 {_120557 : Type'} : (term577 _120557) = (term567 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5756278 _120557 t)). Qed.
Lemma lem5756280 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756281 {_120557 : Type'} : (term578 _120557) = (term568 _120557).
Proof. exact (MK_COMB (@lem5756280 _120557) (@lem5756279 _120557)). Qed.
Lemma lem5756282 {_120557 : Type'} : (term570 _120557) = (term569 _120557).
Proof. exact (MK_COMB (@lem5756277 _120557) (@lem5756281 _120557)). Qed.
Lemma lem5756283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5756284 {_120557 : Type'} : (term579 _120557) = (term580 _120557).
Proof. exact (MK_COMB (@lem5756283) (@lem5756282 _120557)). Qed.
Lemma lem5756285 {_120557 : Type'} (t : _120557 -> Prop) : (term572 _120557 t) = (term195 _120557 t).
Proof. exact (eq_refl (term572 _120557 t)). Qed.
Lemma lem5756286 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756287 {_120557 : Type'} (t : _120557 -> Prop) : (term581 _120557 t) = (term582 _120557 t).
Proof. exact (MK_COMB (@lem5756286) (@lem5756285 _120557 t)). Qed.
Lemma lem5756288 {_120557 : Type'} (t : _120557 -> Prop) : (term576 _120557 t) = (term566 _120557 t).
Proof. exact (eq_refl (term576 _120557 t)). Qed.
Lemma lem5756289 {_120557 : Type'} (t : _120557 -> Prop) : (term583 _120557 t) = (term584 _120557 t).
Proof. exact (MK_COMB (@lem5756287 _120557 t) (@lem5756288 _120557 t)). Qed.
Lemma lem5756290 {_120557 : Type'} : (term585 _120557) = (term586 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5756289 _120557 t)). Qed.
Lemma lem5756291 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756292 {_120557 : Type'} : (term571 _120557) = (term587 _120557).
Proof. exact (MK_COMB (@lem5756291 _120557) (@lem5756290 _120557)). Qed.
Lemma lem5756293 {_120557 : Type'} : ((term570 _120557) = (term571 _120557)) = ((term569 _120557) = (term587 _120557)).
Proof. exact (MK_COMB (@lem5756284 _120557) (@lem5756292 _120557)). Qed.
Lemma lem5756294 {_120557 : Type'} : (term569 _120557) = (term587 _120557).
Proof. exact (EQ_MP (@lem5756293 _120557) (@lem5756271 _120557)). Qed.
Lemma lem5756296 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term268 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5756297 {_120557 : Type'} (P : type686 _120557) (Q : type686 _120557) : (term314 _120557 P Q) = (term313 _120557 P Q).
Proof. exact (@lem5756296 (_120557 -> Prop) P Q). Qed.
Lemma lem5756298 {_120557 : Type'} (t : _120557 -> Prop) : (term588 _120557 t) = (term589 _120557 t).
Proof. exact (@lem5756297 _120557 (term194 _120557 t) (term565 _120557 t)). Qed.
Lemma lem5756299 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term590 _120557 t s) = (term187 _120557 s t).
Proof. exact (eq_refl (term590 _120557 t s)). Qed.
Lemma lem5756300 {_120557 : Type'} (t : _120557 -> Prop) : (term591 _120557 t) = (term194 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5756299 _120557 s t)). Qed.
Lemma lem5756301 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756302 {_120557 : Type'} (t : _120557 -> Prop) : (term592 _120557 t) = (term195 _120557 t).
Proof. exact (MK_COMB (@lem5756301 _120557) (@lem5756300 _120557 t)). Qed.
Lemma lem5756303 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756304 {_120557 : Type'} (t : _120557 -> Prop) : (term593 _120557 t) = (term582 _120557 t).
Proof. exact (MK_COMB (@lem5756303) (@lem5756302 _120557 t)). Qed.
Lemma lem5756305 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term594 _120557 t s) = (term564 _120557 s t).
Proof. exact (eq_refl (term594 _120557 t s)). Qed.
Lemma lem5756306 {_120557 : Type'} (t : _120557 -> Prop) : (term595 _120557 t) = (term565 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5756305 _120557 s t)). Qed.
Lemma lem5756307 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756308 {_120557 : Type'} (t : _120557 -> Prop) : (term596 _120557 t) = (term566 _120557 t).
Proof. exact (MK_COMB (@lem5756307 _120557) (@lem5756306 _120557 t)). Qed.
Lemma lem5756309 {_120557 : Type'} (t : _120557 -> Prop) : (term588 _120557 t) = (term584 _120557 t).
Proof. exact (MK_COMB (@lem5756304 _120557 t) (@lem5756308 _120557 t)). Qed.
Lemma lem5756310 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5756311 {_120557 : Type'} (t : _120557 -> Prop) : (term597 _120557 t) = (term598 _120557 t).
Proof. exact (MK_COMB (@lem5756310) (@lem5756309 _120557 t)). Qed.
Lemma lem5756312 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term590 _120557 t s) = (term187 _120557 s t).
Proof. exact (eq_refl (term590 _120557 t s)). Qed.
Lemma lem5756313 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756314 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term599 _120557 t s) = (term600 _120557 s t).
Proof. exact (MK_COMB (@lem5756313) (@lem5756312 _120557 s t)). Qed.
Lemma lem5756315 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term594 _120557 t s) = (term564 _120557 s t).
Proof. exact (eq_refl (term594 _120557 t s)). Qed.
Lemma lem5756316 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term601 _120557 t s) = (term602 _120557 s t).
Proof. exact (MK_COMB (@lem5756314 _120557 s t) (@lem5756315 _120557 s t)). Qed.
Lemma lem5756317 {_120557 : Type'} (t : _120557 -> Prop) : (term603 _120557 t) = (term604 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5756316 _120557 s t)). Qed.
Lemma lem5756318 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756319 {_120557 : Type'} (t : _120557 -> Prop) : (term589 _120557 t) = (term605 _120557 t).
Proof. exact (MK_COMB (@lem5756318 _120557) (@lem5756317 _120557 t)). Qed.
Lemma lem5756320 {_120557 : Type'} (t : _120557 -> Prop) : ((term588 _120557 t) = (term589 _120557 t)) = ((term584 _120557 t) = (term605 _120557 t)).
Proof. exact (MK_COMB (@lem5756311 _120557 t) (@lem5756319 _120557 t)). Qed.
Lemma lem5756321 {_120557 : Type'} (t : _120557 -> Prop) : (term584 _120557 t) = (term605 _120557 t).
Proof. exact (EQ_MP (@lem5756320 _120557 t) (@lem5756298 _120557 t)). Qed.
Lemma lem5756323 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term268 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5756324 {_120557 : Type'} (P : _120557 -> Prop) (Q : _120557 -> Prop) : (term268 _120557 P Q) = (term267 _120557 P Q).
Proof. exact (@lem5756323 _120557 P Q). Qed.
Lemma lem5756325 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term606 _120557 s t) = (term607 _120557 s t).
Proof. exact (@lem5756324 _120557 (term186 _120557 s t) (term563 _120557 s t)). Qed.
Lemma lem5756326 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term608 _120557 s t x) = (term181 _120557 x s t).
Proof. exact (eq_refl (term608 _120557 s t x)). Qed.
Lemma lem5756327 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term609 _120557 s t) = (term186 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756326 _120557 x s t)). Qed.
Lemma lem5756328 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756329 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term610 _120557 s t) = (term187 _120557 s t).
Proof. exact (MK_COMB (@lem5756328 _120557) (@lem5756327 _120557 s t)). Qed.
Lemma lem5756330 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756331 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term611 _120557 s t) = (term600 _120557 s t).
Proof. exact (MK_COMB (@lem5756330) (@lem5756329 _120557 s t)). Qed.
Lemma lem5756332 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term612 _120557 s t x) = (term562 _120557 x s t).
Proof. exact (eq_refl (term612 _120557 s t x)). Qed.
Lemma lem5756333 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term613 _120557 s t) = (term563 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756332 _120557 x s t)). Qed.
Lemma lem5756334 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756335 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term614 _120557 s t) = (term564 _120557 s t).
Proof. exact (MK_COMB (@lem5756334 _120557) (@lem5756333 _120557 s t)). Qed.
Lemma lem5756336 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term606 _120557 s t) = (term602 _120557 s t).
Proof. exact (MK_COMB (@lem5756331 _120557 s t) (@lem5756335 _120557 s t)). Qed.
Lemma lem5756337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5756338 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term615 _120557 s t) = (term616 _120557 s t).
Proof. exact (MK_COMB (@lem5756337) (@lem5756336 _120557 s t)). Qed.
Lemma lem5756339 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term608 _120557 s t x) = (term181 _120557 x s t).
Proof. exact (eq_refl (term608 _120557 s t x)). Qed.
Lemma lem5756340 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756341 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term617 _120557 s t x) = (term618 _120557 x s t).
Proof. exact (MK_COMB (@lem5756340) (@lem5756339 _120557 x s t)). Qed.
Lemma lem5756342 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term612 _120557 s t x) = (term562 _120557 x s t).
Proof. exact (eq_refl (term612 _120557 s t x)). Qed.
Lemma lem5756343 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term619 _120557 s t x) = (term620 _120557 x s t).
Proof. exact (MK_COMB (@lem5756341 _120557 x s t) (@lem5756342 _120557 x s t)). Qed.
Lemma lem5756344 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term621 _120557 s t) = (term622 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756343 _120557 x s t)). Qed.
Lemma lem5756345 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756346 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term607 _120557 s t) = (term623 _120557 s t).
Proof. exact (MK_COMB (@lem5756345 _120557) (@lem5756344 _120557 s t)). Qed.
Lemma lem5756347 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term606 _120557 s t) = (term607 _120557 s t)) = ((term602 _120557 s t) = (term623 _120557 s t)).
Proof. exact (MK_COMB (@lem5756338 _120557 s t) (@lem5756346 _120557 s t)). Qed.
Lemma lem5756348 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term602 _120557 s t) = (term623 _120557 s t).
Proof. exact (EQ_MP (@lem5756347 _120557 s t) (@lem5756325 _120557 s t)). Qed.
Lemma lem5756350 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term268 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5756351 {_120557 : Type'} (P : _120557 -> Prop) (Q : _120557 -> Prop) : (term268 _120557 P Q) = (term267 _120557 P Q).
Proof. exact (@lem5756350 _120557 P Q). Qed.
Lemma lem5756352 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term624 _120557 x s t) = (term625 _120557 x s t).
Proof. exact (@lem5756351 _120557 (term180 _120557 x s t) (term561 _120557 x s t)). Qed.
Lemma lem5756353 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term626 _120557 x s t x') = (term171 _120557 x s t x').
Proof. exact (eq_refl (term626 _120557 x s t x')). Qed.
Lemma lem5756354 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term627 _120557 x s t) = (term180 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756353 _120557 x s t x')). Qed.
Lemma lem5756355 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756356 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term628 _120557 x s t) = (term181 _120557 x s t).
Proof. exact (MK_COMB (@lem5756355 _120557) (@lem5756354 _120557 x s t)). Qed.
Lemma lem5756357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756358 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term629 _120557 x s t) = (term618 _120557 x s t).
Proof. exact (MK_COMB (@lem5756357) (@lem5756356 _120557 x s t)). Qed.
Lemma lem5756359 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term630 _120557 x s t x') = (term559 _120557 x' x s t).
Proof. exact (eq_refl (term630 _120557 x s t x')). Qed.
Lemma lem5756360 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term631 _120557 x s t) = (term561 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756359 _120557 x' x s t)). Qed.
Lemma lem5756361 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756362 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term632 _120557 x s t) = (term562 _120557 x s t).
Proof. exact (MK_COMB (@lem5756361 _120557) (@lem5756360 _120557 x s t)). Qed.
Lemma lem5756363 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term624 _120557 x s t) = (term620 _120557 x s t).
Proof. exact (MK_COMB (@lem5756358 _120557 x s t) (@lem5756362 _120557 x s t)). Qed.
Lemma lem5756364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5756365 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term633 _120557 x s t) = (term634 _120557 x s t).
Proof. exact (MK_COMB (@lem5756364) (@lem5756363 _120557 x s t)). Qed.
Lemma lem5756366 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term626 _120557 x s t x') = (term171 _120557 x s t x').
Proof. exact (eq_refl (term626 _120557 x s t x')). Qed.
Lemma lem5756367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756368 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term635 _120557 x s t x') = (term636 _120557 x s t x').
Proof. exact (MK_COMB (@lem5756367) (@lem5756366 _120557 x s t x')). Qed.
Lemma lem5756369 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term630 _120557 x s t x') = (term559 _120557 x' x s t).
Proof. exact (eq_refl (term630 _120557 x s t x')). Qed.
Lemma lem5756370 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term637 _120557 x s t x') = (term638 _120557 x' x s t).
Proof. exact (MK_COMB (@lem5756368 _120557 x s t x') (@lem5756369 _120557 x' x s t)). Qed.
Lemma lem5756371 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term639 _120557 x s t) = (term640 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756370 _120557 x' x s t)). Qed.
Lemma lem5756372 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756373 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term625 _120557 x s t) = (term641 _120557 x s t).
Proof. exact (MK_COMB (@lem5756372 _120557) (@lem5756371 _120557 x s t)). Qed.
Lemma lem5756374 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : ((term624 _120557 x s t) = (term625 _120557 x s t)) = ((term620 _120557 x s t) = (term641 _120557 x s t)).
Proof. exact (MK_COMB (@lem5756365 _120557 x s t) (@lem5756373 _120557 x s t)). Qed.
Lemma lem5756375 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term620 _120557 x s t) = (term641 _120557 x s t).
Proof. exact (EQ_MP (@lem5756374 _120557 x s t) (@lem5756352 _120557 x s t)). Qed.
Lemma lem5756376 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term622 _120557 s t) = (term642 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756375 _120557 x s t)). Qed.
Lemma lem5756377 {_120557 : Type'} : (@ex _120557) = (@ex _120557).
Proof. exact (eq_refl (@ex _120557)). Qed.
Lemma lem5756378 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term623 _120557 s t) = (term643 _120557 s t).
Proof. exact (MK_COMB (@lem5756377 _120557) (@lem5756376 _120557 s t)). Qed.
Lemma lem5756379 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term602 _120557 s t) = (term643 _120557 s t).
Proof. exact (TRANS (@lem5756348 _120557 s t) (@lem5756378 _120557 s t)). Qed.
Lemma lem5756380 {_120557 : Type'} (t : _120557 -> Prop) : (term604 _120557 t) = (term644 _120557 t).
Proof. exact (fun_ext (fun s : _120557 -> Prop => @lem5756379 _120557 s t)). Qed.
Lemma lem5756381 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756382 {_120557 : Type'} (t : _120557 -> Prop) : (term605 _120557 t) = (term645 _120557 t).
Proof. exact (MK_COMB (@lem5756381 _120557) (@lem5756380 _120557 t)). Qed.
Lemma lem5756383 {_120557 : Type'} (t : _120557 -> Prop) : (term584 _120557 t) = (term645 _120557 t).
Proof. exact (TRANS (@lem5756321 _120557 t) (@lem5756382 _120557 t)). Qed.
Lemma lem5756384 {_120557 : Type'} : (term586 _120557) = (term646 _120557).
Proof. exact (fun_ext (fun t : _120557 -> Prop => @lem5756383 _120557 t)). Qed.
Lemma lem5756385 {_120557 : Type'} : (@ex (_120557 -> Prop)) = (@ex (_120557 -> Prop)).
Proof. exact (eq_refl (@ex (_120557 -> Prop))). Qed.
Lemma lem5756386 {_120557 : Type'} : (term587 _120557) = (term647 _120557).
Proof. exact (MK_COMB (@lem5756385 _120557) (@lem5756384 _120557)). Qed.
Lemma lem5756387 {_120557 : Type'} : (term569 _120557) = (term647 _120557).
Proof. exact (TRANS (@lem5756294 _120557) (@lem5756386 _120557)). Qed.
Lemma lem5756388 {_120557 : Type'} : (term422 _120557) = (term647 _120557).
Proof. exact (TRANS (@lem5756267 _120557) (@lem5756387 _120557)). Qed.
Lemma lem5756389 {_120557 : Type'} : (term266 _120557) = (term647 _120557).
Proof. exact (TRANS (@lem5755935 _120557) (@lem5756388 _120557)). Qed.
Lemma lem5756390 {_120557 : Type'} : (term149 _120557) = (term647 _120557).
Proof. exact (TRANS (@lem5754551 _120557) (@lem5756389 _120557)). Qed.
Lemma lem5756391 {_120557 : Type'} (h1 : term149 _120557) : term647 _120557.
Proof. exact (EQ_MP (@lem5756390 _120557) (@lem5754334 _120557 h1)). Qed.
Lemma lem5756392 {_120557 : Type'} (t : _120557 -> Prop) (h1 : term645 _120557 t) : term645 _120557 t.
Proof. exact (h1). Qed.
Lemma lem5756393 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term643 _120557 s t) : term643 _120557 s t.
Proof. exact (h1). Qed.
Lemma lem5756394 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term641 _120557 x s t) : term641 _120557 x s t.
Proof. exact (h1). Qed.
Lemma lem5756395 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term638 _120557 x' x s t) : term638 _120557 x' x s t.
Proof. exact (h1). Qed.
Lemma lem5756408 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : (term216 _120557 s t x) = (term216 _120557 s t x).
Proof. exact (eq_refl (term216 _120557 s t x)). Qed.
Lemma lem5756409 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term225 _120557 s t) = (term225 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756408 _120557 s t x)). Qed.
Lemma lem5756410 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5756411 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term226 _120557 s t) = (term226 _120557 s t).
Proof. exact (MK_COMB (@lem5756410 _120557) (@lem5756409 _120557 s t)). Qed.
Lemma lem5756418 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (term54 _120557 s x) = (term54 _120557 s x).
Proof. exact (eq_refl (term54 _120557 s x)). Qed.
Lemma lem5756419 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term231 _120557 x s t) = (term231 _120557 x s t).
Proof. exact (MK_COMB (@lem5756418 _120557 s x) (@lem5756411 _120557 s t)). Qed.
Lemma lem5756438 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term478 _120557 s x t x') = (term478 _120557 s x t x').
Proof. exact (eq_refl (term478 _120557 s x t x')). Qed.
Lemma lem5756439 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term480 _120557 x' x s t) = (term480 _120557 x' x s t).
Proof. exact (MK_COMB (@lem5756438 _120557 s x t x') (@lem5756419 _120557 x s t)). Qed.
Lemma lem5756454 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term441 _120557 x s t x') = (term441 _120557 x s t x').
Proof. exact (eq_refl (term441 _120557 x s t x')). Qed.
Lemma lem5756477 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) : (term204 _120557 s x t x') = (term204 _120557 s x t x').
Proof. exact (eq_refl (term204 _120557 s x t x')). Qed.
Lemma lem5756478 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term213 _120557 s x t) = (term213 _120557 s x t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756477 _120557 s x t x')). Qed.
Lemma lem5756479 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5756480 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term214 _120557 s x t) = (term214 _120557 s x t).
Proof. exact (MK_COMB (@lem5756479 _120557) (@lem5756478 _120557 s x t)). Qed.
Lemma lem5756481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5756482 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) : (term237 _120557 s x t) = (term237 _120557 s x t).
Proof. exact (MK_COMB (@lem5756481) (@lem5756480 _120557 s x t)). Qed.
Lemma lem5756483 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term456 _120557 x s t x') = (term456 _120557 x s t x').
Proof. exact (MK_COMB (@lem5756482 _120557 s x t) (@lem5756454 _120557 x s t x')). Qed.
Lemma lem5756484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5756485 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term557 _120557 x s t x') = (term557 _120557 x s t x').
Proof. exact (MK_COMB (@lem5756484) (@lem5756483 _120557 x s t x')). Qed.
Lemma lem5756486 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term559 _120557 x' x s t) = (term559 _120557 x' x s t).
Proof. exact (MK_COMB (@lem5756485 _120557 x s t x') (@lem5756439 _120557 x' x s t)). Qed.
Lemma lem5756577 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term636 _120557 x s t x') = (term636 _120557 x s t x').
Proof. exact (eq_refl (term636 _120557 x s t x')). Qed.
Lemma lem5756578 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term638 _120557 x' x s t) = (term638 _120557 x' x s t).
Proof. exact (MK_COMB (@lem5756577 _120557 x s t x') (@lem5756486 _120557 x' x s t)). Qed.
Lemma lem5756579 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term638 _120557 x' x s t) : term638 _120557 x' x s t.
Proof. exact (EQ_MP (@lem5756578 _120557 x' x s t) (@lem5756395 _120557 x' x s t h1)). Qed.
Lemma lem5756580 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term171 _120557 x s t x') : term171 _120557 x s t x'.
Proof. exact (h1). Qed.
Lemma lem5756581 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term559 _120557 x' x s t) : term559 _120557 x' x s t.
Proof. exact (h1). Qed.
Lemma lem5756582 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term167 _120557 x s t x') : term167 _120557 x s t x'.
Proof. exact (h1). Qed.
Lemma lem5756583 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term164 _120557 x s t x') : term164 _120557 x s t x'.
Proof. exact (h1). Qed.
Lemma lem5756584 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term167 _120557 x s t x') : term159 _120557 x s t x'.
Proof. exact (proj2 (@lem5756582 _120557 x s t x' h1)). Qed.
Lemma lem5756585 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term167 _120557 x s t x') : term27 _120557 s x t x'.
Proof. exact (proj1 (@lem5756582 _120557 x s t x' h1)). Qed.
Lemma lem5756586 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term167 _120557 x s t x') : term156 _120557 s t x'.
Proof. exact (proj2 (@lem5756584 _120557 x s t x' h1)). Qed.
Lemma lem5756591 {_120557 : Type'} (x : _120557) (t : _120557 -> Prop) (x' : _120557) (h1 : term26 _120557 x t x') : term26 _120557 x t x'.
Proof. exact (h1). Qed.
Lemma lem5756594 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term164 _120557 x s t x') : term33 _120557 x s t x'.
Proof. exact (proj2 (@lem5756583 _120557 x s t x' h1)). Qed.
Lemma lem5756595 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term164 _120557 x s t x') : term153 _120557 s x t x'.
Proof. exact (proj1 (@lem5756583 _120557 x s t x' h1)). Qed.
Lemma lem5756596 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term164 _120557 x s t x') : term151 _120557 x t x'.
Proof. exact (proj2 (@lem5756595 _120557 x s t x' h1)). Qed.
Lemma lem5756601 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term32 _120557 s t x') : term32 _120557 s t x'.
Proof. exact (h1). Qed.
Lemma lem5756604 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term456 _120557 x s t x'.
Proof. exact (h1). Qed.
Lemma lem5756605 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : term480 _120557 x' x s t.
Proof. exact (h1). Qed.
Lemma lem5756606 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term441 _120557 x s t x'.
Proof. exact (proj2 (@lem5756604 _120557 x s t x' h1)). Qed.
Lemma lem5756607 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term214 _120557 s x t.
Proof. exact (proj1 (@lem5756604 _120557 x s t x' h1)). Qed.
Lemma lem5756609 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term55 _120557 s t x') : term55 _120557 s t x'.
Proof. exact (h1). Qed.
Lemma lem5756612 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : term231 _120557 x s t.
Proof. exact (proj2 (@lem5756605 _120557 x' x s t h1)). Qed.
Lemma lem5756613 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : term44 _120557 s x t x'.
Proof. exact (proj1 (@lem5756605 _120557 x' x s t h1)). Qed.
Lemma lem5756614 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : term226 _120557 s t.
Proof. exact (proj2 (@lem5756612 _120557 x' x s t h1)). Qed.
Lemma lem5756616 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : term26 _120557 x t x'.
Proof. exact (proj2 (@lem5756613 _120557 x' x s t h1)). Qed.
Lemma lem5756635 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem5756651 {_120557 : Type'} (x' : _120557) (x : _120557) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5756667 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem5756683 {_120557 : Type'} (x' : _120557) (x : _120557) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5756699 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem5756715 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem5756733 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term204 _120557 s x t x') = (term648 _120557 x s t x').
Proof. exact (@lem19490 (term649 _120557 x' x) (term53 _120557 s x') (term53 _120557 t x')). Qed.
Lemma lem5756734 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term213 _120557 s x t) = (term650 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756733 _120557 x s t x')). Qed.
Lemma lem5756735 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5756737 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term214 _120557 s x t) = (term651 _120557 x s t).
Proof. exact (MK_COMB (@lem5756735 _120557) (@lem5756734 _120557 x s t)). Qed.
Lemma lem5756738 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term651 _120557 x s t.
Proof. exact (EQ_MP (@lem5756737 _120557 x s t) (@lem5756607 _120557 x s t x' h1)). Qed.
Lemma lem5756742 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem5756760 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) : (term204 _120557 s x t x') = (term648 _120557 x s t x').
Proof. exact (@lem19490 (term649 _120557 x' x) (term53 _120557 s x') (term53 _120557 t x')). Qed.
Lemma lem5756761 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term213 _120557 s x t) = (term650 _120557 x s t).
Proof. exact (fun_ext (fun x' : _120557 => @lem5756760 _120557 x s t x')). Qed.
Lemma lem5756762 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5756764 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term214 _120557 s x t) = (term651 _120557 x s t).
Proof. exact (MK_COMB (@lem5756762 _120557) (@lem5756761 _120557 x s t)). Qed.
Lemma lem5756765 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term651 _120557 x s t.
Proof. exact (EQ_MP (@lem5756764 _120557 x s t) (@lem5756607 _120557 x s t x' h1)). Qed.
Lemma lem5756798 {_120557 : Type'} (x' : _120557) (x : _120557) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5756810 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : (term216 _120557 s t x) = (term216 _120557 s t x).
Proof. exact (eq_refl (term216 _120557 s t x)). Qed.
Lemma lem5756811 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term225 _120557 s t) = (term225 _120557 s t).
Proof. exact (fun_ext (fun x : _120557 => @lem5756810 _120557 s t x)). Qed.
Lemma lem5756812 {_120557 : Type'} : (@all _120557) = (@all _120557).
Proof. exact (eq_refl (@all _120557)). Qed.
Lemma lem5756814 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term226 _120557 s t) = (term226 _120557 s t).
Proof. exact (MK_COMB (@lem5756812 _120557) (@lem5756811 _120557 s t)). Qed.
Lemma lem5756815 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : term226 _120557 s t.
Proof. exact (EQ_MP (@lem5756814 _120557 s t) (@lem5756614 _120557 x' x s t h1)). Qed.
Lemma lem5756823 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem5756824 {_120557 : Type'} (_72515 : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term652 _120557 x s t _72515.
Proof. exact (@lem5756738 _120557 x s t x' h1 _72515). Qed.
Lemma lem5756825 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (_72515 : _120557) : (term652 _120557 x s t _72515) = (term648 _120557 x s t _72515).
Proof. exact (eq_refl (term652 _120557 x s t _72515)). Qed.
Lemma lem5756826 {_120557 : Type'} (_72515 : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term648 _120557 x s t _72515.
Proof. exact (EQ_MP (@lem5756825 _120557 x s t _72515) (@lem5756824 _120557 _72515 x s t x' h1)). Qed.
Lemma lem5756827 {_120557 : Type'} (_72516 : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term652 _120557 x s t _72516.
Proof. exact (@lem5756765 _120557 x s t x' h1 _72516). Qed.
Lemma lem5756828 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (_72516 : _120557) : (term652 _120557 x s t _72516) = (term648 _120557 x s t _72516).
Proof. exact (eq_refl (term652 _120557 x s t _72516)). Qed.
Lemma lem5756829 {_120557 : Type'} (_72516 : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term648 _120557 x s t _72516.
Proof. exact (EQ_MP (@lem5756828 _120557 x s t _72516) (@lem5756827 _120557 _72516 x s t x' h1)). Qed.
Lemma lem5756833 {_120557 : Type'} (_72518 : _120557) (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : term653 _120557 s t _72518.
Proof. exact (@lem5756815 _120557 x' x s t h1 _72518). Qed.
Lemma lem5756834 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (_72518 : _120557) : (term653 _120557 s t _72518) = (term216 _120557 s t _72518).
Proof. exact (eq_refl (term653 _120557 s t _72518)). Qed.
Lemma lem5756843 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term167 _120557 x s t x') : term53 _120557 s x'.
Proof. exact (proj1 (@lem5756586 _120557 x s t x' h1)). Qed.
Lemma lem5756847 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem5756849 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term167 _120557 x s t x') : term649 _120557 x' x.
Proof. exact (proj1 (@lem5756584 _120557 x s t x' h1)). Qed.
Lemma lem5756855 {_120557 : Type'} (x' : _120557) (x : _120557) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5756861 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term167 _120557 x s t x') : term53 _120557 t x'.
Proof. exact (proj2 (@lem5756586 _120557 x s t x' h1)). Qed.
Lemma lem5756863 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem5756867 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term164 _120557 x s t x') : term649 _120557 x' x.
Proof. exact (proj1 (@lem5756596 _120557 x s t x' h1)). Qed.
Lemma lem5756871 {_120557 : Type'} (x' : _120557) (x : _120557) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5756873 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term164 _120557 x s t x') : term53 _120557 s x'.
Proof. exact (proj1 (@lem5756595 _120557 x s t x' h1)). Qed.
Lemma lem5756879 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem5756885 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term164 _120557 x s t x') : term53 _120557 t x'.
Proof. exact (proj2 (@lem5756596 _120557 x s t x' h1)). Qed.
Lemma lem5756887 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem5756889 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem5756895 {_120557 : Type'} (_72515 : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term654 _120557 s _72515 x.
Proof. exact (proj1 (@lem5756826 _120557 _72515 x s t x' h1)). Qed.
Lemma lem5756917 {_120557 : Type'} (_72516 : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term216 _120557 s t _72516.
Proof. exact (proj2 (@lem5756829 _120557 _72516 x s t x' h1)). Qed.
Lemma lem5756927 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : s x'.
Proof. exact (proj1 (@lem5756613 _120557 x' x s t h1)). Qed.
Lemma lem5756929 {_120557 : Type'} (x' : _120557) (x : _120557) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5756937 {_120557 : Type'} (_72518 : _120557) (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : term216 _120557 s t _72518.
Proof. exact (EQ_MP (@lem5756834 _120557 s t _72518) (@lem5756833 _120557 _72518 x' x s t h1)). Qed.
Lemma lem5756941 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem5756956 {_120557 : Type'} (x : _120557) : (term655 _120557 x) = (term655 _120557 x).
Proof. exact (eq_refl (term655 _120557 x)). Qed.
Lemma lem5756957 {_120557 : Type'} (x' : _120557) (x : _120557) (h1 : x' = x) : (term656 _120557 x x') = (term657 _120557 x).
Proof. exact (MK_COMB (@lem5756956 _120557 x) (@lem5756855 _120557 x' x h1)). Qed.
Lemma lem5756958 {_120557 : Type'} (x : _120557) : (term657 _120557 x) = (term658 _120557 x).
Proof. exact (eq_refl (term657 _120557 x)). Qed.
Lemma lem5756959 {_120557 : Type'} (x : _120557) (x' : _120557) : (term659 _120557 x x') = (term659 _120557 x x').
Proof. exact (eq_refl (term659 _120557 x x')). Qed.
Lemma lem5756960 {_120557 : Type'} (x' : _120557) (x : _120557) : ((term656 _120557 x x') = (term657 _120557 x)) = ((term656 _120557 x x') = (term658 _120557 x)).
Proof. exact (MK_COMB (@lem5756959 _120557 x x') (@lem5756958 _120557 x)). Qed.
Lemma lem5756961 {_120557 : Type'} (x' : _120557) (x : _120557) : (term656 _120557 x x') = (term649 _120557 x' x).
Proof. exact (eq_refl (term656 _120557 x x')). Qed.
Lemma lem5756962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5756963 {_120557 : Type'} (x' : _120557) (x : _120557) : (term659 _120557 x x') = (term660 _120557 x' x).
Proof. exact (MK_COMB (@lem5756962) (@lem5756961 _120557 x' x)). Qed.
Lemma lem5756964 {_120557 : Type'} (x : _120557) : (term658 _120557 x) = (term658 _120557 x).
Proof. exact (eq_refl (term658 _120557 x)). Qed.
Lemma lem5756965 {_120557 : Type'} (x' : _120557) (x : _120557) : ((term656 _120557 x x') = (term658 _120557 x)) = ((term649 _120557 x' x) = (term658 _120557 x)).
Proof. exact (MK_COMB (@lem5756963 _120557 x' x) (@lem5756964 _120557 x)). Qed.
Lemma lem5756966 {_120557 : Type'} (x' : _120557) (x : _120557) : ((term656 _120557 x x') = (term657 _120557 x)) = ((term649 _120557 x' x) = (term658 _120557 x)).
Proof. exact (TRANS (@lem5756960 _120557 x' x) (@lem5756965 _120557 x' x)). Qed.
Lemma lem5756967 {_120557 : Type'} (x' : _120557) (x : _120557) (h1 : x' = x) : (term649 _120557 x' x) = (term658 _120557 x).
Proof. exact (EQ_MP (@lem5756966 _120557 x' x) (@lem5756957 _120557 x' x h1)). Qed.
Lemma lem5756968 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term167 _120557 x s t x') (h2 : x' = x) : term658 _120557 x.
Proof. exact (EQ_MP (@lem5756967 _120557 x' x h2) (@lem5756849 _120557 x s t x' h1)). Qed.
Lemma lem5757022 {_120557 : Type'} (x : _120557) : (term655 _120557 x) = (term655 _120557 x).
Proof. exact (eq_refl (term655 _120557 x)). Qed.
Lemma lem5757023 {_120557 : Type'} (x' : _120557) (x : _120557) (h1 : x' = x) : (term656 _120557 x x') = (term657 _120557 x).
Proof. exact (MK_COMB (@lem5757022 _120557 x) (@lem5756871 _120557 x' x h1)). Qed.
Lemma lem5757024 {_120557 : Type'} (x : _120557) : (term657 _120557 x) = (term658 _120557 x).
Proof. exact (eq_refl (term657 _120557 x)). Qed.
Lemma lem5757025 {_120557 : Type'} (x : _120557) (x' : _120557) : (term659 _120557 x x') = (term659 _120557 x x').
Proof. exact (eq_refl (term659 _120557 x x')). Qed.
Lemma lem5757026 {_120557 : Type'} (x' : _120557) (x : _120557) : ((term656 _120557 x x') = (term657 _120557 x)) = ((term656 _120557 x x') = (term658 _120557 x)).
Proof. exact (MK_COMB (@lem5757025 _120557 x x') (@lem5757024 _120557 x)). Qed.
Lemma lem5757027 {_120557 : Type'} (x' : _120557) (x : _120557) : (term656 _120557 x x') = (term649 _120557 x' x).
Proof. exact (eq_refl (term656 _120557 x x')). Qed.
Lemma lem5757028 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5757029 {_120557 : Type'} (x' : _120557) (x : _120557) : (term659 _120557 x x') = (term660 _120557 x' x).
Proof. exact (MK_COMB (@lem5757028) (@lem5757027 _120557 x' x)). Qed.
Lemma lem5757030 {_120557 : Type'} (x : _120557) : (term658 _120557 x) = (term658 _120557 x).
Proof. exact (eq_refl (term658 _120557 x)). Qed.
Lemma lem5757031 {_120557 : Type'} (x' : _120557) (x : _120557) : ((term656 _120557 x x') = (term658 _120557 x)) = ((term649 _120557 x' x) = (term658 _120557 x)).
Proof. exact (MK_COMB (@lem5757029 _120557 x' x) (@lem5757030 _120557 x)). Qed.
Lemma lem5757032 {_120557 : Type'} (x' : _120557) (x : _120557) : ((term656 _120557 x x') = (term657 _120557 x)) = ((term649 _120557 x' x) = (term658 _120557 x)).
Proof. exact (TRANS (@lem5757026 _120557 x' x) (@lem5757031 _120557 x' x)). Qed.
Lemma lem5757033 {_120557 : Type'} (x' : _120557) (x : _120557) (h1 : x' = x) : (term649 _120557 x' x) = (term658 _120557 x).
Proof. exact (EQ_MP (@lem5757032 _120557 x' x) (@lem5757023 _120557 x' x h1)). Qed.
Lemma lem5757034 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term164 _120557 x s t x') (h2 : x' = x) : term658 _120557 x.
Proof. exact (EQ_MP (@lem5757033 _120557 x' x h2) (@lem5756867 _120557 x s t x' h1)). Qed.
Lemma lem5757075 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : term53 _120557 s x.
Proof. exact (proj1 (@lem5756612 _120557 x' x s t h1)). Qed.
Lemma lem5757090 {_120557 : Type'} (s : _120557 -> Prop) : (term661 _120557 s) = (term661 _120557 s).
Proof. exact (eq_refl (term661 _120557 s)). Qed.
Lemma lem5757091 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : x' = x) : (term662 _120557 s x') = (term662 _120557 s x).
Proof. exact (MK_COMB (@lem5757090 _120557 s) (@lem5756929 _120557 x' x h1)). Qed.
Lemma lem5757092 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (term662 _120557 s x) = (s x).
Proof. exact (eq_refl (term662 _120557 s x)). Qed.
Lemma lem5757093 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (term663 _120557 s x') = (term663 _120557 s x').
Proof. exact (eq_refl (term663 _120557 s x')). Qed.
Lemma lem5757094 {_120557 : Type'} (x' : _120557) (s : _120557 -> Prop) (x : _120557) : ((term662 _120557 s x') = (term662 _120557 s x)) = ((term662 _120557 s x') = (s x)).
Proof. exact (MK_COMB (@lem5757093 _120557 s x') (@lem5757092 _120557 s x)). Qed.
Lemma lem5757095 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (term662 _120557 s x') = (s x').
Proof. exact (eq_refl (term662 _120557 s x')). Qed.
Lemma lem5757096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5757097 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (term663 _120557 s x') = (term664 _120557 s x').
Proof. exact (MK_COMB (@lem5757096) (@lem5757095 _120557 s x')). Qed.
Lemma lem5757098 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem5757099 {_120557 : Type'} (x' : _120557) (s : _120557 -> Prop) (x : _120557) : ((term662 _120557 s x') = (s x)) = ((s x') = (s x)).
Proof. exact (MK_COMB (@lem5757097 _120557 s x') (@lem5757098 _120557 s x)). Qed.
Lemma lem5757100 {_120557 : Type'} (x' : _120557) (s : _120557 -> Prop) (x : _120557) : ((term662 _120557 s x') = (term662 _120557 s x)) = ((s x') = (s x)).
Proof. exact (TRANS (@lem5757094 _120557 x' s x) (@lem5757099 _120557 x' s x)). Qed.
Lemma lem5757101 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : x' = x) : (s x') = (s x).
Proof. exact (EQ_MP (@lem5757100 _120557 x' s x) (@lem5757091 _120557 s x' x h1)). Qed.
Lemma lem5757130 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem5757131 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) (h1 : s x') : term665 _120557 s x'.
Proof. exact (fun h0 : term53 _120557 s x' => @lem5757130 _120557 s x' h1). Qed.
Lemma lem5757133 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757134 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (term665 _120557 s x') = (s x').
Proof. exact (@lem5757133 (s x')). Qed.
Lemma lem5757135 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem5757134 _120557 s x') (@lem5757131 _120557 s x' h1)). Qed.
Lemma lem5757138 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5757140 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (term53 _120557 s x') = (term667 _120557 s x').
Proof. exact (@lem5757138 (s x')). Qed.
Lemma lem5757143 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term167 _120557 x s t x') : term667 _120557 s x'.
Proof. exact (EQ_MP (@lem5757140 _120557 s x') (@lem5756843 _120557 x s t x' h1)). Qed.
Lemma lem5757146 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term167 _120557 x s t x') : False.
Proof. exact (@lem5757143 _120557 x s t x' h2 (@lem5757135 _120557 s x' h1)). Qed.
Lemma lem5757147 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term167 _120557 x s t x') : term668.
Proof. exact (fun h0 : ~ False => @lem5757146 _120557 x s t x' h1 h2). Qed.
Lemma lem5757149 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757150 : term668 = False.
Proof. exact (@lem5757149 False). Qed.
Lemma lem5757151 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term167 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757150) (@lem5757147 _120557 x s t x' h1 h2)). Qed.
Lemma lem5757179 {_120557 : Type'} (x : _120557) : x = x.
Proof. exact (@lem21386 _120557 x). Qed.
Lemma lem5757180 {_120557 : Type'} (x : _120557) : x = x.
Proof. exact (@lem5757179 _120557 x). Qed.
Lemma lem5757181 {_120557 : Type'} (x : _120557) : term669 _120557 x.
Proof. exact (fun h0 : term658 _120557 x => @lem5757180 _120557 x). Qed.
Lemma lem5757183 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757184 {_120557 : Type'} (x : _120557) : (term669 _120557 x) = (x = x).
Proof. exact (@lem5757183 (x = x)). Qed.
Lemma lem5757185 {_120557 : Type'} (x : _120557) : x = x.
Proof. exact (EQ_MP (@lem5757184 _120557 x) (@lem5757181 _120557 x)). Qed.
Lemma lem5757188 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5757190 {_120557 : Type'} (x : _120557) : (term658 _120557 x) = (term670 _120557 x).
Proof. exact (@lem5757188 (x = x)). Qed.
Lemma lem5757193 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term167 _120557 x s t x') (h2 : x' = x) : term670 _120557 x.
Proof. exact (EQ_MP (@lem5757190 _120557 x) (@lem5756968 _120557 s t x' x h1 h2)). Qed.
Lemma lem5757196 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term167 _120557 x s t x') (h2 : x' = x) : False.
Proof. exact (@lem5757193 _120557 s t x' x h1 h2 (@lem5757185 _120557 x)). Qed.
Lemma lem5757197 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term167 _120557 x s t x') (h2 : x' = x) : term668.
Proof. exact (fun h0 : ~ False => @lem5757196 _120557 s t x' x h1 h2). Qed.
Lemma lem5757199 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757200 : term668 = False.
Proof. exact (@lem5757199 False). Qed.
Lemma lem5757229 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem5757230 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) (h1 : t x') : term665 _120557 t x'.
Proof. exact (fun h0 : term53 _120557 t x' => @lem5757229 _120557 t x' h1). Qed.
Lemma lem5757232 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757233 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) : (term665 _120557 t x') = (t x').
Proof. exact (@lem5757232 (t x')). Qed.
Lemma lem5757234 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem5757233 _120557 t x') (@lem5757230 _120557 t x' h1)). Qed.
Lemma lem5757237 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5757239 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) : (term53 _120557 t x') = (term667 _120557 t x').
Proof. exact (@lem5757237 (t x')). Qed.
Lemma lem5757242 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term167 _120557 x s t x') : term667 _120557 t x'.
Proof. exact (EQ_MP (@lem5757239 _120557 t x') (@lem5756861 _120557 x s t x' h1)). Qed.
Lemma lem5757245 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term167 _120557 x s t x') : False.
Proof. exact (@lem5757242 _120557 x s t x' h2 (@lem5757234 _120557 t x' h1)). Qed.
Lemma lem5757246 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term167 _120557 x s t x') : term668.
Proof. exact (fun h0 : ~ False => @lem5757245 _120557 x s t x' h1 h2). Qed.
Lemma lem5757248 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757249 : term668 = False.
Proof. exact (@lem5757248 False). Qed.
Lemma lem5757250 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term167 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757249) (@lem5757246 _120557 x s t x' h1 h2)). Qed.
Lemma lem5757278 {_120557 : Type'} (x : _120557) : x = x.
Proof. exact (@lem21386 _120557 x). Qed.
Lemma lem5757279 {_120557 : Type'} (x : _120557) : x = x.
Proof. exact (@lem5757278 _120557 x). Qed.
Lemma lem5757280 {_120557 : Type'} (x : _120557) : term669 _120557 x.
Proof. exact (fun h0 : term658 _120557 x => @lem5757279 _120557 x). Qed.
Lemma lem5757282 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757283 {_120557 : Type'} (x : _120557) : (term669 _120557 x) = (x = x).
Proof. exact (@lem5757282 (x = x)). Qed.
Lemma lem5757284 {_120557 : Type'} (x : _120557) : x = x.
Proof. exact (EQ_MP (@lem5757283 _120557 x) (@lem5757280 _120557 x)). Qed.
Lemma lem5757287 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5757289 {_120557 : Type'} (x : _120557) : (term658 _120557 x) = (term670 _120557 x).
Proof. exact (@lem5757287 (x = x)). Qed.
Lemma lem5757292 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term164 _120557 x s t x') (h2 : x' = x) : term670 _120557 x.
Proof. exact (EQ_MP (@lem5757289 _120557 x) (@lem5757034 _120557 s t x' x h1 h2)). Qed.
Lemma lem5757295 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term164 _120557 x s t x') (h2 : x' = x) : False.
Proof. exact (@lem5757292 _120557 s t x' x h1 h2 (@lem5757284 _120557 x)). Qed.
Lemma lem5757296 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term164 _120557 x s t x') (h2 : x' = x) : term668.
Proof. exact (fun h0 : ~ False => @lem5757295 _120557 s t x' x h1 h2). Qed.
Lemma lem5757298 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757299 : term668 = False.
Proof. exact (@lem5757298 False). Qed.
Lemma lem5757328 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem5757329 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) (h1 : s x') : term665 _120557 s x'.
Proof. exact (fun h0 : term53 _120557 s x' => @lem5757328 _120557 s x' h1). Qed.
Lemma lem5757331 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757332 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (term665 _120557 s x') = (s x').
Proof. exact (@lem5757331 (s x')). Qed.
Lemma lem5757333 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem5757332 _120557 s x') (@lem5757329 _120557 s x' h1)). Qed.
Lemma lem5757336 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5757338 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (term53 _120557 s x') = (term667 _120557 s x').
Proof. exact (@lem5757336 (s x')). Qed.
Lemma lem5757341 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term164 _120557 x s t x') : term667 _120557 s x'.
Proof. exact (EQ_MP (@lem5757338 _120557 s x') (@lem5756873 _120557 x s t x' h1)). Qed.
Lemma lem5757344 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term164 _120557 x s t x') : False.
Proof. exact (@lem5757341 _120557 x s t x' h2 (@lem5757333 _120557 s x' h1)). Qed.
Lemma lem5757345 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term164 _120557 x s t x') : term668.
Proof. exact (fun h0 : ~ False => @lem5757344 _120557 x s t x' h1 h2). Qed.
Lemma lem5757347 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757348 : term668 = False.
Proof. exact (@lem5757347 False). Qed.
Lemma lem5757349 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term164 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757348) (@lem5757345 _120557 x s t x' h1 h2)). Qed.
Lemma lem5757377 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem5757378 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) (h1 : t x') : term665 _120557 t x'.
Proof. exact (fun h0 : term53 _120557 t x' => @lem5757377 _120557 t x' h1). Qed.
Lemma lem5757380 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757381 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) : (term665 _120557 t x') = (t x').
Proof. exact (@lem5757380 (t x')). Qed.
Lemma lem5757382 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem5757381 _120557 t x') (@lem5757378 _120557 t x' h1)). Qed.
Lemma lem5757385 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5757387 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) : (term53 _120557 t x') = (term667 _120557 t x').
Proof. exact (@lem5757385 (t x')). Qed.
Lemma lem5757390 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term164 _120557 x s t x') : term667 _120557 t x'.
Proof. exact (EQ_MP (@lem5757387 _120557 t x') (@lem5756885 _120557 x s t x' h1)). Qed.
Lemma lem5757393 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term164 _120557 x s t x') : False.
Proof. exact (@lem5757390 _120557 x s t x' h2 (@lem5757382 _120557 t x' h1)). Qed.
Lemma lem5757394 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term164 _120557 x s t x') : term668.
Proof. exact (fun h0 : ~ False => @lem5757393 _120557 x s t x' h1 h2). Qed.
Lemma lem5757396 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757397 : term668 = False.
Proof. exact (@lem5757396 False). Qed.
Lemma lem5757398 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term164 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757397) (@lem5757394 _120557 x s t x' h1 h2)). Qed.
Lemma lem5757426 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem5757427 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (h1 : s x) : term665 _120557 s x.
Proof. exact (fun h0 : term53 _120557 s x => @lem5757426 _120557 s x h1). Qed.
Lemma lem5757429 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757430 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (term665 _120557 s x) = (s x).
Proof. exact (@lem5757429 (s x)). Qed.
Lemma lem5757431 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem5757430 _120557 s x) (@lem5757427 _120557 s x h1)). Qed.
Lemma lem5757433 {_120557 : Type'} (x : _120557) : x = x.
Proof. exact (@lem21386 _120557 x). Qed.
Lemma lem5757434 {_120557 : Type'} (x : _120557) : x = x.
Proof. exact (@lem5757433 _120557 x). Qed.
Lemma lem5757435 {_120557 : Type'} (x : _120557) : term669 _120557 x.
Proof. exact (fun h0 : term658 _120557 x => @lem5757434 _120557 x). Qed.
Lemma lem5757437 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757438 {_120557 : Type'} (x : _120557) : (term669 _120557 x) = (x = x).
Proof. exact (@lem5757437 (x = x)). Qed.
Lemma lem5757439 {_120557 : Type'} (x : _120557) : x = x.
Proof. exact (EQ_MP (@lem5757438 _120557 x) (@lem5757435 _120557 x)). Qed.
Lemma lem5757441 (a : Prop) (b : Prop) : (term671 a b) = (term672 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5757442 {_120557 : Type'} (s : _120557 -> Prop) (_72515 : _120557) (x : _120557) : (term654 _120557 s _72515 x) = (term673 _120557 s _72515 x).
Proof. exact (@lem5757441 (s _72515) (_72515 = x)). Qed.
Lemma lem5757444 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5757445 {_120557 : Type'} (s : _120557 -> Prop) (_72515 : _120557) (x : _120557) : (term673 _120557 s _72515 x) = (term674 _120557 s _72515 x).
Proof. exact (@lem5757444 (term675 _120557 s _72515 x)). Qed.
Lemma lem5757446 {_120557 : Type'} (s : _120557 -> Prop) (_72515 : _120557) (x : _120557) : (term654 _120557 s _72515 x) = (term674 _120557 s _72515 x).
Proof. exact (TRANS (@lem5757442 _120557 s _72515 x) (@lem5757445 _120557 s _72515 x)). Qed.
Lemma lem5757448 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (h1 : s x) : term676 _120557 s x.
Proof. exact (conj (@lem5757431 _120557 s x h1) (@lem5757439 _120557 x)). Qed.
Lemma lem5757450 {_120557 : Type'} (_72515 : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term674 _120557 s _72515 x.
Proof. exact (EQ_MP (@lem5757446 _120557 s _72515 x) (@lem5756895 _120557 _72515 x s t x' h1)). Qed.
Lemma lem5757451 {_120557 : Type'} (_72515 : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term674 _120557 s _72515 x.
Proof. exact (@lem5757450 _120557 _72515 x s t x' h1). Qed.
Lemma lem5757452 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term677 _120557 s x.
Proof. exact (@lem5757451 _120557 x x s t x' h1). Qed.
Lemma lem5757455 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x) (h2 : term456 _120557 x s t x') : False.
Proof. exact (@lem5757452 _120557 x s t x' h2 (@lem5757448 _120557 s x h1)). Qed.
Lemma lem5757456 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x) (h2 : term456 _120557 x s t x') : term668.
Proof. exact (fun h0 : ~ False => @lem5757455 _120557 x s t x' h1 h2). Qed.
Lemma lem5757458 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757459 : term668 = False.
Proof. exact (@lem5757458 False). Qed.
Lemma lem5757460 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x) (h2 : term456 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757459) (@lem5757456 _120557 x s t x' h1 h2)). Qed.
Lemma lem5757488 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term55 _120557 s t x') : s x'.
Proof. exact (proj1 (@lem5756609 _120557 s t x' h1)). Qed.
Lemma lem5757489 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term55 _120557 s t x') : term665 _120557 s x'.
Proof. exact (fun h0 : term53 _120557 s x' => @lem5757488 _120557 s t x' h1). Qed.
Lemma lem5757491 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757492 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (term665 _120557 s x') = (s x').
Proof. exact (@lem5757491 (s x')). Qed.
Lemma lem5757493 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term55 _120557 s t x') : s x'.
Proof. exact (EQ_MP (@lem5757492 _120557 s x') (@lem5757489 _120557 s t x' h1)). Qed.
Lemma lem5757495 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term55 _120557 s t x') : t x'.
Proof. exact (proj2 (@lem5756609 _120557 s t x' h1)). Qed.
Lemma lem5757496 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term55 _120557 s t x') : term665 _120557 t x'.
Proof. exact (fun h0 : term53 _120557 t x' => @lem5757495 _120557 s t x' h1). Qed.
Lemma lem5757498 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757499 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) : (term665 _120557 t x') = (t x').
Proof. exact (@lem5757498 (t x')). Qed.
Lemma lem5757500 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term55 _120557 s t x') : t x'.
Proof. exact (EQ_MP (@lem5757499 _120557 t x') (@lem5757496 _120557 s t x' h1)). Qed.
Lemma lem5757502 (a : Prop) (b : Prop) : (term671 a b) = (term672 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5757503 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (_72516 : _120557) : (term216 _120557 s t _72516) = (term58 _120557 s t _72516).
Proof. exact (@lem5757502 (s _72516) (t _72516)). Qed.
Lemma lem5757505 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5757506 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (_72516 : _120557) : (term58 _120557 s t _72516) = (term678 _120557 s t _72516).
Proof. exact (@lem5757505 (term55 _120557 s t _72516)). Qed.
Lemma lem5757507 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (_72516 : _120557) : (term216 _120557 s t _72516) = (term678 _120557 s t _72516).
Proof. exact (TRANS (@lem5757503 _120557 s t _72516) (@lem5757506 _120557 s t _72516)). Qed.
Lemma lem5757509 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term55 _120557 s t x') : term55 _120557 s t x'.
Proof. exact (conj (@lem5757493 _120557 s t x' h1) (@lem5757500 _120557 s t x' h1)). Qed.
Lemma lem5757511 {_120557 : Type'} (_72516 : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term678 _120557 s t _72516.
Proof. exact (EQ_MP (@lem5757507 _120557 s t _72516) (@lem5756917 _120557 _72516 x s t x' h1)). Qed.
Lemma lem5757512 {_120557 : Type'} (_72516 : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term678 _120557 s t _72516.
Proof. exact (@lem5757511 _120557 _72516 x s t x' h1). Qed.
Lemma lem5757513 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : term678 _120557 s t x'.
Proof. exact (@lem5757512 _120557 x' x s t x' h1). Qed.
Lemma lem5757516 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') (h2 : term55 _120557 s t x') : False.
Proof. exact (@lem5757513 _120557 x s t x' h1 (@lem5757509 _120557 s t x' h2)). Qed.
Lemma lem5757517 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') (h2 : term55 _120557 s t x') : term668.
Proof. exact (fun h0 : ~ False => @lem5757516 _120557 x s t x' h1 h2). Qed.
Lemma lem5757519 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757520 : term668 = False.
Proof. exact (@lem5757519 False). Qed.
Lemma lem5757521 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') (h2 : term55 _120557 s t x') : False.
Proof. exact (EQ_MP (@lem5757520) (@lem5757517 _120557 x s t x' h1 h2)). Qed.
Lemma lem5757523 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term480 _120557 x' x s t) (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem5757101 _120557 s x' x h2) (@lem5756927 _120557 x' x s t h1)). Qed.
Lemma lem5757524 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term480 _120557 x' x s t) (h2 : x' = x) : term665 _120557 s x.
Proof. exact (fun h0 : term53 _120557 s x => @lem5757523 _120557 s t x' x h1 h2). Qed.
Lemma lem5757526 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757527 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (term665 _120557 s x) = (s x).
Proof. exact (@lem5757526 (s x)). Qed.
Lemma lem5757528 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term480 _120557 x' x s t) (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem5757527 _120557 s x) (@lem5757524 _120557 s t x' x h1 h2)). Qed.
Lemma lem5757531 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5757533 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) : (term53 _120557 s x) = (term667 _120557 s x).
Proof. exact (@lem5757531 (s x)). Qed.
Lemma lem5757536 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : term667 _120557 s x.
Proof. exact (EQ_MP (@lem5757533 _120557 s x) (@lem5757075 _120557 x' x s t h1)). Qed.
Lemma lem5757539 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term480 _120557 x' x s t) (h2 : x' = x) : False.
Proof. exact (@lem5757536 _120557 x' x s t h1 (@lem5757528 _120557 s t x' x h1 h2)). Qed.
Lemma lem5757540 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term480 _120557 x' x s t) (h2 : x' = x) : term668.
Proof. exact (fun h0 : ~ False => @lem5757539 _120557 s t x' x h1 h2). Qed.
Lemma lem5757542 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757543 : term668 = False.
Proof. exact (@lem5757542 False). Qed.
Lemma lem5757546 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : s x'.
Proof. exact (proj1 (@lem5756613 _120557 x' x s t h1)). Qed.
Lemma lem5757547 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : term665 _120557 s x'.
Proof. exact (fun h0 : term53 _120557 s x' => @lem5757546 _120557 x' x s t h1). Qed.
Lemma lem5757549 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757550 {_120557 : Type'} (s : _120557 -> Prop) (x' : _120557) : (term665 _120557 s x') = (s x').
Proof. exact (@lem5757549 (s x')). Qed.
Lemma lem5757551 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : s x'.
Proof. exact (EQ_MP (@lem5757550 _120557 s x') (@lem5757547 _120557 x' x s t h1)). Qed.
Lemma lem5757553 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem5757554 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) (h1 : t x') : term665 _120557 t x'.
Proof. exact (fun h0 : term53 _120557 t x' => @lem5757553 _120557 t x' h1). Qed.
Lemma lem5757556 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757557 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) : (term665 _120557 t x') = (t x').
Proof. exact (@lem5757556 (t x')). Qed.
Lemma lem5757558 {_120557 : Type'} (t : _120557 -> Prop) (x' : _120557) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem5757557 _120557 t x') (@lem5757554 _120557 t x' h1)). Qed.
Lemma lem5757560 (a : Prop) (b : Prop) : (term671 a b) = (term672 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5757561 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (_72518 : _120557) : (term216 _120557 s t _72518) = (term58 _120557 s t _72518).
Proof. exact (@lem5757560 (s _72518) (t _72518)). Qed.
Lemma lem5757563 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5757564 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (_72518 : _120557) : (term58 _120557 s t _72518) = (term678 _120557 s t _72518).
Proof. exact (@lem5757563 (term55 _120557 s t _72518)). Qed.
Lemma lem5757565 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (_72518 : _120557) : (term216 _120557 s t _72518) = (term678 _120557 s t _72518).
Proof. exact (TRANS (@lem5757561 _120557 s t _72518) (@lem5757564 _120557 s t _72518)). Qed.
Lemma lem5757567 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : t x') (h2 : term480 _120557 x' x s t) : term55 _120557 s t x'.
Proof. exact (conj (@lem5757551 _120557 x' x s t h2) (@lem5757558 _120557 t x' h1)). Qed.
Lemma lem5757569 {_120557 : Type'} (_72518 : _120557) (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : term678 _120557 s t _72518.
Proof. exact (EQ_MP (@lem5757565 _120557 s t _72518) (@lem5756937 _120557 _72518 x' x s t h1)). Qed.
Lemma lem5757570 {_120557 : Type'} (_72518 : _120557) (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : term678 _120557 s t _72518.
Proof. exact (@lem5757569 _120557 _72518 x' x s t h1). Qed.
Lemma lem5757571 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : term678 _120557 s t x'.
Proof. exact (@lem5757570 _120557 x' x' x s t h1). Qed.
Lemma lem5757574 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : t x') (h2 : term480 _120557 x' x s t) : False.
Proof. exact (@lem5757571 _120557 x' x s t h2 (@lem5757567 _120557 x' x s t h1 h2)). Qed.
Lemma lem5757575 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : t x') (h2 : term480 _120557 x' x s t) : term668.
Proof. exact (fun h0 : ~ False => @lem5757574 _120557 x' x s t h1 h2). Qed.
Lemma lem5757577 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5757578 : term668 = False.
Proof. exact (@lem5757577 False). Qed.
Lemma lem5757579 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : t x') (h2 : term480 _120557 x' x s t) : False.
Proof. exact (EQ_MP (@lem5757578) (@lem5757575 _120557 x' x s t h1 h2)). Qed.
Lemma lem5757580 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term480 _120557 x' x s t) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5757543) (@lem5757540 _120557 s t x' x h1 h2)). Qed.
Lemma lem5757581 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term164 _120557 x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5757299) (@lem5757296 _120557 s t x' x h1 h2)). Qed.
Lemma lem5757582 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term167 _120557 x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5757200) (@lem5757197 _120557 s t x' x h1 h2)). Qed.
Lemma lem5757583 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : t x') (h2 : term480 _120557 x' x s t) : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem5757579 _120557 x' x s t h1 h2) (fun h3 : False => @lem5756941 _120557 t x' h1)). Qed.
Lemma lem5757584 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : t x') (h2 : term480 _120557 x' x s t) : False.
Proof. exact (EQ_MP (@lem5757583 _120557 x' x s t h1 h2) (@lem5756941 _120557 t x' h1)). Qed.
Lemma lem5757585 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term480 _120557 x' x s t) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5757580 _120557 s t x' x h1 h2) (fun h3 : False => @lem5756929 _120557 x' x h2)). Qed.
Lemma lem5757586 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term480 _120557 x' x s t) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5757585 _120557 s t x' x h1 h2) (@lem5756929 _120557 x' x h2)). Qed.
Lemma lem5757587 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x) (h2 : term456 _120557 x s t x') : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem5757460 _120557 x s t x' h1 h2) (fun h3 : False => @lem5756889 _120557 s x h1)). Qed.
Lemma lem5757588 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x) (h2 : term456 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757587 _120557 x s t x' h1 h2) (@lem5756889 _120557 s x h1)). Qed.
Lemma lem5757589 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term164 _120557 x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem5757398 _120557 x s t x' h1 h2) (fun h3 : False => @lem5756887 _120557 t x' h1)). Qed.
Lemma lem5757590 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term164 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757589 _120557 x s t x' h1 h2) (@lem5756887 _120557 t x' h1)). Qed.
Lemma lem5757591 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term164 _120557 x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem5757349 _120557 x s t x' h1 h2) (fun h3 : False => @lem5756879 _120557 s x' h1)). Qed.
Lemma lem5757592 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term164 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757591 _120557 x s t x' h1 h2) (@lem5756879 _120557 s x' h1)). Qed.
Lemma lem5757593 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term164 _120557 x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5757581 _120557 s t x' x h1 h2) (fun h3 : False => @lem5756871 _120557 x' x h2)). Qed.
Lemma lem5757594 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term164 _120557 x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5757593 _120557 s t x' x h1 h2) (@lem5756871 _120557 x' x h2)). Qed.
Lemma lem5757595 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term167 _120557 x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem5757250 _120557 x s t x' h1 h2) (fun h3 : False => @lem5756863 _120557 t x' h1)). Qed.
Lemma lem5757596 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term167 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757595 _120557 x s t x' h1 h2) (@lem5756863 _120557 t x' h1)). Qed.
Lemma lem5757597 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term167 _120557 x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5757582 _120557 s t x' x h1 h2) (fun h3 : False => @lem5756855 _120557 x' x h2)). Qed.
Lemma lem5757598 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term167 _120557 x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5757597 _120557 s t x' x h1 h2) (@lem5756855 _120557 x' x h2)). Qed.
Lemma lem5757599 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term167 _120557 x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem5757151 _120557 x s t x' h1 h2) (fun h3 : False => @lem5756847 _120557 s x' h1)). Qed.
Lemma lem5757600 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term167 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757599 _120557 x s t x' h1 h2) (@lem5756847 _120557 s x' h1)). Qed.
Lemma lem5757601 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : t x') (h2 : term480 _120557 x' x s t) : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem5757584 _120557 x' x s t h1 h2) (fun h3 : False => @lem5756823 _120557 t x' h1)). Qed.
Lemma lem5757602 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : t x') (h2 : term480 _120557 x' x s t) : False.
Proof. exact (EQ_MP (@lem5757601 _120557 x' x s t h1 h2) (@lem5756823 _120557 t x' h1)). Qed.
Lemma lem5757603 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term480 _120557 x' x s t) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5757586 _120557 s t x' x h1 h2) (fun h3 : False => @lem5756798 _120557 x' x h2)). Qed.
Lemma lem5757604 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term480 _120557 x' x s t) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5757603 _120557 s t x' x h1 h2) (@lem5756798 _120557 x' x h2)). Qed.
Lemma lem5757605 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x) (h2 : term456 _120557 x s t x') : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem5757588 _120557 x s t x' h1 h2) (fun h3 : False => @lem5756742 _120557 s x h1)). Qed.
Lemma lem5757606 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x) (h2 : term456 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757605 _120557 x s t x' h1 h2) (@lem5756742 _120557 s x h1)). Qed.
Lemma lem5757607 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term164 _120557 x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem5757590 _120557 x s t x' h1 h2) (fun h3 : False => @lem5756715 _120557 t x' h1)). Qed.
Lemma lem5757608 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term164 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757607 _120557 x s t x' h1 h2) (@lem5756715 _120557 t x' h1)). Qed.
Lemma lem5757609 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term164 _120557 x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem5757592 _120557 x s t x' h1 h2) (fun h3 : False => @lem5756699 _120557 s x' h1)). Qed.
Lemma lem5757610 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term164 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757609 _120557 x s t x' h1 h2) (@lem5756699 _120557 s x' h1)). Qed.
Lemma lem5757611 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term164 _120557 x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5757594 _120557 s t x' x h1 h2) (fun h3 : False => @lem5756683 _120557 x' x h2)). Qed.
Lemma lem5757612 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term164 _120557 x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5757611 _120557 s t x' x h1 h2) (@lem5756683 _120557 x' x h2)). Qed.
Lemma lem5757613 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term167 _120557 x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem5757596 _120557 x s t x' h1 h2) (fun h3 : False => @lem5756667 _120557 t x' h1)). Qed.
Lemma lem5757614 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term167 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757613 _120557 x s t x' h1 h2) (@lem5756667 _120557 t x' h1)). Qed.
Lemma lem5757615 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term167 _120557 x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5757598 _120557 s t x' x h1 h2) (fun h3 : False => @lem5756651 _120557 x' x h2)). Qed.
Lemma lem5757616 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term167 _120557 x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5757615 _120557 s t x' x h1 h2) (@lem5756651 _120557 x' x h2)). Qed.
Lemma lem5757617 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term167 _120557 x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem5757600 _120557 x s t x' h1 h2) (fun h3 : False => @lem5756635 _120557 s x' h1)). Qed.
Lemma lem5757618 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term167 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757617 _120557 x s t x' h1 h2) (@lem5756635 _120557 s x' h1)). Qed.
Lemma lem5757619 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : t x') (h2 : term480 _120557 x' x s t) : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem5757602 _120557 x' x s t h1 h2) (fun h3 : False => @lem5756823 _120557 t x' h1)). Qed.
Lemma lem5757620 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : t x') (h2 : term480 _120557 x' x s t) : False.
Proof. exact (EQ_MP (@lem5757619 _120557 x' x s t h1 h2) (@lem5756823 _120557 t x' h1)). Qed.
Lemma lem5757621 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term480 _120557 x' x s t) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5757604 _120557 s t x' x h1 h2) (fun h3 : False => @lem5756798 _120557 x' x h2)). Qed.
Lemma lem5757622 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term480 _120557 x' x s t) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5757621 _120557 s t x' x h1 h2) (@lem5756798 _120557 x' x h2)). Qed.
Lemma lem5757623 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x) (h2 : term456 _120557 x s t x') : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem5757606 _120557 x s t x' h1 h2) (fun h3 : False => @lem5756742 _120557 s x h1)). Qed.
Lemma lem5757624 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x) (h2 : term456 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757623 _120557 x s t x' h1 h2) (@lem5756742 _120557 s x h1)). Qed.
Lemma lem5757625 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term164 _120557 x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem5757608 _120557 x s t x' h1 h2) (fun h3 : False => @lem5756715 _120557 t x' h1)). Qed.
Lemma lem5757626 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term164 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757625 _120557 x s t x' h1 h2) (@lem5756715 _120557 t x' h1)). Qed.
Lemma lem5757627 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term164 _120557 x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem5757610 _120557 x s t x' h1 h2) (fun h3 : False => @lem5756699 _120557 s x' h1)). Qed.
Lemma lem5757628 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term164 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757627 _120557 x s t x' h1 h2) (@lem5756699 _120557 s x' h1)). Qed.
Lemma lem5757629 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term164 _120557 x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5757612 _120557 s t x' x h1 h2) (fun h3 : False => @lem5756683 _120557 x' x h2)). Qed.
Lemma lem5757630 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term164 _120557 x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5757629 _120557 s t x' x h1 h2) (@lem5756683 _120557 x' x h2)). Qed.
Lemma lem5757631 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term167 _120557 x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem5757614 _120557 x s t x' h1 h2) (fun h3 : False => @lem5756667 _120557 t x' h1)). Qed.
Lemma lem5757632 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : t x') (h2 : term167 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757631 _120557 x s t x' h1 h2) (@lem5756667 _120557 t x' h1)). Qed.
Lemma lem5757633 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term167 _120557 x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem5757616 _120557 s t x' x h1 h2) (fun h3 : False => @lem5756651 _120557 x' x h2)). Qed.
Lemma lem5757634 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (x : _120557) (h1 : term167 _120557 x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem5757633 _120557 s t x' x h1 h2) (@lem5756651 _120557 x' x h2)). Qed.
Lemma lem5757635 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term167 _120557 x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem5757618 _120557 x s t x' h1 h2) (fun h3 : False => @lem5756635 _120557 s x' h1)). Qed.
Lemma lem5757636 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : s x') (h2 : term167 _120557 x s t x') : False.
Proof. exact (EQ_MP (@lem5757635 _120557 x s t x' h1 h2) (@lem5756635 _120557 s x' h1)). Qed.
Lemma lem5757637 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term480 _120557 x' x s t) : False.
Proof. exact (or_elim (@lem5756616 _120557 x' x s t h1) (fun h0 : x' = x => @lem5757622 _120557 s t x' x h1 h0) (fun h0 : t x' => @lem5757620 _120557 x' x s t h0 h1)). Qed.
Lemma lem5757638 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term456 _120557 x s t x') : False.
Proof. exact (or_elim (@lem5756606 _120557 x s t x' h1) (fun h0 : s x => @lem5757624 _120557 x s t x' h0 h1) (fun h0 : term55 _120557 s t x' => @lem5757521 _120557 x s t x' h1 h0)). Qed.
Lemma lem5757639 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term559 _120557 x' x s t) : False.
Proof. exact (or_elim (@lem5756581 _120557 x' x s t h1) (fun h0 : term456 _120557 x s t x' => @lem5757638 _120557 x s t x' h0) (fun h0 : term480 _120557 x' x s t => @lem5757637 _120557 x' x s t h0)). Qed.
Lemma lem5757640 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term164 _120557 x s t x') (h2 : term32 _120557 s t x') : False.
Proof. exact (or_elim (@lem5756601 _120557 s t x' h2) (fun h0 : s x' => @lem5757628 _120557 x s t x' h0 h1) (fun h0 : t x' => @lem5757626 _120557 x s t x' h0 h1)). Qed.
Lemma lem5757641 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term164 _120557 x s t x') : False.
Proof. exact (or_elim (@lem5756594 _120557 x s t x' h1) (fun h0 : x' = x => @lem5757630 _120557 s t x' x h1 h0) (fun h0 : term32 _120557 s t x' => @lem5757640 _120557 x s t x' h1 h0)). Qed.
Lemma lem5757642 {_120557 : Type'} (s : _120557 -> Prop) (x : _120557) (t : _120557 -> Prop) (x' : _120557) (h1 : term167 _120557 x s t x') (h2 : term26 _120557 x t x') : False.
Proof. exact (or_elim (@lem5756591 _120557 x t x' h2) (fun h0 : x' = x => @lem5757634 _120557 s t x' x h1 h0) (fun h0 : t x' => @lem5757632 _120557 x s t x' h0 h1)). Qed.
Lemma lem5757643 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term167 _120557 x s t x') : False.
Proof. exact (or_elim (@lem5756585 _120557 x s t x' h1) (fun h0 : s x' => @lem5757636 _120557 x s t x' h0 h1) (fun h0 : term26 _120557 x t x' => @lem5757642 _120557 s x t x' h1 h0)). Qed.
Lemma lem5757644 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (x' : _120557) (h1 : term171 _120557 x s t x') : False.
Proof. exact (or_elim (@lem5756580 _120557 x s t x' h1) (fun h0 : term167 _120557 x s t x' => @lem5757643 _120557 x s t x' h0) (fun h0 : term164 _120557 x s t x' => @lem5757641 _120557 x s t x' h0)). Qed.
Lemma lem5757645 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term638 _120557 x' x s t) : False.
Proof. exact (or_elim (@lem5756579 _120557 x' x s t h1) (fun h0 : term171 _120557 x s t x' => @lem5757644 _120557 x s t x' h0) (fun h0 : term559 _120557 x' x s t => @lem5757639 _120557 x' x s t h0)). Qed.
Lemma lem5757646 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term638 _120557 x' x s t) : (term638 _120557 x' x s t) = False.
Proof. exact (prop_ext (fun h2 : term638 _120557 x' x s t => @lem5757645 _120557 x' x s t h1) (fun h2 : False => @lem5756579 _120557 x' x s t h1)). Qed.
Lemma lem5757647 {_120557 : Type'} (x' : _120557) (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term638 _120557 x' x s t) : False.
Proof. exact (EQ_MP (@lem5757646 _120557 x' x s t h1) (@lem5756579 _120557 x' x s t h1)). Qed.
Lemma lem5757648 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term641 _120557 x s t) : False.
Proof. exact (ex_elim (@lem5756394 _120557 x s t h1) (fun x' : _120557 => fun h0 : term640 _120557 x s t x' => @lem5757647 _120557 x' x s t h0)). Qed.
Lemma lem5757649 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term643 _120557 s t) : False.
Proof. exact (ex_elim (@lem5756393 _120557 s t h1) (fun x : _120557 => fun h0 : term642 _120557 s t x => @lem5757648 _120557 x s t h0)). Qed.
Lemma lem5757650 {_120557 : Type'} (t : _120557 -> Prop) (h1 : term645 _120557 t) : False.
Proof. exact (ex_elim (@lem5756392 _120557 t h1) (fun s : _120557 -> Prop => fun h0 : term644 _120557 t s => @lem5757649 _120557 s t h0)). Qed.
Lemma lem5757651 {_120557 : Type'} (h1 : term149 _120557) : False.
Proof. exact (ex_elim (@lem5756391 _120557 h1) (fun t : _120557 -> Prop => fun h0 : term646 _120557 t => @lem5757650 _120557 t h0)). Qed.
Lemma lem5757652 {_120557 : Type'} (h1 : term149 _120557) : (term149 _120557) = False.
Proof. exact (prop_ext (fun h2 : term149 _120557 => @lem5757651 _120557 h1) (fun h2 : False => @lem5754334 _120557 h1)). Qed.
Lemma lem5757653 {_120557 : Type'} (h1 : term149 _120557) : False.
Proof. exact (EQ_MP (@lem5757652 _120557 h1) (@lem5754334 _120557 h1)). Qed.
Lemma lem5757654 {_120557 : Type'} : term148 _120557.
Proof. exact (fun h0 : term149 _120557 => @lem5757653 _120557 h0). Qed.
Lemma lem5757655 {_120557 : Type'} : term147 _120557.
Proof. exact (EQ_MP (@lem5754333 _120557) (@lem5757654 _120557)). Qed.
Lemma lem5757656 {_120557 : Type'} : term126 _120557.
Proof. exact (EQ_MP (@lem5754329 _120557) (@lem5757655 _120557)). Qed.
Lemma lem5757657 {_120557 : Type'} (t : _120557 -> Prop) : term679 _120557 t.
Proof. exact (@lem5757656 _120557 t). Qed.
Lemma lem5757658 {_120557 : Type'} (t : _120557 -> Prop) : (term679 _120557 t) = (term100 _120557 t).
Proof. exact (eq_refl (term679 _120557 t)). Qed.
Lemma lem5757659 {_120557 : Type'} (t : _120557 -> Prop) : term100 _120557 t.
Proof. exact (EQ_MP (@lem5757658 _120557 t) (@lem5757657 _120557 t)). Qed.
Lemma lem5757660 {_120557 : Type'} (t : _120557 -> Prop) (s : _120557 -> Prop) : term680 _120557 t s.
Proof. exact (@lem5757659 _120557 t s). Qed.
Lemma lem5757661 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : (term680 _120557 t s) = (term74 _120557 s t).
Proof. exact (eq_refl (term680 _120557 t s)). Qed.
Lemma lem5757662 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) : term74 _120557 s t.
Proof. exact (EQ_MP (@lem5757661 _120557 s t) (@lem5757660 _120557 t s)). Qed.
Lemma lem5757663 {_120557 : Type'} (s : _120557 -> Prop) (t : _120557 -> Prop) (x : _120557) : term681 _120557 s t x.
Proof. exact (@lem5757662 _120557 s t x). Qed.
Lemma lem5757664 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term681 _120557 s t x) = (term65 _120557 x s t).
Proof. exact (eq_refl (term681 _120557 s t x)). Qed.
Lemma lem5757665 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : term65 _120557 x s t.
Proof. exact (EQ_MP (@lem5757664 _120557 x s t) (@lem5757663 _120557 s t x)). Qed.
Lemma lem5757667 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : term65 _120557 x s t.
Proof. exact (@lem5753891 _120557 x s t (@lem5757665 _120557 x s t)). Qed.
Lemma lem5757668 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term66 _120557 x s t) : False.
Proof. exact (@lem5757667 _120557 x s t (@lem5753875 _120557 x s t h1)). Qed.
Lemma lem5757669 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term66 _120557 x s t) : (term66 _120557 x s t) = False.
Proof. exact (prop_ext (fun h2 : term66 _120557 x s t => @lem5757668 _120557 x s t h1) (fun h2 : False => @lem5753875 _120557 x s t h1)). Qed.
Lemma lem5757670 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) (h1 : term66 _120557 x s t) : False.
Proof. exact (EQ_MP (@lem5757669 _120557 x s t h1) (@lem5753875 _120557 x s t h1)). Qed.
Lemma lem5757671 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : term65 _120557 x s t.
Proof. exact (fun h0 : term66 _120557 x s t => @lem5757670 _120557 x s t h0). Qed.
Lemma lem5757672 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : term63 _120557 x s t.
Proof. exact (EQ_MP (@lem5753874 _120557 x s t) (@lem5757671 _120557 x s t)). Qed.
Lemma lem5757673 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : term16 _120557 x s t.
Proof. exact (EQ_MP (@lem5753870 _120557 x s t) (@lem5757672 _120557 x s t)). Qed.
Lemma lem5757674 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : term15 _120557 x s t.
Proof. exact (EQ_MP (@lem5753651 _120557 x s t) (@lem5757673 _120557 x s t)). Qed.
Lemma lem5757685 {A : Type'} (h1 : term682 A) : term682 A.
Proof. exact (h1). Qed.
Lemma lem5757686 {A : Type'} (P : type686 A) (h1 : term682 A) : term683 A P.
Proof. exact (@lem5757685 A h1 P). Qed.
Lemma lem5757687 {A : Type'} (P : type686 A) : (term683 A P) = (term684 A P).
Proof. exact (eq_refl (term683 A P)). Qed.
Lemma lem5757688 {A : Type'} (P : type686 A) (h1 : term682 A) : term684 A P.
Proof. exact (EQ_MP (@lem5757687 A P) (@lem5757686 A P h1)). Qed.
Lemma lem5757689 {A : Type'} (P : type686 A) (h1 : term685 A P) : term685 A P.
Proof. exact (h1). Qed.
Lemma lem5757690 {A : Type'} (P : type686 A) (h1 : term682 A) (h2 : term685 A P) : term686 A P.
Proof. exact (@lem5757688 A P h1 (@lem5757689 A P h2)). Qed.
Lemma lem5757691 {A : Type'} (P : type686 A) (h1 : term685 A P) : term687 A P.
Proof. exact (fun h0 : term682 A => @lem5757690 A P h0 h1). Qed.
Lemma lem5757692 {A : Type'} (h1 : term682 A) : term682 A.
Proof. exact (h1). Qed.
Lemma lem5757693 {A : Type'} (P : type686 A) (h1 : term682 A) (h2 : term685 A P) : term686 A P.
Proof. exact (@lem5757691 A P h2 (@lem5757692 A h1)). Qed.
Lemma lem5757694 {A : Type'} (P : type686 A) (h1 : term682 A) : term684 A P.
Proof. exact (fun h0 : term685 A P => @lem5757693 A P h1 h0). Qed.
Lemma lem5757695 {A : Type'} (h1 : term682 A) : term682 A.
Proof. exact (fun P : type686 A => @lem5757694 A P h1). Qed.
Lemma lem5757696 {A : Type'} : term688 A.
Proof. exact (fun h0 : term682 A => @lem5757695 A h0). Qed.
Lemma lem5757697 {A : Type'} : term682 A.
Proof. exact (@lem5757696 A (@lem3558722 A)). Qed.
Lemma lem5757698 {A : Type'} (P : type686 A) : term683 A P.
Proof. exact (@lem5757697 A P). Qed.
Lemma lem5757699 {A : Type'} (P : type686 A) : (term683 A P) = (term684 A P).
Proof. exact (eq_refl (term683 A P)). Qed.
Lemma lem5757701 {A : Type'} (P : Prop) : term689 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem5757702 {A : Type'} (P : Prop) : (term689 A P) = (term690 A P).
Proof. exact (eq_refl (term689 A P)). Qed.
Lemma lem5757703 {A : Type'} (P : Prop) : term690 A P.
Proof. exact (EQ_MP (@lem5757702 A P) (@lem5757701 A P)). Qed.
Lemma lem5757704 {A : Type'} (P : Prop) (Q : A -> Prop) : term691 A P Q.
Proof. exact (@lem5757703 A P Q). Qed.
Lemma lem5757705 {A : Type'} (P : Prop) (Q : A -> Prop) : (term691 A P Q) = ((term692 A P Q) = (term693 A P Q)).
Proof. exact (eq_refl (term691 A P Q)). Qed.
Lemma lem5757707 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @monoidal _120607 op.
Proof. exact (h1). Qed.
Lemma lem5757733 (p : Prop) (q : Prop) (r : Prop) : (term694 p q r) = (term695 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem5757734 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term696 _120592 _120607 s op t f) = (term697 _120592 _120607 s op t f).
Proof. exact (@lem5757733 (@FINITE _120592 s) (term698 _120592 s t) ((term699 _120592 _120607 op s t f) = (term700 _120592 _120607 s op t f))). Qed.
Lemma lem5757738 (p : Prop) (q : Prop) (r : Prop) : (term694 p q r) = (term695 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem5757739 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term701 _120592 _120607 s op t f) = (term702 _120592 _120607 s op t f).
Proof. exact (@lem5757738 (@FINITE _120592 t) (@DISJOINT _120592 s t) ((term699 _120592 _120607 op s t f) = (term700 _120592 _120607 s op t f))). Qed.
Lemma lem5757746 {_120592 : Type'} (s : _120592 -> Prop) : (term703 _120592 s) = (term703 _120592 s).
Proof. exact (eq_refl (term703 _120592 s)). Qed.
Lemma lem5757747 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term697 _120592 _120607 s op t f) = (term704 _120592 _120607 s op t f).
Proof. exact (MK_COMB (@lem5757746 _120592 s) (@lem5757739 _120592 _120607 s op t f)). Qed.
Lemma lem5757750 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term696 _120592 _120607 s op t f) = (term704 _120592 _120607 s op t f).
Proof. exact (TRANS (@lem5757734 _120592 _120607 s op t f) (@lem5757747 _120592 _120607 s op t f)). Qed.
Lemma lem5757751 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term705 _120592 _120607 s op f) = (term706 _120592 _120607 s op f).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem5757750 _120592 _120607 s op t f)). Qed.
Lemma lem5757752 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5757753 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term707 _120592 _120607 s op f) = (term708 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5757752 _120592) (@lem5757751 _120592 _120607 s op f)). Qed.
Lemma lem5757755 {A : Type'} (P : Prop) (Q : A -> Prop) : (term692 A P Q) = (term693 A P Q).
Proof. exact (EQ_MP (@lem5757705 A P Q) (@lem5757704 A P Q)). Qed.
Lemma lem5757756 {_120592 : Type'} (P : Prop) (Q : type686 _120592) : (term709 _120592 P Q) = (term710 _120592 P Q).
Proof. exact (@lem5757755 (_120592 -> Prop) P Q). Qed.
Lemma lem5757757 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term711 _120592 _120607 s op f) = (term712 _120592 _120607 s op f).
Proof. exact (@lem5757756 _120592 (@FINITE _120592 s) (term713 _120592 _120607 s op f)). Qed.
Lemma lem5757758 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term714 _120592 _120607 s op f t) = (term702 _120592 _120607 s op t f).
Proof. exact (eq_refl (term714 _120592 _120607 s op f t)). Qed.
Lemma lem5757759 {_120592 : Type'} (s : _120592 -> Prop) : (term703 _120592 s) = (term703 _120592 s).
Proof. exact (eq_refl (term703 _120592 s)). Qed.
Lemma lem5757760 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term715 _120592 _120607 s op f t) = (term704 _120592 _120607 s op t f).
Proof. exact (MK_COMB (@lem5757759 _120592 s) (@lem5757758 _120592 _120607 s op t f)). Qed.
Lemma lem5757761 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term716 _120592 _120607 s op f) = (term706 _120592 _120607 s op f).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem5757760 _120592 _120607 s op t f)). Qed.
Lemma lem5757762 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5757763 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term711 _120592 _120607 s op f) = (term708 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5757762 _120592) (@lem5757761 _120592 _120607 s op f)). Qed.
Lemma lem5757764 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5757765 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term717 _120592 _120607 s op f) = (term718 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5757764) (@lem5757763 _120592 _120607 s op f)). Qed.
Lemma lem5757766 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term714 _120592 _120607 s op f t) = (term702 _120592 _120607 s op t f).
Proof. exact (eq_refl (term714 _120592 _120607 s op f t)). Qed.
Lemma lem5757767 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term719 _120592 _120607 s op f) = (term713 _120592 _120607 s op f).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem5757766 _120592 _120607 s op t f)). Qed.
Lemma lem5757768 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5757769 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term720 _120592 _120607 s op f) = (term721 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5757768 _120592) (@lem5757767 _120592 _120607 s op f)). Qed.
Lemma lem5757770 {_120592 : Type'} (s : _120592 -> Prop) : (term703 _120592 s) = (term703 _120592 s).
Proof. exact (eq_refl (term703 _120592 s)). Qed.
Lemma lem5757771 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term712 _120592 _120607 s op f) = (term722 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5757770 _120592 s) (@lem5757769 _120592 _120607 s op f)). Qed.
Lemma lem5757772 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : ((term711 _120592 _120607 s op f) = (term712 _120592 _120607 s op f)) = ((term708 _120592 _120607 s op f) = (term722 _120592 _120607 s op f)).
Proof. exact (MK_COMB (@lem5757765 _120592 _120607 s op f) (@lem5757771 _120592 _120607 s op f)). Qed.
Lemma lem5757773 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term708 _120592 _120607 s op f) = (term722 _120592 _120607 s op f).
Proof. exact (EQ_MP (@lem5757772 _120592 _120607 s op f) (@lem5757757 _120592 _120607 s op f)). Qed.
Lemma lem5757806 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term707 _120592 _120607 s op f) = (term722 _120592 _120607 s op f).
Proof. exact (TRANS (@lem5757753 _120592 _120607 s op f) (@lem5757773 _120592 _120607 s op f)). Qed.
Lemma lem5757807 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term722 _120592 _120607 s op f) = (term707 _120592 _120607 s op f).
Proof. exact (SYM (@lem5757806 _120592 _120607 s op f)). Qed.
Lemma lem5757808 {_120592 : Type'} (s : _120592 -> Prop) (h1 : @FINITE _120592 s) : @FINITE _120592 s.
Proof. exact (h1). Qed.
Lemma lem5757810 {A : Type'} (P : type686 A) : term684 A P.
Proof. exact (EQ_MP (@lem5757699 A P) (@lem5757698 A P)). Qed.
Lemma lem5757811 {_120592 : Type'} (P : type686 _120592) : term684 _120592 P.
Proof. exact (@lem5757810 _120592 P). Qed.
Lemma lem5757812 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : term723 _120592 _120607 s op f.
Proof. exact (@lem5757811 _120592 (term724 _120592 _120607 s op f)). Qed.
Lemma lem5757813 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term725 _120592 _120607 s op f) = (term726 _120592 _120607 s op f).
Proof. exact (eq_refl (term725 _120592 _120607 s op f)). Qed.
Lemma lem5757814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5757815 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term727 _120592 _120607 s op f) = (term728 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5757814) (@lem5757813 _120592 _120607 s op f)). Qed.
Lemma lem5757816 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term729 _120592 _120607 s op f t) = (term730 _120592 _120607 s op t f).
Proof. exact (eq_refl (term729 _120592 _120607 s op f t)). Qed.
Lemma lem5757817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5757818 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term731 _120592 _120607 s op f t) = (term732 _120592 _120607 s op t f).
Proof. exact (MK_COMB (@lem5757817) (@lem5757816 _120592 _120607 s op t f)). Qed.
Lemma lem5757819 {_120592 : Type'} (x : _120592) (t : _120592 -> Prop) : (term733 _120592 x t) = (term733 _120592 x t).
Proof. exact (eq_refl (term733 _120592 x t)). Qed.
Lemma lem5757820 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) : (term734 _120592 _120607 s op f x t) = (term735 _120592 _120607 s op f x t).
Proof. exact (MK_COMB (@lem5757818 _120592 _120607 s op t f) (@lem5757819 _120592 x t)). Qed.
Lemma lem5757821 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5757822 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) : (term736 _120592 _120607 s op f x t) = (term737 _120592 _120607 s op f x t).
Proof. exact (MK_COMB (@lem5757821) (@lem5757820 _120592 _120607 s op f x t)). Qed.
Lemma lem5757823 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term738 _120592 _120607 s op f x t) = (term739 _120592 _120607 s op x t f).
Proof. exact (eq_refl (term738 _120592 _120607 s op f x t)). Qed.
Lemma lem5757824 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term740 _120592 _120607 s op f x t) = (term741 _120592 _120607 s op x t f).
Proof. exact (MK_COMB (@lem5757822 _120592 _120607 s op f x t) (@lem5757823 _120592 _120607 s op x t f)). Qed.
Lemma lem5757825 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (f : _120592 -> _120607) : (term742 _120592 _120607 s op f x) = (term743 _120592 _120607 s op x f).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem5757824 _120592 _120607 s op x t f)). Qed.
Lemma lem5757826 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5757827 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (f : _120592 -> _120607) : (term744 _120592 _120607 s op f x) = (term745 _120592 _120607 s op x f).
Proof. exact (MK_COMB (@lem5757826 _120592) (@lem5757825 _120592 _120607 s op x f)). Qed.
Lemma lem5757828 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term746 _120592 _120607 s op f) = (term747 _120592 _120607 s op f).
Proof. exact (fun_ext (fun x : _120592 => @lem5757827 _120592 _120607 s op x f)). Qed.
Lemma lem5757829 {_120592 : Type'} : (@all _120592) = (@all _120592).
Proof. exact (eq_refl (@all _120592)). Qed.
Lemma lem5757830 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term748 _120592 _120607 s op f) = (term749 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5757829 _120592) (@lem5757828 _120592 _120607 s op f)). Qed.
Lemma lem5757831 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term750 _120592 _120607 s op f) = (term751 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5757815 _120592 _120607 s op f) (@lem5757830 _120592 _120607 s op f)). Qed.
Lemma lem5757832 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5757833 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term752 _120592 _120607 s op f) = (term753 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5757832) (@lem5757831 _120592 _120607 s op f)). Qed.
Lemma lem5757834 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term729 _120592 _120607 s op f t) = (term730 _120592 _120607 s op t f).
Proof. exact (eq_refl (term729 _120592 _120607 s op f t)). Qed.
Lemma lem5757835 {_120592 : Type'} (t : _120592 -> Prop) : (term703 _120592 t) = (term703 _120592 t).
Proof. exact (eq_refl (term703 _120592 t)). Qed.
Lemma lem5757836 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term754 _120592 _120607 s op f t) = (term702 _120592 _120607 s op t f).
Proof. exact (MK_COMB (@lem5757835 _120592 t) (@lem5757834 _120592 _120607 s op t f)). Qed.
Lemma lem5757837 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term755 _120592 _120607 s op f) = (term713 _120592 _120607 s op f).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem5757836 _120592 _120607 s op t f)). Qed.
Lemma lem5757838 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5757839 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term756 _120592 _120607 s op f) = (term721 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5757838 _120592) (@lem5757837 _120592 _120607 s op f)). Qed.
Lemma lem5757840 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term723 _120592 _120607 s op f) = (term757 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5757833 _120592 _120607 s op f) (@lem5757839 _120592 _120607 s op f)). Qed.
Lemma lem5757841 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : term757 _120592 _120607 s op f.
Proof. exact (EQ_MP (@lem5757840 _120592 _120607 s op f) (@lem5757812 _120592 _120607 s op f)). Qed.
Lemma lem5757842 {A : Type'} (s : A -> Prop) : term758 A s.
Proof. exact (@lem3606772 A s). Qed.
Lemma lem5757843 {A : Type'} (s : A -> Prop) : (term758 A s) = (term759 A s).
Proof. exact (eq_refl (term758 A s)). Qed.
Lemma lem5757844 {A : Type'} (s : A -> Prop) : term759 A s.
Proof. exact (EQ_MP (@lem5757843 A s) (@lem5757842 A s)). Qed.
Lemma lem5757845 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term760 A s t.
Proof. exact (@lem5757844 A s t). Qed.
Lemma lem5757846 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term760 A s t) = ((term761 A s t) = (term762 A s t)).
Proof. exact (eq_refl (term760 A s t)). Qed.
Lemma lem5757853 {A : Type'} : term763 A.
Proof. exact (proj2 (@lem3235853 A)). Qed.
Lemma lem5757854 {A : Type'} (s : A -> Prop) : term764 A s.
Proof. exact (@lem5757853 A s). Qed.
Lemma lem5757855 {A : Type'} (s : A -> Prop) : (term764 A s) = ((@UNION A s (@EMPTY A)) = s).
Proof. exact (eq_refl (term764 A s)). Qed.
Lemma lem5757861 {A : Type'} (s : A -> Prop) : term765 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem5757862 {A : Type'} (s : A -> Prop) : (term765 A s) = (term766 A s).
Proof. exact (eq_refl (term765 A s)). Qed.
Lemma lem5757863 {A : Type'} (s : A -> Prop) : term766 A s.
Proof. exact (EQ_MP (@lem5757862 A s) (@lem5757861 A s)). Qed.
Lemma lem5757864 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term767 A s t.
Proof. exact (@lem5757863 A s t). Qed.
Lemma lem5757865 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term767 A s t) = (term768 A s t).
Proof. exact (eq_refl (term767 A s t)). Qed.
Lemma lem5757866 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term768 A s t.
Proof. exact (EQ_MP (@lem5757865 A s t) (@lem5757864 A s t)). Qed.
Lemma lem5757867 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term769 A s t x.
Proof. exact (@lem5757866 A s t x). Qed.
Lemma lem5757868 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term769 A s t x) = ((term17 A x s t) = (term18 A s x t)).
Proof. exact (eq_refl (term769 A s t x)). Qed.
Lemma lem5757870 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term770 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem5757871 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term770 _120477 _120519 _120521 op) = (term771 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term770 _120477 _120519 _120521 op)). Qed.
Lemma lem5757872 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term771 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem5757871 _120477 _120519 _120521 op) (@lem5757870 _120477 _120519 _120521 op)). Qed.
Lemma lem5757873 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem5757874 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term772 _120477 _120519 _120521 op.
Proof. exact (@lem5757872 _120477 _120519 _120521 op (@lem5757873 _120519 op h1)). Qed.
Lemma lem5757875 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term773 _120519 _120521 op.
Proof. exact (proj2 (@lem5757874 Prop _120519 _120521 op h1)). Qed.
Lemma lem5757876 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term774 _120519 _120521 op f.
Proof. exact (@lem5757875 _120519 _120521 op h1 f). Qed.
Lemma lem5757877 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term774 _120519 _120521 op f) = (term775 _120519 _120521 op f).
Proof. exact (eq_refl (term774 _120519 _120521 op f)). Qed.
Lemma lem5757878 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term775 _120519 _120521 op f.
Proof. exact (EQ_MP (@lem5757877 _120519 _120521 op f) (@lem5757876 _120519 _120521 f op h1)). Qed.
Lemma lem5757879 {_120519 _120521 : Type'} (f : _120521 -> _120519) (x : _120521) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term776 _120519 _120521 op f x.
Proof. exact (@lem5757878 _120519 _120521 f op h1 x). Qed.
Lemma lem5757880 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term776 _120519 _120521 op f x) = (term777 _120519 _120521 x op f).
Proof. exact (eq_refl (term776 _120519 _120521 op f x)). Qed.
Lemma lem5757881 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term777 _120519 _120521 x op f.
Proof. exact (EQ_MP (@lem5757880 _120519 _120521 x op f) (@lem5757879 _120519 _120521 f x op h1)). Qed.
Lemma lem5757882 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term778 _120519 _120521 x op f s.
Proof. exact (@lem5757881 _120519 _120521 x f op h1 s). Qed.
Lemma lem5757883 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term778 _120519 _120521 x op f s) = (term779 _120519 _120521 x op s f).
Proof. exact (eq_refl (term778 _120519 _120521 x op f s)). Qed.
Lemma lem5757884 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term779 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5757883 _120519 _120521 x op s f) (@lem5757882 _120519 _120521 x f s op h1)). Qed.
Lemma lem5757885 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem5757886 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term780 _120519 _120521 op x s f) = (term781 _120519 _120521 x op s f).
Proof. exact (@lem5757884 _120519 _120521 x s f op h2 (@lem5757885 _120521 s h1)). Qed.
Lemma lem5757887 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : term782 _120519 _120521 x op s f.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5757886 _120519 _120521 x f s op h1 h0). Qed.
Lemma lem5757888 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term783 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem5757887 _120519 _120521 x op f s h0). Qed.
Lemma lem5757890 (p : Prop) (q : Prop) (r : Prop) : (term695 p q r) = (term694 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5757895 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term783 _120519 _120521 x op s f) = (term784 _120519 _120521 x op s f).
Proof. exact (@lem5757890 (@FINITE _120521 s) (@monoidal _120519 op) ((term780 _120519 _120521 op x s f) = (term781 _120519 _120521 x op s f))). Qed.
Lemma lem5757897 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term785 _120477 _120519 op.
Proof. exact (proj1 (@lem5757874 _120477 _120519 Prop op h1)). Qed.
Lemma lem5757898 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term786 _120477 _120519 op f.
Proof. exact (@lem5757897 _120477 _120519 op h1 f). Qed.
Lemma lem5757899 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term786 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term786 _120477 _120519 op f)). Qed.
Lemma lem5757900 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem5757899 _120477 _120519 f op) (@lem5757898 _120477 _120519 f op h1)). Qed.
Lemma lem5757906 {_120607 : Type'} (op : type1400 _120607) : (@monoidal _120607 op) = ((@monoidal _120607 op) = True).
Proof. exact (@lem7 (@monoidal _120607 op)). Qed.
Lemma lem5757908 {_120592 : Type'} (s : _120592 -> Prop) : (@FINITE _120592 s) = ((@FINITE _120592 s) = True).
Proof. exact (@lem7 (@FINITE _120592 s)). Qed.
Lemma lem5757915 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term787 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5757916 (p : Prop) (q : Prop) (p' : Prop) : term788 p q p'.
Proof. exact (fun q' : Prop => @lem5757915 p q p' q'). Qed.
Lemma lem5757917 (p : Prop) (q : Prop) : term789 p q.
Proof. exact (fun p' : Prop => @lem5757916 p q p'). Qed.
Lemma lem5757918 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : term790 _120592 _120607 s op f.
Proof. exact (@lem5757917 (@DISJOINT _120592 s (@EMPTY _120592)) ((term791 _120592 _120607 op s f) = (term792 _120592 _120607 s op f))). Qed.
Lemma lem5757919 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (p' : Prop) : term793 _120592 _120607 s op f p'.
Proof. exact (@lem5757918 _120592 _120607 s op f p'). Qed.
Lemma lem5757920 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (p' : Prop) : (term793 _120592 _120607 s op f p') = (term794 _120592 _120607 s op f p').
Proof. exact (eq_refl (term793 _120592 _120607 s op f p')). Qed.
Lemma lem5757921 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (p' : Prop) : term794 _120592 _120607 s op f p'.
Proof. exact (EQ_MP (@lem5757920 _120592 _120607 s op f p') (@lem5757919 _120592 _120607 s op f p')). Qed.
Lemma lem5757922 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (p' : Prop) (q' : Prop) : term795 _120592 _120607 s op f p' q'.
Proof. exact (@lem5757921 _120592 _120607 s op f p' q'). Qed.
Lemma lem5757923 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (p' : Prop) (q' : Prop) : (term795 _120592 _120607 s op f p' q') = (term796 _120592 _120607 s op f p' q').
Proof. exact (eq_refl (term795 _120592 _120607 s op f p' q')). Qed.
Lemma lem5757924 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (p' : Prop) (q' : Prop) : term796 _120592 _120607 s op f p' q'.
Proof. exact (EQ_MP (@lem5757923 _120592 _120607 s op f p' q') (@lem5757922 _120592 _120607 s op f p' q')). Qed.
Lemma lem5757925 {_120592 : Type'} (s : _120592 -> Prop) : (@DISJOINT _120592 s (@EMPTY _120592)) = (@DISJOINT _120592 s (@EMPTY _120592)).
Proof. exact (eq_refl (@DISJOINT _120592 s (@EMPTY _120592))). Qed.
Lemma lem5757926 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) (s : _120592 -> Prop) (q' : Prop) : term797 _120592 _120607 op f s q'.
Proof. exact (@lem5757924 _120592 _120607 s op f (@DISJOINT _120592 s (@EMPTY _120592)) q'). Qed.
Lemma lem5757927 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) (s : _120592 -> Prop) (q' : Prop) : term798 _120592 _120607 op f s q'.
Proof. exact (@lem5757926 _120592 _120607 op f s q' (@lem5757925 _120592 s)). Qed.
Lemma lem5757934 {A : Type'} (s : A -> Prop) : (@UNION A s (@EMPTY A)) = s.
Proof. exact (EQ_MP (@lem5757855 A s) (@lem5757854 A s)). Qed.
Lemma lem5757935 {_120592 : Type'} (s : _120592 -> Prop) : (@UNION _120592 s (@EMPTY _120592)) = s.
Proof. exact (@lem5757934 _120592 s). Qed.
Lemma lem5757936 {_120592 _120607 : Type'} (op : type1400 _120607) : (@iterate _120607 _120592 op) = (@iterate _120607 _120592 op).
Proof. exact (eq_refl (@iterate _120607 _120592 op)). Qed.
Lemma lem5757937 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (term799 _120592 _120607 op s) = (@iterate _120607 _120592 op s).
Proof. exact (MK_COMB (@lem5757936 _120592 _120607 op) (@lem5757935 _120592 s)). Qed.
Lemma lem5757938 {_120592 _120607 : Type'} (f : _120592 -> _120607) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5757939 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term791 _120592 _120607 op s f) = (@iterate _120607 _120592 op s f).
Proof. exact (MK_COMB (@lem5757937 _120592 _120607 op s) (@lem5757938 _120592 _120607 f)). Qed.
Lemma lem5757940 {_120607 : Type'} : (@eq _120607) = (@eq _120607).
Proof. exact (eq_refl (@eq _120607)). Qed.
Lemma lem5757941 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term800 _120592 _120607 op s f) = (term801 _120592 _120607 op s f).
Proof. exact (MK_COMB (@lem5757940 _120607) (@lem5757939 _120592 _120607 op s f)). Qed.
Lemma lem5757943 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term802 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5757900 _120477 _120519 f op h0). Qed.
Lemma lem5757944 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) : term802 _120592 _120607 f op.
Proof. exact (@lem5757943 _120592 _120607 f op). Qed.
Lemma lem5757946 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : (@monoidal _120607 op) = True.
Proof. exact (EQ_MP (@lem5757906 _120607 op) (@lem5757707 _120607 op h1)). Qed.
Lemma lem5757947 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : True = (@monoidal _120607 op).
Proof. exact (SYM (@lem5757946 _120607 op h1)). Qed.
Lemma lem5757948 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @monoidal _120607 op.
Proof. exact (EQ_MP (@lem5757947 _120607 op h1) (@lem0)). Qed.
Lemma lem5757949 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : (@iterate _120607 _120592 op (@EMPTY _120592) f) = (@neutral _120607 op).
Proof. exact (@lem5757944 _120592 _120607 f op (@lem5757948 _120607 op h1)). Qed.
Lemma lem5757950 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term803 _120592 _120607 op s f) = (term803 _120592 _120607 op s f).
Proof. exact (eq_refl (term803 _120592 _120607 op s f)). Qed.
Lemma lem5757951 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : (term792 _120592 _120607 s op f) = (term804 _120592 _120607 s f op).
Proof. exact (MK_COMB (@lem5757950 _120592 _120607 op s f) (@lem5757949 _120592 _120607 f op h1)). Qed.
Lemma lem5757952 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : ((term791 _120592 _120607 op s f) = (term792 _120592 _120607 s op f)) = ((@iterate _120607 _120592 op s f) = (term804 _120592 _120607 s f op)).
Proof. exact (MK_COMB (@lem5757941 _120592 _120607 op s f) (@lem5757951 _120592 _120607 s f op h1)). Qed.
Lemma lem5757955 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term805 _120592 _120607 s f op.
Proof. exact (fun h0 : @DISJOINT _120592 s (@EMPTY _120592) => @lem5757952 _120592 _120607 s f op h1). Qed.
Lemma lem5757956 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : term806 _120592 _120607 s f op.
Proof. exact (@lem5757927 _120592 _120607 op f s ((@iterate _120607 _120592 op s f) = (term804 _120592 _120607 s f op))). Qed.
Lemma lem5757957 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : (term726 _120592 _120607 s op f) = (term807 _120592 _120607 s f op).
Proof. exact (@lem5757956 _120592 _120607 s f op (@lem5757955 _120592 _120607 s f op h1)). Qed.
Lemma lem5757985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5757986 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : (term728 _120592 _120607 s op f) = (term808 _120592 _120607 s f op).
Proof. exact (MK_COMB (@lem5757985) (@lem5757957 _120592 _120607 s f op h1)). Qed.
Lemma lem5758025 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term787 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5758026 (p : Prop) (q : Prop) (p' : Prop) : term788 p q p'.
Proof. exact (fun q' : Prop => @lem5758025 p q p' q'). Qed.
Lemma lem5758027 (p : Prop) (q : Prop) : term789 p q.
Proof. exact (fun p' : Prop => @lem5758026 p q p'). Qed.
Lemma lem5758028 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) : term809 _120592 _120607 s op x t f.
Proof. exact (@lem5758027 (term735 _120592 _120607 s op f x t) (term739 _120592 _120607 s op x t f)). Qed.
Lemma lem5758029 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (p' : Prop) : term810 _120592 _120607 s op x t f p'.
Proof. exact (@lem5758028 _120592 _120607 s op x t f p'). Qed.
Lemma lem5758030 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (p' : Prop) : (term810 _120592 _120607 s op x t f p') = (term811 _120592 _120607 s op x t f p').
Proof. exact (eq_refl (term810 _120592 _120607 s op x t f p')). Qed.
Lemma lem5758031 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (p' : Prop) : term811 _120592 _120607 s op x t f p'.
Proof. exact (EQ_MP (@lem5758030 _120592 _120607 s op x t f p') (@lem5758029 _120592 _120607 s op x t f p')). Qed.
Lemma lem5758032 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (p' : Prop) (q' : Prop) : term812 _120592 _120607 s op x t f p' q'.
Proof. exact (@lem5758031 _120592 _120607 s op x t f p' q'). Qed.
Lemma lem5758033 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (p' : Prop) (q' : Prop) : (term812 _120592 _120607 s op x t f p' q') = (term813 _120592 _120607 s op x t f p' q').
Proof. exact (eq_refl (term812 _120592 _120607 s op x t f p' q')). Qed.
Lemma lem5758034 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (p' : Prop) (q' : Prop) : term813 _120592 _120607 s op x t f p' q'.
Proof. exact (EQ_MP (@lem5758033 _120592 _120607 s op x t f p' q') (@lem5758032 _120592 _120607 s op x t f p' q')). Qed.
Lemma lem5758066 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) : (term735 _120592 _120607 s op f x t) = (term735 _120592 _120607 s op f x t).
Proof. exact (eq_refl (term735 _120592 _120607 s op f x t)). Qed.
Lemma lem5758067 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (q' : Prop) : term814 _120592 _120607 s op f x t q'.
Proof. exact (@lem5758034 _120592 _120607 s op x t f (term735 _120592 _120607 s op f x t) q'). Qed.
Lemma lem5758068 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (q' : Prop) : term815 _120592 _120607 s op f x t q'.
Proof. exact (@lem5758067 _120592 _120607 s op f x t q' (@lem5758066 _120592 _120607 s op f x t)). Qed.
Lemma lem5758069 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : term735 _120592 _120607 s op f x t.
Proof. exact (h1). Qed.
Lemma lem5758070 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : term733 _120592 x t.
Proof. exact (proj2 (@lem5758069 _120592 _120607 s op f x t h1)). Qed.
Lemma lem5758071 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : @FINITE _120592 t.
Proof. exact (proj2 (@lem5758070 _120592 _120607 s op f x t h1)). Qed.
Lemma lem5758072 {_120592 : Type'} (t : _120592 -> Prop) : (@FINITE _120592 t) = ((@FINITE _120592 t) = True).
Proof. exact (@lem7 (@FINITE _120592 t)). Qed.
Lemma lem5758074 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : term52 _120592 x t.
Proof. exact (proj1 (@lem5758070 _120592 _120607 s op f x t h1)). Qed.
Lemma lem5758075 {_120592 : Type'} (x : _120592) (t : _120592 -> Prop) : term816 _120592 x t.
Proof. exact (@lem82 (@IN _120592 x t)). Qed.
Lemma lem5758077 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : term730 _120592 _120607 s op t f.
Proof. exact (proj1 (@lem5758069 _120592 _120607 s op f x t h1)). Qed.
Lemma lem5758078 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : @DISJOINT _120592 s t) : @DISJOINT _120592 s t.
Proof. exact (h1). Qed.
Lemma lem5758079 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) (h2 : @DISJOINT _120592 s t) : (term699 _120592 _120607 op s t f) = (term700 _120592 _120607 s op t f).
Proof. exact (@lem5758077 _120592 _120607 s op f x t h1 (@lem5758078 _120592 s t h2)). Qed.
Lemma lem5758088 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term787 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5758089 (p : Prop) (q : Prop) (p' : Prop) : term788 p q p'.
Proof. exact (fun q' : Prop => @lem5758088 p q p' q'). Qed.
Lemma lem5758090 (p : Prop) (q : Prop) : term789 p q.
Proof. exact (fun p' : Prop => @lem5758089 p q p'). Qed.
Lemma lem5758091 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) : term817 _120592 _120607 s op x t f.
Proof. exact (@lem5758090 (term6 _120592 s x t) ((term818 _120592 _120607 op s x t f) = (term819 _120592 _120607 s op x t f))). Qed.
Lemma lem5758092 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (p' : Prop) : term820 _120592 _120607 s op x t f p'.
Proof. exact (@lem5758091 _120592 _120607 s op x t f p'). Qed.
Lemma lem5758093 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (p' : Prop) : (term820 _120592 _120607 s op x t f p') = (term821 _120592 _120607 s op x t f p').
Proof. exact (eq_refl (term820 _120592 _120607 s op x t f p')). Qed.
Lemma lem5758094 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (p' : Prop) : term821 _120592 _120607 s op x t f p'.
Proof. exact (EQ_MP (@lem5758093 _120592 _120607 s op x t f p') (@lem5758092 _120592 _120607 s op x t f p')). Qed.
Lemma lem5758095 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (p' : Prop) (q' : Prop) : term822 _120592 _120607 s op x t f p' q'.
Proof. exact (@lem5758094 _120592 _120607 s op x t f p' q'). Qed.
Lemma lem5758096 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (p' : Prop) (q' : Prop) : (term822 _120592 _120607 s op x t f p' q') = (term823 _120592 _120607 s op x t f p' q').
Proof. exact (eq_refl (term822 _120592 _120607 s op x t f p' q')). Qed.
Lemma lem5758097 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (p' : Prop) (q' : Prop) : term823 _120592 _120607 s op x t f p' q'.
Proof. exact (EQ_MP (@lem5758096 _120592 _120607 s op x t f p' q') (@lem5758095 _120592 _120607 s op x t f p' q')). Qed.
Lemma lem5758099 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term6 _120557 s x t) = (term13 _120557 x s t).
Proof. exact (proj2 (@lem5757674 _120557 x s t)). Qed.
Lemma lem5758100 {_120592 : Type'} (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) : (term6 _120592 s x t) = (term13 _120592 x s t).
Proof. exact (@lem5758099 _120592 x s t). Qed.
Lemma lem5758103 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (q' : Prop) : term824 _120592 _120607 op f x s t q'.
Proof. exact (@lem5758097 _120592 _120607 s op x t f (term13 _120592 x s t) q'). Qed.
Lemma lem5758104 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (q' : Prop) : term825 _120592 _120607 op f x s t q'.
Proof. exact (@lem5758103 _120592 _120607 op f x s t q' (@lem5758100 _120592 x s t)). Qed.
Lemma lem5758105 {_120592 : Type'} (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) : term13 _120592 x s t.
Proof. exact (h1). Qed.
Lemma lem5758106 {_120592 : Type'} (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) : @DISJOINT _120592 s t.
Proof. exact (proj2 (@lem5758105 _120592 x s t h1)). Qed.
Lemma lem5758107 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (@DISJOINT _120592 s t) = ((@DISJOINT _120592 s t) = True).
Proof. exact (@lem7 (@DISJOINT _120592 s t)). Qed.
Lemma lem5758109 {_120592 : Type'} (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) : term52 _120592 x s.
Proof. exact (proj1 (@lem5758105 _120592 x s t h1)). Qed.
Lemma lem5758110 {_120592 : Type'} (x : _120592) (s : _120592 -> Prop) : term816 _120592 x s.
Proof. exact (@lem82 (@IN _120592 x s)). Qed.
Lemma lem5758115 {_120557 : Type'} (x : _120557) (s : _120557 -> Prop) (t : _120557 -> Prop) : (term1 _120557 s x t) = (term2 _120557 x s t).
Proof. exact (proj1 (@lem5757674 _120557 x s t)). Qed.
Lemma lem5758116 {_120592 : Type'} (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) : (term1 _120592 s x t) = (term2 _120592 x s t).
Proof. exact (@lem5758115 _120592 x s t). Qed.
Lemma lem5758117 {_120592 _120607 : Type'} (op : type1400 _120607) : (@iterate _120607 _120592 op) = (@iterate _120607 _120592 op).
Proof. exact (eq_refl (@iterate _120607 _120592 op)). Qed.
Lemma lem5758118 {_120592 _120607 : Type'} (op : type1400 _120607) (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) : (term826 _120592 _120607 op s x t) = (term827 _120592 _120607 op x s t).
Proof. exact (MK_COMB (@lem5758117 _120592 _120607 op) (@lem5758116 _120592 x s t)). Qed.
Lemma lem5758119 {_120592 _120607 : Type'} (f : _120592 -> _120607) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5758120 {_120592 _120607 : Type'} (op : type1400 _120607) (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term818 _120592 _120607 op s x t f) = (term828 _120592 _120607 op x s t f).
Proof. exact (MK_COMB (@lem5758118 _120592 _120607 op x s t) (@lem5758119 _120592 _120607 f)). Qed.
Lemma lem5758122 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term784 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5757895 _120519 _120521 x op s f) (@lem5757888 _120519 _120521 x op s f)). Qed.
Lemma lem5758123 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : term829 _120592 _120607 x op s f.
Proof. exact (@lem5758122 _120607 _120592 x op s f). Qed.
Lemma lem5758124 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) : term830 _120592 _120607 x op s t f.
Proof. exact (@lem5758123 _120592 _120607 x op (@UNION _120592 s t) f). Qed.
Lemma lem5758128 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term761 A s t) = (term762 A s t).
Proof. exact (EQ_MP (@lem5757846 A s t) (@lem5757845 A s t)). Qed.
Lemma lem5758129 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (term761 _120592 s t) = (term762 _120592 s t).
Proof. exact (@lem5758128 _120592 s t). Qed.
Lemma lem5758133 {_120592 : Type'} (s : _120592 -> Prop) (h1 : @FINITE _120592 s) : (@FINITE _120592 s) = True.
Proof. exact (EQ_MP (@lem5757908 _120592 s) (@lem5757808 _120592 s h1)). Qed.
Lemma lem5758134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5758135 {_120592 : Type'} (s : _120592 -> Prop) (h1 : @FINITE _120592 s) : (term831 _120592 s) = (and True).
Proof. exact (MK_COMB (@lem5758134) (@lem5758133 _120592 s h1)). Qed.
Lemma lem5758137 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : (@FINITE _120592 t) = True.
Proof. exact (EQ_MP (@lem5758072 _120592 t) (@lem5758071 _120592 _120607 s op f x t h1)). Qed.
Lemma lem5758138 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @FINITE _120592 s) (h2 : term735 _120592 _120607 s op f x t) : (term762 _120592 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5758135 _120592 s h1) (@lem5758137 _120592 _120607 s op f x t h2)). Qed.
Lemma lem5758140 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5758141 : (True /\ True) = True.
Proof. exact (@lem5758140 True). Qed.
Lemma lem5758142 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @FINITE _120592 s) (h2 : term735 _120592 _120607 s op f x t) : (term762 _120592 s t) = True.
Proof. exact (TRANS (@lem5758138 _120592 _120607 s op f x t h1 h2) (@lem5758141)). Qed.
Lemma lem5758143 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @FINITE _120592 s) (h2 : term735 _120592 _120607 s op f x t) : (term761 _120592 s t) = True.
Proof. exact (TRANS (@lem5758129 _120592 s t) (@lem5758142 _120592 _120607 s op f x t h1 h2)). Qed.
Lemma lem5758144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5758145 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @FINITE _120592 s) (h2 : term735 _120592 _120607 s op f x t) : (term832 _120592 s t) = (and True).
Proof. exact (MK_COMB (@lem5758144) (@lem5758143 _120592 _120607 s op f x t h1 h2)). Qed.
Lemma lem5758147 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : (@monoidal _120607 op) = True.
Proof. exact (EQ_MP (@lem5757906 _120607 op) (@lem5757707 _120607 op h1)). Qed.
Lemma lem5758148 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) (h3 : term735 _120592 _120607 s op f x t) : (term833 _120592 _120607 s t op) = (True /\ True).
Proof. exact (MK_COMB (@lem5758145 _120592 _120607 s op f x t h1 h3) (@lem5758147 _120607 op h2)). Qed.
Lemma lem5758150 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5758151 : (True /\ True) = True.
Proof. exact (@lem5758150 True). Qed.
Lemma lem5758152 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) (h3 : term735 _120592 _120607 s op f x t) : (term833 _120592 _120607 s t op) = True.
Proof. exact (TRANS (@lem5758148 _120592 _120607 s op f x t h1 h2 h3) (@lem5758151)). Qed.
Lemma lem5758153 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) (h3 : term735 _120592 _120607 s op f x t) : True = (term833 _120592 _120607 s t op).
Proof. exact (SYM (@lem5758152 _120592 _120607 s op f x t h1 h2 h3)). Qed.
Lemma lem5758154 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) (h3 : term735 _120592 _120607 s op f x t) : term833 _120592 _120607 s t op.
Proof. exact (EQ_MP (@lem5758153 _120592 _120607 s op f x t h1 h2 h3) (@lem0)). Qed.
Lemma lem5758155 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) (h3 : term735 _120592 _120607 s op f x t) : (term828 _120592 _120607 op x s t f) = (term834 _120592 _120607 x op s t f).
Proof. exact (@lem5758124 _120592 _120607 x op s t f (@lem5758154 _120592 _120607 s op f x t h1 h2 h3)). Qed.
Lemma lem5758157 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term835 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5758158 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term836 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5758157 _2963 g t e g' t' e'). Qed.
Lemma lem5758159 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term837 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5758158 _2963 g t e g' t'). Qed.
Lemma lem5758160 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term838 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5758159 _2963 g t e g'). Qed.
Lemma lem5758161 {_120607 : Type'} (g : Prop) (t : _120607) (e : _120607) : term838 _120607 g t e.
Proof. exact (@lem5758160 _120607 g t e). Qed.
Lemma lem5758162 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) : term839 _120592 _120607 x op s t f.
Proof. exact (@lem5758161 _120607 (term17 _120592 x s t) (term699 _120592 _120607 op s t f) (term840 _120592 _120607 x op s t f)). Qed.
Lemma lem5758163 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) : term841 _120592 _120607 x op s t f g'.
Proof. exact (@lem5758162 _120592 _120607 x op s t f g'). Qed.
Lemma lem5758164 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) : (term841 _120592 _120607 x op s t f g') = (term842 _120592 _120607 x op s t f g').
Proof. exact (eq_refl (term841 _120592 _120607 x op s t f g')). Qed.
Lemma lem5758165 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) : term842 _120592 _120607 x op s t f g'.
Proof. exact (EQ_MP (@lem5758164 _120592 _120607 x op s t f g') (@lem5758163 _120592 _120607 x op s t f g')). Qed.
Lemma lem5758166 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) (t' : _120607) : term843 _120592 _120607 x op s t f g' t'.
Proof. exact (@lem5758165 _120592 _120607 x op s t f g' t'). Qed.
Lemma lem5758167 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) (t' : _120607) : (term843 _120592 _120607 x op s t f g' t') = (term844 _120592 _120607 x op s t f g' t').
Proof. exact (eq_refl (term843 _120592 _120607 x op s t f g' t')). Qed.
Lemma lem5758168 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) (t' : _120607) : term844 _120592 _120607 x op s t f g' t'.
Proof. exact (EQ_MP (@lem5758167 _120592 _120607 x op s t f g' t') (@lem5758166 _120592 _120607 x op s t f g' t')). Qed.
Lemma lem5758169 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) (t' : _120607) (e' : _120607) : term845 _120592 _120607 x op s t f g' t' e'.
Proof. exact (@lem5758168 _120592 _120607 x op s t f g' t' e'). Qed.
Lemma lem5758170 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) (t' : _120607) (e' : _120607) : (term845 _120592 _120607 x op s t f g' t' e') = (term846 _120592 _120607 x op s t f g' t' e').
Proof. exact (eq_refl (term845 _120592 _120607 x op s t f g' t' e')). Qed.
Lemma lem5758171 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) (t' : _120607) (e' : _120607) : term846 _120592 _120607 x op s t f g' t' e'.
Proof. exact (EQ_MP (@lem5758170 _120592 _120607 x op s t f g' t' e') (@lem5758169 _120592 _120607 x op s t f g' t' e')). Qed.
Lemma lem5758173 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term17 A x s t) = (term18 A s x t).
Proof. exact (EQ_MP (@lem5757868 A s x t) (@lem5757867 A s t x)). Qed.
Lemma lem5758174 {_120592 : Type'} (s : _120592 -> Prop) (x : _120592) (t : _120592 -> Prop) : (term17 _120592 x s t) = (term18 _120592 s x t).
Proof. exact (@lem5758173 _120592 s x t). Qed.
Lemma lem5758178 {_120592 : Type'} (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) : (@IN _120592 x s) = False.
Proof. exact (@lem5758110 _120592 x s (@lem5758109 _120592 x s t h1)). Qed.
Lemma lem5758179 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5758180 {_120592 : Type'} (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) : (term21 _120592 x s) = (or False).
Proof. exact (MK_COMB (@lem5758179) (@lem5758178 _120592 x s t h1)). Qed.
Lemma lem5758182 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : (@IN _120592 x t) = False.
Proof. exact (@lem5758075 _120592 x t (@lem5758074 _120592 _120607 s op f x t h1)). Qed.
Lemma lem5758183 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) (h2 : term735 _120592 _120607 s op f x t) : (term18 _120592 s x t) = (False \/ False).
Proof. exact (MK_COMB (@lem5758180 _120592 x s t h1) (@lem5758182 _120592 _120607 s op f x t h2)). Qed.
Lemma lem5758185 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem5758186 : (False \/ False) = False.
Proof. exact (@lem5758185 False). Qed.
Lemma lem5758187 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) (h2 : term735 _120592 _120607 s op f x t) : (term18 _120592 s x t) = False.
Proof. exact (TRANS (@lem5758183 _120592 _120607 s op f x t h1 h2) (@lem5758186)). Qed.
Lemma lem5758188 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) (h2 : term735 _120592 _120607 s op f x t) : (term17 _120592 x s t) = False.
Proof. exact (TRANS (@lem5758174 _120592 s x t) (@lem5758187 _120592 _120607 s op f x t h1 h2)). Qed.
Lemma lem5758189 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (t' : _120607) (e' : _120607) : term847 _120592 _120607 x op s t f t' e'.
Proof. exact (@lem5758171 _120592 _120607 x op s t f False t' e'). Qed.
Lemma lem5758190 {_120592 _120607 : Type'} (t' : _120607) (e' : _120607) (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) (h2 : term735 _120592 _120607 s op f x t) : term848 _120592 _120607 x op s t f t' e'.
Proof. exact (@lem5758189 _120592 _120607 x op s t f t' e' (@lem5758188 _120592 _120607 s op f x t h1 h2)). Qed.
Lemma lem5758195 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : term730 _120592 _120607 s op t f.
Proof. exact (fun h0 : @DISJOINT _120592 s t => @lem5758079 _120592 _120607 op f x s t h1 h0). Qed.
Lemma lem5758197 {_120592 : Type'} (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) : (@DISJOINT _120592 s t) = True.
Proof. exact (EQ_MP (@lem5758107 _120592 s t) (@lem5758106 _120592 x s t h1)). Qed.
Lemma lem5758198 {_120592 : Type'} (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) : True = (@DISJOINT _120592 s t).
Proof. exact (SYM (@lem5758197 _120592 x s t h1)). Qed.
Lemma lem5758199 {_120592 : Type'} (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) : @DISJOINT _120592 s t.
Proof. exact (EQ_MP (@lem5758198 _120592 x s t h1) (@lem0)). Qed.
Lemma lem5758200 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) (h2 : term735 _120592 _120607 s op f x t) : (term699 _120592 _120607 op s t f) = (term700 _120592 _120607 s op t f).
Proof. exact (@lem5758195 _120592 _120607 s op f x t h2 (@lem5758199 _120592 x s t h1)). Qed.
Lemma lem5758201 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) (h2 : term735 _120592 _120607 s op f x t) : term849 _120592 _120607 s op t f.
Proof. exact (fun h0 : False => @lem5758200 _120592 _120607 s op f x t h1 h2). Qed.
Lemma lem5758202 {_120592 _120607 : Type'} (e' : _120607) (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) (h2 : term735 _120592 _120607 s op f x t) : term850 _120592 _120607 x s op t f e'.
Proof. exact (@lem5758190 _120592 _120607 (term700 _120592 _120607 s op t f) e' s op f x t h1 h2). Qed.
Lemma lem5758203 {_120592 _120607 : Type'} (e' : _120607) (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) (h2 : term735 _120592 _120607 s op f x t) : term851 _120592 _120607 x s op t f e'.
Proof. exact (@lem5758202 _120592 _120607 e' s op f x t h1 h2 (@lem5758201 _120592 _120607 s op f x t h1 h2)). Qed.
Lemma lem5758210 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : term730 _120592 _120607 s op t f.
Proof. exact (fun h0 : @DISJOINT _120592 s t => @lem5758079 _120592 _120607 op f x s t h1 h0). Qed.
Lemma lem5758212 {_120592 : Type'} (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) : (@DISJOINT _120592 s t) = True.
Proof. exact (EQ_MP (@lem5758107 _120592 s t) (@lem5758106 _120592 x s t h1)). Qed.
Lemma lem5758213 {_120592 : Type'} (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) : True = (@DISJOINT _120592 s t).
Proof. exact (SYM (@lem5758212 _120592 x s t h1)). Qed.
Lemma lem5758214 {_120592 : Type'} (x : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) : @DISJOINT _120592 s t.
Proof. exact (EQ_MP (@lem5758213 _120592 x s t h1) (@lem0)). Qed.
Lemma lem5758215 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) (h2 : term735 _120592 _120607 s op f x t) : (term699 _120592 _120607 op s t f) = (term700 _120592 _120607 s op t f).
Proof. exact (@lem5758210 _120592 _120607 s op f x t h2 (@lem5758214 _120592 x s t h1)). Qed.
Lemma lem5758216 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) : (term852 _120592 _120607 op f x) = (term852 _120592 _120607 op f x).
Proof. exact (eq_refl (term852 _120592 _120607 op f x)). Qed.
Lemma lem5758217 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) (h2 : term735 _120592 _120607 s op f x t) : (term840 _120592 _120607 x op s t f) = (term853 _120592 _120607 x s op t f).
Proof. exact (MK_COMB (@lem5758216 _120592 _120607 op f x) (@lem5758215 _120592 _120607 s op f x t h1 h2)). Qed.
Lemma lem5758218 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) (h2 : term735 _120592 _120607 s op f x t) : term854 _120592 _120607 x s op t f.
Proof. exact (fun h0 : ~ False => @lem5758217 _120592 _120607 s op f x t h1 h2). Qed.
Lemma lem5758219 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) (h2 : term735 _120592 _120607 s op f x t) : term855 _120592 _120607 x s op t f.
Proof. exact (@lem5758203 _120592 _120607 (term853 _120592 _120607 x s op t f) s op f x t h1 h2). Qed.
Lemma lem5758220 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) (h2 : term735 _120592 _120607 s op f x t) : (term834 _120592 _120607 x op s t f) = (term856 _120592 _120607 x s op t f).
Proof. exact (@lem5758219 _120592 _120607 s op f x t h1 h2 (@lem5758218 _120592 _120607 s op f x t h1 h2)). Qed.
Lemma lem5758222 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5758223 {_120607 : Type'} (t1 : _120607) (t2 : _120607) : (@COND _120607 False t1 t2) = t2.
Proof. exact (@lem5758222 _120607 t1 t2). Qed.
Lemma lem5758224 {_120592 _120607 : Type'} (x : _120592) (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term856 _120592 _120607 x s op t f) = (term853 _120592 _120607 x s op t f).
Proof. exact (@lem5758223 _120607 (term700 _120592 _120607 s op t f) (term853 _120592 _120607 x s op t f)). Qed.
Lemma lem5758225 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term13 _120592 x s t) (h2 : term735 _120592 _120607 s op f x t) : (term834 _120592 _120607 x op s t f) = (term853 _120592 _120607 x s op t f).
Proof. exact (TRANS (@lem5758220 _120592 _120607 s op f x t h1 h2) (@lem5758224 _120592 _120607 x s op t f)). Qed.
Lemma lem5758226 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) (h3 : term13 _120592 x s t) (h4 : term735 _120592 _120607 s op f x t) : (term828 _120592 _120607 op x s t f) = (term853 _120592 _120607 x s op t f).
Proof. exact (TRANS (@lem5758155 _120592 _120607 s op f x t h1 h2 h4) (@lem5758225 _120592 _120607 s op f x t h3 h4)). Qed.
Lemma lem5758227 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) (h3 : term13 _120592 x s t) (h4 : term735 _120592 _120607 s op f x t) : (term818 _120592 _120607 op s x t f) = (term853 _120592 _120607 x s op t f).
Proof. exact (TRANS (@lem5758120 _120592 _120607 op x s t f) (@lem5758226 _120592 _120607 s op f x t h1 h2 h3 h4)). Qed.
Lemma lem5758228 {_120607 : Type'} : (@eq _120607) = (@eq _120607).
Proof. exact (eq_refl (@eq _120607)). Qed.
Lemma lem5758229 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) (h3 : term13 _120592 x s t) (h4 : term735 _120592 _120607 s op f x t) : (term857 _120592 _120607 op s x t f) = (term858 _120592 _120607 x s op t f).
Proof. exact (MK_COMB (@lem5758228 _120607) (@lem5758227 _120592 _120607 s op f x t h1 h2 h3 h4)). Qed.
Lemma lem5758231 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term784 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5757895 _120519 _120521 x op s f) (@lem5757888 _120519 _120521 x op s f)). Qed.
Lemma lem5758232 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : term829 _120592 _120607 x op s f.
Proof. exact (@lem5758231 _120607 _120592 x op s f). Qed.
Lemma lem5758233 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term829 _120592 _120607 x op t f.
Proof. exact (@lem5758232 _120592 _120607 x op t f). Qed.
Lemma lem5758237 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : (@FINITE _120592 t) = True.
Proof. exact (EQ_MP (@lem5758072 _120592 t) (@lem5758071 _120592 _120607 s op f x t h1)). Qed.
Lemma lem5758238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5758239 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : (term831 _120592 t) = (and True).
Proof. exact (MK_COMB (@lem5758238) (@lem5758237 _120592 _120607 s op f x t h1)). Qed.
Lemma lem5758241 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : (@monoidal _120607 op) = True.
Proof. exact (EQ_MP (@lem5757906 _120607 op) (@lem5757707 _120607 op h1)). Qed.
Lemma lem5758242 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @monoidal _120607 op) (h2 : term735 _120592 _120607 s op f x t) : (term859 _120592 _120607 t op) = (True /\ True).
Proof. exact (MK_COMB (@lem5758239 _120592 _120607 s op f x t h2) (@lem5758241 _120607 op h1)). Qed.
Lemma lem5758244 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5758245 : (True /\ True) = True.
Proof. exact (@lem5758244 True). Qed.
Lemma lem5758246 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @monoidal _120607 op) (h2 : term735 _120592 _120607 s op f x t) : (term859 _120592 _120607 t op) = True.
Proof. exact (TRANS (@lem5758242 _120592 _120607 s op f x t h1 h2) (@lem5758245)). Qed.
Lemma lem5758247 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @monoidal _120607 op) (h2 : term735 _120592 _120607 s op f x t) : True = (term859 _120592 _120607 t op).
Proof. exact (SYM (@lem5758246 _120592 _120607 s op f x t h1 h2)). Qed.
Lemma lem5758248 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @monoidal _120607 op) (h2 : term735 _120592 _120607 s op f x t) : term859 _120592 _120607 t op.
Proof. exact (EQ_MP (@lem5758247 _120592 _120607 s op f x t h1 h2) (@lem0)). Qed.
Lemma lem5758249 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @monoidal _120607 op) (h2 : term735 _120592 _120607 s op f x t) : (term860 _120592 _120607 op x t f) = (term861 _120592 _120607 x op t f).
Proof. exact (@lem5758233 _120592 _120607 x op t f (@lem5758248 _120592 _120607 s op f x t h1 h2)). Qed.
Lemma lem5758251 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term835 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5758252 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term836 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5758251 _2963 g t e g' t' e'). Qed.
Lemma lem5758253 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term837 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5758252 _2963 g t e g' t'). Qed.
Lemma lem5758254 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term838 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5758253 _2963 g t e g'). Qed.
Lemma lem5758255 {_120607 : Type'} (g : Prop) (t : _120607) (e : _120607) : term838 _120607 g t e.
Proof. exact (@lem5758254 _120607 g t e). Qed.
Lemma lem5758256 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term862 _120592 _120607 x op t f.
Proof. exact (@lem5758255 _120607 (@IN _120592 x t) (@iterate _120607 _120592 op t f) (term863 _120592 _120607 x op t f)). Qed.
Lemma lem5758257 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) : term864 _120592 _120607 x op t f g'.
Proof. exact (@lem5758256 _120592 _120607 x op t f g'). Qed.
Lemma lem5758258 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) : (term864 _120592 _120607 x op t f g') = (term865 _120592 _120607 x op t f g').
Proof. exact (eq_refl (term864 _120592 _120607 x op t f g')). Qed.
Lemma lem5758259 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) : term865 _120592 _120607 x op t f g'.
Proof. exact (EQ_MP (@lem5758258 _120592 _120607 x op t f g') (@lem5758257 _120592 _120607 x op t f g')). Qed.
Lemma lem5758260 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) (t' : _120607) : term866 _120592 _120607 x op t f g' t'.
Proof. exact (@lem5758259 _120592 _120607 x op t f g' t'). Qed.
Lemma lem5758261 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) (t' : _120607) : (term866 _120592 _120607 x op t f g' t') = (term867 _120592 _120607 x op t f g' t').
Proof. exact (eq_refl (term866 _120592 _120607 x op t f g' t')). Qed.
Lemma lem5758262 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) (t' : _120607) : term867 _120592 _120607 x op t f g' t'.
Proof. exact (EQ_MP (@lem5758261 _120592 _120607 x op t f g' t') (@lem5758260 _120592 _120607 x op t f g' t')). Qed.
Lemma lem5758263 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) (t' : _120607) (e' : _120607) : term868 _120592 _120607 x op t f g' t' e'.
Proof. exact (@lem5758262 _120592 _120607 x op t f g' t' e'). Qed.
Lemma lem5758264 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) (t' : _120607) (e' : _120607) : (term868 _120592 _120607 x op t f g' t' e') = (term869 _120592 _120607 x op t f g' t' e').
Proof. exact (eq_refl (term868 _120592 _120607 x op t f g' t' e')). Qed.
Lemma lem5758265 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (g' : Prop) (t' : _120607) (e' : _120607) : term869 _120592 _120607 x op t f g' t' e'.
Proof. exact (EQ_MP (@lem5758264 _120592 _120607 x op t f g' t' e') (@lem5758263 _120592 _120607 x op t f g' t' e')). Qed.
Lemma lem5758267 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : (@IN _120592 x t) = False.
Proof. exact (@lem5758075 _120592 x t (@lem5758074 _120592 _120607 s op f x t h1)). Qed.
Lemma lem5758268 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (t' : _120607) (e' : _120607) : term870 _120592 _120607 x op t f t' e'.
Proof. exact (@lem5758265 _120592 _120607 x op t f False t' e'). Qed.
Lemma lem5758269 {_120592 _120607 : Type'} (t' : _120607) (e' : _120607) (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : term871 _120592 _120607 x op t f t' e'.
Proof. exact (@lem5758268 _120592 _120607 x op t f t' e' (@lem5758267 _120592 _120607 s op f x t h1)). Qed.
Lemma lem5758273 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op t f) = (@iterate _120607 _120592 op t f).
Proof. exact (eq_refl (@iterate _120607 _120592 op t f)). Qed.
Lemma lem5758274 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term872 _120592 _120607 op t f.
Proof. exact (fun h0 : False => @lem5758273 _120592 _120607 op t f). Qed.
Lemma lem5758275 {_120592 _120607 : Type'} (e' : _120607) (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : term873 _120592 _120607 x op t f e'.
Proof. exact (@lem5758269 _120592 _120607 (@iterate _120607 _120592 op t f) e' s op f x t h1). Qed.
Lemma lem5758276 {_120592 _120607 : Type'} (e' : _120607) (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : term874 _120592 _120607 x op t f e'.
Proof. exact (@lem5758275 _120592 _120607 e' s op f x t h1 (@lem5758274 _120592 _120607 op t f)). Qed.
Lemma lem5758282 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term863 _120592 _120607 x op t f) = (term863 _120592 _120607 x op t f).
Proof. exact (eq_refl (term863 _120592 _120607 x op t f)). Qed.
Lemma lem5758283 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term875 _120592 _120607 x op t f.
Proof. exact (fun h0 : ~ False => @lem5758282 _120592 _120607 x op t f). Qed.
Lemma lem5758284 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : term876 _120592 _120607 x op t f.
Proof. exact (@lem5758276 _120592 _120607 (term863 _120592 _120607 x op t f) s op f x t h1). Qed.
Lemma lem5758285 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : (term861 _120592 _120607 x op t f) = (term877 _120592 _120607 x op t f).
Proof. exact (@lem5758284 _120592 _120607 s op f x t h1 (@lem5758283 _120592 _120607 x op t f)). Qed.
Lemma lem5758287 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5758288 {_120607 : Type'} (t1 : _120607) (t2 : _120607) : (@COND _120607 False t1 t2) = t2.
Proof. exact (@lem5758287 _120607 t1 t2). Qed.
Lemma lem5758289 {_120592 _120607 : Type'} (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term877 _120592 _120607 x op t f) = (term863 _120592 _120607 x op t f).
Proof. exact (@lem5758288 _120607 (@iterate _120607 _120592 op t f) (term863 _120592 _120607 x op t f)). Qed.
Lemma lem5758290 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : term735 _120592 _120607 s op f x t) : (term861 _120592 _120607 x op t f) = (term863 _120592 _120607 x op t f).
Proof. exact (TRANS (@lem5758285 _120592 _120607 s op f x t h1) (@lem5758289 _120592 _120607 x op t f)). Qed.
Lemma lem5758291 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @monoidal _120607 op) (h2 : term735 _120592 _120607 s op f x t) : (term860 _120592 _120607 op x t f) = (term863 _120592 _120607 x op t f).
Proof. exact (TRANS (@lem5758249 _120592 _120607 s op f x t h1 h2) (@lem5758290 _120592 _120607 s op f x t h2)). Qed.
Lemma lem5758292 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term803 _120592 _120607 op s f) = (term803 _120592 _120607 op s f).
Proof. exact (eq_refl (term803 _120592 _120607 op s f)). Qed.
Lemma lem5758293 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @monoidal _120607 op) (h2 : term735 _120592 _120607 s op f x t) : (term819 _120592 _120607 s op x t f) = (term878 _120592 _120607 s x op t f).
Proof. exact (MK_COMB (@lem5758292 _120592 _120607 op s f) (@lem5758291 _120592 _120607 s op f x t h1 h2)). Qed.
Lemma lem5758294 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) (h3 : term13 _120592 x s t) (h4 : term735 _120592 _120607 s op f x t) : ((term818 _120592 _120607 op s x t f) = (term819 _120592 _120607 s op x t f)) = ((term853 _120592 _120607 x s op t f) = (term878 _120592 _120607 s x op t f)).
Proof. exact (MK_COMB (@lem5758229 _120592 _120607 s op f x t h1 h2 h3 h4) (@lem5758293 _120592 _120607 s op f x t h2 h4)). Qed.
Lemma lem5758297 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) (h3 : term735 _120592 _120607 s op f x t) : term879 _120592 _120607 s x op t f.
Proof. exact (fun h0 : term13 _120592 x s t => @lem5758294 _120592 _120607 s op f x t h1 h2 h0 h3). Qed.
Lemma lem5758298 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term880 _120592 _120607 s x op t f.
Proof. exact (@lem5758104 _120592 _120607 op f x s t ((term853 _120592 _120607 x s op t f) = (term878 _120592 _120607 s x op t f))). Qed.
Lemma lem5758299 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) (h3 : term735 _120592 _120607 s op f x t) : (term739 _120592 _120607 s op x t f) = (term881 _120592 _120607 s x op t f).
Proof. exact (@lem5758298 _120592 _120607 s x op t f (@lem5758297 _120592 _120607 s op f x t h1 h2 h3)). Qed.
Lemma lem5758335 {_120592 _120607 : Type'} (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) : term882 _120592 _120607 s x op t f.
Proof. exact (fun h0 : term735 _120592 _120607 s op f x t => @lem5758299 _120592 _120607 s op f x t h1 h2 h0). Qed.
Lemma lem5758336 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term883 _120592 _120607 s x op t f.
Proof. exact (@lem5758068 _120592 _120607 s op f x t (term881 _120592 _120607 s x op t f)). Qed.
Lemma lem5758337 {_120592 _120607 : Type'} (x : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) : (term741 _120592 _120607 s op x t f) = (term884 _120592 _120607 s x op t f).
Proof. exact (@lem5758336 _120592 _120607 s x op t f (@lem5758335 _120592 _120607 x t f s op h1 h2)). Qed.
Lemma lem5758506 {_120592 _120607 : Type'} (x : _120592) (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) : (term743 _120592 _120607 s op x f) = (term885 _120592 _120607 s x op f).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem5758337 _120592 _120607 x t f s op h1 h2)). Qed.
Lemma lem5758675 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5758676 {_120592 _120607 : Type'} (x : _120592) (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) : (term745 _120592 _120607 s op x f) = (term886 _120592 _120607 s x op f).
Proof. exact (MK_COMB (@lem5758675 _120592) (@lem5758506 _120592 _120607 x f s op h1 h2)). Qed.
Lemma lem5758849 {_120592 _120607 : Type'} (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) : (term747 _120592 _120607 s op f) = (term887 _120592 _120607 s op f).
Proof. exact (fun_ext (fun x : _120592 => @lem5758676 _120592 _120607 x f s op h1 h2)). Qed.
Lemma lem5759022 {_120592 : Type'} : (@all _120592) = (@all _120592).
Proof. exact (eq_refl (@all _120592)). Qed.
Lemma lem5759023 {_120592 _120607 : Type'} (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) : (term749 _120592 _120607 s op f) = (term888 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759022 _120592) (@lem5758849 _120592 _120607 f s op h1 h2)). Qed.
Lemma lem5759200 {_120592 _120607 : Type'} (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) : (term751 _120592 _120607 s op f) = (term889 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5757986 _120592 _120607 s f op h2) (@lem5759023 _120592 _120607 f s op h1 h2)). Qed.
Lemma lem5759406 {_120592 _120607 : Type'} (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) : (term889 _120592 _120607 s op f) = (term751 _120592 _120607 s op f).
Proof. exact (SYM (@lem5759200 _120592 _120607 f s op h1 h2)). Qed.
Lemma lem5759408 (p : Prop) : p = (term64 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5759409 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term889 _120592 _120607 s op f) = (term890 _120592 _120607 s op f).
Proof. exact (@lem5759408 (term889 _120592 _120607 s op f)). Qed.
Lemma lem5759410 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term890 _120592 _120607 s op f) = (term889 _120592 _120607 s op f).
Proof. exact (SYM (@lem5759409 _120592 _120607 s op f)). Qed.
Lemma lem5759411 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term891 _120592 _120607 s op f) : term891 _120592 _120607 s op f.
Proof. exact (h1). Qed.
Lemma lem5759412 {_120607 : Type'} : term892 _120607.
Proof. exact (@lem5712802 _120607). Qed.
Lemma lem5759417 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term893 _120592 _120607 s op f) : term893 _120592 _120607 s op f.
Proof. exact (h1). Qed.
Lemma lem5759418 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : term894 _120592 _120607 s op f.
Proof. exact (fun h0 : term893 _120592 _120607 s op f => @lem5759417 _120592 _120607 s op f h0). Qed.
Lemma lem5759419 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term894 _120592 _120607 s op f) : term894 _120592 _120607 s op f.
Proof. exact (h1). Qed.
Lemma lem5759420 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term893 _120592 _120607 s op f) : term893 _120592 _120607 s op f.
Proof. exact (h1). Qed.
Lemma lem5759421 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term893 _120592 _120607 s op f) (h2 : term894 _120592 _120607 s op f) : term893 _120592 _120607 s op f.
Proof. exact (@lem5759419 _120592 _120607 s op f h2 (@lem5759420 _120592 _120607 s op f h1)). Qed.
Lemma lem5759422 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term893 _120592 _120607 s op f) : term895 _120592 _120607 s op f.
Proof. exact (fun h0 : term894 _120592 _120607 s op f => @lem5759421 _120592 _120607 s op f h1 h0). Qed.
Lemma lem5759423 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term894 _120592 _120607 s op f) : term894 _120592 _120607 s op f.
Proof. exact (h1). Qed.
Lemma lem5759424 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term893 _120592 _120607 s op f) (h2 : term894 _120592 _120607 s op f) : term893 _120592 _120607 s op f.
Proof. exact (@lem5759422 _120592 _120607 s op f h1 (@lem5759423 _120592 _120607 s op f h2)). Qed.
Lemma lem5759425 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term894 _120592 _120607 s op f) : term894 _120592 _120607 s op f.
Proof. exact (fun h0 : term893 _120592 _120607 s op f => @lem5759424 _120592 _120607 s op f h0 h1). Qed.
Lemma lem5759426 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : term896 _120592 _120607 s op f.
Proof. exact (fun h0 : term894 _120592 _120607 s op f => @lem5759425 _120592 _120607 s op f h0). Qed.
Lemma lem5759429 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : term894 _120592 _120607 s op f.
Proof. exact (@lem5759426 _120592 _120607 s op f (@lem5759418 _120592 _120607 s op f)). Qed.
Lemma lem5759430 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : term894 _120592 _120607 s op f.
Proof. exact (@lem5759429 _120592 _120607 s op f). Qed.
Lemma lem5759474 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5759475 {_120607 : Type'} : (term897 _120607) = (term898 _120607).
Proof. exact (@lem5759474 (term892 _120607)). Qed.
Lemma lem5759508 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term899 _120592 _120607 s op f) = (term899 _120592 _120607 s op f).
Proof. exact (eq_refl (term899 _120592 _120607 s op f)). Qed.
Lemma lem5759509 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term900 _120592 _120607 s op f) = (term901 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759508 _120592 _120607 s op f) (@lem5759475 _120607)). Qed.
Lemma lem5759512 {_120592 : Type'} (s : _120592 -> Prop) : (term703 _120592 s) = (term703 _120592 s).
Proof. exact (eq_refl (term703 _120592 s)). Qed.
Lemma lem5759513 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term902 _120592 _120607 s op f) = (term903 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759512 _120592 s) (@lem5759509 _120592 _120607 s op f)). Qed.
Lemma lem5759516 {_120607 : Type'} (op : type1400 _120607) : (term904 _120607 op) = (term904 _120607 op).
Proof. exact (eq_refl (term904 _120607 op)). Qed.
Lemma lem5759517 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term893 _120592 _120607 s op f) = (term905 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759516 _120607 op) (@lem5759513 _120592 _120607 s op f)). Qed.
Lemma lem5759520 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) : (term906 _120592 _120607 op f) = (term907 _120592 _120607 op f).
Proof. exact (fun_ext (fun s : _120592 -> Prop => @lem5759517 _120592 _120607 s op f)). Qed.
Lemma lem5759521 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5759522 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) : (term908 _120592 _120607 op f) = (term909 _120592 _120607 op f).
Proof. exact (MK_COMB (@lem5759521 _120592) (@lem5759520 _120592 _120607 op f)). Qed.
Lemma lem5759527 {_120592 _120607 : Type'} (f : _120592 -> _120607) : (term910 _120592 _120607 f) = (term911 _120592 _120607 f).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5759522 _120592 _120607 op f)). Qed.
Lemma lem5759528 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5759529 {_120592 _120607 : Type'} (f : _120592 -> _120607) : (term912 _120592 _120607 f) = (term913 _120592 _120607 f).
Proof. exact (MK_COMB (@lem5759528 _120607) (@lem5759527 _120592 _120607 f)). Qed.
Lemma lem5759534 {_120592 _120607 : Type'} : (term914 _120592 _120607) = (term915 _120592 _120607).
Proof. exact (fun_ext (fun f : _120592 -> _120607 => @lem5759529 _120592 _120607 f)). Qed.
Lemma lem5759535 {_120592 _120607 : Type'} : (@all (_120592 -> _120607)) = (@all (_120592 -> _120607)).
Proof. exact (eq_refl (@all (_120592 -> _120607))). Qed.
Lemma lem5759544 {_120592 _120607 : Type'} : (term916 _120592 _120607) = (term917 _120592 _120607).
Proof. exact (MK_COMB (@lem5759535 _120592 _120607) (@lem5759534 _120592 _120607)). Qed.
Lemma lem5759545 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term918 _120607 op x) = x) = ((term918 _120607 op x) = x).
Proof. exact (eq_refl ((term918 _120607 op x) = x)). Qed.
Lemma lem5759546 {_120607 : Type'} (op : type1400 _120607) : (term919 _120607 op) = (term919 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5759545 _120607 op x)). Qed.
Lemma lem5759547 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5759548 {_120607 : Type'} (op : type1400 _120607) : (term920 _120607 op) = (term920 _120607 op).
Proof. exact (MK_COMB (@lem5759547 _120607) (@lem5759546 _120607 op)). Qed.
Lemma lem5759549 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : ((term921 _120607 x op y z) = (term922 _120607 op x y z)) = ((term921 _120607 x op y z) = (term922 _120607 op x y z)).
Proof. exact (eq_refl ((term921 _120607 x op y z) = (term922 _120607 op x y z))). Qed.
Lemma lem5759550 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term923 _120607 op x y) = (term923 _120607 op x y).
Proof. exact (fun_ext (fun z : _120607 => @lem5759549 _120607 op x y z)). Qed.
Lemma lem5759551 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5759552 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term924 _120607 op x y) = (term924 _120607 op x y).
Proof. exact (MK_COMB (@lem5759551 _120607) (@lem5759550 _120607 op x y)). Qed.
Lemma lem5759553 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term925 _120607 op x) = (term925 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5759552 _120607 op x y)). Qed.
Lemma lem5759554 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5759555 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term926 _120607 op x) = (term926 _120607 op x).
Proof. exact (MK_COMB (@lem5759554 _120607) (@lem5759553 _120607 op x)). Qed.
Lemma lem5759556 {_120607 : Type'} (op : type1400 _120607) : (term927 _120607 op) = (term927 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5759555 _120607 op x)). Qed.
Lemma lem5759557 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5759558 {_120607 : Type'} (op : type1400 _120607) : (term928 _120607 op) = (term928 _120607 op).
Proof. exact (MK_COMB (@lem5759557 _120607) (@lem5759556 _120607 op)). Qed.
Lemma lem5759559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5759560 {_120607 : Type'} (op : type1400 _120607) : (term929 _120607 op) = (term929 _120607 op).
Proof. exact (MK_COMB (@lem5759559) (@lem5759558 _120607 op)). Qed.
Lemma lem5759561 {_120607 : Type'} (op : type1400 _120607) : (term930 _120607 op) = (term930 _120607 op).
Proof. exact (MK_COMB (@lem5759560 _120607 op) (@lem5759548 _120607 op)). Qed.
Lemma lem5759562 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem5759563 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term931 _120607 op x) = (term931 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5759562 _120607 op y x)). Qed.
Lemma lem5759564 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5759565 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term932 _120607 op x) = (term932 _120607 op x).
Proof. exact (MK_COMB (@lem5759564 _120607) (@lem5759563 _120607 op x)). Qed.
Lemma lem5759566 {_120607 : Type'} (op : type1400 _120607) : (term933 _120607 op) = (term933 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5759565 _120607 op x)). Qed.
Lemma lem5759567 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5759568 {_120607 : Type'} (op : type1400 _120607) : (term934 _120607 op) = (term934 _120607 op).
Proof. exact (MK_COMB (@lem5759567 _120607) (@lem5759566 _120607 op)). Qed.
Lemma lem5759569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5759570 {_120607 : Type'} (op : type1400 _120607) : (term935 _120607 op) = (term935 _120607 op).
Proof. exact (MK_COMB (@lem5759569) (@lem5759568 _120607 op)). Qed.
Lemma lem5759571 {_120607 : Type'} (op : type1400 _120607) : (term936 _120607 op) = (term936 _120607 op).
Proof. exact (MK_COMB (@lem5759570 _120607 op) (@lem5759561 _120607 op)). Qed.
Lemma lem5759574 {_120607 : Type'} (op : type1400 _120607) : (term937 _120607 op) = (term937 _120607 op).
Proof. exact (eq_refl (term937 _120607 op)). Qed.
Lemma lem5759575 {_120607 : Type'} (op : type1400 _120607) : ((@monoidal _120607 op) = (term936 _120607 op)) = ((@monoidal _120607 op) = (term936 _120607 op)).
Proof. exact (MK_COMB (@lem5759574 _120607 op) (@lem5759571 _120607 op)). Qed.
Lemma lem5759576 {_120607 : Type'} : (term938 _120607) = (term938 _120607).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5759575 _120607 op)). Qed.
Lemma lem5759577 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5759578 {_120607 : Type'} : (term892 _120607) = (term892 _120607).
Proof. exact (MK_COMB (@lem5759577 _120607) (@lem5759576 _120607)). Qed.
Lemma lem5759579 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5759580 {_120607 : Type'} : (term898 _120607) = (term898 _120607).
Proof. exact (MK_COMB (@lem5759579) (@lem5759578 _120607)). Qed.
Lemma lem5759609 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term884 _120592 _120607 s x op t f) = (term884 _120592 _120607 s x op t f).
Proof. exact (eq_refl (term884 _120592 _120607 s x op t f)). Qed.
Lemma lem5759610 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term885 _120592 _120607 s x op f) = (term885 _120592 _120607 s x op f).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem5759609 _120592 _120607 s x op t f)). Qed.
Lemma lem5759611 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5759612 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term886 _120592 _120607 s x op f) = (term886 _120592 _120607 s x op f).
Proof. exact (MK_COMB (@lem5759611 _120592) (@lem5759610 _120592 _120607 s x op f)). Qed.
Lemma lem5759613 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term887 _120592 _120607 s op f) = (term887 _120592 _120607 s op f).
Proof. exact (fun_ext (fun x : _120592 => @lem5759612 _120592 _120607 s x op f)). Qed.
Lemma lem5759614 {_120592 : Type'} : (@all _120592) = (@all _120592).
Proof. exact (eq_refl (@all _120592)). Qed.
Lemma lem5759615 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term888 _120592 _120607 s op f) = (term888 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759614 _120592) (@lem5759613 _120592 _120607 s op f)). Qed.
Lemma lem5759622 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term808 _120592 _120607 s f op) = (term808 _120592 _120607 s f op).
Proof. exact (eq_refl (term808 _120592 _120607 s f op)). Qed.
Lemma lem5759623 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term889 _120592 _120607 s op f) = (term889 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759622 _120592 _120607 s f op) (@lem5759615 _120592 _120607 s op f)). Qed.
Lemma lem5759624 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5759625 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term891 _120592 _120607 s op f) = (term891 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759624) (@lem5759623 _120592 _120607 s op f)). Qed.
Lemma lem5759626 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5759627 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term899 _120592 _120607 s op f) = (term899 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759626) (@lem5759625 _120592 _120607 s op f)). Qed.
Lemma lem5759628 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term901 _120592 _120607 s op f) = (term901 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759627 _120592 _120607 s op f) (@lem5759580 _120607)). Qed.
Lemma lem5759631 {_120592 : Type'} (s : _120592 -> Prop) : (term703 _120592 s) = (term703 _120592 s).
Proof. exact (eq_refl (term703 _120592 s)). Qed.
Lemma lem5759632 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term903 _120592 _120607 s op f) = (term903 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759631 _120592 s) (@lem5759628 _120592 _120607 s op f)). Qed.
Lemma lem5759635 {_120607 : Type'} (op : type1400 _120607) : (term904 _120607 op) = (term904 _120607 op).
Proof. exact (eq_refl (term904 _120607 op)). Qed.
Lemma lem5759636 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term905 _120592 _120607 s op f) = (term905 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759635 _120607 op) (@lem5759632 _120592 _120607 s op f)). Qed.
Lemma lem5759637 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) : (term907 _120592 _120607 op f) = (term907 _120592 _120607 op f).
Proof. exact (fun_ext (fun s : _120592 -> Prop => @lem5759636 _120592 _120607 s op f)). Qed.
Lemma lem5759638 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem5759639 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) : (term909 _120592 _120607 op f) = (term909 _120592 _120607 op f).
Proof. exact (MK_COMB (@lem5759638 _120592) (@lem5759637 _120592 _120607 op f)). Qed.
Lemma lem5759640 {_120592 _120607 : Type'} (f : _120592 -> _120607) : (term911 _120592 _120607 f) = (term911 _120592 _120607 f).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5759639 _120592 _120607 op f)). Qed.
Lemma lem5759641 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5759642 {_120592 _120607 : Type'} (f : _120592 -> _120607) : (term913 _120592 _120607 f) = (term913 _120592 _120607 f).
Proof. exact (MK_COMB (@lem5759641 _120607) (@lem5759640 _120592 _120607 f)). Qed.
Lemma lem5759643 {_120592 _120607 : Type'} : (term915 _120592 _120607) = (term915 _120592 _120607).
Proof. exact (fun_ext (fun f : _120592 -> _120607 => @lem5759642 _120592 _120607 f)). Qed.
Lemma lem5759644 {_120592 _120607 : Type'} : (@all (_120592 -> _120607)) = (@all (_120592 -> _120607)).
Proof. exact (eq_refl (@all (_120592 -> _120607))). Qed.
Lemma lem5759645 {_120592 _120607 : Type'} : (term917 _120592 _120607) = (term917 _120592 _120607).
Proof. exact (MK_COMB (@lem5759644 _120592 _120607) (@lem5759643 _120592 _120607)). Qed.
Lemma lem5759746 {_120592 _120607 : Type'} : (term916 _120592 _120607) = (term917 _120592 _120607).
Proof. exact (TRANS (@lem5759544 _120592 _120607) (@lem5759645 _120592 _120607)). Qed.
Lemma lem5759747 {_120592 _120607 : Type'} : (term917 _120592 _120607) = (term916 _120592 _120607).
Proof. exact (SYM (@lem5759746 _120592 _120607)). Qed.
Lemma lem5759750 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term891 _120592 _120607 s op f) : term891 _120592 _120607 s op f.
Proof. exact (h1). Qed.
Lemma lem5759751 {_120607 : Type'} (h1 : term892 _120607) : term892 _120607.
Proof. exact (h1). Qed.
Lemma lem5759757 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @monoidal _120607 op.
Proof. exact (h1). Qed.
Lemma lem5759770 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term939 _120592 _120607 s f op) = (term940 _120592 _120607 s f op).
Proof. exact (@lem17362 (@DISJOINT _120592 s (@EMPTY _120592)) ((@iterate _120607 _120592 op s f) = (term804 _120592 _120607 s f op))). Qed.
Lemma lem5759777 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term730 _120592 _120607 s op t f) = (term941 _120592 _120607 s op t f).
Proof. exact (@lem17265 (@DISJOINT _120592 s t) ((term699 _120592 _120607 op s t f) = (term700 _120592 _120607 s op t f))). Qed.
Lemma lem5759782 {_120592 : Type'} (x : _120592) (t : _120592 -> Prop) : (term733 _120592 x t) = (term733 _120592 x t).
Proof. exact (eq_refl (term733 _120592 x t)). Qed.
Lemma lem5759783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5759784 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term732 _120592 _120607 s op t f) = (term942 _120592 _120607 s op t f).
Proof. exact (MK_COMB (@lem5759783) (@lem5759777 _120592 _120607 s op t f)). Qed.
Lemma lem5759785 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) : (term735 _120592 _120607 s op f x t) = (term943 _120592 _120607 s op f x t).
Proof. exact (MK_COMB (@lem5759784 _120592 _120607 s op t f) (@lem5759782 _120592 x t)). Qed.
Lemma lem5759796 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term944 _120592 _120607 s x op t f) = (term945 _120592 _120607 s x op t f).
Proof. exact (@lem17362 (term13 _120592 x s t) ((term853 _120592 _120607 x s op t f) = (term878 _120592 _120607 s x op t f))). Qed.
Lemma lem5759797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5759798 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x : _120592) (t : _120592 -> Prop) : (term946 _120592 _120607 s op f x t) = (term947 _120592 _120607 s op f x t).
Proof. exact (MK_COMB (@lem5759797) (@lem5759785 _120592 _120607 s op f x t)). Qed.
Lemma lem5759799 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term948 _120592 _120607 s x op t f) = (term949 _120592 _120607 s x op t f).
Proof. exact (MK_COMB (@lem5759798 _120592 _120607 s op f x t) (@lem5759796 _120592 _120607 s x op t f)). Qed.
Lemma lem5759800 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term950 _120592 _120607 s x op t f) = (term948 _120592 _120607 s x op t f).
Proof. exact (@lem17362 (term735 _120592 _120607 s op f x t) (term881 _120592 _120607 s x op t f)). Qed.
Lemma lem5759801 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term950 _120592 _120607 s x op t f) = (term949 _120592 _120607 s x op t f).
Proof. exact (TRANS (@lem5759800 _120592 _120607 s x op t f) (@lem5759799 _120592 _120607 s x op t f)). Qed.
Lemma lem5759802 {_120592 : Type'} (P : type686 _120592) : (term188 _120592 P) = (term189 _120592 P).
Proof. exact (@lem18392 (_120592 -> Prop) P). Qed.
Lemma lem5759803 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term951 _120592 _120607 s x op f) = (term952 _120592 _120607 s x op f).
Proof. exact (@lem5759802 _120592 (term885 _120592 _120607 s x op f)). Qed.
Lemma lem5759804 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term953 _120592 _120607 s x op f t) = (term884 _120592 _120607 s x op t f).
Proof. exact (eq_refl (term953 _120592 _120607 s x op f t)). Qed.
Lemma lem5759805 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5759806 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term954 _120592 _120607 s x op f t) = (term950 _120592 _120607 s x op t f).
Proof. exact (MK_COMB (@lem5759805) (@lem5759804 _120592 _120607 s x op t f)). Qed.
Lemma lem5759807 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term954 _120592 _120607 s x op f t) = (term949 _120592 _120607 s x op t f).
Proof. exact (TRANS (@lem5759806 _120592 _120607 s x op t f) (@lem5759801 _120592 _120607 s x op t f)). Qed.
Lemma lem5759808 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term955 _120592 _120607 s x op f) = (term956 _120592 _120607 s x op f).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem5759807 _120592 _120607 s x op t f)). Qed.
Lemma lem5759809 {_120592 : Type'} : (@ex (_120592 -> Prop)) = (@ex (_120592 -> Prop)).
Proof. exact (eq_refl (@ex (_120592 -> Prop))). Qed.
Lemma lem5759810 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term952 _120592 _120607 s x op f) = (term957 _120592 _120607 s x op f).
Proof. exact (MK_COMB (@lem5759809 _120592) (@lem5759808 _120592 _120607 s x op f)). Qed.
Lemma lem5759811 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term951 _120592 _120607 s x op f) = (term957 _120592 _120607 s x op f).
Proof. exact (TRANS (@lem5759803 _120592 _120607 s x op f) (@lem5759810 _120592 _120607 s x op f)). Qed.
Lemma lem5759812 {_120592 : Type'} (P : _120592 -> Prop) : (term173 _120592 P) = (term174 _120592 P).
Proof. exact (@lem18392 _120592 P). Qed.
Lemma lem5759813 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term958 _120592 _120607 s op f) = (term959 _120592 _120607 s op f).
Proof. exact (@lem5759812 _120592 (term887 _120592 _120607 s op f)). Qed.
Lemma lem5759814 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term960 _120592 _120607 s op f x) = (term886 _120592 _120607 s x op f).
Proof. exact (eq_refl (term960 _120592 _120607 s op f x)). Qed.
Lemma lem5759815 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5759816 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term961 _120592 _120607 s op f x) = (term951 _120592 _120607 s x op f).
Proof. exact (MK_COMB (@lem5759815) (@lem5759814 _120592 _120607 s x op f)). Qed.
Lemma lem5759817 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term961 _120592 _120607 s op f x) = (term957 _120592 _120607 s x op f).
Proof. exact (TRANS (@lem5759816 _120592 _120607 s x op f) (@lem5759811 _120592 _120607 s x op f)). Qed.
Lemma lem5759818 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term962 _120592 _120607 s op f) = (term963 _120592 _120607 s op f).
Proof. exact (fun_ext (fun x : _120592 => @lem5759817 _120592 _120607 s x op f)). Qed.
Lemma lem5759819 {_120592 : Type'} : (@ex _120592) = (@ex _120592).
Proof. exact (eq_refl (@ex _120592)). Qed.
Lemma lem5759820 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term959 _120592 _120607 s op f) = (term964 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759819 _120592) (@lem5759818 _120592 _120607 s op f)). Qed.
Lemma lem5759821 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term958 _120592 _120607 s op f) = (term964 _120592 _120607 s op f).
Proof. exact (TRANS (@lem5759813 _120592 _120607 s op f) (@lem5759820 _120592 _120607 s op f)). Qed.
Lemma lem5759822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5759823 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term965 _120592 _120607 s f op) = (term966 _120592 _120607 s f op).
Proof. exact (MK_COMB (@lem5759822) (@lem5759770 _120592 _120607 s f op)). Qed.
Lemma lem5759824 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term967 _120592 _120607 s op f) = (term968 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759823 _120592 _120607 s f op) (@lem5759821 _120592 _120607 s op f)). Qed.
Lemma lem5759825 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term891 _120592 _120607 s op f) = (term967 _120592 _120607 s op f).
Proof. exact (@lem17045 (term807 _120592 _120607 s f op) (term888 _120592 _120607 s op f)). Qed.
Lemma lem5759826 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term891 _120592 _120607 s op f) = (term968 _120592 _120607 s op f).
Proof. exact (TRANS (@lem5759825 _120592 _120607 s op f) (@lem5759824 _120592 _120607 s op f)). Qed.
Lemma lem5759881 {A : Type'} (P : Prop) (Q : A -> Prop) : (term431 A P Q) = (term432 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5759882 {_120592 : Type'} (P : Prop) (Q : _120592 -> Prop) : (term431 _120592 P Q) = (term432 _120592 P Q).
Proof. exact (@lem5759881 _120592 P Q). Qed.
Lemma lem5759883 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term969 _120592 _120607 s op f) = (term970 _120592 _120607 s op f).
Proof. exact (@lem5759882 _120592 (term940 _120592 _120607 s f op) (term963 _120592 _120607 s op f)). Qed.
Lemma lem5759884 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term971 _120592 _120607 s op f x) = (term957 _120592 _120607 s x op f).
Proof. exact (eq_refl (term971 _120592 _120607 s op f x)). Qed.
Lemma lem5759885 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term972 _120592 _120607 s op f) = (term963 _120592 _120607 s op f).
Proof. exact (fun_ext (fun x : _120592 => @lem5759884 _120592 _120607 s x op f)). Qed.
Lemma lem5759886 {_120592 : Type'} : (@ex _120592) = (@ex _120592).
Proof. exact (eq_refl (@ex _120592)). Qed.
Lemma lem5759887 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term973 _120592 _120607 s op f) = (term964 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759886 _120592) (@lem5759885 _120592 _120607 s op f)). Qed.
Lemma lem5759888 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term966 _120592 _120607 s f op) = (term966 _120592 _120607 s f op).
Proof. exact (eq_refl (term966 _120592 _120607 s f op)). Qed.
Lemma lem5759889 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term969 _120592 _120607 s op f) = (term968 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759888 _120592 _120607 s f op) (@lem5759887 _120592 _120607 s op f)). Qed.
Lemma lem5759890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5759891 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term974 _120592 _120607 s op f) = (term975 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759890) (@lem5759889 _120592 _120607 s op f)). Qed.
Lemma lem5759892 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term971 _120592 _120607 s op f x) = (term957 _120592 _120607 s x op f).
Proof. exact (eq_refl (term971 _120592 _120607 s op f x)). Qed.
Lemma lem5759893 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term966 _120592 _120607 s f op) = (term966 _120592 _120607 s f op).
Proof. exact (eq_refl (term966 _120592 _120607 s f op)). Qed.
Lemma lem5759894 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term976 _120592 _120607 s op f x) = (term977 _120592 _120607 s x op f).
Proof. exact (MK_COMB (@lem5759893 _120592 _120607 s f op) (@lem5759892 _120592 _120607 s x op f)). Qed.
Lemma lem5759895 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term978 _120592 _120607 s op f) = (term979 _120592 _120607 s op f).
Proof. exact (fun_ext (fun x : _120592 => @lem5759894 _120592 _120607 s x op f)). Qed.
Lemma lem5759896 {_120592 : Type'} : (@ex _120592) = (@ex _120592).
Proof. exact (eq_refl (@ex _120592)). Qed.
Lemma lem5759897 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term970 _120592 _120607 s op f) = (term980 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759896 _120592) (@lem5759895 _120592 _120607 s op f)). Qed.
Lemma lem5759898 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : ((term969 _120592 _120607 s op f) = (term970 _120592 _120607 s op f)) = ((term968 _120592 _120607 s op f) = (term980 _120592 _120607 s op f)).
Proof. exact (MK_COMB (@lem5759891 _120592 _120607 s op f) (@lem5759897 _120592 _120607 s op f)). Qed.
Lemma lem5759899 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term968 _120592 _120607 s op f) = (term980 _120592 _120607 s op f).
Proof. exact (EQ_MP (@lem5759898 _120592 _120607 s op f) (@lem5759883 _120592 _120607 s op f)). Qed.
Lemma lem5759901 {A : Type'} (P : Prop) (Q : A -> Prop) : (term431 A P Q) = (term432 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5759902 {_120592 : Type'} (P : Prop) (Q : type686 _120592) : (term981 _120592 P Q) = (term982 _120592 P Q).
Proof. exact (@lem5759901 (_120592 -> Prop) P Q). Qed.
Lemma lem5759903 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term983 _120592 _120607 s x op f) = (term984 _120592 _120607 s x op f).
Proof. exact (@lem5759902 _120592 (term940 _120592 _120607 s f op) (term956 _120592 _120607 s x op f)). Qed.
Lemma lem5759904 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term985 _120592 _120607 s x op f t) = (term949 _120592 _120607 s x op t f).
Proof. exact (eq_refl (term985 _120592 _120607 s x op f t)). Qed.
Lemma lem5759905 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term986 _120592 _120607 s x op f) = (term956 _120592 _120607 s x op f).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem5759904 _120592 _120607 s x op t f)). Qed.
Lemma lem5759906 {_120592 : Type'} : (@ex (_120592 -> Prop)) = (@ex (_120592 -> Prop)).
Proof. exact (eq_refl (@ex (_120592 -> Prop))). Qed.
Lemma lem5759907 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term987 _120592 _120607 s x op f) = (term957 _120592 _120607 s x op f).
Proof. exact (MK_COMB (@lem5759906 _120592) (@lem5759905 _120592 _120607 s x op f)). Qed.
Lemma lem5759908 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term966 _120592 _120607 s f op) = (term966 _120592 _120607 s f op).
Proof. exact (eq_refl (term966 _120592 _120607 s f op)). Qed.
Lemma lem5759909 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term983 _120592 _120607 s x op f) = (term977 _120592 _120607 s x op f).
Proof. exact (MK_COMB (@lem5759908 _120592 _120607 s f op) (@lem5759907 _120592 _120607 s x op f)). Qed.
Lemma lem5759910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5759911 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term988 _120592 _120607 s x op f) = (term989 _120592 _120607 s x op f).
Proof. exact (MK_COMB (@lem5759910) (@lem5759909 _120592 _120607 s x op f)). Qed.
Lemma lem5759912 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term985 _120592 _120607 s x op f t) = (term949 _120592 _120607 s x op t f).
Proof. exact (eq_refl (term985 _120592 _120607 s x op f t)). Qed.
Lemma lem5759913 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term966 _120592 _120607 s f op) = (term966 _120592 _120607 s f op).
Proof. exact (eq_refl (term966 _120592 _120607 s f op)). Qed.
Lemma lem5759914 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term990 _120592 _120607 s x op f t) = (term991 _120592 _120607 s x op t f).
Proof. exact (MK_COMB (@lem5759913 _120592 _120607 s f op) (@lem5759912 _120592 _120607 s x op t f)). Qed.
Lemma lem5759915 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term992 _120592 _120607 s x op f) = (term993 _120592 _120607 s x op f).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem5759914 _120592 _120607 s x op t f)). Qed.
Lemma lem5759916 {_120592 : Type'} : (@ex (_120592 -> Prop)) = (@ex (_120592 -> Prop)).
Proof. exact (eq_refl (@ex (_120592 -> Prop))). Qed.
Lemma lem5759917 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term984 _120592 _120607 s x op f) = (term994 _120592 _120607 s x op f).
Proof. exact (MK_COMB (@lem5759916 _120592) (@lem5759915 _120592 _120607 s x op f)). Qed.
Lemma lem5759918 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : ((term983 _120592 _120607 s x op f) = (term984 _120592 _120607 s x op f)) = ((term977 _120592 _120607 s x op f) = (term994 _120592 _120607 s x op f)).
Proof. exact (MK_COMB (@lem5759911 _120592 _120607 s x op f) (@lem5759917 _120592 _120607 s x op f)). Qed.
Lemma lem5759919 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x : _120592) (op : type1400 _120607) (f : _120592 -> _120607) : (term977 _120592 _120607 s x op f) = (term994 _120592 _120607 s x op f).
Proof. exact (EQ_MP (@lem5759918 _120592 _120607 s x op f) (@lem5759903 _120592 _120607 s x op f)). Qed.
Lemma lem5759920 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term979 _120592 _120607 s op f) = (term995 _120592 _120607 s op f).
Proof. exact (fun_ext (fun x : _120592 => @lem5759919 _120592 _120607 s x op f)). Qed.
Lemma lem5759921 {_120592 : Type'} : (@ex _120592) = (@ex _120592).
Proof. exact (eq_refl (@ex _120592)). Qed.
Lemma lem5759922 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term980 _120592 _120607 s op f) = (term996 _120592 _120607 s op f).
Proof. exact (MK_COMB (@lem5759921 _120592) (@lem5759920 _120592 _120607 s op f)). Qed.
Lemma lem5759924 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term968 _120592 _120607 s op f) = (term996 _120592 _120607 s op f).
Proof. exact (TRANS (@lem5759899 _120592 _120607 s op f) (@lem5759922 _120592 _120607 s op f)). Qed.
Lemma lem5759925 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term891 _120592 _120607 s op f) = (term996 _120592 _120607 s op f).
Proof. exact (TRANS (@lem5759826 _120592 _120607 s op f) (@lem5759924 _120592 _120607 s op f)). Qed.
Lemma lem5759926 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term891 _120592 _120607 s op f) : term996 _120592 _120607 s op f.
Proof. exact (EQ_MP (@lem5759925 _120592 _120607 s op f) (@lem5759750 _120592 _120607 s op f h1)). Qed.
Lemma lem5759930 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem5759931 {_120607 : Type'} (P : _120607 -> Prop) : (term173 _120607 P) = (term174 _120607 P).
Proof. exact (@lem18392 _120607 P). Qed.
Lemma lem5759932 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term997 _120607 op x) = (term998 _120607 op x).
Proof. exact (@lem5759931 _120607 (term931 _120607 op x)). Qed.
Lemma lem5759933 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term999 _120607 op x y) = ((op x y) = (op y x)).
Proof. exact (eq_refl (term999 _120607 op x y)). Qed.
Lemma lem5759934 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5759936 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1000 _120607 op x y) = (term1001 _120607 op y x).
Proof. exact (MK_COMB (@lem5759934) (@lem5759933 _120607 op y x)). Qed.
Lemma lem5759937 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1002 _120607 op x) = (term1003 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5759936 _120607 op y x)). Qed.
Lemma lem5759938 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5759939 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term998 _120607 op x) = (term1004 _120607 op x).
Proof. exact (MK_COMB (@lem5759938 _120607) (@lem5759937 _120607 op x)). Qed.
Lemma lem5759940 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term997 _120607 op x) = (term1004 _120607 op x).
Proof. exact (TRANS (@lem5759932 _120607 op x) (@lem5759939 _120607 op x)). Qed.
Lemma lem5759941 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term931 _120607 op x) = (term931 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5759930 _120607 op y x)). Qed.
Lemma lem5759942 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5759943 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term932 _120607 op x) = (term932 _120607 op x).
Proof. exact (MK_COMB (@lem5759942 _120607) (@lem5759941 _120607 op x)). Qed.
Lemma lem5759944 {_120607 : Type'} (P : _120607 -> Prop) : (term173 _120607 P) = (term174 _120607 P).
Proof. exact (@lem18392 _120607 P). Qed.
Lemma lem5759945 {_120607 : Type'} (op : type1400 _120607) : (term1005 _120607 op) = (term1006 _120607 op).
Proof. exact (@lem5759944 _120607 (term933 _120607 op)). Qed.
Lemma lem5759946 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1007 _120607 op x) = (term932 _120607 op x).
Proof. exact (eq_refl (term1007 _120607 op x)). Qed.
Lemma lem5759947 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5759948 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1008 _120607 op x) = (term997 _120607 op x).
Proof. exact (MK_COMB (@lem5759947) (@lem5759946 _120607 op x)). Qed.
Lemma lem5759949 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1008 _120607 op x) = (term1004 _120607 op x).
Proof. exact (TRANS (@lem5759948 _120607 op x) (@lem5759940 _120607 op x)). Qed.
Lemma lem5759950 {_120607 : Type'} (op : type1400 _120607) : (term1009 _120607 op) = (term1010 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5759949 _120607 op x)). Qed.
Lemma lem5759951 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5759952 {_120607 : Type'} (op : type1400 _120607) : (term1006 _120607 op) = (term1011 _120607 op).
Proof. exact (MK_COMB (@lem5759951 _120607) (@lem5759950 _120607 op)). Qed.
Lemma lem5759953 {_120607 : Type'} (op : type1400 _120607) : (term1005 _120607 op) = (term1011 _120607 op).
Proof. exact (TRANS (@lem5759945 _120607 op) (@lem5759952 _120607 op)). Qed.
Lemma lem5759954 {_120607 : Type'} (op : type1400 _120607) : (term933 _120607 op) = (term933 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5759943 _120607 op x)). Qed.
Lemma lem5759955 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5759956 {_120607 : Type'} (op : type1400 _120607) : (term934 _120607 op) = (term934 _120607 op).
Proof. exact (MK_COMB (@lem5759955 _120607) (@lem5759954 _120607 op)). Qed.
Lemma lem5759958 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : ((term921 _120607 x op y z) = (term922 _120607 op x y z)) = ((term921 _120607 x op y z) = (term922 _120607 op x y z)).
Proof. exact (eq_refl ((term921 _120607 x op y z) = (term922 _120607 op x y z))). Qed.
Lemma lem5759959 {_120607 : Type'} (P : _120607 -> Prop) : (term173 _120607 P) = (term174 _120607 P).
Proof. exact (@lem18392 _120607 P). Qed.
Lemma lem5759960 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1012 _120607 op x y) = (term1013 _120607 op x y).
Proof. exact (@lem5759959 _120607 (term923 _120607 op x y)). Qed.
Lemma lem5759961 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term1014 _120607 op x y z) = ((term921 _120607 x op y z) = (term922 _120607 op x y z)).
Proof. exact (eq_refl (term1014 _120607 op x y z)). Qed.
Lemma lem5759962 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5759964 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term1015 _120607 op x y z) = (term1016 _120607 op x y z).
Proof. exact (MK_COMB (@lem5759962) (@lem5759961 _120607 op x y z)). Qed.
Lemma lem5759965 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1017 _120607 op x y) = (term1018 _120607 op x y).
Proof. exact (fun_ext (fun z : _120607 => @lem5759964 _120607 op x y z)). Qed.
Lemma lem5759966 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5759967 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1013 _120607 op x y) = (term1019 _120607 op x y).
Proof. exact (MK_COMB (@lem5759966 _120607) (@lem5759965 _120607 op x y)). Qed.
Lemma lem5759968 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1012 _120607 op x y) = (term1019 _120607 op x y).
Proof. exact (TRANS (@lem5759960 _120607 op x y) (@lem5759967 _120607 op x y)). Qed.
Lemma lem5759969 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term923 _120607 op x y) = (term923 _120607 op x y).
Proof. exact (fun_ext (fun z : _120607 => @lem5759958 _120607 op x y z)). Qed.
Lemma lem5759970 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5759971 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term924 _120607 op x y) = (term924 _120607 op x y).
Proof. exact (MK_COMB (@lem5759970 _120607) (@lem5759969 _120607 op x y)). Qed.
Lemma lem5759972 {_120607 : Type'} (P : _120607 -> Prop) : (term173 _120607 P) = (term174 _120607 P).
Proof. exact (@lem18392 _120607 P). Qed.
Lemma lem5759973 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1020 _120607 op x) = (term1021 _120607 op x).
Proof. exact (@lem5759972 _120607 (term925 _120607 op x)). Qed.
Lemma lem5759974 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1022 _120607 op x y) = (term924 _120607 op x y).
Proof. exact (eq_refl (term1022 _120607 op x y)). Qed.
Lemma lem5759975 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5759976 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1023 _120607 op x y) = (term1012 _120607 op x y).
Proof. exact (MK_COMB (@lem5759975) (@lem5759974 _120607 op x y)). Qed.
Lemma lem5759977 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1023 _120607 op x y) = (term1019 _120607 op x y).
Proof. exact (TRANS (@lem5759976 _120607 op x y) (@lem5759968 _120607 op x y)). Qed.
Lemma lem5759978 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1024 _120607 op x) = (term1025 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5759977 _120607 op x y)). Qed.
Lemma lem5759979 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5759980 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1021 _120607 op x) = (term1026 _120607 op x).
Proof. exact (MK_COMB (@lem5759979 _120607) (@lem5759978 _120607 op x)). Qed.
Lemma lem5759981 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1020 _120607 op x) = (term1026 _120607 op x).
Proof. exact (TRANS (@lem5759973 _120607 op x) (@lem5759980 _120607 op x)). Qed.
Lemma lem5759982 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term925 _120607 op x) = (term925 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5759971 _120607 op x y)). Qed.
Lemma lem5759983 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5759984 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term926 _120607 op x) = (term926 _120607 op x).
Proof. exact (MK_COMB (@lem5759983 _120607) (@lem5759982 _120607 op x)). Qed.
Lemma lem5759985 {_120607 : Type'} (P : _120607 -> Prop) : (term173 _120607 P) = (term174 _120607 P).
Proof. exact (@lem18392 _120607 P). Qed.
Lemma lem5759986 {_120607 : Type'} (op : type1400 _120607) : (term1027 _120607 op) = (term1028 _120607 op).
Proof. exact (@lem5759985 _120607 (term927 _120607 op)). Qed.
Lemma lem5759987 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1029 _120607 op x) = (term926 _120607 op x).
Proof. exact (eq_refl (term1029 _120607 op x)). Qed.
Lemma lem5759988 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5759989 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1030 _120607 op x) = (term1020 _120607 op x).
Proof. exact (MK_COMB (@lem5759988) (@lem5759987 _120607 op x)). Qed.
Lemma lem5759990 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1030 _120607 op x) = (term1026 _120607 op x).
Proof. exact (TRANS (@lem5759989 _120607 op x) (@lem5759981 _120607 op x)). Qed.
Lemma lem5759991 {_120607 : Type'} (op : type1400 _120607) : (term1031 _120607 op) = (term1032 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5759990 _120607 op x)). Qed.
Lemma lem5759992 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5759993 {_120607 : Type'} (op : type1400 _120607) : (term1028 _120607 op) = (term1033 _120607 op).
Proof. exact (MK_COMB (@lem5759992 _120607) (@lem5759991 _120607 op)). Qed.
Lemma lem5759994 {_120607 : Type'} (op : type1400 _120607) : (term1027 _120607 op) = (term1033 _120607 op).
Proof. exact (TRANS (@lem5759986 _120607 op) (@lem5759993 _120607 op)). Qed.
Lemma lem5759995 {_120607 : Type'} (op : type1400 _120607) : (term927 _120607 op) = (term927 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5759984 _120607 op x)). Qed.
Lemma lem5759996 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5759997 {_120607 : Type'} (op : type1400 _120607) : (term928 _120607 op) = (term928 _120607 op).
Proof. exact (MK_COMB (@lem5759996 _120607) (@lem5759995 _120607 op)). Qed.
Lemma lem5759999 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term918 _120607 op x) = x) = ((term918 _120607 op x) = x).
Proof. exact (eq_refl ((term918 _120607 op x) = x)). Qed.
Lemma lem5760000 {_120607 : Type'} (P : _120607 -> Prop) : (term173 _120607 P) = (term174 _120607 P).
Proof. exact (@lem18392 _120607 P). Qed.
Lemma lem5760001 {_120607 : Type'} (op : type1400 _120607) : (term1034 _120607 op) = (term1035 _120607 op).
Proof. exact (@lem5760000 _120607 (term919 _120607 op)). Qed.
Lemma lem5760002 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1036 _120607 op x) = ((term918 _120607 op x) = x).
Proof. exact (eq_refl (term1036 _120607 op x)). Qed.
Lemma lem5760003 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5760005 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1037 _120607 op x) = (term1038 _120607 op x).
Proof. exact (MK_COMB (@lem5760003) (@lem5760002 _120607 op x)). Qed.
Lemma lem5760006 {_120607 : Type'} (op : type1400 _120607) : (term1039 _120607 op) = (term1040 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760005 _120607 op x)). Qed.
Lemma lem5760007 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760008 {_120607 : Type'} (op : type1400 _120607) : (term1035 _120607 op) = (term1041 _120607 op).
Proof. exact (MK_COMB (@lem5760007 _120607) (@lem5760006 _120607 op)). Qed.
Lemma lem5760009 {_120607 : Type'} (op : type1400 _120607) : (term1034 _120607 op) = (term1041 _120607 op).
Proof. exact (TRANS (@lem5760001 _120607 op) (@lem5760008 _120607 op)). Qed.
Lemma lem5760010 {_120607 : Type'} (op : type1400 _120607) : (term919 _120607 op) = (term919 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5759999 _120607 op x)). Qed.
Lemma lem5760011 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5760012 {_120607 : Type'} (op : type1400 _120607) : (term920 _120607 op) = (term920 _120607 op).
Proof. exact (MK_COMB (@lem5760011 _120607) (@lem5760010 _120607 op)). Qed.
Lemma lem5760013 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5760014 {_120607 : Type'} (op : type1400 _120607) : (term1042 _120607 op) = (term1043 _120607 op).
Proof. exact (MK_COMB (@lem5760013) (@lem5759994 _120607 op)). Qed.
Lemma lem5760015 {_120607 : Type'} (op : type1400 _120607) : (term1044 _120607 op) = (term1045 _120607 op).
Proof. exact (MK_COMB (@lem5760014 _120607 op) (@lem5760009 _120607 op)). Qed.
Lemma lem5760016 {_120607 : Type'} (op : type1400 _120607) : (term1046 _120607 op) = (term1044 _120607 op).
Proof. exact (@lem17045 (term928 _120607 op) (term920 _120607 op)). Qed.
Lemma lem5760017 {_120607 : Type'} (op : type1400 _120607) : (term1046 _120607 op) = (term1045 _120607 op).
Proof. exact (TRANS (@lem5760016 _120607 op) (@lem5760015 _120607 op)). Qed.
Lemma lem5760018 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5760019 {_120607 : Type'} (op : type1400 _120607) : (term929 _120607 op) = (term929 _120607 op).
Proof. exact (MK_COMB (@lem5760018) (@lem5759997 _120607 op)). Qed.
Lemma lem5760020 {_120607 : Type'} (op : type1400 _120607) : (term930 _120607 op) = (term930 _120607 op).
Proof. exact (MK_COMB (@lem5760019 _120607 op) (@lem5760012 _120607 op)). Qed.
Lemma lem5760021 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5760022 {_120607 : Type'} (op : type1400 _120607) : (term1047 _120607 op) = (term1048 _120607 op).
Proof. exact (MK_COMB (@lem5760021) (@lem5759953 _120607 op)). Qed.
Lemma lem5760023 {_120607 : Type'} (op : type1400 _120607) : (term1049 _120607 op) = (term1050 _120607 op).
Proof. exact (MK_COMB (@lem5760022 _120607 op) (@lem5760017 _120607 op)). Qed.
Lemma lem5760024 {_120607 : Type'} (op : type1400 _120607) : (term1051 _120607 op) = (term1049 _120607 op).
Proof. exact (@lem17045 (term934 _120607 op) (term930 _120607 op)). Qed.
Lemma lem5760025 {_120607 : Type'} (op : type1400 _120607) : (term1051 _120607 op) = (term1050 _120607 op).
Proof. exact (TRANS (@lem5760024 _120607 op) (@lem5760023 _120607 op)). Qed.
Lemma lem5760026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5760027 {_120607 : Type'} (op : type1400 _120607) : (term935 _120607 op) = (term935 _120607 op).
Proof. exact (MK_COMB (@lem5760026) (@lem5759956 _120607 op)). Qed.
Lemma lem5760028 {_120607 : Type'} (op : type1400 _120607) : (term936 _120607 op) = (term936 _120607 op).
Proof. exact (MK_COMB (@lem5760027 _120607 op) (@lem5760020 _120607 op)). Qed.
Lemma lem5760030 {_120607 : Type'} (op : type1400 _120607) : (term1052 _120607 op) = (term1052 _120607 op).
Proof. exact (eq_refl (term1052 _120607 op)). Qed.
Lemma lem5760031 {_120607 : Type'} (op : type1400 _120607) : (term1053 _120607 op) = (term1053 _120607 op).
Proof. exact (MK_COMB (@lem5760030 _120607 op) (@lem5760028 _120607 op)). Qed.
Lemma lem5760033 {_120607 : Type'} (op : type1400 _120607) : (term1054 _120607 op) = (term1054 _120607 op).
Proof. exact (eq_refl (term1054 _120607 op)). Qed.
Lemma lem5760034 {_120607 : Type'} (op : type1400 _120607) : (term1055 _120607 op) = (term1056 _120607 op).
Proof. exact (MK_COMB (@lem5760033 _120607 op) (@lem5760025 _120607 op)). Qed.
Lemma lem5760035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5760036 {_120607 : Type'} (op : type1400 _120607) : (term1057 _120607 op) = (term1058 _120607 op).
Proof. exact (MK_COMB (@lem5760035) (@lem5760034 _120607 op)). Qed.
Lemma lem5760037 {_120607 : Type'} (op : type1400 _120607) : (term1059 _120607 op) = (term1060 _120607 op).
Proof. exact (MK_COMB (@lem5760036 _120607 op) (@lem5760031 _120607 op)). Qed.
Lemma lem5760038 {_120607 : Type'} (op : type1400 _120607) : ((@monoidal _120607 op) = (term936 _120607 op)) = (term1059 _120607 op).
Proof. exact (@lem17784 (@monoidal _120607 op) (term936 _120607 op)). Qed.
Lemma lem5760039 {_120607 : Type'} (op : type1400 _120607) : ((@monoidal _120607 op) = (term936 _120607 op)) = (term1060 _120607 op).
Proof. exact (TRANS (@lem5760038 _120607 op) (@lem5760037 _120607 op)). Qed.
Lemma lem5760040 {_120607 : Type'} : (term938 _120607) = (term1061 _120607).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5760039 _120607 op)). Qed.
Lemma lem5760041 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5760042 {_120607 : Type'} : (term892 _120607) = (term1062 _120607).
Proof. exact (MK_COMB (@lem5760041 _120607) (@lem5760040 _120607)). Qed.
Lemma lem5760044 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5760045 {_120607 : Type'} (P : type403 _120607) (Q : type403 _120607) : (term1063 _120607 P Q) = (term1064 _120607 P Q).
Proof. exact (@lem5760044 (type1400 _120607) P Q). Qed.
Lemma lem5760046 {_120607 : Type'} : (term1065 _120607) = (term1066 _120607).
Proof. exact (@lem5760045 _120607 (term1067 _120607) (term1068 _120607)). Qed.
Lemma lem5760047 {_120607 : Type'} (op : type1400 _120607) : (term1069 _120607 op) = (term1056 _120607 op).
Proof. exact (eq_refl (term1069 _120607 op)). Qed.
Lemma lem5760048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5760049 {_120607 : Type'} (op : type1400 _120607) : (term1070 _120607 op) = (term1058 _120607 op).
Proof. exact (MK_COMB (@lem5760048) (@lem5760047 _120607 op)). Qed.
Lemma lem5760050 {_120607 : Type'} (op : type1400 _120607) : (term1071 _120607 op) = (term1053 _120607 op).
Proof. exact (eq_refl (term1071 _120607 op)). Qed.
Lemma lem5760051 {_120607 : Type'} (op : type1400 _120607) : (term1072 _120607 op) = (term1060 _120607 op).
Proof. exact (MK_COMB (@lem5760049 _120607 op) (@lem5760050 _120607 op)). Qed.
Lemma lem5760052 {_120607 : Type'} : (term1073 _120607) = (term1061 _120607).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5760051 _120607 op)). Qed.
Lemma lem5760053 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5760054 {_120607 : Type'} : (term1065 _120607) = (term1062 _120607).
Proof. exact (MK_COMB (@lem5760053 _120607) (@lem5760052 _120607)). Qed.
Lemma lem5760055 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760056 {_120607 : Type'} : (term1074 _120607) = (term1075 _120607).
Proof. exact (MK_COMB (@lem5760055) (@lem5760054 _120607)). Qed.
Lemma lem5760057 {_120607 : Type'} (op : type1400 _120607) : (term1069 _120607 op) = (term1056 _120607 op).
Proof. exact (eq_refl (term1069 _120607 op)). Qed.
Lemma lem5760058 {_120607 : Type'} : (term1076 _120607) = (term1067 _120607).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5760057 _120607 op)). Qed.
Lemma lem5760059 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5760060 {_120607 : Type'} : (term1077 _120607) = (term1078 _120607).
Proof. exact (MK_COMB (@lem5760059 _120607) (@lem5760058 _120607)). Qed.
Lemma lem5760061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5760062 {_120607 : Type'} : (term1079 _120607) = (term1080 _120607).
Proof. exact (MK_COMB (@lem5760061) (@lem5760060 _120607)). Qed.
Lemma lem5760063 {_120607 : Type'} (op : type1400 _120607) : (term1071 _120607 op) = (term1053 _120607 op).
Proof. exact (eq_refl (term1071 _120607 op)). Qed.
Lemma lem5760064 {_120607 : Type'} : (term1081 _120607) = (term1068 _120607).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5760063 _120607 op)). Qed.
Lemma lem5760065 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5760066 {_120607 : Type'} : (term1082 _120607) = (term1083 _120607).
Proof. exact (MK_COMB (@lem5760065 _120607) (@lem5760064 _120607)). Qed.
Lemma lem5760067 {_120607 : Type'} : (term1066 _120607) = (term1084 _120607).
Proof. exact (MK_COMB (@lem5760062 _120607) (@lem5760066 _120607)). Qed.
Lemma lem5760068 {_120607 : Type'} : ((term1065 _120607) = (term1066 _120607)) = ((term1062 _120607) = (term1084 _120607)).
Proof. exact (MK_COMB (@lem5760056 _120607) (@lem5760067 _120607)). Qed.
Lemma lem5760069 {_120607 : Type'} : (term1062 _120607) = (term1084 _120607).
Proof. exact (EQ_MP (@lem5760068 _120607) (@lem5760046 _120607)). Qed.
Lemma lem5760195 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term268 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5760196 {_120607 : Type'} (P : _120607 -> Prop) (Q : _120607 -> Prop) : (term268 _120607 P Q) = (term267 _120607 P Q).
Proof. exact (@lem5760195 _120607 P Q). Qed.
Lemma lem5760197 {_120607 : Type'} (op : type1400 _120607) : (term1085 _120607 op) = (term1086 _120607 op).
Proof. exact (@lem5760196 _120607 (term1032 _120607 op) (term1040 _120607 op)). Qed.
Lemma lem5760198 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1087 _120607 op x) = (term1026 _120607 op x).
Proof. exact (eq_refl (term1087 _120607 op x)). Qed.
Lemma lem5760199 {_120607 : Type'} (op : type1400 _120607) : (term1088 _120607 op) = (term1032 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760198 _120607 op x)). Qed.
Lemma lem5760200 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760201 {_120607 : Type'} (op : type1400 _120607) : (term1089 _120607 op) = (term1033 _120607 op).
Proof. exact (MK_COMB (@lem5760200 _120607) (@lem5760199 _120607 op)). Qed.
Lemma lem5760202 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5760203 {_120607 : Type'} (op : type1400 _120607) : (term1090 _120607 op) = (term1043 _120607 op).
Proof. exact (MK_COMB (@lem5760202) (@lem5760201 _120607 op)). Qed.
Lemma lem5760204 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1091 _120607 op x) = (term1038 _120607 op x).
Proof. exact (eq_refl (term1091 _120607 op x)). Qed.
Lemma lem5760205 {_120607 : Type'} (op : type1400 _120607) : (term1092 _120607 op) = (term1040 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760204 _120607 op x)). Qed.
Lemma lem5760206 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760207 {_120607 : Type'} (op : type1400 _120607) : (term1093 _120607 op) = (term1041 _120607 op).
Proof. exact (MK_COMB (@lem5760206 _120607) (@lem5760205 _120607 op)). Qed.
Lemma lem5760208 {_120607 : Type'} (op : type1400 _120607) : (term1085 _120607 op) = (term1045 _120607 op).
Proof. exact (MK_COMB (@lem5760203 _120607 op) (@lem5760207 _120607 op)). Qed.
Lemma lem5760209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760210 {_120607 : Type'} (op : type1400 _120607) : (term1094 _120607 op) = (term1095 _120607 op).
Proof. exact (MK_COMB (@lem5760209) (@lem5760208 _120607 op)). Qed.
Lemma lem5760211 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1087 _120607 op x) = (term1026 _120607 op x).
Proof. exact (eq_refl (term1087 _120607 op x)). Qed.
Lemma lem5760212 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5760213 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1096 _120607 op x) = (term1097 _120607 op x).
Proof. exact (MK_COMB (@lem5760212) (@lem5760211 _120607 op x)). Qed.
Lemma lem5760214 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1091 _120607 op x) = (term1038 _120607 op x).
Proof. exact (eq_refl (term1091 _120607 op x)). Qed.
Lemma lem5760215 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1098 _120607 op x) = (term1099 _120607 op x).
Proof. exact (MK_COMB (@lem5760213 _120607 op x) (@lem5760214 _120607 op x)). Qed.
Lemma lem5760216 {_120607 : Type'} (op : type1400 _120607) : (term1100 _120607 op) = (term1101 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760215 _120607 op x)). Qed.
Lemma lem5760217 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760218 {_120607 : Type'} (op : type1400 _120607) : (term1086 _120607 op) = (term1102 _120607 op).
Proof. exact (MK_COMB (@lem5760217 _120607) (@lem5760216 _120607 op)). Qed.
Lemma lem5760219 {_120607 : Type'} (op : type1400 _120607) : ((term1085 _120607 op) = (term1086 _120607 op)) = ((term1045 _120607 op) = (term1102 _120607 op)).
Proof. exact (MK_COMB (@lem5760210 _120607 op) (@lem5760218 _120607 op)). Qed.
Lemma lem5760220 {_120607 : Type'} (op : type1400 _120607) : (term1045 _120607 op) = (term1102 _120607 op).
Proof. exact (EQ_MP (@lem5760219 _120607 op) (@lem5760197 _120607 op)). Qed.
Lemma lem5760222 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1103 A P Q) = (term1104 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5760223 {_120607 : Type'} (P : _120607 -> Prop) (Q : Prop) : (term1103 _120607 P Q) = (term1104 _120607 P Q).
Proof. exact (@lem5760222 _120607 P Q). Qed.
Lemma lem5760224 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1105 _120607 op x) = (term1106 _120607 op x).
Proof. exact (@lem5760223 _120607 (term1025 _120607 op x) (term1038 _120607 op x)). Qed.
Lemma lem5760225 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1107 _120607 op x y) = (term1019 _120607 op x y).
Proof. exact (eq_refl (term1107 _120607 op x y)). Qed.
Lemma lem5760226 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1108 _120607 op x) = (term1025 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5760225 _120607 op x y)). Qed.
Lemma lem5760227 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760228 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1109 _120607 op x) = (term1026 _120607 op x).
Proof. exact (MK_COMB (@lem5760227 _120607) (@lem5760226 _120607 op x)). Qed.
Lemma lem5760229 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5760230 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1110 _120607 op x) = (term1097 _120607 op x).
Proof. exact (MK_COMB (@lem5760229) (@lem5760228 _120607 op x)). Qed.
Lemma lem5760231 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1038 _120607 op x) = (term1038 _120607 op x).
Proof. exact (eq_refl (term1038 _120607 op x)). Qed.
Lemma lem5760232 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1105 _120607 op x) = (term1099 _120607 op x).
Proof. exact (MK_COMB (@lem5760230 _120607 op x) (@lem5760231 _120607 op x)). Qed.
Lemma lem5760233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760234 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1111 _120607 op x) = (term1112 _120607 op x).
Proof. exact (MK_COMB (@lem5760233) (@lem5760232 _120607 op x)). Qed.
Lemma lem5760235 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1107 _120607 op x y) = (term1019 _120607 op x y).
Proof. exact (eq_refl (term1107 _120607 op x y)). Qed.
Lemma lem5760236 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5760237 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1113 _120607 op x y) = (term1114 _120607 op x y).
Proof. exact (MK_COMB (@lem5760236) (@lem5760235 _120607 op x y)). Qed.
Lemma lem5760238 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1038 _120607 op x) = (term1038 _120607 op x).
Proof. exact (eq_refl (term1038 _120607 op x)). Qed.
Lemma lem5760239 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1115 _120607 y op x) = (term1116 _120607 y op x).
Proof. exact (MK_COMB (@lem5760237 _120607 op x y) (@lem5760238 _120607 op x)). Qed.
Lemma lem5760240 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1117 _120607 op x) = (term1118 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5760239 _120607 y op x)). Qed.
Lemma lem5760241 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760242 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1106 _120607 op x) = (term1119 _120607 op x).
Proof. exact (MK_COMB (@lem5760241 _120607) (@lem5760240 _120607 op x)). Qed.
Lemma lem5760243 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1105 _120607 op x) = (term1106 _120607 op x)) = ((term1099 _120607 op x) = (term1119 _120607 op x)).
Proof. exact (MK_COMB (@lem5760234 _120607 op x) (@lem5760242 _120607 op x)). Qed.
Lemma lem5760244 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1099 _120607 op x) = (term1119 _120607 op x).
Proof. exact (EQ_MP (@lem5760243 _120607 op x) (@lem5760224 _120607 op x)). Qed.
Lemma lem5760246 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1103 A P Q) = (term1104 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5760247 {_120607 : Type'} (P : _120607 -> Prop) (Q : Prop) : (term1103 _120607 P Q) = (term1104 _120607 P Q).
Proof. exact (@lem5760246 _120607 P Q). Qed.
Lemma lem5760248 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1120 _120607 y op x) = (term1121 _120607 y op x).
Proof. exact (@lem5760247 _120607 (term1018 _120607 op x y) (term1038 _120607 op x)). Qed.
Lemma lem5760249 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term1122 _120607 op x y z) = (term1016 _120607 op x y z).
Proof. exact (eq_refl (term1122 _120607 op x y z)). Qed.
Lemma lem5760250 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1123 _120607 op x y) = (term1018 _120607 op x y).
Proof. exact (fun_ext (fun z : _120607 => @lem5760249 _120607 op x y z)). Qed.
Lemma lem5760251 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760252 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1124 _120607 op x y) = (term1019 _120607 op x y).
Proof. exact (MK_COMB (@lem5760251 _120607) (@lem5760250 _120607 op x y)). Qed.
Lemma lem5760253 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5760254 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1125 _120607 op x y) = (term1114 _120607 op x y).
Proof. exact (MK_COMB (@lem5760253) (@lem5760252 _120607 op x y)). Qed.
Lemma lem5760255 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1038 _120607 op x) = (term1038 _120607 op x).
Proof. exact (eq_refl (term1038 _120607 op x)). Qed.
Lemma lem5760256 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1120 _120607 y op x) = (term1116 _120607 y op x).
Proof. exact (MK_COMB (@lem5760254 _120607 op x y) (@lem5760255 _120607 op x)). Qed.
Lemma lem5760257 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760258 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1126 _120607 y op x) = (term1127 _120607 y op x).
Proof. exact (MK_COMB (@lem5760257) (@lem5760256 _120607 y op x)). Qed.
Lemma lem5760259 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term1122 _120607 op x y z) = (term1016 _120607 op x y z).
Proof. exact (eq_refl (term1122 _120607 op x y z)). Qed.
Lemma lem5760260 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5760261 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term1128 _120607 op x y z) = (term1129 _120607 op x y z).
Proof. exact (MK_COMB (@lem5760260) (@lem5760259 _120607 op x y z)). Qed.
Lemma lem5760262 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1038 _120607 op x) = (term1038 _120607 op x).
Proof. exact (eq_refl (term1038 _120607 op x)). Qed.
Lemma lem5760263 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1130 _120607 y z op x) = (term1131 _120607 y z op x).
Proof. exact (MK_COMB (@lem5760261 _120607 op x y z) (@lem5760262 _120607 op x)). Qed.
Lemma lem5760264 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1132 _120607 y op x) = (term1133 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5760263 _120607 y z op x)). Qed.
Lemma lem5760265 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760266 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1121 _120607 y op x) = (term1134 _120607 y op x).
Proof. exact (MK_COMB (@lem5760265 _120607) (@lem5760264 _120607 y op x)). Qed.
Lemma lem5760267 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : ((term1120 _120607 y op x) = (term1121 _120607 y op x)) = ((term1116 _120607 y op x) = (term1134 _120607 y op x)).
Proof. exact (MK_COMB (@lem5760258 _120607 y op x) (@lem5760266 _120607 y op x)). Qed.
Lemma lem5760268 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1116 _120607 y op x) = (term1134 _120607 y op x).
Proof. exact (EQ_MP (@lem5760267 _120607 y op x) (@lem5760248 _120607 y op x)). Qed.
Lemma lem5760269 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1118 _120607 op x) = (term1135 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5760268 _120607 y op x)). Qed.
Lemma lem5760270 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760271 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1119 _120607 op x) = (term1136 _120607 op x).
Proof. exact (MK_COMB (@lem5760270 _120607) (@lem5760269 _120607 op x)). Qed.
Lemma lem5760272 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1099 _120607 op x) = (term1136 _120607 op x).
Proof. exact (TRANS (@lem5760244 _120607 op x) (@lem5760271 _120607 op x)). Qed.
Lemma lem5760273 {_120607 : Type'} (op : type1400 _120607) : (term1101 _120607 op) = (term1137 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760272 _120607 op x)). Qed.
Lemma lem5760274 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760275 {_120607 : Type'} (op : type1400 _120607) : (term1102 _120607 op) = (term1138 _120607 op).
Proof. exact (MK_COMB (@lem5760274 _120607) (@lem5760273 _120607 op)). Qed.
Lemma lem5760276 {_120607 : Type'} (op : type1400 _120607) : (term1045 _120607 op) = (term1138 _120607 op).
Proof. exact (TRANS (@lem5760220 _120607 op) (@lem5760275 _120607 op)). Qed.
Lemma lem5760277 {_120607 : Type'} (op : type1400 _120607) : (term1048 _120607 op) = (term1048 _120607 op).
Proof. exact (eq_refl (term1048 _120607 op)). Qed.
Lemma lem5760278 {_120607 : Type'} (op : type1400 _120607) : (term1050 _120607 op) = (term1139 _120607 op).
Proof. exact (MK_COMB (@lem5760277 _120607 op) (@lem5760276 _120607 op)). Qed.
Lemma lem5760280 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term268 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5760281 {_120607 : Type'} (P : _120607 -> Prop) (Q : _120607 -> Prop) : (term268 _120607 P Q) = (term267 _120607 P Q).
Proof. exact (@lem5760280 _120607 P Q). Qed.
Lemma lem5760282 {_120607 : Type'} (op : type1400 _120607) : (term1140 _120607 op) = (term1141 _120607 op).
Proof. exact (@lem5760281 _120607 (term1010 _120607 op) (term1137 _120607 op)). Qed.
Lemma lem5760283 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1142 _120607 op x) = (term1004 _120607 op x).
Proof. exact (eq_refl (term1142 _120607 op x)). Qed.
Lemma lem5760284 {_120607 : Type'} (op : type1400 _120607) : (term1143 _120607 op) = (term1010 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760283 _120607 op x)). Qed.
Lemma lem5760285 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760286 {_120607 : Type'} (op : type1400 _120607) : (term1144 _120607 op) = (term1011 _120607 op).
Proof. exact (MK_COMB (@lem5760285 _120607) (@lem5760284 _120607 op)). Qed.
Lemma lem5760287 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5760288 {_120607 : Type'} (op : type1400 _120607) : (term1145 _120607 op) = (term1048 _120607 op).
Proof. exact (MK_COMB (@lem5760287) (@lem5760286 _120607 op)). Qed.
Lemma lem5760289 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1146 _120607 op x) = (term1136 _120607 op x).
Proof. exact (eq_refl (term1146 _120607 op x)). Qed.
Lemma lem5760290 {_120607 : Type'} (op : type1400 _120607) : (term1147 _120607 op) = (term1137 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760289 _120607 op x)). Qed.
Lemma lem5760291 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760292 {_120607 : Type'} (op : type1400 _120607) : (term1148 _120607 op) = (term1138 _120607 op).
Proof. exact (MK_COMB (@lem5760291 _120607) (@lem5760290 _120607 op)). Qed.
Lemma lem5760293 {_120607 : Type'} (op : type1400 _120607) : (term1140 _120607 op) = (term1139 _120607 op).
Proof. exact (MK_COMB (@lem5760288 _120607 op) (@lem5760292 _120607 op)). Qed.
Lemma lem5760294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760295 {_120607 : Type'} (op : type1400 _120607) : (term1149 _120607 op) = (term1150 _120607 op).
Proof. exact (MK_COMB (@lem5760294) (@lem5760293 _120607 op)). Qed.
Lemma lem5760296 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1142 _120607 op x) = (term1004 _120607 op x).
Proof. exact (eq_refl (term1142 _120607 op x)). Qed.
Lemma lem5760297 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5760298 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1151 _120607 op x) = (term1152 _120607 op x).
Proof. exact (MK_COMB (@lem5760297) (@lem5760296 _120607 op x)). Qed.
Lemma lem5760299 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1146 _120607 op x) = (term1136 _120607 op x).
Proof. exact (eq_refl (term1146 _120607 op x)). Qed.
Lemma lem5760300 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1153 _120607 op x) = (term1154 _120607 op x).
Proof. exact (MK_COMB (@lem5760298 _120607 op x) (@lem5760299 _120607 op x)). Qed.
Lemma lem5760301 {_120607 : Type'} (op : type1400 _120607) : (term1155 _120607 op) = (term1156 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760300 _120607 op x)). Qed.
Lemma lem5760302 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760303 {_120607 : Type'} (op : type1400 _120607) : (term1141 _120607 op) = (term1157 _120607 op).
Proof. exact (MK_COMB (@lem5760302 _120607) (@lem5760301 _120607 op)). Qed.
Lemma lem5760304 {_120607 : Type'} (op : type1400 _120607) : ((term1140 _120607 op) = (term1141 _120607 op)) = ((term1139 _120607 op) = (term1157 _120607 op)).
Proof. exact (MK_COMB (@lem5760295 _120607 op) (@lem5760303 _120607 op)). Qed.
Lemma lem5760305 {_120607 : Type'} (op : type1400 _120607) : (term1139 _120607 op) = (term1157 _120607 op).
Proof. exact (EQ_MP (@lem5760304 _120607 op) (@lem5760282 _120607 op)). Qed.
Lemma lem5760307 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term268 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5760308 {_120607 : Type'} (P : _120607 -> Prop) (Q : _120607 -> Prop) : (term268 _120607 P Q) = (term267 _120607 P Q).
Proof. exact (@lem5760307 _120607 P Q). Qed.
Lemma lem5760309 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1158 _120607 op x) = (term1159 _120607 op x).
Proof. exact (@lem5760308 _120607 (term1003 _120607 op x) (term1135 _120607 op x)). Qed.
Lemma lem5760310 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1160 _120607 op x y) = (term1001 _120607 op y x).
Proof. exact (eq_refl (term1160 _120607 op x y)). Qed.
Lemma lem5760311 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1161 _120607 op x) = (term1003 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5760310 _120607 op y x)). Qed.
Lemma lem5760312 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760313 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1162 _120607 op x) = (term1004 _120607 op x).
Proof. exact (MK_COMB (@lem5760312 _120607) (@lem5760311 _120607 op x)). Qed.
Lemma lem5760314 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5760315 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1163 _120607 op x) = (term1152 _120607 op x).
Proof. exact (MK_COMB (@lem5760314) (@lem5760313 _120607 op x)). Qed.
Lemma lem5760316 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1164 _120607 op x y) = (term1134 _120607 y op x).
Proof. exact (eq_refl (term1164 _120607 op x y)). Qed.
Lemma lem5760317 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1165 _120607 op x) = (term1135 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5760316 _120607 y op x)). Qed.
Lemma lem5760318 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760319 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1166 _120607 op x) = (term1136 _120607 op x).
Proof. exact (MK_COMB (@lem5760318 _120607) (@lem5760317 _120607 op x)). Qed.
Lemma lem5760320 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1158 _120607 op x) = (term1154 _120607 op x).
Proof. exact (MK_COMB (@lem5760315 _120607 op x) (@lem5760319 _120607 op x)). Qed.
Lemma lem5760321 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760322 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1167 _120607 op x) = (term1168 _120607 op x).
Proof. exact (MK_COMB (@lem5760321) (@lem5760320 _120607 op x)). Qed.
Lemma lem5760323 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1160 _120607 op x y) = (term1001 _120607 op y x).
Proof. exact (eq_refl (term1160 _120607 op x y)). Qed.
Lemma lem5760324 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5760325 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1169 _120607 op x y) = (term1170 _120607 op y x).
Proof. exact (MK_COMB (@lem5760324) (@lem5760323 _120607 op y x)). Qed.
Lemma lem5760326 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1164 _120607 op x y) = (term1134 _120607 y op x).
Proof. exact (eq_refl (term1164 _120607 op x y)). Qed.
Lemma lem5760327 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1171 _120607 op x y) = (term1172 _120607 y op x).
Proof. exact (MK_COMB (@lem5760325 _120607 op y x) (@lem5760326 _120607 y op x)). Qed.
Lemma lem5760328 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1173 _120607 op x) = (term1174 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5760327 _120607 y op x)). Qed.
Lemma lem5760329 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760330 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1159 _120607 op x) = (term1175 _120607 op x).
Proof. exact (MK_COMB (@lem5760329 _120607) (@lem5760328 _120607 op x)). Qed.
Lemma lem5760331 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1158 _120607 op x) = (term1159 _120607 op x)) = ((term1154 _120607 op x) = (term1175 _120607 op x)).
Proof. exact (MK_COMB (@lem5760322 _120607 op x) (@lem5760330 _120607 op x)). Qed.
Lemma lem5760332 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1154 _120607 op x) = (term1175 _120607 op x).
Proof. exact (EQ_MP (@lem5760331 _120607 op x) (@lem5760309 _120607 op x)). Qed.
Lemma lem5760334 {A : Type'} (P : Prop) (Q : A -> Prop) : (term431 A P Q) = (term432 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5760335 {_120607 : Type'} (P : Prop) (Q : _120607 -> Prop) : (term431 _120607 P Q) = (term432 _120607 P Q).
Proof. exact (@lem5760334 _120607 P Q). Qed.
Lemma lem5760336 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1176 _120607 y op x) = (term1177 _120607 y op x).
Proof. exact (@lem5760335 _120607 (term1001 _120607 op y x) (term1133 _120607 y op x)). Qed.
Lemma lem5760337 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1178 _120607 y op x z) = (term1131 _120607 y z op x).
Proof. exact (eq_refl (term1178 _120607 y op x z)). Qed.
Lemma lem5760338 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1179 _120607 y op x) = (term1133 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5760337 _120607 y z op x)). Qed.
Lemma lem5760339 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760340 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1180 _120607 y op x) = (term1134 _120607 y op x).
Proof. exact (MK_COMB (@lem5760339 _120607) (@lem5760338 _120607 y op x)). Qed.
Lemma lem5760341 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1170 _120607 op y x) = (term1170 _120607 op y x).
Proof. exact (eq_refl (term1170 _120607 op y x)). Qed.
Lemma lem5760342 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1176 _120607 y op x) = (term1172 _120607 y op x).
Proof. exact (MK_COMB (@lem5760341 _120607 op y x) (@lem5760340 _120607 y op x)). Qed.
Lemma lem5760343 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760344 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1181 _120607 y op x) = (term1182 _120607 y op x).
Proof. exact (MK_COMB (@lem5760343) (@lem5760342 _120607 y op x)). Qed.
Lemma lem5760345 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1178 _120607 y op x z) = (term1131 _120607 y z op x).
Proof. exact (eq_refl (term1178 _120607 y op x z)). Qed.
Lemma lem5760346 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1170 _120607 op y x) = (term1170 _120607 op y x).
Proof. exact (eq_refl (term1170 _120607 op y x)). Qed.
Lemma lem5760347 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1183 _120607 y op x z) = (term1184 _120607 y z op x).
Proof. exact (MK_COMB (@lem5760346 _120607 op y x) (@lem5760345 _120607 y z op x)). Qed.
Lemma lem5760348 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1185 _120607 y op x) = (term1186 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5760347 _120607 y z op x)). Qed.
Lemma lem5760349 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760350 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1177 _120607 y op x) = (term1187 _120607 y op x).
Proof. exact (MK_COMB (@lem5760349 _120607) (@lem5760348 _120607 y op x)). Qed.
Lemma lem5760351 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : ((term1176 _120607 y op x) = (term1177 _120607 y op x)) = ((term1172 _120607 y op x) = (term1187 _120607 y op x)).
Proof. exact (MK_COMB (@lem5760344 _120607 y op x) (@lem5760350 _120607 y op x)). Qed.
Lemma lem5760352 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1172 _120607 y op x) = (term1187 _120607 y op x).
Proof. exact (EQ_MP (@lem5760351 _120607 y op x) (@lem5760336 _120607 y op x)). Qed.
Lemma lem5760353 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1174 _120607 op x) = (term1188 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5760352 _120607 y op x)). Qed.
Lemma lem5760354 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760355 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1175 _120607 op x) = (term1189 _120607 op x).
Proof. exact (MK_COMB (@lem5760354 _120607) (@lem5760353 _120607 op x)). Qed.
Lemma lem5760356 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1154 _120607 op x) = (term1189 _120607 op x).
Proof. exact (TRANS (@lem5760332 _120607 op x) (@lem5760355 _120607 op x)). Qed.
Lemma lem5760357 {_120607 : Type'} (op : type1400 _120607) : (term1156 _120607 op) = (term1190 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760356 _120607 op x)). Qed.
Lemma lem5760358 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760359 {_120607 : Type'} (op : type1400 _120607) : (term1157 _120607 op) = (term1191 _120607 op).
Proof. exact (MK_COMB (@lem5760358 _120607) (@lem5760357 _120607 op)). Qed.
Lemma lem5760360 {_120607 : Type'} (op : type1400 _120607) : (term1139 _120607 op) = (term1191 _120607 op).
Proof. exact (TRANS (@lem5760305 _120607 op) (@lem5760359 _120607 op)). Qed.
Lemma lem5760361 {_120607 : Type'} (op : type1400 _120607) : (term1050 _120607 op) = (term1191 _120607 op).
Proof. exact (TRANS (@lem5760278 _120607 op) (@lem5760360 _120607 op)). Qed.
Lemma lem5760362 {_120607 : Type'} (op : type1400 _120607) : (term1054 _120607 op) = (term1054 _120607 op).
Proof. exact (eq_refl (term1054 _120607 op)). Qed.
Lemma lem5760363 {_120607 : Type'} (op : type1400 _120607) : (term1056 _120607 op) = (term1192 _120607 op).
Proof. exact (MK_COMB (@lem5760362 _120607 op) (@lem5760361 _120607 op)). Qed.
Lemma lem5760365 {A : Type'} (P : Prop) (Q : A -> Prop) : (term431 A P Q) = (term432 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5760366 {_120607 : Type'} (P : Prop) (Q : _120607 -> Prop) : (term431 _120607 P Q) = (term432 _120607 P Q).
Proof. exact (@lem5760365 _120607 P Q). Qed.
Lemma lem5760367 {_120607 : Type'} (op : type1400 _120607) : (term1193 _120607 op) = (term1194 _120607 op).
Proof. exact (@lem5760366 _120607 (@monoidal _120607 op) (term1190 _120607 op)). Qed.
Lemma lem5760368 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1195 _120607 op x) = (term1189 _120607 op x).
Proof. exact (eq_refl (term1195 _120607 op x)). Qed.
Lemma lem5760369 {_120607 : Type'} (op : type1400 _120607) : (term1196 _120607 op) = (term1190 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760368 _120607 op x)). Qed.
Lemma lem5760370 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760371 {_120607 : Type'} (op : type1400 _120607) : (term1197 _120607 op) = (term1191 _120607 op).
Proof. exact (MK_COMB (@lem5760370 _120607) (@lem5760369 _120607 op)). Qed.
Lemma lem5760372 {_120607 : Type'} (op : type1400 _120607) : (term1054 _120607 op) = (term1054 _120607 op).
Proof. exact (eq_refl (term1054 _120607 op)). Qed.
Lemma lem5760373 {_120607 : Type'} (op : type1400 _120607) : (term1193 _120607 op) = (term1192 _120607 op).
Proof. exact (MK_COMB (@lem5760372 _120607 op) (@lem5760371 _120607 op)). Qed.
Lemma lem5760374 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760375 {_120607 : Type'} (op : type1400 _120607) : (term1198 _120607 op) = (term1199 _120607 op).
Proof. exact (MK_COMB (@lem5760374) (@lem5760373 _120607 op)). Qed.
Lemma lem5760376 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1195 _120607 op x) = (term1189 _120607 op x).
Proof. exact (eq_refl (term1195 _120607 op x)). Qed.
Lemma lem5760377 {_120607 : Type'} (op : type1400 _120607) : (term1054 _120607 op) = (term1054 _120607 op).
Proof. exact (eq_refl (term1054 _120607 op)). Qed.
Lemma lem5760378 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1200 _120607 op x) = (term1201 _120607 op x).
Proof. exact (MK_COMB (@lem5760377 _120607 op) (@lem5760376 _120607 op x)). Qed.
Lemma lem5760379 {_120607 : Type'} (op : type1400 _120607) : (term1202 _120607 op) = (term1203 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760378 _120607 op x)). Qed.
Lemma lem5760380 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760381 {_120607 : Type'} (op : type1400 _120607) : (term1194 _120607 op) = (term1204 _120607 op).
Proof. exact (MK_COMB (@lem5760380 _120607) (@lem5760379 _120607 op)). Qed.
Lemma lem5760382 {_120607 : Type'} (op : type1400 _120607) : ((term1193 _120607 op) = (term1194 _120607 op)) = ((term1192 _120607 op) = (term1204 _120607 op)).
Proof. exact (MK_COMB (@lem5760375 _120607 op) (@lem5760381 _120607 op)). Qed.
Lemma lem5760383 {_120607 : Type'} (op : type1400 _120607) : (term1192 _120607 op) = (term1204 _120607 op).
Proof. exact (EQ_MP (@lem5760382 _120607 op) (@lem5760367 _120607 op)). Qed.
Lemma lem5760385 {A : Type'} (P : Prop) (Q : A -> Prop) : (term431 A P Q) = (term432 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5760386 {_120607 : Type'} (P : Prop) (Q : _120607 -> Prop) : (term431 _120607 P Q) = (term432 _120607 P Q).
Proof. exact (@lem5760385 _120607 P Q). Qed.
Lemma lem5760387 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1205 _120607 op x) = (term1206 _120607 op x).
Proof. exact (@lem5760386 _120607 (@monoidal _120607 op) (term1188 _120607 op x)). Qed.
Lemma lem5760388 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1207 _120607 op x y) = (term1187 _120607 y op x).
Proof. exact (eq_refl (term1207 _120607 op x y)). Qed.
Lemma lem5760389 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1208 _120607 op x) = (term1188 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5760388 _120607 y op x)). Qed.
Lemma lem5760390 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760391 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1209 _120607 op x) = (term1189 _120607 op x).
Proof. exact (MK_COMB (@lem5760390 _120607) (@lem5760389 _120607 op x)). Qed.
Lemma lem5760392 {_120607 : Type'} (op : type1400 _120607) : (term1054 _120607 op) = (term1054 _120607 op).
Proof. exact (eq_refl (term1054 _120607 op)). Qed.
Lemma lem5760393 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1205 _120607 op x) = (term1201 _120607 op x).
Proof. exact (MK_COMB (@lem5760392 _120607 op) (@lem5760391 _120607 op x)). Qed.
Lemma lem5760394 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760395 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1210 _120607 op x) = (term1211 _120607 op x).
Proof. exact (MK_COMB (@lem5760394) (@lem5760393 _120607 op x)). Qed.
Lemma lem5760396 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1207 _120607 op x y) = (term1187 _120607 y op x).
Proof. exact (eq_refl (term1207 _120607 op x y)). Qed.
Lemma lem5760397 {_120607 : Type'} (op : type1400 _120607) : (term1054 _120607 op) = (term1054 _120607 op).
Proof. exact (eq_refl (term1054 _120607 op)). Qed.
Lemma lem5760398 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1212 _120607 op x y) = (term1213 _120607 y op x).
Proof. exact (MK_COMB (@lem5760397 _120607 op) (@lem5760396 _120607 y op x)). Qed.
Lemma lem5760399 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1214 _120607 op x) = (term1215 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5760398 _120607 y op x)). Qed.
Lemma lem5760400 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760401 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1206 _120607 op x) = (term1216 _120607 op x).
Proof. exact (MK_COMB (@lem5760400 _120607) (@lem5760399 _120607 op x)). Qed.
Lemma lem5760402 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1205 _120607 op x) = (term1206 _120607 op x)) = ((term1201 _120607 op x) = (term1216 _120607 op x)).
Proof. exact (MK_COMB (@lem5760395 _120607 op x) (@lem5760401 _120607 op x)). Qed.
Lemma lem5760403 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1201 _120607 op x) = (term1216 _120607 op x).
Proof. exact (EQ_MP (@lem5760402 _120607 op x) (@lem5760387 _120607 op x)). Qed.
Lemma lem5760405 {A : Type'} (P : Prop) (Q : A -> Prop) : (term431 A P Q) = (term432 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5760406 {_120607 : Type'} (P : Prop) (Q : _120607 -> Prop) : (term431 _120607 P Q) = (term432 _120607 P Q).
Proof. exact (@lem5760405 _120607 P Q). Qed.
Lemma lem5760407 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1217 _120607 y op x) = (term1218 _120607 y op x).
Proof. exact (@lem5760406 _120607 (@monoidal _120607 op) (term1186 _120607 y op x)). Qed.
Lemma lem5760408 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1219 _120607 y op x z) = (term1184 _120607 y z op x).
Proof. exact (eq_refl (term1219 _120607 y op x z)). Qed.
Lemma lem5760409 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1220 _120607 y op x) = (term1186 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5760408 _120607 y z op x)). Qed.
Lemma lem5760410 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760411 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1221 _120607 y op x) = (term1187 _120607 y op x).
Proof. exact (MK_COMB (@lem5760410 _120607) (@lem5760409 _120607 y op x)). Qed.
Lemma lem5760412 {_120607 : Type'} (op : type1400 _120607) : (term1054 _120607 op) = (term1054 _120607 op).
Proof. exact (eq_refl (term1054 _120607 op)). Qed.
Lemma lem5760413 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1217 _120607 y op x) = (term1213 _120607 y op x).
Proof. exact (MK_COMB (@lem5760412 _120607 op) (@lem5760411 _120607 y op x)). Qed.
Lemma lem5760414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760415 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1222 _120607 y op x) = (term1223 _120607 y op x).
Proof. exact (MK_COMB (@lem5760414) (@lem5760413 _120607 y op x)). Qed.
Lemma lem5760416 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1219 _120607 y op x z) = (term1184 _120607 y z op x).
Proof. exact (eq_refl (term1219 _120607 y op x z)). Qed.
Lemma lem5760417 {_120607 : Type'} (op : type1400 _120607) : (term1054 _120607 op) = (term1054 _120607 op).
Proof. exact (eq_refl (term1054 _120607 op)). Qed.
Lemma lem5760418 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1224 _120607 y op x z) = (term1225 _120607 y z op x).
Proof. exact (MK_COMB (@lem5760417 _120607 op) (@lem5760416 _120607 y z op x)). Qed.
Lemma lem5760419 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1226 _120607 y op x) = (term1227 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5760418 _120607 y z op x)). Qed.
Lemma lem5760420 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760421 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1218 _120607 y op x) = (term1228 _120607 y op x).
Proof. exact (MK_COMB (@lem5760420 _120607) (@lem5760419 _120607 y op x)). Qed.
Lemma lem5760422 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : ((term1217 _120607 y op x) = (term1218 _120607 y op x)) = ((term1213 _120607 y op x) = (term1228 _120607 y op x)).
Proof. exact (MK_COMB (@lem5760415 _120607 y op x) (@lem5760421 _120607 y op x)). Qed.
Lemma lem5760423 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1213 _120607 y op x) = (term1228 _120607 y op x).
Proof. exact (EQ_MP (@lem5760422 _120607 y op x) (@lem5760407 _120607 y op x)). Qed.
Lemma lem5760424 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1215 _120607 op x) = (term1229 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5760423 _120607 y op x)). Qed.
Lemma lem5760425 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760426 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1216 _120607 op x) = (term1230 _120607 op x).
Proof. exact (MK_COMB (@lem5760425 _120607) (@lem5760424 _120607 op x)). Qed.
Lemma lem5760427 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1201 _120607 op x) = (term1230 _120607 op x).
Proof. exact (TRANS (@lem5760403 _120607 op x) (@lem5760426 _120607 op x)). Qed.
Lemma lem5760428 {_120607 : Type'} (op : type1400 _120607) : (term1203 _120607 op) = (term1231 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760427 _120607 op x)). Qed.
Lemma lem5760429 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760430 {_120607 : Type'} (op : type1400 _120607) : (term1204 _120607 op) = (term1232 _120607 op).
Proof. exact (MK_COMB (@lem5760429 _120607) (@lem5760428 _120607 op)). Qed.
Lemma lem5760431 {_120607 : Type'} (op : type1400 _120607) : (term1192 _120607 op) = (term1232 _120607 op).
Proof. exact (TRANS (@lem5760383 _120607 op) (@lem5760430 _120607 op)). Qed.
Lemma lem5760432 {_120607 : Type'} (op : type1400 _120607) : (term1056 _120607 op) = (term1232 _120607 op).
Proof. exact (TRANS (@lem5760363 _120607 op) (@lem5760431 _120607 op)). Qed.
Lemma lem5760433 {_120607 : Type'} : (term1067 _120607) = (term1233 _120607).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5760432 _120607 op)). Qed.
Lemma lem5760434 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5760435 {_120607 : Type'} : (term1078 _120607) = (term1234 _120607).
Proof. exact (MK_COMB (@lem5760434 _120607) (@lem5760433 _120607)). Qed.
Lemma lem5760437 {A B : Type'} (P : type1413 A B) : (term1235 A B P) = (term1236 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5760438 {_120607 : Type'} (P : type401 _120607) : (term1237 _120607 P) = (term1238 _120607 P).
Proof. exact (@lem5760437 (type1400 _120607) _120607 P). Qed.
Lemma lem5760439 {_120607 : Type'} : (term1239 _120607) = (term1240 _120607).
Proof. exact (@lem5760438 _120607 (term1241 _120607)). Qed.
Lemma lem5760440 {_120607 : Type'} (op : type1400 _120607) : (term1242 _120607 op) = (term1231 _120607 op).
Proof. exact (eq_refl (term1242 _120607 op)). Qed.
Lemma lem5760441 {_120607 : Type'} (x : _120607) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5760442 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1243 _120607 op x) = (term1244 _120607 op x).
Proof. exact (MK_COMB (@lem5760440 _120607 op) (@lem5760441 _120607 x)). Qed.
Lemma lem5760443 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1244 _120607 op x) = (term1230 _120607 op x).
Proof. exact (eq_refl (term1244 _120607 op x)). Qed.
Lemma lem5760444 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1243 _120607 op x) = (term1230 _120607 op x).
Proof. exact (TRANS (@lem5760442 _120607 op x) (@lem5760443 _120607 op x)). Qed.
Lemma lem5760445 {_120607 : Type'} (op : type1400 _120607) : (term1245 _120607 op) = (term1231 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760444 _120607 op x)). Qed.
Lemma lem5760446 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760447 {_120607 : Type'} (op : type1400 _120607) : (term1246 _120607 op) = (term1232 _120607 op).
Proof. exact (MK_COMB (@lem5760446 _120607) (@lem5760445 _120607 op)). Qed.
Lemma lem5760448 {_120607 : Type'} : (term1247 _120607) = (term1233 _120607).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5760447 _120607 op)). Qed.
Lemma lem5760449 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5760450 {_120607 : Type'} : (term1239 _120607) = (term1234 _120607).
Proof. exact (MK_COMB (@lem5760449 _120607) (@lem5760448 _120607)). Qed.
Lemma lem5760451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760452 {_120607 : Type'} : (term1248 _120607) = (term1249 _120607).
Proof. exact (MK_COMB (@lem5760451) (@lem5760450 _120607)). Qed.
Lemma lem5760453 {_120607 : Type'} (op : type1400 _120607) : (term1242 _120607 op) = (term1231 _120607 op).
Proof. exact (eq_refl (term1242 _120607 op)). Qed.
Lemma lem5760454 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (x op) = (x op).
Proof. exact (eq_refl (x op)). Qed.
Lemma lem5760455 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1250 _120607 x op) = (term1251 _120607 x op).
Proof. exact (MK_COMB (@lem5760453 _120607 op) (@lem5760454 _120607 x op)). Qed.
Lemma lem5760456 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1251 _120607 x op) = (term1252 _120607 x op).
Proof. exact (eq_refl (term1251 _120607 x op)). Qed.
Lemma lem5760457 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1250 _120607 x op) = (term1252 _120607 x op).
Proof. exact (TRANS (@lem5760455 _120607 x op) (@lem5760456 _120607 x op)). Qed.
Lemma lem5760458 {_120607 : Type'} (x : type402 _120607) : (term1253 _120607 x) = (term1254 _120607 x).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5760457 _120607 x op)). Qed.
Lemma lem5760459 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5760460 {_120607 : Type'} (x : type402 _120607) : (term1255 _120607 x) = (term1256 _120607 x).
Proof. exact (MK_COMB (@lem5760459 _120607) (@lem5760458 _120607 x)). Qed.
Lemma lem5760461 {_120607 : Type'} : (term1257 _120607) = (term1258 _120607).
Proof. exact (fun_ext (fun x : type402 _120607 => @lem5760460 _120607 x)). Qed.
Lemma lem5760462 {_120607 : Type'} : (@ex ((_120607 -> _120607 -> _120607) -> _120607)) = (@ex ((_120607 -> _120607 -> _120607) -> _120607)).
Proof. exact (eq_refl (@ex ((_120607 -> _120607 -> _120607) -> _120607))). Qed.
Lemma lem5760463 {_120607 : Type'} : (term1240 _120607) = (term1259 _120607).
Proof. exact (MK_COMB (@lem5760462 _120607) (@lem5760461 _120607)). Qed.
Lemma lem5760464 {_120607 : Type'} : ((term1239 _120607) = (term1240 _120607)) = ((term1234 _120607) = (term1259 _120607)).
Proof. exact (MK_COMB (@lem5760452 _120607) (@lem5760463 _120607)). Qed.
Lemma lem5760465 {_120607 : Type'} : (term1234 _120607) = (term1259 _120607).
Proof. exact (EQ_MP (@lem5760464 _120607) (@lem5760439 _120607)). Qed.
Lemma lem5760467 {A B : Type'} (P : type1413 A B) : (term1235 A B P) = (term1236 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5760468 {_120607 : Type'} (P : type401 _120607) : (term1237 _120607 P) = (term1238 _120607 P).
Proof. exact (@lem5760467 (type1400 _120607) _120607 P). Qed.
Lemma lem5760469 {_120607 : Type'} (x : type402 _120607) : (term1260 _120607 x) = (term1261 _120607 x).
Proof. exact (@lem5760468 _120607 (term1262 _120607 x)). Qed.
Lemma lem5760470 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1263 _120607 x op) = (term1264 _120607 x op).
Proof. exact (eq_refl (term1263 _120607 x op)). Qed.
Lemma lem5760471 {_120607 : Type'} (y : _120607) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5760472 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) (y : _120607) : (term1265 _120607 x op y) = (term1266 _120607 x op y).
Proof. exact (MK_COMB (@lem5760470 _120607 x op) (@lem5760471 _120607 y)). Qed.
Lemma lem5760473 {_120607 : Type'} (y : _120607) (x : type402 _120607) (op : type1400 _120607) : (term1266 _120607 x op y) = (term1267 _120607 y x op).
Proof. exact (eq_refl (term1266 _120607 x op y)). Qed.
Lemma lem5760474 {_120607 : Type'} (y : _120607) (x : type402 _120607) (op : type1400 _120607) : (term1265 _120607 x op y) = (term1267 _120607 y x op).
Proof. exact (TRANS (@lem5760472 _120607 x op y) (@lem5760473 _120607 y x op)). Qed.
Lemma lem5760475 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1268 _120607 x op) = (term1264 _120607 x op).
Proof. exact (fun_ext (fun y : _120607 => @lem5760474 _120607 y x op)). Qed.
Lemma lem5760476 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760477 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1269 _120607 x op) = (term1252 _120607 x op).
Proof. exact (MK_COMB (@lem5760476 _120607) (@lem5760475 _120607 x op)). Qed.
Lemma lem5760478 {_120607 : Type'} (x : type402 _120607) : (term1270 _120607 x) = (term1254 _120607 x).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5760477 _120607 x op)). Qed.
Lemma lem5760479 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5760480 {_120607 : Type'} (x : type402 _120607) : (term1260 _120607 x) = (term1256 _120607 x).
Proof. exact (MK_COMB (@lem5760479 _120607) (@lem5760478 _120607 x)). Qed.
Lemma lem5760481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760482 {_120607 : Type'} (x : type402 _120607) : (term1271 _120607 x) = (term1272 _120607 x).
Proof. exact (MK_COMB (@lem5760481) (@lem5760480 _120607 x)). Qed.
Lemma lem5760483 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1263 _120607 x op) = (term1264 _120607 x op).
Proof. exact (eq_refl (term1263 _120607 x op)). Qed.
Lemma lem5760484 {_120607 : Type'} (y : type402 _120607) (op : type1400 _120607) : (y op) = (y op).
Proof. exact (eq_refl (y op)). Qed.
Lemma lem5760485 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (op : type1400 _120607) : (term1273 _120607 x y op) = (term1274 _120607 x y op).
Proof. exact (MK_COMB (@lem5760483 _120607 x op) (@lem5760484 _120607 y op)). Qed.
Lemma lem5760486 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1274 _120607 x y op) = (term1275 _120607 y x op).
Proof. exact (eq_refl (term1274 _120607 x y op)). Qed.
Lemma lem5760487 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1273 _120607 x y op) = (term1275 _120607 y x op).
Proof. exact (TRANS (@lem5760485 _120607 x y op) (@lem5760486 _120607 y x op)). Qed.
Lemma lem5760488 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1276 _120607 x y) = (term1277 _120607 y x).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5760487 _120607 y x op)). Qed.
Lemma lem5760489 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5760490 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1278 _120607 x y) = (term1279 _120607 y x).
Proof. exact (MK_COMB (@lem5760489 _120607) (@lem5760488 _120607 y x)). Qed.
Lemma lem5760491 {_120607 : Type'} (x : type402 _120607) : (term1280 _120607 x) = (term1281 _120607 x).
Proof. exact (fun_ext (fun y : type402 _120607 => @lem5760490 _120607 y x)). Qed.
Lemma lem5760492 {_120607 : Type'} : (@ex ((_120607 -> _120607 -> _120607) -> _120607)) = (@ex ((_120607 -> _120607 -> _120607) -> _120607)).
Proof. exact (eq_refl (@ex ((_120607 -> _120607 -> _120607) -> _120607))). Qed.
Lemma lem5760493 {_120607 : Type'} (x : type402 _120607) : (term1261 _120607 x) = (term1282 _120607 x).
Proof. exact (MK_COMB (@lem5760492 _120607) (@lem5760491 _120607 x)). Qed.
Lemma lem5760494 {_120607 : Type'} (x : type402 _120607) : ((term1260 _120607 x) = (term1261 _120607 x)) = ((term1256 _120607 x) = (term1282 _120607 x)).
Proof. exact (MK_COMB (@lem5760482 _120607 x) (@lem5760493 _120607 x)). Qed.
Lemma lem5760495 {_120607 : Type'} (x : type402 _120607) : (term1256 _120607 x) = (term1282 _120607 x).
Proof. exact (EQ_MP (@lem5760494 _120607 x) (@lem5760469 _120607 x)). Qed.
Lemma lem5760497 {A B : Type'} (P : type1413 A B) : (term1235 A B P) = (term1236 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5760498 {_120607 : Type'} (P : type401 _120607) : (term1237 _120607 P) = (term1238 _120607 P).
Proof. exact (@lem5760497 (type1400 _120607) _120607 P). Qed.
Lemma lem5760499 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1283 _120607 y x) = (term1284 _120607 y x).
Proof. exact (@lem5760498 _120607 (term1285 _120607 y x)). Qed.
Lemma lem5760500 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1286 _120607 y x op) = (term1287 _120607 y x op).
Proof. exact (eq_refl (term1286 _120607 y x op)). Qed.
Lemma lem5760501 {_120607 : Type'} (z : _120607) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5760502 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (op : type1400 _120607) (z : _120607) : (term1288 _120607 y x op z) = (term1289 _120607 y x op z).
Proof. exact (MK_COMB (@lem5760500 _120607 y x op) (@lem5760501 _120607 z)). Qed.
Lemma lem5760503 {_120607 : Type'} (y : type402 _120607) (z : _120607) (x : type402 _120607) (op : type1400 _120607) : (term1289 _120607 y x op z) = (term1290 _120607 y z x op).
Proof. exact (eq_refl (term1289 _120607 y x op z)). Qed.
Lemma lem5760504 {_120607 : Type'} (y : type402 _120607) (z : _120607) (x : type402 _120607) (op : type1400 _120607) : (term1288 _120607 y x op z) = (term1290 _120607 y z x op).
Proof. exact (TRANS (@lem5760502 _120607 y x op z) (@lem5760503 _120607 y z x op)). Qed.
Lemma lem5760505 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1291 _120607 y x op) = (term1287 _120607 y x op).
Proof. exact (fun_ext (fun z : _120607 => @lem5760504 _120607 y z x op)). Qed.
Lemma lem5760506 {_120607 : Type'} : (@ex _120607) = (@ex _120607).
Proof. exact (eq_refl (@ex _120607)). Qed.
Lemma lem5760507 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1292 _120607 y x op) = (term1275 _120607 y x op).
Proof. exact (MK_COMB (@lem5760506 _120607) (@lem5760505 _120607 y x op)). Qed.
Lemma lem5760508 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1293 _120607 y x) = (term1277 _120607 y x).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5760507 _120607 y x op)). Qed.
Lemma lem5760509 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5760510 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1283 _120607 y x) = (term1279 _120607 y x).
Proof. exact (MK_COMB (@lem5760509 _120607) (@lem5760508 _120607 y x)). Qed.
Lemma lem5760511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760512 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1294 _120607 y x) = (term1295 _120607 y x).
Proof. exact (MK_COMB (@lem5760511) (@lem5760510 _120607 y x)). Qed.
Lemma lem5760513 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1286 _120607 y x op) = (term1287 _120607 y x op).
Proof. exact (eq_refl (term1286 _120607 y x op)). Qed.
Lemma lem5760514 {_120607 : Type'} (z : type402 _120607) (op : type1400 _120607) : (z op) = (z op).
Proof. exact (eq_refl (z op)). Qed.
Lemma lem5760515 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1296 _120607 y x z op) = (term1297 _120607 y x z op).
Proof. exact (MK_COMB (@lem5760513 _120607 y x op) (@lem5760514 _120607 z op)). Qed.
Lemma lem5760516 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1297 _120607 y x z op) = (term1298 _120607 y z x op).
Proof. exact (eq_refl (term1297 _120607 y x z op)). Qed.
Lemma lem5760517 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1296 _120607 y x z op) = (term1298 _120607 y z x op).
Proof. exact (TRANS (@lem5760515 _120607 y x z op) (@lem5760516 _120607 y z x op)). Qed.
Lemma lem5760518 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) : (term1299 _120607 y x z) = (term1300 _120607 y z x).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5760517 _120607 y z x op)). Qed.
Lemma lem5760519 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5760520 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) : (term1301 _120607 y x z) = (term1302 _120607 y z x).
Proof. exact (MK_COMB (@lem5760519 _120607) (@lem5760518 _120607 y z x)). Qed.
Lemma lem5760521 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1303 _120607 y x) = (term1304 _120607 y x).
Proof. exact (fun_ext (fun z : type402 _120607 => @lem5760520 _120607 y z x)). Qed.
Lemma lem5760522 {_120607 : Type'} : (@ex ((_120607 -> _120607 -> _120607) -> _120607)) = (@ex ((_120607 -> _120607 -> _120607) -> _120607)).
Proof. exact (eq_refl (@ex ((_120607 -> _120607 -> _120607) -> _120607))). Qed.
Lemma lem5760523 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1284 _120607 y x) = (term1305 _120607 y x).
Proof. exact (MK_COMB (@lem5760522 _120607) (@lem5760521 _120607 y x)). Qed.
Lemma lem5760524 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : ((term1283 _120607 y x) = (term1284 _120607 y x)) = ((term1279 _120607 y x) = (term1305 _120607 y x)).
Proof. exact (MK_COMB (@lem5760512 _120607 y x) (@lem5760523 _120607 y x)). Qed.
Lemma lem5760525 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1279 _120607 y x) = (term1305 _120607 y x).
Proof. exact (EQ_MP (@lem5760524 _120607 y x) (@lem5760499 _120607 y x)). Qed.
Lemma lem5760526 {_120607 : Type'} (x : type402 _120607) : (term1281 _120607 x) = (term1306 _120607 x).
Proof. exact (fun_ext (fun y : type402 _120607 => @lem5760525 _120607 y x)). Qed.
Lemma lem5760527 {_120607 : Type'} : (@ex ((_120607 -> _120607 -> _120607) -> _120607)) = (@ex ((_120607 -> _120607 -> _120607) -> _120607)).
Proof. exact (eq_refl (@ex ((_120607 -> _120607 -> _120607) -> _120607))). Qed.
Lemma lem5760528 {_120607 : Type'} (x : type402 _120607) : (term1282 _120607 x) = (term1307 _120607 x).
Proof. exact (MK_COMB (@lem5760527 _120607) (@lem5760526 _120607 x)). Qed.
Lemma lem5760529 {_120607 : Type'} (x : type402 _120607) : (term1256 _120607 x) = (term1307 _120607 x).
Proof. exact (TRANS (@lem5760495 _120607 x) (@lem5760528 _120607 x)). Qed.
Lemma lem5760530 {_120607 : Type'} : (term1258 _120607) = (term1308 _120607).
Proof. exact (fun_ext (fun x : type402 _120607 => @lem5760529 _120607 x)). Qed.
Lemma lem5760531 {_120607 : Type'} : (@ex ((_120607 -> _120607 -> _120607) -> _120607)) = (@ex ((_120607 -> _120607 -> _120607) -> _120607)).
Proof. exact (eq_refl (@ex ((_120607 -> _120607 -> _120607) -> _120607))). Qed.
Lemma lem5760532 {_120607 : Type'} : (term1259 _120607) = (term1309 _120607).
Proof. exact (MK_COMB (@lem5760531 _120607) (@lem5760530 _120607)). Qed.
Lemma lem5760533 {_120607 : Type'} : (term1234 _120607) = (term1309 _120607).
Proof. exact (TRANS (@lem5760465 _120607) (@lem5760532 _120607)). Qed.
Lemma lem5760534 {_120607 : Type'} : (term1078 _120607) = (term1309 _120607).
Proof. exact (TRANS (@lem5760435 _120607) (@lem5760533 _120607)). Qed.
Lemma lem5760535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5760536 {_120607 : Type'} : (term1080 _120607) = (term1310 _120607).
Proof. exact (MK_COMB (@lem5760535) (@lem5760534 _120607)). Qed.
Lemma lem5760537 {_120607 : Type'} : (term1083 _120607) = (term1083 _120607).
Proof. exact (eq_refl (term1083 _120607)). Qed.
Lemma lem5760538 {_120607 : Type'} : (term1084 _120607) = (term1311 _120607).
Proof. exact (MK_COMB (@lem5760536 _120607) (@lem5760537 _120607)). Qed.
Lemma lem5760540 {A : Type'} (P : A -> Prop) (Q : Prop) : (term467 A P Q) = (term468 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5760541 {_120607 : Type'} (P : type82 _120607) (Q : Prop) : (term1312 _120607 P Q) = (term1313 _120607 P Q).
Proof. exact (@lem5760540 (type402 _120607) P Q). Qed.
Lemma lem5760542 {_120607 : Type'} : (term1314 _120607) = (term1315 _120607).
Proof. exact (@lem5760541 _120607 (term1308 _120607) (term1083 _120607)). Qed.
Lemma lem5760543 {_120607 : Type'} (x : type402 _120607) : (term1316 _120607 x) = (term1307 _120607 x).
Proof. exact (eq_refl (term1316 _120607 x)). Qed.
Lemma lem5760544 {_120607 : Type'} : (term1317 _120607) = (term1308 _120607).
Proof. exact (fun_ext (fun x : type402 _120607 => @lem5760543 _120607 x)). Qed.
Lemma lem5760545 {_120607 : Type'} : (@ex ((_120607 -> _120607 -> _120607) -> _120607)) = (@ex ((_120607 -> _120607 -> _120607) -> _120607)).
Proof. exact (eq_refl (@ex ((_120607 -> _120607 -> _120607) -> _120607))). Qed.
Lemma lem5760546 {_120607 : Type'} : (term1318 _120607) = (term1309 _120607).
Proof. exact (MK_COMB (@lem5760545 _120607) (@lem5760544 _120607)). Qed.
Lemma lem5760547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5760548 {_120607 : Type'} : (term1319 _120607) = (term1310 _120607).
Proof. exact (MK_COMB (@lem5760547) (@lem5760546 _120607)). Qed.
Lemma lem5760549 {_120607 : Type'} : (term1083 _120607) = (term1083 _120607).
Proof. exact (eq_refl (term1083 _120607)). Qed.
Lemma lem5760550 {_120607 : Type'} : (term1314 _120607) = (term1311 _120607).
Proof. exact (MK_COMB (@lem5760548 _120607) (@lem5760549 _120607)). Qed.
Lemma lem5760551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760552 {_120607 : Type'} : (term1320 _120607) = (term1321 _120607).
Proof. exact (MK_COMB (@lem5760551) (@lem5760550 _120607)). Qed.
Lemma lem5760553 {_120607 : Type'} (x : type402 _120607) : (term1316 _120607 x) = (term1307 _120607 x).
Proof. exact (eq_refl (term1316 _120607 x)). Qed.
Lemma lem5760554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5760555 {_120607 : Type'} (x : type402 _120607) : (term1322 _120607 x) = (term1323 _120607 x).
Proof. exact (MK_COMB (@lem5760554) (@lem5760553 _120607 x)). Qed.
Lemma lem5760556 {_120607 : Type'} : (term1083 _120607) = (term1083 _120607).
Proof. exact (eq_refl (term1083 _120607)). Qed.
Lemma lem5760557 {_120607 : Type'} (x : type402 _120607) : (term1324 _120607 x) = (term1325 _120607 x).
Proof. exact (MK_COMB (@lem5760555 _120607 x) (@lem5760556 _120607)). Qed.
Lemma lem5760558 {_120607 : Type'} : (term1326 _120607) = (term1327 _120607).
Proof. exact (fun_ext (fun x : type402 _120607 => @lem5760557 _120607 x)). Qed.
Lemma lem5760559 {_120607 : Type'} : (@ex ((_120607 -> _120607 -> _120607) -> _120607)) = (@ex ((_120607 -> _120607 -> _120607) -> _120607)).
Proof. exact (eq_refl (@ex ((_120607 -> _120607 -> _120607) -> _120607))). Qed.
Lemma lem5760560 {_120607 : Type'} : (term1315 _120607) = (term1328 _120607).
Proof. exact (MK_COMB (@lem5760559 _120607) (@lem5760558 _120607)). Qed.
Lemma lem5760561 {_120607 : Type'} : ((term1314 _120607) = (term1315 _120607)) = ((term1311 _120607) = (term1328 _120607)).
Proof. exact (MK_COMB (@lem5760552 _120607) (@lem5760560 _120607)). Qed.
Lemma lem5760562 {_120607 : Type'} : (term1311 _120607) = (term1328 _120607).
Proof. exact (EQ_MP (@lem5760561 _120607) (@lem5760542 _120607)). Qed.
Lemma lem5760564 {A : Type'} (P : A -> Prop) (Q : Prop) : (term467 A P Q) = (term468 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5760565 {_120607 : Type'} (P : type82 _120607) (Q : Prop) : (term1312 _120607 P Q) = (term1313 _120607 P Q).
Proof. exact (@lem5760564 (type402 _120607) P Q). Qed.
Lemma lem5760566 {_120607 : Type'} (x : type402 _120607) : (term1329 _120607 x) = (term1330 _120607 x).
Proof. exact (@lem5760565 _120607 (term1306 _120607 x) (term1083 _120607)). Qed.
Lemma lem5760567 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1331 _120607 x y) = (term1305 _120607 y x).
Proof. exact (eq_refl (term1331 _120607 x y)). Qed.
Lemma lem5760568 {_120607 : Type'} (x : type402 _120607) : (term1332 _120607 x) = (term1306 _120607 x).
Proof. exact (fun_ext (fun y : type402 _120607 => @lem5760567 _120607 y x)). Qed.
Lemma lem5760569 {_120607 : Type'} : (@ex ((_120607 -> _120607 -> _120607) -> _120607)) = (@ex ((_120607 -> _120607 -> _120607) -> _120607)).
Proof. exact (eq_refl (@ex ((_120607 -> _120607 -> _120607) -> _120607))). Qed.
Lemma lem5760570 {_120607 : Type'} (x : type402 _120607) : (term1333 _120607 x) = (term1307 _120607 x).
Proof. exact (MK_COMB (@lem5760569 _120607) (@lem5760568 _120607 x)). Qed.
Lemma lem5760571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5760572 {_120607 : Type'} (x : type402 _120607) : (term1334 _120607 x) = (term1323 _120607 x).
Proof. exact (MK_COMB (@lem5760571) (@lem5760570 _120607 x)). Qed.
Lemma lem5760573 {_120607 : Type'} : (term1083 _120607) = (term1083 _120607).
Proof. exact (eq_refl (term1083 _120607)). Qed.
Lemma lem5760574 {_120607 : Type'} (x : type402 _120607) : (term1329 _120607 x) = (term1325 _120607 x).
Proof. exact (MK_COMB (@lem5760572 _120607 x) (@lem5760573 _120607)). Qed.
Lemma lem5760575 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760576 {_120607 : Type'} (x : type402 _120607) : (term1335 _120607 x) = (term1336 _120607 x).
Proof. exact (MK_COMB (@lem5760575) (@lem5760574 _120607 x)). Qed.
Lemma lem5760577 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1331 _120607 x y) = (term1305 _120607 y x).
Proof. exact (eq_refl (term1331 _120607 x y)). Qed.
Lemma lem5760578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5760579 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1337 _120607 x y) = (term1338 _120607 y x).
Proof. exact (MK_COMB (@lem5760578) (@lem5760577 _120607 y x)). Qed.
Lemma lem5760580 {_120607 : Type'} : (term1083 _120607) = (term1083 _120607).
Proof. exact (eq_refl (term1083 _120607)). Qed.
Lemma lem5760581 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1339 _120607 x y) = (term1340 _120607 y x).
Proof. exact (MK_COMB (@lem5760579 _120607 y x) (@lem5760580 _120607)). Qed.
Lemma lem5760582 {_120607 : Type'} (x : type402 _120607) : (term1341 _120607 x) = (term1342 _120607 x).
Proof. exact (fun_ext (fun y : type402 _120607 => @lem5760581 _120607 y x)). Qed.
Lemma lem5760583 {_120607 : Type'} : (@ex ((_120607 -> _120607 -> _120607) -> _120607)) = (@ex ((_120607 -> _120607 -> _120607) -> _120607)).
Proof. exact (eq_refl (@ex ((_120607 -> _120607 -> _120607) -> _120607))). Qed.
Lemma lem5760584 {_120607 : Type'} (x : type402 _120607) : (term1330 _120607 x) = (term1343 _120607 x).
Proof. exact (MK_COMB (@lem5760583 _120607) (@lem5760582 _120607 x)). Qed.
Lemma lem5760585 {_120607 : Type'} (x : type402 _120607) : ((term1329 _120607 x) = (term1330 _120607 x)) = ((term1325 _120607 x) = (term1343 _120607 x)).
Proof. exact (MK_COMB (@lem5760576 _120607 x) (@lem5760584 _120607 x)). Qed.
Lemma lem5760586 {_120607 : Type'} (x : type402 _120607) : (term1325 _120607 x) = (term1343 _120607 x).
Proof. exact (EQ_MP (@lem5760585 _120607 x) (@lem5760566 _120607 x)). Qed.
Lemma lem5760588 {A : Type'} (P : A -> Prop) (Q : Prop) : (term467 A P Q) = (term468 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5760589 {_120607 : Type'} (P : type82 _120607) (Q : Prop) : (term1312 _120607 P Q) = (term1313 _120607 P Q).
Proof. exact (@lem5760588 (type402 _120607) P Q). Qed.
Lemma lem5760590 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1344 _120607 y x) = (term1345 _120607 y x).
Proof. exact (@lem5760589 _120607 (term1304 _120607 y x) (term1083 _120607)). Qed.
Lemma lem5760591 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) : (term1346 _120607 y x z) = (term1302 _120607 y z x).
Proof. exact (eq_refl (term1346 _120607 y x z)). Qed.
Lemma lem5760592 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1347 _120607 y x) = (term1304 _120607 y x).
Proof. exact (fun_ext (fun z : type402 _120607 => @lem5760591 _120607 y z x)). Qed.
Lemma lem5760593 {_120607 : Type'} : (@ex ((_120607 -> _120607 -> _120607) -> _120607)) = (@ex ((_120607 -> _120607 -> _120607) -> _120607)).
Proof. exact (eq_refl (@ex ((_120607 -> _120607 -> _120607) -> _120607))). Qed.
Lemma lem5760594 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1348 _120607 y x) = (term1305 _120607 y x).
Proof. exact (MK_COMB (@lem5760593 _120607) (@lem5760592 _120607 y x)). Qed.
Lemma lem5760595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5760596 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1349 _120607 y x) = (term1338 _120607 y x).
Proof. exact (MK_COMB (@lem5760595) (@lem5760594 _120607 y x)). Qed.
Lemma lem5760597 {_120607 : Type'} : (term1083 _120607) = (term1083 _120607).
Proof. exact (eq_refl (term1083 _120607)). Qed.
Lemma lem5760598 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1344 _120607 y x) = (term1340 _120607 y x).
Proof. exact (MK_COMB (@lem5760596 _120607 y x) (@lem5760597 _120607)). Qed.
Lemma lem5760599 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5760600 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1350 _120607 y x) = (term1351 _120607 y x).
Proof. exact (MK_COMB (@lem5760599) (@lem5760598 _120607 y x)). Qed.
Lemma lem5760601 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) : (term1346 _120607 y x z) = (term1302 _120607 y z x).
Proof. exact (eq_refl (term1346 _120607 y x z)). Qed.
Lemma lem5760602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5760603 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) : (term1352 _120607 y x z) = (term1353 _120607 y z x).
Proof. exact (MK_COMB (@lem5760602) (@lem5760601 _120607 y z x)). Qed.
Lemma lem5760604 {_120607 : Type'} : (term1083 _120607) = (term1083 _120607).
Proof. exact (eq_refl (term1083 _120607)). Qed.
Lemma lem5760605 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) : (term1354 _120607 y x z) = (term1355 _120607 y z x).
Proof. exact (MK_COMB (@lem5760603 _120607 y z x) (@lem5760604 _120607)). Qed.
Lemma lem5760606 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1356 _120607 y x) = (term1357 _120607 y x).
Proof. exact (fun_ext (fun z : type402 _120607 => @lem5760605 _120607 y z x)). Qed.
Lemma lem5760607 {_120607 : Type'} : (@ex ((_120607 -> _120607 -> _120607) -> _120607)) = (@ex ((_120607 -> _120607 -> _120607) -> _120607)).
Proof. exact (eq_refl (@ex ((_120607 -> _120607 -> _120607) -> _120607))). Qed.
Lemma lem5760608 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1345 _120607 y x) = (term1358 _120607 y x).
Proof. exact (MK_COMB (@lem5760607 _120607) (@lem5760606 _120607 y x)). Qed.
Lemma lem5760609 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : ((term1344 _120607 y x) = (term1345 _120607 y x)) = ((term1340 _120607 y x) = (term1358 _120607 y x)).
Proof. exact (MK_COMB (@lem5760600 _120607 y x) (@lem5760608 _120607 y x)). Qed.
Lemma lem5760610 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) : (term1340 _120607 y x) = (term1358 _120607 y x).
Proof. exact (EQ_MP (@lem5760609 _120607 y x) (@lem5760590 _120607 y x)). Qed.
Lemma lem5760611 {_120607 : Type'} (x : type402 _120607) : (term1342 _120607 x) = (term1359 _120607 x).
Proof. exact (fun_ext (fun y : type402 _120607 => @lem5760610 _120607 y x)). Qed.
Lemma lem5760612 {_120607 : Type'} : (@ex ((_120607 -> _120607 -> _120607) -> _120607)) = (@ex ((_120607 -> _120607 -> _120607) -> _120607)).
Proof. exact (eq_refl (@ex ((_120607 -> _120607 -> _120607) -> _120607))). Qed.
Lemma lem5760613 {_120607 : Type'} (x : type402 _120607) : (term1343 _120607 x) = (term1360 _120607 x).
Proof. exact (MK_COMB (@lem5760612 _120607) (@lem5760611 _120607 x)). Qed.
Lemma lem5760614 {_120607 : Type'} (x : type402 _120607) : (term1325 _120607 x) = (term1360 _120607 x).
Proof. exact (TRANS (@lem5760586 _120607 x) (@lem5760613 _120607 x)). Qed.
Lemma lem5760615 {_120607 : Type'} : (term1327 _120607) = (term1361 _120607).
Proof. exact (fun_ext (fun x : type402 _120607 => @lem5760614 _120607 x)). Qed.
Lemma lem5760616 {_120607 : Type'} : (@ex ((_120607 -> _120607 -> _120607) -> _120607)) = (@ex ((_120607 -> _120607 -> _120607) -> _120607)).
Proof. exact (eq_refl (@ex ((_120607 -> _120607 -> _120607) -> _120607))). Qed.
Lemma lem5760617 {_120607 : Type'} : (term1328 _120607) = (term1362 _120607).
Proof. exact (MK_COMB (@lem5760616 _120607) (@lem5760615 _120607)). Qed.
Lemma lem5760618 {_120607 : Type'} : (term1311 _120607) = (term1362 _120607).
Proof. exact (TRANS (@lem5760562 _120607) (@lem5760617 _120607)). Qed.
Lemma lem5760619 {_120607 : Type'} : (term1084 _120607) = (term1362 _120607).
Proof. exact (TRANS (@lem5760538 _120607) (@lem5760618 _120607)). Qed.
Lemma lem5760620 {_120607 : Type'} : (term1062 _120607) = (term1362 _120607).
Proof. exact (TRANS (@lem5760069 _120607) (@lem5760619 _120607)). Qed.
Lemma lem5760621 {_120607 : Type'} : (term892 _120607) = (term1362 _120607).
Proof. exact (TRANS (@lem5760042 _120607) (@lem5760620 _120607)). Qed.
Lemma lem5760622 {_120607 : Type'} (h1 : term892 _120607) : term1362 _120607.
Proof. exact (EQ_MP (@lem5760621 _120607) (@lem5759751 _120607 h1)). Qed.
Lemma lem5760623 {_120607 : Type'} (x : type402 _120607) (h1 : term1360 _120607 x) : term1360 _120607 x.
Proof. exact (h1). Qed.
Lemma lem5760624 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (h1 : term1358 _120607 y x) : term1358 _120607 y x.
Proof. exact (h1). Qed.
Lemma lem5760625 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1355 _120607 y z x.
Proof. exact (h1). Qed.
Lemma lem5760626 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term994 _120592 _120607 s x' op f) : term994 _120592 _120607 s x' op f.
Proof. exact (h1). Qed.
Lemma lem5760627 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term991 _120592 _120607 s x' op t f) : term991 _120592 _120607 s x' op t f.
Proof. exact (h1). Qed.
Lemma lem5760632 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760633 {_120607 : Type'} (f : type403 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> Prop) f x).
Proof. exact (@lem5760632 (type1400 _120607) Prop f x). Qed.
Lemma lem5760635 {_120607 : Type'} (op : type1400 _120607) : (@monoidal _120607 op) = (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op).
Proof. exact (@lem5760633 _120607 (@monoidal _120607) op). Qed.
Lemma lem5760646 {_120607 : Type'} : (@eq _120607) = (@eq _120607).
Proof. exact (eq_refl (@eq _120607)). Qed.
Lemma lem5760647 {_120607 : Type'} (op : type1400 _120607) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5760652 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760653 {_120607 : Type'} (f : type402 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> _120607) f x).
Proof. exact (@lem5760652 (type1400 _120607) _120607 f x). Qed.
Lemma lem5760655 {_120607 : Type'} (op : type1400 _120607) : (@neutral _120607 op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) (@neutral _120607) op).
Proof. exact (@lem5760653 _120607 (@neutral _120607) op). Qed.
Lemma lem5760656 {_120607 : Type'} (x : _120607) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5760657 {_120607 : Type'} (op : type1400 _120607) : (term1363 _120607 op) = (term1364 _120607 op).
Proof. exact (MK_COMB (@lem5760647 _120607 op) (@lem5760655 _120607 op)). Qed.
Lemma lem5760658 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term918 _120607 op x) = (term1365 _120607 op x).
Proof. exact (MK_COMB (@lem5760657 _120607 op) (@lem5760656 _120607 x)). Qed.
Lemma lem5760660 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760661 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5760660 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5760662 {_120607 : Type'} (op : type1400 _120607) : (term1364 _120607 op) = (term1366 _120607 op).
Proof. exact (@lem5760661 _120607 op (@I ((_120607 -> _120607 -> _120607) -> _120607) (@neutral _120607) op)). Qed.
Lemma lem5760663 {_120607 : Type'} (x : _120607) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5760664 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1365 _120607 op x) = (term1367 _120607 op x).
Proof. exact (MK_COMB (@lem5760662 _120607 op) (@lem5760663 _120607 x)). Qed.
Lemma lem5760666 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760667 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5760666 _120607 _120607 f x). Qed.
Lemma lem5760668 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1367 _120607 op x) = (term1368 _120607 op x).
Proof. exact (@lem5760667 _120607 (term1366 _120607 op) x). Qed.
Lemma lem5760669 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1365 _120607 op x) = (term1368 _120607 op x).
Proof. exact (TRANS (@lem5760664 _120607 op x) (@lem5760668 _120607 op x)). Qed.
Lemma lem5760670 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term918 _120607 op x) = (term1368 _120607 op x).
Proof. exact (TRANS (@lem5760658 _120607 op x) (@lem5760669 _120607 op x)). Qed.
Lemma lem5760671 {_120607 : Type'} (x : _120607) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5760672 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1369 _120607 op x) = (term1370 _120607 op x).
Proof. exact (MK_COMB (@lem5760646 _120607) (@lem5760670 _120607 op x)). Qed.
Lemma lem5760673 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term918 _120607 op x) = x) = ((term1368 _120607 op x) = x).
Proof. exact (MK_COMB (@lem5760672 _120607 op x) (@lem5760671 _120607 x)). Qed.
Lemma lem5760674 {_120607 : Type'} (op : type1400 _120607) : (term919 _120607 op) = (term1371 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760673 _120607 op x)). Qed.
Lemma lem5760675 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5760676 {_120607 : Type'} (op : type1400 _120607) : (term920 _120607 op) = (term1372 _120607 op).
Proof. exact (MK_COMB (@lem5760675 _120607) (@lem5760674 _120607 op)). Qed.
Lemma lem5760677 {_120607 : Type'} : (@eq _120607) = (@eq _120607).
Proof. exact (eq_refl (@eq _120607)). Qed.
Lemma lem5760686 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760687 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5760686 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5760688 {_120607 : Type'} (op : type1400 _120607) (y : _120607) : (op y) = (@I (_120607 -> _120607 -> _120607) op y).
Proof. exact (@lem5760687 _120607 op y). Qed.
Lemma lem5760689 {_120607 : Type'} (z : _120607) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5760690 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (z : _120607) : (op y z) = (@I (_120607 -> _120607 -> _120607) op y z).
Proof. exact (MK_COMB (@lem5760688 _120607 op y) (@lem5760689 _120607 z)). Qed.
Lemma lem5760692 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760693 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5760692 _120607 _120607 f x). Qed.
Lemma lem5760694 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (z : _120607) : (@I (_120607 -> _120607 -> _120607) op y z) = (term1373 _120607 op y z).
Proof. exact (@lem5760693 _120607 (@I (_120607 -> _120607 -> _120607) op y) z). Qed.
Lemma lem5760696 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (z : _120607) : (op y z) = (term1373 _120607 op y z).
Proof. exact (TRANS (@lem5760690 _120607 op y z) (@lem5760694 _120607 op y z)). Qed.
Lemma lem5760697 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (op x) = (op x).
Proof. exact (eq_refl (op x)). Qed.
Lemma lem5760698 {_120607 : Type'} (x : _120607) (op : type1400 _120607) (y : _120607) (z : _120607) : (term921 _120607 x op y z) = (term1374 _120607 x op y z).
Proof. exact (MK_COMB (@lem5760697 _120607 op x) (@lem5760696 _120607 op y z)). Qed.
Lemma lem5760700 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760701 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5760700 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5760702 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (op x) = (@I (_120607 -> _120607 -> _120607) op x).
Proof. exact (@lem5760701 _120607 op x). Qed.
Lemma lem5760703 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (z : _120607) : (term1373 _120607 op y z) = (term1373 _120607 op y z).
Proof. exact (eq_refl (term1373 _120607 op y z)). Qed.
Lemma lem5760704 {_120607 : Type'} (x : _120607) (op : type1400 _120607) (y : _120607) (z : _120607) : (term1374 _120607 x op y z) = (term1375 _120607 x op y z).
Proof. exact (MK_COMB (@lem5760702 _120607 op x) (@lem5760703 _120607 op y z)). Qed.
Lemma lem5760706 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760707 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5760706 _120607 _120607 f x). Qed.
Lemma lem5760708 {_120607 : Type'} (x : _120607) (op : type1400 _120607) (y : _120607) (z : _120607) : (term1375 _120607 x op y z) = (term1376 _120607 x op y z).
Proof. exact (@lem5760707 _120607 (@I (_120607 -> _120607 -> _120607) op x) (term1373 _120607 op y z)). Qed.
Lemma lem5760709 {_120607 : Type'} (x : _120607) (op : type1400 _120607) (y : _120607) (z : _120607) : (term1374 _120607 x op y z) = (term1376 _120607 x op y z).
Proof. exact (TRANS (@lem5760704 _120607 x op y z) (@lem5760708 _120607 x op y z)). Qed.
Lemma lem5760710 {_120607 : Type'} (x : _120607) (op : type1400 _120607) (y : _120607) (z : _120607) : (term921 _120607 x op y z) = (term1376 _120607 x op y z).
Proof. exact (TRANS (@lem5760698 _120607 x op y z) (@lem5760709 _120607 x op y z)). Qed.
Lemma lem5760711 {_120607 : Type'} (op : type1400 _120607) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5760718 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760719 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5760718 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5760720 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (op x) = (@I (_120607 -> _120607 -> _120607) op x).
Proof. exact (@lem5760719 _120607 op x). Qed.
Lemma lem5760721 {_120607 : Type'} (y : _120607) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5760722 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (op x y) = (@I (_120607 -> _120607 -> _120607) op x y).
Proof. exact (MK_COMB (@lem5760720 _120607 op x) (@lem5760721 _120607 y)). Qed.
Lemma lem5760724 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760725 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5760724 _120607 _120607 f x). Qed.
Lemma lem5760726 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (@I (_120607 -> _120607 -> _120607) op x y) = (term1373 _120607 op x y).
Proof. exact (@lem5760725 _120607 (@I (_120607 -> _120607 -> _120607) op x) y). Qed.
Lemma lem5760728 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (op x y) = (term1373 _120607 op x y).
Proof. exact (TRANS (@lem5760722 _120607 op x y) (@lem5760726 _120607 op x y)). Qed.
Lemma lem5760729 {_120607 : Type'} (z : _120607) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5760730 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1377 _120607 op x y) = (term1378 _120607 op x y).
Proof. exact (MK_COMB (@lem5760711 _120607 op) (@lem5760728 _120607 op x y)). Qed.
Lemma lem5760731 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term922 _120607 op x y z) = (term1379 _120607 op x y z).
Proof. exact (MK_COMB (@lem5760730 _120607 op x y) (@lem5760729 _120607 z)). Qed.
Lemma lem5760733 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760734 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5760733 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5760735 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1378 _120607 op x y) = (term1380 _120607 op x y).
Proof. exact (@lem5760734 _120607 op (term1373 _120607 op x y)). Qed.
Lemma lem5760736 {_120607 : Type'} (z : _120607) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5760737 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term1379 _120607 op x y z) = (term1381 _120607 op x y z).
Proof. exact (MK_COMB (@lem5760735 _120607 op x y) (@lem5760736 _120607 z)). Qed.
Lemma lem5760739 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760740 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5760739 _120607 _120607 f x). Qed.
Lemma lem5760741 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term1381 _120607 op x y z) = (term1382 _120607 op x y z).
Proof. exact (@lem5760740 _120607 (term1380 _120607 op x y) z). Qed.
Lemma lem5760742 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term1379 _120607 op x y z) = (term1382 _120607 op x y z).
Proof. exact (TRANS (@lem5760737 _120607 op x y z) (@lem5760741 _120607 op x y z)). Qed.
Lemma lem5760743 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term922 _120607 op x y z) = (term1382 _120607 op x y z).
Proof. exact (TRANS (@lem5760731 _120607 op x y z) (@lem5760742 _120607 op x y z)). Qed.
Lemma lem5760744 {_120607 : Type'} (x : _120607) (op : type1400 _120607) (y : _120607) (z : _120607) : (term1383 _120607 x op y z) = (term1384 _120607 x op y z).
Proof. exact (MK_COMB (@lem5760677 _120607) (@lem5760710 _120607 x op y z)). Qed.
Lemma lem5760745 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : ((term921 _120607 x op y z) = (term922 _120607 op x y z)) = ((term1376 _120607 x op y z) = (term1382 _120607 op x y z)).
Proof. exact (MK_COMB (@lem5760744 _120607 x op y z) (@lem5760743 _120607 op x y z)). Qed.
Lemma lem5760746 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term923 _120607 op x y) = (term1385 _120607 op x y).
Proof. exact (fun_ext (fun z : _120607 => @lem5760745 _120607 op x y z)). Qed.
Lemma lem5760747 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5760748 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term924 _120607 op x y) = (term1386 _120607 op x y).
Proof. exact (MK_COMB (@lem5760747 _120607) (@lem5760746 _120607 op x y)). Qed.
Lemma lem5760749 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term925 _120607 op x) = (term1387 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5760748 _120607 op x y)). Qed.
Lemma lem5760750 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5760751 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term926 _120607 op x) = (term1388 _120607 op x).
Proof. exact (MK_COMB (@lem5760750 _120607) (@lem5760749 _120607 op x)). Qed.
Lemma lem5760752 {_120607 : Type'} (op : type1400 _120607) : (term927 _120607 op) = (term1389 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760751 _120607 op x)). Qed.
Lemma lem5760753 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5760754 {_120607 : Type'} (op : type1400 _120607) : (term928 _120607 op) = (term1390 _120607 op).
Proof. exact (MK_COMB (@lem5760753 _120607) (@lem5760752 _120607 op)). Qed.
Lemma lem5760755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5760756 {_120607 : Type'} (op : type1400 _120607) : (term929 _120607 op) = (term1391 _120607 op).
Proof. exact (MK_COMB (@lem5760755) (@lem5760754 _120607 op)). Qed.
Lemma lem5760757 {_120607 : Type'} (op : type1400 _120607) : (term930 _120607 op) = (term1392 _120607 op).
Proof. exact (MK_COMB (@lem5760756 _120607 op) (@lem5760676 _120607 op)). Qed.
Lemma lem5760758 {_120607 : Type'} : (@eq _120607) = (@eq _120607).
Proof. exact (eq_refl (@eq _120607)). Qed.
Lemma lem5760765 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760766 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5760765 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5760767 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (op x) = (@I (_120607 -> _120607 -> _120607) op x).
Proof. exact (@lem5760766 _120607 op x). Qed.
Lemma lem5760768 {_120607 : Type'} (y : _120607) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5760769 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (op x y) = (@I (_120607 -> _120607 -> _120607) op x y).
Proof. exact (MK_COMB (@lem5760767 _120607 op x) (@lem5760768 _120607 y)). Qed.
Lemma lem5760771 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760772 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5760771 _120607 _120607 f x). Qed.
Lemma lem5760773 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (@I (_120607 -> _120607 -> _120607) op x y) = (term1373 _120607 op x y).
Proof. exact (@lem5760772 _120607 (@I (_120607 -> _120607 -> _120607) op x) y). Qed.
Lemma lem5760775 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (op x y) = (term1373 _120607 op x y).
Proof. exact (TRANS (@lem5760769 _120607 op x y) (@lem5760773 _120607 op x y)). Qed.
Lemma lem5760782 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760783 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5760782 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5760784 {_120607 : Type'} (op : type1400 _120607) (y : _120607) : (op y) = (@I (_120607 -> _120607 -> _120607) op y).
Proof. exact (@lem5760783 _120607 op y). Qed.
Lemma lem5760785 {_120607 : Type'} (x : _120607) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5760786 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (op y x) = (@I (_120607 -> _120607 -> _120607) op y x).
Proof. exact (MK_COMB (@lem5760784 _120607 op y) (@lem5760785 _120607 x)). Qed.
Lemma lem5760788 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760789 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5760788 _120607 _120607 f x). Qed.
Lemma lem5760790 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (@I (_120607 -> _120607 -> _120607) op y x) = (term1373 _120607 op y x).
Proof. exact (@lem5760789 _120607 (@I (_120607 -> _120607 -> _120607) op y) x). Qed.
Lemma lem5760792 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (op y x) = (term1373 _120607 op y x).
Proof. exact (TRANS (@lem5760786 _120607 op y x) (@lem5760790 _120607 op y x)). Qed.
Lemma lem5760793 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1393 _120607 op x y) = (term1394 _120607 op x y).
Proof. exact (MK_COMB (@lem5760758 _120607) (@lem5760775 _120607 op x y)). Qed.
Lemma lem5760794 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : ((op x y) = (op y x)) = ((term1373 _120607 op x y) = (term1373 _120607 op y x)).
Proof. exact (MK_COMB (@lem5760793 _120607 op x y) (@lem5760792 _120607 op y x)). Qed.
Lemma lem5760795 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term931 _120607 op x) = (term1395 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5760794 _120607 op y x)). Qed.
Lemma lem5760796 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5760797 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term932 _120607 op x) = (term1396 _120607 op x).
Proof. exact (MK_COMB (@lem5760796 _120607) (@lem5760795 _120607 op x)). Qed.
Lemma lem5760798 {_120607 : Type'} (op : type1400 _120607) : (term933 _120607 op) = (term1397 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5760797 _120607 op x)). Qed.
Lemma lem5760799 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5760800 {_120607 : Type'} (op : type1400 _120607) : (term934 _120607 op) = (term1398 _120607 op).
Proof. exact (MK_COMB (@lem5760799 _120607) (@lem5760798 _120607 op)). Qed.
Lemma lem5760801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5760802 {_120607 : Type'} (op : type1400 _120607) : (term935 _120607 op) = (term1399 _120607 op).
Proof. exact (MK_COMB (@lem5760801) (@lem5760800 _120607 op)). Qed.
Lemma lem5760803 {_120607 : Type'} (op : type1400 _120607) : (term936 _120607 op) = (term1400 _120607 op).
Proof. exact (MK_COMB (@lem5760802 _120607 op) (@lem5760757 _120607 op)). Qed.
Lemma lem5760804 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5760809 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760810 {_120607 : Type'} (f : type403 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> Prop) f x).
Proof. exact (@lem5760809 (type1400 _120607) Prop f x). Qed.
Lemma lem5760812 {_120607 : Type'} (op : type1400 _120607) : (@monoidal _120607 op) = (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op).
Proof. exact (@lem5760810 _120607 (@monoidal _120607) op). Qed.
Lemma lem5760813 {_120607 : Type'} (op : type1400 _120607) : (term1401 _120607 op) = (term1402 _120607 op).
Proof. exact (MK_COMB (@lem5760804) (@lem5760812 _120607 op)). Qed.
Lemma lem5760814 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5760815 {_120607 : Type'} (op : type1400 _120607) : (term1052 _120607 op) = (term1403 _120607 op).
Proof. exact (MK_COMB (@lem5760814) (@lem5760813 _120607 op)). Qed.
Lemma lem5760816 {_120607 : Type'} (op : type1400 _120607) : (term1053 _120607 op) = (term1404 _120607 op).
Proof. exact (MK_COMB (@lem5760815 _120607 op) (@lem5760803 _120607 op)). Qed.
Lemma lem5760817 {_120607 : Type'} : (term1068 _120607) = (term1405 _120607).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5760816 _120607 op)). Qed.
Lemma lem5760818 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5760819 {_120607 : Type'} : (term1083 _120607) = (term1406 _120607).
Proof. exact (MK_COMB (@lem5760818 _120607) (@lem5760817 _120607)). Qed.
Lemma lem5760820 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5760821 {_120607 : Type'} : (@eq _120607) = (@eq _120607).
Proof. exact (eq_refl (@eq _120607)). Qed.
Lemma lem5760822 {_120607 : Type'} (op : type1400 _120607) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5760827 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760828 {_120607 : Type'} (f : type402 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> _120607) f x).
Proof. exact (@lem5760827 (type1400 _120607) _120607 f x). Qed.
Lemma lem5760830 {_120607 : Type'} (op : type1400 _120607) : (@neutral _120607 op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) (@neutral _120607) op).
Proof. exact (@lem5760828 _120607 (@neutral _120607) op). Qed.
Lemma lem5760835 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760836 {_120607 : Type'} (f : type402 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> _120607) f x).
Proof. exact (@lem5760835 (type1400 _120607) _120607 f x). Qed.
Lemma lem5760838 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (x op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) x op).
Proof. exact (@lem5760836 _120607 x op). Qed.
Lemma lem5760839 {_120607 : Type'} (op : type1400 _120607) : (term1363 _120607 op) = (term1364 _120607 op).
Proof. exact (MK_COMB (@lem5760822 _120607 op) (@lem5760830 _120607 op)). Qed.
Lemma lem5760840 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1407 _120607 x op) = (term1408 _120607 x op).
Proof. exact (MK_COMB (@lem5760839 _120607 op) (@lem5760838 _120607 x op)). Qed.
Lemma lem5760842 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760843 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5760842 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5760844 {_120607 : Type'} (op : type1400 _120607) : (term1364 _120607 op) = (term1366 _120607 op).
Proof. exact (@lem5760843 _120607 op (@I ((_120607 -> _120607 -> _120607) -> _120607) (@neutral _120607) op)). Qed.
Lemma lem5760845 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (@I ((_120607 -> _120607 -> _120607) -> _120607) x op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) x op).
Proof. exact (eq_refl (@I ((_120607 -> _120607 -> _120607) -> _120607) x op)). Qed.
Lemma lem5760846 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1408 _120607 x op) = (term1409 _120607 x op).
Proof. exact (MK_COMB (@lem5760844 _120607 op) (@lem5760845 _120607 x op)). Qed.
Lemma lem5760848 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760849 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5760848 _120607 _120607 f x). Qed.
Lemma lem5760850 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1409 _120607 x op) = (term1410 _120607 x op).
Proof. exact (@lem5760849 _120607 (term1366 _120607 op) (@I ((_120607 -> _120607 -> _120607) -> _120607) x op)). Qed.
Lemma lem5760851 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1408 _120607 x op) = (term1410 _120607 x op).
Proof. exact (TRANS (@lem5760846 _120607 x op) (@lem5760850 _120607 x op)). Qed.
Lemma lem5760852 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1407 _120607 x op) = (term1410 _120607 x op).
Proof. exact (TRANS (@lem5760840 _120607 x op) (@lem5760851 _120607 x op)). Qed.
Lemma lem5760857 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760858 {_120607 : Type'} (f : type402 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> _120607) f x).
Proof. exact (@lem5760857 (type1400 _120607) _120607 f x). Qed.
Lemma lem5760860 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (x op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) x op).
Proof. exact (@lem5760858 _120607 x op). Qed.
Lemma lem5760861 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1411 _120607 x op) = (term1412 _120607 x op).
Proof. exact (MK_COMB (@lem5760821 _120607) (@lem5760852 _120607 x op)). Qed.
Lemma lem5760862 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : ((term1407 _120607 x op) = (x op)) = ((term1410 _120607 x op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) x op)).
Proof. exact (MK_COMB (@lem5760861 _120607 x op) (@lem5760860 _120607 x op)). Qed.
Lemma lem5760863 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1413 _120607 x op) = (term1414 _120607 x op).
Proof. exact (MK_COMB (@lem5760820) (@lem5760862 _120607 x op)). Qed.
Lemma lem5760864 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5760865 {_120607 : Type'} : (@eq _120607) = (@eq _120607).
Proof. exact (eq_refl (@eq _120607)). Qed.
Lemma lem5760866 {_120607 : Type'} (op : type1400 _120607) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5760871 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760872 {_120607 : Type'} (f : type402 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> _120607) f x).
Proof. exact (@lem5760871 (type1400 _120607) _120607 f x). Qed.
Lemma lem5760874 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (x op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) x op).
Proof. exact (@lem5760872 _120607 x op). Qed.
Lemma lem5760875 {_120607 : Type'} (op : type1400 _120607) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5760880 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760881 {_120607 : Type'} (f : type402 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> _120607) f x).
Proof. exact (@lem5760880 (type1400 _120607) _120607 f x). Qed.
Lemma lem5760883 {_120607 : Type'} (y : type402 _120607) (op : type1400 _120607) : (y op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) y op).
Proof. exact (@lem5760881 _120607 y op). Qed.
Lemma lem5760888 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760889 {_120607 : Type'} (f : type402 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> _120607) f x).
Proof. exact (@lem5760888 (type1400 _120607) _120607 f x). Qed.
Lemma lem5760891 {_120607 : Type'} (z : type402 _120607) (op : type1400 _120607) : (z op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) z op).
Proof. exact (@lem5760889 _120607 z op). Qed.
Lemma lem5760892 {_120607 : Type'} (y : type402 _120607) (op : type1400 _120607) : (term1415 _120607 y op) = (term1416 _120607 y op).
Proof. exact (MK_COMB (@lem5760875 _120607 op) (@lem5760883 _120607 y op)). Qed.
Lemma lem5760893 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1417 _120607 y z op) = (term1418 _120607 y z op).
Proof. exact (MK_COMB (@lem5760892 _120607 y op) (@lem5760891 _120607 z op)). Qed.
Lemma lem5760895 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760896 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5760895 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5760897 {_120607 : Type'} (y : type402 _120607) (op : type1400 _120607) : (term1416 _120607 y op) = (term1419 _120607 y op).
Proof. exact (@lem5760896 _120607 op (@I ((_120607 -> _120607 -> _120607) -> _120607) y op)). Qed.
Lemma lem5760898 {_120607 : Type'} (z : type402 _120607) (op : type1400 _120607) : (@I ((_120607 -> _120607 -> _120607) -> _120607) z op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) z op).
Proof. exact (eq_refl (@I ((_120607 -> _120607 -> _120607) -> _120607) z op)). Qed.
Lemma lem5760899 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1418 _120607 y z op) = (term1420 _120607 y z op).
Proof. exact (MK_COMB (@lem5760897 _120607 y op) (@lem5760898 _120607 z op)). Qed.
Lemma lem5760901 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760902 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5760901 _120607 _120607 f x). Qed.
Lemma lem5760903 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1420 _120607 y z op) = (term1421 _120607 y z op).
Proof. exact (@lem5760902 _120607 (term1419 _120607 y op) (@I ((_120607 -> _120607 -> _120607) -> _120607) z op)). Qed.
Lemma lem5760904 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1418 _120607 y z op) = (term1421 _120607 y z op).
Proof. exact (TRANS (@lem5760899 _120607 y z op) (@lem5760903 _120607 y z op)). Qed.
Lemma lem5760905 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1417 _120607 y z op) = (term1421 _120607 y z op).
Proof. exact (TRANS (@lem5760893 _120607 y z op) (@lem5760904 _120607 y z op)). Qed.
Lemma lem5760906 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1415 _120607 x op) = (term1416 _120607 x op).
Proof. exact (MK_COMB (@lem5760866 _120607 op) (@lem5760874 _120607 x op)). Qed.
Lemma lem5760907 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1422 _120607 x y z op) = (term1423 _120607 x y z op).
Proof. exact (MK_COMB (@lem5760906 _120607 x op) (@lem5760905 _120607 y z op)). Qed.
Lemma lem5760909 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760910 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5760909 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5760911 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1416 _120607 x op) = (term1419 _120607 x op).
Proof. exact (@lem5760910 _120607 op (@I ((_120607 -> _120607 -> _120607) -> _120607) x op)). Qed.
Lemma lem5760912 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1421 _120607 y z op) = (term1421 _120607 y z op).
Proof. exact (eq_refl (term1421 _120607 y z op)). Qed.
Lemma lem5760913 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1423 _120607 x y z op) = (term1424 _120607 x y z op).
Proof. exact (MK_COMB (@lem5760911 _120607 x op) (@lem5760912 _120607 y z op)). Qed.
Lemma lem5760915 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760916 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5760915 _120607 _120607 f x). Qed.
Lemma lem5760917 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1424 _120607 x y z op) = (term1425 _120607 x y z op).
Proof. exact (@lem5760916 _120607 (term1419 _120607 x op) (term1421 _120607 y z op)). Qed.
Lemma lem5760918 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1423 _120607 x y z op) = (term1425 _120607 x y z op).
Proof. exact (TRANS (@lem5760913 _120607 x y z op) (@lem5760917 _120607 x y z op)). Qed.
Lemma lem5760919 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1422 _120607 x y z op) = (term1425 _120607 x y z op).
Proof. exact (TRANS (@lem5760907 _120607 x y z op) (@lem5760918 _120607 x y z op)). Qed.
Lemma lem5760920 {_120607 : Type'} (op : type1400 _120607) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5760921 {_120607 : Type'} (op : type1400 _120607) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5760926 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760927 {_120607 : Type'} (f : type402 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> _120607) f x).
Proof. exact (@lem5760926 (type1400 _120607) _120607 f x). Qed.
Lemma lem5760929 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (x op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) x op).
Proof. exact (@lem5760927 _120607 x op). Qed.
Lemma lem5760934 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760935 {_120607 : Type'} (f : type402 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> _120607) f x).
Proof. exact (@lem5760934 (type1400 _120607) _120607 f x). Qed.
Lemma lem5760937 {_120607 : Type'} (y : type402 _120607) (op : type1400 _120607) : (y op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) y op).
Proof. exact (@lem5760935 _120607 y op). Qed.
Lemma lem5760938 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1415 _120607 x op) = (term1416 _120607 x op).
Proof. exact (MK_COMB (@lem5760921 _120607 op) (@lem5760929 _120607 x op)). Qed.
Lemma lem5760939 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (op : type1400 _120607) : (term1417 _120607 x y op) = (term1418 _120607 x y op).
Proof. exact (MK_COMB (@lem5760938 _120607 x op) (@lem5760937 _120607 y op)). Qed.
Lemma lem5760941 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760942 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5760941 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5760943 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1416 _120607 x op) = (term1419 _120607 x op).
Proof. exact (@lem5760942 _120607 op (@I ((_120607 -> _120607 -> _120607) -> _120607) x op)). Qed.
Lemma lem5760944 {_120607 : Type'} (y : type402 _120607) (op : type1400 _120607) : (@I ((_120607 -> _120607 -> _120607) -> _120607) y op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) y op).
Proof. exact (eq_refl (@I ((_120607 -> _120607 -> _120607) -> _120607) y op)). Qed.
Lemma lem5760945 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (op : type1400 _120607) : (term1418 _120607 x y op) = (term1420 _120607 x y op).
Proof. exact (MK_COMB (@lem5760943 _120607 x op) (@lem5760944 _120607 y op)). Qed.
Lemma lem5760947 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760948 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5760947 _120607 _120607 f x). Qed.
Lemma lem5760949 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (op : type1400 _120607) : (term1420 _120607 x y op) = (term1421 _120607 x y op).
Proof. exact (@lem5760948 _120607 (term1419 _120607 x op) (@I ((_120607 -> _120607 -> _120607) -> _120607) y op)). Qed.
Lemma lem5760950 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (op : type1400 _120607) : (term1418 _120607 x y op) = (term1421 _120607 x y op).
Proof. exact (TRANS (@lem5760945 _120607 x y op) (@lem5760949 _120607 x y op)). Qed.
Lemma lem5760951 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (op : type1400 _120607) : (term1417 _120607 x y op) = (term1421 _120607 x y op).
Proof. exact (TRANS (@lem5760939 _120607 x y op) (@lem5760950 _120607 x y op)). Qed.
Lemma lem5760956 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760957 {_120607 : Type'} (f : type402 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> _120607) f x).
Proof. exact (@lem5760956 (type1400 _120607) _120607 f x). Qed.
Lemma lem5760959 {_120607 : Type'} (z : type402 _120607) (op : type1400 _120607) : (z op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) z op).
Proof. exact (@lem5760957 _120607 z op). Qed.
Lemma lem5760960 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (op : type1400 _120607) : (term1426 _120607 x y op) = (term1427 _120607 x y op).
Proof. exact (MK_COMB (@lem5760920 _120607 op) (@lem5760951 _120607 x y op)). Qed.
Lemma lem5760961 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1428 _120607 x y z op) = (term1429 _120607 x y z op).
Proof. exact (MK_COMB (@lem5760960 _120607 x y op) (@lem5760959 _120607 z op)). Qed.
Lemma lem5760963 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760964 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5760963 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5760965 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (op : type1400 _120607) : (term1427 _120607 x y op) = (term1430 _120607 x y op).
Proof. exact (@lem5760964 _120607 op (term1421 _120607 x y op)). Qed.
Lemma lem5760966 {_120607 : Type'} (z : type402 _120607) (op : type1400 _120607) : (@I ((_120607 -> _120607 -> _120607) -> _120607) z op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) z op).
Proof. exact (eq_refl (@I ((_120607 -> _120607 -> _120607) -> _120607) z op)). Qed.
Lemma lem5760967 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1429 _120607 x y z op) = (term1431 _120607 x y z op).
Proof. exact (MK_COMB (@lem5760965 _120607 x y op) (@lem5760966 _120607 z op)). Qed.
Lemma lem5760969 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760970 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5760969 _120607 _120607 f x). Qed.
Lemma lem5760971 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1431 _120607 x y z op) = (term1432 _120607 x y z op).
Proof. exact (@lem5760970 _120607 (term1430 _120607 x y op) (@I ((_120607 -> _120607 -> _120607) -> _120607) z op)). Qed.
Lemma lem5760972 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1429 _120607 x y z op) = (term1432 _120607 x y z op).
Proof. exact (TRANS (@lem5760967 _120607 x y z op) (@lem5760971 _120607 x y z op)). Qed.
Lemma lem5760973 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1428 _120607 x y z op) = (term1432 _120607 x y z op).
Proof. exact (TRANS (@lem5760961 _120607 x y z op) (@lem5760972 _120607 x y z op)). Qed.
Lemma lem5760974 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1433 _120607 x y z op) = (term1434 _120607 x y z op).
Proof. exact (MK_COMB (@lem5760865 _120607) (@lem5760919 _120607 x y z op)). Qed.
Lemma lem5760975 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : ((term1422 _120607 x y z op) = (term1428 _120607 x y z op)) = ((term1425 _120607 x y z op) = (term1432 _120607 x y z op)).
Proof. exact (MK_COMB (@lem5760974 _120607 x y z op) (@lem5760973 _120607 x y z op)). Qed.
Lemma lem5760976 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1435 _120607 x y z op) = (term1436 _120607 x y z op).
Proof. exact (MK_COMB (@lem5760864) (@lem5760975 _120607 x y z op)). Qed.
Lemma lem5760977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5760978 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (z : type402 _120607) (op : type1400 _120607) : (term1437 _120607 x y z op) = (term1438 _120607 x y z op).
Proof. exact (MK_COMB (@lem5760977) (@lem5760976 _120607 x y z op)). Qed.
Lemma lem5760979 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1439 _120607 y z x op) = (term1440 _120607 y z x op).
Proof. exact (MK_COMB (@lem5760978 _120607 x y z op) (@lem5760863 _120607 x op)). Qed.
Lemma lem5760980 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5760981 {_120607 : Type'} : (@eq _120607) = (@eq _120607).
Proof. exact (eq_refl (@eq _120607)). Qed.
Lemma lem5760982 {_120607 : Type'} (op : type1400 _120607) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5760987 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760988 {_120607 : Type'} (f : type402 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> _120607) f x).
Proof. exact (@lem5760987 (type1400 _120607) _120607 f x). Qed.
Lemma lem5760990 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (x op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) x op).
Proof. exact (@lem5760988 _120607 x op). Qed.
Lemma lem5760995 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5760996 {_120607 : Type'} (f : type402 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> _120607) f x).
Proof. exact (@lem5760995 (type1400 _120607) _120607 f x). Qed.
Lemma lem5760998 {_120607 : Type'} (y : type402 _120607) (op : type1400 _120607) : (y op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) y op).
Proof. exact (@lem5760996 _120607 y op). Qed.
Lemma lem5760999 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1415 _120607 x op) = (term1416 _120607 x op).
Proof. exact (MK_COMB (@lem5760982 _120607 op) (@lem5760990 _120607 x op)). Qed.
Lemma lem5761000 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (op : type1400 _120607) : (term1417 _120607 x y op) = (term1418 _120607 x y op).
Proof. exact (MK_COMB (@lem5760999 _120607 x op) (@lem5760998 _120607 y op)). Qed.
Lemma lem5761002 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761003 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5761002 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5761004 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (term1416 _120607 x op) = (term1419 _120607 x op).
Proof. exact (@lem5761003 _120607 op (@I ((_120607 -> _120607 -> _120607) -> _120607) x op)). Qed.
Lemma lem5761005 {_120607 : Type'} (y : type402 _120607) (op : type1400 _120607) : (@I ((_120607 -> _120607 -> _120607) -> _120607) y op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) y op).
Proof. exact (eq_refl (@I ((_120607 -> _120607 -> _120607) -> _120607) y op)). Qed.
Lemma lem5761006 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (op : type1400 _120607) : (term1418 _120607 x y op) = (term1420 _120607 x y op).
Proof. exact (MK_COMB (@lem5761004 _120607 x op) (@lem5761005 _120607 y op)). Qed.
Lemma lem5761008 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761009 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5761008 _120607 _120607 f x). Qed.
Lemma lem5761010 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (op : type1400 _120607) : (term1420 _120607 x y op) = (term1421 _120607 x y op).
Proof. exact (@lem5761009 _120607 (term1419 _120607 x op) (@I ((_120607 -> _120607 -> _120607) -> _120607) y op)). Qed.
Lemma lem5761011 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (op : type1400 _120607) : (term1418 _120607 x y op) = (term1421 _120607 x y op).
Proof. exact (TRANS (@lem5761006 _120607 x y op) (@lem5761010 _120607 x y op)). Qed.
Lemma lem5761012 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (op : type1400 _120607) : (term1417 _120607 x y op) = (term1421 _120607 x y op).
Proof. exact (TRANS (@lem5761000 _120607 x y op) (@lem5761011 _120607 x y op)). Qed.
Lemma lem5761013 {_120607 : Type'} (op : type1400 _120607) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5761018 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761019 {_120607 : Type'} (f : type402 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> _120607) f x).
Proof. exact (@lem5761018 (type1400 _120607) _120607 f x). Qed.
Lemma lem5761021 {_120607 : Type'} (y : type402 _120607) (op : type1400 _120607) : (y op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) y op).
Proof. exact (@lem5761019 _120607 y op). Qed.
Lemma lem5761026 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761027 {_120607 : Type'} (f : type402 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> _120607) f x).
Proof. exact (@lem5761026 (type1400 _120607) _120607 f x). Qed.
Lemma lem5761029 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (x op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) x op).
Proof. exact (@lem5761027 _120607 x op). Qed.
Lemma lem5761030 {_120607 : Type'} (y : type402 _120607) (op : type1400 _120607) : (term1415 _120607 y op) = (term1416 _120607 y op).
Proof. exact (MK_COMB (@lem5761013 _120607 op) (@lem5761021 _120607 y op)). Qed.
Lemma lem5761031 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1417 _120607 y x op) = (term1418 _120607 y x op).
Proof. exact (MK_COMB (@lem5761030 _120607 y op) (@lem5761029 _120607 x op)). Qed.
Lemma lem5761033 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761034 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5761033 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5761035 {_120607 : Type'} (y : type402 _120607) (op : type1400 _120607) : (term1416 _120607 y op) = (term1419 _120607 y op).
Proof. exact (@lem5761034 _120607 op (@I ((_120607 -> _120607 -> _120607) -> _120607) y op)). Qed.
Lemma lem5761036 {_120607 : Type'} (x : type402 _120607) (op : type1400 _120607) : (@I ((_120607 -> _120607 -> _120607) -> _120607) x op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) x op).
Proof. exact (eq_refl (@I ((_120607 -> _120607 -> _120607) -> _120607) x op)). Qed.
Lemma lem5761037 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1418 _120607 y x op) = (term1420 _120607 y x op).
Proof. exact (MK_COMB (@lem5761035 _120607 y op) (@lem5761036 _120607 x op)). Qed.
Lemma lem5761039 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761040 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5761039 _120607 _120607 f x). Qed.
Lemma lem5761041 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1420 _120607 y x op) = (term1421 _120607 y x op).
Proof. exact (@lem5761040 _120607 (term1419 _120607 y op) (@I ((_120607 -> _120607 -> _120607) -> _120607) x op)). Qed.
Lemma lem5761042 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1418 _120607 y x op) = (term1421 _120607 y x op).
Proof. exact (TRANS (@lem5761037 _120607 y x op) (@lem5761041 _120607 y x op)). Qed.
Lemma lem5761043 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1417 _120607 y x op) = (term1421 _120607 y x op).
Proof. exact (TRANS (@lem5761031 _120607 y x op) (@lem5761042 _120607 y x op)). Qed.
Lemma lem5761044 {_120607 : Type'} (x : type402 _120607) (y : type402 _120607) (op : type1400 _120607) : (term1441 _120607 x y op) = (term1442 _120607 x y op).
Proof. exact (MK_COMB (@lem5760981 _120607) (@lem5761012 _120607 x y op)). Qed.
Lemma lem5761045 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : ((term1417 _120607 x y op) = (term1417 _120607 y x op)) = ((term1421 _120607 x y op) = (term1421 _120607 y x op)).
Proof. exact (MK_COMB (@lem5761044 _120607 x y op) (@lem5761043 _120607 y x op)). Qed.
Lemma lem5761046 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1443 _120607 y x op) = (term1444 _120607 y x op).
Proof. exact (MK_COMB (@lem5760980) (@lem5761045 _120607 y x op)). Qed.
Lemma lem5761047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5761048 {_120607 : Type'} (y : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1445 _120607 y x op) = (term1446 _120607 y x op).
Proof. exact (MK_COMB (@lem5761047) (@lem5761046 _120607 y x op)). Qed.
Lemma lem5761049 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1447 _120607 y z x op) = (term1448 _120607 y z x op).
Proof. exact (MK_COMB (@lem5761048 _120607 y x op) (@lem5760979 _120607 y z x op)). Qed.
Lemma lem5761054 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761055 {_120607 : Type'} (f : type403 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> Prop) f x).
Proof. exact (@lem5761054 (type1400 _120607) Prop f x). Qed.
Lemma lem5761057 {_120607 : Type'} (op : type1400 _120607) : (@monoidal _120607 op) = (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op).
Proof. exact (@lem5761055 _120607 (@monoidal _120607) op). Qed.
Lemma lem5761058 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5761059 {_120607 : Type'} (op : type1400 _120607) : (term1054 _120607 op) = (term1449 _120607 op).
Proof. exact (MK_COMB (@lem5761058) (@lem5761057 _120607 op)). Qed.
Lemma lem5761060 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (op : type1400 _120607) : (term1298 _120607 y z x op) = (term1450 _120607 y z x op).
Proof. exact (MK_COMB (@lem5761059 _120607 op) (@lem5761049 _120607 y z x op)). Qed.
Lemma lem5761061 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) : (term1300 _120607 y z x) = (term1451 _120607 y z x).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5761060 _120607 y z x op)). Qed.
Lemma lem5761062 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5761063 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) : (term1302 _120607 y z x) = (term1452 _120607 y z x).
Proof. exact (MK_COMB (@lem5761062 _120607) (@lem5761061 _120607 y z x)). Qed.
Lemma lem5761064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761065 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) : (term1353 _120607 y z x) = (term1453 _120607 y z x).
Proof. exact (MK_COMB (@lem5761064) (@lem5761063 _120607 y z x)). Qed.
Lemma lem5761066 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) : (term1355 _120607 y z x) = (term1454 _120607 y z x).
Proof. exact (MK_COMB (@lem5761065 _120607 y z x) (@lem5760819 _120607)). Qed.
Lemma lem5761067 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1454 _120607 y z x.
Proof. exact (EQ_MP (@lem5761066 _120607 y z x) (@lem5760625 _120607 y z x h1)). Qed.
Lemma lem5761068 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5761069 {_120607 : Type'} : (@eq _120607) = (@eq _120607).
Proof. exact (eq_refl (@eq _120607)). Qed.
Lemma lem5761070 {_120607 : Type'} (op : type1400 _120607) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5761075 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761076 {_120592 _120607 : Type'} (f : _120592 -> _120607) (x : _120592) : (f x) = (@I (_120592 -> _120607) f x).
Proof. exact (@lem5761075 _120592 _120607 f x). Qed.
Lemma lem5761078 {_120592 _120607 : Type'} (f : _120592 -> _120607) (x' : _120592) : (f x') = (@I (_120592 -> _120607) f x').
Proof. exact (@lem5761076 _120592 _120607 f x'). Qed.
Lemma lem5761079 {_120607 : Type'} (op : type1400 _120607) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5761088 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761089 {_120592 _120607 : Type'} (f : type750 _120592 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761088 (type1400 _120607) (type632 _120592 _120607) f x). Qed.
Lemma lem5761090 {_120592 _120607 : Type'} (op : type1400 _120607) : (@iterate _120607 _120592 op) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op).
Proof. exact (@lem5761089 _120592 _120607 (@iterate _120607 _120592) op). Qed.
Lemma lem5761091 {_120592 : Type'} (s : _120592 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5761092 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (@iterate _120607 _120592 op s) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op s).
Proof. exact (MK_COMB (@lem5761090 _120592 _120607 op) (@lem5761091 _120592 s)). Qed.
Lemma lem5761094 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761095 {_120592 _120607 : Type'} (f : type632 _120592 _120607) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761094 (_120592 -> Prop) (type570 _120592 _120607) f x). Qed.
Lemma lem5761096 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op s) = (term1455 _120592 _120607 op s).
Proof. exact (@lem5761095 _120592 _120607 (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op) s). Qed.
Lemma lem5761097 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (@iterate _120607 _120592 op s) = (term1455 _120592 _120607 op s).
Proof. exact (TRANS (@lem5761092 _120592 _120607 op s) (@lem5761096 _120592 _120607 op s)). Qed.
Lemma lem5761098 {_120592 _120607 : Type'} (f : _120592 -> _120607) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5761099 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op s f) = (term1456 _120592 _120607 op s f).
Proof. exact (MK_COMB (@lem5761097 _120592 _120607 op s) (@lem5761098 _120592 _120607 f)). Qed.
Lemma lem5761101 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761102 {_120592 _120607 : Type'} (f : type570 _120592 _120607) (x : _120592 -> _120607) : (f x) = (@I ((_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761101 (_120592 -> _120607) _120607 f x). Qed.
Lemma lem5761103 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term1456 _120592 _120607 op s f) = (term1457 _120592 _120607 op s f).
Proof. exact (@lem5761102 _120592 _120607 (term1455 _120592 _120607 op s) f). Qed.
Lemma lem5761105 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op s f) = (term1457 _120592 _120607 op s f).
Proof. exact (TRANS (@lem5761099 _120592 _120607 op s f) (@lem5761103 _120592 _120607 op s f)). Qed.
Lemma lem5761114 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761115 {_120592 _120607 : Type'} (f : type750 _120592 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761114 (type1400 _120607) (type632 _120592 _120607) f x). Qed.
Lemma lem5761116 {_120592 _120607 : Type'} (op : type1400 _120607) : (@iterate _120607 _120592 op) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op).
Proof. exact (@lem5761115 _120592 _120607 (@iterate _120607 _120592) op). Qed.
Lemma lem5761117 {_120592 : Type'} (t : _120592 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5761118 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) : (@iterate _120607 _120592 op t) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op t).
Proof. exact (MK_COMB (@lem5761116 _120592 _120607 op) (@lem5761117 _120592 t)). Qed.
Lemma lem5761120 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761121 {_120592 _120607 : Type'} (f : type632 _120592 _120607) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761120 (_120592 -> Prop) (type570 _120592 _120607) f x). Qed.
Lemma lem5761122 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) : (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op t) = (term1455 _120592 _120607 op t).
Proof. exact (@lem5761121 _120592 _120607 (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op) t). Qed.
Lemma lem5761123 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) : (@iterate _120607 _120592 op t) = (term1455 _120592 _120607 op t).
Proof. exact (TRANS (@lem5761118 _120592 _120607 op t) (@lem5761122 _120592 _120607 op t)). Qed.
Lemma lem5761124 {_120592 _120607 : Type'} (f : _120592 -> _120607) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5761125 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op t f) = (term1456 _120592 _120607 op t f).
Proof. exact (MK_COMB (@lem5761123 _120592 _120607 op t) (@lem5761124 _120592 _120607 f)). Qed.
Lemma lem5761127 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761128 {_120592 _120607 : Type'} (f : type570 _120592 _120607) (x : _120592 -> _120607) : (f x) = (@I ((_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761127 (_120592 -> _120607) _120607 f x). Qed.
Lemma lem5761129 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1456 _120592 _120607 op t f) = (term1457 _120592 _120607 op t f).
Proof. exact (@lem5761128 _120592 _120607 (term1455 _120592 _120607 op t) f). Qed.
Lemma lem5761131 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op t f) = (term1457 _120592 _120607 op t f).
Proof. exact (TRANS (@lem5761125 _120592 _120607 op t f) (@lem5761129 _120592 _120607 op t f)). Qed.
Lemma lem5761132 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term803 _120592 _120607 op s f) = (term1458 _120592 _120607 op s f).
Proof. exact (MK_COMB (@lem5761079 _120607 op) (@lem5761105 _120592 _120607 op s f)). Qed.
Lemma lem5761133 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term700 _120592 _120607 s op t f) = (term1459 _120592 _120607 s op t f).
Proof. exact (MK_COMB (@lem5761132 _120592 _120607 op s f) (@lem5761131 _120592 _120607 op t f)). Qed.
Lemma lem5761135 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761136 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5761135 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5761137 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term1458 _120592 _120607 op s f) = (term1460 _120592 _120607 op s f).
Proof. exact (@lem5761136 _120607 op (term1457 _120592 _120607 op s f)). Qed.
Lemma lem5761138 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1457 _120592 _120607 op t f) = (term1457 _120592 _120607 op t f).
Proof. exact (eq_refl (term1457 _120592 _120607 op t f)). Qed.
Lemma lem5761139 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1459 _120592 _120607 s op t f) = (term1461 _120592 _120607 s op t f).
Proof. exact (MK_COMB (@lem5761137 _120592 _120607 op s f) (@lem5761138 _120592 _120607 op t f)). Qed.
Lemma lem5761141 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761142 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5761141 _120607 _120607 f x). Qed.
Lemma lem5761143 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1461 _120592 _120607 s op t f) = (term1462 _120592 _120607 s op t f).
Proof. exact (@lem5761142 _120607 (term1460 _120592 _120607 op s f) (term1457 _120592 _120607 op t f)). Qed.
Lemma lem5761144 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1459 _120592 _120607 s op t f) = (term1462 _120592 _120607 s op t f).
Proof. exact (TRANS (@lem5761139 _120592 _120607 s op t f) (@lem5761143 _120592 _120607 s op t f)). Qed.
Lemma lem5761145 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term700 _120592 _120607 s op t f) = (term1462 _120592 _120607 s op t f).
Proof. exact (TRANS (@lem5761133 _120592 _120607 s op t f) (@lem5761144 _120592 _120607 s op t f)). Qed.
Lemma lem5761146 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) (x' : _120592) : (term852 _120592 _120607 op f x') = (term1463 _120592 _120607 op f x').
Proof. exact (MK_COMB (@lem5761070 _120607 op) (@lem5761078 _120592 _120607 f x')). Qed.
Lemma lem5761147 {_120592 _120607 : Type'} (x' : _120592) (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term853 _120592 _120607 x' s op t f) = (term1464 _120592 _120607 x' s op t f).
Proof. exact (MK_COMB (@lem5761146 _120592 _120607 op f x') (@lem5761145 _120592 _120607 s op t f)). Qed.
Lemma lem5761149 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761150 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5761149 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5761151 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) (x' : _120592) : (term1463 _120592 _120607 op f x') = (term1465 _120592 _120607 op f x').
Proof. exact (@lem5761150 _120607 op (@I (_120592 -> _120607) f x')). Qed.
Lemma lem5761152 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1462 _120592 _120607 s op t f) = (term1462 _120592 _120607 s op t f).
Proof. exact (eq_refl (term1462 _120592 _120607 s op t f)). Qed.
Lemma lem5761153 {_120592 _120607 : Type'} (x' : _120592) (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1464 _120592 _120607 x' s op t f) = (term1466 _120592 _120607 x' s op t f).
Proof. exact (MK_COMB (@lem5761151 _120592 _120607 op f x') (@lem5761152 _120592 _120607 s op t f)). Qed.
Lemma lem5761155 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761156 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5761155 _120607 _120607 f x). Qed.
Lemma lem5761157 {_120592 _120607 : Type'} (x' : _120592) (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1466 _120592 _120607 x' s op t f) = (term1467 _120592 _120607 x' s op t f).
Proof. exact (@lem5761156 _120607 (term1465 _120592 _120607 op f x') (term1462 _120592 _120607 s op t f)). Qed.
Lemma lem5761158 {_120592 _120607 : Type'} (x' : _120592) (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1464 _120592 _120607 x' s op t f) = (term1467 _120592 _120607 x' s op t f).
Proof. exact (TRANS (@lem5761153 _120592 _120607 x' s op t f) (@lem5761157 _120592 _120607 x' s op t f)). Qed.
Lemma lem5761159 {_120592 _120607 : Type'} (x' : _120592) (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term853 _120592 _120607 x' s op t f) = (term1467 _120592 _120607 x' s op t f).
Proof. exact (TRANS (@lem5761147 _120592 _120607 x' s op t f) (@lem5761158 _120592 _120607 x' s op t f)). Qed.
Lemma lem5761160 {_120607 : Type'} (op : type1400 _120607) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5761169 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761170 {_120592 _120607 : Type'} (f : type750 _120592 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761169 (type1400 _120607) (type632 _120592 _120607) f x). Qed.
Lemma lem5761171 {_120592 _120607 : Type'} (op : type1400 _120607) : (@iterate _120607 _120592 op) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op).
Proof. exact (@lem5761170 _120592 _120607 (@iterate _120607 _120592) op). Qed.
Lemma lem5761172 {_120592 : Type'} (s : _120592 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5761173 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (@iterate _120607 _120592 op s) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op s).
Proof. exact (MK_COMB (@lem5761171 _120592 _120607 op) (@lem5761172 _120592 s)). Qed.
Lemma lem5761175 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761176 {_120592 _120607 : Type'} (f : type632 _120592 _120607) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761175 (_120592 -> Prop) (type570 _120592 _120607) f x). Qed.
Lemma lem5761177 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op s) = (term1455 _120592 _120607 op s).
Proof. exact (@lem5761176 _120592 _120607 (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op) s). Qed.
Lemma lem5761178 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (@iterate _120607 _120592 op s) = (term1455 _120592 _120607 op s).
Proof. exact (TRANS (@lem5761173 _120592 _120607 op s) (@lem5761177 _120592 _120607 op s)). Qed.
Lemma lem5761179 {_120592 _120607 : Type'} (f : _120592 -> _120607) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5761180 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op s f) = (term1456 _120592 _120607 op s f).
Proof. exact (MK_COMB (@lem5761178 _120592 _120607 op s) (@lem5761179 _120592 _120607 f)). Qed.
Lemma lem5761182 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761183 {_120592 _120607 : Type'} (f : type570 _120592 _120607) (x : _120592 -> _120607) : (f x) = (@I ((_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761182 (_120592 -> _120607) _120607 f x). Qed.
Lemma lem5761184 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term1456 _120592 _120607 op s f) = (term1457 _120592 _120607 op s f).
Proof. exact (@lem5761183 _120592 _120607 (term1455 _120592 _120607 op s) f). Qed.
Lemma lem5761186 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op s f) = (term1457 _120592 _120607 op s f).
Proof. exact (TRANS (@lem5761180 _120592 _120607 op s f) (@lem5761184 _120592 _120607 op s f)). Qed.
Lemma lem5761187 {_120607 : Type'} (op : type1400 _120607) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5761192 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761193 {_120592 _120607 : Type'} (f : _120592 -> _120607) (x : _120592) : (f x) = (@I (_120592 -> _120607) f x).
Proof. exact (@lem5761192 _120592 _120607 f x). Qed.
Lemma lem5761195 {_120592 _120607 : Type'} (f : _120592 -> _120607) (x' : _120592) : (f x') = (@I (_120592 -> _120607) f x').
Proof. exact (@lem5761193 _120592 _120607 f x'). Qed.
Lemma lem5761204 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761205 {_120592 _120607 : Type'} (f : type750 _120592 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761204 (type1400 _120607) (type632 _120592 _120607) f x). Qed.
Lemma lem5761206 {_120592 _120607 : Type'} (op : type1400 _120607) : (@iterate _120607 _120592 op) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op).
Proof. exact (@lem5761205 _120592 _120607 (@iterate _120607 _120592) op). Qed.
Lemma lem5761207 {_120592 : Type'} (t : _120592 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5761208 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) : (@iterate _120607 _120592 op t) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op t).
Proof. exact (MK_COMB (@lem5761206 _120592 _120607 op) (@lem5761207 _120592 t)). Qed.
Lemma lem5761210 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761211 {_120592 _120607 : Type'} (f : type632 _120592 _120607) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761210 (_120592 -> Prop) (type570 _120592 _120607) f x). Qed.
Lemma lem5761212 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) : (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op t) = (term1455 _120592 _120607 op t).
Proof. exact (@lem5761211 _120592 _120607 (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op) t). Qed.
Lemma lem5761213 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) : (@iterate _120607 _120592 op t) = (term1455 _120592 _120607 op t).
Proof. exact (TRANS (@lem5761208 _120592 _120607 op t) (@lem5761212 _120592 _120607 op t)). Qed.
Lemma lem5761214 {_120592 _120607 : Type'} (f : _120592 -> _120607) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5761215 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op t f) = (term1456 _120592 _120607 op t f).
Proof. exact (MK_COMB (@lem5761213 _120592 _120607 op t) (@lem5761214 _120592 _120607 f)). Qed.
Lemma lem5761217 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761218 {_120592 _120607 : Type'} (f : type570 _120592 _120607) (x : _120592 -> _120607) : (f x) = (@I ((_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761217 (_120592 -> _120607) _120607 f x). Qed.
Lemma lem5761219 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1456 _120592 _120607 op t f) = (term1457 _120592 _120607 op t f).
Proof. exact (@lem5761218 _120592 _120607 (term1455 _120592 _120607 op t) f). Qed.
Lemma lem5761221 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op t f) = (term1457 _120592 _120607 op t f).
Proof. exact (TRANS (@lem5761215 _120592 _120607 op t f) (@lem5761219 _120592 _120607 op t f)). Qed.
Lemma lem5761222 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) (x' : _120592) : (term852 _120592 _120607 op f x') = (term1463 _120592 _120607 op f x').
Proof. exact (MK_COMB (@lem5761187 _120607 op) (@lem5761195 _120592 _120607 f x')). Qed.
Lemma lem5761223 {_120592 _120607 : Type'} (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term863 _120592 _120607 x' op t f) = (term1468 _120592 _120607 x' op t f).
Proof. exact (MK_COMB (@lem5761222 _120592 _120607 op f x') (@lem5761221 _120592 _120607 op t f)). Qed.
Lemma lem5761225 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761226 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5761225 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5761227 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) (x' : _120592) : (term1463 _120592 _120607 op f x') = (term1465 _120592 _120607 op f x').
Proof. exact (@lem5761226 _120607 op (@I (_120592 -> _120607) f x')). Qed.
Lemma lem5761228 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1457 _120592 _120607 op t f) = (term1457 _120592 _120607 op t f).
Proof. exact (eq_refl (term1457 _120592 _120607 op t f)). Qed.
Lemma lem5761229 {_120592 _120607 : Type'} (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1468 _120592 _120607 x' op t f) = (term1469 _120592 _120607 x' op t f).
Proof. exact (MK_COMB (@lem5761227 _120592 _120607 op f x') (@lem5761228 _120592 _120607 op t f)). Qed.
Lemma lem5761231 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761232 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5761231 _120607 _120607 f x). Qed.
Lemma lem5761233 {_120592 _120607 : Type'} (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1469 _120592 _120607 x' op t f) = (term1470 _120592 _120607 x' op t f).
Proof. exact (@lem5761232 _120607 (term1465 _120592 _120607 op f x') (term1457 _120592 _120607 op t f)). Qed.
Lemma lem5761234 {_120592 _120607 : Type'} (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1468 _120592 _120607 x' op t f) = (term1470 _120592 _120607 x' op t f).
Proof. exact (TRANS (@lem5761229 _120592 _120607 x' op t f) (@lem5761233 _120592 _120607 x' op t f)). Qed.
Lemma lem5761235 {_120592 _120607 : Type'} (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term863 _120592 _120607 x' op t f) = (term1470 _120592 _120607 x' op t f).
Proof. exact (TRANS (@lem5761223 _120592 _120607 x' op t f) (@lem5761234 _120592 _120607 x' op t f)). Qed.
Lemma lem5761236 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term803 _120592 _120607 op s f) = (term1458 _120592 _120607 op s f).
Proof. exact (MK_COMB (@lem5761160 _120607 op) (@lem5761186 _120592 _120607 op s f)). Qed.
Lemma lem5761237 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term878 _120592 _120607 s x' op t f) = (term1471 _120592 _120607 s x' op t f).
Proof. exact (MK_COMB (@lem5761236 _120592 _120607 op s f) (@lem5761235 _120592 _120607 x' op t f)). Qed.
Lemma lem5761239 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761240 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5761239 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5761241 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term1458 _120592 _120607 op s f) = (term1460 _120592 _120607 op s f).
Proof. exact (@lem5761240 _120607 op (term1457 _120592 _120607 op s f)). Qed.
Lemma lem5761242 {_120592 _120607 : Type'} (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1470 _120592 _120607 x' op t f) = (term1470 _120592 _120607 x' op t f).
Proof. exact (eq_refl (term1470 _120592 _120607 x' op t f)). Qed.
Lemma lem5761243 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1471 _120592 _120607 s x' op t f) = (term1472 _120592 _120607 s x' op t f).
Proof. exact (MK_COMB (@lem5761241 _120592 _120607 op s f) (@lem5761242 _120592 _120607 x' op t f)). Qed.
Lemma lem5761245 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761246 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5761245 _120607 _120607 f x). Qed.
Lemma lem5761247 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1472 _120592 _120607 s x' op t f) = (term1473 _120592 _120607 s x' op t f).
Proof. exact (@lem5761246 _120607 (term1460 _120592 _120607 op s f) (term1470 _120592 _120607 x' op t f)). Qed.
Lemma lem5761248 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1471 _120592 _120607 s x' op t f) = (term1473 _120592 _120607 s x' op t f).
Proof. exact (TRANS (@lem5761243 _120592 _120607 s x' op t f) (@lem5761247 _120592 _120607 s x' op t f)). Qed.
Lemma lem5761249 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term878 _120592 _120607 s x' op t f) = (term1473 _120592 _120607 s x' op t f).
Proof. exact (TRANS (@lem5761237 _120592 _120607 s x' op t f) (@lem5761248 _120592 _120607 s x' op t f)). Qed.
Lemma lem5761250 {_120592 _120607 : Type'} (x' : _120592) (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term858 _120592 _120607 x' s op t f) = (term1474 _120592 _120607 x' s op t f).
Proof. exact (MK_COMB (@lem5761069 _120607) (@lem5761159 _120592 _120607 x' s op t f)). Qed.
Lemma lem5761251 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : ((term853 _120592 _120607 x' s op t f) = (term878 _120592 _120607 s x' op t f)) = ((term1467 _120592 _120607 x' s op t f) = (term1473 _120592 _120607 s x' op t f)).
Proof. exact (MK_COMB (@lem5761250 _120592 _120607 x' s op t f) (@lem5761249 _120592 _120607 s x' op t f)). Qed.
Lemma lem5761252 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1475 _120592 _120607 s x' op t f) = (term1476 _120592 _120607 s x' op t f).
Proof. exact (MK_COMB (@lem5761068) (@lem5761251 _120592 _120607 s x' op t f)). Qed.
Lemma lem5761259 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761260 {_120592 : Type'} (f : type639 _120592) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> Prop) f x).
Proof. exact (@lem5761259 (_120592 -> Prop) (type686 _120592) f x). Qed.
Lemma lem5761261 {_120592 : Type'} (s : _120592 -> Prop) : (@DISJOINT _120592 s) = (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> Prop) (@DISJOINT _120592) s).
Proof. exact (@lem5761260 _120592 (@DISJOINT _120592) s). Qed.
Lemma lem5761262 {_120592 : Type'} (t : _120592 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5761263 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (@DISJOINT _120592 s t) = (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> Prop) (@DISJOINT _120592) s t).
Proof. exact (MK_COMB (@lem5761261 _120592 s) (@lem5761262 _120592 t)). Qed.
Lemma lem5761265 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761266 {_120592 : Type'} (f : type686 _120592) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> Prop) f x).
Proof. exact (@lem5761265 (_120592 -> Prop) Prop f x). Qed.
Lemma lem5761267 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> Prop) (@DISJOINT _120592) s t) = (term1477 _120592 s t).
Proof. exact (@lem5761266 _120592 (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> Prop) (@DISJOINT _120592) s) t). Qed.
Lemma lem5761269 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (@DISJOINT _120592 s t) = (term1477 _120592 s t).
Proof. exact (TRANS (@lem5761263 _120592 s t) (@lem5761267 _120592 s t)). Qed.
Lemma lem5761270 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5761277 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761278 {_120592 : Type'} (f : type1364 _120592) (x : _120592) : (f x) = (@I (_120592 -> (_120592 -> Prop) -> Prop) f x).
Proof. exact (@lem5761277 _120592 (type686 _120592) f x). Qed.
Lemma lem5761279 {_120592 : Type'} (x' : _120592) : (@IN _120592 x') = (@I (_120592 -> (_120592 -> Prop) -> Prop) (@IN _120592) x').
Proof. exact (@lem5761278 _120592 (@IN _120592) x'). Qed.
Lemma lem5761280 {_120592 : Type'} (s : _120592 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5761281 {_120592 : Type'} (x' : _120592) (s : _120592 -> Prop) : (@IN _120592 x' s) = (@I (_120592 -> (_120592 -> Prop) -> Prop) (@IN _120592) x' s).
Proof. exact (MK_COMB (@lem5761279 _120592 x') (@lem5761280 _120592 s)). Qed.
Lemma lem5761283 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761284 {_120592 : Type'} (f : type686 _120592) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> Prop) f x).
Proof. exact (@lem5761283 (_120592 -> Prop) Prop f x). Qed.
Lemma lem5761285 {_120592 : Type'} (x' : _120592) (s : _120592 -> Prop) : (@I (_120592 -> (_120592 -> Prop) -> Prop) (@IN _120592) x' s) = (term1478 _120592 x' s).
Proof. exact (@lem5761284 _120592 (@I (_120592 -> (_120592 -> Prop) -> Prop) (@IN _120592) x') s). Qed.
Lemma lem5761287 {_120592 : Type'} (x' : _120592) (s : _120592 -> Prop) : (@IN _120592 x' s) = (term1478 _120592 x' s).
Proof. exact (TRANS (@lem5761281 _120592 x' s) (@lem5761285 _120592 x' s)). Qed.
Lemma lem5761288 {_120592 : Type'} (x' : _120592) (s : _120592 -> Prop) : (term52 _120592 x' s) = (term1479 _120592 x' s).
Proof. exact (MK_COMB (@lem5761270) (@lem5761287 _120592 x' s)). Qed.
Lemma lem5761289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761290 {_120592 : Type'} (x' : _120592) (s : _120592 -> Prop) : (term12 _120592 x' s) = (term1480 _120592 x' s).
Proof. exact (MK_COMB (@lem5761289) (@lem5761288 _120592 x' s)). Qed.
Lemma lem5761291 {_120592 : Type'} (x' : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) : (term13 _120592 x' s t) = (term1481 _120592 x' s t).
Proof. exact (MK_COMB (@lem5761290 _120592 x' s) (@lem5761269 _120592 s t)). Qed.
Lemma lem5761292 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761293 {_120592 : Type'} (x' : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) : (term1482 _120592 x' s t) = (term1483 _120592 x' s t).
Proof. exact (MK_COMB (@lem5761292) (@lem5761291 _120592 x' s t)). Qed.
Lemma lem5761294 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term945 _120592 _120607 s x' op t f) = (term1484 _120592 _120607 s x' op t f).
Proof. exact (MK_COMB (@lem5761293 _120592 x' s t) (@lem5761252 _120592 _120607 s x' op t f)). Qed.
Lemma lem5761299 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761300 {_120592 : Type'} (f : type686 _120592) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> Prop) f x).
Proof. exact (@lem5761299 (_120592 -> Prop) Prop f x). Qed.
Lemma lem5761302 {_120592 : Type'} (t : _120592 -> Prop) : (@FINITE _120592 t) = (@I ((_120592 -> Prop) -> Prop) (@FINITE _120592) t).
Proof. exact (@lem5761300 _120592 (@FINITE _120592) t). Qed.
Lemma lem5761303 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5761310 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761311 {_120592 : Type'} (f : type1364 _120592) (x : _120592) : (f x) = (@I (_120592 -> (_120592 -> Prop) -> Prop) f x).
Proof. exact (@lem5761310 _120592 (type686 _120592) f x). Qed.
Lemma lem5761312 {_120592 : Type'} (x' : _120592) : (@IN _120592 x') = (@I (_120592 -> (_120592 -> Prop) -> Prop) (@IN _120592) x').
Proof. exact (@lem5761311 _120592 (@IN _120592) x'). Qed.
Lemma lem5761313 {_120592 : Type'} (t : _120592 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5761314 {_120592 : Type'} (x' : _120592) (t : _120592 -> Prop) : (@IN _120592 x' t) = (@I (_120592 -> (_120592 -> Prop) -> Prop) (@IN _120592) x' t).
Proof. exact (MK_COMB (@lem5761312 _120592 x') (@lem5761313 _120592 t)). Qed.
Lemma lem5761316 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761317 {_120592 : Type'} (f : type686 _120592) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> Prop) f x).
Proof. exact (@lem5761316 (_120592 -> Prop) Prop f x). Qed.
Lemma lem5761318 {_120592 : Type'} (x' : _120592) (t : _120592 -> Prop) : (@I (_120592 -> (_120592 -> Prop) -> Prop) (@IN _120592) x' t) = (term1478 _120592 x' t).
Proof. exact (@lem5761317 _120592 (@I (_120592 -> (_120592 -> Prop) -> Prop) (@IN _120592) x') t). Qed.
Lemma lem5761320 {_120592 : Type'} (x' : _120592) (t : _120592 -> Prop) : (@IN _120592 x' t) = (term1478 _120592 x' t).
Proof. exact (TRANS (@lem5761314 _120592 x' t) (@lem5761318 _120592 x' t)). Qed.
Lemma lem5761321 {_120592 : Type'} (x' : _120592) (t : _120592 -> Prop) : (term52 _120592 x' t) = (term1479 _120592 x' t).
Proof. exact (MK_COMB (@lem5761303) (@lem5761320 _120592 x' t)). Qed.
Lemma lem5761322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761323 {_120592 : Type'} (x' : _120592) (t : _120592 -> Prop) : (term12 _120592 x' t) = (term1480 _120592 x' t).
Proof. exact (MK_COMB (@lem5761322) (@lem5761321 _120592 x' t)). Qed.
Lemma lem5761324 {_120592 : Type'} (x' : _120592) (t : _120592 -> Prop) : (term733 _120592 x' t) = (term1485 _120592 x' t).
Proof. exact (MK_COMB (@lem5761323 _120592 x' t) (@lem5761302 _120592 t)). Qed.
Lemma lem5761325 {_120607 : Type'} : (@eq _120607) = (@eq _120607).
Proof. exact (eq_refl (@eq _120607)). Qed.
Lemma lem5761334 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761335 {_120592 : Type'} (f : type636 _120592) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> _120592 -> Prop) f x).
Proof. exact (@lem5761334 (_120592 -> Prop) (type672 _120592) f x). Qed.
Lemma lem5761336 {_120592 : Type'} (s : _120592 -> Prop) : (@UNION _120592 s) = (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> _120592 -> Prop) (@UNION _120592) s).
Proof. exact (@lem5761335 _120592 (@UNION _120592) s). Qed.
Lemma lem5761337 {_120592 : Type'} (t : _120592 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5761338 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (@UNION _120592 s t) = (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> _120592 -> Prop) (@UNION _120592) s t).
Proof. exact (MK_COMB (@lem5761336 _120592 s) (@lem5761337 _120592 t)). Qed.
Lemma lem5761340 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761341 {_120592 : Type'} (f : type672 _120592) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> _120592 -> Prop) f x).
Proof. exact (@lem5761340 (_120592 -> Prop) (_120592 -> Prop) f x). Qed.
Lemma lem5761342 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> _120592 -> Prop) (@UNION _120592) s t) = (term1486 _120592 s t).
Proof. exact (@lem5761341 _120592 (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> _120592 -> Prop) (@UNION _120592) s) t). Qed.
Lemma lem5761344 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (@UNION _120592 s t) = (term1486 _120592 s t).
Proof. exact (TRANS (@lem5761338 _120592 s t) (@lem5761342 _120592 s t)). Qed.
Lemma lem5761345 {_120592 _120607 : Type'} (f : _120592 -> _120607) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5761346 {_120592 _120607 : Type'} (op : type1400 _120607) : (@iterate _120607 _120592 op) = (@iterate _120607 _120592 op).
Proof. exact (eq_refl (@iterate _120607 _120592 op)). Qed.
Lemma lem5761347 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) : (term1487 _120592 _120607 op s t) = (term1488 _120592 _120607 op s t).
Proof. exact (MK_COMB (@lem5761346 _120592 _120607 op) (@lem5761344 _120592 s t)). Qed.
Lemma lem5761348 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term699 _120592 _120607 op s t f) = (term1489 _120592 _120607 op s t f).
Proof. exact (MK_COMB (@lem5761347 _120592 _120607 op s t) (@lem5761345 _120592 _120607 f)). Qed.
Lemma lem5761350 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761351 {_120592 _120607 : Type'} (f : type750 _120592 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761350 (type1400 _120607) (type632 _120592 _120607) f x). Qed.
Lemma lem5761352 {_120592 _120607 : Type'} (op : type1400 _120607) : (@iterate _120607 _120592 op) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op).
Proof. exact (@lem5761351 _120592 _120607 (@iterate _120607 _120592) op). Qed.
Lemma lem5761353 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (term1486 _120592 s t) = (term1486 _120592 s t).
Proof. exact (eq_refl (term1486 _120592 s t)). Qed.
Lemma lem5761354 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) : (term1488 _120592 _120607 op s t) = (term1490 _120592 _120607 op s t).
Proof. exact (MK_COMB (@lem5761352 _120592 _120607 op) (@lem5761353 _120592 s t)). Qed.
Lemma lem5761356 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761357 {_120592 _120607 : Type'} (f : type632 _120592 _120607) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761356 (_120592 -> Prop) (type570 _120592 _120607) f x). Qed.
Lemma lem5761358 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) : (term1490 _120592 _120607 op s t) = (term1491 _120592 _120607 op s t).
Proof. exact (@lem5761357 _120592 _120607 (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op) (term1486 _120592 s t)). Qed.
Lemma lem5761359 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) : (term1488 _120592 _120607 op s t) = (term1491 _120592 _120607 op s t).
Proof. exact (TRANS (@lem5761354 _120592 _120607 op s t) (@lem5761358 _120592 _120607 op s t)). Qed.
Lemma lem5761360 {_120592 _120607 : Type'} (f : _120592 -> _120607) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5761361 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1489 _120592 _120607 op s t f) = (term1492 _120592 _120607 op s t f).
Proof. exact (MK_COMB (@lem5761359 _120592 _120607 op s t) (@lem5761360 _120592 _120607 f)). Qed.
Lemma lem5761363 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761364 {_120592 _120607 : Type'} (f : type570 _120592 _120607) (x : _120592 -> _120607) : (f x) = (@I ((_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761363 (_120592 -> _120607) _120607 f x). Qed.
Lemma lem5761365 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1492 _120592 _120607 op s t f) = (term1493 _120592 _120607 op s t f).
Proof. exact (@lem5761364 _120592 _120607 (term1491 _120592 _120607 op s t) f). Qed.
Lemma lem5761366 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1489 _120592 _120607 op s t f) = (term1493 _120592 _120607 op s t f).
Proof. exact (TRANS (@lem5761361 _120592 _120607 op s t f) (@lem5761365 _120592 _120607 op s t f)). Qed.
Lemma lem5761367 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term699 _120592 _120607 op s t f) = (term1493 _120592 _120607 op s t f).
Proof. exact (TRANS (@lem5761348 _120592 _120607 op s t f) (@lem5761366 _120592 _120607 op s t f)). Qed.
Lemma lem5761368 {_120607 : Type'} (op : type1400 _120607) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5761377 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761378 {_120592 _120607 : Type'} (f : type750 _120592 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761377 (type1400 _120607) (type632 _120592 _120607) f x). Qed.
Lemma lem5761379 {_120592 _120607 : Type'} (op : type1400 _120607) : (@iterate _120607 _120592 op) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op).
Proof. exact (@lem5761378 _120592 _120607 (@iterate _120607 _120592) op). Qed.
Lemma lem5761380 {_120592 : Type'} (s : _120592 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5761381 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (@iterate _120607 _120592 op s) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op s).
Proof. exact (MK_COMB (@lem5761379 _120592 _120607 op) (@lem5761380 _120592 s)). Qed.
Lemma lem5761383 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761384 {_120592 _120607 : Type'} (f : type632 _120592 _120607) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761383 (_120592 -> Prop) (type570 _120592 _120607) f x). Qed.
Lemma lem5761385 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op s) = (term1455 _120592 _120607 op s).
Proof. exact (@lem5761384 _120592 _120607 (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op) s). Qed.
Lemma lem5761386 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (@iterate _120607 _120592 op s) = (term1455 _120592 _120607 op s).
Proof. exact (TRANS (@lem5761381 _120592 _120607 op s) (@lem5761385 _120592 _120607 op s)). Qed.
Lemma lem5761387 {_120592 _120607 : Type'} (f : _120592 -> _120607) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5761388 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op s f) = (term1456 _120592 _120607 op s f).
Proof. exact (MK_COMB (@lem5761386 _120592 _120607 op s) (@lem5761387 _120592 _120607 f)). Qed.
Lemma lem5761390 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761391 {_120592 _120607 : Type'} (f : type570 _120592 _120607) (x : _120592 -> _120607) : (f x) = (@I ((_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761390 (_120592 -> _120607) _120607 f x). Qed.
Lemma lem5761392 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term1456 _120592 _120607 op s f) = (term1457 _120592 _120607 op s f).
Proof. exact (@lem5761391 _120592 _120607 (term1455 _120592 _120607 op s) f). Qed.
Lemma lem5761394 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op s f) = (term1457 _120592 _120607 op s f).
Proof. exact (TRANS (@lem5761388 _120592 _120607 op s f) (@lem5761392 _120592 _120607 op s f)). Qed.
Lemma lem5761403 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761404 {_120592 _120607 : Type'} (f : type750 _120592 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761403 (type1400 _120607) (type632 _120592 _120607) f x). Qed.
Lemma lem5761405 {_120592 _120607 : Type'} (op : type1400 _120607) : (@iterate _120607 _120592 op) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op).
Proof. exact (@lem5761404 _120592 _120607 (@iterate _120607 _120592) op). Qed.
Lemma lem5761406 {_120592 : Type'} (t : _120592 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5761407 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) : (@iterate _120607 _120592 op t) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op t).
Proof. exact (MK_COMB (@lem5761405 _120592 _120607 op) (@lem5761406 _120592 t)). Qed.
Lemma lem5761409 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761410 {_120592 _120607 : Type'} (f : type632 _120592 _120607) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761409 (_120592 -> Prop) (type570 _120592 _120607) f x). Qed.
Lemma lem5761411 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) : (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op t) = (term1455 _120592 _120607 op t).
Proof. exact (@lem5761410 _120592 _120607 (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op) t). Qed.
Lemma lem5761412 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) : (@iterate _120607 _120592 op t) = (term1455 _120592 _120607 op t).
Proof. exact (TRANS (@lem5761407 _120592 _120607 op t) (@lem5761411 _120592 _120607 op t)). Qed.
Lemma lem5761413 {_120592 _120607 : Type'} (f : _120592 -> _120607) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5761414 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op t f) = (term1456 _120592 _120607 op t f).
Proof. exact (MK_COMB (@lem5761412 _120592 _120607 op t) (@lem5761413 _120592 _120607 f)). Qed.
Lemma lem5761416 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761417 {_120592 _120607 : Type'} (f : type570 _120592 _120607) (x : _120592 -> _120607) : (f x) = (@I ((_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761416 (_120592 -> _120607) _120607 f x). Qed.
Lemma lem5761418 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1456 _120592 _120607 op t f) = (term1457 _120592 _120607 op t f).
Proof. exact (@lem5761417 _120592 _120607 (term1455 _120592 _120607 op t) f). Qed.
Lemma lem5761420 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op t f) = (term1457 _120592 _120607 op t f).
Proof. exact (TRANS (@lem5761414 _120592 _120607 op t f) (@lem5761418 _120592 _120607 op t f)). Qed.
Lemma lem5761421 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term803 _120592 _120607 op s f) = (term1458 _120592 _120607 op s f).
Proof. exact (MK_COMB (@lem5761368 _120607 op) (@lem5761394 _120592 _120607 op s f)). Qed.
Lemma lem5761422 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term700 _120592 _120607 s op t f) = (term1459 _120592 _120607 s op t f).
Proof. exact (MK_COMB (@lem5761421 _120592 _120607 op s f) (@lem5761420 _120592 _120607 op t f)). Qed.
Lemma lem5761424 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761425 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5761424 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5761426 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term1458 _120592 _120607 op s f) = (term1460 _120592 _120607 op s f).
Proof. exact (@lem5761425 _120607 op (term1457 _120592 _120607 op s f)). Qed.
Lemma lem5761427 {_120592 _120607 : Type'} (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1457 _120592 _120607 op t f) = (term1457 _120592 _120607 op t f).
Proof. exact (eq_refl (term1457 _120592 _120607 op t f)). Qed.
Lemma lem5761428 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1459 _120592 _120607 s op t f) = (term1461 _120592 _120607 s op t f).
Proof. exact (MK_COMB (@lem5761426 _120592 _120607 op s f) (@lem5761427 _120592 _120607 op t f)). Qed.
Lemma lem5761430 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761431 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5761430 _120607 _120607 f x). Qed.
Lemma lem5761432 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1461 _120592 _120607 s op t f) = (term1462 _120592 _120607 s op t f).
Proof. exact (@lem5761431 _120607 (term1460 _120592 _120607 op s f) (term1457 _120592 _120607 op t f)). Qed.
Lemma lem5761433 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1459 _120592 _120607 s op t f) = (term1462 _120592 _120607 s op t f).
Proof. exact (TRANS (@lem5761428 _120592 _120607 s op t f) (@lem5761432 _120592 _120607 s op t f)). Qed.
Lemma lem5761434 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term700 _120592 _120607 s op t f) = (term1462 _120592 _120607 s op t f).
Proof. exact (TRANS (@lem5761422 _120592 _120607 s op t f) (@lem5761433 _120592 _120607 s op t f)). Qed.
Lemma lem5761435 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1494 _120592 _120607 op s t f) = (term1495 _120592 _120607 op s t f).
Proof. exact (MK_COMB (@lem5761325 _120607) (@lem5761367 _120592 _120607 op s t f)). Qed.
Lemma lem5761436 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : ((term699 _120592 _120607 op s t f) = (term700 _120592 _120607 s op t f)) = ((term1493 _120592 _120607 op s t f) = (term1462 _120592 _120607 s op t f)).
Proof. exact (MK_COMB (@lem5761435 _120592 _120607 op s t f) (@lem5761434 _120592 _120607 s op t f)). Qed.
Lemma lem5761437 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5761444 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761445 {_120592 : Type'} (f : type639 _120592) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> Prop) f x).
Proof. exact (@lem5761444 (_120592 -> Prop) (type686 _120592) f x). Qed.
Lemma lem5761446 {_120592 : Type'} (s : _120592 -> Prop) : (@DISJOINT _120592 s) = (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> Prop) (@DISJOINT _120592) s).
Proof. exact (@lem5761445 _120592 (@DISJOINT _120592) s). Qed.
Lemma lem5761447 {_120592 : Type'} (t : _120592 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5761448 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (@DISJOINT _120592 s t) = (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> Prop) (@DISJOINT _120592) s t).
Proof. exact (MK_COMB (@lem5761446 _120592 s) (@lem5761447 _120592 t)). Qed.
Lemma lem5761450 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761451 {_120592 : Type'} (f : type686 _120592) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> Prop) f x).
Proof. exact (@lem5761450 (_120592 -> Prop) Prop f x). Qed.
Lemma lem5761452 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> Prop) (@DISJOINT _120592) s t) = (term1477 _120592 s t).
Proof. exact (@lem5761451 _120592 (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> Prop) (@DISJOINT _120592) s) t). Qed.
Lemma lem5761454 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (@DISJOINT _120592 s t) = (term1477 _120592 s t).
Proof. exact (TRANS (@lem5761448 _120592 s t) (@lem5761452 _120592 s t)). Qed.
Lemma lem5761455 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (term1496 _120592 s t) = (term1497 _120592 s t).
Proof. exact (MK_COMB (@lem5761437) (@lem5761454 _120592 s t)). Qed.
Lemma lem5761456 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5761457 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (term1498 _120592 s t) = (term1499 _120592 s t).
Proof. exact (MK_COMB (@lem5761456) (@lem5761455 _120592 s t)). Qed.
Lemma lem5761458 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term941 _120592 _120607 s op t f) = (term1500 _120592 _120607 s op t f).
Proof. exact (MK_COMB (@lem5761457 _120592 s t) (@lem5761436 _120592 _120607 s op t f)). Qed.
Lemma lem5761459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761460 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term942 _120592 _120607 s op t f) = (term1501 _120592 _120607 s op t f).
Proof. exact (MK_COMB (@lem5761459) (@lem5761458 _120592 _120607 s op t f)). Qed.
Lemma lem5761461 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x' : _120592) (t : _120592 -> Prop) : (term943 _120592 _120607 s op f x' t) = (term1502 _120592 _120607 s op f x' t).
Proof. exact (MK_COMB (@lem5761460 _120592 _120607 s op t f) (@lem5761324 _120592 x' t)). Qed.
Lemma lem5761462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761463 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (x' : _120592) (t : _120592 -> Prop) : (term947 _120592 _120607 s op f x' t) = (term1503 _120592 _120607 s op f x' t).
Proof. exact (MK_COMB (@lem5761462) (@lem5761461 _120592 _120607 s op f x' t)). Qed.
Lemma lem5761464 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term949 _120592 _120607 s x' op t f) = (term1504 _120592 _120607 s x' op t f).
Proof. exact (MK_COMB (@lem5761463 _120592 _120607 s op f x' t) (@lem5761294 _120592 _120607 s x' op t f)). Qed.
Lemma lem5761465 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5761466 {_120607 : Type'} : (@eq _120607) = (@eq _120607).
Proof. exact (eq_refl (@eq _120607)). Qed.
Lemma lem5761475 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761476 {_120592 _120607 : Type'} (f : type750 _120592 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761475 (type1400 _120607) (type632 _120592 _120607) f x). Qed.
Lemma lem5761477 {_120592 _120607 : Type'} (op : type1400 _120607) : (@iterate _120607 _120592 op) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op).
Proof. exact (@lem5761476 _120592 _120607 (@iterate _120607 _120592) op). Qed.
Lemma lem5761478 {_120592 : Type'} (s : _120592 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5761479 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (@iterate _120607 _120592 op s) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op s).
Proof. exact (MK_COMB (@lem5761477 _120592 _120607 op) (@lem5761478 _120592 s)). Qed.
Lemma lem5761481 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761482 {_120592 _120607 : Type'} (f : type632 _120592 _120607) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761481 (_120592 -> Prop) (type570 _120592 _120607) f x). Qed.
Lemma lem5761483 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op s) = (term1455 _120592 _120607 op s).
Proof. exact (@lem5761482 _120592 _120607 (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op) s). Qed.
Lemma lem5761484 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (@iterate _120607 _120592 op s) = (term1455 _120592 _120607 op s).
Proof. exact (TRANS (@lem5761479 _120592 _120607 op s) (@lem5761483 _120592 _120607 op s)). Qed.
Lemma lem5761485 {_120592 _120607 : Type'} (f : _120592 -> _120607) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5761486 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op s f) = (term1456 _120592 _120607 op s f).
Proof. exact (MK_COMB (@lem5761484 _120592 _120607 op s) (@lem5761485 _120592 _120607 f)). Qed.
Lemma lem5761488 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761489 {_120592 _120607 : Type'} (f : type570 _120592 _120607) (x : _120592 -> _120607) : (f x) = (@I ((_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761488 (_120592 -> _120607) _120607 f x). Qed.
Lemma lem5761490 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term1456 _120592 _120607 op s f) = (term1457 _120592 _120607 op s f).
Proof. exact (@lem5761489 _120592 _120607 (term1455 _120592 _120607 op s) f). Qed.
Lemma lem5761492 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op s f) = (term1457 _120592 _120607 op s f).
Proof. exact (TRANS (@lem5761486 _120592 _120607 op s f) (@lem5761490 _120592 _120607 op s f)). Qed.
Lemma lem5761493 {_120607 : Type'} (op : type1400 _120607) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5761502 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761503 {_120592 _120607 : Type'} (f : type750 _120592 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761502 (type1400 _120607) (type632 _120592 _120607) f x). Qed.
Lemma lem5761504 {_120592 _120607 : Type'} (op : type1400 _120607) : (@iterate _120607 _120592 op) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op).
Proof. exact (@lem5761503 _120592 _120607 (@iterate _120607 _120592) op). Qed.
Lemma lem5761505 {_120592 : Type'} (s : _120592 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5761506 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (@iterate _120607 _120592 op s) = (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op s).
Proof. exact (MK_COMB (@lem5761504 _120592 _120607 op) (@lem5761505 _120592 s)). Qed.
Lemma lem5761508 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761509 {_120592 _120607 : Type'} (f : type632 _120592 _120607) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> (_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761508 (_120592 -> Prop) (type570 _120592 _120607) f x). Qed.
Lemma lem5761510 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op s) = (term1455 _120592 _120607 op s).
Proof. exact (@lem5761509 _120592 _120607 (@I ((_120607 -> _120607 -> _120607) -> (_120592 -> Prop) -> (_120592 -> _120607) -> _120607) (@iterate _120607 _120592) op) s). Qed.
Lemma lem5761511 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) : (@iterate _120607 _120592 op s) = (term1455 _120592 _120607 op s).
Proof. exact (TRANS (@lem5761506 _120592 _120607 op s) (@lem5761510 _120592 _120607 op s)). Qed.
Lemma lem5761512 {_120592 _120607 : Type'} (f : _120592 -> _120607) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5761513 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op s f) = (term1456 _120592 _120607 op s f).
Proof. exact (MK_COMB (@lem5761511 _120592 _120607 op s) (@lem5761512 _120592 _120607 f)). Qed.
Lemma lem5761515 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761516 {_120592 _120607 : Type'} (f : type570 _120592 _120607) (x : _120592 -> _120607) : (f x) = (@I ((_120592 -> _120607) -> _120607) f x).
Proof. exact (@lem5761515 (_120592 -> _120607) _120607 f x). Qed.
Lemma lem5761517 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term1456 _120592 _120607 op s f) = (term1457 _120592 _120607 op s f).
Proof. exact (@lem5761516 _120592 _120607 (term1455 _120592 _120607 op s) f). Qed.
Lemma lem5761519 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (@iterate _120607 _120592 op s f) = (term1457 _120592 _120607 op s f).
Proof. exact (TRANS (@lem5761513 _120592 _120607 op s f) (@lem5761517 _120592 _120607 op s f)). Qed.
Lemma lem5761524 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761525 {_120607 : Type'} (f : type402 _120607) (x : type1400 _120607) : (f x) = (@I ((_120607 -> _120607 -> _120607) -> _120607) f x).
Proof. exact (@lem5761524 (type1400 _120607) _120607 f x). Qed.
Lemma lem5761527 {_120607 : Type'} (op : type1400 _120607) : (@neutral _120607 op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) (@neutral _120607) op).
Proof. exact (@lem5761525 _120607 (@neutral _120607) op). Qed.
Lemma lem5761528 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term803 _120592 _120607 op s f) = (term1458 _120592 _120607 op s f).
Proof. exact (MK_COMB (@lem5761493 _120607 op) (@lem5761519 _120592 _120607 op s f)). Qed.
Lemma lem5761529 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term804 _120592 _120607 s f op) = (term1505 _120592 _120607 s f op).
Proof. exact (MK_COMB (@lem5761528 _120592 _120607 op s f) (@lem5761527 _120607 op)). Qed.
Lemma lem5761531 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761532 {_120607 : Type'} (f : type1400 _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607 -> _120607) f x).
Proof. exact (@lem5761531 _120607 (_120607 -> _120607) f x). Qed.
Lemma lem5761533 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term1458 _120592 _120607 op s f) = (term1460 _120592 _120607 op s f).
Proof. exact (@lem5761532 _120607 op (term1457 _120592 _120607 op s f)). Qed.
Lemma lem5761534 {_120607 : Type'} (op : type1400 _120607) : (@I ((_120607 -> _120607 -> _120607) -> _120607) (@neutral _120607) op) = (@I ((_120607 -> _120607 -> _120607) -> _120607) (@neutral _120607) op).
Proof. exact (eq_refl (@I ((_120607 -> _120607 -> _120607) -> _120607) (@neutral _120607) op)). Qed.
Lemma lem5761535 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term1505 _120592 _120607 s f op) = (term1506 _120592 _120607 s f op).
Proof. exact (MK_COMB (@lem5761533 _120592 _120607 op s f) (@lem5761534 _120607 op)). Qed.
Lemma lem5761537 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761538 {_120607 : Type'} (f : _120607 -> _120607) (x : _120607) : (f x) = (@I (_120607 -> _120607) f x).
Proof. exact (@lem5761537 _120607 _120607 f x). Qed.
Lemma lem5761539 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term1506 _120592 _120607 s f op) = (term1507 _120592 _120607 s f op).
Proof. exact (@lem5761538 _120607 (term1460 _120592 _120607 op s f) (@I ((_120607 -> _120607 -> _120607) -> _120607) (@neutral _120607) op)). Qed.
Lemma lem5761540 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term1505 _120592 _120607 s f op) = (term1507 _120592 _120607 s f op).
Proof. exact (TRANS (@lem5761535 _120592 _120607 s f op) (@lem5761539 _120592 _120607 s f op)). Qed.
Lemma lem5761541 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term804 _120592 _120607 s f op) = (term1507 _120592 _120607 s f op).
Proof. exact (TRANS (@lem5761529 _120592 _120607 s f op) (@lem5761540 _120592 _120607 s f op)). Qed.
Lemma lem5761542 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term801 _120592 _120607 op s f) = (term1508 _120592 _120607 op s f).
Proof. exact (MK_COMB (@lem5761466 _120607) (@lem5761492 _120592 _120607 op s f)). Qed.
Lemma lem5761543 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : ((@iterate _120607 _120592 op s f) = (term804 _120592 _120607 s f op)) = ((term1457 _120592 _120607 op s f) = (term1507 _120592 _120607 s f op)).
Proof. exact (MK_COMB (@lem5761542 _120592 _120607 op s f) (@lem5761541 _120592 _120607 s f op)). Qed.
Lemma lem5761544 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term1509 _120592 _120607 s f op) = (term1510 _120592 _120607 s f op).
Proof. exact (MK_COMB (@lem5761465) (@lem5761543 _120592 _120607 s f op)). Qed.
Lemma lem5761551 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761552 {_120592 : Type'} (f : type639 _120592) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> Prop) f x).
Proof. exact (@lem5761551 (_120592 -> Prop) (type686 _120592) f x). Qed.
Lemma lem5761553 {_120592 : Type'} (s : _120592 -> Prop) : (@DISJOINT _120592 s) = (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> Prop) (@DISJOINT _120592) s).
Proof. exact (@lem5761552 _120592 (@DISJOINT _120592) s). Qed.
Lemma lem5761554 {_120592 : Type'} : (@EMPTY _120592) = (@EMPTY _120592).
Proof. exact (eq_refl (@EMPTY _120592)). Qed.
Lemma lem5761555 {_120592 : Type'} (s : _120592 -> Prop) : (@DISJOINT _120592 s (@EMPTY _120592)) = (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> Prop) (@DISJOINT _120592) s (@EMPTY _120592)).
Proof. exact (MK_COMB (@lem5761553 _120592 s) (@lem5761554 _120592)). Qed.
Lemma lem5761557 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5761558 {_120592 : Type'} (f : type686 _120592) (x : _120592 -> Prop) : (f x) = (@I ((_120592 -> Prop) -> Prop) f x).
Proof. exact (@lem5761557 (_120592 -> Prop) Prop f x). Qed.
Lemma lem5761559 {_120592 : Type'} (s : _120592 -> Prop) : (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> Prop) (@DISJOINT _120592) s (@EMPTY _120592)) = (term1511 _120592 s).
Proof. exact (@lem5761558 _120592 (@I ((_120592 -> Prop) -> (_120592 -> Prop) -> Prop) (@DISJOINT _120592) s) (@EMPTY _120592)). Qed.
Lemma lem5761561 {_120592 : Type'} (s : _120592 -> Prop) : (@DISJOINT _120592 s (@EMPTY _120592)) = (term1511 _120592 s).
Proof. exact (TRANS (@lem5761555 _120592 s) (@lem5761559 _120592 s)). Qed.
Lemma lem5761562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761563 {_120592 : Type'} (s : _120592 -> Prop) : (term1512 _120592 s) = (term1513 _120592 s).
Proof. exact (MK_COMB (@lem5761562) (@lem5761561 _120592 s)). Qed.
Lemma lem5761564 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term940 _120592 _120607 s f op) = (term1514 _120592 _120607 s f op).
Proof. exact (MK_COMB (@lem5761563 _120592 s) (@lem5761544 _120592 _120607 s f op)). Qed.
Lemma lem5761565 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5761566 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term966 _120592 _120607 s f op) = (term1515 _120592 _120607 s f op).
Proof. exact (MK_COMB (@lem5761565) (@lem5761564 _120592 _120607 s f op)). Qed.
Lemma lem5761567 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term991 _120592 _120607 s x' op t f) = (term1516 _120592 _120607 s x' op t f).
Proof. exact (MK_COMB (@lem5761566 _120592 _120607 s f op) (@lem5761464 _120592 _120607 s x' op t f)). Qed.
Lemma lem5761568 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term991 _120592 _120607 s x' op t f) : term1516 _120592 _120607 s x' op t f.
Proof. exact (EQ_MP (@lem5761567 _120592 _120607 s x' op t f) (@lem5760627 _120592 _120607 s x' op t f h1)). Qed.
Lemma lem5761569 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1406 _120607.
Proof. exact (proj2 (@lem5761067 _120607 y z x h1)). Qed.
Lemma lem5761571 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : term1514 _120592 _120607 s f op) : term1514 _120592 _120607 s f op.
Proof. exact (h1). Qed.
Lemma lem5761572 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1504 _120592 _120607 s x' op t f) : term1504 _120592 _120607 s x' op t f.
Proof. exact (h1). Qed.
Lemma lem5761575 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1504 _120592 _120607 s x' op t f) : term1484 _120592 _120607 s x' op t f.
Proof. exact (proj2 (@lem5761572 _120592 _120607 s x' op t f h1)). Qed.
Lemma lem5761576 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1504 _120592 _120607 s x' op t f) : term1502 _120592 _120607 s op f x' t.
Proof. exact (proj1 (@lem5761572 _120592 _120607 s x' op t f h1)). Qed.
Lemma lem5761578 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1504 _120592 _120607 s x' op t f) : term1481 _120592 x' s t.
Proof. exact (proj1 (@lem5761575 _120592 _120607 s x' op t f h1)). Qed.
Lemma lem5761582 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1504 _120592 _120607 s x' op t f) : term1500 _120592 _120607 s op t f.
Proof. exact (proj1 (@lem5761576 _120592 _120607 s x' op t f h1)). Qed.
Lemma lem5761621 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5761622 {_120607 : Type'} (P : _120607 -> Prop) (Q : _120607 -> Prop) : (term77 _120607 P Q) = (term76 _120607 P Q).
Proof. exact (@lem5761621 _120607 P Q). Qed.
Lemma lem5761623 {_120607 : Type'} (op : type1400 _120607) : (term1517 _120607 op) = (term1518 _120607 op).
Proof. exact (@lem5761622 _120607 (term1389 _120607 op) (term1371 _120607 op)). Qed.
Lemma lem5761624 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1519 _120607 op x) = (term1388 _120607 op x).
Proof. exact (eq_refl (term1519 _120607 op x)). Qed.
Lemma lem5761625 {_120607 : Type'} (op : type1400 _120607) : (term1520 _120607 op) = (term1389 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5761624 _120607 op x)). Qed.
Lemma lem5761626 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761627 {_120607 : Type'} (op : type1400 _120607) : (term1521 _120607 op) = (term1390 _120607 op).
Proof. exact (MK_COMB (@lem5761626 _120607) (@lem5761625 _120607 op)). Qed.
Lemma lem5761628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761629 {_120607 : Type'} (op : type1400 _120607) : (term1522 _120607 op) = (term1391 _120607 op).
Proof. exact (MK_COMB (@lem5761628) (@lem5761627 _120607 op)). Qed.
Lemma lem5761630 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1523 _120607 op x) = ((term1368 _120607 op x) = x).
Proof. exact (eq_refl (term1523 _120607 op x)). Qed.
Lemma lem5761631 {_120607 : Type'} (op : type1400 _120607) : (term1524 _120607 op) = (term1371 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5761630 _120607 op x)). Qed.
Lemma lem5761632 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761633 {_120607 : Type'} (op : type1400 _120607) : (term1525 _120607 op) = (term1372 _120607 op).
Proof. exact (MK_COMB (@lem5761632 _120607) (@lem5761631 _120607 op)). Qed.
Lemma lem5761634 {_120607 : Type'} (op : type1400 _120607) : (term1517 _120607 op) = (term1392 _120607 op).
Proof. exact (MK_COMB (@lem5761629 _120607 op) (@lem5761633 _120607 op)). Qed.
Lemma lem5761635 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5761636 {_120607 : Type'} (op : type1400 _120607) : (term1526 _120607 op) = (term1527 _120607 op).
Proof. exact (MK_COMB (@lem5761635) (@lem5761634 _120607 op)). Qed.
Lemma lem5761637 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1519 _120607 op x) = (term1388 _120607 op x).
Proof. exact (eq_refl (term1519 _120607 op x)). Qed.
Lemma lem5761638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761639 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1528 _120607 op x) = (term1529 _120607 op x).
Proof. exact (MK_COMB (@lem5761638) (@lem5761637 _120607 op x)). Qed.
Lemma lem5761640 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1523 _120607 op x) = ((term1368 _120607 op x) = x).
Proof. exact (eq_refl (term1523 _120607 op x)). Qed.
Lemma lem5761641 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1530 _120607 op x) = (term1531 _120607 op x).
Proof. exact (MK_COMB (@lem5761639 _120607 op x) (@lem5761640 _120607 op x)). Qed.
Lemma lem5761642 {_120607 : Type'} (op : type1400 _120607) : (term1532 _120607 op) = (term1533 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5761641 _120607 op x)). Qed.
Lemma lem5761643 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761644 {_120607 : Type'} (op : type1400 _120607) : (term1518 _120607 op) = (term1534 _120607 op).
Proof. exact (MK_COMB (@lem5761643 _120607) (@lem5761642 _120607 op)). Qed.
Lemma lem5761645 {_120607 : Type'} (op : type1400 _120607) : ((term1517 _120607 op) = (term1518 _120607 op)) = ((term1392 _120607 op) = (term1534 _120607 op)).
Proof. exact (MK_COMB (@lem5761636 _120607 op) (@lem5761644 _120607 op)). Qed.
Lemma lem5761646 {_120607 : Type'} (op : type1400 _120607) : (term1392 _120607 op) = (term1534 _120607 op).
Proof. exact (EQ_MP (@lem5761645 _120607 op) (@lem5761623 _120607 op)). Qed.
Lemma lem5761648 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1535 A P Q) = (term1536 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem5761649 {_120607 : Type'} (P : _120607 -> Prop) (Q : Prop) : (term1535 _120607 P Q) = (term1536 _120607 P Q).
Proof. exact (@lem5761648 _120607 P Q). Qed.
Lemma lem5761650 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1537 _120607 op x) = (term1538 _120607 op x).
Proof. exact (@lem5761649 _120607 (term1387 _120607 op x) ((term1368 _120607 op x) = x)). Qed.
Lemma lem5761651 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1539 _120607 op x y) = (term1386 _120607 op x y).
Proof. exact (eq_refl (term1539 _120607 op x y)). Qed.
Lemma lem5761652 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1540 _120607 op x) = (term1387 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5761651 _120607 op x y)). Qed.
Lemma lem5761653 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761654 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1541 _120607 op x) = (term1388 _120607 op x).
Proof. exact (MK_COMB (@lem5761653 _120607) (@lem5761652 _120607 op x)). Qed.
Lemma lem5761655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761656 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1542 _120607 op x) = (term1529 _120607 op x).
Proof. exact (MK_COMB (@lem5761655) (@lem5761654 _120607 op x)). Qed.
Lemma lem5761657 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1368 _120607 op x) = x) = ((term1368 _120607 op x) = x).
Proof. exact (eq_refl ((term1368 _120607 op x) = x)). Qed.
Lemma lem5761658 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1537 _120607 op x) = (term1531 _120607 op x).
Proof. exact (MK_COMB (@lem5761656 _120607 op x) (@lem5761657 _120607 op x)). Qed.
Lemma lem5761659 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5761660 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1543 _120607 op x) = (term1544 _120607 op x).
Proof. exact (MK_COMB (@lem5761659) (@lem5761658 _120607 op x)). Qed.
Lemma lem5761661 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1539 _120607 op x y) = (term1386 _120607 op x y).
Proof. exact (eq_refl (term1539 _120607 op x y)). Qed.
Lemma lem5761662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761663 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1545 _120607 op x y) = (term1546 _120607 op x y).
Proof. exact (MK_COMB (@lem5761662) (@lem5761661 _120607 op x y)). Qed.
Lemma lem5761664 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1368 _120607 op x) = x) = ((term1368 _120607 op x) = x).
Proof. exact (eq_refl ((term1368 _120607 op x) = x)). Qed.
Lemma lem5761665 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1547 _120607 y op x) = (term1548 _120607 y op x).
Proof. exact (MK_COMB (@lem5761663 _120607 op x y) (@lem5761664 _120607 op x)). Qed.
Lemma lem5761666 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1549 _120607 op x) = (term1550 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5761665 _120607 y op x)). Qed.
Lemma lem5761667 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761668 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1538 _120607 op x) = (term1551 _120607 op x).
Proof. exact (MK_COMB (@lem5761667 _120607) (@lem5761666 _120607 op x)). Qed.
Lemma lem5761669 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1537 _120607 op x) = (term1538 _120607 op x)) = ((term1531 _120607 op x) = (term1551 _120607 op x)).
Proof. exact (MK_COMB (@lem5761660 _120607 op x) (@lem5761668 _120607 op x)). Qed.
Lemma lem5761670 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1531 _120607 op x) = (term1551 _120607 op x).
Proof. exact (EQ_MP (@lem5761669 _120607 op x) (@lem5761650 _120607 op x)). Qed.
Lemma lem5761672 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1535 A P Q) = (term1536 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem5761673 {_120607 : Type'} (P : _120607 -> Prop) (Q : Prop) : (term1535 _120607 P Q) = (term1536 _120607 P Q).
Proof. exact (@lem5761672 _120607 P Q). Qed.
Lemma lem5761674 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1552 _120607 y op x) = (term1553 _120607 y op x).
Proof. exact (@lem5761673 _120607 (term1385 _120607 op x y) ((term1368 _120607 op x) = x)). Qed.
Lemma lem5761675 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term1554 _120607 op x y z) = ((term1376 _120607 x op y z) = (term1382 _120607 op x y z)).
Proof. exact (eq_refl (term1554 _120607 op x y z)). Qed.
Lemma lem5761676 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1555 _120607 op x y) = (term1385 _120607 op x y).
Proof. exact (fun_ext (fun z : _120607 => @lem5761675 _120607 op x y z)). Qed.
Lemma lem5761677 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761678 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1556 _120607 op x y) = (term1386 _120607 op x y).
Proof. exact (MK_COMB (@lem5761677 _120607) (@lem5761676 _120607 op x y)). Qed.
Lemma lem5761679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761680 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1557 _120607 op x y) = (term1546 _120607 op x y).
Proof. exact (MK_COMB (@lem5761679) (@lem5761678 _120607 op x y)). Qed.
Lemma lem5761681 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1368 _120607 op x) = x) = ((term1368 _120607 op x) = x).
Proof. exact (eq_refl ((term1368 _120607 op x) = x)). Qed.
Lemma lem5761682 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1552 _120607 y op x) = (term1548 _120607 y op x).
Proof. exact (MK_COMB (@lem5761680 _120607 op x y) (@lem5761681 _120607 op x)). Qed.
Lemma lem5761683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5761684 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1558 _120607 y op x) = (term1559 _120607 y op x).
Proof. exact (MK_COMB (@lem5761683) (@lem5761682 _120607 y op x)). Qed.
Lemma lem5761685 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term1554 _120607 op x y z) = ((term1376 _120607 x op y z) = (term1382 _120607 op x y z)).
Proof. exact (eq_refl (term1554 _120607 op x y z)). Qed.
Lemma lem5761686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761687 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term1560 _120607 op x y z) = (term1561 _120607 op x y z).
Proof. exact (MK_COMB (@lem5761686) (@lem5761685 _120607 op x y z)). Qed.
Lemma lem5761688 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1368 _120607 op x) = x) = ((term1368 _120607 op x) = x).
Proof. exact (eq_refl ((term1368 _120607 op x) = x)). Qed.
Lemma lem5761689 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1562 _120607 y z op x) = (term1563 _120607 y z op x).
Proof. exact (MK_COMB (@lem5761687 _120607 op x y z) (@lem5761688 _120607 op x)). Qed.
Lemma lem5761690 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1564 _120607 y op x) = (term1565 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5761689 _120607 y z op x)). Qed.
Lemma lem5761691 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761692 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1553 _120607 y op x) = (term1566 _120607 y op x).
Proof. exact (MK_COMB (@lem5761691 _120607) (@lem5761690 _120607 y op x)). Qed.
Lemma lem5761693 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : ((term1552 _120607 y op x) = (term1553 _120607 y op x)) = ((term1548 _120607 y op x) = (term1566 _120607 y op x)).
Proof. exact (MK_COMB (@lem5761684 _120607 y op x) (@lem5761692 _120607 y op x)). Qed.
Lemma lem5761694 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1548 _120607 y op x) = (term1566 _120607 y op x).
Proof. exact (EQ_MP (@lem5761693 _120607 y op x) (@lem5761674 _120607 y op x)). Qed.
Lemma lem5761695 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1550 _120607 op x) = (term1567 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5761694 _120607 y op x)). Qed.
Lemma lem5761696 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761697 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1551 _120607 op x) = (term1568 _120607 op x).
Proof. exact (MK_COMB (@lem5761696 _120607) (@lem5761695 _120607 op x)). Qed.
Lemma lem5761698 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1531 _120607 op x) = (term1568 _120607 op x).
Proof. exact (TRANS (@lem5761670 _120607 op x) (@lem5761697 _120607 op x)). Qed.
Lemma lem5761699 {_120607 : Type'} (op : type1400 _120607) : (term1533 _120607 op) = (term1569 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5761698 _120607 op x)). Qed.
Lemma lem5761700 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761701 {_120607 : Type'} (op : type1400 _120607) : (term1534 _120607 op) = (term1570 _120607 op).
Proof. exact (MK_COMB (@lem5761700 _120607) (@lem5761699 _120607 op)). Qed.
Lemma lem5761702 {_120607 : Type'} (op : type1400 _120607) : (term1392 _120607 op) = (term1570 _120607 op).
Proof. exact (TRANS (@lem5761646 _120607 op) (@lem5761701 _120607 op)). Qed.
Lemma lem5761703 {_120607 : Type'} (op : type1400 _120607) : (term1399 _120607 op) = (term1399 _120607 op).
Proof. exact (eq_refl (term1399 _120607 op)). Qed.
Lemma lem5761704 {_120607 : Type'} (op : type1400 _120607) : (term1400 _120607 op) = (term1571 _120607 op).
Proof. exact (MK_COMB (@lem5761703 _120607 op) (@lem5761702 _120607 op)). Qed.
Lemma lem5761706 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5761707 {_120607 : Type'} (P : _120607 -> Prop) (Q : _120607 -> Prop) : (term77 _120607 P Q) = (term76 _120607 P Q).
Proof. exact (@lem5761706 _120607 P Q). Qed.
Lemma lem5761708 {_120607 : Type'} (op : type1400 _120607) : (term1572 _120607 op) = (term1573 _120607 op).
Proof. exact (@lem5761707 _120607 (term1397 _120607 op) (term1569 _120607 op)). Qed.
Lemma lem5761709 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1574 _120607 op x) = (term1396 _120607 op x).
Proof. exact (eq_refl (term1574 _120607 op x)). Qed.
Lemma lem5761710 {_120607 : Type'} (op : type1400 _120607) : (term1575 _120607 op) = (term1397 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5761709 _120607 op x)). Qed.
Lemma lem5761711 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761712 {_120607 : Type'} (op : type1400 _120607) : (term1576 _120607 op) = (term1398 _120607 op).
Proof. exact (MK_COMB (@lem5761711 _120607) (@lem5761710 _120607 op)). Qed.
Lemma lem5761713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761714 {_120607 : Type'} (op : type1400 _120607) : (term1577 _120607 op) = (term1399 _120607 op).
Proof. exact (MK_COMB (@lem5761713) (@lem5761712 _120607 op)). Qed.
Lemma lem5761715 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1578 _120607 op x) = (term1568 _120607 op x).
Proof. exact (eq_refl (term1578 _120607 op x)). Qed.
Lemma lem5761716 {_120607 : Type'} (op : type1400 _120607) : (term1579 _120607 op) = (term1569 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5761715 _120607 op x)). Qed.
Lemma lem5761717 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761718 {_120607 : Type'} (op : type1400 _120607) : (term1580 _120607 op) = (term1570 _120607 op).
Proof. exact (MK_COMB (@lem5761717 _120607) (@lem5761716 _120607 op)). Qed.
Lemma lem5761719 {_120607 : Type'} (op : type1400 _120607) : (term1572 _120607 op) = (term1571 _120607 op).
Proof. exact (MK_COMB (@lem5761714 _120607 op) (@lem5761718 _120607 op)). Qed.
Lemma lem5761720 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5761721 {_120607 : Type'} (op : type1400 _120607) : (term1581 _120607 op) = (term1582 _120607 op).
Proof. exact (MK_COMB (@lem5761720) (@lem5761719 _120607 op)). Qed.
Lemma lem5761722 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1574 _120607 op x) = (term1396 _120607 op x).
Proof. exact (eq_refl (term1574 _120607 op x)). Qed.
Lemma lem5761723 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761724 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1583 _120607 op x) = (term1584 _120607 op x).
Proof. exact (MK_COMB (@lem5761723) (@lem5761722 _120607 op x)). Qed.
Lemma lem5761725 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1578 _120607 op x) = (term1568 _120607 op x).
Proof. exact (eq_refl (term1578 _120607 op x)). Qed.
Lemma lem5761726 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1585 _120607 op x) = (term1586 _120607 op x).
Proof. exact (MK_COMB (@lem5761724 _120607 op x) (@lem5761725 _120607 op x)). Qed.
Lemma lem5761727 {_120607 : Type'} (op : type1400 _120607) : (term1587 _120607 op) = (term1588 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5761726 _120607 op x)). Qed.
Lemma lem5761728 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761729 {_120607 : Type'} (op : type1400 _120607) : (term1573 _120607 op) = (term1589 _120607 op).
Proof. exact (MK_COMB (@lem5761728 _120607) (@lem5761727 _120607 op)). Qed.
Lemma lem5761730 {_120607 : Type'} (op : type1400 _120607) : ((term1572 _120607 op) = (term1573 _120607 op)) = ((term1571 _120607 op) = (term1589 _120607 op)).
Proof. exact (MK_COMB (@lem5761721 _120607 op) (@lem5761729 _120607 op)). Qed.
Lemma lem5761731 {_120607 : Type'} (op : type1400 _120607) : (term1571 _120607 op) = (term1589 _120607 op).
Proof. exact (EQ_MP (@lem5761730 _120607 op) (@lem5761708 _120607 op)). Qed.
Lemma lem5761733 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5761734 {_120607 : Type'} (P : _120607 -> Prop) (Q : _120607 -> Prop) : (term77 _120607 P Q) = (term76 _120607 P Q).
Proof. exact (@lem5761733 _120607 P Q). Qed.
Lemma lem5761735 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1590 _120607 op x) = (term1591 _120607 op x).
Proof. exact (@lem5761734 _120607 (term1395 _120607 op x) (term1567 _120607 op x)). Qed.
Lemma lem5761736 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1592 _120607 op x y) = ((term1373 _120607 op x y) = (term1373 _120607 op y x)).
Proof. exact (eq_refl (term1592 _120607 op x y)). Qed.
Lemma lem5761737 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1593 _120607 op x) = (term1395 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5761736 _120607 op y x)). Qed.
Lemma lem5761738 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761739 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1594 _120607 op x) = (term1396 _120607 op x).
Proof. exact (MK_COMB (@lem5761738 _120607) (@lem5761737 _120607 op x)). Qed.
Lemma lem5761740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761741 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1595 _120607 op x) = (term1584 _120607 op x).
Proof. exact (MK_COMB (@lem5761740) (@lem5761739 _120607 op x)). Qed.
Lemma lem5761742 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1596 _120607 op x y) = (term1566 _120607 y op x).
Proof. exact (eq_refl (term1596 _120607 op x y)). Qed.
Lemma lem5761743 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1597 _120607 op x) = (term1567 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5761742 _120607 y op x)). Qed.
Lemma lem5761744 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761745 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1598 _120607 op x) = (term1568 _120607 op x).
Proof. exact (MK_COMB (@lem5761744 _120607) (@lem5761743 _120607 op x)). Qed.
Lemma lem5761746 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1590 _120607 op x) = (term1586 _120607 op x).
Proof. exact (MK_COMB (@lem5761741 _120607 op x) (@lem5761745 _120607 op x)). Qed.
Lemma lem5761747 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5761748 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1599 _120607 op x) = (term1600 _120607 op x).
Proof. exact (MK_COMB (@lem5761747) (@lem5761746 _120607 op x)). Qed.
Lemma lem5761749 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1592 _120607 op x y) = ((term1373 _120607 op x y) = (term1373 _120607 op y x)).
Proof. exact (eq_refl (term1592 _120607 op x y)). Qed.
Lemma lem5761750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5761751 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1601 _120607 op x y) = (term1602 _120607 op y x).
Proof. exact (MK_COMB (@lem5761750) (@lem5761749 _120607 op y x)). Qed.
Lemma lem5761752 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1596 _120607 op x y) = (term1566 _120607 y op x).
Proof. exact (eq_refl (term1596 _120607 op x y)). Qed.
Lemma lem5761753 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1603 _120607 op x y) = (term1604 _120607 y op x).
Proof. exact (MK_COMB (@lem5761751 _120607 op y x) (@lem5761752 _120607 y op x)). Qed.
Lemma lem5761754 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1605 _120607 op x) = (term1606 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5761753 _120607 y op x)). Qed.
Lemma lem5761755 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761756 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1591 _120607 op x) = (term1607 _120607 op x).
Proof. exact (MK_COMB (@lem5761755 _120607) (@lem5761754 _120607 op x)). Qed.
Lemma lem5761757 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1590 _120607 op x) = (term1591 _120607 op x)) = ((term1586 _120607 op x) = (term1607 _120607 op x)).
Proof. exact (MK_COMB (@lem5761748 _120607 op x) (@lem5761756 _120607 op x)). Qed.
Lemma lem5761758 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1586 _120607 op x) = (term1607 _120607 op x).
Proof. exact (EQ_MP (@lem5761757 _120607 op x) (@lem5761735 _120607 op x)). Qed.
Lemma lem5761760 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1608 A P Q) = (term1609 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5761761 {_120607 : Type'} (P : Prop) (Q : _120607 -> Prop) : (term1608 _120607 P Q) = (term1609 _120607 P Q).
Proof. exact (@lem5761760 _120607 P Q). Qed.
Lemma lem5761762 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1610 _120607 y op x) = (term1611 _120607 y op x).
Proof. exact (@lem5761761 _120607 ((term1373 _120607 op x y) = (term1373 _120607 op y x)) (term1565 _120607 y op x)). Qed.
Lemma lem5761763 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1612 _120607 y op x z) = (term1563 _120607 y z op x).
Proof. exact (eq_refl (term1612 _120607 y op x z)). Qed.
Lemma lem5761764 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1613 _120607 y op x) = (term1565 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5761763 _120607 y z op x)). Qed.
Lemma lem5761765 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761766 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1614 _120607 y op x) = (term1566 _120607 y op x).
Proof. exact (MK_COMB (@lem5761765 _120607) (@lem5761764 _120607 y op x)). Qed.
Lemma lem5761767 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1602 _120607 op y x) = (term1602 _120607 op y x).
Proof. exact (eq_refl (term1602 _120607 op y x)). Qed.
Lemma lem5761768 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1610 _120607 y op x) = (term1604 _120607 y op x).
Proof. exact (MK_COMB (@lem5761767 _120607 op y x) (@lem5761766 _120607 y op x)). Qed.
Lemma lem5761769 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5761770 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1615 _120607 y op x) = (term1616 _120607 y op x).
Proof. exact (MK_COMB (@lem5761769) (@lem5761768 _120607 y op x)). Qed.
Lemma lem5761771 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1612 _120607 y op x z) = (term1563 _120607 y z op x).
Proof. exact (eq_refl (term1612 _120607 y op x z)). Qed.
Lemma lem5761772 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1602 _120607 op y x) = (term1602 _120607 op y x).
Proof. exact (eq_refl (term1602 _120607 op y x)). Qed.
Lemma lem5761773 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1617 _120607 y op x z) = (term1618 _120607 y z op x).
Proof. exact (MK_COMB (@lem5761772 _120607 op y x) (@lem5761771 _120607 y z op x)). Qed.
Lemma lem5761774 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1619 _120607 y op x) = (term1620 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5761773 _120607 y z op x)). Qed.
Lemma lem5761775 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761776 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1611 _120607 y op x) = (term1621 _120607 y op x).
Proof. exact (MK_COMB (@lem5761775 _120607) (@lem5761774 _120607 y op x)). Qed.
Lemma lem5761777 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : ((term1610 _120607 y op x) = (term1611 _120607 y op x)) = ((term1604 _120607 y op x) = (term1621 _120607 y op x)).
Proof. exact (MK_COMB (@lem5761770 _120607 y op x) (@lem5761776 _120607 y op x)). Qed.
Lemma lem5761778 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1604 _120607 y op x) = (term1621 _120607 y op x).
Proof. exact (EQ_MP (@lem5761777 _120607 y op x) (@lem5761762 _120607 y op x)). Qed.
Lemma lem5761779 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1606 _120607 op x) = (term1622 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5761778 _120607 y op x)). Qed.
Lemma lem5761780 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761781 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1607 _120607 op x) = (term1623 _120607 op x).
Proof. exact (MK_COMB (@lem5761780 _120607) (@lem5761779 _120607 op x)). Qed.
Lemma lem5761782 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1586 _120607 op x) = (term1623 _120607 op x).
Proof. exact (TRANS (@lem5761758 _120607 op x) (@lem5761781 _120607 op x)). Qed.
Lemma lem5761783 {_120607 : Type'} (op : type1400 _120607) : (term1588 _120607 op) = (term1624 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5761782 _120607 op x)). Qed.
Lemma lem5761784 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761785 {_120607 : Type'} (op : type1400 _120607) : (term1589 _120607 op) = (term1625 _120607 op).
Proof. exact (MK_COMB (@lem5761784 _120607) (@lem5761783 _120607 op)). Qed.
Lemma lem5761786 {_120607 : Type'} (op : type1400 _120607) : (term1571 _120607 op) = (term1625 _120607 op).
Proof. exact (TRANS (@lem5761731 _120607 op) (@lem5761785 _120607 op)). Qed.
Lemma lem5761787 {_120607 : Type'} (op : type1400 _120607) : (term1400 _120607 op) = (term1625 _120607 op).
Proof. exact (TRANS (@lem5761704 _120607 op) (@lem5761786 _120607 op)). Qed.
Lemma lem5761788 {_120607 : Type'} (op : type1400 _120607) : (term1403 _120607 op) = (term1403 _120607 op).
Proof. exact (eq_refl (term1403 _120607 op)). Qed.
Lemma lem5761789 {_120607 : Type'} (op : type1400 _120607) : (term1404 _120607 op) = (term1626 _120607 op).
Proof. exact (MK_COMB (@lem5761788 _120607 op) (@lem5761787 _120607 op)). Qed.
Lemma lem5761791 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1627 A P Q) = (term1628 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5761792 {_120607 : Type'} (P : Prop) (Q : _120607 -> Prop) : (term1627 _120607 P Q) = (term1628 _120607 P Q).
Proof. exact (@lem5761791 _120607 P Q). Qed.
Lemma lem5761793 {_120607 : Type'} (op : type1400 _120607) : (term1629 _120607 op) = (term1630 _120607 op).
Proof. exact (@lem5761792 _120607 (term1402 _120607 op) (term1624 _120607 op)). Qed.
Lemma lem5761794 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1631 _120607 op x) = (term1623 _120607 op x).
Proof. exact (eq_refl (term1631 _120607 op x)). Qed.
Lemma lem5761795 {_120607 : Type'} (op : type1400 _120607) : (term1632 _120607 op) = (term1624 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5761794 _120607 op x)). Qed.
Lemma lem5761796 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761797 {_120607 : Type'} (op : type1400 _120607) : (term1633 _120607 op) = (term1625 _120607 op).
Proof. exact (MK_COMB (@lem5761796 _120607) (@lem5761795 _120607 op)). Qed.
Lemma lem5761798 {_120607 : Type'} (op : type1400 _120607) : (term1403 _120607 op) = (term1403 _120607 op).
Proof. exact (eq_refl (term1403 _120607 op)). Qed.
Lemma lem5761799 {_120607 : Type'} (op : type1400 _120607) : (term1629 _120607 op) = (term1626 _120607 op).
Proof. exact (MK_COMB (@lem5761798 _120607 op) (@lem5761797 _120607 op)). Qed.
Lemma lem5761800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5761801 {_120607 : Type'} (op : type1400 _120607) : (term1634 _120607 op) = (term1635 _120607 op).
Proof. exact (MK_COMB (@lem5761800) (@lem5761799 _120607 op)). Qed.
Lemma lem5761802 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1631 _120607 op x) = (term1623 _120607 op x).
Proof. exact (eq_refl (term1631 _120607 op x)). Qed.
Lemma lem5761803 {_120607 : Type'} (op : type1400 _120607) : (term1403 _120607 op) = (term1403 _120607 op).
Proof. exact (eq_refl (term1403 _120607 op)). Qed.
Lemma lem5761804 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1636 _120607 op x) = (term1637 _120607 op x).
Proof. exact (MK_COMB (@lem5761803 _120607 op) (@lem5761802 _120607 op x)). Qed.
Lemma lem5761805 {_120607 : Type'} (op : type1400 _120607) : (term1638 _120607 op) = (term1639 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5761804 _120607 op x)). Qed.
Lemma lem5761806 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761807 {_120607 : Type'} (op : type1400 _120607) : (term1630 _120607 op) = (term1640 _120607 op).
Proof. exact (MK_COMB (@lem5761806 _120607) (@lem5761805 _120607 op)). Qed.
Lemma lem5761808 {_120607 : Type'} (op : type1400 _120607) : ((term1629 _120607 op) = (term1630 _120607 op)) = ((term1626 _120607 op) = (term1640 _120607 op)).
Proof. exact (MK_COMB (@lem5761801 _120607 op) (@lem5761807 _120607 op)). Qed.
Lemma lem5761809 {_120607 : Type'} (op : type1400 _120607) : (term1626 _120607 op) = (term1640 _120607 op).
Proof. exact (EQ_MP (@lem5761808 _120607 op) (@lem5761793 _120607 op)). Qed.
Lemma lem5761811 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1627 A P Q) = (term1628 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5761812 {_120607 : Type'} (P : Prop) (Q : _120607 -> Prop) : (term1627 _120607 P Q) = (term1628 _120607 P Q).
Proof. exact (@lem5761811 _120607 P Q). Qed.
Lemma lem5761813 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1641 _120607 op x) = (term1642 _120607 op x).
Proof. exact (@lem5761812 _120607 (term1402 _120607 op) (term1622 _120607 op x)). Qed.
Lemma lem5761814 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1643 _120607 op x y) = (term1621 _120607 y op x).
Proof. exact (eq_refl (term1643 _120607 op x y)). Qed.
Lemma lem5761815 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1644 _120607 op x) = (term1622 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5761814 _120607 y op x)). Qed.
Lemma lem5761816 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761817 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1645 _120607 op x) = (term1623 _120607 op x).
Proof. exact (MK_COMB (@lem5761816 _120607) (@lem5761815 _120607 op x)). Qed.
Lemma lem5761818 {_120607 : Type'} (op : type1400 _120607) : (term1403 _120607 op) = (term1403 _120607 op).
Proof. exact (eq_refl (term1403 _120607 op)). Qed.
Lemma lem5761819 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1641 _120607 op x) = (term1637 _120607 op x).
Proof. exact (MK_COMB (@lem5761818 _120607 op) (@lem5761817 _120607 op x)). Qed.
Lemma lem5761820 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5761821 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1646 _120607 op x) = (term1647 _120607 op x).
Proof. exact (MK_COMB (@lem5761820) (@lem5761819 _120607 op x)). Qed.
Lemma lem5761822 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1643 _120607 op x y) = (term1621 _120607 y op x).
Proof. exact (eq_refl (term1643 _120607 op x y)). Qed.
Lemma lem5761823 {_120607 : Type'} (op : type1400 _120607) : (term1403 _120607 op) = (term1403 _120607 op).
Proof. exact (eq_refl (term1403 _120607 op)). Qed.
Lemma lem5761824 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1648 _120607 op x y) = (term1649 _120607 y op x).
Proof. exact (MK_COMB (@lem5761823 _120607 op) (@lem5761822 _120607 y op x)). Qed.
Lemma lem5761825 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1650 _120607 op x) = (term1651 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5761824 _120607 y op x)). Qed.
Lemma lem5761826 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761827 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1642 _120607 op x) = (term1652 _120607 op x).
Proof. exact (MK_COMB (@lem5761826 _120607) (@lem5761825 _120607 op x)). Qed.
Lemma lem5761828 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1641 _120607 op x) = (term1642 _120607 op x)) = ((term1637 _120607 op x) = (term1652 _120607 op x)).
Proof. exact (MK_COMB (@lem5761821 _120607 op x) (@lem5761827 _120607 op x)). Qed.
Lemma lem5761829 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1637 _120607 op x) = (term1652 _120607 op x).
Proof. exact (EQ_MP (@lem5761828 _120607 op x) (@lem5761813 _120607 op x)). Qed.
Lemma lem5761831 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1627 A P Q) = (term1628 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5761832 {_120607 : Type'} (P : Prop) (Q : _120607 -> Prop) : (term1627 _120607 P Q) = (term1628 _120607 P Q).
Proof. exact (@lem5761831 _120607 P Q). Qed.
Lemma lem5761833 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1653 _120607 y op x) = (term1654 _120607 y op x).
Proof. exact (@lem5761832 _120607 (term1402 _120607 op) (term1620 _120607 y op x)). Qed.
Lemma lem5761834 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1655 _120607 y op x z) = (term1618 _120607 y z op x).
Proof. exact (eq_refl (term1655 _120607 y op x z)). Qed.
Lemma lem5761835 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1656 _120607 y op x) = (term1620 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5761834 _120607 y z op x)). Qed.
Lemma lem5761836 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761837 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1657 _120607 y op x) = (term1621 _120607 y op x).
Proof. exact (MK_COMB (@lem5761836 _120607) (@lem5761835 _120607 y op x)). Qed.
Lemma lem5761838 {_120607 : Type'} (op : type1400 _120607) : (term1403 _120607 op) = (term1403 _120607 op).
Proof. exact (eq_refl (term1403 _120607 op)). Qed.
Lemma lem5761839 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1653 _120607 y op x) = (term1649 _120607 y op x).
Proof. exact (MK_COMB (@lem5761838 _120607 op) (@lem5761837 _120607 y op x)). Qed.
Lemma lem5761840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5761841 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1658 _120607 y op x) = (term1659 _120607 y op x).
Proof. exact (MK_COMB (@lem5761840) (@lem5761839 _120607 y op x)). Qed.
Lemma lem5761842 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1655 _120607 y op x z) = (term1618 _120607 y z op x).
Proof. exact (eq_refl (term1655 _120607 y op x z)). Qed.
Lemma lem5761843 {_120607 : Type'} (op : type1400 _120607) : (term1403 _120607 op) = (term1403 _120607 op).
Proof. exact (eq_refl (term1403 _120607 op)). Qed.
Lemma lem5761844 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1660 _120607 y op x z) = (term1661 _120607 y z op x).
Proof. exact (MK_COMB (@lem5761843 _120607 op) (@lem5761842 _120607 y z op x)). Qed.
Lemma lem5761845 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1662 _120607 y op x) = (term1663 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5761844 _120607 y z op x)). Qed.
Lemma lem5761846 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761847 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1654 _120607 y op x) = (term1664 _120607 y op x).
Proof. exact (MK_COMB (@lem5761846 _120607) (@lem5761845 _120607 y op x)). Qed.
Lemma lem5761848 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : ((term1653 _120607 y op x) = (term1654 _120607 y op x)) = ((term1649 _120607 y op x) = (term1664 _120607 y op x)).
Proof. exact (MK_COMB (@lem5761841 _120607 y op x) (@lem5761847 _120607 y op x)). Qed.
Lemma lem5761849 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1649 _120607 y op x) = (term1664 _120607 y op x).
Proof. exact (EQ_MP (@lem5761848 _120607 y op x) (@lem5761833 _120607 y op x)). Qed.
Lemma lem5761850 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1651 _120607 op x) = (term1665 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5761849 _120607 y op x)). Qed.
Lemma lem5761851 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761852 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1652 _120607 op x) = (term1666 _120607 op x).
Proof. exact (MK_COMB (@lem5761851 _120607) (@lem5761850 _120607 op x)). Qed.
Lemma lem5761853 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1637 _120607 op x) = (term1666 _120607 op x).
Proof. exact (TRANS (@lem5761829 _120607 op x) (@lem5761852 _120607 op x)). Qed.
Lemma lem5761854 {_120607 : Type'} (op : type1400 _120607) : (term1639 _120607 op) = (term1667 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5761853 _120607 op x)). Qed.
Lemma lem5761855 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761856 {_120607 : Type'} (op : type1400 _120607) : (term1640 _120607 op) = (term1668 _120607 op).
Proof. exact (MK_COMB (@lem5761855 _120607) (@lem5761854 _120607 op)). Qed.
Lemma lem5761857 {_120607 : Type'} (op : type1400 _120607) : (term1626 _120607 op) = (term1668 _120607 op).
Proof. exact (TRANS (@lem5761809 _120607 op) (@lem5761856 _120607 op)). Qed.
Lemma lem5761858 {_120607 : Type'} (op : type1400 _120607) : (term1404 _120607 op) = (term1668 _120607 op).
Proof. exact (TRANS (@lem5761789 _120607 op) (@lem5761857 _120607 op)). Qed.
Lemma lem5761859 {_120607 : Type'} : (term1405 _120607) = (term1669 _120607).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5761858 _120607 op)). Qed.
Lemma lem5761860 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5761861 {_120607 : Type'} : (term1406 _120607) = (term1670 _120607).
Proof. exact (MK_COMB (@lem5761860 _120607) (@lem5761859 _120607)). Qed.
Lemma lem5761875 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1661 _120607 y z op x) = (term1671 _120607 y z op x).
Proof. exact (@lem19490 ((term1373 _120607 op x y) = (term1373 _120607 op y x)) (term1402 _120607 op) (term1563 _120607 y z op x)). Qed.
Lemma lem5761882 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1672 _120607 y z op x) = (term1673 _120607 y z op x).
Proof. exact (@lem19490 ((term1376 _120607 x op y z) = (term1382 _120607 op x y z)) (term1402 _120607 op) ((term1368 _120607 op x) = x)). Qed.
Lemma lem5761885 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1674 _120607 op y x) = (term1674 _120607 op y x).
Proof. exact (eq_refl (term1674 _120607 op y x)). Qed.
Lemma lem5761886 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1671 _120607 y z op x) = (term1675 _120607 y z op x).
Proof. exact (MK_COMB (@lem5761885 _120607 op y x) (@lem5761882 _120607 y z op x)). Qed.
Lemma lem5761888 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1661 _120607 y z op x) = (term1675 _120607 y z op x).
Proof. exact (TRANS (@lem5761875 _120607 y z op x) (@lem5761886 _120607 y z op x)). Qed.
Lemma lem5761889 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1663 _120607 y op x) = (term1676 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5761888 _120607 y z op x)). Qed.
Lemma lem5761890 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761891 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1664 _120607 y op x) = (term1677 _120607 y op x).
Proof. exact (MK_COMB (@lem5761890 _120607) (@lem5761889 _120607 y op x)). Qed.
Lemma lem5761892 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1665 _120607 op x) = (term1678 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5761891 _120607 y op x)). Qed.
Lemma lem5761893 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761894 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1666 _120607 op x) = (term1679 _120607 op x).
Proof. exact (MK_COMB (@lem5761893 _120607) (@lem5761892 _120607 op x)). Qed.
Lemma lem5761895 {_120607 : Type'} (op : type1400 _120607) : (term1667 _120607 op) = (term1680 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5761894 _120607 op x)). Qed.
Lemma lem5761896 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5761897 {_120607 : Type'} (op : type1400 _120607) : (term1668 _120607 op) = (term1681 _120607 op).
Proof. exact (MK_COMB (@lem5761896 _120607) (@lem5761895 _120607 op)). Qed.
Lemma lem5761898 {_120607 : Type'} : (term1669 _120607) = (term1682 _120607).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5761897 _120607 op)). Qed.
Lemma lem5761899 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5761900 {_120607 : Type'} : (term1670 _120607) = (term1683 _120607).
Proof. exact (MK_COMB (@lem5761899 _120607) (@lem5761898 _120607)). Qed.
Lemma lem5761901 {_120607 : Type'} : (term1406 _120607) = (term1683 _120607).
Proof. exact (TRANS (@lem5761861 _120607) (@lem5761900 _120607)). Qed.
Lemma lem5761902 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1683 _120607.
Proof. exact (EQ_MP (@lem5761901 _120607) (@lem5761569 _120607 y z x h1)). Qed.
Lemma lem5762250 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term1497 _120592 s t) : term1497 _120592 s t.
Proof. exact (h1). Qed.
Lemma lem5762285 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5762286 {_120607 : Type'} (P : _120607 -> Prop) (Q : _120607 -> Prop) : (term77 _120607 P Q) = (term76 _120607 P Q).
Proof. exact (@lem5762285 _120607 P Q). Qed.
Lemma lem5762287 {_120607 : Type'} (op : type1400 _120607) : (term1517 _120607 op) = (term1518 _120607 op).
Proof. exact (@lem5762286 _120607 (term1389 _120607 op) (term1371 _120607 op)). Qed.
Lemma lem5762288 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1519 _120607 op x) = (term1388 _120607 op x).
Proof. exact (eq_refl (term1519 _120607 op x)). Qed.
Lemma lem5762289 {_120607 : Type'} (op : type1400 _120607) : (term1520 _120607 op) = (term1389 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5762288 _120607 op x)). Qed.
Lemma lem5762290 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762291 {_120607 : Type'} (op : type1400 _120607) : (term1521 _120607 op) = (term1390 _120607 op).
Proof. exact (MK_COMB (@lem5762290 _120607) (@lem5762289 _120607 op)). Qed.
Lemma lem5762292 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5762293 {_120607 : Type'} (op : type1400 _120607) : (term1522 _120607 op) = (term1391 _120607 op).
Proof. exact (MK_COMB (@lem5762292) (@lem5762291 _120607 op)). Qed.
Lemma lem5762294 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1523 _120607 op x) = ((term1368 _120607 op x) = x).
Proof. exact (eq_refl (term1523 _120607 op x)). Qed.
Lemma lem5762295 {_120607 : Type'} (op : type1400 _120607) : (term1524 _120607 op) = (term1371 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5762294 _120607 op x)). Qed.
Lemma lem5762296 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762297 {_120607 : Type'} (op : type1400 _120607) : (term1525 _120607 op) = (term1372 _120607 op).
Proof. exact (MK_COMB (@lem5762296 _120607) (@lem5762295 _120607 op)). Qed.
Lemma lem5762298 {_120607 : Type'} (op : type1400 _120607) : (term1517 _120607 op) = (term1392 _120607 op).
Proof. exact (MK_COMB (@lem5762293 _120607 op) (@lem5762297 _120607 op)). Qed.
Lemma lem5762299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5762300 {_120607 : Type'} (op : type1400 _120607) : (term1526 _120607 op) = (term1527 _120607 op).
Proof. exact (MK_COMB (@lem5762299) (@lem5762298 _120607 op)). Qed.
Lemma lem5762301 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1519 _120607 op x) = (term1388 _120607 op x).
Proof. exact (eq_refl (term1519 _120607 op x)). Qed.
Lemma lem5762302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5762303 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1528 _120607 op x) = (term1529 _120607 op x).
Proof. exact (MK_COMB (@lem5762302) (@lem5762301 _120607 op x)). Qed.
Lemma lem5762304 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1523 _120607 op x) = ((term1368 _120607 op x) = x).
Proof. exact (eq_refl (term1523 _120607 op x)). Qed.
Lemma lem5762305 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1530 _120607 op x) = (term1531 _120607 op x).
Proof. exact (MK_COMB (@lem5762303 _120607 op x) (@lem5762304 _120607 op x)). Qed.
Lemma lem5762306 {_120607 : Type'} (op : type1400 _120607) : (term1532 _120607 op) = (term1533 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5762305 _120607 op x)). Qed.
Lemma lem5762307 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762308 {_120607 : Type'} (op : type1400 _120607) : (term1518 _120607 op) = (term1534 _120607 op).
Proof. exact (MK_COMB (@lem5762307 _120607) (@lem5762306 _120607 op)). Qed.
Lemma lem5762309 {_120607 : Type'} (op : type1400 _120607) : ((term1517 _120607 op) = (term1518 _120607 op)) = ((term1392 _120607 op) = (term1534 _120607 op)).
Proof. exact (MK_COMB (@lem5762300 _120607 op) (@lem5762308 _120607 op)). Qed.
Lemma lem5762310 {_120607 : Type'} (op : type1400 _120607) : (term1392 _120607 op) = (term1534 _120607 op).
Proof. exact (EQ_MP (@lem5762309 _120607 op) (@lem5762287 _120607 op)). Qed.
Lemma lem5762312 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1535 A P Q) = (term1536 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem5762313 {_120607 : Type'} (P : _120607 -> Prop) (Q : Prop) : (term1535 _120607 P Q) = (term1536 _120607 P Q).
Proof. exact (@lem5762312 _120607 P Q). Qed.
Lemma lem5762314 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1537 _120607 op x) = (term1538 _120607 op x).
Proof. exact (@lem5762313 _120607 (term1387 _120607 op x) ((term1368 _120607 op x) = x)). Qed.
Lemma lem5762315 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1539 _120607 op x y) = (term1386 _120607 op x y).
Proof. exact (eq_refl (term1539 _120607 op x y)). Qed.
Lemma lem5762316 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1540 _120607 op x) = (term1387 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5762315 _120607 op x y)). Qed.
Lemma lem5762317 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762318 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1541 _120607 op x) = (term1388 _120607 op x).
Proof. exact (MK_COMB (@lem5762317 _120607) (@lem5762316 _120607 op x)). Qed.
Lemma lem5762319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5762320 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1542 _120607 op x) = (term1529 _120607 op x).
Proof. exact (MK_COMB (@lem5762319) (@lem5762318 _120607 op x)). Qed.
Lemma lem5762321 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1368 _120607 op x) = x) = ((term1368 _120607 op x) = x).
Proof. exact (eq_refl ((term1368 _120607 op x) = x)). Qed.
Lemma lem5762322 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1537 _120607 op x) = (term1531 _120607 op x).
Proof. exact (MK_COMB (@lem5762320 _120607 op x) (@lem5762321 _120607 op x)). Qed.
Lemma lem5762323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5762324 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1543 _120607 op x) = (term1544 _120607 op x).
Proof. exact (MK_COMB (@lem5762323) (@lem5762322 _120607 op x)). Qed.
Lemma lem5762325 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1539 _120607 op x y) = (term1386 _120607 op x y).
Proof. exact (eq_refl (term1539 _120607 op x y)). Qed.
Lemma lem5762326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5762327 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1545 _120607 op x y) = (term1546 _120607 op x y).
Proof. exact (MK_COMB (@lem5762326) (@lem5762325 _120607 op x y)). Qed.
Lemma lem5762328 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1368 _120607 op x) = x) = ((term1368 _120607 op x) = x).
Proof. exact (eq_refl ((term1368 _120607 op x) = x)). Qed.
Lemma lem5762329 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1547 _120607 y op x) = (term1548 _120607 y op x).
Proof. exact (MK_COMB (@lem5762327 _120607 op x y) (@lem5762328 _120607 op x)). Qed.
Lemma lem5762330 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1549 _120607 op x) = (term1550 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5762329 _120607 y op x)). Qed.
Lemma lem5762331 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762332 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1538 _120607 op x) = (term1551 _120607 op x).
Proof. exact (MK_COMB (@lem5762331 _120607) (@lem5762330 _120607 op x)). Qed.
Lemma lem5762333 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1537 _120607 op x) = (term1538 _120607 op x)) = ((term1531 _120607 op x) = (term1551 _120607 op x)).
Proof. exact (MK_COMB (@lem5762324 _120607 op x) (@lem5762332 _120607 op x)). Qed.
Lemma lem5762334 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1531 _120607 op x) = (term1551 _120607 op x).
Proof. exact (EQ_MP (@lem5762333 _120607 op x) (@lem5762314 _120607 op x)). Qed.
Lemma lem5762336 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1535 A P Q) = (term1536 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem5762337 {_120607 : Type'} (P : _120607 -> Prop) (Q : Prop) : (term1535 _120607 P Q) = (term1536 _120607 P Q).
Proof. exact (@lem5762336 _120607 P Q). Qed.
Lemma lem5762338 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1552 _120607 y op x) = (term1553 _120607 y op x).
Proof. exact (@lem5762337 _120607 (term1385 _120607 op x y) ((term1368 _120607 op x) = x)). Qed.
Lemma lem5762339 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term1554 _120607 op x y z) = ((term1376 _120607 x op y z) = (term1382 _120607 op x y z)).
Proof. exact (eq_refl (term1554 _120607 op x y z)). Qed.
Lemma lem5762340 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1555 _120607 op x y) = (term1385 _120607 op x y).
Proof. exact (fun_ext (fun z : _120607 => @lem5762339 _120607 op x y z)). Qed.
Lemma lem5762341 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762342 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1556 _120607 op x y) = (term1386 _120607 op x y).
Proof. exact (MK_COMB (@lem5762341 _120607) (@lem5762340 _120607 op x y)). Qed.
Lemma lem5762343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5762344 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) : (term1557 _120607 op x y) = (term1546 _120607 op x y).
Proof. exact (MK_COMB (@lem5762343) (@lem5762342 _120607 op x y)). Qed.
Lemma lem5762345 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1368 _120607 op x) = x) = ((term1368 _120607 op x) = x).
Proof. exact (eq_refl ((term1368 _120607 op x) = x)). Qed.
Lemma lem5762346 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1552 _120607 y op x) = (term1548 _120607 y op x).
Proof. exact (MK_COMB (@lem5762344 _120607 op x y) (@lem5762345 _120607 op x)). Qed.
Lemma lem5762347 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5762348 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1558 _120607 y op x) = (term1559 _120607 y op x).
Proof. exact (MK_COMB (@lem5762347) (@lem5762346 _120607 y op x)). Qed.
Lemma lem5762349 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term1554 _120607 op x y z) = ((term1376 _120607 x op y z) = (term1382 _120607 op x y z)).
Proof. exact (eq_refl (term1554 _120607 op x y z)). Qed.
Lemma lem5762350 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5762351 {_120607 : Type'} (op : type1400 _120607) (x : _120607) (y : _120607) (z : _120607) : (term1560 _120607 op x y z) = (term1561 _120607 op x y z).
Proof. exact (MK_COMB (@lem5762350) (@lem5762349 _120607 op x y z)). Qed.
Lemma lem5762352 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1368 _120607 op x) = x) = ((term1368 _120607 op x) = x).
Proof. exact (eq_refl ((term1368 _120607 op x) = x)). Qed.
Lemma lem5762353 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1562 _120607 y z op x) = (term1563 _120607 y z op x).
Proof. exact (MK_COMB (@lem5762351 _120607 op x y z) (@lem5762352 _120607 op x)). Qed.
Lemma lem5762354 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1564 _120607 y op x) = (term1565 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5762353 _120607 y z op x)). Qed.
Lemma lem5762355 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762356 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1553 _120607 y op x) = (term1566 _120607 y op x).
Proof. exact (MK_COMB (@lem5762355 _120607) (@lem5762354 _120607 y op x)). Qed.
Lemma lem5762357 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : ((term1552 _120607 y op x) = (term1553 _120607 y op x)) = ((term1548 _120607 y op x) = (term1566 _120607 y op x)).
Proof. exact (MK_COMB (@lem5762348 _120607 y op x) (@lem5762356 _120607 y op x)). Qed.
Lemma lem5762358 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1548 _120607 y op x) = (term1566 _120607 y op x).
Proof. exact (EQ_MP (@lem5762357 _120607 y op x) (@lem5762338 _120607 y op x)). Qed.
Lemma lem5762359 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1550 _120607 op x) = (term1567 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5762358 _120607 y op x)). Qed.
Lemma lem5762360 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762361 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1551 _120607 op x) = (term1568 _120607 op x).
Proof. exact (MK_COMB (@lem5762360 _120607) (@lem5762359 _120607 op x)). Qed.
Lemma lem5762362 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1531 _120607 op x) = (term1568 _120607 op x).
Proof. exact (TRANS (@lem5762334 _120607 op x) (@lem5762361 _120607 op x)). Qed.
Lemma lem5762363 {_120607 : Type'} (op : type1400 _120607) : (term1533 _120607 op) = (term1569 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5762362 _120607 op x)). Qed.
Lemma lem5762364 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762365 {_120607 : Type'} (op : type1400 _120607) : (term1534 _120607 op) = (term1570 _120607 op).
Proof. exact (MK_COMB (@lem5762364 _120607) (@lem5762363 _120607 op)). Qed.
Lemma lem5762366 {_120607 : Type'} (op : type1400 _120607) : (term1392 _120607 op) = (term1570 _120607 op).
Proof. exact (TRANS (@lem5762310 _120607 op) (@lem5762365 _120607 op)). Qed.
Lemma lem5762367 {_120607 : Type'} (op : type1400 _120607) : (term1399 _120607 op) = (term1399 _120607 op).
Proof. exact (eq_refl (term1399 _120607 op)). Qed.
Lemma lem5762368 {_120607 : Type'} (op : type1400 _120607) : (term1400 _120607 op) = (term1571 _120607 op).
Proof. exact (MK_COMB (@lem5762367 _120607 op) (@lem5762366 _120607 op)). Qed.
Lemma lem5762370 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5762371 {_120607 : Type'} (P : _120607 -> Prop) (Q : _120607 -> Prop) : (term77 _120607 P Q) = (term76 _120607 P Q).
Proof. exact (@lem5762370 _120607 P Q). Qed.
Lemma lem5762372 {_120607 : Type'} (op : type1400 _120607) : (term1572 _120607 op) = (term1573 _120607 op).
Proof. exact (@lem5762371 _120607 (term1397 _120607 op) (term1569 _120607 op)). Qed.
Lemma lem5762373 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1574 _120607 op x) = (term1396 _120607 op x).
Proof. exact (eq_refl (term1574 _120607 op x)). Qed.
Lemma lem5762374 {_120607 : Type'} (op : type1400 _120607) : (term1575 _120607 op) = (term1397 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5762373 _120607 op x)). Qed.
Lemma lem5762375 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762376 {_120607 : Type'} (op : type1400 _120607) : (term1576 _120607 op) = (term1398 _120607 op).
Proof. exact (MK_COMB (@lem5762375 _120607) (@lem5762374 _120607 op)). Qed.
Lemma lem5762377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5762378 {_120607 : Type'} (op : type1400 _120607) : (term1577 _120607 op) = (term1399 _120607 op).
Proof. exact (MK_COMB (@lem5762377) (@lem5762376 _120607 op)). Qed.
Lemma lem5762379 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1578 _120607 op x) = (term1568 _120607 op x).
Proof. exact (eq_refl (term1578 _120607 op x)). Qed.
Lemma lem5762380 {_120607 : Type'} (op : type1400 _120607) : (term1579 _120607 op) = (term1569 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5762379 _120607 op x)). Qed.
Lemma lem5762381 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762382 {_120607 : Type'} (op : type1400 _120607) : (term1580 _120607 op) = (term1570 _120607 op).
Proof. exact (MK_COMB (@lem5762381 _120607) (@lem5762380 _120607 op)). Qed.
Lemma lem5762383 {_120607 : Type'} (op : type1400 _120607) : (term1572 _120607 op) = (term1571 _120607 op).
Proof. exact (MK_COMB (@lem5762378 _120607 op) (@lem5762382 _120607 op)). Qed.
Lemma lem5762384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5762385 {_120607 : Type'} (op : type1400 _120607) : (term1581 _120607 op) = (term1582 _120607 op).
Proof. exact (MK_COMB (@lem5762384) (@lem5762383 _120607 op)). Qed.
Lemma lem5762386 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1574 _120607 op x) = (term1396 _120607 op x).
Proof. exact (eq_refl (term1574 _120607 op x)). Qed.
Lemma lem5762387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5762388 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1583 _120607 op x) = (term1584 _120607 op x).
Proof. exact (MK_COMB (@lem5762387) (@lem5762386 _120607 op x)). Qed.
Lemma lem5762389 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1578 _120607 op x) = (term1568 _120607 op x).
Proof. exact (eq_refl (term1578 _120607 op x)). Qed.
Lemma lem5762390 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1585 _120607 op x) = (term1586 _120607 op x).
Proof. exact (MK_COMB (@lem5762388 _120607 op x) (@lem5762389 _120607 op x)). Qed.
Lemma lem5762391 {_120607 : Type'} (op : type1400 _120607) : (term1587 _120607 op) = (term1588 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5762390 _120607 op x)). Qed.
Lemma lem5762392 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762393 {_120607 : Type'} (op : type1400 _120607) : (term1573 _120607 op) = (term1589 _120607 op).
Proof. exact (MK_COMB (@lem5762392 _120607) (@lem5762391 _120607 op)). Qed.
Lemma lem5762394 {_120607 : Type'} (op : type1400 _120607) : ((term1572 _120607 op) = (term1573 _120607 op)) = ((term1571 _120607 op) = (term1589 _120607 op)).
Proof. exact (MK_COMB (@lem5762385 _120607 op) (@lem5762393 _120607 op)). Qed.
Lemma lem5762395 {_120607 : Type'} (op : type1400 _120607) : (term1571 _120607 op) = (term1589 _120607 op).
Proof. exact (EQ_MP (@lem5762394 _120607 op) (@lem5762372 _120607 op)). Qed.
Lemma lem5762397 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5762398 {_120607 : Type'} (P : _120607 -> Prop) (Q : _120607 -> Prop) : (term77 _120607 P Q) = (term76 _120607 P Q).
Proof. exact (@lem5762397 _120607 P Q). Qed.
Lemma lem5762399 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1590 _120607 op x) = (term1591 _120607 op x).
Proof. exact (@lem5762398 _120607 (term1395 _120607 op x) (term1567 _120607 op x)). Qed.
Lemma lem5762400 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1592 _120607 op x y) = ((term1373 _120607 op x y) = (term1373 _120607 op y x)).
Proof. exact (eq_refl (term1592 _120607 op x y)). Qed.
Lemma lem5762401 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1593 _120607 op x) = (term1395 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5762400 _120607 op y x)). Qed.
Lemma lem5762402 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762403 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1594 _120607 op x) = (term1396 _120607 op x).
Proof. exact (MK_COMB (@lem5762402 _120607) (@lem5762401 _120607 op x)). Qed.
Lemma lem5762404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5762405 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1595 _120607 op x) = (term1584 _120607 op x).
Proof. exact (MK_COMB (@lem5762404) (@lem5762403 _120607 op x)). Qed.
Lemma lem5762406 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1596 _120607 op x y) = (term1566 _120607 y op x).
Proof. exact (eq_refl (term1596 _120607 op x y)). Qed.
Lemma lem5762407 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1597 _120607 op x) = (term1567 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5762406 _120607 y op x)). Qed.
Lemma lem5762408 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762409 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1598 _120607 op x) = (term1568 _120607 op x).
Proof. exact (MK_COMB (@lem5762408 _120607) (@lem5762407 _120607 op x)). Qed.
Lemma lem5762410 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1590 _120607 op x) = (term1586 _120607 op x).
Proof. exact (MK_COMB (@lem5762405 _120607 op x) (@lem5762409 _120607 op x)). Qed.
Lemma lem5762411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5762412 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1599 _120607 op x) = (term1600 _120607 op x).
Proof. exact (MK_COMB (@lem5762411) (@lem5762410 _120607 op x)). Qed.
Lemma lem5762413 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1592 _120607 op x y) = ((term1373 _120607 op x y) = (term1373 _120607 op y x)).
Proof. exact (eq_refl (term1592 _120607 op x y)). Qed.
Lemma lem5762414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5762415 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1601 _120607 op x y) = (term1602 _120607 op y x).
Proof. exact (MK_COMB (@lem5762414) (@lem5762413 _120607 op y x)). Qed.
Lemma lem5762416 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1596 _120607 op x y) = (term1566 _120607 y op x).
Proof. exact (eq_refl (term1596 _120607 op x y)). Qed.
Lemma lem5762417 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1603 _120607 op x y) = (term1604 _120607 y op x).
Proof. exact (MK_COMB (@lem5762415 _120607 op y x) (@lem5762416 _120607 y op x)). Qed.
Lemma lem5762418 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1605 _120607 op x) = (term1606 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5762417 _120607 y op x)). Qed.
Lemma lem5762419 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762420 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1591 _120607 op x) = (term1607 _120607 op x).
Proof. exact (MK_COMB (@lem5762419 _120607) (@lem5762418 _120607 op x)). Qed.
Lemma lem5762421 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1590 _120607 op x) = (term1591 _120607 op x)) = ((term1586 _120607 op x) = (term1607 _120607 op x)).
Proof. exact (MK_COMB (@lem5762412 _120607 op x) (@lem5762420 _120607 op x)). Qed.
Lemma lem5762422 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1586 _120607 op x) = (term1607 _120607 op x).
Proof. exact (EQ_MP (@lem5762421 _120607 op x) (@lem5762399 _120607 op x)). Qed.
Lemma lem5762424 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1608 A P Q) = (term1609 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5762425 {_120607 : Type'} (P : Prop) (Q : _120607 -> Prop) : (term1608 _120607 P Q) = (term1609 _120607 P Q).
Proof. exact (@lem5762424 _120607 P Q). Qed.
Lemma lem5762426 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1610 _120607 y op x) = (term1611 _120607 y op x).
Proof. exact (@lem5762425 _120607 ((term1373 _120607 op x y) = (term1373 _120607 op y x)) (term1565 _120607 y op x)). Qed.
Lemma lem5762427 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1612 _120607 y op x z) = (term1563 _120607 y z op x).
Proof. exact (eq_refl (term1612 _120607 y op x z)). Qed.
Lemma lem5762428 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1613 _120607 y op x) = (term1565 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5762427 _120607 y z op x)). Qed.
Lemma lem5762429 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762430 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1614 _120607 y op x) = (term1566 _120607 y op x).
Proof. exact (MK_COMB (@lem5762429 _120607) (@lem5762428 _120607 y op x)). Qed.
Lemma lem5762431 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1602 _120607 op y x) = (term1602 _120607 op y x).
Proof. exact (eq_refl (term1602 _120607 op y x)). Qed.
Lemma lem5762432 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1610 _120607 y op x) = (term1604 _120607 y op x).
Proof. exact (MK_COMB (@lem5762431 _120607 op y x) (@lem5762430 _120607 y op x)). Qed.
Lemma lem5762433 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5762434 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1615 _120607 y op x) = (term1616 _120607 y op x).
Proof. exact (MK_COMB (@lem5762433) (@lem5762432 _120607 y op x)). Qed.
Lemma lem5762435 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1612 _120607 y op x z) = (term1563 _120607 y z op x).
Proof. exact (eq_refl (term1612 _120607 y op x z)). Qed.
Lemma lem5762436 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1602 _120607 op y x) = (term1602 _120607 op y x).
Proof. exact (eq_refl (term1602 _120607 op y x)). Qed.
Lemma lem5762437 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1617 _120607 y op x z) = (term1618 _120607 y z op x).
Proof. exact (MK_COMB (@lem5762436 _120607 op y x) (@lem5762435 _120607 y z op x)). Qed.
Lemma lem5762438 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1619 _120607 y op x) = (term1620 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5762437 _120607 y z op x)). Qed.
Lemma lem5762439 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762440 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1611 _120607 y op x) = (term1621 _120607 y op x).
Proof. exact (MK_COMB (@lem5762439 _120607) (@lem5762438 _120607 y op x)). Qed.
Lemma lem5762441 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : ((term1610 _120607 y op x) = (term1611 _120607 y op x)) = ((term1604 _120607 y op x) = (term1621 _120607 y op x)).
Proof. exact (MK_COMB (@lem5762434 _120607 y op x) (@lem5762440 _120607 y op x)). Qed.
Lemma lem5762442 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1604 _120607 y op x) = (term1621 _120607 y op x).
Proof. exact (EQ_MP (@lem5762441 _120607 y op x) (@lem5762426 _120607 y op x)). Qed.
Lemma lem5762443 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1606 _120607 op x) = (term1622 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5762442 _120607 y op x)). Qed.
Lemma lem5762444 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762445 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1607 _120607 op x) = (term1623 _120607 op x).
Proof. exact (MK_COMB (@lem5762444 _120607) (@lem5762443 _120607 op x)). Qed.
Lemma lem5762446 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1586 _120607 op x) = (term1623 _120607 op x).
Proof. exact (TRANS (@lem5762422 _120607 op x) (@lem5762445 _120607 op x)). Qed.
Lemma lem5762447 {_120607 : Type'} (op : type1400 _120607) : (term1588 _120607 op) = (term1624 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5762446 _120607 op x)). Qed.
Lemma lem5762448 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762449 {_120607 : Type'} (op : type1400 _120607) : (term1589 _120607 op) = (term1625 _120607 op).
Proof. exact (MK_COMB (@lem5762448 _120607) (@lem5762447 _120607 op)). Qed.
Lemma lem5762450 {_120607 : Type'} (op : type1400 _120607) : (term1571 _120607 op) = (term1625 _120607 op).
Proof. exact (TRANS (@lem5762395 _120607 op) (@lem5762449 _120607 op)). Qed.
Lemma lem5762451 {_120607 : Type'} (op : type1400 _120607) : (term1400 _120607 op) = (term1625 _120607 op).
Proof. exact (TRANS (@lem5762368 _120607 op) (@lem5762450 _120607 op)). Qed.
Lemma lem5762452 {_120607 : Type'} (op : type1400 _120607) : (term1403 _120607 op) = (term1403 _120607 op).
Proof. exact (eq_refl (term1403 _120607 op)). Qed.
Lemma lem5762453 {_120607 : Type'} (op : type1400 _120607) : (term1404 _120607 op) = (term1626 _120607 op).
Proof. exact (MK_COMB (@lem5762452 _120607 op) (@lem5762451 _120607 op)). Qed.
Lemma lem5762455 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1627 A P Q) = (term1628 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5762456 {_120607 : Type'} (P : Prop) (Q : _120607 -> Prop) : (term1627 _120607 P Q) = (term1628 _120607 P Q).
Proof. exact (@lem5762455 _120607 P Q). Qed.
Lemma lem5762457 {_120607 : Type'} (op : type1400 _120607) : (term1629 _120607 op) = (term1630 _120607 op).
Proof. exact (@lem5762456 _120607 (term1402 _120607 op) (term1624 _120607 op)). Qed.
Lemma lem5762458 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1631 _120607 op x) = (term1623 _120607 op x).
Proof. exact (eq_refl (term1631 _120607 op x)). Qed.
Lemma lem5762459 {_120607 : Type'} (op : type1400 _120607) : (term1632 _120607 op) = (term1624 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5762458 _120607 op x)). Qed.
Lemma lem5762460 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762461 {_120607 : Type'} (op : type1400 _120607) : (term1633 _120607 op) = (term1625 _120607 op).
Proof. exact (MK_COMB (@lem5762460 _120607) (@lem5762459 _120607 op)). Qed.
Lemma lem5762462 {_120607 : Type'} (op : type1400 _120607) : (term1403 _120607 op) = (term1403 _120607 op).
Proof. exact (eq_refl (term1403 _120607 op)). Qed.
Lemma lem5762463 {_120607 : Type'} (op : type1400 _120607) : (term1629 _120607 op) = (term1626 _120607 op).
Proof. exact (MK_COMB (@lem5762462 _120607 op) (@lem5762461 _120607 op)). Qed.
Lemma lem5762464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5762465 {_120607 : Type'} (op : type1400 _120607) : (term1634 _120607 op) = (term1635 _120607 op).
Proof. exact (MK_COMB (@lem5762464) (@lem5762463 _120607 op)). Qed.
Lemma lem5762466 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1631 _120607 op x) = (term1623 _120607 op x).
Proof. exact (eq_refl (term1631 _120607 op x)). Qed.
Lemma lem5762467 {_120607 : Type'} (op : type1400 _120607) : (term1403 _120607 op) = (term1403 _120607 op).
Proof. exact (eq_refl (term1403 _120607 op)). Qed.
Lemma lem5762468 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1636 _120607 op x) = (term1637 _120607 op x).
Proof. exact (MK_COMB (@lem5762467 _120607 op) (@lem5762466 _120607 op x)). Qed.
Lemma lem5762469 {_120607 : Type'} (op : type1400 _120607) : (term1638 _120607 op) = (term1639 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5762468 _120607 op x)). Qed.
Lemma lem5762470 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762471 {_120607 : Type'} (op : type1400 _120607) : (term1630 _120607 op) = (term1640 _120607 op).
Proof. exact (MK_COMB (@lem5762470 _120607) (@lem5762469 _120607 op)). Qed.
Lemma lem5762472 {_120607 : Type'} (op : type1400 _120607) : ((term1629 _120607 op) = (term1630 _120607 op)) = ((term1626 _120607 op) = (term1640 _120607 op)).
Proof. exact (MK_COMB (@lem5762465 _120607 op) (@lem5762471 _120607 op)). Qed.
Lemma lem5762473 {_120607 : Type'} (op : type1400 _120607) : (term1626 _120607 op) = (term1640 _120607 op).
Proof. exact (EQ_MP (@lem5762472 _120607 op) (@lem5762457 _120607 op)). Qed.
Lemma lem5762475 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1627 A P Q) = (term1628 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5762476 {_120607 : Type'} (P : Prop) (Q : _120607 -> Prop) : (term1627 _120607 P Q) = (term1628 _120607 P Q).
Proof. exact (@lem5762475 _120607 P Q). Qed.
Lemma lem5762477 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1641 _120607 op x) = (term1642 _120607 op x).
Proof. exact (@lem5762476 _120607 (term1402 _120607 op) (term1622 _120607 op x)). Qed.
Lemma lem5762478 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1643 _120607 op x y) = (term1621 _120607 y op x).
Proof. exact (eq_refl (term1643 _120607 op x y)). Qed.
Lemma lem5762479 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1644 _120607 op x) = (term1622 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5762478 _120607 y op x)). Qed.
Lemma lem5762480 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762481 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1645 _120607 op x) = (term1623 _120607 op x).
Proof. exact (MK_COMB (@lem5762480 _120607) (@lem5762479 _120607 op x)). Qed.
Lemma lem5762482 {_120607 : Type'} (op : type1400 _120607) : (term1403 _120607 op) = (term1403 _120607 op).
Proof. exact (eq_refl (term1403 _120607 op)). Qed.
Lemma lem5762483 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1641 _120607 op x) = (term1637 _120607 op x).
Proof. exact (MK_COMB (@lem5762482 _120607 op) (@lem5762481 _120607 op x)). Qed.
Lemma lem5762484 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5762485 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1646 _120607 op x) = (term1647 _120607 op x).
Proof. exact (MK_COMB (@lem5762484) (@lem5762483 _120607 op x)). Qed.
Lemma lem5762486 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1643 _120607 op x y) = (term1621 _120607 y op x).
Proof. exact (eq_refl (term1643 _120607 op x y)). Qed.
Lemma lem5762487 {_120607 : Type'} (op : type1400 _120607) : (term1403 _120607 op) = (term1403 _120607 op).
Proof. exact (eq_refl (term1403 _120607 op)). Qed.
Lemma lem5762488 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1648 _120607 op x y) = (term1649 _120607 y op x).
Proof. exact (MK_COMB (@lem5762487 _120607 op) (@lem5762486 _120607 y op x)). Qed.
Lemma lem5762489 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1650 _120607 op x) = (term1651 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5762488 _120607 y op x)). Qed.
Lemma lem5762490 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762491 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1642 _120607 op x) = (term1652 _120607 op x).
Proof. exact (MK_COMB (@lem5762490 _120607) (@lem5762489 _120607 op x)). Qed.
Lemma lem5762492 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : ((term1641 _120607 op x) = (term1642 _120607 op x)) = ((term1637 _120607 op x) = (term1652 _120607 op x)).
Proof. exact (MK_COMB (@lem5762485 _120607 op x) (@lem5762491 _120607 op x)). Qed.
Lemma lem5762493 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1637 _120607 op x) = (term1652 _120607 op x).
Proof. exact (EQ_MP (@lem5762492 _120607 op x) (@lem5762477 _120607 op x)). Qed.
Lemma lem5762495 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1627 A P Q) = (term1628 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5762496 {_120607 : Type'} (P : Prop) (Q : _120607 -> Prop) : (term1627 _120607 P Q) = (term1628 _120607 P Q).
Proof. exact (@lem5762495 _120607 P Q). Qed.
Lemma lem5762497 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1653 _120607 y op x) = (term1654 _120607 y op x).
Proof. exact (@lem5762496 _120607 (term1402 _120607 op) (term1620 _120607 y op x)). Qed.
Lemma lem5762498 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1655 _120607 y op x z) = (term1618 _120607 y z op x).
Proof. exact (eq_refl (term1655 _120607 y op x z)). Qed.
Lemma lem5762499 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1656 _120607 y op x) = (term1620 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5762498 _120607 y z op x)). Qed.
Lemma lem5762500 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762501 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1657 _120607 y op x) = (term1621 _120607 y op x).
Proof. exact (MK_COMB (@lem5762500 _120607) (@lem5762499 _120607 y op x)). Qed.
Lemma lem5762502 {_120607 : Type'} (op : type1400 _120607) : (term1403 _120607 op) = (term1403 _120607 op).
Proof. exact (eq_refl (term1403 _120607 op)). Qed.
Lemma lem5762503 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1653 _120607 y op x) = (term1649 _120607 y op x).
Proof. exact (MK_COMB (@lem5762502 _120607 op) (@lem5762501 _120607 y op x)). Qed.
Lemma lem5762504 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5762505 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1658 _120607 y op x) = (term1659 _120607 y op x).
Proof. exact (MK_COMB (@lem5762504) (@lem5762503 _120607 y op x)). Qed.
Lemma lem5762506 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1655 _120607 y op x z) = (term1618 _120607 y z op x).
Proof. exact (eq_refl (term1655 _120607 y op x z)). Qed.
Lemma lem5762507 {_120607 : Type'} (op : type1400 _120607) : (term1403 _120607 op) = (term1403 _120607 op).
Proof. exact (eq_refl (term1403 _120607 op)). Qed.
Lemma lem5762508 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1660 _120607 y op x z) = (term1661 _120607 y z op x).
Proof. exact (MK_COMB (@lem5762507 _120607 op) (@lem5762506 _120607 y z op x)). Qed.
Lemma lem5762509 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1662 _120607 y op x) = (term1663 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5762508 _120607 y z op x)). Qed.
Lemma lem5762510 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762511 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1654 _120607 y op x) = (term1664 _120607 y op x).
Proof. exact (MK_COMB (@lem5762510 _120607) (@lem5762509 _120607 y op x)). Qed.
Lemma lem5762512 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : ((term1653 _120607 y op x) = (term1654 _120607 y op x)) = ((term1649 _120607 y op x) = (term1664 _120607 y op x)).
Proof. exact (MK_COMB (@lem5762505 _120607 y op x) (@lem5762511 _120607 y op x)). Qed.
Lemma lem5762513 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1649 _120607 y op x) = (term1664 _120607 y op x).
Proof. exact (EQ_MP (@lem5762512 _120607 y op x) (@lem5762497 _120607 y op x)). Qed.
Lemma lem5762514 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1651 _120607 op x) = (term1665 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5762513 _120607 y op x)). Qed.
Lemma lem5762515 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762516 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1652 _120607 op x) = (term1666 _120607 op x).
Proof. exact (MK_COMB (@lem5762515 _120607) (@lem5762514 _120607 op x)). Qed.
Lemma lem5762517 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1637 _120607 op x) = (term1666 _120607 op x).
Proof. exact (TRANS (@lem5762493 _120607 op x) (@lem5762516 _120607 op x)). Qed.
Lemma lem5762518 {_120607 : Type'} (op : type1400 _120607) : (term1639 _120607 op) = (term1667 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5762517 _120607 op x)). Qed.
Lemma lem5762519 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762520 {_120607 : Type'} (op : type1400 _120607) : (term1640 _120607 op) = (term1668 _120607 op).
Proof. exact (MK_COMB (@lem5762519 _120607) (@lem5762518 _120607 op)). Qed.
Lemma lem5762521 {_120607 : Type'} (op : type1400 _120607) : (term1626 _120607 op) = (term1668 _120607 op).
Proof. exact (TRANS (@lem5762473 _120607 op) (@lem5762520 _120607 op)). Qed.
Lemma lem5762522 {_120607 : Type'} (op : type1400 _120607) : (term1404 _120607 op) = (term1668 _120607 op).
Proof. exact (TRANS (@lem5762453 _120607 op) (@lem5762521 _120607 op)). Qed.
Lemma lem5762523 {_120607 : Type'} : (term1405 _120607) = (term1669 _120607).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5762522 _120607 op)). Qed.
Lemma lem5762524 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5762525 {_120607 : Type'} : (term1406 _120607) = (term1670 _120607).
Proof. exact (MK_COMB (@lem5762524 _120607) (@lem5762523 _120607)). Qed.
Lemma lem5762539 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1661 _120607 y z op x) = (term1671 _120607 y z op x).
Proof. exact (@lem19490 ((term1373 _120607 op x y) = (term1373 _120607 op y x)) (term1402 _120607 op) (term1563 _120607 y z op x)). Qed.
Lemma lem5762546 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1672 _120607 y z op x) = (term1673 _120607 y z op x).
Proof. exact (@lem19490 ((term1376 _120607 x op y z) = (term1382 _120607 op x y z)) (term1402 _120607 op) ((term1368 _120607 op x) = x)). Qed.
Lemma lem5762549 {_120607 : Type'} (op : type1400 _120607) (y : _120607) (x : _120607) : (term1674 _120607 op y x) = (term1674 _120607 op y x).
Proof. exact (eq_refl (term1674 _120607 op y x)). Qed.
Lemma lem5762550 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1671 _120607 y z op x) = (term1675 _120607 y z op x).
Proof. exact (MK_COMB (@lem5762549 _120607 op y x) (@lem5762546 _120607 y z op x)). Qed.
Lemma lem5762552 {_120607 : Type'} (y : _120607) (z : _120607) (op : type1400 _120607) (x : _120607) : (term1661 _120607 y z op x) = (term1675 _120607 y z op x).
Proof. exact (TRANS (@lem5762539 _120607 y z op x) (@lem5762550 _120607 y z op x)). Qed.
Lemma lem5762553 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1663 _120607 y op x) = (term1676 _120607 y op x).
Proof. exact (fun_ext (fun z : _120607 => @lem5762552 _120607 y z op x)). Qed.
Lemma lem5762554 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762555 {_120607 : Type'} (y : _120607) (op : type1400 _120607) (x : _120607) : (term1664 _120607 y op x) = (term1677 _120607 y op x).
Proof. exact (MK_COMB (@lem5762554 _120607) (@lem5762553 _120607 y op x)). Qed.
Lemma lem5762556 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1665 _120607 op x) = (term1678 _120607 op x).
Proof. exact (fun_ext (fun y : _120607 => @lem5762555 _120607 y op x)). Qed.
Lemma lem5762557 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762558 {_120607 : Type'} (op : type1400 _120607) (x : _120607) : (term1666 _120607 op x) = (term1679 _120607 op x).
Proof. exact (MK_COMB (@lem5762557 _120607) (@lem5762556 _120607 op x)). Qed.
Lemma lem5762559 {_120607 : Type'} (op : type1400 _120607) : (term1667 _120607 op) = (term1680 _120607 op).
Proof. exact (fun_ext (fun x : _120607 => @lem5762558 _120607 op x)). Qed.
Lemma lem5762560 {_120607 : Type'} : (@all _120607) = (@all _120607).
Proof. exact (eq_refl (@all _120607)). Qed.
Lemma lem5762561 {_120607 : Type'} (op : type1400 _120607) : (term1668 _120607 op) = (term1681 _120607 op).
Proof. exact (MK_COMB (@lem5762560 _120607) (@lem5762559 _120607 op)). Qed.
Lemma lem5762562 {_120607 : Type'} : (term1669 _120607) = (term1682 _120607).
Proof. exact (fun_ext (fun op : type1400 _120607 => @lem5762561 _120607 op)). Qed.
Lemma lem5762563 {_120607 : Type'} : (@all (_120607 -> _120607 -> _120607)) = (@all (_120607 -> _120607 -> _120607)).
Proof. exact (eq_refl (@all (_120607 -> _120607 -> _120607))). Qed.
Lemma lem5762564 {_120607 : Type'} : (term1670 _120607) = (term1683 _120607).
Proof. exact (MK_COMB (@lem5762563 _120607) (@lem5762562 _120607)). Qed.
Lemma lem5762565 {_120607 : Type'} : (term1406 _120607) = (term1683 _120607).
Proof. exact (TRANS (@lem5762525 _120607) (@lem5762564 _120607)). Qed.
Lemma lem5762566 {_120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1683 _120607.
Proof. exact (EQ_MP (@lem5762565 _120607) (@lem5761569 _120607 y z x h1)). Qed.
Lemma lem5762594 {_120607 : Type'} (_72576 : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1684 _120607 _72576.
Proof. exact (@lem5761902 _120607 y z x h1 _72576). Qed.
Lemma lem5762595 {_120607 : Type'} (_72576 : type1400 _120607) : (term1684 _120607 _72576) = (term1681 _120607 _72576).
Proof. exact (eq_refl (term1684 _120607 _72576)). Qed.
Lemma lem5762596 {_120607 : Type'} (_72576 : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1681 _120607 _72576.
Proof. exact (EQ_MP (@lem5762595 _120607 _72576) (@lem5762594 _120607 _72576 y z x h1)). Qed.
Lemma lem5762597 {_120607 : Type'} (_72576 : type1400 _120607) (_72577 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1685 _120607 _72576 _72577.
Proof. exact (@lem5762596 _120607 _72576 y z x h1 _72577). Qed.
Lemma lem5762598 {_120607 : Type'} (_72576 : type1400 _120607) (_72577 : _120607) : (term1685 _120607 _72576 _72577) = (term1679 _120607 _72576 _72577).
Proof. exact (eq_refl (term1685 _120607 _72576 _72577)). Qed.
Lemma lem5762599 {_120607 : Type'} (_72576 : type1400 _120607) (_72577 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1679 _120607 _72576 _72577.
Proof. exact (EQ_MP (@lem5762598 _120607 _72576 _72577) (@lem5762597 _120607 _72576 _72577 y z x h1)). Qed.
Lemma lem5762600 {_120607 : Type'} (_72576 : type1400 _120607) (_72577 : _120607) (_72578 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1686 _120607 _72576 _72577 _72578.
Proof. exact (@lem5762599 _120607 _72576 _72577 y z x h1 _72578). Qed.
Lemma lem5762601 {_120607 : Type'} (_72578 : _120607) (_72576 : type1400 _120607) (_72577 : _120607) : (term1686 _120607 _72576 _72577 _72578) = (term1677 _120607 _72578 _72576 _72577).
Proof. exact (eq_refl (term1686 _120607 _72576 _72577 _72578)). Qed.
Lemma lem5762602 {_120607 : Type'} (_72578 : _120607) (_72576 : type1400 _120607) (_72577 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1677 _120607 _72578 _72576 _72577.
Proof. exact (EQ_MP (@lem5762601 _120607 _72578 _72576 _72577) (@lem5762600 _120607 _72576 _72577 _72578 y z x h1)). Qed.
Lemma lem5762603 {_120607 : Type'} (_72578 : _120607) (_72576 : type1400 _120607) (_72577 : _120607) (_72579 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1687 _120607 _72578 _72576 _72577 _72579.
Proof. exact (@lem5762602 _120607 _72578 _72576 _72577 y z x h1 _72579). Qed.
Lemma lem5762604 {_120607 : Type'} (_72578 : _120607) (_72579 : _120607) (_72576 : type1400 _120607) (_72577 : _120607) : (term1687 _120607 _72578 _72576 _72577 _72579) = (term1675 _120607 _72578 _72579 _72576 _72577).
Proof. exact (eq_refl (term1687 _120607 _72578 _72576 _72577 _72579)). Qed.
Lemma lem5762605 {_120607 : Type'} (_72578 : _120607) (_72579 : _120607) (_72576 : type1400 _120607) (_72577 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1675 _120607 _72578 _72579 _72576 _72577.
Proof. exact (EQ_MP (@lem5762604 _120607 _72578 _72579 _72576 _72577) (@lem5762603 _120607 _72578 _72576 _72577 _72579 y z x h1)). Qed.
Lemma lem5762624 {_120607 : Type'} (_72586 : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1684 _120607 _72586.
Proof. exact (@lem5762566 _120607 y z x h1 _72586). Qed.
Lemma lem5762625 {_120607 : Type'} (_72586 : type1400 _120607) : (term1684 _120607 _72586) = (term1681 _120607 _72586).
Proof. exact (eq_refl (term1684 _120607 _72586)). Qed.
Lemma lem5762626 {_120607 : Type'} (_72586 : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1681 _120607 _72586.
Proof. exact (EQ_MP (@lem5762625 _120607 _72586) (@lem5762624 _120607 _72586 y z x h1)). Qed.
Lemma lem5762627 {_120607 : Type'} (_72586 : type1400 _120607) (_72587 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1685 _120607 _72586 _72587.
Proof. exact (@lem5762626 _120607 _72586 y z x h1 _72587). Qed.
Lemma lem5762628 {_120607 : Type'} (_72586 : type1400 _120607) (_72587 : _120607) : (term1685 _120607 _72586 _72587) = (term1679 _120607 _72586 _72587).
Proof. exact (eq_refl (term1685 _120607 _72586 _72587)). Qed.
Lemma lem5762629 {_120607 : Type'} (_72586 : type1400 _120607) (_72587 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1679 _120607 _72586 _72587.
Proof. exact (EQ_MP (@lem5762628 _120607 _72586 _72587) (@lem5762627 _120607 _72586 _72587 y z x h1)). Qed.
Lemma lem5762630 {_120607 : Type'} (_72586 : type1400 _120607) (_72587 : _120607) (_72588 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1686 _120607 _72586 _72587 _72588.
Proof. exact (@lem5762629 _120607 _72586 _72587 y z x h1 _72588). Qed.
Lemma lem5762631 {_120607 : Type'} (_72588 : _120607) (_72586 : type1400 _120607) (_72587 : _120607) : (term1686 _120607 _72586 _72587 _72588) = (term1677 _120607 _72588 _72586 _72587).
Proof. exact (eq_refl (term1686 _120607 _72586 _72587 _72588)). Qed.
Lemma lem5762632 {_120607 : Type'} (_72588 : _120607) (_72586 : type1400 _120607) (_72587 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1677 _120607 _72588 _72586 _72587.
Proof. exact (EQ_MP (@lem5762631 _120607 _72588 _72586 _72587) (@lem5762630 _120607 _72586 _72587 _72588 y z x h1)). Qed.
Lemma lem5762633 {_120607 : Type'} (_72588 : _120607) (_72586 : type1400 _120607) (_72587 : _120607) (_72589 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1687 _120607 _72588 _72586 _72587 _72589.
Proof. exact (@lem5762632 _120607 _72588 _72586 _72587 y z x h1 _72589). Qed.
Lemma lem5762634 {_120607 : Type'} (_72588 : _120607) (_72589 : _120607) (_72586 : type1400 _120607) (_72587 : _120607) : (term1687 _120607 _72588 _72586 _72587 _72589) = (term1675 _120607 _72588 _72589 _72586 _72587).
Proof. exact (eq_refl (term1687 _120607 _72588 _72586 _72587 _72589)). Qed.
Lemma lem5762635 {_120607 : Type'} (_72588 : _120607) (_72589 : _120607) (_72586 : type1400 _120607) (_72587 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1675 _120607 _72588 _72589 _72586 _72587.
Proof. exact (EQ_MP (@lem5762634 _120607 _72588 _72589 _72586 _72587) (@lem5762633 _120607 _72588 _72586 _72587 _72589 y z x h1)). Qed.
Lemma lem5762636 {_120607 : Type'} (_72578 : _120607) (_72579 : _120607) (_72576 : type1400 _120607) (_72577 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1673 _120607 _72578 _72579 _72576 _72577.
Proof. exact (proj2 (@lem5762605 _120607 _72578 _72579 _72576 _72577 y z x h1)). Qed.
Lemma lem5762644 {_120607 : Type'} (_72588 : _120607) (_72589 : _120607) (_72586 : type1400 _120607) (_72587 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1673 _120607 _72588 _72589 _72586 _72587.
Proof. exact (proj2 (@lem5762635 _120607 _72588 _72589 _72586 _72587 y z x h1)). Qed.
Lemma lem5762669 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : term1514 _120592 _120607 s f op) : term1510 _120592 _120607 s f op.
Proof. exact (proj2 (@lem5761571 _120592 _120607 s f op h1)). Qed.
Lemma lem5762675 {_120607 : Type'} (_72576 : type1400 _120607) (_72578 : _120607) (_72577 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1688 _120607 _72576 _72578 _72577.
Proof. exact (proj1 (@lem5762605 _120607 _72578 (@el _120607) _72576 _72577 y z x h1)). Qed.
Lemma lem5762687 {_120607 : Type'} (_72576 : type1400 _120607) (_72577 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1689 _120607 _72576 _72577.
Proof. exact (proj2 (@lem5762636 _120607 (@el _120607) (@el _120607) _72576 _72577 y z x h1)). Qed.
Lemma lem5762717 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term1497 _120592 s t) : term1497 _120592 s t.
Proof. exact (h1). Qed.
Lemma lem5762755 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1504 _120592 _120607 s x' op t f) : term1476 _120592 _120607 s x' op t f.
Proof. exact (proj2 (@lem5761575 _120592 _120607 s x' op t f h1)). Qed.
Lemma lem5762771 {_120607 : Type'} (_72586 : type1400 _120607) (_72588 : _120607) (_72587 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1688 _120607 _72586 _72588 _72587.
Proof. exact (proj1 (@lem5762635 _120607 _72588 (@el _120607) _72586 _72587 y z x h1)). Qed.
Lemma lem5762777 {_120607 : Type'} (_72586 : type1400 _120607) (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1690 _120607 _72586 _72587 _72588 _72589.
Proof. exact (proj1 (@lem5762644 _120607 _72588 _72589 _72586 _72587 y z x h1)). Qed.
Lemma lem5762928 {_120607 : Type'} (x : _120607) (y : _120607) (z : _120607) : term1691 _120607 x y z.
Proof. exact (@lem21385 _120607 x y z). Qed.
Lemma lem5762952 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op.
Proof. exact (EQ_MP (@lem5760635 _120607 op) (@lem5759757 _120607 op h1)). Qed.
Lemma lem5762953 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : term1692 _120607 op.
Proof. exact (fun h0 : term1402 _120607 op => @lem5762952 _120607 op h1). Qed.
Lemma lem5762955 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5762956 {_120607 : Type'} (op : type1400 _120607) : (term1692 _120607 op) = (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op).
Proof. exact (@lem5762955 (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op)). Qed.
Lemma lem5762957 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op.
Proof. exact (EQ_MP (@lem5762956 _120607 op) (@lem5762953 _120607 op h1)). Qed.
Lemma lem5762963 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5762964 {_120607 : Type'} (_72577 : _120607) (_72576 : type1400 _120607) : (term1689 _120607 _72576 _72577) = (term1693 _120607 _72577 _72576).
Proof. exact (@lem5762963 ((term1368 _120607 _72576 _72577) = _72577) (term1402 _120607 _72576)). Qed.
Lemma lem5762972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5762973 {_120607 : Type'} (_72577 : _120607) (_72576 : type1400 _120607) : (term1694 _120607 _72576 _72577) = (term1695 _120607 _72577 _72576).
Proof. exact (MK_COMB (@lem5762972) (@lem5762964 _120607 _72577 _72576)). Qed.
Lemma lem5762981 {_120607 : Type'} (_72577 : _120607) (_72576 : type1400 _120607) : (term1693 _120607 _72577 _72576) = (term1693 _120607 _72577 _72576).
Proof. exact (eq_refl (term1693 _120607 _72577 _72576)). Qed.
Lemma lem5762982 {_120607 : Type'} (_72577 : _120607) (_72576 : type1400 _120607) : ((term1689 _120607 _72576 _72577) = (term1693 _120607 _72577 _72576)) = ((term1693 _120607 _72577 _72576) = (term1693 _120607 _72577 _72576)).
Proof. exact (MK_COMB (@lem5762973 _120607 _72577 _72576) (@lem5762981 _120607 _72577 _72576)). Qed.
Lemma lem5762984 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5762985 (x : Prop) : (x = x) = True.
Proof. exact (@lem5762984 Prop x). Qed.
Lemma lem5762986 {_120607 : Type'} (_72577 : _120607) (_72576 : type1400 _120607) : ((term1693 _120607 _72577 _72576) = (term1693 _120607 _72577 _72576)) = True.
Proof. exact (@lem5762985 (term1693 _120607 _72577 _72576)). Qed.
Lemma lem5762987 {_120607 : Type'} (_72577 : _120607) (_72576 : type1400 _120607) : ((term1689 _120607 _72576 _72577) = (term1693 _120607 _72577 _72576)) = True.
Proof. exact (TRANS (@lem5762982 _120607 _72577 _72576) (@lem5762986 _120607 _72577 _72576)). Qed.
Lemma lem5762988 {_120607 : Type'} (_72577 : _120607) (_72576 : type1400 _120607) : True = ((term1689 _120607 _72576 _72577) = (term1693 _120607 _72577 _72576)).
Proof. exact (SYM (@lem5762987 _120607 _72577 _72576)). Qed.
Lemma lem5762989 {_120607 : Type'} (_72577 : _120607) (_72576 : type1400 _120607) : (term1689 _120607 _72576 _72577) = (term1693 _120607 _72577 _72576).
Proof. exact (EQ_MP (@lem5762988 _120607 _72577 _72576) (@lem0)). Qed.
Lemma lem5762990 {_120607 : Type'} (_72577 : _120607) (_72576 : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1693 _120607 _72577 _72576.
Proof. exact (EQ_MP (@lem5762989 _120607 _72577 _72576) (@lem5762687 _120607 _72576 _72577 y z x h1)). Qed.
Lemma lem5762992 (b : Prop) (a : Prop) : (a \/ b) = (term1696 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5762993 {_120607 : Type'} (_72576 : type1400 _120607) (_72577 : _120607) : (term1693 _120607 _72577 _72576) = (term1697 _120607 _72576 _72577).
Proof. exact (@lem5762992 (term1402 _120607 _72576) ((term1368 _120607 _72576 _72577) = _72577)). Qed.
Lemma lem5762995 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5762996 {_120607 : Type'} (_72576 : type1400 _120607) : (term1698 _120607 _72576) = (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) _72576).
Proof. exact (@lem5762995 (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) _72576)). Qed.
Lemma lem5762997 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5762998 {_120607 : Type'} (_72576 : type1400 _120607) : (term1699 _120607 _72576) = (term1700 _120607 _72576).
Proof. exact (MK_COMB (@lem5762997) (@lem5762996 _120607 _72576)). Qed.
Lemma lem5762999 {_120607 : Type'} (_72576 : type1400 _120607) (_72577 : _120607) : ((term1368 _120607 _72576 _72577) = _72577) = ((term1368 _120607 _72576 _72577) = _72577).
Proof. exact (eq_refl ((term1368 _120607 _72576 _72577) = _72577)). Qed.
Lemma lem5763000 {_120607 : Type'} (_72576 : type1400 _120607) (_72577 : _120607) : (term1697 _120607 _72576 _72577) = (term1701 _120607 _72576 _72577).
Proof. exact (MK_COMB (@lem5762998 _120607 _72576) (@lem5762999 _120607 _72576 _72577)). Qed.
Lemma lem5763001 {_120607 : Type'} (_72576 : type1400 _120607) (_72577 : _120607) : (term1693 _120607 _72577 _72576) = (term1701 _120607 _72576 _72577).
Proof. exact (TRANS (@lem5762993 _120607 _72576 _72577) (@lem5763000 _120607 _72576 _72577)). Qed.
Lemma lem5763004 {_120607 : Type'} (_72576 : type1400 _120607) (_72577 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1701 _120607 _72576 _72577.
Proof. exact (EQ_MP (@lem5763001 _120607 _72576 _72577) (@lem5762990 _120607 _72577 _72576 y z x h1)). Qed.
Lemma lem5763005 {_120607 : Type'} (_72576 : type1400 _120607) (_72577 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1701 _120607 _72576 _72577.
Proof. exact (@lem5763004 _120607 _72576 _72577 y z x h1). Qed.
Lemma lem5763006 {_120607 : Type'} (op : type1400 _120607) (_72577 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1701 _120607 op _72577.
Proof. exact (@lem5763005 _120607 op _72577 y z x h1). Qed.
Lemma lem5763009 {_120607 : Type'} (_72577 : _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1368 _120607 op _72577) = _72577.
Proof. exact (@lem5763006 _120607 op _72577 y z x h2 (@lem5762957 _120607 op h1)). Qed.
Lemma lem5763010 {_120607 : Type'} (_72577 : _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1368 _120607 op _72577) = _72577.
Proof. exact (@lem5763009 _120607 _72577 op y z x h1 h2). Qed.
Lemma lem5763011 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1702 _120592 _120607 op s f) = (term1457 _120592 _120607 op s f).
Proof. exact (@lem5763010 _120607 (term1457 _120592 _120607 op s f) op y z x h1 h2). Qed.
Lemma lem5763012 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : term1703 _120592 _120607 op s f.
Proof. exact (fun h0 : term1704 _120592 _120607 op s f => @lem5763011 _120592 _120607 s f op y z x h1 h2). Qed.
Lemma lem5763014 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5763015 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term1703 _120592 _120607 op s f) = ((term1702 _120592 _120607 op s f) = (term1457 _120592 _120607 op s f)).
Proof. exact (@lem5763014 ((term1702 _120592 _120607 op s f) = (term1457 _120592 _120607 op s f))). Qed.
Lemma lem5763016 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1702 _120592 _120607 op s f) = (term1457 _120592 _120607 op s f).
Proof. exact (EQ_MP (@lem5763015 _120592 _120607 op s f) (@lem5763012 _120592 _120607 s f op y z x h1 h2)). Qed.
Lemma lem5763018 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op.
Proof. exact (EQ_MP (@lem5760635 _120607 op) (@lem5759757 _120607 op h1)). Qed.
Lemma lem5763019 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : term1692 _120607 op.
Proof. exact (fun h0 : term1402 _120607 op => @lem5763018 _120607 op h1). Qed.
Lemma lem5763021 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5763022 {_120607 : Type'} (op : type1400 _120607) : (term1692 _120607 op) = (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op).
Proof. exact (@lem5763021 (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op)). Qed.
Lemma lem5763023 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op.
Proof. exact (EQ_MP (@lem5763022 _120607 op) (@lem5763019 _120607 op h1)). Qed.
Lemma lem5763029 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5763030 {_120607 : Type'} (_72578 : _120607) (_72577 : _120607) (_72576 : type1400 _120607) : (term1688 _120607 _72576 _72578 _72577) = (term1705 _120607 _72578 _72577 _72576).
Proof. exact (@lem5763029 ((term1373 _120607 _72576 _72577 _72578) = (term1373 _120607 _72576 _72578 _72577)) (term1402 _120607 _72576)). Qed.
Lemma lem5763038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5763039 {_120607 : Type'} (_72578 : _120607) (_72577 : _120607) (_72576 : type1400 _120607) : (term1706 _120607 _72576 _72578 _72577) = (term1707 _120607 _72578 _72577 _72576).
Proof. exact (MK_COMB (@lem5763038) (@lem5763030 _120607 _72578 _72577 _72576)). Qed.
Lemma lem5763047 {_120607 : Type'} (_72578 : _120607) (_72577 : _120607) (_72576 : type1400 _120607) : (term1705 _120607 _72578 _72577 _72576) = (term1705 _120607 _72578 _72577 _72576).
Proof. exact (eq_refl (term1705 _120607 _72578 _72577 _72576)). Qed.
Lemma lem5763048 {_120607 : Type'} (_72578 : _120607) (_72577 : _120607) (_72576 : type1400 _120607) : ((term1688 _120607 _72576 _72578 _72577) = (term1705 _120607 _72578 _72577 _72576)) = ((term1705 _120607 _72578 _72577 _72576) = (term1705 _120607 _72578 _72577 _72576)).
Proof. exact (MK_COMB (@lem5763039 _120607 _72578 _72577 _72576) (@lem5763047 _120607 _72578 _72577 _72576)). Qed.
Lemma lem5763050 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5763051 (x : Prop) : (x = x) = True.
Proof. exact (@lem5763050 Prop x). Qed.
Lemma lem5763052 {_120607 : Type'} (_72578 : _120607) (_72577 : _120607) (_72576 : type1400 _120607) : ((term1705 _120607 _72578 _72577 _72576) = (term1705 _120607 _72578 _72577 _72576)) = True.
Proof. exact (@lem5763051 (term1705 _120607 _72578 _72577 _72576)). Qed.
Lemma lem5763053 {_120607 : Type'} (_72578 : _120607) (_72577 : _120607) (_72576 : type1400 _120607) : ((term1688 _120607 _72576 _72578 _72577) = (term1705 _120607 _72578 _72577 _72576)) = True.
Proof. exact (TRANS (@lem5763048 _120607 _72578 _72577 _72576) (@lem5763052 _120607 _72578 _72577 _72576)). Qed.
Lemma lem5763054 {_120607 : Type'} (_72578 : _120607) (_72577 : _120607) (_72576 : type1400 _120607) : True = ((term1688 _120607 _72576 _72578 _72577) = (term1705 _120607 _72578 _72577 _72576)).
Proof. exact (SYM (@lem5763053 _120607 _72578 _72577 _72576)). Qed.
Lemma lem5763055 {_120607 : Type'} (_72578 : _120607) (_72577 : _120607) (_72576 : type1400 _120607) : (term1688 _120607 _72576 _72578 _72577) = (term1705 _120607 _72578 _72577 _72576).
Proof. exact (EQ_MP (@lem5763054 _120607 _72578 _72577 _72576) (@lem0)). Qed.
Lemma lem5763056 {_120607 : Type'} (_72578 : _120607) (_72577 : _120607) (_72576 : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1705 _120607 _72578 _72577 _72576.
Proof. exact (EQ_MP (@lem5763055 _120607 _72578 _72577 _72576) (@lem5762675 _120607 _72576 _72578 _72577 y z x h1)). Qed.
Lemma lem5763058 (b : Prop) (a : Prop) : (a \/ b) = (term1696 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5763059 {_120607 : Type'} (_72576 : type1400 _120607) (_72578 : _120607) (_72577 : _120607) : (term1705 _120607 _72578 _72577 _72576) = (term1708 _120607 _72576 _72578 _72577).
Proof. exact (@lem5763058 (term1402 _120607 _72576) ((term1373 _120607 _72576 _72577 _72578) = (term1373 _120607 _72576 _72578 _72577))). Qed.
Lemma lem5763061 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5763062 {_120607 : Type'} (_72576 : type1400 _120607) : (term1698 _120607 _72576) = (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) _72576).
Proof. exact (@lem5763061 (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) _72576)). Qed.
Lemma lem5763063 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5763064 {_120607 : Type'} (_72576 : type1400 _120607) : (term1699 _120607 _72576) = (term1700 _120607 _72576).
Proof. exact (MK_COMB (@lem5763063) (@lem5763062 _120607 _72576)). Qed.
Lemma lem5763065 {_120607 : Type'} (_72576 : type1400 _120607) (_72578 : _120607) (_72577 : _120607) : ((term1373 _120607 _72576 _72577 _72578) = (term1373 _120607 _72576 _72578 _72577)) = ((term1373 _120607 _72576 _72577 _72578) = (term1373 _120607 _72576 _72578 _72577)).
Proof. exact (eq_refl ((term1373 _120607 _72576 _72577 _72578) = (term1373 _120607 _72576 _72578 _72577))). Qed.
Lemma lem5763066 {_120607 : Type'} (_72576 : type1400 _120607) (_72578 : _120607) (_72577 : _120607) : (term1708 _120607 _72576 _72578 _72577) = (term1709 _120607 _72576 _72578 _72577).
Proof. exact (MK_COMB (@lem5763064 _120607 _72576) (@lem5763065 _120607 _72576 _72578 _72577)). Qed.
Lemma lem5763067 {_120607 : Type'} (_72576 : type1400 _120607) (_72578 : _120607) (_72577 : _120607) : (term1705 _120607 _72578 _72577 _72576) = (term1709 _120607 _72576 _72578 _72577).
Proof. exact (TRANS (@lem5763059 _120607 _72576 _72578 _72577) (@lem5763066 _120607 _72576 _72578 _72577)). Qed.
Lemma lem5763070 {_120607 : Type'} (_72576 : type1400 _120607) (_72578 : _120607) (_72577 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1709 _120607 _72576 _72578 _72577.
Proof. exact (EQ_MP (@lem5763067 _120607 _72576 _72578 _72577) (@lem5763056 _120607 _72578 _72577 _72576 y z x h1)). Qed.
Lemma lem5763071 {_120607 : Type'} (_72576 : type1400 _120607) (_72578 : _120607) (_72577 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1709 _120607 _72576 _72578 _72577.
Proof. exact (@lem5763070 _120607 _72576 _72578 _72577 y z x h1). Qed.
Lemma lem5763072 {_120607 : Type'} (op : type1400 _120607) (_72578 : _120607) (_72577 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1709 _120607 op _72578 _72577.
Proof. exact (@lem5763071 _120607 op _72578 _72577 y z x h1). Qed.
Lemma lem5763075 {_120607 : Type'} (_72578 : _120607) (_72577 : _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1373 _120607 op _72577 _72578) = (term1373 _120607 op _72578 _72577).
Proof. exact (@lem5763072 _120607 op _72578 _72577 y z x h2 (@lem5763023 _120607 op h1)). Qed.
Lemma lem5763076 {_120607 : Type'} (_72578 : _120607) (_72577 : _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1373 _120607 op _72577 _72578) = (term1373 _120607 op _72578 _72577).
Proof. exact (@lem5763075 _120607 _72578 _72577 op y z x h1 h2). Qed.
Lemma lem5763077 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1702 _120592 _120607 op s f) = (term1507 _120592 _120607 s f op).
Proof. exact (@lem5763076 _120607 (term1457 _120592 _120607 op s f) (@I ((_120607 -> _120607 -> _120607) -> _120607) (@neutral _120607) op) op y z x h1 h2). Qed.
Lemma lem5763078 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : term1710 _120592 _120607 s f op.
Proof. exact (fun h0 : term1711 _120592 _120607 s f op => @lem5763077 _120592 _120607 s f op y z x h1 h2). Qed.
Lemma lem5763080 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5763081 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term1710 _120592 _120607 s f op) = ((term1702 _120592 _120607 op s f) = (term1507 _120592 _120607 s f op)).
Proof. exact (@lem5763080 ((term1702 _120592 _120607 op s f) = (term1507 _120592 _120607 s f op))). Qed.
Lemma lem5763082 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1702 _120592 _120607 op s f) = (term1507 _120592 _120607 s f op).
Proof. exact (EQ_MP (@lem5763081 _120592 _120607 s f op) (@lem5763078 _120592 _120607 s f op y z x h1 h2)). Qed.
Lemma lem5763100 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5763101 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1712 _120607 x y z) = (term1713 _120607 y x z).
Proof. exact (@lem5763100 (y = z) (term649 _120607 x z)). Qed.
Lemma lem5763111 {_120607 : Type'} (x : _120607) (y : _120607) : (term1714 _120607 x y) = (term1714 _120607 x y).
Proof. exact (eq_refl (term1714 _120607 x y)). Qed.
Lemma lem5763112 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1691 _120607 x y z) = (term1715 _120607 y x z).
Proof. exact (MK_COMB (@lem5763111 _120607 x y) (@lem5763101 _120607 y x z)). Qed.
Lemma lem5763116 (q : Prop) (p : Prop) (r : Prop) : (term1716 p q r) = (term1716 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5763117 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1715 _120607 y x z) = (term1717 _120607 y x z).
Proof. exact (@lem5763116 (y = z) (term649 _120607 x y) (term649 _120607 x z)). Qed.
Lemma lem5763139 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1691 _120607 x y z) = (term1717 _120607 y x z).
Proof. exact (TRANS (@lem5763112 _120607 y x z) (@lem5763117 _120607 y x z)). Qed.
Lemma lem5763140 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5763141 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1718 _120607 x y z) = (term1719 _120607 y x z).
Proof. exact (MK_COMB (@lem5763140) (@lem5763139 _120607 y x z)). Qed.
Lemma lem5763163 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1717 _120607 y x z) = (term1717 _120607 y x z).
Proof. exact (eq_refl (term1717 _120607 y x z)). Qed.
Lemma lem5763164 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : ((term1691 _120607 x y z) = (term1717 _120607 y x z)) = ((term1717 _120607 y x z) = (term1717 _120607 y x z)).
Proof. exact (MK_COMB (@lem5763141 _120607 y x z) (@lem5763163 _120607 y x z)). Qed.
Lemma lem5763166 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5763167 (x : Prop) : (x = x) = True.
Proof. exact (@lem5763166 Prop x). Qed.
Lemma lem5763168 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : ((term1717 _120607 y x z) = (term1717 _120607 y x z)) = True.
Proof. exact (@lem5763167 (term1717 _120607 y x z)). Qed.
Lemma lem5763169 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : ((term1691 _120607 x y z) = (term1717 _120607 y x z)) = True.
Proof. exact (TRANS (@lem5763164 _120607 y x z) (@lem5763168 _120607 y x z)). Qed.
Lemma lem5763170 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : True = ((term1691 _120607 x y z) = (term1717 _120607 y x z)).
Proof. exact (SYM (@lem5763169 _120607 y x z)). Qed.
Lemma lem5763171 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1691 _120607 x y z) = (term1717 _120607 y x z).
Proof. exact (EQ_MP (@lem5763170 _120607 y x z) (@lem0)). Qed.
Lemma lem5763172 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : term1717 _120607 y x z.
Proof. exact (EQ_MP (@lem5763171 _120607 y x z) (@lem5762928 _120607 x y z)). Qed.
Lemma lem5763174 (b : Prop) (a : Prop) : (a \/ b) = (term1696 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5763175 {_120607 : Type'} (x : _120607) (y : _120607) (z : _120607) : (term1717 _120607 y x z) = (term1720 _120607 x y z).
Proof. exact (@lem5763174 (term1721 _120607 y x z) (y = z)). Qed.
Lemma lem5763177 (a : Prop) (b : Prop) : (term1722 a b) = (term1723 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5763178 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1724 _120607 y x z) = (term1725 _120607 y x z).
Proof. exact (@lem5763177 (term649 _120607 x y) (term649 _120607 x z)). Qed.
Lemma lem5763180 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5763181 {_120607 : Type'} (x : _120607) (y : _120607) : (term1726 _120607 x y) = (x = y).
Proof. exact (@lem5763180 (x = y)). Qed.
Lemma lem5763182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5763183 {_120607 : Type'} (x : _120607) (y : _120607) : (term1727 _120607 x y) = (term1728 _120607 x y).
Proof. exact (MK_COMB (@lem5763182) (@lem5763181 _120607 x y)). Qed.
Lemma lem5763185 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5763186 {_120607 : Type'} (x : _120607) (z : _120607) : (term1726 _120607 x z) = (x = z).
Proof. exact (@lem5763185 (x = z)). Qed.
Lemma lem5763187 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1725 _120607 y x z) = (term1729 _120607 y x z).
Proof. exact (MK_COMB (@lem5763183 _120607 x y) (@lem5763186 _120607 x z)). Qed.
Lemma lem5763188 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1724 _120607 y x z) = (term1729 _120607 y x z).
Proof. exact (TRANS (@lem5763178 _120607 y x z) (@lem5763187 _120607 y x z)). Qed.
Lemma lem5763189 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5763190 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1730 _120607 y x z) = (term1731 _120607 y x z).
Proof. exact (MK_COMB (@lem5763189) (@lem5763188 _120607 y x z)). Qed.
Lemma lem5763191 {_120607 : Type'} (y : _120607) (z : _120607) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5763192 {_120607 : Type'} (x : _120607) (y : _120607) (z : _120607) : (term1720 _120607 x y z) = (term1732 _120607 x y z).
Proof. exact (MK_COMB (@lem5763190 _120607 y x z) (@lem5763191 _120607 y z)). Qed.
Lemma lem5763193 {_120607 : Type'} (x : _120607) (y : _120607) (z : _120607) : (term1717 _120607 y x z) = (term1732 _120607 x y z).
Proof. exact (TRANS (@lem5763175 _120607 x y z) (@lem5763192 _120607 x y z)). Qed.
Lemma lem5763195 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : term1733 _120592 _120607 s f op.
Proof. exact (conj (@lem5763016 _120592 _120607 s f op y z x h1 h2) (@lem5763082 _120592 _120607 s f op y z x h1 h2)). Qed.
Lemma lem5763197 {_120607 : Type'} (x : _120607) (y : _120607) (z : _120607) : term1732 _120607 x y z.
Proof. exact (EQ_MP (@lem5763193 _120607 x y z) (@lem5763172 _120607 y x z)). Qed.
Lemma lem5763198 {_120607 : Type'} (x : _120607) (y : _120607) (z : _120607) : term1732 _120607 x y z.
Proof. exact (@lem5763197 _120607 x y z). Qed.
Lemma lem5763199 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : term1734 _120592 _120607 s f op.
Proof. exact (@lem5763198 _120607 (term1702 _120592 _120607 op s f) (term1457 _120592 _120607 op s f) (term1507 _120592 _120607 s f op)). Qed.
Lemma lem5763202 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1457 _120592 _120607 op s f) = (term1507 _120592 _120607 s f op).
Proof. exact (@lem5763199 _120592 _120607 s f op (@lem5763195 _120592 _120607 s f op y z x h1 h2)). Qed.
Lemma lem5763203 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1457 _120592 _120607 op s f) = (term1507 _120592 _120607 s f op).
Proof. exact (@lem5763202 _120592 _120607 s f op y z x h1 h2). Qed.
Lemma lem5763204 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : term1735 _120592 _120607 s f op.
Proof. exact (fun h0 : term1510 _120592 _120607 s f op => @lem5763203 _120592 _120607 s f op y z x h1 h2). Qed.
Lemma lem5763206 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5763207 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term1735 _120592 _120607 s f op) = ((term1457 _120592 _120607 op s f) = (term1507 _120592 _120607 s f op)).
Proof. exact (@lem5763206 ((term1457 _120592 _120607 op s f) = (term1507 _120592 _120607 s f op))). Qed.
Lemma lem5763208 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1457 _120592 _120607 op s f) = (term1507 _120592 _120607 s f op).
Proof. exact (EQ_MP (@lem5763207 _120592 _120607 s f op) (@lem5763204 _120592 _120607 s f op y z x h1 h2)). Qed.
Lemma lem5763211 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5763213 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) : (term1510 _120592 _120607 s f op) = (term1736 _120592 _120607 s f op).
Proof. exact (@lem5763211 ((term1457 _120592 _120607 op s f) = (term1507 _120592 _120607 s f op))). Qed.
Lemma lem5763216 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : term1514 _120592 _120607 s f op) : term1736 _120592 _120607 s f op.
Proof. exact (EQ_MP (@lem5763213 _120592 _120607 s f op) (@lem5762669 _120592 _120607 s f op h1)). Qed.
Lemma lem5763219 {_120592 _120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) (h3 : term1514 _120592 _120607 s f op) : False.
Proof. exact (@lem5763216 _120592 _120607 s f op h3 (@lem5763208 _120592 _120607 s f op y z x h1 h2)). Qed.
Lemma lem5763220 {_120592 _120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) (h3 : term1514 _120592 _120607 s f op) : term668.
Proof. exact (fun h0 : ~ False => @lem5763219 _120592 _120607 y z x s f op h1 h2 h3). Qed.
Lemma lem5763222 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5763223 : term668 = False.
Proof. exact (@lem5763222 False). Qed.
Lemma lem5763224 {_120592 _120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) (h3 : term1514 _120592 _120607 s f op) : False.
Proof. exact (EQ_MP (@lem5763223) (@lem5763220 _120592 _120607 y z x s f op h1 h2 h3)). Qed.
Lemma lem5763427 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1504 _120592 _120607 s x' op t f) : term1477 _120592 s t.
Proof. exact (proj2 (@lem5761578 _120592 _120607 s x' op t f h1)). Qed.
Lemma lem5763428 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1504 _120592 _120607 s x' op t f) : term1737 _120592 s t.
Proof. exact (fun h0 : term1497 _120592 s t => @lem5763427 _120592 _120607 s x' op t f h1). Qed.
Lemma lem5763430 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5763431 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (term1737 _120592 s t) = (term1477 _120592 s t).
Proof. exact (@lem5763430 (term1477 _120592 s t)). Qed.
Lemma lem5763432 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1504 _120592 _120607 s x' op t f) : term1477 _120592 s t.
Proof. exact (EQ_MP (@lem5763431 _120592 s t) (@lem5763428 _120592 _120607 s x' op t f h1)). Qed.
Lemma lem5763435 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5763437 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (term1497 _120592 s t) = (term1738 _120592 s t).
Proof. exact (@lem5763435 (term1477 _120592 s t)). Qed.
Lemma lem5763440 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term1497 _120592 s t) : term1738 _120592 s t.
Proof. exact (EQ_MP (@lem5763437 _120592 s t) (@lem5762717 _120592 s t h1)). Qed.
Lemma lem5763443 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1497 _120592 s t) (h2 : term1504 _120592 _120607 s x' op t f) : False.
Proof. exact (@lem5763440 _120592 s t h1 (@lem5763432 _120592 _120607 s x' op t f h2)). Qed.
Lemma lem5763444 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1497 _120592 s t) (h2 : term1504 _120592 _120607 s x' op t f) : term668.
Proof. exact (fun h0 : ~ False => @lem5763443 _120592 _120607 s x' op t f h1 h2). Qed.
Lemma lem5763446 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5763447 : term668 = False.
Proof. exact (@lem5763446 False). Qed.
Lemma lem5763448 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1497 _120592 s t) (h2 : term1504 _120592 _120607 s x' op t f) : False.
Proof. exact (EQ_MP (@lem5763447) (@lem5763444 _120592 _120607 s x' op t f h1 h2)). Qed.
Lemma lem5763622 {_120607 : Type'} : (@I (_120607 -> _120607)) = (@I (_120607 -> _120607)).
Proof. exact (eq_refl (@I (_120607 -> _120607))). Qed.
Lemma lem5763623 {_120607 : Type'} (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) (h1 : _72714 = _72716) : _72714 = _72716.
Proof. exact (h1). Qed.
Lemma lem5763624 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (h1 : _72715 = _72717) : _72715 = _72717.
Proof. exact (h1). Qed.
Lemma lem5763625 {_120607 : Type'} (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) (h1 : _72714 = _72716) : (@I (_120607 -> _120607) _72714) = (@I (_120607 -> _120607) _72716).
Proof. exact (MK_COMB (@lem5763622 _120607) (@lem5763623 _120607 _72714 _72716 h1)). Qed.
Lemma lem5763626 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) (h1 : _72715 = _72717) (h2 : _72714 = _72716) : (@I (_120607 -> _120607) _72714 _72715) = (@I (_120607 -> _120607) _72716 _72717).
Proof. exact (MK_COMB (@lem5763625 _120607 _72714 _72716 h2) (@lem5763624 _120607 _72715 _72717 h1)). Qed.
Lemma lem5763627 {_120607 : Type'} (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) (_72715 : _120607) (_72717 : _120607) (h1 : _72715 = _72717) : term1739 _120607 _72714 _72715 _72716 _72717.
Proof. exact (fun h0 : _72714 = _72716 => @lem5763626 _120607 _72715 _72717 _72714 _72716 h1 h0). Qed.
Lemma lem5763629 (a : Prop) (b : Prop) : (a -> b) = (term1740 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5763630 {_120607 : Type'} (_72714 : _120607 -> _120607) (_72715 : _120607) (_72716 : _120607 -> _120607) (_72717 : _120607) : (term1739 _120607 _72714 _72715 _72716 _72717) = (term1741 _120607 _72714 _72715 _72716 _72717).
Proof. exact (@lem5763629 (_72714 = _72716) ((@I (_120607 -> _120607) _72714 _72715) = (@I (_120607 -> _120607) _72716 _72717))). Qed.
Lemma lem5763631 {_120607 : Type'} (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) (_72715 : _120607) (_72717 : _120607) (h1 : _72715 = _72717) : term1741 _120607 _72714 _72715 _72716 _72717.
Proof. exact (EQ_MP (@lem5763630 _120607 _72714 _72715 _72716 _72717) (@lem5763627 _120607 _72714 _72716 _72715 _72717 h1)). Qed.
Lemma lem5763632 {_120607 : Type'} (_72714 : _120607 -> _120607) (_72715 : _120607) (_72716 : _120607 -> _120607) (_72717 : _120607) : term1742 _120607 _72714 _72715 _72716 _72717.
Proof. exact (fun h0 : _72715 = _72717 => @lem5763631 _120607 _72714 _72716 _72715 _72717 h0). Qed.
Lemma lem5763634 (a : Prop) (b : Prop) : (a -> b) = (term1740 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5763635 {_120607 : Type'} (_72714 : _120607 -> _120607) (_72715 : _120607) (_72716 : _120607 -> _120607) (_72717 : _120607) : (term1742 _120607 _72714 _72715 _72716 _72717) = (term1743 _120607 _72714 _72715 _72716 _72717).
Proof. exact (@lem5763634 (_72715 = _72717) (term1741 _120607 _72714 _72715 _72716 _72717)). Qed.
Lemma lem5763636 {_120607 : Type'} (_72714 : _120607 -> _120607) (_72715 : _120607) (_72716 : _120607 -> _120607) (_72717 : _120607) : term1743 _120607 _72714 _72715 _72716 _72717.
Proof. exact (EQ_MP (@lem5763635 _120607 _72714 _72715 _72716 _72717) (@lem5763632 _120607 _72714 _72715 _72716 _72717)). Qed.
Lemma lem5763653 {_120607 : Type'} (x : _120607) (y : _120607) (z : _120607) : term1691 _120607 x y z.
Proof. exact (@lem21385 _120607 x y z). Qed.
Lemma lem5763685 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op.
Proof. exact (EQ_MP (@lem5760635 _120607 op) (@lem5759757 _120607 op h1)). Qed.
Lemma lem5763686 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : term1692 _120607 op.
Proof. exact (fun h0 : term1402 _120607 op => @lem5763685 _120607 op h1). Qed.
Lemma lem5763688 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5763689 {_120607 : Type'} (op : type1400 _120607) : (term1692 _120607 op) = (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op).
Proof. exact (@lem5763688 (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op)). Qed.
Lemma lem5763690 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op.
Proof. exact (EQ_MP (@lem5763689 _120607 op) (@lem5763686 _120607 op h1)). Qed.
Lemma lem5763696 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5763697 {_120607 : Type'} (_72588 : _120607) (_72587 : _120607) (_72586 : type1400 _120607) : (term1688 _120607 _72586 _72588 _72587) = (term1705 _120607 _72588 _72587 _72586).
Proof. exact (@lem5763696 ((term1373 _120607 _72586 _72587 _72588) = (term1373 _120607 _72586 _72588 _72587)) (term1402 _120607 _72586)). Qed.
Lemma lem5763705 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5763706 {_120607 : Type'} (_72588 : _120607) (_72587 : _120607) (_72586 : type1400 _120607) : (term1706 _120607 _72586 _72588 _72587) = (term1707 _120607 _72588 _72587 _72586).
Proof. exact (MK_COMB (@lem5763705) (@lem5763697 _120607 _72588 _72587 _72586)). Qed.
Lemma lem5763714 {_120607 : Type'} (_72588 : _120607) (_72587 : _120607) (_72586 : type1400 _120607) : (term1705 _120607 _72588 _72587 _72586) = (term1705 _120607 _72588 _72587 _72586).
Proof. exact (eq_refl (term1705 _120607 _72588 _72587 _72586)). Qed.
Lemma lem5763715 {_120607 : Type'} (_72588 : _120607) (_72587 : _120607) (_72586 : type1400 _120607) : ((term1688 _120607 _72586 _72588 _72587) = (term1705 _120607 _72588 _72587 _72586)) = ((term1705 _120607 _72588 _72587 _72586) = (term1705 _120607 _72588 _72587 _72586)).
Proof. exact (MK_COMB (@lem5763706 _120607 _72588 _72587 _72586) (@lem5763714 _120607 _72588 _72587 _72586)). Qed.
Lemma lem5763717 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5763718 (x : Prop) : (x = x) = True.
Proof. exact (@lem5763717 Prop x). Qed.
Lemma lem5763719 {_120607 : Type'} (_72588 : _120607) (_72587 : _120607) (_72586 : type1400 _120607) : ((term1705 _120607 _72588 _72587 _72586) = (term1705 _120607 _72588 _72587 _72586)) = True.
Proof. exact (@lem5763718 (term1705 _120607 _72588 _72587 _72586)). Qed.
Lemma lem5763720 {_120607 : Type'} (_72588 : _120607) (_72587 : _120607) (_72586 : type1400 _120607) : ((term1688 _120607 _72586 _72588 _72587) = (term1705 _120607 _72588 _72587 _72586)) = True.
Proof. exact (TRANS (@lem5763715 _120607 _72588 _72587 _72586) (@lem5763719 _120607 _72588 _72587 _72586)). Qed.
Lemma lem5763721 {_120607 : Type'} (_72588 : _120607) (_72587 : _120607) (_72586 : type1400 _120607) : True = ((term1688 _120607 _72586 _72588 _72587) = (term1705 _120607 _72588 _72587 _72586)).
Proof. exact (SYM (@lem5763720 _120607 _72588 _72587 _72586)). Qed.
Lemma lem5763722 {_120607 : Type'} (_72588 : _120607) (_72587 : _120607) (_72586 : type1400 _120607) : (term1688 _120607 _72586 _72588 _72587) = (term1705 _120607 _72588 _72587 _72586).
Proof. exact (EQ_MP (@lem5763721 _120607 _72588 _72587 _72586) (@lem0)). Qed.
Lemma lem5763723 {_120607 : Type'} (_72588 : _120607) (_72587 : _120607) (_72586 : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1705 _120607 _72588 _72587 _72586.
Proof. exact (EQ_MP (@lem5763722 _120607 _72588 _72587 _72586) (@lem5762771 _120607 _72586 _72588 _72587 y z x h1)). Qed.
Lemma lem5763725 (b : Prop) (a : Prop) : (a \/ b) = (term1696 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5763726 {_120607 : Type'} (_72586 : type1400 _120607) (_72588 : _120607) (_72587 : _120607) : (term1705 _120607 _72588 _72587 _72586) = (term1708 _120607 _72586 _72588 _72587).
Proof. exact (@lem5763725 (term1402 _120607 _72586) ((term1373 _120607 _72586 _72587 _72588) = (term1373 _120607 _72586 _72588 _72587))). Qed.
Lemma lem5763728 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5763729 {_120607 : Type'} (_72586 : type1400 _120607) : (term1698 _120607 _72586) = (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) _72586).
Proof. exact (@lem5763728 (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) _72586)). Qed.
Lemma lem5763730 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5763731 {_120607 : Type'} (_72586 : type1400 _120607) : (term1699 _120607 _72586) = (term1700 _120607 _72586).
Proof. exact (MK_COMB (@lem5763730) (@lem5763729 _120607 _72586)). Qed.
Lemma lem5763732 {_120607 : Type'} (_72586 : type1400 _120607) (_72588 : _120607) (_72587 : _120607) : ((term1373 _120607 _72586 _72587 _72588) = (term1373 _120607 _72586 _72588 _72587)) = ((term1373 _120607 _72586 _72587 _72588) = (term1373 _120607 _72586 _72588 _72587)).
Proof. exact (eq_refl ((term1373 _120607 _72586 _72587 _72588) = (term1373 _120607 _72586 _72588 _72587))). Qed.
Lemma lem5763733 {_120607 : Type'} (_72586 : type1400 _120607) (_72588 : _120607) (_72587 : _120607) : (term1708 _120607 _72586 _72588 _72587) = (term1709 _120607 _72586 _72588 _72587).
Proof. exact (MK_COMB (@lem5763731 _120607 _72586) (@lem5763732 _120607 _72586 _72588 _72587)). Qed.
Lemma lem5763734 {_120607 : Type'} (_72586 : type1400 _120607) (_72588 : _120607) (_72587 : _120607) : (term1705 _120607 _72588 _72587 _72586) = (term1709 _120607 _72586 _72588 _72587).
Proof. exact (TRANS (@lem5763726 _120607 _72586 _72588 _72587) (@lem5763733 _120607 _72586 _72588 _72587)). Qed.
Lemma lem5763737 {_120607 : Type'} (_72586 : type1400 _120607) (_72588 : _120607) (_72587 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1709 _120607 _72586 _72588 _72587.
Proof. exact (EQ_MP (@lem5763734 _120607 _72586 _72588 _72587) (@lem5763723 _120607 _72588 _72587 _72586 y z x h1)). Qed.
Lemma lem5763738 {_120607 : Type'} (_72586 : type1400 _120607) (_72588 : _120607) (_72587 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1709 _120607 _72586 _72588 _72587.
Proof. exact (@lem5763737 _120607 _72586 _72588 _72587 y z x h1). Qed.
Lemma lem5763739 {_120607 : Type'} (op : type1400 _120607) (_72588 : _120607) (_72587 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1709 _120607 op _72588 _72587.
Proof. exact (@lem5763738 _120607 op _72588 _72587 y z x h1). Qed.
Lemma lem5763742 {_120607 : Type'} (_72588 : _120607) (_72587 : _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1373 _120607 op _72587 _72588) = (term1373 _120607 op _72588 _72587).
Proof. exact (@lem5763739 _120607 op _72588 _72587 y z x h2 (@lem5763690 _120607 op h1)). Qed.
Lemma lem5763743 {_120607 : Type'} (_72588 : _120607) (_72587 : _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1373 _120607 op _72587 _72588) = (term1373 _120607 op _72588 _72587).
Proof. exact (@lem5763742 _120607 _72588 _72587 op y z x h1 h2). Qed.
Lemma lem5763744 {_120592 _120607 : Type'} (x' : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1744 _120592 _120607 s op t f x') = (term1467 _120592 _120607 x' s op t f).
Proof. exact (@lem5763743 _120607 (@I (_120592 -> _120607) f x') (term1462 _120592 _120607 s op t f) op y z x h1 h2). Qed.
Lemma lem5763745 {_120592 _120607 : Type'} (x' : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : term1745 _120592 _120607 x' s op t f.
Proof. exact (fun h0 : term1746 _120592 _120607 x' s op t f => @lem5763744 _120592 _120607 x' s t f op y z x h1 h2). Qed.
Lemma lem5763747 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5763748 {_120592 _120607 : Type'} (x' : _120592) (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1745 _120592 _120607 x' s op t f) = ((term1744 _120592 _120607 s op t f x') = (term1467 _120592 _120607 x' s op t f)).
Proof. exact (@lem5763747 ((term1744 _120592 _120607 s op t f x') = (term1467 _120592 _120607 x' s op t f))). Qed.
Lemma lem5763749 {_120592 _120607 : Type'} (x' : _120592) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1744 _120592 _120607 s op t f x') = (term1467 _120592 _120607 x' s op t f).
Proof. exact (EQ_MP (@lem5763748 _120592 _120607 x' s op t f) (@lem5763745 _120592 _120607 x' s t f op y z x h1 h2)). Qed.
Lemma lem5763751 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op.
Proof. exact (EQ_MP (@lem5760635 _120607 op) (@lem5759757 _120607 op h1)). Qed.
Lemma lem5763752 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : term1692 _120607 op.
Proof. exact (fun h0 : term1402 _120607 op => @lem5763751 _120607 op h1). Qed.
Lemma lem5763754 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5763755 {_120607 : Type'} (op : type1400 _120607) : (term1692 _120607 op) = (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op).
Proof. exact (@lem5763754 (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op)). Qed.
Lemma lem5763756 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op.
Proof. exact (EQ_MP (@lem5763755 _120607 op) (@lem5763752 _120607 op h1)). Qed.
Lemma lem5763762 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5763763 {_120607 : Type'} (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) (_72586 : type1400 _120607) : (term1690 _120607 _72586 _72587 _72588 _72589) = (term1747 _120607 _72587 _72588 _72589 _72586).
Proof. exact (@lem5763762 ((term1376 _120607 _72587 _72586 _72588 _72589) = (term1382 _120607 _72586 _72587 _72588 _72589)) (term1402 _120607 _72586)). Qed.
Lemma lem5763771 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5763772 {_120607 : Type'} (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) (_72586 : type1400 _120607) : (term1748 _120607 _72586 _72587 _72588 _72589) = (term1749 _120607 _72587 _72588 _72589 _72586).
Proof. exact (MK_COMB (@lem5763771) (@lem5763763 _120607 _72587 _72588 _72589 _72586)). Qed.
Lemma lem5763780 {_120607 : Type'} (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) (_72586 : type1400 _120607) : (term1747 _120607 _72587 _72588 _72589 _72586) = (term1747 _120607 _72587 _72588 _72589 _72586).
Proof. exact (eq_refl (term1747 _120607 _72587 _72588 _72589 _72586)). Qed.
Lemma lem5763781 {_120607 : Type'} (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) (_72586 : type1400 _120607) : ((term1690 _120607 _72586 _72587 _72588 _72589) = (term1747 _120607 _72587 _72588 _72589 _72586)) = ((term1747 _120607 _72587 _72588 _72589 _72586) = (term1747 _120607 _72587 _72588 _72589 _72586)).
Proof. exact (MK_COMB (@lem5763772 _120607 _72587 _72588 _72589 _72586) (@lem5763780 _120607 _72587 _72588 _72589 _72586)). Qed.
Lemma lem5763783 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5763784 (x : Prop) : (x = x) = True.
Proof. exact (@lem5763783 Prop x). Qed.
Lemma lem5763785 {_120607 : Type'} (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) (_72586 : type1400 _120607) : ((term1747 _120607 _72587 _72588 _72589 _72586) = (term1747 _120607 _72587 _72588 _72589 _72586)) = True.
Proof. exact (@lem5763784 (term1747 _120607 _72587 _72588 _72589 _72586)). Qed.
Lemma lem5763786 {_120607 : Type'} (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) (_72586 : type1400 _120607) : ((term1690 _120607 _72586 _72587 _72588 _72589) = (term1747 _120607 _72587 _72588 _72589 _72586)) = True.
Proof. exact (TRANS (@lem5763781 _120607 _72587 _72588 _72589 _72586) (@lem5763785 _120607 _72587 _72588 _72589 _72586)). Qed.
Lemma lem5763787 {_120607 : Type'} (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) (_72586 : type1400 _120607) : True = ((term1690 _120607 _72586 _72587 _72588 _72589) = (term1747 _120607 _72587 _72588 _72589 _72586)).
Proof. exact (SYM (@lem5763786 _120607 _72587 _72588 _72589 _72586)). Qed.
Lemma lem5763788 {_120607 : Type'} (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) (_72586 : type1400 _120607) : (term1690 _120607 _72586 _72587 _72588 _72589) = (term1747 _120607 _72587 _72588 _72589 _72586).
Proof. exact (EQ_MP (@lem5763787 _120607 _72587 _72588 _72589 _72586) (@lem0)). Qed.
Lemma lem5763789 {_120607 : Type'} (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) (_72586 : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1747 _120607 _72587 _72588 _72589 _72586.
Proof. exact (EQ_MP (@lem5763788 _120607 _72587 _72588 _72589 _72586) (@lem5762777 _120607 _72586 _72587 _72588 _72589 y z x h1)). Qed.
Lemma lem5763791 (b : Prop) (a : Prop) : (a \/ b) = (term1696 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5763792 {_120607 : Type'} (_72586 : type1400 _120607) (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) : (term1747 _120607 _72587 _72588 _72589 _72586) = (term1750 _120607 _72586 _72587 _72588 _72589).
Proof. exact (@lem5763791 (term1402 _120607 _72586) ((term1376 _120607 _72587 _72586 _72588 _72589) = (term1382 _120607 _72586 _72587 _72588 _72589))). Qed.
Lemma lem5763794 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5763795 {_120607 : Type'} (_72586 : type1400 _120607) : (term1698 _120607 _72586) = (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) _72586).
Proof. exact (@lem5763794 (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) _72586)). Qed.
Lemma lem5763796 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5763797 {_120607 : Type'} (_72586 : type1400 _120607) : (term1699 _120607 _72586) = (term1700 _120607 _72586).
Proof. exact (MK_COMB (@lem5763796) (@lem5763795 _120607 _72586)). Qed.
Lemma lem5763798 {_120607 : Type'} (_72586 : type1400 _120607) (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) : ((term1376 _120607 _72587 _72586 _72588 _72589) = (term1382 _120607 _72586 _72587 _72588 _72589)) = ((term1376 _120607 _72587 _72586 _72588 _72589) = (term1382 _120607 _72586 _72587 _72588 _72589)).
Proof. exact (eq_refl ((term1376 _120607 _72587 _72586 _72588 _72589) = (term1382 _120607 _72586 _72587 _72588 _72589))). Qed.
Lemma lem5763799 {_120607 : Type'} (_72586 : type1400 _120607) (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) : (term1750 _120607 _72586 _72587 _72588 _72589) = (term1751 _120607 _72586 _72587 _72588 _72589).
Proof. exact (MK_COMB (@lem5763797 _120607 _72586) (@lem5763798 _120607 _72586 _72587 _72588 _72589)). Qed.
Lemma lem5763800 {_120607 : Type'} (_72586 : type1400 _120607) (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) : (term1747 _120607 _72587 _72588 _72589 _72586) = (term1751 _120607 _72586 _72587 _72588 _72589).
Proof. exact (TRANS (@lem5763792 _120607 _72586 _72587 _72588 _72589) (@lem5763799 _120607 _72586 _72587 _72588 _72589)). Qed.
Lemma lem5763803 {_120607 : Type'} (_72586 : type1400 _120607) (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1751 _120607 _72586 _72587 _72588 _72589.
Proof. exact (EQ_MP (@lem5763800 _120607 _72586 _72587 _72588 _72589) (@lem5763789 _120607 _72587 _72588 _72589 _72586 y z x h1)). Qed.
Lemma lem5763804 {_120607 : Type'} (_72586 : type1400 _120607) (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1751 _120607 _72586 _72587 _72588 _72589.
Proof. exact (@lem5763803 _120607 _72586 _72587 _72588 _72589 y z x h1). Qed.
Lemma lem5763805 {_120607 : Type'} (op : type1400 _120607) (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1751 _120607 op _72587 _72588 _72589.
Proof. exact (@lem5763804 _120607 op _72587 _72588 _72589 y z x h1). Qed.
Lemma lem5763808 {_120607 : Type'} (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1376 _120607 _72587 op _72588 _72589) = (term1382 _120607 op _72587 _72588 _72589).
Proof. exact (@lem5763805 _120607 op _72587 _72588 _72589 y z x h2 (@lem5763756 _120607 op h1)). Qed.
Lemma lem5763809 {_120607 : Type'} (_72587 : _120607) (_72588 : _120607) (_72589 : _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1376 _120607 _72587 op _72588 _72589) = (term1382 _120607 op _72587 _72588 _72589).
Proof. exact (@lem5763808 _120607 _72587 _72588 _72589 op y z x h1 h2). Qed.
Lemma lem5763810 {_120592 _120607 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (x' : _120592) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1752 _120592 _120607 s op t f x') = (term1744 _120592 _120607 s op t f x').
Proof. exact (@lem5763809 _120607 (term1457 _120592 _120607 op s f) (term1457 _120592 _120607 op t f) (@I (_120592 -> _120607) f x') op y z x h1 h2). Qed.
Lemma lem5763811 {_120592 _120607 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (x' : _120592) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : term1753 _120592 _120607 s op t f x'.
Proof. exact (fun h0 : term1754 _120592 _120607 s op t f x' => @lem5763810 _120592 _120607 s t f x' op y z x h1 h2). Qed.
Lemma lem5763813 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5763814 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (x' : _120592) : (term1753 _120592 _120607 s op t f x') = ((term1752 _120592 _120607 s op t f x') = (term1744 _120592 _120607 s op t f x')).
Proof. exact (@lem5763813 ((term1752 _120592 _120607 s op t f x') = (term1744 _120592 _120607 s op t f x'))). Qed.
Lemma lem5763815 {_120592 _120607 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (x' : _120592) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1752 _120592 _120607 s op t f x') = (term1744 _120592 _120607 s op t f x').
Proof. exact (EQ_MP (@lem5763814 _120592 _120607 s op t f x') (@lem5763811 _120592 _120607 s t f x' op y z x h1 h2)). Qed.
Lemma lem5763817 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op.
Proof. exact (EQ_MP (@lem5760635 _120607 op) (@lem5759757 _120607 op h1)). Qed.
Lemma lem5763818 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : term1692 _120607 op.
Proof. exact (fun h0 : term1402 _120607 op => @lem5763817 _120607 op h1). Qed.
Lemma lem5763820 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5763821 {_120607 : Type'} (op : type1400 _120607) : (term1692 _120607 op) = (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op).
Proof. exact (@lem5763820 (@I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op)). Qed.
Lemma lem5763822 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @I ((_120607 -> _120607 -> _120607) -> Prop) (@monoidal _120607) op.
Proof. exact (EQ_MP (@lem5763821 _120607 op) (@lem5763818 _120607 op h1)). Qed.
Lemma lem5763824 {_120607 : Type'} (_72586 : type1400 _120607) (_72588 : _120607) (_72587 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1709 _120607 _72586 _72588 _72587.
Proof. exact (EQ_MP (@lem5763734 _120607 _72586 _72588 _72587) (@lem5763723 _120607 _72588 _72587 _72586 y z x h1)). Qed.
Lemma lem5763825 {_120607 : Type'} (_72586 : type1400 _120607) (_72588 : _120607) (_72587 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1709 _120607 _72586 _72588 _72587.
Proof. exact (@lem5763824 _120607 _72586 _72588 _72587 y z x h1). Qed.
Lemma lem5763826 {_120607 : Type'} (op : type1400 _120607) (_72588 : _120607) (_72587 : _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term1355 _120607 y z x) : term1709 _120607 op _72588 _72587.
Proof. exact (@lem5763825 _120607 op _72588 _72587 y z x h1). Qed.
Lemma lem5763829 {_120607 : Type'} (_72588 : _120607) (_72587 : _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1373 _120607 op _72587 _72588) = (term1373 _120607 op _72588 _72587).
Proof. exact (@lem5763826 _120607 op _72588 _72587 y z x h2 (@lem5763822 _120607 op h1)). Qed.
Lemma lem5763830 {_120607 : Type'} (_72588 : _120607) (_72587 : _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1373 _120607 op _72587 _72588) = (term1373 _120607 op _72588 _72587).
Proof. exact (@lem5763829 _120607 _72588 _72587 op y z x h1 h2). Qed.
Lemma lem5763831 {_120592 _120607 : Type'} (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1755 _120592 _120607 op t f x') = (term1470 _120592 _120607 x' op t f).
Proof. exact (@lem5763830 _120607 (@I (_120592 -> _120607) f x') (term1457 _120592 _120607 op t f) op y z x h1 h2). Qed.
Lemma lem5763832 {_120592 _120607 : Type'} (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : term1756 _120592 _120607 x' op t f.
Proof. exact (fun h0 : term1757 _120592 _120607 x' op t f => @lem5763831 _120592 _120607 x' t f op y z x h1 h2). Qed.
Lemma lem5763834 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5763835 {_120592 _120607 : Type'} (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1756 _120592 _120607 x' op t f) = ((term1755 _120592 _120607 op t f x') = (term1470 _120592 _120607 x' op t f)).
Proof. exact (@lem5763834 ((term1755 _120592 _120607 op t f x') = (term1470 _120592 _120607 x' op t f))). Qed.
Lemma lem5763836 {_120592 _120607 : Type'} (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1755 _120592 _120607 op t f x') = (term1470 _120592 _120607 x' op t f).
Proof. exact (EQ_MP (@lem5763835 _120592 _120607 x' op t f) (@lem5763832 _120592 _120607 x' t f op y z x h1 h2)). Qed.
Lemma lem5763838 {_120607 : Type'} (x : _120607 -> _120607) : x = x.
Proof. exact (@lem21386 (_120607 -> _120607) x). Qed.
Lemma lem5763839 {_120607 : Type'} (x : _120607 -> _120607) : x = x.
Proof. exact (@lem5763838 _120607 x). Qed.
Lemma lem5763840 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term1460 _120592 _120607 op s f) = (term1460 _120592 _120607 op s f).
Proof. exact (@lem5763839 _120607 (term1460 _120592 _120607 op s f)). Qed.
Lemma lem5763841 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : term1758 _120592 _120607 op s f.
Proof. exact (fun h0 : term1759 _120592 _120607 op s f => @lem5763840 _120592 _120607 op s f). Qed.
Lemma lem5763843 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5763844 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term1758 _120592 _120607 op s f) = ((term1460 _120592 _120607 op s f) = (term1460 _120592 _120607 op s f)).
Proof. exact (@lem5763843 ((term1460 _120592 _120607 op s f) = (term1460 _120592 _120607 op s f))). Qed.
Lemma lem5763845 {_120592 _120607 : Type'} (op : type1400 _120607) (s : _120592 -> Prop) (f : _120592 -> _120607) : (term1460 _120592 _120607 op s f) = (term1460 _120592 _120607 op s f).
Proof. exact (EQ_MP (@lem5763844 _120592 _120607 op s f) (@lem5763841 _120592 _120607 op s f)). Qed.
Lemma lem5763863 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5763864 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : (term1741 _120607 _72714 _72715 _72716 _72717) = (term1760 _120607 _72715 _72717 _72714 _72716).
Proof. exact (@lem5763863 ((@I (_120607 -> _120607) _72714 _72715) = (@I (_120607 -> _120607) _72716 _72717)) (term1761 _120607 _72714 _72716)). Qed.
Lemma lem5763874 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) : (term1714 _120607 _72715 _72717) = (term1714 _120607 _72715 _72717).
Proof. exact (eq_refl (term1714 _120607 _72715 _72717)). Qed.
Lemma lem5763875 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : (term1743 _120607 _72714 _72715 _72716 _72717) = (term1762 _120607 _72715 _72717 _72714 _72716).
Proof. exact (MK_COMB (@lem5763874 _120607 _72715 _72717) (@lem5763864 _120607 _72715 _72717 _72714 _72716)). Qed.
Lemma lem5763879 (q : Prop) (p : Prop) (r : Prop) : (term1716 p q r) = (term1716 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5763880 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : (term1762 _120607 _72715 _72717 _72714 _72716) = (term1763 _120607 _72715 _72717 _72714 _72716).
Proof. exact (@lem5763879 ((@I (_120607 -> _120607) _72714 _72715) = (@I (_120607 -> _120607) _72716 _72717)) (term649 _120607 _72715 _72717) (term1761 _120607 _72714 _72716)). Qed.
Lemma lem5763902 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : (term1743 _120607 _72714 _72715 _72716 _72717) = (term1763 _120607 _72715 _72717 _72714 _72716).
Proof. exact (TRANS (@lem5763875 _120607 _72715 _72717 _72714 _72716) (@lem5763880 _120607 _72715 _72717 _72714 _72716)). Qed.
Lemma lem5763903 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5763904 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : (term1764 _120607 _72714 _72715 _72716 _72717) = (term1765 _120607 _72715 _72717 _72714 _72716).
Proof. exact (MK_COMB (@lem5763903) (@lem5763902 _120607 _72715 _72717 _72714 _72716)). Qed.
Lemma lem5763926 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : (term1763 _120607 _72715 _72717 _72714 _72716) = (term1763 _120607 _72715 _72717 _72714 _72716).
Proof. exact (eq_refl (term1763 _120607 _72715 _72717 _72714 _72716)). Qed.
Lemma lem5763927 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : ((term1743 _120607 _72714 _72715 _72716 _72717) = (term1763 _120607 _72715 _72717 _72714 _72716)) = ((term1763 _120607 _72715 _72717 _72714 _72716) = (term1763 _120607 _72715 _72717 _72714 _72716)).
Proof. exact (MK_COMB (@lem5763904 _120607 _72715 _72717 _72714 _72716) (@lem5763926 _120607 _72715 _72717 _72714 _72716)). Qed.
Lemma lem5763929 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5763930 (x : Prop) : (x = x) = True.
Proof. exact (@lem5763929 Prop x). Qed.
Lemma lem5763931 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : ((term1763 _120607 _72715 _72717 _72714 _72716) = (term1763 _120607 _72715 _72717 _72714 _72716)) = True.
Proof. exact (@lem5763930 (term1763 _120607 _72715 _72717 _72714 _72716)). Qed.
Lemma lem5763932 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : ((term1743 _120607 _72714 _72715 _72716 _72717) = (term1763 _120607 _72715 _72717 _72714 _72716)) = True.
Proof. exact (TRANS (@lem5763927 _120607 _72715 _72717 _72714 _72716) (@lem5763931 _120607 _72715 _72717 _72714 _72716)). Qed.
Lemma lem5763933 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : True = ((term1743 _120607 _72714 _72715 _72716 _72717) = (term1763 _120607 _72715 _72717 _72714 _72716)).
Proof. exact (SYM (@lem5763932 _120607 _72715 _72717 _72714 _72716)). Qed.
Lemma lem5763934 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : (term1743 _120607 _72714 _72715 _72716 _72717) = (term1763 _120607 _72715 _72717 _72714 _72716).
Proof. exact (EQ_MP (@lem5763933 _120607 _72715 _72717 _72714 _72716) (@lem0)). Qed.
Lemma lem5763935 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : term1763 _120607 _72715 _72717 _72714 _72716.
Proof. exact (EQ_MP (@lem5763934 _120607 _72715 _72717 _72714 _72716) (@lem5763636 _120607 _72714 _72715 _72716 _72717)). Qed.
Lemma lem5763937 (b : Prop) (a : Prop) : (a \/ b) = (term1696 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5763938 {_120607 : Type'} (_72714 : _120607 -> _120607) (_72715 : _120607) (_72716 : _120607 -> _120607) (_72717 : _120607) : (term1763 _120607 _72715 _72717 _72714 _72716) = (term1766 _120607 _72714 _72715 _72716 _72717).
Proof. exact (@lem5763937 (term1767 _120607 _72715 _72717 _72714 _72716) ((@I (_120607 -> _120607) _72714 _72715) = (@I (_120607 -> _120607) _72716 _72717))). Qed.
Lemma lem5763940 (a : Prop) (b : Prop) : (term1722 a b) = (term1723 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5763941 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : (term1768 _120607 _72715 _72717 _72714 _72716) = (term1769 _120607 _72715 _72717 _72714 _72716).
Proof. exact (@lem5763940 (term649 _120607 _72715 _72717) (term1761 _120607 _72714 _72716)). Qed.
Lemma lem5763943 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5763944 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) : (term1726 _120607 _72715 _72717) = (_72715 = _72717).
Proof. exact (@lem5763943 (_72715 = _72717)). Qed.
Lemma lem5763945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5763946 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) : (term1727 _120607 _72715 _72717) = (term1728 _120607 _72715 _72717).
Proof. exact (MK_COMB (@lem5763945) (@lem5763944 _120607 _72715 _72717)). Qed.
Lemma lem5763948 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5763949 {_120607 : Type'} (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : (term1770 _120607 _72714 _72716) = (_72714 = _72716).
Proof. exact (@lem5763948 (_72714 = _72716)). Qed.
Lemma lem5763950 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : (term1769 _120607 _72715 _72717 _72714 _72716) = (term1771 _120607 _72715 _72717 _72714 _72716).
Proof. exact (MK_COMB (@lem5763946 _120607 _72715 _72717) (@lem5763949 _120607 _72714 _72716)). Qed.
Lemma lem5763951 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : (term1768 _120607 _72715 _72717 _72714 _72716) = (term1771 _120607 _72715 _72717 _72714 _72716).
Proof. exact (TRANS (@lem5763941 _120607 _72715 _72717 _72714 _72716) (@lem5763950 _120607 _72715 _72717 _72714 _72716)). Qed.
Lemma lem5763952 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5763953 {_120607 : Type'} (_72715 : _120607) (_72717 : _120607) (_72714 : _120607 -> _120607) (_72716 : _120607 -> _120607) : (term1772 _120607 _72715 _72717 _72714 _72716) = (term1773 _120607 _72715 _72717 _72714 _72716).
Proof. exact (MK_COMB (@lem5763952) (@lem5763951 _120607 _72715 _72717 _72714 _72716)). Qed.
Lemma lem5763954 {_120607 : Type'} (_72714 : _120607 -> _120607) (_72715 : _120607) (_72716 : _120607 -> _120607) (_72717 : _120607) : ((@I (_120607 -> _120607) _72714 _72715) = (@I (_120607 -> _120607) _72716 _72717)) = ((@I (_120607 -> _120607) _72714 _72715) = (@I (_120607 -> _120607) _72716 _72717)).
Proof. exact (eq_refl ((@I (_120607 -> _120607) _72714 _72715) = (@I (_120607 -> _120607) _72716 _72717))). Qed.
Lemma lem5763955 {_120607 : Type'} (_72714 : _120607 -> _120607) (_72715 : _120607) (_72716 : _120607 -> _120607) (_72717 : _120607) : (term1766 _120607 _72714 _72715 _72716 _72717) = (term1774 _120607 _72714 _72715 _72716 _72717).
Proof. exact (MK_COMB (@lem5763953 _120607 _72715 _72717 _72714 _72716) (@lem5763954 _120607 _72714 _72715 _72716 _72717)). Qed.
Lemma lem5763956 {_120607 : Type'} (_72714 : _120607 -> _120607) (_72715 : _120607) (_72716 : _120607 -> _120607) (_72717 : _120607) : (term1763 _120607 _72715 _72717 _72714 _72716) = (term1774 _120607 _72714 _72715 _72716 _72717).
Proof. exact (TRANS (@lem5763938 _120607 _72714 _72715 _72716 _72717) (@lem5763955 _120607 _72714 _72715 _72716 _72717)). Qed.
Lemma lem5763958 {_120592 _120607 : Type'} (x' : _120592) (t : _120592 -> Prop) (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : term1775 _120592 _120607 x' t op s f.
Proof. exact (conj (@lem5763836 _120592 _120607 x' t f op y z x h1 h2) (@lem5763845 _120592 _120607 op s f)). Qed.
Lemma lem5763960 {_120607 : Type'} (_72714 : _120607 -> _120607) (_72715 : _120607) (_72716 : _120607 -> _120607) (_72717 : _120607) : term1774 _120607 _72714 _72715 _72716 _72717.
Proof. exact (EQ_MP (@lem5763956 _120607 _72714 _72715 _72716 _72717) (@lem5763935 _120607 _72715 _72717 _72714 _72716)). Qed.
Lemma lem5763961 {_120607 : Type'} (_72714 : _120607 -> _120607) (_72715 : _120607) (_72716 : _120607 -> _120607) (_72717 : _120607) : term1774 _120607 _72714 _72715 _72716 _72717.
Proof. exact (@lem5763960 _120607 _72714 _72715 _72716 _72717). Qed.
Lemma lem5763962 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term1776 _120592 _120607 s x' op t f.
Proof. exact (@lem5763961 _120607 (term1460 _120592 _120607 op s f) (term1755 _120592 _120607 op t f x') (term1460 _120592 _120607 op s f) (term1470 _120592 _120607 x' op t f)). Qed.
Lemma lem5763965 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1752 _120592 _120607 s op t f x') = (term1473 _120592 _120607 s x' op t f).
Proof. exact (@lem5763962 _120592 _120607 s x' op t f (@lem5763958 _120592 _120607 x' t s f op y z x h1 h2)). Qed.
Lemma lem5763966 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1752 _120592 _120607 s op t f x') = (term1473 _120592 _120607 s x' op t f).
Proof. exact (@lem5763965 _120592 _120607 s x' t f op y z x h1 h2). Qed.
Lemma lem5763967 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : term1777 _120592 _120607 s x' op t f.
Proof. exact (fun h0 : term1778 _120592 _120607 s x' op t f => @lem5763966 _120592 _120607 s x' t f op y z x h1 h2). Qed.
Lemma lem5763969 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5763970 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1777 _120592 _120607 s x' op t f) = ((term1752 _120592 _120607 s op t f x') = (term1473 _120592 _120607 s x' op t f)).
Proof. exact (@lem5763969 ((term1752 _120592 _120607 s op t f x') = (term1473 _120592 _120607 s x' op t f))). Qed.
Lemma lem5763971 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1752 _120592 _120607 s op t f x') = (term1473 _120592 _120607 s x' op t f).
Proof. exact (EQ_MP (@lem5763970 _120592 _120607 s x' op t f) (@lem5763967 _120592 _120607 s x' t f op y z x h1 h2)). Qed.
Lemma lem5763989 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5763990 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1712 _120607 x y z) = (term1713 _120607 y x z).
Proof. exact (@lem5763989 (y = z) (term649 _120607 x z)). Qed.
Lemma lem5764000 {_120607 : Type'} (x : _120607) (y : _120607) : (term1714 _120607 x y) = (term1714 _120607 x y).
Proof. exact (eq_refl (term1714 _120607 x y)). Qed.
Lemma lem5764001 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1691 _120607 x y z) = (term1715 _120607 y x z).
Proof. exact (MK_COMB (@lem5764000 _120607 x y) (@lem5763990 _120607 y x z)). Qed.
Lemma lem5764005 (q : Prop) (p : Prop) (r : Prop) : (term1716 p q r) = (term1716 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5764006 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1715 _120607 y x z) = (term1717 _120607 y x z).
Proof. exact (@lem5764005 (y = z) (term649 _120607 x y) (term649 _120607 x z)). Qed.
Lemma lem5764028 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1691 _120607 x y z) = (term1717 _120607 y x z).
Proof. exact (TRANS (@lem5764001 _120607 y x z) (@lem5764006 _120607 y x z)). Qed.
Lemma lem5764029 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5764030 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1718 _120607 x y z) = (term1719 _120607 y x z).
Proof. exact (MK_COMB (@lem5764029) (@lem5764028 _120607 y x z)). Qed.
Lemma lem5764052 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1717 _120607 y x z) = (term1717 _120607 y x z).
Proof. exact (eq_refl (term1717 _120607 y x z)). Qed.
Lemma lem5764053 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : ((term1691 _120607 x y z) = (term1717 _120607 y x z)) = ((term1717 _120607 y x z) = (term1717 _120607 y x z)).
Proof. exact (MK_COMB (@lem5764030 _120607 y x z) (@lem5764052 _120607 y x z)). Qed.
Lemma lem5764055 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5764056 (x : Prop) : (x = x) = True.
Proof. exact (@lem5764055 Prop x). Qed.
Lemma lem5764057 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : ((term1717 _120607 y x z) = (term1717 _120607 y x z)) = True.
Proof. exact (@lem5764056 (term1717 _120607 y x z)). Qed.
Lemma lem5764058 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : ((term1691 _120607 x y z) = (term1717 _120607 y x z)) = True.
Proof. exact (TRANS (@lem5764053 _120607 y x z) (@lem5764057 _120607 y x z)). Qed.
Lemma lem5764059 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : True = ((term1691 _120607 x y z) = (term1717 _120607 y x z)).
Proof. exact (SYM (@lem5764058 _120607 y x z)). Qed.
Lemma lem5764060 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1691 _120607 x y z) = (term1717 _120607 y x z).
Proof. exact (EQ_MP (@lem5764059 _120607 y x z) (@lem0)). Qed.
Lemma lem5764061 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : term1717 _120607 y x z.
Proof. exact (EQ_MP (@lem5764060 _120607 y x z) (@lem5763653 _120607 x y z)). Qed.
Lemma lem5764063 (b : Prop) (a : Prop) : (a \/ b) = (term1696 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5764064 {_120607 : Type'} (x : _120607) (y : _120607) (z : _120607) : (term1717 _120607 y x z) = (term1720 _120607 x y z).
Proof. exact (@lem5764063 (term1721 _120607 y x z) (y = z)). Qed.
Lemma lem5764066 (a : Prop) (b : Prop) : (term1722 a b) = (term1723 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5764067 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1724 _120607 y x z) = (term1725 _120607 y x z).
Proof. exact (@lem5764066 (term649 _120607 x y) (term649 _120607 x z)). Qed.
Lemma lem5764069 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5764070 {_120607 : Type'} (x : _120607) (y : _120607) : (term1726 _120607 x y) = (x = y).
Proof. exact (@lem5764069 (x = y)). Qed.
Lemma lem5764071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5764072 {_120607 : Type'} (x : _120607) (y : _120607) : (term1727 _120607 x y) = (term1728 _120607 x y).
Proof. exact (MK_COMB (@lem5764071) (@lem5764070 _120607 x y)). Qed.
Lemma lem5764074 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5764075 {_120607 : Type'} (x : _120607) (z : _120607) : (term1726 _120607 x z) = (x = z).
Proof. exact (@lem5764074 (x = z)). Qed.
Lemma lem5764076 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1725 _120607 y x z) = (term1729 _120607 y x z).
Proof. exact (MK_COMB (@lem5764072 _120607 x y) (@lem5764075 _120607 x z)). Qed.
Lemma lem5764077 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1724 _120607 y x z) = (term1729 _120607 y x z).
Proof. exact (TRANS (@lem5764067 _120607 y x z) (@lem5764076 _120607 y x z)). Qed.
Lemma lem5764078 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5764079 {_120607 : Type'} (y : _120607) (x : _120607) (z : _120607) : (term1730 _120607 y x z) = (term1731 _120607 y x z).
Proof. exact (MK_COMB (@lem5764078) (@lem5764077 _120607 y x z)). Qed.
Lemma lem5764080 {_120607 : Type'} (y : _120607) (z : _120607) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5764081 {_120607 : Type'} (x : _120607) (y : _120607) (z : _120607) : (term1720 _120607 x y z) = (term1732 _120607 x y z).
Proof. exact (MK_COMB (@lem5764079 _120607 y x z) (@lem5764080 _120607 y z)). Qed.
Lemma lem5764082 {_120607 : Type'} (x : _120607) (y : _120607) (z : _120607) : (term1717 _120607 y x z) = (term1732 _120607 x y z).
Proof. exact (TRANS (@lem5764064 _120607 x y z) (@lem5764081 _120607 x y z)). Qed.
Lemma lem5764084 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : term1779 _120592 _120607 s x' op t f.
Proof. exact (conj (@lem5763815 _120592 _120607 s t f x' op y z x h1 h2) (@lem5763971 _120592 _120607 s x' t f op y z x h1 h2)). Qed.
Lemma lem5764086 {_120607 : Type'} (x : _120607) (y : _120607) (z : _120607) : term1732 _120607 x y z.
Proof. exact (EQ_MP (@lem5764082 _120607 x y z) (@lem5764061 _120607 y x z)). Qed.
Lemma lem5764087 {_120607 : Type'} (x : _120607) (y : _120607) (z : _120607) : term1732 _120607 x y z.
Proof. exact (@lem5764086 _120607 x y z). Qed.
Lemma lem5764088 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term1780 _120592 _120607 s x' op t f.
Proof. exact (@lem5764087 _120607 (term1752 _120592 _120607 s op t f x') (term1744 _120592 _120607 s op t f x') (term1473 _120592 _120607 s x' op t f)). Qed.
Lemma lem5764091 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1744 _120592 _120607 s op t f x') = (term1473 _120592 _120607 s x' op t f).
Proof. exact (@lem5764088 _120592 _120607 s x' op t f (@lem5764084 _120592 _120607 s x' t f op y z x h1 h2)). Qed.
Lemma lem5764092 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1744 _120592 _120607 s op t f x') = (term1473 _120592 _120607 s x' op t f).
Proof. exact (@lem5764091 _120592 _120607 s x' t f op y z x h1 h2). Qed.
Lemma lem5764093 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : term1781 _120592 _120607 s x' op t f.
Proof. exact (fun h0 : term1782 _120592 _120607 s x' op t f => @lem5764092 _120592 _120607 s x' t f op y z x h1 h2). Qed.
Lemma lem5764095 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5764096 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1781 _120592 _120607 s x' op t f) = ((term1744 _120592 _120607 s op t f x') = (term1473 _120592 _120607 s x' op t f)).
Proof. exact (@lem5764095 ((term1744 _120592 _120607 s op t f x') = (term1473 _120592 _120607 s x' op t f))). Qed.
Lemma lem5764097 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1744 _120592 _120607 s op t f x') = (term1473 _120592 _120607 s x' op t f).
Proof. exact (EQ_MP (@lem5764096 _120592 _120607 s x' op t f) (@lem5764093 _120592 _120607 s x' t f op y z x h1 h2)). Qed.
Lemma lem5764098 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : term1783 _120592 _120607 s x' op t f.
Proof. exact (conj (@lem5763749 _120592 _120607 x' s t f op y z x h1 h2) (@lem5764097 _120592 _120607 s x' t f op y z x h1 h2)). Qed.
Lemma lem5764100 {_120607 : Type'} (x : _120607) (y : _120607) (z : _120607) : term1732 _120607 x y z.
Proof. exact (EQ_MP (@lem5764082 _120607 x y z) (@lem5764061 _120607 y x z)). Qed.
Lemma lem5764101 {_120607 : Type'} (x : _120607) (y : _120607) (z : _120607) : term1732 _120607 x y z.
Proof. exact (@lem5764100 _120607 x y z). Qed.
Lemma lem5764102 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term1784 _120592 _120607 s x' op t f.
Proof. exact (@lem5764101 _120607 (term1744 _120592 _120607 s op t f x') (term1467 _120592 _120607 x' s op t f) (term1473 _120592 _120607 s x' op t f)). Qed.
Lemma lem5764105 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1467 _120592 _120607 x' s op t f) = (term1473 _120592 _120607 s x' op t f).
Proof. exact (@lem5764102 _120592 _120607 s x' op t f (@lem5764098 _120592 _120607 s x' t f op y z x h1 h2)). Qed.
Lemma lem5764106 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1467 _120592 _120607 x' s op t f) = (term1473 _120592 _120607 s x' op t f).
Proof. exact (@lem5764105 _120592 _120607 s x' t f op y z x h1 h2). Qed.
Lemma lem5764107 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : term1785 _120592 _120607 s x' op t f.
Proof. exact (fun h0 : term1476 _120592 _120607 s x' op t f => @lem5764106 _120592 _120607 s x' t f op y z x h1 h2). Qed.
Lemma lem5764109 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5764110 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1785 _120592 _120607 s x' op t f) = ((term1467 _120592 _120607 x' s op t f) = (term1473 _120592 _120607 s x' op t f)).
Proof. exact (@lem5764109 ((term1467 _120592 _120607 x' s op t f) = (term1473 _120592 _120607 s x' op t f))). Qed.
Lemma lem5764111 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) : (term1467 _120592 _120607 x' s op t f) = (term1473 _120592 _120607 s x' op t f).
Proof. exact (EQ_MP (@lem5764110 _120592 _120607 s x' op t f) (@lem5764107 _120592 _120607 s x' t f op y z x h1 h2)). Qed.
Lemma lem5764114 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5764116 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term1476 _120592 _120607 s x' op t f) = (term1786 _120592 _120607 s x' op t f).
Proof. exact (@lem5764114 ((term1467 _120592 _120607 x' s op t f) = (term1473 _120592 _120607 s x' op t f))). Qed.
Lemma lem5764119 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1504 _120592 _120607 s x' op t f) : term1786 _120592 _120607 s x' op t f.
Proof. exact (EQ_MP (@lem5764116 _120592 _120607 s x' op t f) (@lem5762755 _120592 _120607 s x' op t f h1)). Qed.
Lemma lem5764122 {_120592 _120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) (h3 : term1504 _120592 _120607 s x' op t f) : False.
Proof. exact (@lem5764119 _120592 _120607 s x' op t f h3 (@lem5764111 _120592 _120607 s x' t f op y z x h1 h2)). Qed.
Lemma lem5764123 {_120592 _120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) (h3 : term1504 _120592 _120607 s x' op t f) : term668.
Proof. exact (fun h0 : ~ False => @lem5764122 _120592 _120607 y z x s x' op t f h1 h2 h3). Qed.
Lemma lem5764125 (p : Prop) : (term666 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5764126 : term668 = False.
Proof. exact (@lem5764125 False). Qed.
Lemma lem5764127 {_120592 _120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) (h3 : term1504 _120592 _120607 s x' op t f) : False.
Proof. exact (EQ_MP (@lem5764126) (@lem5764123 _120592 _120607 y z x s x' op t f h1 h2 h3)). Qed.
Lemma lem5764128 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1497 _120592 s t) (h2 : term1504 _120592 _120607 s x' op t f) : (term1497 _120592 s t) = False.
Proof. exact (prop_ext (fun h3 : term1497 _120592 s t => @lem5763448 _120592 _120607 s x' op t f h1 h2) (fun h3 : False => @lem5762717 _120592 s t h1)). Qed.
Lemma lem5764129 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1497 _120592 s t) (h2 : term1504 _120592 _120607 s x' op t f) : False.
Proof. exact (EQ_MP (@lem5764128 _120592 _120607 s x' op t f h1 h2) (@lem5762717 _120592 s t h1)). Qed.
Lemma lem5764130 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1497 _120592 s t) (h2 : term1504 _120592 _120607 s x' op t f) : (term1497 _120592 s t) = False.
Proof. exact (prop_ext (fun h3 : term1497 _120592 s t => @lem5764129 _120592 _120607 s x' op t f h1 h2) (fun h3 : False => @lem5762250 _120592 s t h1)). Qed.
Lemma lem5764131 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1497 _120592 s t) (h2 : term1504 _120592 _120607 s x' op t f) : False.
Proof. exact (EQ_MP (@lem5764130 _120592 _120607 s x' op t f h1 h2) (@lem5762250 _120592 s t h1)). Qed.
Lemma lem5764132 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1497 _120592 s t) (h2 : term1504 _120592 _120607 s x' op t f) : (term1497 _120592 s t) = False.
Proof. exact (prop_ext (fun h3 : term1497 _120592 s t => @lem5764131 _120592 _120607 s x' op t f h1 h2) (fun h3 : False => @lem5762250 _120592 s t h1)). Qed.
Lemma lem5764133 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : term1497 _120592 s t) (h2 : term1504 _120592 _120607 s x' op t f) : False.
Proof. exact (EQ_MP (@lem5764132 _120592 _120607 s x' op t f h1 h2) (@lem5762250 _120592 s t h1)). Qed.
Lemma lem5764134 {_120592 _120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) (h3 : term1504 _120592 _120607 s x' op t f) : False.
Proof. exact (or_elim (@lem5761582 _120592 _120607 s x' op t f h3) (fun h0 : term1497 _120592 s t => @lem5764133 _120592 _120607 s x' op t f h0 h3) (fun h0 : (term1493 _120592 _120607 op s t f) = (term1462 _120592 _120607 s op t f) => @lem5764127 _120592 _120607 y z x s x' op t f h1 h2 h3)). Qed.
Lemma lem5764135 {_120592 _120607 : Type'} (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (s : _120592 -> Prop) (x' : _120592) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) (h1 : @monoidal _120607 op) (h2 : term1355 _120607 y z x) (h3 : term991 _120592 _120607 s x' op t f) : False.
Proof. exact (or_elim (@lem5761568 _120592 _120607 s x' op t f h3) (fun h0 : term1514 _120592 _120607 s f op => @lem5763224 _120592 _120607 y z x s f op h1 h2 h0) (fun h0 : term1504 _120592 _120607 s x' op t f => @lem5764134 _120592 _120607 y z x s x' op t f h1 h2 h0)). Qed.
Lemma lem5764136 {_120592 _120607 : Type'} (s : _120592 -> Prop) (x' : _120592) (f : _120592 -> _120607) (op : type1400 _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : term994 _120592 _120607 s x' op f) (h2 : @monoidal _120607 op) (h3 : term1355 _120607 y z x) : False.
Proof. exact (ex_elim (@lem5760626 _120592 _120607 s x' op f h1) (fun t : _120592 -> Prop => fun h0 : term993 _120592 _120607 s x' op f t => @lem5764135 _120592 _120607 y z x s x' op t f h2 h3 h0)). Qed.
Lemma lem5764137 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (y : type402 _120607) (z : type402 _120607) (x : type402 _120607) (h1 : @monoidal _120607 op) (h2 : term891 _120592 _120607 s op f) (h3 : term1355 _120607 y z x) : False.
Proof. exact (ex_elim (@lem5759926 _120592 _120607 s op f h2) (fun x' : _120592 => fun h0 : term995 _120592 _120607 s op f x' => @lem5764136 _120592 _120607 s x' f op y z x h0 h1 h3)). Qed.
Lemma lem5764138 {_120592 _120607 : Type'} (y : type402 _120607) (x : type402 _120607) (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term1358 _120607 y x) (h2 : @monoidal _120607 op) (h3 : term891 _120592 _120607 s op f) : False.
Proof. exact (ex_elim (@lem5760624 _120607 y x h1) (fun z : type402 _120607 => fun h0 : term1357 _120607 y x z => @lem5764137 _120592 _120607 s op f y z x h2 h3 h0)). Qed.
Lemma lem5764139 {_120592 _120607 : Type'} (x : type402 _120607) (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term1360 _120607 x) (h2 : @monoidal _120607 op) (h3 : term891 _120592 _120607 s op f) : False.
Proof. exact (ex_elim (@lem5760623 _120607 x h1) (fun y : type402 _120607 => fun h0 : term1359 _120607 x y => @lem5764138 _120592 _120607 y x s op f h0 h2 h3)). Qed.
Lemma lem5764140 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term892 _120607) (h2 : @monoidal _120607 op) (h3 : term891 _120592 _120607 s op f) : False.
Proof. exact (ex_elim (@lem5760622 _120607 h1) (fun x : type402 _120607 => fun h0 : term1361 _120607 x => @lem5764139 _120592 _120607 x s op f h0 h2 h3)). Qed.
Lemma lem5764141 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term892 _120607) (h2 : @monoidal _120607 op) (h3 : term891 _120592 _120607 s op f) : (@monoidal _120607 op) = False.
Proof. exact (prop_ext (fun h4 : @monoidal _120607 op => @lem5764140 _120592 _120607 s op f h1 h2 h3) (fun h4 : False => @lem5759757 _120607 op h2)). Qed.
Lemma lem5764142 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : term892 _120607) (h2 : @monoidal _120607 op) (h3 : term891 _120592 _120607 s op f) : False.
Proof. exact (EQ_MP (@lem5764141 _120592 _120607 s op f h1 h2 h3) (@lem5759757 _120607 op h2)). Qed.
Lemma lem5764143 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : @monoidal _120607 op) (h2 : term891 _120592 _120607 s op f) : term897 _120607.
Proof. exact (fun h0 : term892 _120607 => @lem5764142 _120592 _120607 s op f h0 h1 h2). Qed.
Lemma lem5764144 {_120607 : Type'} : (term897 _120607) = (term898 _120607).
Proof. exact (@lem69 (term892 _120607)). Qed.
Lemma lem5764145 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : @monoidal _120607 op) (h2 : term891 _120592 _120607 s op f) : term898 _120607.
Proof. exact (EQ_MP (@lem5764144 _120607) (@lem5764143 _120592 _120607 s op f h1 h2)). Qed.
Lemma lem5764146 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term901 _120592 _120607 s op f.
Proof. exact (fun h0 : term891 _120592 _120607 s op f => @lem5764145 _120592 _120607 s op f h1 h0). Qed.
Lemma lem5764147 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term903 _120592 _120607 s op f.
Proof. exact (fun h0 : @FINITE _120592 s => @lem5764146 _120592 _120607 s f op h1). Qed.
Lemma lem5764148 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : term905 _120592 _120607 s op f.
Proof. exact (fun h0 : @monoidal _120607 op => @lem5764147 _120592 _120607 s f op h0). Qed.
Lemma lem5764153 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) : term909 _120592 _120607 op f.
Proof. exact (fun s : _120592 -> Prop => @lem5764148 _120592 _120607 s op f). Qed.
Lemma lem5764158 {_120592 _120607 : Type'} (f : _120592 -> _120607) : term913 _120592 _120607 f.
Proof. exact (fun op : type1400 _120607 => @lem5764153 _120592 _120607 op f). Qed.
Lemma lem5764163 {_120592 _120607 : Type'} : term917 _120592 _120607.
Proof. exact (fun f : _120592 -> _120607 => @lem5764158 _120592 _120607 f). Qed.
Lemma lem5764164 {_120592 _120607 : Type'} : term916 _120592 _120607.
Proof. exact (EQ_MP (@lem5759747 _120592 _120607) (@lem5764163 _120592 _120607)). Qed.
Lemma lem5764165 {_120592 _120607 : Type'} (f : _120592 -> _120607) : term1787 _120592 _120607 f.
Proof. exact (@lem5764164 _120592 _120607 f). Qed.
Lemma lem5764166 {_120592 _120607 : Type'} (f : _120592 -> _120607) : (term1787 _120592 _120607 f) = (term912 _120592 _120607 f).
Proof. exact (eq_refl (term1787 _120592 _120607 f)). Qed.
Lemma lem5764167 {_120592 _120607 : Type'} (f : _120592 -> _120607) : term912 _120592 _120607 f.
Proof. exact (EQ_MP (@lem5764166 _120592 _120607 f) (@lem5764165 _120592 _120607 f)). Qed.
Lemma lem5764168 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) : term1788 _120592 _120607 f op.
Proof. exact (@lem5764167 _120592 _120607 f op). Qed.
Lemma lem5764169 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) : (term1788 _120592 _120607 f op) = (term908 _120592 _120607 op f).
Proof. exact (eq_refl (term1788 _120592 _120607 f op)). Qed.
Lemma lem5764170 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) : term908 _120592 _120607 op f.
Proof. exact (EQ_MP (@lem5764169 _120592 _120607 op f) (@lem5764168 _120592 _120607 f op)). Qed.
Lemma lem5764171 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) (s : _120592 -> Prop) : term1789 _120592 _120607 op f s.
Proof. exact (@lem5764170 _120592 _120607 op f s). Qed.
Lemma lem5764172 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term1789 _120592 _120607 op f s) = (term893 _120592 _120607 s op f).
Proof. exact (eq_refl (term1789 _120592 _120607 op f s)). Qed.
Lemma lem5764173 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : term893 _120592 _120607 s op f.
Proof. exact (EQ_MP (@lem5764172 _120592 _120607 s op f) (@lem5764171 _120592 _120607 op f s)). Qed.
Lemma lem5764175 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : term893 _120592 _120607 s op f.
Proof. exact (@lem5759430 _120592 _120607 s op f (@lem5764173 _120592 _120607 s op f)). Qed.
Lemma lem5764176 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term902 _120592 _120607 s op f.
Proof. exact (@lem5764175 _120592 _120607 s op f (@lem5757707 _120607 op h1)). Qed.
Lemma lem5764177 {_120592 _120607 : Type'} (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) : term900 _120592 _120607 s op f.
Proof. exact (@lem5764176 _120592 _120607 s f op h2 (@lem5757808 _120592 s h1)). Qed.
Lemma lem5764178 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) (h3 : term891 _120592 _120607 s op f) : term897 _120607.
Proof. exact (@lem5764177 _120592 _120607 f s op h1 h2 (@lem5759411 _120592 _120607 s op f h3)). Qed.
Lemma lem5764179 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) (h3 : term891 _120592 _120607 s op f) : False.
Proof. exact (@lem5764178 _120592 _120607 s op f h1 h2 h3 (@lem5759412 _120607)). Qed.
Lemma lem5764180 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) (h3 : term891 _120592 _120607 s op f) : (term891 _120592 _120607 s op f) = False.
Proof. exact (prop_ext (fun h4 : term891 _120592 _120607 s op f => @lem5764179 _120592 _120607 s op f h1 h2 h3) (fun h4 : False => @lem5759411 _120592 _120607 s op f h3)). Qed.
Lemma lem5764181 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) (h3 : term891 _120592 _120607 s op f) : False.
Proof. exact (EQ_MP (@lem5764180 _120592 _120607 s op f h1 h2 h3) (@lem5759411 _120592 _120607 s op f h3)). Qed.
Lemma lem5764182 {_120592 _120607 : Type'} (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) : term890 _120592 _120607 s op f.
Proof. exact (fun h0 : term891 _120592 _120607 s op f => @lem5764181 _120592 _120607 s op f h1 h2 h0). Qed.
Lemma lem5764183 {_120592 _120607 : Type'} (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) : term889 _120592 _120607 s op f.
Proof. exact (EQ_MP (@lem5759410 _120592 _120607 s op f) (@lem5764182 _120592 _120607 f s op h1 h2)). Qed.
Lemma lem5764184 {_120592 _120607 : Type'} (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) : term751 _120592 _120607 s op f.
Proof. exact (EQ_MP (@lem5759406 _120592 _120607 f s op h1 h2) (@lem5764183 _120592 _120607 f s op h1 h2)). Qed.
Lemma lem5764185 {_120592 _120607 : Type'} (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @FINITE _120592 s) (h2 : @monoidal _120607 op) : term721 _120592 _120607 s op f.
Proof. exact (@lem5757841 _120592 _120607 s op f (@lem5764184 _120592 _120607 f s op h1 h2)). Qed.
Lemma lem5764186 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term722 _120592 _120607 s op f.
Proof. exact (fun h0 : @FINITE _120592 s => @lem5764185 _120592 _120607 f s op h0 h1). Qed.
Lemma lem5764187 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term707 _120592 _120607 s op f.
Proof. exact (EQ_MP (@lem5757807 _120592 _120607 s op f) (@lem5764186 _120592 _120607 s f op h1)). Qed.
Lemma lem5764192 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term1790 _120592 _120607 op f.
Proof. exact (fun s : _120592 -> Prop => @lem5764187 _120592 _120607 s f op h1). Qed.
Lemma lem5764197 {_120592 _120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : term1791 _120592 _120607 op.
Proof. exact (fun f : _120592 -> _120607 => @lem5764192 _120592 _120607 f op h1). Qed.
Lemma lem5764198 {_120592 _120607 : Type'} (op : type1400 _120607) : term1792 _120592 _120607 op.
Proof. exact (fun h0 : @monoidal _120607 op => @lem5764197 _120592 _120607 op h0). Qed.
Lemma lem5764203 {_120592 _120607 : Type'} : term1793 _120592 _120607.
Proof. exact (fun op : type1400 _120607 => @lem5764198 _120592 _120607 op). Qed.
