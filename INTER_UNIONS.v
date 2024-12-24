Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_UNIONS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXTENSION_spec.
Require Import IN_INTER_spec.
Require Import IN_UNIONS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
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
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
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
Require Import thm21386_spec.
Require Import thm3184747_spec.
Require Import thm3184750_spec.
Require Import thm69_spec.
Lemma lem3329634 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3329635 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3329636 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3329635 t1) (@lem3329634 t1)). Qed.
Lemma lem3329637 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3329636 t1 t2). Qed.
Lemma lem3329638 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3329639 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3329638 t1 t2) (@lem3329637 t1 t2)). Qed.
Lemma lem3329640 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3329639 t1 t2 t3). Qed.
Lemma lem3329641 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3329642 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3329641 t1 t2 t3) (@lem3329640 t1 t2 t3)). Qed.
Lemma lem3329643 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3329642 t1 t2 t3)). Qed.
Lemma lem3329644 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem3329645 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem3329646 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem3329645 A s) (@lem3329644 A s)). Qed.
Lemma lem3329647 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem3329646 A s t). Qed.
Lemma lem3329648 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = (term10 A s t).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem3329649 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term10 A s t.
Proof. exact (EQ_MP (@lem3329648 A s t) (@lem3329647 A s t)). Qed.
Lemma lem3329650 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term11 A s t x.
Proof. exact (@lem3329649 A s t x). Qed.
Lemma lem3329651 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A s t x) = ((term12 A x s t) = (term13 A s x t)).
Proof. exact (eq_refl (term11 A s t x)). Qed.
Lemma lem3329684 {_83064 : Type'} : term14 _83064.
Proof. exact (EQ_MP (@lem3184750 _83064) (@lem3184747 _83064)). Qed.
Lemma lem3329685 {_83064 : Type'} (P : type919 _83064) : term15 _83064 P.
Proof. exact (@lem3329684 _83064 P). Qed.
Lemma lem3329686 {_83064 : Type'} (P : type919 _83064) : (term15 _83064 P) = (term16 _83064 P).
Proof. exact (eq_refl (term15 _83064 P)). Qed.
Lemma lem3329687 {_83064 : Type'} (P : type919 _83064) : term16 _83064 P.
Proof. exact (EQ_MP (@lem3329686 _83064 P) (@lem3329685 _83064 P)). Qed.
Lemma lem3329688 {_83064 : Type'} (P : type919 _83064) (x : _83064) : term17 _83064 P x.
Proof. exact (@lem3329687 _83064 P x). Qed.
Lemma lem3329689 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term17 _83064 P x) = ((term18 _83064 x P) = (term19 _83064 P x)).
Proof. exact (eq_refl (term17 _83064 P x)). Qed.
Lemma lem3329691 {A : Type'} (s : type686 A) : term20 A s.
Proof. exact (@lem3205091 A s). Qed.
Lemma lem3329692 {A : Type'} (s : type686 A) : (term20 A s) = (term21 A s).
Proof. exact (eq_refl (term20 A s)). Qed.
Lemma lem3329693 {A : Type'} (s : type686 A) : term21 A s.
Proof. exact (EQ_MP (@lem3329692 A s) (@lem3329691 A s)). Qed.
Lemma lem3329694 {A : Type'} (s : type686 A) (x : A) : term22 A s x.
Proof. exact (@lem3329693 A s x). Qed.
Lemma lem3329695 {A : Type'} (s : type686 A) (x : A) : (term22 A s x) = ((term23 A x s) = (term24 A s x)).
Proof. exact (eq_refl (term22 A s x)). Qed.
Lemma lem3329697 {A : Type'} (s : A -> Prop) : term25 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3329698 {A : Type'} (s : A -> Prop) : (term25 A s) = (term26 A s).
Proof. exact (eq_refl (term25 A s)). Qed.
Lemma lem3329699 {A : Type'} (s : A -> Prop) : term26 A s.
Proof. exact (EQ_MP (@lem3329698 A s) (@lem3329697 A s)). Qed.
Lemma lem3329700 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term27 A s t.
Proof. exact (@lem3329699 A s t). Qed.
Lemma lem3329701 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term27 A s t) = ((s = t) = (term28 A s t)).
Proof. exact (eq_refl (term27 A s t)). Qed.
Lemma lem3329716 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term28 A s t).
Proof. exact (EQ_MP (@lem3329701 A s t) (@lem3329700 A s t)). Qed.
Lemma lem3329717 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (s = t) = (term28 _86990 s t).
Proof. exact (@lem3329716 _86990 s t). Qed.
Lemma lem3329718 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : ((term29 _86990 s t) = (term30 _86990 s t)) = (term31 _86990 s t).
Proof. exact (@lem3329717 _86990 (term29 _86990 s t) (term30 _86990 s t)). Qed.
Lemma lem3329719 {_86990 : Type'} (s : type686 _86990) : (term32 _86990 s) = (term33 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3329718 _86990 s t)). Qed.
Lemma lem3329720 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3329721 {_86990 : Type'} (s : type686 _86990) : (term34 _86990 s) = (term35 _86990 s).
Proof. exact (MK_COMB (@lem3329720 _86990) (@lem3329719 _86990 s)). Qed.
Lemma lem3329722 {_86990 : Type'} : (term36 _86990) = (term37 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3329721 _86990 s)). Qed.
Lemma lem3329723 {_86990 : Type'} : (@all ((_86990 -> Prop) -> Prop)) = (@all ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3329724 {_86990 : Type'} : (term38 _86990) = (term39 _86990).
Proof. exact (MK_COMB (@lem3329723 _86990) (@lem3329722 _86990)). Qed.
Lemma lem3329725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3329726 {_86990 : Type'} : (term40 _86990) = (term41 _86990).
Proof. exact (MK_COMB (@lem3329725) (@lem3329724 _86990)). Qed.
Lemma lem3329738 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term28 A s t).
Proof. exact (EQ_MP (@lem3329701 A s t) (@lem3329700 A s t)). Qed.
Lemma lem3329739 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (s = t) = (term28 _87026 s t).
Proof. exact (@lem3329738 _87026 s t). Qed.
Lemma lem3329740 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : ((term42 _87026 t s) = (term43 _87026 s t)) = (term44 _87026 s t).
Proof. exact (@lem3329739 _87026 (term42 _87026 t s) (term43 _87026 s t)). Qed.
Lemma lem3329741 {_87026 : Type'} (s : type686 _87026) : (term45 _87026 s) = (term46 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3329740 _87026 s t)). Qed.
Lemma lem3329742 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3329743 {_87026 : Type'} (s : type686 _87026) : (term47 _87026 s) = (term48 _87026 s).
Proof. exact (MK_COMB (@lem3329742 _87026) (@lem3329741 _87026 s)). Qed.
Lemma lem3329744 {_87026 : Type'} : (term49 _87026) = (term50 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3329743 _87026 s)). Qed.
Lemma lem3329745 {_87026 : Type'} : (@all ((_87026 -> Prop) -> Prop)) = (@all ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3329746 {_87026 : Type'} : (term51 _87026) = (term52 _87026).
Proof. exact (MK_COMB (@lem3329745 _87026) (@lem3329744 _87026)). Qed.
Lemma lem3329747 {_86990 _87026 : Type'} : (term53 _86990 _87026) = (term54 _86990 _87026).
Proof. exact (MK_COMB (@lem3329726 _86990) (@lem3329746 _87026)). Qed.
Lemma lem3329748 {_86990 _87026 : Type'} : (term54 _86990 _87026) = (term53 _86990 _87026).
Proof. exact (SYM (@lem3329747 _86990 _87026)). Qed.
Lemma lem3329766 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A x s t) = (term13 A s x t).
Proof. exact (EQ_MP (@lem3329651 A s x t) (@lem3329650 A s t x)). Qed.
Lemma lem3329767 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term12 _86990 x s t) = (term13 _86990 s x t).
Proof. exact (@lem3329766 _86990 s x t). Qed.
Lemma lem3329768 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term55 _86990 x s t) = (term56 _86990 s x t).
Proof. exact (@lem3329767 _86990 (@UNIONS _86990 s) x t). Qed.
Lemma lem3329772 {A : Type'} (s : type686 A) (x : A) : (term23 A x s) = (term24 A s x).
Proof. exact (EQ_MP (@lem3329695 A s x) (@lem3329694 A s x)). Qed.
Lemma lem3329773 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term23 _86990 x s) = (term24 _86990 s x).
Proof. exact (@lem3329772 _86990 s x). Qed.
Lemma lem3329780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3329781 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term57 _86990 x s) = (term58 _86990 s x).
Proof. exact (MK_COMB (@lem3329780) (@lem3329773 _86990 s x)). Qed.
Lemma lem3329782 {_86990 : Type'} (x : _86990) (t : _86990 -> Prop) : (@IN _86990 x t) = (@IN _86990 x t).
Proof. exact (eq_refl (@IN _86990 x t)). Qed.
Lemma lem3329783 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term56 _86990 s x t) = (term59 _86990 s x t).
Proof. exact (MK_COMB (@lem3329781 _86990 s x) (@lem3329782 _86990 x t)). Qed.
Lemma lem3329786 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term55 _86990 x s t) = (term59 _86990 s x t).
Proof. exact (TRANS (@lem3329768 _86990 s x t) (@lem3329783 _86990 s x t)). Qed.
Lemma lem3329787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3329788 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term60 _86990 x s t) = (term61 _86990 s x t).
Proof. exact (MK_COMB (@lem3329787) (@lem3329786 _86990 s x t)). Qed.
Lemma lem3329790 {A : Type'} (s : type686 A) (x : A) : (term23 A x s) = (term24 A s x).
Proof. exact (EQ_MP (@lem3329695 A s x) (@lem3329694 A s x)). Qed.
Lemma lem3329791 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term23 _86990 x s) = (term24 _86990 s x).
Proof. exact (@lem3329790 _86990 s x). Qed.
Lemma lem3329792 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term62 _86990 x s t) = (term63 _86990 s t x).
Proof. exact (@lem3329791 _86990 (term64 _86990 s t) x). Qed.
Lemma lem3329802 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term18 _83064 x P) = (term19 _83064 P x).
Proof. exact (EQ_MP (@lem3329689 _83064 P x) (@lem3329688 _83064 P x)). Qed.
Lemma lem3329803 {_86990 : Type'} (P : type909 _86990) (x : _86990 -> Prop) : (term65 _86990 x P) = (term66 _86990 P x).
Proof. exact (@lem3329802 (_86990 -> Prop) P x). Qed.
Lemma lem3329804 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (t' : _86990 -> Prop) : (term67 _86990 t' s t) = (term68 _86990 s t t').
Proof. exact (@lem3329803 _86990 (term69 _86990 s t) t'). Qed.
Lemma lem3329805 {_86990 : Type'} (GEN_PVAR_21 : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) : (term70 _86990 s t GEN_PVAR_21) = (term71 _86990 GEN_PVAR_21 s t).
Proof. exact (eq_refl (term70 _86990 s t GEN_PVAR_21)). Qed.
Lemma lem3329806 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term72 _86990 s t) = (term73 _86990 s t).
Proof. exact (fun_ext (fun GEN_PVAR_21 : _86990 -> Prop => @lem3329805 _86990 GEN_PVAR_21 s t)). Qed.
Lemma lem3329807 {_86990 : Type'} : (@GSPEC (_86990 -> Prop)) = (@GSPEC (_86990 -> Prop)).
Proof. exact (eq_refl (@GSPEC (_86990 -> Prop))). Qed.
Lemma lem3329808 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term74 _86990 s t) = (term64 _86990 s t).
Proof. exact (MK_COMB (@lem3329807 _86990) (@lem3329806 _86990 s t)). Qed.
Lemma lem3329809 {_86990 : Type'} (t' : _86990 -> Prop) : (@IN (_86990 -> Prop) t') = (@IN (_86990 -> Prop) t').
Proof. exact (eq_refl (@IN (_86990 -> Prop) t')). Qed.
Lemma lem3329810 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) : (term67 _86990 t' s t) = (term75 _86990 t' s t).
Proof. exact (MK_COMB (@lem3329809 _86990 t') (@lem3329808 _86990 s t)). Qed.
Lemma lem3329811 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3329812 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) : (term76 _86990 t' s t) = (term77 _86990 t' s t).
Proof. exact (MK_COMB (@lem3329811) (@lem3329810 _86990 t' s t)). Qed.
Lemma lem3329813 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) : (term68 _86990 s t t') = (term78 _86990 t' s t).
Proof. exact (eq_refl (term68 _86990 s t t')). Qed.
Lemma lem3329814 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) : ((term67 _86990 t' s t) = (term68 _86990 s t t')) = ((term75 _86990 t' s t) = (term78 _86990 t' s t)).
Proof. exact (MK_COMB (@lem3329812 _86990 t' s t) (@lem3329813 _86990 t' s t)). Qed.
Lemma lem3329815 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) : (term75 _86990 t' s t) = (term78 _86990 t' s t).
Proof. exact (EQ_MP (@lem3329814 _86990 t' s t) (@lem3329804 _86990 s t t')). Qed.
Lemma lem3329821 {A B : Type'} (f : A -> B) (y : A) : (term79 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3329822 {_86990 : Type'} (f : type1527 _86990) (y : Prop) : (term80 _86990 f y) = (f y).
Proof. exact (@lem3329821 Prop (type686 _86990) f y). Qed.
Lemma lem3329823 {_86990 : Type'} (t' : _86990 -> Prop) (x : _86990 -> Prop) (s : type686 _86990) : (term81 _86990 t' x s) = (term82 _86990 t' x s).
Proof. exact (@lem3329822 _86990 (term83 _86990 t') (@IN (_86990 -> Prop) x s)). Qed.
Lemma lem3329824 {_86990 : Type'} (p : Prop) (t' : _86990 -> Prop) : (term84 _86990 t' p) = (term85 _86990 p t').
Proof. exact (eq_refl (term84 _86990 t' p)). Qed.
Lemma lem3329825 {_86990 : Type'} (t' : _86990 -> Prop) : (term86 _86990 t') = (term83 _86990 t').
Proof. exact (fun_ext (fun p : Prop => @lem3329824 _86990 p t')). Qed.
Lemma lem3329826 {_86990 : Type'} (x : _86990 -> Prop) (s : type686 _86990) : (@IN (_86990 -> Prop) x s) = (@IN (_86990 -> Prop) x s).
Proof. exact (eq_refl (@IN (_86990 -> Prop) x s)). Qed.
Lemma lem3329827 {_86990 : Type'} (t' : _86990 -> Prop) (x : _86990 -> Prop) (s : type686 _86990) : (term81 _86990 t' x s) = (term82 _86990 t' x s).
Proof. exact (MK_COMB (@lem3329825 _86990 t') (@lem3329826 _86990 x s)). Qed.
Lemma lem3329828 {_86990 : Type'} : (@eq ((_86990 -> Prop) -> Prop)) = (@eq ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3329829 {_86990 : Type'} (t' : _86990 -> Prop) (x : _86990 -> Prop) (s : type686 _86990) : (term87 _86990 t' x s) = (term88 _86990 t' x s).
Proof. exact (MK_COMB (@lem3329828 _86990) (@lem3329827 _86990 t' x s)). Qed.
Lemma lem3329830 {_86990 : Type'} (x : _86990 -> Prop) (s : type686 _86990) (t' : _86990 -> Prop) : (term82 _86990 t' x s) = (term89 _86990 x s t').
Proof. exact (eq_refl (term82 _86990 t' x s)). Qed.
Lemma lem3329831 {_86990 : Type'} (x : _86990 -> Prop) (s : type686 _86990) (t' : _86990 -> Prop) : ((term81 _86990 t' x s) = (term82 _86990 t' x s)) = ((term82 _86990 t' x s) = (term89 _86990 x s t')).
Proof. exact (MK_COMB (@lem3329829 _86990 t' x s) (@lem3329830 _86990 x s t')). Qed.
Lemma lem3329832 {_86990 : Type'} (x : _86990 -> Prop) (s : type686 _86990) (t' : _86990 -> Prop) : (term82 _86990 t' x s) = (term89 _86990 x s t').
Proof. exact (EQ_MP (@lem3329831 _86990 x s t') (@lem3329823 _86990 t' x s)). Qed.
Lemma lem3329837 {_86990 : Type'} (x : _86990 -> Prop) (t : _86990 -> Prop) : (@INTER _86990 x t) = (@INTER _86990 x t).
Proof. exact (eq_refl (@INTER _86990 x t)). Qed.
Lemma lem3329838 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term90 _86990 t' s x t) = (term91 _86990 s t' x t).
Proof. exact (MK_COMB (@lem3329832 _86990 x s t') (@lem3329837 _86990 x t)). Qed.
Lemma lem3329840 {A B : Type'} (f : A -> B) (y : A) : (term79 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3329841 {_86990 : Type'} (f : type686 _86990) (y : _86990 -> Prop) : (term92 _86990 f y) = (f y).
Proof. exact (@lem3329840 (_86990 -> Prop) Prop f y). Qed.
Lemma lem3329842 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term93 _86990 s t' x t) = (term91 _86990 s t' x t).
Proof. exact (@lem3329841 _86990 (term89 _86990 x s t') (@INTER _86990 x t)). Qed.
Lemma lem3329843 {_86990 : Type'} (x : _86990 -> Prop) (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term94 _86990 x s t' t) = (term95 _86990 x s t' t).
Proof. exact (eq_refl (term94 _86990 x s t' t)). Qed.
Lemma lem3329844 {_86990 : Type'} (x : _86990 -> Prop) (s : type686 _86990) (t' : _86990 -> Prop) : (term96 _86990 x s t') = (term89 _86990 x s t').
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3329843 _86990 x s t' t)). Qed.
Lemma lem3329845 {_86990 : Type'} (x : _86990 -> Prop) (t : _86990 -> Prop) : (@INTER _86990 x t) = (@INTER _86990 x t).
Proof. exact (eq_refl (@INTER _86990 x t)). Qed.
Lemma lem3329846 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term93 _86990 s t' x t) = (term91 _86990 s t' x t).
Proof. exact (MK_COMB (@lem3329844 _86990 x s t') (@lem3329845 _86990 x t)). Qed.
Lemma lem3329847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3329848 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term97 _86990 s t' x t) = (term98 _86990 s t' x t).
Proof. exact (MK_COMB (@lem3329847) (@lem3329846 _86990 s t' x t)). Qed.
Lemma lem3329849 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term91 _86990 s t' x t) = (term99 _86990 s t' x t).
Proof. exact (eq_refl (term91 _86990 s t' x t)). Qed.
Lemma lem3329850 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : ((term93 _86990 s t' x t) = (term91 _86990 s t' x t)) = ((term91 _86990 s t' x t) = (term99 _86990 s t' x t)).
Proof. exact (MK_COMB (@lem3329848 _86990 s t' x t) (@lem3329849 _86990 s t' x t)). Qed.
Lemma lem3329851 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term91 _86990 s t' x t) = (term99 _86990 s t' x t).
Proof. exact (EQ_MP (@lem3329850 _86990 s t' x t) (@lem3329842 _86990 s t' x t)). Qed.
Lemma lem3329856 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term90 _86990 t' s x t) = (term99 _86990 s t' x t).
Proof. exact (TRANS (@lem3329838 _86990 s t' x t) (@lem3329851 _86990 s t' x t)). Qed.
Lemma lem3329857 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term100 _86990 t' s t) = (term101 _86990 s t' t).
Proof. exact (fun_ext (fun x : _86990 -> Prop => @lem3329856 _86990 s t' x t)). Qed.
Lemma lem3329858 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3329859 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term78 _86990 t' s t) = (term102 _86990 s t' t).
Proof. exact (MK_COMB (@lem3329858 _86990) (@lem3329857 _86990 s t' t)). Qed.
Lemma lem3329864 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term75 _86990 t' s t) = (term102 _86990 s t' t).
Proof. exact (TRANS (@lem3329815 _86990 t' s t) (@lem3329859 _86990 s t' t)). Qed.
Lemma lem3329865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3329866 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term103 _86990 t' s t) = (term104 _86990 s t' t).
Proof. exact (MK_COMB (@lem3329865) (@lem3329864 _86990 s t' t)). Qed.
Lemma lem3329867 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (@IN _86990 x t') = (@IN _86990 x t').
Proof. exact (eq_refl (@IN _86990 x t')). Qed.
Lemma lem3329868 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term105 _86990 s t x t') = (term106 _86990 s t x t').
Proof. exact (MK_COMB (@lem3329866 _86990 s t' t) (@lem3329867 _86990 x t')). Qed.
Lemma lem3329871 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term107 _86990 s t x) = (term108 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3329868 _86990 s t x t')). Qed.
Lemma lem3329872 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3329873 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term63 _86990 s t x) = (term109 _86990 s t x).
Proof. exact (MK_COMB (@lem3329872 _86990) (@lem3329871 _86990 s t x)). Qed.
Lemma lem3329878 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term62 _86990 x s t) = (term109 _86990 s t x).
Proof. exact (TRANS (@lem3329792 _86990 s t x) (@lem3329873 _86990 s t x)). Qed.
Lemma lem3329879 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : ((term55 _86990 x s t) = (term62 _86990 x s t)) = ((term59 _86990 s x t) = (term109 _86990 s t x)).
Proof. exact (MK_COMB (@lem3329788 _86990 s x t) (@lem3329878 _86990 s t x)). Qed.
Lemma lem3329882 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term110 _86990 s t) = (term111 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3329879 _86990 s t x)). Qed.
Lemma lem3329883 {_86990 : Type'} : (@all _86990) = (@all _86990).
Proof. exact (eq_refl (@all _86990)). Qed.
Lemma lem3329884 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term31 _86990 s t) = (term112 _86990 s t).
Proof. exact (MK_COMB (@lem3329883 _86990) (@lem3329882 _86990 s t)). Qed.
Lemma lem3329889 {_86990 : Type'} (s : type686 _86990) : (term33 _86990 s) = (term113 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3329884 _86990 s t)). Qed.
Lemma lem3329890 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3329891 {_86990 : Type'} (s : type686 _86990) : (term35 _86990 s) = (term114 _86990 s).
Proof. exact (MK_COMB (@lem3329890 _86990) (@lem3329889 _86990 s)). Qed.
Lemma lem3329896 {_86990 : Type'} : (term37 _86990) = (term115 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3329891 _86990 s)). Qed.
Lemma lem3329897 {_86990 : Type'} : (@all ((_86990 -> Prop) -> Prop)) = (@all ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3329898 {_86990 : Type'} : (term39 _86990) = (term116 _86990).
Proof. exact (MK_COMB (@lem3329897 _86990) (@lem3329896 _86990)). Qed.
Lemma lem3329903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3329904 {_86990 : Type'} : (term41 _86990) = (term117 _86990).
Proof. exact (MK_COMB (@lem3329903) (@lem3329898 _86990)). Qed.
Lemma lem3329920 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A x s t) = (term13 A s x t).
Proof. exact (EQ_MP (@lem3329651 A s x t) (@lem3329650 A s t x)). Qed.
Lemma lem3329921 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term12 _87026 x s t) = (term13 _87026 s x t).
Proof. exact (@lem3329920 _87026 s x t). Qed.
Lemma lem3329922 {_87026 : Type'} (t : _87026 -> Prop) (x : _87026) (s : type686 _87026) : (term118 _87026 x t s) = (term119 _87026 t x s).
Proof. exact (@lem3329921 _87026 t x (@UNIONS _87026 s)). Qed.
Lemma lem3329926 {A : Type'} (s : type686 A) (x : A) : (term23 A x s) = (term24 A s x).
Proof. exact (EQ_MP (@lem3329695 A s x) (@lem3329694 A s x)). Qed.
Lemma lem3329927 {_87026 : Type'} (s : type686 _87026) (x : _87026) : (term23 _87026 x s) = (term24 _87026 s x).
Proof. exact (@lem3329926 _87026 s x). Qed.
Lemma lem3329934 {_87026 : Type'} (x : _87026) (t : _87026 -> Prop) : (term120 _87026 x t) = (term120 _87026 x t).
Proof. exact (eq_refl (term120 _87026 x t)). Qed.
Lemma lem3329935 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term119 _87026 t x s) = (term121 _87026 t s x).
Proof. exact (MK_COMB (@lem3329934 _87026 x t) (@lem3329927 _87026 s x)). Qed.
Lemma lem3329938 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term118 _87026 x t s) = (term121 _87026 t s x).
Proof. exact (TRANS (@lem3329922 _87026 t x s) (@lem3329935 _87026 t s x)). Qed.
Lemma lem3329939 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3329940 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term122 _87026 x t s) = (term123 _87026 t s x).
Proof. exact (MK_COMB (@lem3329939) (@lem3329938 _87026 t s x)). Qed.
Lemma lem3329942 {A : Type'} (s : type686 A) (x : A) : (term23 A x s) = (term24 A s x).
Proof. exact (EQ_MP (@lem3329695 A s x) (@lem3329694 A s x)). Qed.
Lemma lem3329943 {_87026 : Type'} (s : type686 _87026) (x : _87026) : (term23 _87026 x s) = (term24 _87026 s x).
Proof. exact (@lem3329942 _87026 s x). Qed.
Lemma lem3329944 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term124 _87026 x s t) = (term125 _87026 s t x).
Proof. exact (@lem3329943 _87026 (term126 _87026 s t) x). Qed.
Lemma lem3329954 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term18 _83064 x P) = (term19 _83064 P x).
Proof. exact (EQ_MP (@lem3329689 _83064 P x) (@lem3329688 _83064 P x)). Qed.
Lemma lem3329955 {_87026 : Type'} (P : type909 _87026) (x : _87026 -> Prop) : (term65 _87026 x P) = (term66 _87026 P x).
Proof. exact (@lem3329954 (_87026 -> Prop) P x). Qed.
Lemma lem3329956 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (t' : _87026 -> Prop) : (term127 _87026 t' s t) = (term128 _87026 s t t').
Proof. exact (@lem3329955 _87026 (term129 _87026 s t) t'). Qed.
Lemma lem3329957 {_87026 : Type'} (GEN_PVAR_22 : _87026 -> Prop) (s : type686 _87026) (t : _87026 -> Prop) : (term130 _87026 s t GEN_PVAR_22) = (term131 _87026 GEN_PVAR_22 s t).
Proof. exact (eq_refl (term130 _87026 s t GEN_PVAR_22)). Qed.
Lemma lem3329958 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term132 _87026 s t) = (term133 _87026 s t).
Proof. exact (fun_ext (fun GEN_PVAR_22 : _87026 -> Prop => @lem3329957 _87026 GEN_PVAR_22 s t)). Qed.
Lemma lem3329959 {_87026 : Type'} : (@GSPEC (_87026 -> Prop)) = (@GSPEC (_87026 -> Prop)).
Proof. exact (eq_refl (@GSPEC (_87026 -> Prop))). Qed.
Lemma lem3329960 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term134 _87026 s t) = (term126 _87026 s t).
Proof. exact (MK_COMB (@lem3329959 _87026) (@lem3329958 _87026 s t)). Qed.
Lemma lem3329961 {_87026 : Type'} (t' : _87026 -> Prop) : (@IN (_87026 -> Prop) t') = (@IN (_87026 -> Prop) t').
Proof. exact (eq_refl (@IN (_87026 -> Prop) t')). Qed.
Lemma lem3329962 {_87026 : Type'} (t' : _87026 -> Prop) (s : type686 _87026) (t : _87026 -> Prop) : (term127 _87026 t' s t) = (term135 _87026 t' s t).
Proof. exact (MK_COMB (@lem3329961 _87026 t') (@lem3329960 _87026 s t)). Qed.
Lemma lem3329963 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3329964 {_87026 : Type'} (t' : _87026 -> Prop) (s : type686 _87026) (t : _87026 -> Prop) : (term136 _87026 t' s t) = (term137 _87026 t' s t).
Proof. exact (MK_COMB (@lem3329963) (@lem3329962 _87026 t' s t)). Qed.
Lemma lem3329965 {_87026 : Type'} (t' : _87026 -> Prop) (s : type686 _87026) (t : _87026 -> Prop) : (term128 _87026 s t t') = (term138 _87026 t' s t).
Proof. exact (eq_refl (term128 _87026 s t t')). Qed.
Lemma lem3329966 {_87026 : Type'} (t' : _87026 -> Prop) (s : type686 _87026) (t : _87026 -> Prop) : ((term127 _87026 t' s t) = (term128 _87026 s t t')) = ((term135 _87026 t' s t) = (term138 _87026 t' s t)).
Proof. exact (MK_COMB (@lem3329964 _87026 t' s t) (@lem3329965 _87026 t' s t)). Qed.
Lemma lem3329967 {_87026 : Type'} (t' : _87026 -> Prop) (s : type686 _87026) (t : _87026 -> Prop) : (term135 _87026 t' s t) = (term138 _87026 t' s t).
Proof. exact (EQ_MP (@lem3329966 _87026 t' s t) (@lem3329956 _87026 s t t')). Qed.
Lemma lem3329973 {A B : Type'} (f : A -> B) (y : A) : (term79 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3329974 {_87026 : Type'} (f : type1527 _87026) (y : Prop) : (term80 _87026 f y) = (f y).
Proof. exact (@lem3329973 Prop (type686 _87026) f y). Qed.
Lemma lem3329975 {_87026 : Type'} (t' : _87026 -> Prop) (x : _87026 -> Prop) (s : type686 _87026) : (term81 _87026 t' x s) = (term82 _87026 t' x s).
Proof. exact (@lem3329974 _87026 (term83 _87026 t') (@IN (_87026 -> Prop) x s)). Qed.
Lemma lem3329976 {_87026 : Type'} (p : Prop) (t' : _87026 -> Prop) : (term84 _87026 t' p) = (term85 _87026 p t').
Proof. exact (eq_refl (term84 _87026 t' p)). Qed.
Lemma lem3329977 {_87026 : Type'} (t' : _87026 -> Prop) : (term86 _87026 t') = (term83 _87026 t').
Proof. exact (fun_ext (fun p : Prop => @lem3329976 _87026 p t')). Qed.
Lemma lem3329978 {_87026 : Type'} (x : _87026 -> Prop) (s : type686 _87026) : (@IN (_87026 -> Prop) x s) = (@IN (_87026 -> Prop) x s).
Proof. exact (eq_refl (@IN (_87026 -> Prop) x s)). Qed.
Lemma lem3329979 {_87026 : Type'} (t' : _87026 -> Prop) (x : _87026 -> Prop) (s : type686 _87026) : (term81 _87026 t' x s) = (term82 _87026 t' x s).
Proof. exact (MK_COMB (@lem3329977 _87026 t') (@lem3329978 _87026 x s)). Qed.
Lemma lem3329980 {_87026 : Type'} : (@eq ((_87026 -> Prop) -> Prop)) = (@eq ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3329981 {_87026 : Type'} (t' : _87026 -> Prop) (x : _87026 -> Prop) (s : type686 _87026) : (term87 _87026 t' x s) = (term88 _87026 t' x s).
Proof. exact (MK_COMB (@lem3329980 _87026) (@lem3329979 _87026 t' x s)). Qed.
Lemma lem3329982 {_87026 : Type'} (x : _87026 -> Prop) (s : type686 _87026) (t' : _87026 -> Prop) : (term82 _87026 t' x s) = (term89 _87026 x s t').
Proof. exact (eq_refl (term82 _87026 t' x s)). Qed.
Lemma lem3329983 {_87026 : Type'} (x : _87026 -> Prop) (s : type686 _87026) (t' : _87026 -> Prop) : ((term81 _87026 t' x s) = (term82 _87026 t' x s)) = ((term82 _87026 t' x s) = (term89 _87026 x s t')).
Proof. exact (MK_COMB (@lem3329981 _87026 t' x s) (@lem3329982 _87026 x s t')). Qed.
Lemma lem3329984 {_87026 : Type'} (x : _87026 -> Prop) (s : type686 _87026) (t' : _87026 -> Prop) : (term82 _87026 t' x s) = (term89 _87026 x s t').
Proof. exact (EQ_MP (@lem3329983 _87026 x s t') (@lem3329975 _87026 t' x s)). Qed.
Lemma lem3329989 {_87026 : Type'} (t : _87026 -> Prop) (x : _87026 -> Prop) : (@INTER _87026 t x) = (@INTER _87026 t x).
Proof. exact (eq_refl (@INTER _87026 t x)). Qed.
Lemma lem3329990 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term139 _87026 t' s t x) = (term140 _87026 s t' t x).
Proof. exact (MK_COMB (@lem3329984 _87026 x s t') (@lem3329989 _87026 t x)). Qed.
Lemma lem3329992 {A B : Type'} (f : A -> B) (y : A) : (term79 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3329993 {_87026 : Type'} (f : type686 _87026) (y : _87026 -> Prop) : (term92 _87026 f y) = (f y).
Proof. exact (@lem3329992 (_87026 -> Prop) Prop f y). Qed.
Lemma lem3329994 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term141 _87026 s t' t x) = (term140 _87026 s t' t x).
Proof. exact (@lem3329993 _87026 (term89 _87026 x s t') (@INTER _87026 t x)). Qed.
Lemma lem3329995 {_87026 : Type'} (x : _87026 -> Prop) (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term94 _87026 x s t' t) = (term95 _87026 x s t' t).
Proof. exact (eq_refl (term94 _87026 x s t' t)). Qed.
Lemma lem3329996 {_87026 : Type'} (x : _87026 -> Prop) (s : type686 _87026) (t' : _87026 -> Prop) : (term96 _87026 x s t') = (term89 _87026 x s t').
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3329995 _87026 x s t' t)). Qed.
Lemma lem3329997 {_87026 : Type'} (t : _87026 -> Prop) (x : _87026 -> Prop) : (@INTER _87026 t x) = (@INTER _87026 t x).
Proof. exact (eq_refl (@INTER _87026 t x)). Qed.
Lemma lem3329998 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term141 _87026 s t' t x) = (term140 _87026 s t' t x).
Proof. exact (MK_COMB (@lem3329996 _87026 x s t') (@lem3329997 _87026 t x)). Qed.
Lemma lem3329999 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3330000 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term142 _87026 s t' t x) = (term143 _87026 s t' t x).
Proof. exact (MK_COMB (@lem3329999) (@lem3329998 _87026 s t' t x)). Qed.
Lemma lem3330001 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term140 _87026 s t' t x) = (term144 _87026 s t' t x).
Proof. exact (eq_refl (term140 _87026 s t' t x)). Qed.
Lemma lem3330002 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : ((term141 _87026 s t' t x) = (term140 _87026 s t' t x)) = ((term140 _87026 s t' t x) = (term144 _87026 s t' t x)).
Proof. exact (MK_COMB (@lem3330000 _87026 s t' t x) (@lem3330001 _87026 s t' t x)). Qed.
Lemma lem3330003 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term140 _87026 s t' t x) = (term144 _87026 s t' t x).
Proof. exact (EQ_MP (@lem3330002 _87026 s t' t x) (@lem3329994 _87026 s t' t x)). Qed.
Lemma lem3330008 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term139 _87026 t' s t x) = (term144 _87026 s t' t x).
Proof. exact (TRANS (@lem3329990 _87026 s t' t x) (@lem3330003 _87026 s t' t x)). Qed.
Lemma lem3330009 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term145 _87026 t' s t) = (term146 _87026 s t' t).
Proof. exact (fun_ext (fun x : _87026 -> Prop => @lem3330008 _87026 s t' t x)). Qed.
Lemma lem3330010 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3330011 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term138 _87026 t' s t) = (term147 _87026 s t' t).
Proof. exact (MK_COMB (@lem3330010 _87026) (@lem3330009 _87026 s t' t)). Qed.
Lemma lem3330016 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term135 _87026 t' s t) = (term147 _87026 s t' t).
Proof. exact (TRANS (@lem3329967 _87026 t' s t) (@lem3330011 _87026 s t' t)). Qed.
Lemma lem3330017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3330018 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term148 _87026 t' s t) = (term149 _87026 s t' t).
Proof. exact (MK_COMB (@lem3330017) (@lem3330016 _87026 s t' t)). Qed.
Lemma lem3330019 {_87026 : Type'} (x : _87026) (t' : _87026 -> Prop) : (@IN _87026 x t') = (@IN _87026 x t').
Proof. exact (eq_refl (@IN _87026 x t')). Qed.
Lemma lem3330020 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term150 _87026 s t x t') = (term151 _87026 s t x t').
Proof. exact (MK_COMB (@lem3330018 _87026 s t' t) (@lem3330019 _87026 x t')). Qed.
Lemma lem3330023 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term152 _87026 s t x) = (term153 _87026 s t x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3330020 _87026 s t x t')). Qed.
Lemma lem3330024 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3330025 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term125 _87026 s t x) = (term154 _87026 s t x).
Proof. exact (MK_COMB (@lem3330024 _87026) (@lem3330023 _87026 s t x)). Qed.
Lemma lem3330030 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term124 _87026 x s t) = (term154 _87026 s t x).
Proof. exact (TRANS (@lem3329944 _87026 s t x) (@lem3330025 _87026 s t x)). Qed.
Lemma lem3330031 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : ((term118 _87026 x t s) = (term124 _87026 x s t)) = ((term121 _87026 t s x) = (term154 _87026 s t x)).
Proof. exact (MK_COMB (@lem3329940 _87026 t s x) (@lem3330030 _87026 s t x)). Qed.
Lemma lem3330034 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term155 _87026 s t) = (term156 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3330031 _87026 s t x)). Qed.
Lemma lem3330035 {_87026 : Type'} : (@all _87026) = (@all _87026).
Proof. exact (eq_refl (@all _87026)). Qed.
Lemma lem3330036 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term44 _87026 s t) = (term157 _87026 s t).
Proof. exact (MK_COMB (@lem3330035 _87026) (@lem3330034 _87026 s t)). Qed.
Lemma lem3330041 {_87026 : Type'} (s : type686 _87026) : (term46 _87026 s) = (term158 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3330036 _87026 s t)). Qed.
Lemma lem3330042 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3330043 {_87026 : Type'} (s : type686 _87026) : (term48 _87026 s) = (term159 _87026 s).
Proof. exact (MK_COMB (@lem3330042 _87026) (@lem3330041 _87026 s)). Qed.
Lemma lem3330048 {_87026 : Type'} : (term50 _87026) = (term160 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3330043 _87026 s)). Qed.
Lemma lem3330049 {_87026 : Type'} : (@all ((_87026 -> Prop) -> Prop)) = (@all ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3330050 {_87026 : Type'} : (term52 _87026) = (term161 _87026).
Proof. exact (MK_COMB (@lem3330049 _87026) (@lem3330048 _87026)). Qed.
Lemma lem3330055 {_86990 _87026 : Type'} : (term54 _86990 _87026) = (term162 _86990 _87026).
Proof. exact (MK_COMB (@lem3329904 _86990) (@lem3330050 _87026)). Qed.
Lemma lem3330058 {_86990 _87026 : Type'} : (term162 _86990 _87026) = (term54 _86990 _87026).
Proof. exact (SYM (@lem3330055 _86990 _87026)). Qed.
Lemma lem3330060 (p : Prop) : p = (term163 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3330061 {_86990 _87026 : Type'} : (term162 _86990 _87026) = (term164 _86990 _87026).
Proof. exact (@lem3330060 (term162 _86990 _87026)). Qed.
Lemma lem3330062 {_86990 _87026 : Type'} : (term164 _86990 _87026) = (term162 _86990 _87026).
Proof. exact (SYM (@lem3330061 _86990 _87026)). Qed.
Lemma lem3330063 {_86990 _87026 : Type'} (h1 : term165 _86990 _87026) : term165 _86990 _87026.
Proof. exact (h1). Qed.
Lemma lem3330064 {_86990 : Type'} : term166 _86990.
Proof. exact (@lem3205222 (_86990 -> Prop)). Qed.
Lemma lem3330065 {_86990 : Type'} : term167 _86990.
Proof. exact (@lem3205222 _86990). Qed.
Lemma lem3330066 {_87026 : Type'} : term167 _87026.
Proof. exact (@lem3205222 _87026). Qed.
Lemma lem3330067 {_87026 : Type'} : term166 _87026.
Proof. exact (@lem3205222 (_87026 -> Prop)). Qed.
Lemma lem3330072 {_86990 _87026 : Type'} (h1 : term168 _86990 _87026) : term168 _86990 _87026.
Proof. exact (h1). Qed.
Lemma lem3330073 {_86990 _87026 : Type'} : term169 _86990 _87026.
Proof. exact (fun h0 : term168 _86990 _87026 => @lem3330072 _86990 _87026 h0). Qed.
Lemma lem3330074 {_86990 _87026 : Type'} (h1 : term169 _86990 _87026) : term169 _86990 _87026.
Proof. exact (h1). Qed.
Lemma lem3330075 {_86990 _87026 : Type'} (h1 : term168 _86990 _87026) : term168 _86990 _87026.
Proof. exact (h1). Qed.
Lemma lem3330076 {_86990 _87026 : Type'} (h1 : term168 _86990 _87026) (h2 : term169 _86990 _87026) : term168 _86990 _87026.
Proof. exact (@lem3330074 _86990 _87026 h2 (@lem3330075 _86990 _87026 h1)). Qed.
Lemma lem3330077 {_86990 _87026 : Type'} (h1 : term168 _86990 _87026) : term170 _86990 _87026.
Proof. exact (fun h0 : term169 _86990 _87026 => @lem3330076 _86990 _87026 h1 h0). Qed.
Lemma lem3330078 {_86990 _87026 : Type'} (h1 : term169 _86990 _87026) : term169 _86990 _87026.
Proof. exact (h1). Qed.
Lemma lem3330079 {_86990 _87026 : Type'} (h1 : term168 _86990 _87026) (h2 : term169 _86990 _87026) : term168 _86990 _87026.
Proof. exact (@lem3330077 _86990 _87026 h1 (@lem3330078 _86990 _87026 h2)). Qed.
Lemma lem3330080 {_86990 _87026 : Type'} (h1 : term169 _86990 _87026) : term169 _86990 _87026.
Proof. exact (fun h0 : term168 _86990 _87026 => @lem3330079 _86990 _87026 h0 h1). Qed.
Lemma lem3330081 {_86990 _87026 : Type'} : term171 _86990 _87026.
Proof. exact (fun h0 : term169 _86990 _87026 => @lem3330080 _86990 _87026 h0). Qed.
Lemma lem3330084 {_86990 _87026 : Type'} : term169 _86990 _87026.
Proof. exact (@lem3330081 _86990 _87026 (@lem3330073 _86990 _87026)). Qed.
Lemma lem3330085 {_86990 _87026 : Type'} : term169 _86990 _87026.
Proof. exact (@lem3330084 _86990 _87026). Qed.
Lemma lem3330467 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3330468 {_87026 : Type'} : (term172 _87026) = (term173 _87026).
Proof. exact (@lem3330467 (term166 _87026)). Qed.
Lemma lem3330483 {_86990 : Type'} : (term174 _86990) = (term174 _86990).
Proof. exact (eq_refl (term174 _86990)). Qed.
Lemma lem3330484 {_86990 _87026 : Type'} : (term175 _86990 _87026) = (term176 _86990 _87026).
Proof. exact (MK_COMB (@lem3330483 _86990) (@lem3330468 _87026)). Qed.
Lemma lem3330487 {_87026 : Type'} : (term177 _87026) = (term177 _87026).
Proof. exact (eq_refl (term177 _87026)). Qed.
Lemma lem3330488 {_86990 _87026 : Type'} : (term178 _86990 _87026) = (term179 _86990 _87026).
Proof. exact (MK_COMB (@lem3330487 _87026) (@lem3330484 _86990 _87026)). Qed.
Lemma lem3330491 {_86990 : Type'} : (term177 _86990) = (term177 _86990).
Proof. exact (eq_refl (term177 _86990)). Qed.
Lemma lem3330492 {_86990 _87026 : Type'} : (term180 _86990 _87026) = (term181 _86990 _87026).
Proof. exact (MK_COMB (@lem3330491 _86990) (@lem3330488 _86990 _87026)). Qed.
Lemma lem3330495 {_86990 _87026 : Type'} : (term182 _86990 _87026) = (term182 _86990 _87026).
Proof. exact (eq_refl (term182 _86990 _87026)). Qed.
Lemma lem3330502 {_86990 _87026 : Type'} : (term168 _86990 _87026) = (term183 _86990 _87026).
Proof. exact (MK_COMB (@lem3330495 _86990 _87026) (@lem3330492 _86990 _87026)). Qed.
Lemma lem3330511 {_87026 : Type'} (s : type686 _87026) (x : _87026 -> Prop) (t : type686 _87026) : ((term184 _87026 x s t) = (term185 _87026 s x t)) = ((term184 _87026 x s t) = (term185 _87026 s x t)).
Proof. exact (eq_refl ((term184 _87026 x s t) = (term185 _87026 s x t))). Qed.
Lemma lem3330512 {_87026 : Type'} (s : type686 _87026) (t : type686 _87026) : (term186 _87026 s t) = (term186 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 -> Prop => @lem3330511 _87026 s x t)). Qed.
Lemma lem3330513 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3330514 {_87026 : Type'} (s : type686 _87026) (t : type686 _87026) : (term187 _87026 s t) = (term187 _87026 s t).
Proof. exact (MK_COMB (@lem3330513 _87026) (@lem3330512 _87026 s t)). Qed.
Lemma lem3330515 {_87026 : Type'} (s : type686 _87026) : (term188 _87026 s) = (term188 _87026 s).
Proof. exact (fun_ext (fun t : type686 _87026 => @lem3330514 _87026 s t)). Qed.
Lemma lem3330516 {_87026 : Type'} : (@all ((_87026 -> Prop) -> Prop)) = (@all ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3330517 {_87026 : Type'} (s : type686 _87026) : (term189 _87026 s) = (term189 _87026 s).
Proof. exact (MK_COMB (@lem3330516 _87026) (@lem3330515 _87026 s)). Qed.
Lemma lem3330518 {_87026 : Type'} : (term190 _87026) = (term190 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3330517 _87026 s)). Qed.
Lemma lem3330519 {_87026 : Type'} : (@all ((_87026 -> Prop) -> Prop)) = (@all ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3330520 {_87026 : Type'} : (term166 _87026) = (term166 _87026).
Proof. exact (MK_COMB (@lem3330519 _87026) (@lem3330518 _87026)). Qed.
Lemma lem3330521 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3330522 {_87026 : Type'} : (term173 _87026) = (term173 _87026).
Proof. exact (MK_COMB (@lem3330521) (@lem3330520 _87026)). Qed.
Lemma lem3330531 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : type686 _86990) : ((term184 _86990 x s t) = (term185 _86990 s x t)) = ((term184 _86990 x s t) = (term185 _86990 s x t)).
Proof. exact (eq_refl ((term184 _86990 x s t) = (term185 _86990 s x t))). Qed.
Lemma lem3330532 {_86990 : Type'} (s : type686 _86990) (t : type686 _86990) : (term186 _86990 s t) = (term186 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 -> Prop => @lem3330531 _86990 s x t)). Qed.
Lemma lem3330533 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3330534 {_86990 : Type'} (s : type686 _86990) (t : type686 _86990) : (term187 _86990 s t) = (term187 _86990 s t).
Proof. exact (MK_COMB (@lem3330533 _86990) (@lem3330532 _86990 s t)). Qed.
Lemma lem3330535 {_86990 : Type'} (s : type686 _86990) : (term188 _86990 s) = (term188 _86990 s).
Proof. exact (fun_ext (fun t : type686 _86990 => @lem3330534 _86990 s t)). Qed.
Lemma lem3330536 {_86990 : Type'} : (@all ((_86990 -> Prop) -> Prop)) = (@all ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3330537 {_86990 : Type'} (s : type686 _86990) : (term189 _86990 s) = (term189 _86990 s).
Proof. exact (MK_COMB (@lem3330536 _86990) (@lem3330535 _86990 s)). Qed.
Lemma lem3330538 {_86990 : Type'} : (term190 _86990) = (term190 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3330537 _86990 s)). Qed.
Lemma lem3330539 {_86990 : Type'} : (@all ((_86990 -> Prop) -> Prop)) = (@all ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3330540 {_86990 : Type'} : (term166 _86990) = (term166 _86990).
Proof. exact (MK_COMB (@lem3330539 _86990) (@lem3330538 _86990)). Qed.
Lemma lem3330541 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3330542 {_86990 : Type'} : (term174 _86990) = (term174 _86990).
Proof. exact (MK_COMB (@lem3330541) (@lem3330540 _86990)). Qed.
Lemma lem3330543 {_86990 _87026 : Type'} : (term176 _86990 _87026) = (term176 _86990 _87026).
Proof. exact (MK_COMB (@lem3330542 _86990) (@lem3330522 _87026)). Qed.
Lemma lem3330552 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : ((term12 _87026 x s t) = (term13 _87026 s x t)) = ((term12 _87026 x s t) = (term13 _87026 s x t)).
Proof. exact (eq_refl ((term12 _87026 x s t) = (term13 _87026 s x t))). Qed.
Lemma lem3330553 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term191 _87026 s t) = (term191 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3330552 _87026 s x t)). Qed.
Lemma lem3330554 {_87026 : Type'} : (@all _87026) = (@all _87026).
Proof. exact (eq_refl (@all _87026)). Qed.
Lemma lem3330555 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term10 _87026 s t) = (term10 _87026 s t).
Proof. exact (MK_COMB (@lem3330554 _87026) (@lem3330553 _87026 s t)). Qed.
Lemma lem3330556 {_87026 : Type'} (s : _87026 -> Prop) : (term192 _87026 s) = (term192 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3330555 _87026 s t)). Qed.
Lemma lem3330557 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3330558 {_87026 : Type'} (s : _87026 -> Prop) : (term8 _87026 s) = (term8 _87026 s).
Proof. exact (MK_COMB (@lem3330557 _87026) (@lem3330556 _87026 s)). Qed.
Lemma lem3330559 {_87026 : Type'} : (term193 _87026) = (term193 _87026).
Proof. exact (fun_ext (fun s : _87026 -> Prop => @lem3330558 _87026 s)). Qed.
Lemma lem3330560 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3330561 {_87026 : Type'} : (term167 _87026) = (term167 _87026).
Proof. exact (MK_COMB (@lem3330560 _87026) (@lem3330559 _87026)). Qed.
Lemma lem3330562 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3330563 {_87026 : Type'} : (term177 _87026) = (term177 _87026).
Proof. exact (MK_COMB (@lem3330562) (@lem3330561 _87026)). Qed.
Lemma lem3330564 {_86990 _87026 : Type'} : (term179 _86990 _87026) = (term179 _86990 _87026).
Proof. exact (MK_COMB (@lem3330563 _87026) (@lem3330543 _86990 _87026)). Qed.
Lemma lem3330573 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : ((term12 _86990 x s t) = (term13 _86990 s x t)) = ((term12 _86990 x s t) = (term13 _86990 s x t)).
Proof. exact (eq_refl ((term12 _86990 x s t) = (term13 _86990 s x t))). Qed.
Lemma lem3330574 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term191 _86990 s t) = (term191 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3330573 _86990 s x t)). Qed.
Lemma lem3330575 {_86990 : Type'} : (@all _86990) = (@all _86990).
Proof. exact (eq_refl (@all _86990)). Qed.
Lemma lem3330576 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term10 _86990 s t) = (term10 _86990 s t).
Proof. exact (MK_COMB (@lem3330575 _86990) (@lem3330574 _86990 s t)). Qed.
Lemma lem3330577 {_86990 : Type'} (s : _86990 -> Prop) : (term192 _86990 s) = (term192 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3330576 _86990 s t)). Qed.
Lemma lem3330578 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3330579 {_86990 : Type'} (s : _86990 -> Prop) : (term8 _86990 s) = (term8 _86990 s).
Proof. exact (MK_COMB (@lem3330578 _86990) (@lem3330577 _86990 s)). Qed.
Lemma lem3330580 {_86990 : Type'} : (term193 _86990) = (term193 _86990).
Proof. exact (fun_ext (fun s : _86990 -> Prop => @lem3330579 _86990 s)). Qed.
Lemma lem3330581 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3330582 {_86990 : Type'} : (term167 _86990) = (term167 _86990).
Proof. exact (MK_COMB (@lem3330581 _86990) (@lem3330580 _86990)). Qed.
Lemma lem3330583 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3330584 {_86990 : Type'} : (term177 _86990) = (term177 _86990).
Proof. exact (MK_COMB (@lem3330583) (@lem3330582 _86990)). Qed.
Lemma lem3330585 {_86990 _87026 : Type'} : (term181 _86990 _87026) = (term181 _86990 _87026).
Proof. exact (MK_COMB (@lem3330584 _86990) (@lem3330564 _86990 _87026)). Qed.
Lemma lem3330586 {_87026 : Type'} (x : _87026) (t' : _87026 -> Prop) : (@IN _87026 x t') = (@IN _87026 x t').
Proof. exact (eq_refl (@IN _87026 x t')). Qed.
Lemma lem3330591 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term144 _87026 s t' t x) = (term144 _87026 s t' t x).
Proof. exact (eq_refl (term144 _87026 s t' t x)). Qed.
Lemma lem3330592 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term146 _87026 s t' t) = (term146 _87026 s t' t).
Proof. exact (fun_ext (fun x : _87026 -> Prop => @lem3330591 _87026 s t' t x)). Qed.
Lemma lem3330593 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3330594 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term147 _87026 s t' t) = (term147 _87026 s t' t).
Proof. exact (MK_COMB (@lem3330593 _87026) (@lem3330592 _87026 s t' t)). Qed.
Lemma lem3330595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3330596 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term149 _87026 s t' t) = (term149 _87026 s t' t).
Proof. exact (MK_COMB (@lem3330595) (@lem3330594 _87026 s t' t)). Qed.
Lemma lem3330597 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term151 _87026 s t x t') = (term151 _87026 s t x t').
Proof. exact (MK_COMB (@lem3330596 _87026 s t' t) (@lem3330586 _87026 x t')). Qed.
Lemma lem3330598 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term153 _87026 s t x) = (term153 _87026 s t x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3330597 _87026 s t x t')). Qed.
Lemma lem3330599 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3330600 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term154 _87026 s t x) = (term154 _87026 s t x).
Proof. exact (MK_COMB (@lem3330599 _87026) (@lem3330598 _87026 s t x)). Qed.
Lemma lem3330605 {_87026 : Type'} (s : type686 _87026) (x : _87026) (t : _87026 -> Prop) : (term194 _87026 s x t) = (term194 _87026 s x t).
Proof. exact (eq_refl (term194 _87026 s x t)). Qed.
Lemma lem3330606 {_87026 : Type'} (s : type686 _87026) (x : _87026) : (term195 _87026 s x) = (term195 _87026 s x).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3330605 _87026 s x t)). Qed.
Lemma lem3330607 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3330608 {_87026 : Type'} (s : type686 _87026) (x : _87026) : (term24 _87026 s x) = (term24 _87026 s x).
Proof. exact (MK_COMB (@lem3330607 _87026) (@lem3330606 _87026 s x)). Qed.
Lemma lem3330611 {_87026 : Type'} (x : _87026) (t : _87026 -> Prop) : (term120 _87026 x t) = (term120 _87026 x t).
Proof. exact (eq_refl (term120 _87026 x t)). Qed.
Lemma lem3330612 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term121 _87026 t s x) = (term121 _87026 t s x).
Proof. exact (MK_COMB (@lem3330611 _87026 x t) (@lem3330608 _87026 s x)). Qed.
Lemma lem3330613 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3330614 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term123 _87026 t s x) = (term123 _87026 t s x).
Proof. exact (MK_COMB (@lem3330613) (@lem3330612 _87026 t s x)). Qed.
Lemma lem3330615 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : ((term121 _87026 t s x) = (term154 _87026 s t x)) = ((term121 _87026 t s x) = (term154 _87026 s t x)).
Proof. exact (MK_COMB (@lem3330614 _87026 t s x) (@lem3330600 _87026 s t x)). Qed.
Lemma lem3330616 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term156 _87026 s t) = (term156 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3330615 _87026 s t x)). Qed.
Lemma lem3330617 {_87026 : Type'} : (@all _87026) = (@all _87026).
Proof. exact (eq_refl (@all _87026)). Qed.
Lemma lem3330618 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term157 _87026 s t) = (term157 _87026 s t).
Proof. exact (MK_COMB (@lem3330617 _87026) (@lem3330616 _87026 s t)). Qed.
Lemma lem3330619 {_87026 : Type'} (s : type686 _87026) : (term158 _87026 s) = (term158 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3330618 _87026 s t)). Qed.
Lemma lem3330620 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3330621 {_87026 : Type'} (s : type686 _87026) : (term159 _87026 s) = (term159 _87026 s).
Proof. exact (MK_COMB (@lem3330620 _87026) (@lem3330619 _87026 s)). Qed.
Lemma lem3330622 {_87026 : Type'} : (term160 _87026) = (term160 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3330621 _87026 s)). Qed.
Lemma lem3330623 {_87026 : Type'} : (@all ((_87026 -> Prop) -> Prop)) = (@all ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3330624 {_87026 : Type'} : (term161 _87026) = (term161 _87026).
Proof. exact (MK_COMB (@lem3330623 _87026) (@lem3330622 _87026)). Qed.
Lemma lem3330625 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (@IN _86990 x t') = (@IN _86990 x t').
Proof. exact (eq_refl (@IN _86990 x t')). Qed.
Lemma lem3330630 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term99 _86990 s t' x t) = (term99 _86990 s t' x t).
Proof. exact (eq_refl (term99 _86990 s t' x t)). Qed.
Lemma lem3330631 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term101 _86990 s t' t) = (term101 _86990 s t' t).
Proof. exact (fun_ext (fun x : _86990 -> Prop => @lem3330630 _86990 s t' x t)). Qed.
Lemma lem3330632 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3330633 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term102 _86990 s t' t) = (term102 _86990 s t' t).
Proof. exact (MK_COMB (@lem3330632 _86990) (@lem3330631 _86990 s t' t)). Qed.
Lemma lem3330634 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3330635 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term104 _86990 s t' t) = (term104 _86990 s t' t).
Proof. exact (MK_COMB (@lem3330634) (@lem3330633 _86990 s t' t)). Qed.
Lemma lem3330636 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term106 _86990 s t x t') = (term106 _86990 s t x t').
Proof. exact (MK_COMB (@lem3330635 _86990 s t' t) (@lem3330625 _86990 x t')). Qed.
Lemma lem3330637 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term108 _86990 s t x) = (term108 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3330636 _86990 s t x t')). Qed.
Lemma lem3330638 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3330639 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term109 _86990 s t x) = (term109 _86990 s t x).
Proof. exact (MK_COMB (@lem3330638 _86990) (@lem3330637 _86990 s t x)). Qed.
Lemma lem3330640 {_86990 : Type'} (x : _86990) (t : _86990 -> Prop) : (@IN _86990 x t) = (@IN _86990 x t).
Proof. exact (eq_refl (@IN _86990 x t)). Qed.
Lemma lem3330645 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term194 _86990 s x t) = (term194 _86990 s x t).
Proof. exact (eq_refl (term194 _86990 s x t)). Qed.
Lemma lem3330646 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term195 _86990 s x) = (term195 _86990 s x).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3330645 _86990 s x t)). Qed.
Lemma lem3330647 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3330648 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term24 _86990 s x) = (term24 _86990 s x).
Proof. exact (MK_COMB (@lem3330647 _86990) (@lem3330646 _86990 s x)). Qed.
Lemma lem3330649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3330650 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term58 _86990 s x) = (term58 _86990 s x).
Proof. exact (MK_COMB (@lem3330649) (@lem3330648 _86990 s x)). Qed.
Lemma lem3330651 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term59 _86990 s x t) = (term59 _86990 s x t).
Proof. exact (MK_COMB (@lem3330650 _86990 s x) (@lem3330640 _86990 x t)). Qed.
Lemma lem3330652 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3330653 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term61 _86990 s x t) = (term61 _86990 s x t).
Proof. exact (MK_COMB (@lem3330652) (@lem3330651 _86990 s x t)). Qed.
Lemma lem3330654 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : ((term59 _86990 s x t) = (term109 _86990 s t x)) = ((term59 _86990 s x t) = (term109 _86990 s t x)).
Proof. exact (MK_COMB (@lem3330653 _86990 s x t) (@lem3330639 _86990 s t x)). Qed.
Lemma lem3330655 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term111 _86990 s t) = (term111 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3330654 _86990 s t x)). Qed.
Lemma lem3330656 {_86990 : Type'} : (@all _86990) = (@all _86990).
Proof. exact (eq_refl (@all _86990)). Qed.
Lemma lem3330657 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term112 _86990 s t) = (term112 _86990 s t).
Proof. exact (MK_COMB (@lem3330656 _86990) (@lem3330655 _86990 s t)). Qed.
Lemma lem3330658 {_86990 : Type'} (s : type686 _86990) : (term113 _86990 s) = (term113 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3330657 _86990 s t)). Qed.
Lemma lem3330659 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3330660 {_86990 : Type'} (s : type686 _86990) : (term114 _86990 s) = (term114 _86990 s).
Proof. exact (MK_COMB (@lem3330659 _86990) (@lem3330658 _86990 s)). Qed.
Lemma lem3330661 {_86990 : Type'} : (term115 _86990) = (term115 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3330660 _86990 s)). Qed.
Lemma lem3330662 {_86990 : Type'} : (@all ((_86990 -> Prop) -> Prop)) = (@all ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3330663 {_86990 : Type'} : (term116 _86990) = (term116 _86990).
Proof. exact (MK_COMB (@lem3330662 _86990) (@lem3330661 _86990)). Qed.
Lemma lem3330664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3330665 {_86990 : Type'} : (term117 _86990) = (term117 _86990).
Proof. exact (MK_COMB (@lem3330664) (@lem3330663 _86990)). Qed.
Lemma lem3330666 {_86990 _87026 : Type'} : (term162 _86990 _87026) = (term162 _86990 _87026).
Proof. exact (MK_COMB (@lem3330665 _86990) (@lem3330624 _87026)). Qed.
Lemma lem3330667 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3330668 {_86990 _87026 : Type'} : (term165 _86990 _87026) = (term165 _86990 _87026).
Proof. exact (MK_COMB (@lem3330667) (@lem3330666 _86990 _87026)). Qed.
Lemma lem3330669 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3330670 {_86990 _87026 : Type'} : (term182 _86990 _87026) = (term182 _86990 _87026).
Proof. exact (MK_COMB (@lem3330669) (@lem3330668 _86990 _87026)). Qed.
Lemma lem3330671 {_86990 _87026 : Type'} : (term183 _86990 _87026) = (term183 _86990 _87026).
Proof. exact (MK_COMB (@lem3330670 _86990 _87026) (@lem3330585 _86990 _87026)). Qed.
Lemma lem3330852 {_86990 _87026 : Type'} : (term168 _86990 _87026) = (term183 _86990 _87026).
Proof. exact (TRANS (@lem3330502 _86990 _87026) (@lem3330671 _86990 _87026)). Qed.
Lemma lem3330853 {_86990 _87026 : Type'} : (term183 _86990 _87026) = (term168 _86990 _87026).
Proof. exact (SYM (@lem3330852 _86990 _87026)). Qed.
Lemma lem3330854 {_86990 _87026 : Type'} (h1 : term165 _86990 _87026) : term165 _86990 _87026.
Proof. exact (h1). Qed.
Lemma lem3330855 {_86990 : Type'} (h1 : term167 _86990) : term167 _86990.
Proof. exact (h1). Qed.
Lemma lem3330856 {_87026 : Type'} (h1 : term167 _87026) : term167 _87026.
Proof. exact (h1). Qed.
Lemma lem3330867 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term196 _86990 s x t) = (term197 _86990 s x t).
Proof. exact (@lem17045 (@IN (_86990 -> Prop) t s) (@IN _86990 x t)). Qed.
Lemma lem3330870 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term194 _86990 s x t) = (term194 _86990 s x t).
Proof. exact (eq_refl (term194 _86990 s x t)). Qed.
Lemma lem3330871 {_86990 : Type'} (P : type686 _86990) : (term198 _86990 P) = (term199 _86990 P).
Proof. exact (@lem18394 (_86990 -> Prop) P). Qed.
Lemma lem3330872 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term200 _86990 s x) = (term201 _86990 s x).
Proof. exact (@lem3330871 _86990 (term195 _86990 s x)). Qed.
Lemma lem3330873 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term202 _86990 s x t) = (term194 _86990 s x t).
Proof. exact (eq_refl (term202 _86990 s x t)). Qed.
Lemma lem3330874 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3330875 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term203 _86990 s x t) = (term196 _86990 s x t).
Proof. exact (MK_COMB (@lem3330874) (@lem3330873 _86990 s x t)). Qed.
Lemma lem3330876 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term203 _86990 s x t) = (term197 _86990 s x t).
Proof. exact (TRANS (@lem3330875 _86990 s x t) (@lem3330867 _86990 s x t)). Qed.
Lemma lem3330877 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term204 _86990 s x) = (term205 _86990 s x).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3330876 _86990 s x t)). Qed.
Lemma lem3330878 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3330879 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term201 _86990 s x) = (term206 _86990 s x).
Proof. exact (MK_COMB (@lem3330878 _86990) (@lem3330877 _86990 s x)). Qed.
Lemma lem3330880 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term200 _86990 s x) = (term206 _86990 s x).
Proof. exact (TRANS (@lem3330872 _86990 s x) (@lem3330879 _86990 s x)). Qed.
Lemma lem3330881 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term195 _86990 s x) = (term195 _86990 s x).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3330870 _86990 s x t)). Qed.
Lemma lem3330882 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3330883 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term24 _86990 s x) = (term24 _86990 s x).
Proof. exact (MK_COMB (@lem3330882 _86990) (@lem3330881 _86990 s x)). Qed.
Lemma lem3330884 {_86990 : Type'} (x : _86990) (t : _86990 -> Prop) : (term207 _86990 x t) = (term207 _86990 x t).
Proof. exact (eq_refl (term207 _86990 x t)). Qed.
Lemma lem3330885 {_86990 : Type'} (x : _86990) (t : _86990 -> Prop) : (@IN _86990 x t) = (@IN _86990 x t).
Proof. exact (eq_refl (@IN _86990 x t)). Qed.
Lemma lem3330886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3330887 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term208 _86990 s x) = (term209 _86990 s x).
Proof. exact (MK_COMB (@lem3330886) (@lem3330880 _86990 s x)). Qed.
Lemma lem3330888 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term210 _86990 s x t) = (term211 _86990 s x t).
Proof. exact (MK_COMB (@lem3330887 _86990 s x) (@lem3330884 _86990 x t)). Qed.
Lemma lem3330889 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term212 _86990 s x t) = (term210 _86990 s x t).
Proof. exact (@lem17045 (term24 _86990 s x) (@IN _86990 x t)). Qed.
Lemma lem3330890 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term212 _86990 s x t) = (term211 _86990 s x t).
Proof. exact (TRANS (@lem3330889 _86990 s x t) (@lem3330888 _86990 s x t)). Qed.
Lemma lem3330891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3330892 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term58 _86990 s x) = (term58 _86990 s x).
Proof. exact (MK_COMB (@lem3330891) (@lem3330883 _86990 s x)). Qed.
Lemma lem3330893 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term59 _86990 s x t) = (term59 _86990 s x t).
Proof. exact (MK_COMB (@lem3330892 _86990 s x) (@lem3330885 _86990 x t)). Qed.
Lemma lem3330902 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term213 _86990 s t' x t) = (term214 _86990 s t' x t).
Proof. exact (@lem17045 (@IN (_86990 -> Prop) x s) (t' = (@INTER _86990 x t))). Qed.
Lemma lem3330905 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term99 _86990 s t' x t) = (term99 _86990 s t' x t).
Proof. exact (eq_refl (term99 _86990 s t' x t)). Qed.
Lemma lem3330906 {_86990 : Type'} (P : type686 _86990) : (term198 _86990 P) = (term199 _86990 P).
Proof. exact (@lem18394 (_86990 -> Prop) P). Qed.
Lemma lem3330907 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term215 _86990 s t' t) = (term216 _86990 s t' t).
Proof. exact (@lem3330906 _86990 (term101 _86990 s t' t)). Qed.
Lemma lem3330908 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term217 _86990 s t' t x) = (term99 _86990 s t' x t).
Proof. exact (eq_refl (term217 _86990 s t' t x)). Qed.
Lemma lem3330909 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3330910 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term218 _86990 s t' t x) = (term213 _86990 s t' x t).
Proof. exact (MK_COMB (@lem3330909) (@lem3330908 _86990 s t' x t)). Qed.
Lemma lem3330911 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term218 _86990 s t' t x) = (term214 _86990 s t' x t).
Proof. exact (TRANS (@lem3330910 _86990 s t' x t) (@lem3330902 _86990 s t' x t)). Qed.
Lemma lem3330912 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term219 _86990 s t' t) = (term220 _86990 s t' t).
Proof. exact (fun_ext (fun x : _86990 -> Prop => @lem3330911 _86990 s t' x t)). Qed.
Lemma lem3330913 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3330914 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term216 _86990 s t' t) = (term221 _86990 s t' t).
Proof. exact (MK_COMB (@lem3330913 _86990) (@lem3330912 _86990 s t' t)). Qed.
Lemma lem3330915 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term215 _86990 s t' t) = (term221 _86990 s t' t).
Proof. exact (TRANS (@lem3330907 _86990 s t' t) (@lem3330914 _86990 s t' t)). Qed.
Lemma lem3330916 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term101 _86990 s t' t) = (term101 _86990 s t' t).
Proof. exact (fun_ext (fun x : _86990 -> Prop => @lem3330905 _86990 s t' x t)). Qed.
Lemma lem3330917 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3330918 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term102 _86990 s t' t) = (term102 _86990 s t' t).
Proof. exact (MK_COMB (@lem3330917 _86990) (@lem3330916 _86990 s t' t)). Qed.
Lemma lem3330919 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (term207 _86990 x t') = (term207 _86990 x t').
Proof. exact (eq_refl (term207 _86990 x t')). Qed.
Lemma lem3330920 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (@IN _86990 x t') = (@IN _86990 x t').
Proof. exact (eq_refl (@IN _86990 x t')). Qed.
Lemma lem3330921 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3330922 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term222 _86990 s t' t) = (term223 _86990 s t' t).
Proof. exact (MK_COMB (@lem3330921) (@lem3330915 _86990 s t' t)). Qed.
Lemma lem3330923 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term224 _86990 s t x t') = (term225 _86990 s t x t').
Proof. exact (MK_COMB (@lem3330922 _86990 s t' t) (@lem3330919 _86990 x t')). Qed.
Lemma lem3330924 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term226 _86990 s t x t') = (term224 _86990 s t x t').
Proof. exact (@lem17045 (term102 _86990 s t' t) (@IN _86990 x t')). Qed.
Lemma lem3330925 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term226 _86990 s t x t') = (term225 _86990 s t x t').
Proof. exact (TRANS (@lem3330924 _86990 s t x t') (@lem3330923 _86990 s t x t')). Qed.
Lemma lem3330926 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3330927 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term104 _86990 s t' t) = (term104 _86990 s t' t).
Proof. exact (MK_COMB (@lem3330926) (@lem3330918 _86990 s t' t)). Qed.
Lemma lem3330928 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term106 _86990 s t x t') = (term106 _86990 s t x t').
Proof. exact (MK_COMB (@lem3330927 _86990 s t' t) (@lem3330920 _86990 x t')). Qed.
Lemma lem3330929 {_86990 : Type'} (P : type686 _86990) : (term198 _86990 P) = (term199 _86990 P).
Proof. exact (@lem18394 (_86990 -> Prop) P). Qed.
Lemma lem3330930 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term227 _86990 s t x) = (term228 _86990 s t x).
Proof. exact (@lem3330929 _86990 (term108 _86990 s t x)). Qed.
Lemma lem3330931 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term229 _86990 s t x t') = (term106 _86990 s t x t').
Proof. exact (eq_refl (term229 _86990 s t x t')). Qed.
Lemma lem3330932 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3330933 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term230 _86990 s t x t') = (term226 _86990 s t x t').
Proof. exact (MK_COMB (@lem3330932) (@lem3330931 _86990 s t x t')). Qed.
Lemma lem3330934 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term230 _86990 s t x t') = (term225 _86990 s t x t').
Proof. exact (TRANS (@lem3330933 _86990 s t x t') (@lem3330925 _86990 s t x t')). Qed.
Lemma lem3330935 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term231 _86990 s t x) = (term232 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3330934 _86990 s t x t')). Qed.
Lemma lem3330936 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3330937 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term228 _86990 s t x) = (term233 _86990 s t x).
Proof. exact (MK_COMB (@lem3330936 _86990) (@lem3330935 _86990 s t x)). Qed.
Lemma lem3330938 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term227 _86990 s t x) = (term233 _86990 s t x).
Proof. exact (TRANS (@lem3330930 _86990 s t x) (@lem3330937 _86990 s t x)). Qed.
Lemma lem3330939 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term108 _86990 s t x) = (term108 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3330928 _86990 s t x t')). Qed.
Lemma lem3330940 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3330941 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term109 _86990 s t x) = (term109 _86990 s t x).
Proof. exact (MK_COMB (@lem3330940 _86990) (@lem3330939 _86990 s t x)). Qed.
Lemma lem3330942 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3330943 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term234 _86990 s x t) = (term235 _86990 s x t).
Proof. exact (MK_COMB (@lem3330942) (@lem3330890 _86990 s x t)). Qed.
Lemma lem3330944 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term236 _86990 s t x) = (term237 _86990 s t x).
Proof. exact (MK_COMB (@lem3330943 _86990 s x t) (@lem3330941 _86990 s t x)). Qed.
Lemma lem3330945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3330946 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term238 _86990 s x t) = (term238 _86990 s x t).
Proof. exact (MK_COMB (@lem3330945) (@lem3330893 _86990 s x t)). Qed.
Lemma lem3330947 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term239 _86990 s t x) = (term240 _86990 s t x).
Proof. exact (MK_COMB (@lem3330946 _86990 s x t) (@lem3330938 _86990 s t x)). Qed.
Lemma lem3330948 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3330949 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term241 _86990 s t x) = (term242 _86990 s t x).
Proof. exact (MK_COMB (@lem3330948) (@lem3330947 _86990 s t x)). Qed.
Lemma lem3330950 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term243 _86990 s t x) = (term244 _86990 s t x).
Proof. exact (MK_COMB (@lem3330949 _86990 s t x) (@lem3330944 _86990 s t x)). Qed.
Lemma lem3330951 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term245 _86990 s t x) = (term243 _86990 s t x).
Proof. exact (@lem17646 (term59 _86990 s x t) (term109 _86990 s t x)). Qed.
Lemma lem3330952 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term245 _86990 s t x) = (term244 _86990 s t x).
Proof. exact (TRANS (@lem3330951 _86990 s t x) (@lem3330950 _86990 s t x)). Qed.
Lemma lem3330953 {_86990 : Type'} (P : _86990 -> Prop) : (term246 _86990 P) = (term247 _86990 P).
Proof. exact (@lem18392 _86990 P). Qed.
Lemma lem3330954 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term248 _86990 s t) = (term249 _86990 s t).
Proof. exact (@lem3330953 _86990 (term111 _86990 s t)). Qed.
Lemma lem3330955 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term250 _86990 s t x) = ((term59 _86990 s x t) = (term109 _86990 s t x)).
Proof. exact (eq_refl (term250 _86990 s t x)). Qed.
Lemma lem3330956 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3330957 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term251 _86990 s t x) = (term245 _86990 s t x).
Proof. exact (MK_COMB (@lem3330956) (@lem3330955 _86990 s t x)). Qed.
Lemma lem3330958 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term251 _86990 s t x) = (term244 _86990 s t x).
Proof. exact (TRANS (@lem3330957 _86990 s t x) (@lem3330952 _86990 s t x)). Qed.
Lemma lem3330959 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term252 _86990 s t) = (term253 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3330958 _86990 s t x)). Qed.
Lemma lem3330960 {_86990 : Type'} : (@ex _86990) = (@ex _86990).
Proof. exact (eq_refl (@ex _86990)). Qed.
Lemma lem3330961 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term249 _86990 s t) = (term254 _86990 s t).
Proof. exact (MK_COMB (@lem3330960 _86990) (@lem3330959 _86990 s t)). Qed.
Lemma lem3330962 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term248 _86990 s t) = (term254 _86990 s t).
Proof. exact (TRANS (@lem3330954 _86990 s t) (@lem3330961 _86990 s t)). Qed.
Lemma lem3330963 {_86990 : Type'} (P : type686 _86990) : (term255 _86990 P) = (term256 _86990 P).
Proof. exact (@lem18392 (_86990 -> Prop) P). Qed.
Lemma lem3330964 {_86990 : Type'} (s : type686 _86990) : (term257 _86990 s) = (term258 _86990 s).
Proof. exact (@lem3330963 _86990 (term113 _86990 s)). Qed.
Lemma lem3330965 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term259 _86990 s t) = (term112 _86990 s t).
Proof. exact (eq_refl (term259 _86990 s t)). Qed.
Lemma lem3330966 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3330967 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term260 _86990 s t) = (term248 _86990 s t).
Proof. exact (MK_COMB (@lem3330966) (@lem3330965 _86990 s t)). Qed.
Lemma lem3330968 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term260 _86990 s t) = (term254 _86990 s t).
Proof. exact (TRANS (@lem3330967 _86990 s t) (@lem3330962 _86990 s t)). Qed.
Lemma lem3330969 {_86990 : Type'} (s : type686 _86990) : (term261 _86990 s) = (term262 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3330968 _86990 s t)). Qed.
Lemma lem3330970 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3330971 {_86990 : Type'} (s : type686 _86990) : (term258 _86990 s) = (term263 _86990 s).
Proof. exact (MK_COMB (@lem3330970 _86990) (@lem3330969 _86990 s)). Qed.
Lemma lem3330972 {_86990 : Type'} (s : type686 _86990) : (term257 _86990 s) = (term263 _86990 s).
Proof. exact (TRANS (@lem3330964 _86990 s) (@lem3330971 _86990 s)). Qed.
Lemma lem3330973 {_86990 : Type'} (P : type180 _86990) : (term264 _86990 P) = (term265 _86990 P).
Proof. exact (@lem18392 (type686 _86990) P). Qed.
Lemma lem3330974 {_86990 : Type'} : (term266 _86990) = (term267 _86990).
Proof. exact (@lem3330973 _86990 (term115 _86990)). Qed.
Lemma lem3330975 {_86990 : Type'} (s : type686 _86990) : (term268 _86990 s) = (term114 _86990 s).
Proof. exact (eq_refl (term268 _86990 s)). Qed.
Lemma lem3330976 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3330977 {_86990 : Type'} (s : type686 _86990) : (term269 _86990 s) = (term257 _86990 s).
Proof. exact (MK_COMB (@lem3330976) (@lem3330975 _86990 s)). Qed.
Lemma lem3330978 {_86990 : Type'} (s : type686 _86990) : (term269 _86990 s) = (term263 _86990 s).
Proof. exact (TRANS (@lem3330977 _86990 s) (@lem3330972 _86990 s)). Qed.
Lemma lem3330979 {_86990 : Type'} : (term270 _86990) = (term271 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3330978 _86990 s)). Qed.
Lemma lem3330980 {_86990 : Type'} : (@ex ((_86990 -> Prop) -> Prop)) = (@ex ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3330981 {_86990 : Type'} : (term267 _86990) = (term272 _86990).
Proof. exact (MK_COMB (@lem3330980 _86990) (@lem3330979 _86990)). Qed.
Lemma lem3330982 {_86990 : Type'} : (term266 _86990) = (term272 _86990).
Proof. exact (TRANS (@lem3330974 _86990) (@lem3330981 _86990)). Qed.
Lemma lem3330993 {_87026 : Type'} (s : type686 _87026) (x : _87026) (t : _87026 -> Prop) : (term196 _87026 s x t) = (term197 _87026 s x t).
Proof. exact (@lem17045 (@IN (_87026 -> Prop) t s) (@IN _87026 x t)). Qed.
Lemma lem3330996 {_87026 : Type'} (s : type686 _87026) (x : _87026) (t : _87026 -> Prop) : (term194 _87026 s x t) = (term194 _87026 s x t).
Proof. exact (eq_refl (term194 _87026 s x t)). Qed.
Lemma lem3330997 {_87026 : Type'} (P : type686 _87026) : (term198 _87026 P) = (term199 _87026 P).
Proof. exact (@lem18394 (_87026 -> Prop) P). Qed.
Lemma lem3330998 {_87026 : Type'} (s : type686 _87026) (x : _87026) : (term200 _87026 s x) = (term201 _87026 s x).
Proof. exact (@lem3330997 _87026 (term195 _87026 s x)). Qed.
Lemma lem3330999 {_87026 : Type'} (s : type686 _87026) (x : _87026) (t : _87026 -> Prop) : (term202 _87026 s x t) = (term194 _87026 s x t).
Proof. exact (eq_refl (term202 _87026 s x t)). Qed.
Lemma lem3331000 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3331001 {_87026 : Type'} (s : type686 _87026) (x : _87026) (t : _87026 -> Prop) : (term203 _87026 s x t) = (term196 _87026 s x t).
Proof. exact (MK_COMB (@lem3331000) (@lem3330999 _87026 s x t)). Qed.
Lemma lem3331002 {_87026 : Type'} (s : type686 _87026) (x : _87026) (t : _87026 -> Prop) : (term203 _87026 s x t) = (term197 _87026 s x t).
Proof. exact (TRANS (@lem3331001 _87026 s x t) (@lem3330993 _87026 s x t)). Qed.
Lemma lem3331003 {_87026 : Type'} (s : type686 _87026) (x : _87026) : (term204 _87026 s x) = (term205 _87026 s x).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3331002 _87026 s x t)). Qed.
Lemma lem3331004 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3331005 {_87026 : Type'} (s : type686 _87026) (x : _87026) : (term201 _87026 s x) = (term206 _87026 s x).
Proof. exact (MK_COMB (@lem3331004 _87026) (@lem3331003 _87026 s x)). Qed.
Lemma lem3331006 {_87026 : Type'} (s : type686 _87026) (x : _87026) : (term200 _87026 s x) = (term206 _87026 s x).
Proof. exact (TRANS (@lem3330998 _87026 s x) (@lem3331005 _87026 s x)). Qed.
Lemma lem3331007 {_87026 : Type'} (s : type686 _87026) (x : _87026) : (term195 _87026 s x) = (term195 _87026 s x).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3330996 _87026 s x t)). Qed.
Lemma lem3331008 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3331009 {_87026 : Type'} (s : type686 _87026) (x : _87026) : (term24 _87026 s x) = (term24 _87026 s x).
Proof. exact (MK_COMB (@lem3331008 _87026) (@lem3331007 _87026 s x)). Qed.
Lemma lem3331011 {_87026 : Type'} (x : _87026) (t : _87026 -> Prop) : (term273 _87026 x t) = (term273 _87026 x t).
Proof. exact (eq_refl (term273 _87026 x t)). Qed.
Lemma lem3331012 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term274 _87026 t s x) = (term275 _87026 t s x).
Proof. exact (MK_COMB (@lem3331011 _87026 x t) (@lem3331006 _87026 s x)). Qed.
Lemma lem3331013 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term276 _87026 t s x) = (term274 _87026 t s x).
Proof. exact (@lem17045 (@IN _87026 x t) (term24 _87026 s x)). Qed.
Lemma lem3331014 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term276 _87026 t s x) = (term275 _87026 t s x).
Proof. exact (TRANS (@lem3331013 _87026 t s x) (@lem3331012 _87026 t s x)). Qed.
Lemma lem3331016 {_87026 : Type'} (x : _87026) (t : _87026 -> Prop) : (term120 _87026 x t) = (term120 _87026 x t).
Proof. exact (eq_refl (term120 _87026 x t)). Qed.
Lemma lem3331017 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term121 _87026 t s x) = (term121 _87026 t s x).
Proof. exact (MK_COMB (@lem3331016 _87026 x t) (@lem3331009 _87026 s x)). Qed.
Lemma lem3331026 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term277 _87026 s t' t x) = (term278 _87026 s t' t x).
Proof. exact (@lem17045 (@IN (_87026 -> Prop) x s) (t' = (@INTER _87026 t x))). Qed.
Lemma lem3331029 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term144 _87026 s t' t x) = (term144 _87026 s t' t x).
Proof. exact (eq_refl (term144 _87026 s t' t x)). Qed.
Lemma lem3331030 {_87026 : Type'} (P : type686 _87026) : (term198 _87026 P) = (term199 _87026 P).
Proof. exact (@lem18394 (_87026 -> Prop) P). Qed.
Lemma lem3331031 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term279 _87026 s t' t) = (term280 _87026 s t' t).
Proof. exact (@lem3331030 _87026 (term146 _87026 s t' t)). Qed.
Lemma lem3331032 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term281 _87026 s t' t x) = (term144 _87026 s t' t x).
Proof. exact (eq_refl (term281 _87026 s t' t x)). Qed.
Lemma lem3331033 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3331034 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term282 _87026 s t' t x) = (term277 _87026 s t' t x).
Proof. exact (MK_COMB (@lem3331033) (@lem3331032 _87026 s t' t x)). Qed.
Lemma lem3331035 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term282 _87026 s t' t x) = (term278 _87026 s t' t x).
Proof. exact (TRANS (@lem3331034 _87026 s t' t x) (@lem3331026 _87026 s t' t x)). Qed.
Lemma lem3331036 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term283 _87026 s t' t) = (term284 _87026 s t' t).
Proof. exact (fun_ext (fun x : _87026 -> Prop => @lem3331035 _87026 s t' t x)). Qed.
Lemma lem3331037 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3331038 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term280 _87026 s t' t) = (term285 _87026 s t' t).
Proof. exact (MK_COMB (@lem3331037 _87026) (@lem3331036 _87026 s t' t)). Qed.
Lemma lem3331039 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term279 _87026 s t' t) = (term285 _87026 s t' t).
Proof. exact (TRANS (@lem3331031 _87026 s t' t) (@lem3331038 _87026 s t' t)). Qed.
Lemma lem3331040 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term146 _87026 s t' t) = (term146 _87026 s t' t).
Proof. exact (fun_ext (fun x : _87026 -> Prop => @lem3331029 _87026 s t' t x)). Qed.
Lemma lem3331041 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3331042 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term147 _87026 s t' t) = (term147 _87026 s t' t).
Proof. exact (MK_COMB (@lem3331041 _87026) (@lem3331040 _87026 s t' t)). Qed.
Lemma lem3331043 {_87026 : Type'} (x : _87026) (t' : _87026 -> Prop) : (term207 _87026 x t') = (term207 _87026 x t').
Proof. exact (eq_refl (term207 _87026 x t')). Qed.
Lemma lem3331044 {_87026 : Type'} (x : _87026) (t' : _87026 -> Prop) : (@IN _87026 x t') = (@IN _87026 x t').
Proof. exact (eq_refl (@IN _87026 x t')). Qed.
Lemma lem3331045 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3331046 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term286 _87026 s t' t) = (term287 _87026 s t' t).
Proof. exact (MK_COMB (@lem3331045) (@lem3331039 _87026 s t' t)). Qed.
Lemma lem3331047 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term288 _87026 s t x t') = (term289 _87026 s t x t').
Proof. exact (MK_COMB (@lem3331046 _87026 s t' t) (@lem3331043 _87026 x t')). Qed.
Lemma lem3331048 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term290 _87026 s t x t') = (term288 _87026 s t x t').
Proof. exact (@lem17045 (term147 _87026 s t' t) (@IN _87026 x t')). Qed.
Lemma lem3331049 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term290 _87026 s t x t') = (term289 _87026 s t x t').
Proof. exact (TRANS (@lem3331048 _87026 s t x t') (@lem3331047 _87026 s t x t')). Qed.
Lemma lem3331050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3331051 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term149 _87026 s t' t) = (term149 _87026 s t' t).
Proof. exact (MK_COMB (@lem3331050) (@lem3331042 _87026 s t' t)). Qed.
Lemma lem3331052 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term151 _87026 s t x t') = (term151 _87026 s t x t').
Proof. exact (MK_COMB (@lem3331051 _87026 s t' t) (@lem3331044 _87026 x t')). Qed.
Lemma lem3331053 {_87026 : Type'} (P : type686 _87026) : (term198 _87026 P) = (term199 _87026 P).
Proof. exact (@lem18394 (_87026 -> Prop) P). Qed.
Lemma lem3331054 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term291 _87026 s t x) = (term292 _87026 s t x).
Proof. exact (@lem3331053 _87026 (term153 _87026 s t x)). Qed.
Lemma lem3331055 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term293 _87026 s t x t') = (term151 _87026 s t x t').
Proof. exact (eq_refl (term293 _87026 s t x t')). Qed.
Lemma lem3331056 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3331057 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term294 _87026 s t x t') = (term290 _87026 s t x t').
Proof. exact (MK_COMB (@lem3331056) (@lem3331055 _87026 s t x t')). Qed.
Lemma lem3331058 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term294 _87026 s t x t') = (term289 _87026 s t x t').
Proof. exact (TRANS (@lem3331057 _87026 s t x t') (@lem3331049 _87026 s t x t')). Qed.
Lemma lem3331059 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term295 _87026 s t x) = (term296 _87026 s t x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3331058 _87026 s t x t')). Qed.
Lemma lem3331060 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3331061 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term292 _87026 s t x) = (term297 _87026 s t x).
Proof. exact (MK_COMB (@lem3331060 _87026) (@lem3331059 _87026 s t x)). Qed.
Lemma lem3331062 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term291 _87026 s t x) = (term297 _87026 s t x).
Proof. exact (TRANS (@lem3331054 _87026 s t x) (@lem3331061 _87026 s t x)). Qed.
Lemma lem3331063 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term153 _87026 s t x) = (term153 _87026 s t x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3331052 _87026 s t x t')). Qed.
Lemma lem3331064 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3331065 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term154 _87026 s t x) = (term154 _87026 s t x).
Proof. exact (MK_COMB (@lem3331064 _87026) (@lem3331063 _87026 s t x)). Qed.
Lemma lem3331066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3331067 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term298 _87026 t s x) = (term299 _87026 t s x).
Proof. exact (MK_COMB (@lem3331066) (@lem3331014 _87026 t s x)). Qed.
Lemma lem3331068 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term300 _87026 s t x) = (term301 _87026 s t x).
Proof. exact (MK_COMB (@lem3331067 _87026 t s x) (@lem3331065 _87026 s t x)). Qed.
Lemma lem3331069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3331070 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term302 _87026 t s x) = (term302 _87026 t s x).
Proof. exact (MK_COMB (@lem3331069) (@lem3331017 _87026 t s x)). Qed.
Lemma lem3331071 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term303 _87026 s t x) = (term304 _87026 s t x).
Proof. exact (MK_COMB (@lem3331070 _87026 t s x) (@lem3331062 _87026 s t x)). Qed.
Lemma lem3331072 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3331073 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term305 _87026 s t x) = (term306 _87026 s t x).
Proof. exact (MK_COMB (@lem3331072) (@lem3331071 _87026 s t x)). Qed.
Lemma lem3331074 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term307 _87026 s t x) = (term308 _87026 s t x).
Proof. exact (MK_COMB (@lem3331073 _87026 s t x) (@lem3331068 _87026 s t x)). Qed.
Lemma lem3331075 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term309 _87026 s t x) = (term307 _87026 s t x).
Proof. exact (@lem17646 (term121 _87026 t s x) (term154 _87026 s t x)). Qed.
Lemma lem3331076 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term309 _87026 s t x) = (term308 _87026 s t x).
Proof. exact (TRANS (@lem3331075 _87026 s t x) (@lem3331074 _87026 s t x)). Qed.
Lemma lem3331077 {_87026 : Type'} (P : _87026 -> Prop) : (term246 _87026 P) = (term247 _87026 P).
Proof. exact (@lem18392 _87026 P). Qed.
Lemma lem3331078 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term310 _87026 s t) = (term311 _87026 s t).
Proof. exact (@lem3331077 _87026 (term156 _87026 s t)). Qed.
Lemma lem3331079 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term312 _87026 s t x) = ((term121 _87026 t s x) = (term154 _87026 s t x)).
Proof. exact (eq_refl (term312 _87026 s t x)). Qed.
Lemma lem3331080 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3331081 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term313 _87026 s t x) = (term309 _87026 s t x).
Proof. exact (MK_COMB (@lem3331080) (@lem3331079 _87026 s t x)). Qed.
Lemma lem3331082 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term313 _87026 s t x) = (term308 _87026 s t x).
Proof. exact (TRANS (@lem3331081 _87026 s t x) (@lem3331076 _87026 s t x)). Qed.
Lemma lem3331083 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term314 _87026 s t) = (term315 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3331082 _87026 s t x)). Qed.
Lemma lem3331084 {_87026 : Type'} : (@ex _87026) = (@ex _87026).
Proof. exact (eq_refl (@ex _87026)). Qed.
Lemma lem3331085 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term311 _87026 s t) = (term316 _87026 s t).
Proof. exact (MK_COMB (@lem3331084 _87026) (@lem3331083 _87026 s t)). Qed.
Lemma lem3331086 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term310 _87026 s t) = (term316 _87026 s t).
Proof. exact (TRANS (@lem3331078 _87026 s t) (@lem3331085 _87026 s t)). Qed.
Lemma lem3331087 {_87026 : Type'} (P : type686 _87026) : (term255 _87026 P) = (term256 _87026 P).
Proof. exact (@lem18392 (_87026 -> Prop) P). Qed.
Lemma lem3331088 {_87026 : Type'} (s : type686 _87026) : (term317 _87026 s) = (term318 _87026 s).
Proof. exact (@lem3331087 _87026 (term158 _87026 s)). Qed.
Lemma lem3331089 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term319 _87026 s t) = (term157 _87026 s t).
Proof. exact (eq_refl (term319 _87026 s t)). Qed.
Lemma lem3331090 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3331091 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term320 _87026 s t) = (term310 _87026 s t).
Proof. exact (MK_COMB (@lem3331090) (@lem3331089 _87026 s t)). Qed.
Lemma lem3331092 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term320 _87026 s t) = (term316 _87026 s t).
Proof. exact (TRANS (@lem3331091 _87026 s t) (@lem3331086 _87026 s t)). Qed.
Lemma lem3331093 {_87026 : Type'} (s : type686 _87026) : (term321 _87026 s) = (term322 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3331092 _87026 s t)). Qed.
Lemma lem3331094 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3331095 {_87026 : Type'} (s : type686 _87026) : (term318 _87026 s) = (term323 _87026 s).
Proof. exact (MK_COMB (@lem3331094 _87026) (@lem3331093 _87026 s)). Qed.
Lemma lem3331096 {_87026 : Type'} (s : type686 _87026) : (term317 _87026 s) = (term323 _87026 s).
Proof. exact (TRANS (@lem3331088 _87026 s) (@lem3331095 _87026 s)). Qed.
Lemma lem3331097 {_87026 : Type'} (P : type180 _87026) : (term264 _87026 P) = (term265 _87026 P).
Proof. exact (@lem18392 (type686 _87026) P). Qed.
Lemma lem3331098 {_87026 : Type'} : (term324 _87026) = (term325 _87026).
Proof. exact (@lem3331097 _87026 (term160 _87026)). Qed.
Lemma lem3331099 {_87026 : Type'} (s : type686 _87026) : (term326 _87026 s) = (term159 _87026 s).
Proof. exact (eq_refl (term326 _87026 s)). Qed.
Lemma lem3331100 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3331101 {_87026 : Type'} (s : type686 _87026) : (term327 _87026 s) = (term317 _87026 s).
Proof. exact (MK_COMB (@lem3331100) (@lem3331099 _87026 s)). Qed.
Lemma lem3331102 {_87026 : Type'} (s : type686 _87026) : (term327 _87026 s) = (term323 _87026 s).
Proof. exact (TRANS (@lem3331101 _87026 s) (@lem3331096 _87026 s)). Qed.
Lemma lem3331103 {_87026 : Type'} : (term328 _87026) = (term329 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3331102 _87026 s)). Qed.
Lemma lem3331104 {_87026 : Type'} : (@ex ((_87026 -> Prop) -> Prop)) = (@ex ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3331105 {_87026 : Type'} : (term325 _87026) = (term330 _87026).
Proof. exact (MK_COMB (@lem3331104 _87026) (@lem3331103 _87026)). Qed.
Lemma lem3331106 {_87026 : Type'} : (term324 _87026) = (term330 _87026).
Proof. exact (TRANS (@lem3331098 _87026) (@lem3331105 _87026)). Qed.
Lemma lem3331107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3331108 {_86990 : Type'} : (term331 _86990) = (term332 _86990).
Proof. exact (MK_COMB (@lem3331107) (@lem3330982 _86990)). Qed.
Lemma lem3331109 {_86990 _87026 : Type'} : (term333 _86990 _87026) = (term334 _86990 _87026).
Proof. exact (MK_COMB (@lem3331108 _86990) (@lem3331106 _87026)). Qed.
Lemma lem3331110 {_86990 _87026 : Type'} : (term165 _86990 _87026) = (term333 _86990 _87026).
Proof. exact (@lem17045 (term116 _86990) (term161 _87026)). Qed.
Lemma lem3331111 {_86990 _87026 : Type'} : (term165 _86990 _87026) = (term334 _86990 _87026).
Proof. exact (TRANS (@lem3331110 _86990 _87026) (@lem3331109 _86990 _87026)). Qed.
Lemma lem3331121 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3331122 {_86990 : Type'} (P : _86990 -> Prop) (Q : _86990 -> Prop) : (term335 _86990 P Q) = (term336 _86990 P Q).
Proof. exact (@lem3331121 _86990 P Q). Qed.
Lemma lem3331123 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term337 _86990 s t) = (term338 _86990 s t).
Proof. exact (@lem3331122 _86990 (term339 _86990 s t) (term340 _86990 s t)). Qed.
Lemma lem3331124 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term341 _86990 s t x) = (term240 _86990 s t x).
Proof. exact (eq_refl (term341 _86990 s t x)). Qed.
Lemma lem3331125 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3331126 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term342 _86990 s t x) = (term242 _86990 s t x).
Proof. exact (MK_COMB (@lem3331125) (@lem3331124 _86990 s t x)). Qed.
Lemma lem3331127 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term343 _86990 s t x) = (term237 _86990 s t x).
Proof. exact (eq_refl (term343 _86990 s t x)). Qed.
Lemma lem3331128 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term344 _86990 s t x) = (term244 _86990 s t x).
Proof. exact (MK_COMB (@lem3331126 _86990 s t x) (@lem3331127 _86990 s t x)). Qed.
Lemma lem3331129 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term345 _86990 s t) = (term253 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3331128 _86990 s t x)). Qed.
Lemma lem3331130 {_86990 : Type'} : (@ex _86990) = (@ex _86990).
Proof. exact (eq_refl (@ex _86990)). Qed.
Lemma lem3331131 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term337 _86990 s t) = (term254 _86990 s t).
Proof. exact (MK_COMB (@lem3331130 _86990) (@lem3331129 _86990 s t)). Qed.
Lemma lem3331132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3331133 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term346 _86990 s t) = (term347 _86990 s t).
Proof. exact (MK_COMB (@lem3331132) (@lem3331131 _86990 s t)). Qed.
Lemma lem3331134 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term341 _86990 s t x) = (term240 _86990 s t x).
Proof. exact (eq_refl (term341 _86990 s t x)). Qed.
Lemma lem3331135 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term348 _86990 s t) = (term339 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3331134 _86990 s t x)). Qed.
Lemma lem3331136 {_86990 : Type'} : (@ex _86990) = (@ex _86990).
Proof. exact (eq_refl (@ex _86990)). Qed.
Lemma lem3331137 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term349 _86990 s t) = (term350 _86990 s t).
Proof. exact (MK_COMB (@lem3331136 _86990) (@lem3331135 _86990 s t)). Qed.
Lemma lem3331138 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3331139 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term351 _86990 s t) = (term352 _86990 s t).
Proof. exact (MK_COMB (@lem3331138) (@lem3331137 _86990 s t)). Qed.
Lemma lem3331140 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term343 _86990 s t x) = (term237 _86990 s t x).
Proof. exact (eq_refl (term343 _86990 s t x)). Qed.
Lemma lem3331141 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term353 _86990 s t) = (term340 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3331140 _86990 s t x)). Qed.
Lemma lem3331142 {_86990 : Type'} : (@ex _86990) = (@ex _86990).
Proof. exact (eq_refl (@ex _86990)). Qed.
Lemma lem3331143 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term354 _86990 s t) = (term355 _86990 s t).
Proof. exact (MK_COMB (@lem3331142 _86990) (@lem3331141 _86990 s t)). Qed.
Lemma lem3331144 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term338 _86990 s t) = (term356 _86990 s t).
Proof. exact (MK_COMB (@lem3331139 _86990 s t) (@lem3331143 _86990 s t)). Qed.
Lemma lem3331145 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : ((term337 _86990 s t) = (term338 _86990 s t)) = ((term254 _86990 s t) = (term356 _86990 s t)).
Proof. exact (MK_COMB (@lem3331133 _86990 s t) (@lem3331144 _86990 s t)). Qed.
Lemma lem3331146 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term254 _86990 s t) = (term356 _86990 s t).
Proof. exact (EQ_MP (@lem3331145 _86990 s t) (@lem3331123 _86990 s t)). Qed.
Lemma lem3331531 {_86990 : Type'} (s : type686 _86990) : (term262 _86990 s) = (term357 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3331146 _86990 s t)). Qed.
Lemma lem3331532 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3331533 {_86990 : Type'} (s : type686 _86990) : (term263 _86990 s) = (term358 _86990 s).
Proof. exact (MK_COMB (@lem3331532 _86990) (@lem3331531 _86990 s)). Qed.
Lemma lem3331535 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3331536 {_86990 : Type'} (P : type686 _86990) (Q : type686 _86990) : (term359 _86990 P Q) = (term360 _86990 P Q).
Proof. exact (@lem3331535 (_86990 -> Prop) P Q). Qed.
Lemma lem3331537 {_86990 : Type'} (s : type686 _86990) : (term361 _86990 s) = (term362 _86990 s).
Proof. exact (@lem3331536 _86990 (term363 _86990 s) (term364 _86990 s)). Qed.
Lemma lem3331538 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term365 _86990 s t) = (term350 _86990 s t).
Proof. exact (eq_refl (term365 _86990 s t)). Qed.
Lemma lem3331539 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3331540 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term366 _86990 s t) = (term352 _86990 s t).
Proof. exact (MK_COMB (@lem3331539) (@lem3331538 _86990 s t)). Qed.
Lemma lem3331541 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term367 _86990 s t) = (term355 _86990 s t).
Proof. exact (eq_refl (term367 _86990 s t)). Qed.
Lemma lem3331542 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term368 _86990 s t) = (term356 _86990 s t).
Proof. exact (MK_COMB (@lem3331540 _86990 s t) (@lem3331541 _86990 s t)). Qed.
Lemma lem3331543 {_86990 : Type'} (s : type686 _86990) : (term369 _86990 s) = (term357 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3331542 _86990 s t)). Qed.
Lemma lem3331544 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3331545 {_86990 : Type'} (s : type686 _86990) : (term361 _86990 s) = (term358 _86990 s).
Proof. exact (MK_COMB (@lem3331544 _86990) (@lem3331543 _86990 s)). Qed.
Lemma lem3331546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3331547 {_86990 : Type'} (s : type686 _86990) : (term370 _86990 s) = (term371 _86990 s).
Proof. exact (MK_COMB (@lem3331546) (@lem3331545 _86990 s)). Qed.
Lemma lem3331548 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term365 _86990 s t) = (term350 _86990 s t).
Proof. exact (eq_refl (term365 _86990 s t)). Qed.
Lemma lem3331549 {_86990 : Type'} (s : type686 _86990) : (term372 _86990 s) = (term363 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3331548 _86990 s t)). Qed.
Lemma lem3331550 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3331551 {_86990 : Type'} (s : type686 _86990) : (term373 _86990 s) = (term374 _86990 s).
Proof. exact (MK_COMB (@lem3331550 _86990) (@lem3331549 _86990 s)). Qed.
Lemma lem3331552 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3331553 {_86990 : Type'} (s : type686 _86990) : (term375 _86990 s) = (term376 _86990 s).
Proof. exact (MK_COMB (@lem3331552) (@lem3331551 _86990 s)). Qed.
Lemma lem3331554 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term367 _86990 s t) = (term355 _86990 s t).
Proof. exact (eq_refl (term367 _86990 s t)). Qed.
Lemma lem3331555 {_86990 : Type'} (s : type686 _86990) : (term377 _86990 s) = (term364 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3331554 _86990 s t)). Qed.
Lemma lem3331556 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3331557 {_86990 : Type'} (s : type686 _86990) : (term378 _86990 s) = (term379 _86990 s).
Proof. exact (MK_COMB (@lem3331556 _86990) (@lem3331555 _86990 s)). Qed.
Lemma lem3331558 {_86990 : Type'} (s : type686 _86990) : (term362 _86990 s) = (term380 _86990 s).
Proof. exact (MK_COMB (@lem3331553 _86990 s) (@lem3331557 _86990 s)). Qed.
Lemma lem3331559 {_86990 : Type'} (s : type686 _86990) : ((term361 _86990 s) = (term362 _86990 s)) = ((term358 _86990 s) = (term380 _86990 s)).
Proof. exact (MK_COMB (@lem3331547 _86990 s) (@lem3331558 _86990 s)). Qed.
Lemma lem3331560 {_86990 : Type'} (s : type686 _86990) : (term358 _86990 s) = (term380 _86990 s).
Proof. exact (EQ_MP (@lem3331559 _86990 s) (@lem3331537 _86990 s)). Qed.
Lemma lem3331953 {_86990 : Type'} (s : type686 _86990) : (term263 _86990 s) = (term380 _86990 s).
Proof. exact (TRANS (@lem3331533 _86990 s) (@lem3331560 _86990 s)). Qed.
Lemma lem3331954 {_86990 : Type'} : (term271 _86990) = (term381 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3331953 _86990 s)). Qed.
Lemma lem3331955 {_86990 : Type'} : (@ex ((_86990 -> Prop) -> Prop)) = (@ex ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3331956 {_86990 : Type'} : (term272 _86990) = (term382 _86990).
Proof. exact (MK_COMB (@lem3331955 _86990) (@lem3331954 _86990)). Qed.
Lemma lem3331958 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3331959 {_86990 : Type'} (P : type180 _86990) (Q : type180 _86990) : (term383 _86990 P Q) = (term384 _86990 P Q).
Proof. exact (@lem3331958 (type686 _86990) P Q). Qed.
Lemma lem3331960 {_86990 : Type'} : (term385 _86990) = (term386 _86990).
Proof. exact (@lem3331959 _86990 (term387 _86990) (term388 _86990)). Qed.
Lemma lem3331961 {_86990 : Type'} (s : type686 _86990) : (term389 _86990 s) = (term374 _86990 s).
Proof. exact (eq_refl (term389 _86990 s)). Qed.
Lemma lem3331962 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3331963 {_86990 : Type'} (s : type686 _86990) : (term390 _86990 s) = (term376 _86990 s).
Proof. exact (MK_COMB (@lem3331962) (@lem3331961 _86990 s)). Qed.
Lemma lem3331964 {_86990 : Type'} (s : type686 _86990) : (term391 _86990 s) = (term379 _86990 s).
Proof. exact (eq_refl (term391 _86990 s)). Qed.
Lemma lem3331965 {_86990 : Type'} (s : type686 _86990) : (term392 _86990 s) = (term380 _86990 s).
Proof. exact (MK_COMB (@lem3331963 _86990 s) (@lem3331964 _86990 s)). Qed.
Lemma lem3331966 {_86990 : Type'} : (term393 _86990) = (term381 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3331965 _86990 s)). Qed.
Lemma lem3331967 {_86990 : Type'} : (@ex ((_86990 -> Prop) -> Prop)) = (@ex ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3331968 {_86990 : Type'} : (term385 _86990) = (term382 _86990).
Proof. exact (MK_COMB (@lem3331967 _86990) (@lem3331966 _86990)). Qed.
Lemma lem3331969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3331970 {_86990 : Type'} : (term394 _86990) = (term395 _86990).
Proof. exact (MK_COMB (@lem3331969) (@lem3331968 _86990)). Qed.
Lemma lem3331971 {_86990 : Type'} (s : type686 _86990) : (term389 _86990 s) = (term374 _86990 s).
Proof. exact (eq_refl (term389 _86990 s)). Qed.
Lemma lem3331972 {_86990 : Type'} : (term396 _86990) = (term387 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3331971 _86990 s)). Qed.
Lemma lem3331973 {_86990 : Type'} : (@ex ((_86990 -> Prop) -> Prop)) = (@ex ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3331974 {_86990 : Type'} : (term397 _86990) = (term398 _86990).
Proof. exact (MK_COMB (@lem3331973 _86990) (@lem3331972 _86990)). Qed.
Lemma lem3331975 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3331976 {_86990 : Type'} : (term399 _86990) = (term400 _86990).
Proof. exact (MK_COMB (@lem3331975) (@lem3331974 _86990)). Qed.
Lemma lem3331977 {_86990 : Type'} (s : type686 _86990) : (term391 _86990 s) = (term379 _86990 s).
Proof. exact (eq_refl (term391 _86990 s)). Qed.
Lemma lem3331978 {_86990 : Type'} : (term401 _86990) = (term388 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3331977 _86990 s)). Qed.
Lemma lem3331979 {_86990 : Type'} : (@ex ((_86990 -> Prop) -> Prop)) = (@ex ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3331980 {_86990 : Type'} : (term402 _86990) = (term403 _86990).
Proof. exact (MK_COMB (@lem3331979 _86990) (@lem3331978 _86990)). Qed.
Lemma lem3331981 {_86990 : Type'} : (term386 _86990) = (term404 _86990).
Proof. exact (MK_COMB (@lem3331976 _86990) (@lem3331980 _86990)). Qed.
Lemma lem3331982 {_86990 : Type'} : ((term385 _86990) = (term386 _86990)) = ((term382 _86990) = (term404 _86990)).
Proof. exact (MK_COMB (@lem3331970 _86990) (@lem3331981 _86990)). Qed.
Lemma lem3331983 {_86990 : Type'} : (term382 _86990) = (term404 _86990).
Proof. exact (EQ_MP (@lem3331982 _86990) (@lem3331960 _86990)). Qed.
Lemma lem3332384 {_86990 : Type'} : (term272 _86990) = (term404 _86990).
Proof. exact (TRANS (@lem3331956 _86990) (@lem3331983 _86990)). Qed.
Lemma lem3332385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3332386 {_86990 : Type'} : (term332 _86990) = (term405 _86990).
Proof. exact (MK_COMB (@lem3332385) (@lem3332384 _86990)). Qed.
Lemma lem3332396 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3332397 {_87026 : Type'} (P : _87026 -> Prop) (Q : _87026 -> Prop) : (term335 _87026 P Q) = (term336 _87026 P Q).
Proof. exact (@lem3332396 _87026 P Q). Qed.
Lemma lem3332398 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term406 _87026 s t) = (term407 _87026 s t).
Proof. exact (@lem3332397 _87026 (term408 _87026 s t) (term409 _87026 s t)). Qed.
Lemma lem3332399 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term410 _87026 s t x) = (term304 _87026 s t x).
Proof. exact (eq_refl (term410 _87026 s t x)). Qed.
Lemma lem3332400 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3332401 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term411 _87026 s t x) = (term306 _87026 s t x).
Proof. exact (MK_COMB (@lem3332400) (@lem3332399 _87026 s t x)). Qed.
Lemma lem3332402 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term412 _87026 s t x) = (term301 _87026 s t x).
Proof. exact (eq_refl (term412 _87026 s t x)). Qed.
Lemma lem3332403 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term413 _87026 s t x) = (term308 _87026 s t x).
Proof. exact (MK_COMB (@lem3332401 _87026 s t x) (@lem3332402 _87026 s t x)). Qed.
Lemma lem3332404 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term414 _87026 s t) = (term315 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3332403 _87026 s t x)). Qed.
Lemma lem3332405 {_87026 : Type'} : (@ex _87026) = (@ex _87026).
Proof. exact (eq_refl (@ex _87026)). Qed.
Lemma lem3332406 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term406 _87026 s t) = (term316 _87026 s t).
Proof. exact (MK_COMB (@lem3332405 _87026) (@lem3332404 _87026 s t)). Qed.
Lemma lem3332407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3332408 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term415 _87026 s t) = (term416 _87026 s t).
Proof. exact (MK_COMB (@lem3332407) (@lem3332406 _87026 s t)). Qed.
Lemma lem3332409 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term410 _87026 s t x) = (term304 _87026 s t x).
Proof. exact (eq_refl (term410 _87026 s t x)). Qed.
Lemma lem3332410 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term417 _87026 s t) = (term408 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3332409 _87026 s t x)). Qed.
Lemma lem3332411 {_87026 : Type'} : (@ex _87026) = (@ex _87026).
Proof. exact (eq_refl (@ex _87026)). Qed.
Lemma lem3332412 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term418 _87026 s t) = (term419 _87026 s t).
Proof. exact (MK_COMB (@lem3332411 _87026) (@lem3332410 _87026 s t)). Qed.
Lemma lem3332413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3332414 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term420 _87026 s t) = (term421 _87026 s t).
Proof. exact (MK_COMB (@lem3332413) (@lem3332412 _87026 s t)). Qed.
Lemma lem3332415 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term412 _87026 s t x) = (term301 _87026 s t x).
Proof. exact (eq_refl (term412 _87026 s t x)). Qed.
Lemma lem3332416 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term422 _87026 s t) = (term409 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3332415 _87026 s t x)). Qed.
Lemma lem3332417 {_87026 : Type'} : (@ex _87026) = (@ex _87026).
Proof. exact (eq_refl (@ex _87026)). Qed.
Lemma lem3332418 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term423 _87026 s t) = (term424 _87026 s t).
Proof. exact (MK_COMB (@lem3332417 _87026) (@lem3332416 _87026 s t)). Qed.
Lemma lem3332419 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term407 _87026 s t) = (term425 _87026 s t).
Proof. exact (MK_COMB (@lem3332414 _87026 s t) (@lem3332418 _87026 s t)). Qed.
Lemma lem3332420 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : ((term406 _87026 s t) = (term407 _87026 s t)) = ((term316 _87026 s t) = (term425 _87026 s t)).
Proof. exact (MK_COMB (@lem3332408 _87026 s t) (@lem3332419 _87026 s t)). Qed.
Lemma lem3332421 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term316 _87026 s t) = (term425 _87026 s t).
Proof. exact (EQ_MP (@lem3332420 _87026 s t) (@lem3332398 _87026 s t)). Qed.
Lemma lem3332806 {_87026 : Type'} (s : type686 _87026) : (term322 _87026 s) = (term426 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3332421 _87026 s t)). Qed.
Lemma lem3332807 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3332808 {_87026 : Type'} (s : type686 _87026) : (term323 _87026 s) = (term427 _87026 s).
Proof. exact (MK_COMB (@lem3332807 _87026) (@lem3332806 _87026 s)). Qed.
Lemma lem3332810 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3332811 {_87026 : Type'} (P : type686 _87026) (Q : type686 _87026) : (term359 _87026 P Q) = (term360 _87026 P Q).
Proof. exact (@lem3332810 (_87026 -> Prop) P Q). Qed.
Lemma lem3332812 {_87026 : Type'} (s : type686 _87026) : (term428 _87026 s) = (term429 _87026 s).
Proof. exact (@lem3332811 _87026 (term430 _87026 s) (term431 _87026 s)). Qed.
Lemma lem3332813 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term432 _87026 s t) = (term419 _87026 s t).
Proof. exact (eq_refl (term432 _87026 s t)). Qed.
Lemma lem3332814 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3332815 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term433 _87026 s t) = (term421 _87026 s t).
Proof. exact (MK_COMB (@lem3332814) (@lem3332813 _87026 s t)). Qed.
Lemma lem3332816 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term434 _87026 s t) = (term424 _87026 s t).
Proof. exact (eq_refl (term434 _87026 s t)). Qed.
Lemma lem3332817 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term435 _87026 s t) = (term425 _87026 s t).
Proof. exact (MK_COMB (@lem3332815 _87026 s t) (@lem3332816 _87026 s t)). Qed.
Lemma lem3332818 {_87026 : Type'} (s : type686 _87026) : (term436 _87026 s) = (term426 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3332817 _87026 s t)). Qed.
Lemma lem3332819 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3332820 {_87026 : Type'} (s : type686 _87026) : (term428 _87026 s) = (term427 _87026 s).
Proof. exact (MK_COMB (@lem3332819 _87026) (@lem3332818 _87026 s)). Qed.
Lemma lem3332821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3332822 {_87026 : Type'} (s : type686 _87026) : (term437 _87026 s) = (term438 _87026 s).
Proof. exact (MK_COMB (@lem3332821) (@lem3332820 _87026 s)). Qed.
Lemma lem3332823 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term432 _87026 s t) = (term419 _87026 s t).
Proof. exact (eq_refl (term432 _87026 s t)). Qed.
Lemma lem3332824 {_87026 : Type'} (s : type686 _87026) : (term439 _87026 s) = (term430 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3332823 _87026 s t)). Qed.
Lemma lem3332825 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3332826 {_87026 : Type'} (s : type686 _87026) : (term440 _87026 s) = (term441 _87026 s).
Proof. exact (MK_COMB (@lem3332825 _87026) (@lem3332824 _87026 s)). Qed.
Lemma lem3332827 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3332828 {_87026 : Type'} (s : type686 _87026) : (term442 _87026 s) = (term443 _87026 s).
Proof. exact (MK_COMB (@lem3332827) (@lem3332826 _87026 s)). Qed.
Lemma lem3332829 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term434 _87026 s t) = (term424 _87026 s t).
Proof. exact (eq_refl (term434 _87026 s t)). Qed.
Lemma lem3332830 {_87026 : Type'} (s : type686 _87026) : (term444 _87026 s) = (term431 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3332829 _87026 s t)). Qed.
Lemma lem3332831 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3332832 {_87026 : Type'} (s : type686 _87026) : (term445 _87026 s) = (term446 _87026 s).
Proof. exact (MK_COMB (@lem3332831 _87026) (@lem3332830 _87026 s)). Qed.
Lemma lem3332833 {_87026 : Type'} (s : type686 _87026) : (term429 _87026 s) = (term447 _87026 s).
Proof. exact (MK_COMB (@lem3332828 _87026 s) (@lem3332832 _87026 s)). Qed.
Lemma lem3332834 {_87026 : Type'} (s : type686 _87026) : ((term428 _87026 s) = (term429 _87026 s)) = ((term427 _87026 s) = (term447 _87026 s)).
Proof. exact (MK_COMB (@lem3332822 _87026 s) (@lem3332833 _87026 s)). Qed.
Lemma lem3332835 {_87026 : Type'} (s : type686 _87026) : (term427 _87026 s) = (term447 _87026 s).
Proof. exact (EQ_MP (@lem3332834 _87026 s) (@lem3332812 _87026 s)). Qed.
Lemma lem3333228 {_87026 : Type'} (s : type686 _87026) : (term323 _87026 s) = (term447 _87026 s).
Proof. exact (TRANS (@lem3332808 _87026 s) (@lem3332835 _87026 s)). Qed.
Lemma lem3333229 {_87026 : Type'} : (term329 _87026) = (term448 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3333228 _87026 s)). Qed.
Lemma lem3333230 {_87026 : Type'} : (@ex ((_87026 -> Prop) -> Prop)) = (@ex ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3333231 {_87026 : Type'} : (term330 _87026) = (term449 _87026).
Proof. exact (MK_COMB (@lem3333230 _87026) (@lem3333229 _87026)). Qed.
Lemma lem3333233 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3333234 {_87026 : Type'} (P : type180 _87026) (Q : type180 _87026) : (term383 _87026 P Q) = (term384 _87026 P Q).
Proof. exact (@lem3333233 (type686 _87026) P Q). Qed.
Lemma lem3333235 {_87026 : Type'} : (term450 _87026) = (term451 _87026).
Proof. exact (@lem3333234 _87026 (term452 _87026) (term453 _87026)). Qed.
Lemma lem3333236 {_87026 : Type'} (s : type686 _87026) : (term454 _87026 s) = (term441 _87026 s).
Proof. exact (eq_refl (term454 _87026 s)). Qed.
Lemma lem3333237 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3333238 {_87026 : Type'} (s : type686 _87026) : (term455 _87026 s) = (term443 _87026 s).
Proof. exact (MK_COMB (@lem3333237) (@lem3333236 _87026 s)). Qed.
Lemma lem3333239 {_87026 : Type'} (s : type686 _87026) : (term456 _87026 s) = (term446 _87026 s).
Proof. exact (eq_refl (term456 _87026 s)). Qed.
Lemma lem3333240 {_87026 : Type'} (s : type686 _87026) : (term457 _87026 s) = (term447 _87026 s).
Proof. exact (MK_COMB (@lem3333238 _87026 s) (@lem3333239 _87026 s)). Qed.
Lemma lem3333241 {_87026 : Type'} : (term458 _87026) = (term448 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3333240 _87026 s)). Qed.
Lemma lem3333242 {_87026 : Type'} : (@ex ((_87026 -> Prop) -> Prop)) = (@ex ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3333243 {_87026 : Type'} : (term450 _87026) = (term449 _87026).
Proof. exact (MK_COMB (@lem3333242 _87026) (@lem3333241 _87026)). Qed.
Lemma lem3333244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3333245 {_87026 : Type'} : (term459 _87026) = (term460 _87026).
Proof. exact (MK_COMB (@lem3333244) (@lem3333243 _87026)). Qed.
Lemma lem3333246 {_87026 : Type'} (s : type686 _87026) : (term454 _87026 s) = (term441 _87026 s).
Proof. exact (eq_refl (term454 _87026 s)). Qed.
Lemma lem3333247 {_87026 : Type'} : (term461 _87026) = (term452 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3333246 _87026 s)). Qed.
Lemma lem3333248 {_87026 : Type'} : (@ex ((_87026 -> Prop) -> Prop)) = (@ex ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3333249 {_87026 : Type'} : (term462 _87026) = (term463 _87026).
Proof. exact (MK_COMB (@lem3333248 _87026) (@lem3333247 _87026)). Qed.
Lemma lem3333250 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3333251 {_87026 : Type'} : (term464 _87026) = (term465 _87026).
Proof. exact (MK_COMB (@lem3333250) (@lem3333249 _87026)). Qed.
Lemma lem3333252 {_87026 : Type'} (s : type686 _87026) : (term456 _87026 s) = (term446 _87026 s).
Proof. exact (eq_refl (term456 _87026 s)). Qed.
Lemma lem3333253 {_87026 : Type'} : (term466 _87026) = (term453 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3333252 _87026 s)). Qed.
Lemma lem3333254 {_87026 : Type'} : (@ex ((_87026 -> Prop) -> Prop)) = (@ex ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3333255 {_87026 : Type'} : (term467 _87026) = (term468 _87026).
Proof. exact (MK_COMB (@lem3333254 _87026) (@lem3333253 _87026)). Qed.
Lemma lem3333256 {_87026 : Type'} : (term451 _87026) = (term469 _87026).
Proof. exact (MK_COMB (@lem3333251 _87026) (@lem3333255 _87026)). Qed.
Lemma lem3333257 {_87026 : Type'} : ((term450 _87026) = (term451 _87026)) = ((term449 _87026) = (term469 _87026)).
Proof. exact (MK_COMB (@lem3333245 _87026) (@lem3333256 _87026)). Qed.
Lemma lem3333258 {_87026 : Type'} : (term449 _87026) = (term469 _87026).
Proof. exact (EQ_MP (@lem3333257 _87026) (@lem3333235 _87026)). Qed.
Lemma lem3333659 {_87026 : Type'} : (term330 _87026) = (term469 _87026).
Proof. exact (TRANS (@lem3333231 _87026) (@lem3333258 _87026)). Qed.
Lemma lem3333660 {_86990 _87026 : Type'} : (term334 _86990 _87026) = (term470 _86990 _87026).
Proof. exact (MK_COMB (@lem3332386 _86990) (@lem3333659 _87026)). Qed.
Lemma lem3333662 {A : Type'} (P : A -> Prop) (Q : Prop) : (term471 A P Q) = (term472 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3333663 {_86990 : Type'} (P : type686 _86990) (Q : Prop) : (term473 _86990 P Q) = (term474 _86990 P Q).
Proof. exact (@lem3333662 (_86990 -> Prop) P Q). Qed.
Lemma lem3333664 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term475 _86990 s x t) = (term476 _86990 s x t).
Proof. exact (@lem3333663 _86990 (term195 _86990 s x) (@IN _86990 x t)). Qed.
Lemma lem3333665 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term202 _86990 s x t) = (term194 _86990 s x t).
Proof. exact (eq_refl (term202 _86990 s x t)). Qed.
Lemma lem3333666 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term477 _86990 s x) = (term195 _86990 s x).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3333665 _86990 s x t)). Qed.
Lemma lem3333667 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333668 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term478 _86990 s x) = (term24 _86990 s x).
Proof. exact (MK_COMB (@lem3333667 _86990) (@lem3333666 _86990 s x)). Qed.
Lemma lem3333669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3333670 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term479 _86990 s x) = (term58 _86990 s x).
Proof. exact (MK_COMB (@lem3333669) (@lem3333668 _86990 s x)). Qed.
Lemma lem3333671 {_86990 : Type'} (x : _86990) (t : _86990 -> Prop) : (@IN _86990 x t) = (@IN _86990 x t).
Proof. exact (eq_refl (@IN _86990 x t)). Qed.
Lemma lem3333672 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term475 _86990 s x t) = (term59 _86990 s x t).
Proof. exact (MK_COMB (@lem3333670 _86990 s x) (@lem3333671 _86990 x t)). Qed.
Lemma lem3333673 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3333674 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term480 _86990 s x t) = (term61 _86990 s x t).
Proof. exact (MK_COMB (@lem3333673) (@lem3333672 _86990 s x t)). Qed.
Lemma lem3333675 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t' : _86990 -> Prop) : (term202 _86990 s x t') = (term194 _86990 s x t').
Proof. exact (eq_refl (term202 _86990 s x t')). Qed.
Lemma lem3333676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3333677 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t' : _86990 -> Prop) : (term481 _86990 s x t') = (term482 _86990 s x t').
Proof. exact (MK_COMB (@lem3333676) (@lem3333675 _86990 s x t')). Qed.
Lemma lem3333678 {_86990 : Type'} (x : _86990) (t : _86990 -> Prop) : (@IN _86990 x t) = (@IN _86990 x t).
Proof. exact (eq_refl (@IN _86990 x t)). Qed.
Lemma lem3333679 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term483 _86990 s t' x t) = (term484 _86990 s t' x t).
Proof. exact (MK_COMB (@lem3333677 _86990 s x t') (@lem3333678 _86990 x t)). Qed.
Lemma lem3333680 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term485 _86990 s x t) = (term486 _86990 s x t).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3333679 _86990 s t' x t)). Qed.
Lemma lem3333681 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333682 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term476 _86990 s x t) = (term487 _86990 s x t).
Proof. exact (MK_COMB (@lem3333681 _86990) (@lem3333680 _86990 s x t)). Qed.
Lemma lem3333683 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : ((term475 _86990 s x t) = (term476 _86990 s x t)) = ((term59 _86990 s x t) = (term487 _86990 s x t)).
Proof. exact (MK_COMB (@lem3333674 _86990 s x t) (@lem3333682 _86990 s x t)). Qed.
Lemma lem3333684 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term59 _86990 s x t) = (term487 _86990 s x t).
Proof. exact (EQ_MP (@lem3333683 _86990 s x t) (@lem3333664 _86990 s x t)). Qed.
Lemma lem3333685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3333686 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term238 _86990 s x t) = (term488 _86990 s x t).
Proof. exact (MK_COMB (@lem3333685) (@lem3333684 _86990 s x t)). Qed.
Lemma lem3333687 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term233 _86990 s t x) = (term233 _86990 s t x).
Proof. exact (eq_refl (term233 _86990 s t x)). Qed.
Lemma lem3333688 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term240 _86990 s t x) = (term489 _86990 s t x).
Proof. exact (MK_COMB (@lem3333686 _86990 s x t) (@lem3333687 _86990 s t x)). Qed.
Lemma lem3333690 {A : Type'} (P : A -> Prop) (Q : Prop) : (term471 A P Q) = (term472 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3333691 {_86990 : Type'} (P : type686 _86990) (Q : Prop) : (term473 _86990 P Q) = (term474 _86990 P Q).
Proof. exact (@lem3333690 (_86990 -> Prop) P Q). Qed.
Lemma lem3333692 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term490 _86990 s t x) = (term491 _86990 s t x).
Proof. exact (@lem3333691 _86990 (term486 _86990 s x t) (term233 _86990 s t x)). Qed.
Lemma lem3333693 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term492 _86990 s x t t') = (term484 _86990 s t' x t).
Proof. exact (eq_refl (term492 _86990 s x t t')). Qed.
Lemma lem3333694 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term493 _86990 s x t) = (term486 _86990 s x t).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3333693 _86990 s t' x t)). Qed.
Lemma lem3333695 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333696 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term494 _86990 s x t) = (term487 _86990 s x t).
Proof. exact (MK_COMB (@lem3333695 _86990) (@lem3333694 _86990 s x t)). Qed.
Lemma lem3333697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3333698 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term495 _86990 s x t) = (term488 _86990 s x t).
Proof. exact (MK_COMB (@lem3333697) (@lem3333696 _86990 s x t)). Qed.
Lemma lem3333699 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term233 _86990 s t x) = (term233 _86990 s t x).
Proof. exact (eq_refl (term233 _86990 s t x)). Qed.
Lemma lem3333700 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term490 _86990 s t x) = (term489 _86990 s t x).
Proof. exact (MK_COMB (@lem3333698 _86990 s x t) (@lem3333699 _86990 s t x)). Qed.
Lemma lem3333701 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3333702 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term496 _86990 s t x) = (term497 _86990 s t x).
Proof. exact (MK_COMB (@lem3333701) (@lem3333700 _86990 s t x)). Qed.
Lemma lem3333703 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term492 _86990 s x t t') = (term484 _86990 s t' x t).
Proof. exact (eq_refl (term492 _86990 s x t t')). Qed.
Lemma lem3333704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3333705 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term498 _86990 s x t t') = (term499 _86990 s t' x t).
Proof. exact (MK_COMB (@lem3333704) (@lem3333703 _86990 s t' x t)). Qed.
Lemma lem3333706 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term233 _86990 s t x) = (term233 _86990 s t x).
Proof. exact (eq_refl (term233 _86990 s t x)). Qed.
Lemma lem3333707 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term500 _86990 t' s t x) = (term501 _86990 t' s t x).
Proof. exact (MK_COMB (@lem3333705 _86990 s t' x t) (@lem3333706 _86990 s t x)). Qed.
Lemma lem3333708 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term502 _86990 s t x) = (term503 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3333707 _86990 t' s t x)). Qed.
Lemma lem3333709 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333710 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term491 _86990 s t x) = (term504 _86990 s t x).
Proof. exact (MK_COMB (@lem3333709 _86990) (@lem3333708 _86990 s t x)). Qed.
Lemma lem3333711 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : ((term490 _86990 s t x) = (term491 _86990 s t x)) = ((term489 _86990 s t x) = (term504 _86990 s t x)).
Proof. exact (MK_COMB (@lem3333702 _86990 s t x) (@lem3333710 _86990 s t x)). Qed.
Lemma lem3333712 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term489 _86990 s t x) = (term504 _86990 s t x).
Proof. exact (EQ_MP (@lem3333711 _86990 s t x) (@lem3333692 _86990 s t x)). Qed.
Lemma lem3333713 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term240 _86990 s t x) = (term504 _86990 s t x).
Proof. exact (TRANS (@lem3333688 _86990 s t x) (@lem3333712 _86990 s t x)). Qed.
Lemma lem3333714 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term339 _86990 s t) = (term505 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3333713 _86990 s t x)). Qed.
Lemma lem3333715 {_86990 : Type'} : (@ex _86990) = (@ex _86990).
Proof. exact (eq_refl (@ex _86990)). Qed.
Lemma lem3333716 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term350 _86990 s t) = (term506 _86990 s t).
Proof. exact (MK_COMB (@lem3333715 _86990) (@lem3333714 _86990 s t)). Qed.
Lemma lem3333717 {_86990 : Type'} (s : type686 _86990) : (term363 _86990 s) = (term507 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3333716 _86990 s t)). Qed.
Lemma lem3333718 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333719 {_86990 : Type'} (s : type686 _86990) : (term374 _86990 s) = (term508 _86990 s).
Proof. exact (MK_COMB (@lem3333718 _86990) (@lem3333717 _86990 s)). Qed.
Lemma lem3333720 {_86990 : Type'} : (term387 _86990) = (term509 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3333719 _86990 s)). Qed.
Lemma lem3333721 {_86990 : Type'} : (@ex ((_86990 -> Prop) -> Prop)) = (@ex ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3333722 {_86990 : Type'} : (term398 _86990) = (term510 _86990).
Proof. exact (MK_COMB (@lem3333721 _86990) (@lem3333720 _86990)). Qed.
Lemma lem3333723 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3333724 {_86990 : Type'} : (term400 _86990) = (term511 _86990).
Proof. exact (MK_COMB (@lem3333723) (@lem3333722 _86990)). Qed.
Lemma lem3333726 {A : Type'} (P : A -> Prop) (Q : Prop) : (term471 A P Q) = (term472 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3333727 {_86990 : Type'} (P : type686 _86990) (Q : Prop) : (term473 _86990 P Q) = (term474 _86990 P Q).
Proof. exact (@lem3333726 (_86990 -> Prop) P Q). Qed.
Lemma lem3333728 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term512 _86990 s t x t') = (term513 _86990 s t x t').
Proof. exact (@lem3333727 _86990 (term101 _86990 s t' t) (@IN _86990 x t')). Qed.
Lemma lem3333729 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term217 _86990 s t' t x) = (term99 _86990 s t' x t).
Proof. exact (eq_refl (term217 _86990 s t' t x)). Qed.
Lemma lem3333730 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term514 _86990 s t' t) = (term101 _86990 s t' t).
Proof. exact (fun_ext (fun x : _86990 -> Prop => @lem3333729 _86990 s t' x t)). Qed.
Lemma lem3333731 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333732 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term515 _86990 s t' t) = (term102 _86990 s t' t).
Proof. exact (MK_COMB (@lem3333731 _86990) (@lem3333730 _86990 s t' t)). Qed.
Lemma lem3333733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3333734 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term516 _86990 s t' t) = (term104 _86990 s t' t).
Proof. exact (MK_COMB (@lem3333733) (@lem3333732 _86990 s t' t)). Qed.
Lemma lem3333735 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (@IN _86990 x t') = (@IN _86990 x t').
Proof. exact (eq_refl (@IN _86990 x t')). Qed.
Lemma lem3333736 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term512 _86990 s t x t') = (term106 _86990 s t x t').
Proof. exact (MK_COMB (@lem3333734 _86990 s t' t) (@lem3333735 _86990 x t')). Qed.
Lemma lem3333737 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3333738 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term517 _86990 s t x t') = (term518 _86990 s t x t').
Proof. exact (MK_COMB (@lem3333737) (@lem3333736 _86990 s t x t')). Qed.
Lemma lem3333739 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term217 _86990 s t' t x) = (term99 _86990 s t' x t).
Proof. exact (eq_refl (term217 _86990 s t' t x)). Qed.
Lemma lem3333740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3333741 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term519 _86990 s t' t x) = (term520 _86990 s t' x t).
Proof. exact (MK_COMB (@lem3333740) (@lem3333739 _86990 s t' x t)). Qed.
Lemma lem3333742 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (@IN _86990 x t') = (@IN _86990 x t').
Proof. exact (eq_refl (@IN _86990 x t')). Qed.
Lemma lem3333743 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term521 _86990 s t x x' t') = (term522 _86990 s x t x' t').
Proof. exact (MK_COMB (@lem3333741 _86990 s t' x t) (@lem3333742 _86990 x' t')). Qed.
Lemma lem3333744 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term523 _86990 s t x t') = (term524 _86990 s t x t').
Proof. exact (fun_ext (fun x' : _86990 -> Prop => @lem3333743 _86990 s x' t x t')). Qed.
Lemma lem3333745 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333746 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term513 _86990 s t x t') = (term525 _86990 s t x t').
Proof. exact (MK_COMB (@lem3333745 _86990) (@lem3333744 _86990 s t x t')). Qed.
Lemma lem3333747 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : ((term512 _86990 s t x t') = (term513 _86990 s t x t')) = ((term106 _86990 s t x t') = (term525 _86990 s t x t')).
Proof. exact (MK_COMB (@lem3333738 _86990 s t x t') (@lem3333746 _86990 s t x t')). Qed.
Lemma lem3333748 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term106 _86990 s t x t') = (term525 _86990 s t x t').
Proof. exact (EQ_MP (@lem3333747 _86990 s t x t') (@lem3333728 _86990 s t x t')). Qed.
Lemma lem3333749 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term108 _86990 s t x) = (term526 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3333748 _86990 s t x t')). Qed.
Lemma lem3333750 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333751 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term109 _86990 s t x) = (term527 _86990 s t x).
Proof. exact (MK_COMB (@lem3333750 _86990) (@lem3333749 _86990 s t x)). Qed.
Lemma lem3333752 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term235 _86990 s x t) = (term235 _86990 s x t).
Proof. exact (eq_refl (term235 _86990 s x t)). Qed.
Lemma lem3333753 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term237 _86990 s t x) = (term528 _86990 s t x).
Proof. exact (MK_COMB (@lem3333752 _86990 s x t) (@lem3333751 _86990 s t x)). Qed.
Lemma lem3333755 {A : Type'} (P : Prop) (Q : A -> Prop) : (term529 A P Q) = (term530 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3333756 {_86990 : Type'} (P : Prop) (Q : type686 _86990) : (term531 _86990 P Q) = (term532 _86990 P Q).
Proof. exact (@lem3333755 (_86990 -> Prop) P Q). Qed.
Lemma lem3333757 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term533 _86990 s t x) = (term534 _86990 s t x).
Proof. exact (@lem3333756 _86990 (term211 _86990 s x t) (term526 _86990 s t x)). Qed.
Lemma lem3333758 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term535 _86990 s t x t') = (term525 _86990 s t x t').
Proof. exact (eq_refl (term535 _86990 s t x t')). Qed.
Lemma lem3333759 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term536 _86990 s t x) = (term526 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3333758 _86990 s t x t')). Qed.
Lemma lem3333760 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333761 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term537 _86990 s t x) = (term527 _86990 s t x).
Proof. exact (MK_COMB (@lem3333760 _86990) (@lem3333759 _86990 s t x)). Qed.
Lemma lem3333762 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term235 _86990 s x t) = (term235 _86990 s x t).
Proof. exact (eq_refl (term235 _86990 s x t)). Qed.
Lemma lem3333763 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term533 _86990 s t x) = (term528 _86990 s t x).
Proof. exact (MK_COMB (@lem3333762 _86990 s x t) (@lem3333761 _86990 s t x)). Qed.
Lemma lem3333764 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3333765 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term538 _86990 s t x) = (term539 _86990 s t x).
Proof. exact (MK_COMB (@lem3333764) (@lem3333763 _86990 s t x)). Qed.
Lemma lem3333766 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term535 _86990 s t x t') = (term525 _86990 s t x t').
Proof. exact (eq_refl (term535 _86990 s t x t')). Qed.
Lemma lem3333767 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term235 _86990 s x t) = (term235 _86990 s x t).
Proof. exact (eq_refl (term235 _86990 s x t)). Qed.
Lemma lem3333768 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term540 _86990 s t x t') = (term541 _86990 s t x t').
Proof. exact (MK_COMB (@lem3333767 _86990 s x t) (@lem3333766 _86990 s t x t')). Qed.
Lemma lem3333769 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term542 _86990 s t x) = (term543 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3333768 _86990 s t x t')). Qed.
Lemma lem3333770 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333771 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term534 _86990 s t x) = (term544 _86990 s t x).
Proof. exact (MK_COMB (@lem3333770 _86990) (@lem3333769 _86990 s t x)). Qed.
Lemma lem3333772 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : ((term533 _86990 s t x) = (term534 _86990 s t x)) = ((term528 _86990 s t x) = (term544 _86990 s t x)).
Proof. exact (MK_COMB (@lem3333765 _86990 s t x) (@lem3333771 _86990 s t x)). Qed.
Lemma lem3333773 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term528 _86990 s t x) = (term544 _86990 s t x).
Proof. exact (EQ_MP (@lem3333772 _86990 s t x) (@lem3333757 _86990 s t x)). Qed.
Lemma lem3333775 {A : Type'} (P : Prop) (Q : A -> Prop) : (term529 A P Q) = (term530 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3333776 {_86990 : Type'} (P : Prop) (Q : type686 _86990) : (term531 _86990 P Q) = (term532 _86990 P Q).
Proof. exact (@lem3333775 (_86990 -> Prop) P Q). Qed.
Lemma lem3333777 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term545 _86990 s t x t') = (term546 _86990 s t x t').
Proof. exact (@lem3333776 _86990 (term211 _86990 s x t) (term524 _86990 s t x t')). Qed.
Lemma lem3333778 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term547 _86990 s t x' t' x) = (term522 _86990 s x t x' t').
Proof. exact (eq_refl (term547 _86990 s t x' t' x)). Qed.
Lemma lem3333779 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term548 _86990 s t x t') = (term524 _86990 s t x t').
Proof. exact (fun_ext (fun x' : _86990 -> Prop => @lem3333778 _86990 s x' t x t')). Qed.
Lemma lem3333780 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333781 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term549 _86990 s t x t') = (term525 _86990 s t x t').
Proof. exact (MK_COMB (@lem3333780 _86990) (@lem3333779 _86990 s t x t')). Qed.
Lemma lem3333782 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term235 _86990 s x t) = (term235 _86990 s x t).
Proof. exact (eq_refl (term235 _86990 s x t)). Qed.
Lemma lem3333783 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term545 _86990 s t x t') = (term541 _86990 s t x t').
Proof. exact (MK_COMB (@lem3333782 _86990 s x t) (@lem3333781 _86990 s t x t')). Qed.
Lemma lem3333784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3333785 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term550 _86990 s t x t') = (term551 _86990 s t x t').
Proof. exact (MK_COMB (@lem3333784) (@lem3333783 _86990 s t x t')). Qed.
Lemma lem3333786 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term547 _86990 s t x' t' x) = (term522 _86990 s x t x' t').
Proof. exact (eq_refl (term547 _86990 s t x' t' x)). Qed.
Lemma lem3333787 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term235 _86990 s x t) = (term235 _86990 s x t).
Proof. exact (eq_refl (term235 _86990 s x t)). Qed.
Lemma lem3333788 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term552 _86990 s t x' t' x) = (term553 _86990 s x t x' t').
Proof. exact (MK_COMB (@lem3333787 _86990 s x' t) (@lem3333786 _86990 s x t x' t')). Qed.
Lemma lem3333789 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term554 _86990 s t x t') = (term555 _86990 s t x t').
Proof. exact (fun_ext (fun x' : _86990 -> Prop => @lem3333788 _86990 s x' t x t')). Qed.
Lemma lem3333790 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333791 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term546 _86990 s t x t') = (term556 _86990 s t x t').
Proof. exact (MK_COMB (@lem3333790 _86990) (@lem3333789 _86990 s t x t')). Qed.
Lemma lem3333792 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : ((term545 _86990 s t x t') = (term546 _86990 s t x t')) = ((term541 _86990 s t x t') = (term556 _86990 s t x t')).
Proof. exact (MK_COMB (@lem3333785 _86990 s t x t') (@lem3333791 _86990 s t x t')). Qed.
Lemma lem3333793 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term541 _86990 s t x t') = (term556 _86990 s t x t').
Proof. exact (EQ_MP (@lem3333792 _86990 s t x t') (@lem3333777 _86990 s t x t')). Qed.
Lemma lem3333794 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term543 _86990 s t x) = (term557 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3333793 _86990 s t x t')). Qed.
Lemma lem3333795 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333796 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term544 _86990 s t x) = (term558 _86990 s t x).
Proof. exact (MK_COMB (@lem3333795 _86990) (@lem3333794 _86990 s t x)). Qed.
Lemma lem3333797 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term528 _86990 s t x) = (term558 _86990 s t x).
Proof. exact (TRANS (@lem3333773 _86990 s t x) (@lem3333796 _86990 s t x)). Qed.
Lemma lem3333798 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term237 _86990 s t x) = (term558 _86990 s t x).
Proof. exact (TRANS (@lem3333753 _86990 s t x) (@lem3333797 _86990 s t x)). Qed.
Lemma lem3333799 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term340 _86990 s t) = (term559 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3333798 _86990 s t x)). Qed.
Lemma lem3333800 {_86990 : Type'} : (@ex _86990) = (@ex _86990).
Proof. exact (eq_refl (@ex _86990)). Qed.
Lemma lem3333801 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term355 _86990 s t) = (term560 _86990 s t).
Proof. exact (MK_COMB (@lem3333800 _86990) (@lem3333799 _86990 s t)). Qed.
Lemma lem3333802 {_86990 : Type'} (s : type686 _86990) : (term364 _86990 s) = (term561 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3333801 _86990 s t)). Qed.
Lemma lem3333803 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333804 {_86990 : Type'} (s : type686 _86990) : (term379 _86990 s) = (term562 _86990 s).
Proof. exact (MK_COMB (@lem3333803 _86990) (@lem3333802 _86990 s)). Qed.
Lemma lem3333805 {_86990 : Type'} : (term388 _86990) = (term563 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3333804 _86990 s)). Qed.
Lemma lem3333806 {_86990 : Type'} : (@ex ((_86990 -> Prop) -> Prop)) = (@ex ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3333807 {_86990 : Type'} : (term403 _86990) = (term564 _86990).
Proof. exact (MK_COMB (@lem3333806 _86990) (@lem3333805 _86990)). Qed.
Lemma lem3333808 {_86990 : Type'} : (term404 _86990) = (term565 _86990).
Proof. exact (MK_COMB (@lem3333724 _86990) (@lem3333807 _86990)). Qed.
Lemma lem3333810 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term336 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3333811 {_86990 : Type'} (P : type180 _86990) (Q : type180 _86990) : (term384 _86990 P Q) = (term383 _86990 P Q).
Proof. exact (@lem3333810 (type686 _86990) P Q). Qed.
Lemma lem3333812 {_86990 : Type'} : (term566 _86990) = (term567 _86990).
Proof. exact (@lem3333811 _86990 (term509 _86990) (term563 _86990)). Qed.
Lemma lem3333813 {_86990 : Type'} (s : type686 _86990) : (term568 _86990 s) = (term508 _86990 s).
Proof. exact (eq_refl (term568 _86990 s)). Qed.
Lemma lem3333814 {_86990 : Type'} : (term569 _86990) = (term509 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3333813 _86990 s)). Qed.
Lemma lem3333815 {_86990 : Type'} : (@ex ((_86990 -> Prop) -> Prop)) = (@ex ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3333816 {_86990 : Type'} : (term570 _86990) = (term510 _86990).
Proof. exact (MK_COMB (@lem3333815 _86990) (@lem3333814 _86990)). Qed.
Lemma lem3333817 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3333818 {_86990 : Type'} : (term571 _86990) = (term511 _86990).
Proof. exact (MK_COMB (@lem3333817) (@lem3333816 _86990)). Qed.
Lemma lem3333819 {_86990 : Type'} (s : type686 _86990) : (term572 _86990 s) = (term562 _86990 s).
Proof. exact (eq_refl (term572 _86990 s)). Qed.
Lemma lem3333820 {_86990 : Type'} : (term573 _86990) = (term563 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3333819 _86990 s)). Qed.
Lemma lem3333821 {_86990 : Type'} : (@ex ((_86990 -> Prop) -> Prop)) = (@ex ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3333822 {_86990 : Type'} : (term574 _86990) = (term564 _86990).
Proof. exact (MK_COMB (@lem3333821 _86990) (@lem3333820 _86990)). Qed.
Lemma lem3333823 {_86990 : Type'} : (term566 _86990) = (term565 _86990).
Proof. exact (MK_COMB (@lem3333818 _86990) (@lem3333822 _86990)). Qed.
Lemma lem3333824 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3333825 {_86990 : Type'} : (term575 _86990) = (term576 _86990).
Proof. exact (MK_COMB (@lem3333824) (@lem3333823 _86990)). Qed.
Lemma lem3333826 {_86990 : Type'} (s : type686 _86990) : (term568 _86990 s) = (term508 _86990 s).
Proof. exact (eq_refl (term568 _86990 s)). Qed.
Lemma lem3333827 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3333828 {_86990 : Type'} (s : type686 _86990) : (term577 _86990 s) = (term578 _86990 s).
Proof. exact (MK_COMB (@lem3333827) (@lem3333826 _86990 s)). Qed.
Lemma lem3333829 {_86990 : Type'} (s : type686 _86990) : (term572 _86990 s) = (term562 _86990 s).
Proof. exact (eq_refl (term572 _86990 s)). Qed.
Lemma lem3333830 {_86990 : Type'} (s : type686 _86990) : (term579 _86990 s) = (term580 _86990 s).
Proof. exact (MK_COMB (@lem3333828 _86990 s) (@lem3333829 _86990 s)). Qed.
Lemma lem3333831 {_86990 : Type'} : (term581 _86990) = (term582 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3333830 _86990 s)). Qed.
Lemma lem3333832 {_86990 : Type'} : (@ex ((_86990 -> Prop) -> Prop)) = (@ex ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3333833 {_86990 : Type'} : (term567 _86990) = (term583 _86990).
Proof. exact (MK_COMB (@lem3333832 _86990) (@lem3333831 _86990)). Qed.
Lemma lem3333834 {_86990 : Type'} : ((term566 _86990) = (term567 _86990)) = ((term565 _86990) = (term583 _86990)).
Proof. exact (MK_COMB (@lem3333825 _86990) (@lem3333833 _86990)). Qed.
Lemma lem3333835 {_86990 : Type'} : (term565 _86990) = (term583 _86990).
Proof. exact (EQ_MP (@lem3333834 _86990) (@lem3333812 _86990)). Qed.
Lemma lem3333837 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term336 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3333838 {_86990 : Type'} (P : type686 _86990) (Q : type686 _86990) : (term360 _86990 P Q) = (term359 _86990 P Q).
Proof. exact (@lem3333837 (_86990 -> Prop) P Q). Qed.
Lemma lem3333839 {_86990 : Type'} (s : type686 _86990) : (term584 _86990 s) = (term585 _86990 s).
Proof. exact (@lem3333838 _86990 (term507 _86990 s) (term561 _86990 s)). Qed.
Lemma lem3333840 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term586 _86990 s t) = (term506 _86990 s t).
Proof. exact (eq_refl (term586 _86990 s t)). Qed.
Lemma lem3333841 {_86990 : Type'} (s : type686 _86990) : (term587 _86990 s) = (term507 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3333840 _86990 s t)). Qed.
Lemma lem3333842 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333843 {_86990 : Type'} (s : type686 _86990) : (term588 _86990 s) = (term508 _86990 s).
Proof. exact (MK_COMB (@lem3333842 _86990) (@lem3333841 _86990 s)). Qed.
Lemma lem3333844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3333845 {_86990 : Type'} (s : type686 _86990) : (term589 _86990 s) = (term578 _86990 s).
Proof. exact (MK_COMB (@lem3333844) (@lem3333843 _86990 s)). Qed.
Lemma lem3333846 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term590 _86990 s t) = (term560 _86990 s t).
Proof. exact (eq_refl (term590 _86990 s t)). Qed.
Lemma lem3333847 {_86990 : Type'} (s : type686 _86990) : (term591 _86990 s) = (term561 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3333846 _86990 s t)). Qed.
Lemma lem3333848 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333849 {_86990 : Type'} (s : type686 _86990) : (term592 _86990 s) = (term562 _86990 s).
Proof. exact (MK_COMB (@lem3333848 _86990) (@lem3333847 _86990 s)). Qed.
Lemma lem3333850 {_86990 : Type'} (s : type686 _86990) : (term584 _86990 s) = (term580 _86990 s).
Proof. exact (MK_COMB (@lem3333845 _86990 s) (@lem3333849 _86990 s)). Qed.
Lemma lem3333851 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3333852 {_86990 : Type'} (s : type686 _86990) : (term593 _86990 s) = (term594 _86990 s).
Proof. exact (MK_COMB (@lem3333851) (@lem3333850 _86990 s)). Qed.
Lemma lem3333853 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term586 _86990 s t) = (term506 _86990 s t).
Proof. exact (eq_refl (term586 _86990 s t)). Qed.
Lemma lem3333854 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3333855 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term595 _86990 s t) = (term596 _86990 s t).
Proof. exact (MK_COMB (@lem3333854) (@lem3333853 _86990 s t)). Qed.
Lemma lem3333856 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term590 _86990 s t) = (term560 _86990 s t).
Proof. exact (eq_refl (term590 _86990 s t)). Qed.
Lemma lem3333857 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term597 _86990 s t) = (term598 _86990 s t).
Proof. exact (MK_COMB (@lem3333855 _86990 s t) (@lem3333856 _86990 s t)). Qed.
Lemma lem3333858 {_86990 : Type'} (s : type686 _86990) : (term599 _86990 s) = (term600 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3333857 _86990 s t)). Qed.
Lemma lem3333859 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333860 {_86990 : Type'} (s : type686 _86990) : (term585 _86990 s) = (term601 _86990 s).
Proof. exact (MK_COMB (@lem3333859 _86990) (@lem3333858 _86990 s)). Qed.
Lemma lem3333861 {_86990 : Type'} (s : type686 _86990) : ((term584 _86990 s) = (term585 _86990 s)) = ((term580 _86990 s) = (term601 _86990 s)).
Proof. exact (MK_COMB (@lem3333852 _86990 s) (@lem3333860 _86990 s)). Qed.
Lemma lem3333862 {_86990 : Type'} (s : type686 _86990) : (term580 _86990 s) = (term601 _86990 s).
Proof. exact (EQ_MP (@lem3333861 _86990 s) (@lem3333839 _86990 s)). Qed.
Lemma lem3333864 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term336 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3333865 {_86990 : Type'} (P : _86990 -> Prop) (Q : _86990 -> Prop) : (term336 _86990 P Q) = (term335 _86990 P Q).
Proof. exact (@lem3333864 _86990 P Q). Qed.
Lemma lem3333866 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term602 _86990 s t) = (term603 _86990 s t).
Proof. exact (@lem3333865 _86990 (term505 _86990 s t) (term559 _86990 s t)). Qed.
Lemma lem3333867 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term604 _86990 s t x) = (term504 _86990 s t x).
Proof. exact (eq_refl (term604 _86990 s t x)). Qed.
Lemma lem3333868 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term605 _86990 s t) = (term505 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3333867 _86990 s t x)). Qed.
Lemma lem3333869 {_86990 : Type'} : (@ex _86990) = (@ex _86990).
Proof. exact (eq_refl (@ex _86990)). Qed.
Lemma lem3333870 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term606 _86990 s t) = (term506 _86990 s t).
Proof. exact (MK_COMB (@lem3333869 _86990) (@lem3333868 _86990 s t)). Qed.
Lemma lem3333871 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3333872 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term607 _86990 s t) = (term596 _86990 s t).
Proof. exact (MK_COMB (@lem3333871) (@lem3333870 _86990 s t)). Qed.
Lemma lem3333873 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term608 _86990 s t x) = (term558 _86990 s t x).
Proof. exact (eq_refl (term608 _86990 s t x)). Qed.
Lemma lem3333874 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term609 _86990 s t) = (term559 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3333873 _86990 s t x)). Qed.
Lemma lem3333875 {_86990 : Type'} : (@ex _86990) = (@ex _86990).
Proof. exact (eq_refl (@ex _86990)). Qed.
Lemma lem3333876 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term610 _86990 s t) = (term560 _86990 s t).
Proof. exact (MK_COMB (@lem3333875 _86990) (@lem3333874 _86990 s t)). Qed.
Lemma lem3333877 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term602 _86990 s t) = (term598 _86990 s t).
Proof. exact (MK_COMB (@lem3333872 _86990 s t) (@lem3333876 _86990 s t)). Qed.
Lemma lem3333878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3333879 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term611 _86990 s t) = (term612 _86990 s t).
Proof. exact (MK_COMB (@lem3333878) (@lem3333877 _86990 s t)). Qed.
Lemma lem3333880 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term604 _86990 s t x) = (term504 _86990 s t x).
Proof. exact (eq_refl (term604 _86990 s t x)). Qed.
Lemma lem3333881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3333882 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term613 _86990 s t x) = (term614 _86990 s t x).
Proof. exact (MK_COMB (@lem3333881) (@lem3333880 _86990 s t x)). Qed.
Lemma lem3333883 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term608 _86990 s t x) = (term558 _86990 s t x).
Proof. exact (eq_refl (term608 _86990 s t x)). Qed.
Lemma lem3333884 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term615 _86990 s t x) = (term616 _86990 s t x).
Proof. exact (MK_COMB (@lem3333882 _86990 s t x) (@lem3333883 _86990 s t x)). Qed.
Lemma lem3333885 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term617 _86990 s t) = (term618 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3333884 _86990 s t x)). Qed.
Lemma lem3333886 {_86990 : Type'} : (@ex _86990) = (@ex _86990).
Proof. exact (eq_refl (@ex _86990)). Qed.
Lemma lem3333887 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term603 _86990 s t) = (term619 _86990 s t).
Proof. exact (MK_COMB (@lem3333886 _86990) (@lem3333885 _86990 s t)). Qed.
Lemma lem3333888 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : ((term602 _86990 s t) = (term603 _86990 s t)) = ((term598 _86990 s t) = (term619 _86990 s t)).
Proof. exact (MK_COMB (@lem3333879 _86990 s t) (@lem3333887 _86990 s t)). Qed.
Lemma lem3333889 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term598 _86990 s t) = (term619 _86990 s t).
Proof. exact (EQ_MP (@lem3333888 _86990 s t) (@lem3333866 _86990 s t)). Qed.
Lemma lem3333891 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term336 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3333892 {_86990 : Type'} (P : type686 _86990) (Q : type686 _86990) : (term360 _86990 P Q) = (term359 _86990 P Q).
Proof. exact (@lem3333891 (_86990 -> Prop) P Q). Qed.
Lemma lem3333893 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term620 _86990 s t x) = (term621 _86990 s t x).
Proof. exact (@lem3333892 _86990 (term503 _86990 s t x) (term557 _86990 s t x)). Qed.
Lemma lem3333894 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term622 _86990 s t x t') = (term501 _86990 t' s t x).
Proof. exact (eq_refl (term622 _86990 s t x t')). Qed.
Lemma lem3333895 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term623 _86990 s t x) = (term503 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3333894 _86990 t' s t x)). Qed.
Lemma lem3333896 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333897 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term624 _86990 s t x) = (term504 _86990 s t x).
Proof. exact (MK_COMB (@lem3333896 _86990) (@lem3333895 _86990 s t x)). Qed.
Lemma lem3333898 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3333899 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term625 _86990 s t x) = (term614 _86990 s t x).
Proof. exact (MK_COMB (@lem3333898) (@lem3333897 _86990 s t x)). Qed.
Lemma lem3333900 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term626 _86990 s t x t') = (term556 _86990 s t x t').
Proof. exact (eq_refl (term626 _86990 s t x t')). Qed.
Lemma lem3333901 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term627 _86990 s t x) = (term557 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3333900 _86990 s t x t')). Qed.
Lemma lem3333902 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333903 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term628 _86990 s t x) = (term558 _86990 s t x).
Proof. exact (MK_COMB (@lem3333902 _86990) (@lem3333901 _86990 s t x)). Qed.
Lemma lem3333904 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term620 _86990 s t x) = (term616 _86990 s t x).
Proof. exact (MK_COMB (@lem3333899 _86990 s t x) (@lem3333903 _86990 s t x)). Qed.
Lemma lem3333905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3333906 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term629 _86990 s t x) = (term630 _86990 s t x).
Proof. exact (MK_COMB (@lem3333905) (@lem3333904 _86990 s t x)). Qed.
Lemma lem3333907 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term622 _86990 s t x t') = (term501 _86990 t' s t x).
Proof. exact (eq_refl (term622 _86990 s t x t')). Qed.
Lemma lem3333908 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3333909 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term631 _86990 s t x t') = (term632 _86990 t' s t x).
Proof. exact (MK_COMB (@lem3333908) (@lem3333907 _86990 t' s t x)). Qed.
Lemma lem3333910 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term626 _86990 s t x t') = (term556 _86990 s t x t').
Proof. exact (eq_refl (term626 _86990 s t x t')). Qed.
Lemma lem3333911 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term633 _86990 s t x t') = (term634 _86990 s t x t').
Proof. exact (MK_COMB (@lem3333909 _86990 t' s t x) (@lem3333910 _86990 s t x t')). Qed.
Lemma lem3333912 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term635 _86990 s t x) = (term636 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3333911 _86990 s t x t')). Qed.
Lemma lem3333913 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333914 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term621 _86990 s t x) = (term637 _86990 s t x).
Proof. exact (MK_COMB (@lem3333913 _86990) (@lem3333912 _86990 s t x)). Qed.
Lemma lem3333915 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : ((term620 _86990 s t x) = (term621 _86990 s t x)) = ((term616 _86990 s t x) = (term637 _86990 s t x)).
Proof. exact (MK_COMB (@lem3333906 _86990 s t x) (@lem3333914 _86990 s t x)). Qed.
Lemma lem3333916 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term616 _86990 s t x) = (term637 _86990 s t x).
Proof. exact (EQ_MP (@lem3333915 _86990 s t x) (@lem3333893 _86990 s t x)). Qed.
Lemma lem3333918 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3333919 {_86990 : Type'} (P : Prop) (Q : type686 _86990) : (term640 _86990 P Q) = (term641 _86990 P Q).
Proof. exact (@lem3333918 (_86990 -> Prop) P Q). Qed.
Lemma lem3333920 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term642 _86990 s t x t') = (term643 _86990 s t x t').
Proof. exact (@lem3333919 _86990 (term501 _86990 t' s t x) (term555 _86990 s t x t')). Qed.
Lemma lem3333921 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term644 _86990 s t x' t' x) = (term553 _86990 s x t x' t').
Proof. exact (eq_refl (term644 _86990 s t x' t' x)). Qed.
Lemma lem3333922 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term645 _86990 s t x t') = (term555 _86990 s t x t').
Proof. exact (fun_ext (fun x' : _86990 -> Prop => @lem3333921 _86990 s x' t x t')). Qed.
Lemma lem3333923 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333924 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term646 _86990 s t x t') = (term556 _86990 s t x t').
Proof. exact (MK_COMB (@lem3333923 _86990) (@lem3333922 _86990 s t x t')). Qed.
Lemma lem3333925 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term632 _86990 t' s t x) = (term632 _86990 t' s t x).
Proof. exact (eq_refl (term632 _86990 t' s t x)). Qed.
Lemma lem3333926 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term642 _86990 s t x t') = (term634 _86990 s t x t').
Proof. exact (MK_COMB (@lem3333925 _86990 t' s t x) (@lem3333924 _86990 s t x t')). Qed.
Lemma lem3333927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3333928 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term647 _86990 s t x t') = (term648 _86990 s t x t').
Proof. exact (MK_COMB (@lem3333927) (@lem3333926 _86990 s t x t')). Qed.
Lemma lem3333929 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term644 _86990 s t x' t' x) = (term553 _86990 s x t x' t').
Proof. exact (eq_refl (term644 _86990 s t x' t' x)). Qed.
Lemma lem3333930 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term632 _86990 t' s t x) = (term632 _86990 t' s t x).
Proof. exact (eq_refl (term632 _86990 t' s t x)). Qed.
Lemma lem3333931 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term649 _86990 s t x' t' x) = (term650 _86990 s x t x' t').
Proof. exact (MK_COMB (@lem3333930 _86990 t' s t x') (@lem3333929 _86990 s x t x' t')). Qed.
Lemma lem3333932 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term651 _86990 s t x t') = (term652 _86990 s t x t').
Proof. exact (fun_ext (fun x' : _86990 -> Prop => @lem3333931 _86990 s x' t x t')). Qed.
Lemma lem3333933 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333934 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term643 _86990 s t x t') = (term653 _86990 s t x t').
Proof. exact (MK_COMB (@lem3333933 _86990) (@lem3333932 _86990 s t x t')). Qed.
Lemma lem3333935 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : ((term642 _86990 s t x t') = (term643 _86990 s t x t')) = ((term634 _86990 s t x t') = (term653 _86990 s t x t')).
Proof. exact (MK_COMB (@lem3333928 _86990 s t x t') (@lem3333934 _86990 s t x t')). Qed.
Lemma lem3333936 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term634 _86990 s t x t') = (term653 _86990 s t x t').
Proof. exact (EQ_MP (@lem3333935 _86990 s t x t') (@lem3333920 _86990 s t x t')). Qed.
Lemma lem3333937 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term636 _86990 s t x) = (term654 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3333936 _86990 s t x t')). Qed.
Lemma lem3333938 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333939 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term637 _86990 s t x) = (term655 _86990 s t x).
Proof. exact (MK_COMB (@lem3333938 _86990) (@lem3333937 _86990 s t x)). Qed.
Lemma lem3333940 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term616 _86990 s t x) = (term655 _86990 s t x).
Proof. exact (TRANS (@lem3333916 _86990 s t x) (@lem3333939 _86990 s t x)). Qed.
Lemma lem3333941 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term618 _86990 s t) = (term656 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3333940 _86990 s t x)). Qed.
Lemma lem3333942 {_86990 : Type'} : (@ex _86990) = (@ex _86990).
Proof. exact (eq_refl (@ex _86990)). Qed.
Lemma lem3333943 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term619 _86990 s t) = (term657 _86990 s t).
Proof. exact (MK_COMB (@lem3333942 _86990) (@lem3333941 _86990 s t)). Qed.
Lemma lem3333944 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term598 _86990 s t) = (term657 _86990 s t).
Proof. exact (TRANS (@lem3333889 _86990 s t) (@lem3333943 _86990 s t)). Qed.
Lemma lem3333945 {_86990 : Type'} (s : type686 _86990) : (term600 _86990 s) = (term658 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3333944 _86990 s t)). Qed.
Lemma lem3333946 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3333947 {_86990 : Type'} (s : type686 _86990) : (term601 _86990 s) = (term659 _86990 s).
Proof. exact (MK_COMB (@lem3333946 _86990) (@lem3333945 _86990 s)). Qed.
Lemma lem3333948 {_86990 : Type'} (s : type686 _86990) : (term580 _86990 s) = (term659 _86990 s).
Proof. exact (TRANS (@lem3333862 _86990 s) (@lem3333947 _86990 s)). Qed.
Lemma lem3333949 {_86990 : Type'} : (term582 _86990) = (term660 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3333948 _86990 s)). Qed.
Lemma lem3333950 {_86990 : Type'} : (@ex ((_86990 -> Prop) -> Prop)) = (@ex ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3333951 {_86990 : Type'} : (term583 _86990) = (term661 _86990).
Proof. exact (MK_COMB (@lem3333950 _86990) (@lem3333949 _86990)). Qed.
Lemma lem3333952 {_86990 : Type'} : (term565 _86990) = (term661 _86990).
Proof. exact (TRANS (@lem3333835 _86990) (@lem3333951 _86990)). Qed.
Lemma lem3333953 {_86990 : Type'} : (term404 _86990) = (term661 _86990).
Proof. exact (TRANS (@lem3333808 _86990) (@lem3333952 _86990)). Qed.
Lemma lem3333954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3333955 {_86990 : Type'} : (term405 _86990) = (term662 _86990).
Proof. exact (MK_COMB (@lem3333954) (@lem3333953 _86990)). Qed.
Lemma lem3333957 {A : Type'} (P : Prop) (Q : A -> Prop) : (term529 A P Q) = (term530 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3333958 {_87026 : Type'} (P : Prop) (Q : type686 _87026) : (term531 _87026 P Q) = (term532 _87026 P Q).
Proof. exact (@lem3333957 (_87026 -> Prop) P Q). Qed.
Lemma lem3333959 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term663 _87026 t s x) = (term664 _87026 t s x).
Proof. exact (@lem3333958 _87026 (@IN _87026 x t) (term195 _87026 s x)). Qed.
Lemma lem3333960 {_87026 : Type'} (s : type686 _87026) (x : _87026) (t : _87026 -> Prop) : (term202 _87026 s x t) = (term194 _87026 s x t).
Proof. exact (eq_refl (term202 _87026 s x t)). Qed.
Lemma lem3333961 {_87026 : Type'} (s : type686 _87026) (x : _87026) : (term477 _87026 s x) = (term195 _87026 s x).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3333960 _87026 s x t)). Qed.
Lemma lem3333962 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3333963 {_87026 : Type'} (s : type686 _87026) (x : _87026) : (term478 _87026 s x) = (term24 _87026 s x).
Proof. exact (MK_COMB (@lem3333962 _87026) (@lem3333961 _87026 s x)). Qed.
Lemma lem3333964 {_87026 : Type'} (x : _87026) (t : _87026 -> Prop) : (term120 _87026 x t) = (term120 _87026 x t).
Proof. exact (eq_refl (term120 _87026 x t)). Qed.
Lemma lem3333965 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term663 _87026 t s x) = (term121 _87026 t s x).
Proof. exact (MK_COMB (@lem3333964 _87026 x t) (@lem3333963 _87026 s x)). Qed.
Lemma lem3333966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3333967 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term665 _87026 t s x) = (term123 _87026 t s x).
Proof. exact (MK_COMB (@lem3333966) (@lem3333965 _87026 t s x)). Qed.
Lemma lem3333968 {_87026 : Type'} (s : type686 _87026) (x : _87026) (t' : _87026 -> Prop) : (term202 _87026 s x t') = (term194 _87026 s x t').
Proof. exact (eq_refl (term202 _87026 s x t')). Qed.
Lemma lem3333969 {_87026 : Type'} (x : _87026) (t : _87026 -> Prop) : (term120 _87026 x t) = (term120 _87026 x t).
Proof. exact (eq_refl (term120 _87026 x t)). Qed.
Lemma lem3333970 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) (t' : _87026 -> Prop) : (term666 _87026 t s x t') = (term667 _87026 t s x t').
Proof. exact (MK_COMB (@lem3333969 _87026 x t) (@lem3333968 _87026 s x t')). Qed.
Lemma lem3333971 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term668 _87026 t s x) = (term669 _87026 t s x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3333970 _87026 t s x t')). Qed.
Lemma lem3333972 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3333973 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term664 _87026 t s x) = (term670 _87026 t s x).
Proof. exact (MK_COMB (@lem3333972 _87026) (@lem3333971 _87026 t s x)). Qed.
Lemma lem3333974 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : ((term663 _87026 t s x) = (term664 _87026 t s x)) = ((term121 _87026 t s x) = (term670 _87026 t s x)).
Proof. exact (MK_COMB (@lem3333967 _87026 t s x) (@lem3333973 _87026 t s x)). Qed.
Lemma lem3333975 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term121 _87026 t s x) = (term670 _87026 t s x).
Proof. exact (EQ_MP (@lem3333974 _87026 t s x) (@lem3333959 _87026 t s x)). Qed.
Lemma lem3333976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3333977 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term302 _87026 t s x) = (term671 _87026 t s x).
Proof. exact (MK_COMB (@lem3333976) (@lem3333975 _87026 t s x)). Qed.
Lemma lem3333978 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term297 _87026 s t x) = (term297 _87026 s t x).
Proof. exact (eq_refl (term297 _87026 s t x)). Qed.
Lemma lem3333979 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term304 _87026 s t x) = (term672 _87026 s t x).
Proof. exact (MK_COMB (@lem3333977 _87026 t s x) (@lem3333978 _87026 s t x)). Qed.
Lemma lem3333981 {A : Type'} (P : A -> Prop) (Q : Prop) : (term471 A P Q) = (term472 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3333982 {_87026 : Type'} (P : type686 _87026) (Q : Prop) : (term473 _87026 P Q) = (term474 _87026 P Q).
Proof. exact (@lem3333981 (_87026 -> Prop) P Q). Qed.
Lemma lem3333983 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term673 _87026 s t x) = (term674 _87026 s t x).
Proof. exact (@lem3333982 _87026 (term669 _87026 t s x) (term297 _87026 s t x)). Qed.
Lemma lem3333984 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) (t' : _87026 -> Prop) : (term675 _87026 t s x t') = (term667 _87026 t s x t').
Proof. exact (eq_refl (term675 _87026 t s x t')). Qed.
Lemma lem3333985 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term676 _87026 t s x) = (term669 _87026 t s x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3333984 _87026 t s x t')). Qed.
Lemma lem3333986 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3333987 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term677 _87026 t s x) = (term670 _87026 t s x).
Proof. exact (MK_COMB (@lem3333986 _87026) (@lem3333985 _87026 t s x)). Qed.
Lemma lem3333988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3333989 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term678 _87026 t s x) = (term671 _87026 t s x).
Proof. exact (MK_COMB (@lem3333988) (@lem3333987 _87026 t s x)). Qed.
Lemma lem3333990 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term297 _87026 s t x) = (term297 _87026 s t x).
Proof. exact (eq_refl (term297 _87026 s t x)). Qed.
Lemma lem3333991 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term673 _87026 s t x) = (term672 _87026 s t x).
Proof. exact (MK_COMB (@lem3333989 _87026 t s x) (@lem3333990 _87026 s t x)). Qed.
Lemma lem3333992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3333993 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term679 _87026 s t x) = (term680 _87026 s t x).
Proof. exact (MK_COMB (@lem3333992) (@lem3333991 _87026 s t x)). Qed.
Lemma lem3333994 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) (t' : _87026 -> Prop) : (term675 _87026 t s x t') = (term667 _87026 t s x t').
Proof. exact (eq_refl (term675 _87026 t s x t')). Qed.
Lemma lem3333995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3333996 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) (t' : _87026 -> Prop) : (term681 _87026 t s x t') = (term682 _87026 t s x t').
Proof. exact (MK_COMB (@lem3333995) (@lem3333994 _87026 t s x t')). Qed.
Lemma lem3333997 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term297 _87026 s t x) = (term297 _87026 s t x).
Proof. exact (eq_refl (term297 _87026 s t x)). Qed.
Lemma lem3333998 {_87026 : Type'} (t' : _87026 -> Prop) (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term683 _87026 t' s t x) = (term684 _87026 t' s t x).
Proof. exact (MK_COMB (@lem3333996 _87026 t s x t') (@lem3333997 _87026 s t x)). Qed.
Lemma lem3333999 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term685 _87026 s t x) = (term686 _87026 s t x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3333998 _87026 t' s t x)). Qed.
Lemma lem3334000 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334001 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term674 _87026 s t x) = (term687 _87026 s t x).
Proof. exact (MK_COMB (@lem3334000 _87026) (@lem3333999 _87026 s t x)). Qed.
Lemma lem3334002 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : ((term673 _87026 s t x) = (term674 _87026 s t x)) = ((term672 _87026 s t x) = (term687 _87026 s t x)).
Proof. exact (MK_COMB (@lem3333993 _87026 s t x) (@lem3334001 _87026 s t x)). Qed.
Lemma lem3334003 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term672 _87026 s t x) = (term687 _87026 s t x).
Proof. exact (EQ_MP (@lem3334002 _87026 s t x) (@lem3333983 _87026 s t x)). Qed.
Lemma lem3334004 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term304 _87026 s t x) = (term687 _87026 s t x).
Proof. exact (TRANS (@lem3333979 _87026 s t x) (@lem3334003 _87026 s t x)). Qed.
Lemma lem3334005 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term408 _87026 s t) = (term688 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3334004 _87026 s t x)). Qed.
Lemma lem3334006 {_87026 : Type'} : (@ex _87026) = (@ex _87026).
Proof. exact (eq_refl (@ex _87026)). Qed.
Lemma lem3334007 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term419 _87026 s t) = (term689 _87026 s t).
Proof. exact (MK_COMB (@lem3334006 _87026) (@lem3334005 _87026 s t)). Qed.
Lemma lem3334008 {_87026 : Type'} (s : type686 _87026) : (term430 _87026 s) = (term690 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3334007 _87026 s t)). Qed.
Lemma lem3334009 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334010 {_87026 : Type'} (s : type686 _87026) : (term441 _87026 s) = (term691 _87026 s).
Proof. exact (MK_COMB (@lem3334009 _87026) (@lem3334008 _87026 s)). Qed.
Lemma lem3334011 {_87026 : Type'} : (term452 _87026) = (term692 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3334010 _87026 s)). Qed.
Lemma lem3334012 {_87026 : Type'} : (@ex ((_87026 -> Prop) -> Prop)) = (@ex ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3334013 {_87026 : Type'} : (term463 _87026) = (term693 _87026).
Proof. exact (MK_COMB (@lem3334012 _87026) (@lem3334011 _87026)). Qed.
Lemma lem3334014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334015 {_87026 : Type'} : (term465 _87026) = (term694 _87026).
Proof. exact (MK_COMB (@lem3334014) (@lem3334013 _87026)). Qed.
Lemma lem3334017 {A : Type'} (P : A -> Prop) (Q : Prop) : (term471 A P Q) = (term472 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3334018 {_87026 : Type'} (P : type686 _87026) (Q : Prop) : (term473 _87026 P Q) = (term474 _87026 P Q).
Proof. exact (@lem3334017 (_87026 -> Prop) P Q). Qed.
Lemma lem3334019 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term695 _87026 s t x t') = (term696 _87026 s t x t').
Proof. exact (@lem3334018 _87026 (term146 _87026 s t' t) (@IN _87026 x t')). Qed.
Lemma lem3334020 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term281 _87026 s t' t x) = (term144 _87026 s t' t x).
Proof. exact (eq_refl (term281 _87026 s t' t x)). Qed.
Lemma lem3334021 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term697 _87026 s t' t) = (term146 _87026 s t' t).
Proof. exact (fun_ext (fun x : _87026 -> Prop => @lem3334020 _87026 s t' t x)). Qed.
Lemma lem3334022 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334023 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term698 _87026 s t' t) = (term147 _87026 s t' t).
Proof. exact (MK_COMB (@lem3334022 _87026) (@lem3334021 _87026 s t' t)). Qed.
Lemma lem3334024 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3334025 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) : (term699 _87026 s t' t) = (term149 _87026 s t' t).
Proof. exact (MK_COMB (@lem3334024) (@lem3334023 _87026 s t' t)). Qed.
Lemma lem3334026 {_87026 : Type'} (x : _87026) (t' : _87026 -> Prop) : (@IN _87026 x t') = (@IN _87026 x t').
Proof. exact (eq_refl (@IN _87026 x t')). Qed.
Lemma lem3334027 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term695 _87026 s t x t') = (term151 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334025 _87026 s t' t) (@lem3334026 _87026 x t')). Qed.
Lemma lem3334028 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334029 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term700 _87026 s t x t') = (term701 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334028) (@lem3334027 _87026 s t x t')). Qed.
Lemma lem3334030 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term281 _87026 s t' t x) = (term144 _87026 s t' t x).
Proof. exact (eq_refl (term281 _87026 s t' t x)). Qed.
Lemma lem3334031 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3334032 {_87026 : Type'} (s : type686 _87026) (t' : _87026 -> Prop) (t : _87026 -> Prop) (x : _87026 -> Prop) : (term702 _87026 s t' t x) = (term703 _87026 s t' t x).
Proof. exact (MK_COMB (@lem3334031) (@lem3334030 _87026 s t' t x)). Qed.
Lemma lem3334033 {_87026 : Type'} (x : _87026) (t' : _87026 -> Prop) : (@IN _87026 x t') = (@IN _87026 x t').
Proof. exact (eq_refl (@IN _87026 x t')). Qed.
Lemma lem3334034 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026 -> Prop) (x' : _87026) (t' : _87026 -> Prop) : (term704 _87026 s t x x' t') = (term705 _87026 s t x x' t').
Proof. exact (MK_COMB (@lem3334032 _87026 s t' t x) (@lem3334033 _87026 x' t')). Qed.
Lemma lem3334035 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term706 _87026 s t x t') = (term707 _87026 s t x t').
Proof. exact (fun_ext (fun x' : _87026 -> Prop => @lem3334034 _87026 s t x' x t')). Qed.
Lemma lem3334036 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334037 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term696 _87026 s t x t') = (term708 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334036 _87026) (@lem3334035 _87026 s t x t')). Qed.
Lemma lem3334038 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : ((term695 _87026 s t x t') = (term696 _87026 s t x t')) = ((term151 _87026 s t x t') = (term708 _87026 s t x t')).
Proof. exact (MK_COMB (@lem3334029 _87026 s t x t') (@lem3334037 _87026 s t x t')). Qed.
Lemma lem3334039 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term151 _87026 s t x t') = (term708 _87026 s t x t').
Proof. exact (EQ_MP (@lem3334038 _87026 s t x t') (@lem3334019 _87026 s t x t')). Qed.
Lemma lem3334040 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term153 _87026 s t x) = (term709 _87026 s t x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3334039 _87026 s t x t')). Qed.
Lemma lem3334041 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334042 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term154 _87026 s t x) = (term710 _87026 s t x).
Proof. exact (MK_COMB (@lem3334041 _87026) (@lem3334040 _87026 s t x)). Qed.
Lemma lem3334043 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term299 _87026 t s x) = (term299 _87026 t s x).
Proof. exact (eq_refl (term299 _87026 t s x)). Qed.
Lemma lem3334044 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term301 _87026 s t x) = (term711 _87026 s t x).
Proof. exact (MK_COMB (@lem3334043 _87026 t s x) (@lem3334042 _87026 s t x)). Qed.
Lemma lem3334046 {A : Type'} (P : Prop) (Q : A -> Prop) : (term529 A P Q) = (term530 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3334047 {_87026 : Type'} (P : Prop) (Q : type686 _87026) : (term531 _87026 P Q) = (term532 _87026 P Q).
Proof. exact (@lem3334046 (_87026 -> Prop) P Q). Qed.
Lemma lem3334048 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term712 _87026 s t x) = (term713 _87026 s t x).
Proof. exact (@lem3334047 _87026 (term275 _87026 t s x) (term709 _87026 s t x)). Qed.
Lemma lem3334049 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term714 _87026 s t x t') = (term708 _87026 s t x t').
Proof. exact (eq_refl (term714 _87026 s t x t')). Qed.
Lemma lem3334050 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term715 _87026 s t x) = (term709 _87026 s t x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3334049 _87026 s t x t')). Qed.
Lemma lem3334051 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334052 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term716 _87026 s t x) = (term710 _87026 s t x).
Proof. exact (MK_COMB (@lem3334051 _87026) (@lem3334050 _87026 s t x)). Qed.
Lemma lem3334053 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term299 _87026 t s x) = (term299 _87026 t s x).
Proof. exact (eq_refl (term299 _87026 t s x)). Qed.
Lemma lem3334054 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term712 _87026 s t x) = (term711 _87026 s t x).
Proof. exact (MK_COMB (@lem3334053 _87026 t s x) (@lem3334052 _87026 s t x)). Qed.
Lemma lem3334055 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334056 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term717 _87026 s t x) = (term718 _87026 s t x).
Proof. exact (MK_COMB (@lem3334055) (@lem3334054 _87026 s t x)). Qed.
Lemma lem3334057 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term714 _87026 s t x t') = (term708 _87026 s t x t').
Proof. exact (eq_refl (term714 _87026 s t x t')). Qed.
Lemma lem3334058 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term299 _87026 t s x) = (term299 _87026 t s x).
Proof. exact (eq_refl (term299 _87026 t s x)). Qed.
Lemma lem3334059 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term719 _87026 s t x t') = (term720 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334058 _87026 t s x) (@lem3334057 _87026 s t x t')). Qed.
Lemma lem3334060 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term721 _87026 s t x) = (term722 _87026 s t x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3334059 _87026 s t x t')). Qed.
Lemma lem3334061 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334062 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term713 _87026 s t x) = (term723 _87026 s t x).
Proof. exact (MK_COMB (@lem3334061 _87026) (@lem3334060 _87026 s t x)). Qed.
Lemma lem3334063 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : ((term712 _87026 s t x) = (term713 _87026 s t x)) = ((term711 _87026 s t x) = (term723 _87026 s t x)).
Proof. exact (MK_COMB (@lem3334056 _87026 s t x) (@lem3334062 _87026 s t x)). Qed.
Lemma lem3334064 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term711 _87026 s t x) = (term723 _87026 s t x).
Proof. exact (EQ_MP (@lem3334063 _87026 s t x) (@lem3334048 _87026 s t x)). Qed.
Lemma lem3334066 {A : Type'} (P : Prop) (Q : A -> Prop) : (term529 A P Q) = (term530 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3334067 {_87026 : Type'} (P : Prop) (Q : type686 _87026) : (term531 _87026 P Q) = (term532 _87026 P Q).
Proof. exact (@lem3334066 (_87026 -> Prop) P Q). Qed.
Lemma lem3334068 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term724 _87026 s t x t') = (term725 _87026 s t x t').
Proof. exact (@lem3334067 _87026 (term275 _87026 t s x) (term707 _87026 s t x t')). Qed.
Lemma lem3334069 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026 -> Prop) (x' : _87026) (t' : _87026 -> Prop) : (term726 _87026 s t x' t' x) = (term705 _87026 s t x x' t').
Proof. exact (eq_refl (term726 _87026 s t x' t' x)). Qed.
Lemma lem3334070 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term727 _87026 s t x t') = (term707 _87026 s t x t').
Proof. exact (fun_ext (fun x' : _87026 -> Prop => @lem3334069 _87026 s t x' x t')). Qed.
Lemma lem3334071 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334072 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term728 _87026 s t x t') = (term708 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334071 _87026) (@lem3334070 _87026 s t x t')). Qed.
Lemma lem3334073 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term299 _87026 t s x) = (term299 _87026 t s x).
Proof. exact (eq_refl (term299 _87026 t s x)). Qed.
Lemma lem3334074 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term724 _87026 s t x t') = (term720 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334073 _87026 t s x) (@lem3334072 _87026 s t x t')). Qed.
Lemma lem3334075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334076 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term729 _87026 s t x t') = (term730 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334075) (@lem3334074 _87026 s t x t')). Qed.
Lemma lem3334077 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026 -> Prop) (x' : _87026) (t' : _87026 -> Prop) : (term726 _87026 s t x' t' x) = (term705 _87026 s t x x' t').
Proof. exact (eq_refl (term726 _87026 s t x' t' x)). Qed.
Lemma lem3334078 {_87026 : Type'} (t : _87026 -> Prop) (s : type686 _87026) (x : _87026) : (term299 _87026 t s x) = (term299 _87026 t s x).
Proof. exact (eq_refl (term299 _87026 t s x)). Qed.
Lemma lem3334079 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026 -> Prop) (x' : _87026) (t' : _87026 -> Prop) : (term731 _87026 s t x' t' x) = (term732 _87026 s t x x' t').
Proof. exact (MK_COMB (@lem3334078 _87026 t s x') (@lem3334077 _87026 s t x x' t')). Qed.
Lemma lem3334080 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term733 _87026 s t x t') = (term734 _87026 s t x t').
Proof. exact (fun_ext (fun x' : _87026 -> Prop => @lem3334079 _87026 s t x' x t')). Qed.
Lemma lem3334081 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334082 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term725 _87026 s t x t') = (term735 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334081 _87026) (@lem3334080 _87026 s t x t')). Qed.
Lemma lem3334083 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : ((term724 _87026 s t x t') = (term725 _87026 s t x t')) = ((term720 _87026 s t x t') = (term735 _87026 s t x t')).
Proof. exact (MK_COMB (@lem3334076 _87026 s t x t') (@lem3334082 _87026 s t x t')). Qed.
Lemma lem3334084 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term720 _87026 s t x t') = (term735 _87026 s t x t').
Proof. exact (EQ_MP (@lem3334083 _87026 s t x t') (@lem3334068 _87026 s t x t')). Qed.
Lemma lem3334085 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term722 _87026 s t x) = (term736 _87026 s t x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3334084 _87026 s t x t')). Qed.
Lemma lem3334086 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334087 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term723 _87026 s t x) = (term737 _87026 s t x).
Proof. exact (MK_COMB (@lem3334086 _87026) (@lem3334085 _87026 s t x)). Qed.
Lemma lem3334088 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term711 _87026 s t x) = (term737 _87026 s t x).
Proof. exact (TRANS (@lem3334064 _87026 s t x) (@lem3334087 _87026 s t x)). Qed.
Lemma lem3334089 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term301 _87026 s t x) = (term737 _87026 s t x).
Proof. exact (TRANS (@lem3334044 _87026 s t x) (@lem3334088 _87026 s t x)). Qed.
Lemma lem3334090 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term409 _87026 s t) = (term738 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3334089 _87026 s t x)). Qed.
Lemma lem3334091 {_87026 : Type'} : (@ex _87026) = (@ex _87026).
Proof. exact (eq_refl (@ex _87026)). Qed.
Lemma lem3334092 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term424 _87026 s t) = (term739 _87026 s t).
Proof. exact (MK_COMB (@lem3334091 _87026) (@lem3334090 _87026 s t)). Qed.
Lemma lem3334093 {_87026 : Type'} (s : type686 _87026) : (term431 _87026 s) = (term740 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3334092 _87026 s t)). Qed.
Lemma lem3334094 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334095 {_87026 : Type'} (s : type686 _87026) : (term446 _87026 s) = (term741 _87026 s).
Proof. exact (MK_COMB (@lem3334094 _87026) (@lem3334093 _87026 s)). Qed.
Lemma lem3334096 {_87026 : Type'} : (term453 _87026) = (term742 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3334095 _87026 s)). Qed.
Lemma lem3334097 {_87026 : Type'} : (@ex ((_87026 -> Prop) -> Prop)) = (@ex ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3334098 {_87026 : Type'} : (term468 _87026) = (term743 _87026).
Proof. exact (MK_COMB (@lem3334097 _87026) (@lem3334096 _87026)). Qed.
Lemma lem3334099 {_87026 : Type'} : (term469 _87026) = (term744 _87026).
Proof. exact (MK_COMB (@lem3334015 _87026) (@lem3334098 _87026)). Qed.
Lemma lem3334101 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term336 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3334102 {_87026 : Type'} (P : type180 _87026) (Q : type180 _87026) : (term384 _87026 P Q) = (term383 _87026 P Q).
Proof. exact (@lem3334101 (type686 _87026) P Q). Qed.
Lemma lem3334103 {_87026 : Type'} : (term745 _87026) = (term746 _87026).
Proof. exact (@lem3334102 _87026 (term692 _87026) (term742 _87026)). Qed.
Lemma lem3334104 {_87026 : Type'} (s : type686 _87026) : (term747 _87026 s) = (term691 _87026 s).
Proof. exact (eq_refl (term747 _87026 s)). Qed.
Lemma lem3334105 {_87026 : Type'} : (term748 _87026) = (term692 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3334104 _87026 s)). Qed.
Lemma lem3334106 {_87026 : Type'} : (@ex ((_87026 -> Prop) -> Prop)) = (@ex ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3334107 {_87026 : Type'} : (term749 _87026) = (term693 _87026).
Proof. exact (MK_COMB (@lem3334106 _87026) (@lem3334105 _87026)). Qed.
Lemma lem3334108 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334109 {_87026 : Type'} : (term750 _87026) = (term694 _87026).
Proof. exact (MK_COMB (@lem3334108) (@lem3334107 _87026)). Qed.
Lemma lem3334110 {_87026 : Type'} (s : type686 _87026) : (term751 _87026 s) = (term741 _87026 s).
Proof. exact (eq_refl (term751 _87026 s)). Qed.
Lemma lem3334111 {_87026 : Type'} : (term752 _87026) = (term742 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3334110 _87026 s)). Qed.
Lemma lem3334112 {_87026 : Type'} : (@ex ((_87026 -> Prop) -> Prop)) = (@ex ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3334113 {_87026 : Type'} : (term753 _87026) = (term743 _87026).
Proof. exact (MK_COMB (@lem3334112 _87026) (@lem3334111 _87026)). Qed.
Lemma lem3334114 {_87026 : Type'} : (term745 _87026) = (term744 _87026).
Proof. exact (MK_COMB (@lem3334109 _87026) (@lem3334113 _87026)). Qed.
Lemma lem3334115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334116 {_87026 : Type'} : (term754 _87026) = (term755 _87026).
Proof. exact (MK_COMB (@lem3334115) (@lem3334114 _87026)). Qed.
Lemma lem3334117 {_87026 : Type'} (s : type686 _87026) : (term747 _87026 s) = (term691 _87026 s).
Proof. exact (eq_refl (term747 _87026 s)). Qed.
Lemma lem3334118 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334119 {_87026 : Type'} (s : type686 _87026) : (term756 _87026 s) = (term757 _87026 s).
Proof. exact (MK_COMB (@lem3334118) (@lem3334117 _87026 s)). Qed.
Lemma lem3334120 {_87026 : Type'} (s : type686 _87026) : (term751 _87026 s) = (term741 _87026 s).
Proof. exact (eq_refl (term751 _87026 s)). Qed.
Lemma lem3334121 {_87026 : Type'} (s : type686 _87026) : (term758 _87026 s) = (term759 _87026 s).
Proof. exact (MK_COMB (@lem3334119 _87026 s) (@lem3334120 _87026 s)). Qed.
Lemma lem3334122 {_87026 : Type'} : (term760 _87026) = (term761 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3334121 _87026 s)). Qed.
Lemma lem3334123 {_87026 : Type'} : (@ex ((_87026 -> Prop) -> Prop)) = (@ex ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3334124 {_87026 : Type'} : (term746 _87026) = (term762 _87026).
Proof. exact (MK_COMB (@lem3334123 _87026) (@lem3334122 _87026)). Qed.
Lemma lem3334125 {_87026 : Type'} : ((term745 _87026) = (term746 _87026)) = ((term744 _87026) = (term762 _87026)).
Proof. exact (MK_COMB (@lem3334116 _87026) (@lem3334124 _87026)). Qed.
Lemma lem3334126 {_87026 : Type'} : (term744 _87026) = (term762 _87026).
Proof. exact (EQ_MP (@lem3334125 _87026) (@lem3334103 _87026)). Qed.
Lemma lem3334128 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term336 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3334129 {_87026 : Type'} (P : type686 _87026) (Q : type686 _87026) : (term360 _87026 P Q) = (term359 _87026 P Q).
Proof. exact (@lem3334128 (_87026 -> Prop) P Q). Qed.
Lemma lem3334130 {_87026 : Type'} (s : type686 _87026) : (term763 _87026 s) = (term764 _87026 s).
Proof. exact (@lem3334129 _87026 (term690 _87026 s) (term740 _87026 s)). Qed.
Lemma lem3334131 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term765 _87026 s t) = (term689 _87026 s t).
Proof. exact (eq_refl (term765 _87026 s t)). Qed.
Lemma lem3334132 {_87026 : Type'} (s : type686 _87026) : (term766 _87026 s) = (term690 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3334131 _87026 s t)). Qed.
Lemma lem3334133 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334134 {_87026 : Type'} (s : type686 _87026) : (term767 _87026 s) = (term691 _87026 s).
Proof. exact (MK_COMB (@lem3334133 _87026) (@lem3334132 _87026 s)). Qed.
Lemma lem3334135 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334136 {_87026 : Type'} (s : type686 _87026) : (term768 _87026 s) = (term757 _87026 s).
Proof. exact (MK_COMB (@lem3334135) (@lem3334134 _87026 s)). Qed.
Lemma lem3334137 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term769 _87026 s t) = (term739 _87026 s t).
Proof. exact (eq_refl (term769 _87026 s t)). Qed.
Lemma lem3334138 {_87026 : Type'} (s : type686 _87026) : (term770 _87026 s) = (term740 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3334137 _87026 s t)). Qed.
Lemma lem3334139 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334140 {_87026 : Type'} (s : type686 _87026) : (term771 _87026 s) = (term741 _87026 s).
Proof. exact (MK_COMB (@lem3334139 _87026) (@lem3334138 _87026 s)). Qed.
Lemma lem3334141 {_87026 : Type'} (s : type686 _87026) : (term763 _87026 s) = (term759 _87026 s).
Proof. exact (MK_COMB (@lem3334136 _87026 s) (@lem3334140 _87026 s)). Qed.
Lemma lem3334142 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334143 {_87026 : Type'} (s : type686 _87026) : (term772 _87026 s) = (term773 _87026 s).
Proof. exact (MK_COMB (@lem3334142) (@lem3334141 _87026 s)). Qed.
Lemma lem3334144 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term765 _87026 s t) = (term689 _87026 s t).
Proof. exact (eq_refl (term765 _87026 s t)). Qed.
Lemma lem3334145 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334146 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term774 _87026 s t) = (term775 _87026 s t).
Proof. exact (MK_COMB (@lem3334145) (@lem3334144 _87026 s t)). Qed.
Lemma lem3334147 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term769 _87026 s t) = (term739 _87026 s t).
Proof. exact (eq_refl (term769 _87026 s t)). Qed.
Lemma lem3334148 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term776 _87026 s t) = (term777 _87026 s t).
Proof. exact (MK_COMB (@lem3334146 _87026 s t) (@lem3334147 _87026 s t)). Qed.
Lemma lem3334149 {_87026 : Type'} (s : type686 _87026) : (term778 _87026 s) = (term779 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3334148 _87026 s t)). Qed.
Lemma lem3334150 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334151 {_87026 : Type'} (s : type686 _87026) : (term764 _87026 s) = (term780 _87026 s).
Proof. exact (MK_COMB (@lem3334150 _87026) (@lem3334149 _87026 s)). Qed.
Lemma lem3334152 {_87026 : Type'} (s : type686 _87026) : ((term763 _87026 s) = (term764 _87026 s)) = ((term759 _87026 s) = (term780 _87026 s)).
Proof. exact (MK_COMB (@lem3334143 _87026 s) (@lem3334151 _87026 s)). Qed.
Lemma lem3334153 {_87026 : Type'} (s : type686 _87026) : (term759 _87026 s) = (term780 _87026 s).
Proof. exact (EQ_MP (@lem3334152 _87026 s) (@lem3334130 _87026 s)). Qed.
Lemma lem3334155 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term336 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3334156 {_87026 : Type'} (P : _87026 -> Prop) (Q : _87026 -> Prop) : (term336 _87026 P Q) = (term335 _87026 P Q).
Proof. exact (@lem3334155 _87026 P Q). Qed.
Lemma lem3334157 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term781 _87026 s t) = (term782 _87026 s t).
Proof. exact (@lem3334156 _87026 (term688 _87026 s t) (term738 _87026 s t)). Qed.
Lemma lem3334158 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term783 _87026 s t x) = (term687 _87026 s t x).
Proof. exact (eq_refl (term783 _87026 s t x)). Qed.
Lemma lem3334159 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term784 _87026 s t) = (term688 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3334158 _87026 s t x)). Qed.
Lemma lem3334160 {_87026 : Type'} : (@ex _87026) = (@ex _87026).
Proof. exact (eq_refl (@ex _87026)). Qed.
Lemma lem3334161 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term785 _87026 s t) = (term689 _87026 s t).
Proof. exact (MK_COMB (@lem3334160 _87026) (@lem3334159 _87026 s t)). Qed.
Lemma lem3334162 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334163 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term786 _87026 s t) = (term775 _87026 s t).
Proof. exact (MK_COMB (@lem3334162) (@lem3334161 _87026 s t)). Qed.
Lemma lem3334164 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term787 _87026 s t x) = (term737 _87026 s t x).
Proof. exact (eq_refl (term787 _87026 s t x)). Qed.
Lemma lem3334165 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term788 _87026 s t) = (term738 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3334164 _87026 s t x)). Qed.
Lemma lem3334166 {_87026 : Type'} : (@ex _87026) = (@ex _87026).
Proof. exact (eq_refl (@ex _87026)). Qed.
Lemma lem3334167 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term789 _87026 s t) = (term739 _87026 s t).
Proof. exact (MK_COMB (@lem3334166 _87026) (@lem3334165 _87026 s t)). Qed.
Lemma lem3334168 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term781 _87026 s t) = (term777 _87026 s t).
Proof. exact (MK_COMB (@lem3334163 _87026 s t) (@lem3334167 _87026 s t)). Qed.
Lemma lem3334169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334170 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term790 _87026 s t) = (term791 _87026 s t).
Proof. exact (MK_COMB (@lem3334169) (@lem3334168 _87026 s t)). Qed.
Lemma lem3334171 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term783 _87026 s t x) = (term687 _87026 s t x).
Proof. exact (eq_refl (term783 _87026 s t x)). Qed.
Lemma lem3334172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334173 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term792 _87026 s t x) = (term793 _87026 s t x).
Proof. exact (MK_COMB (@lem3334172) (@lem3334171 _87026 s t x)). Qed.
Lemma lem3334174 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term787 _87026 s t x) = (term737 _87026 s t x).
Proof. exact (eq_refl (term787 _87026 s t x)). Qed.
Lemma lem3334175 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term794 _87026 s t x) = (term795 _87026 s t x).
Proof. exact (MK_COMB (@lem3334173 _87026 s t x) (@lem3334174 _87026 s t x)). Qed.
Lemma lem3334176 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term796 _87026 s t) = (term797 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3334175 _87026 s t x)). Qed.
Lemma lem3334177 {_87026 : Type'} : (@ex _87026) = (@ex _87026).
Proof. exact (eq_refl (@ex _87026)). Qed.
Lemma lem3334178 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term782 _87026 s t) = (term798 _87026 s t).
Proof. exact (MK_COMB (@lem3334177 _87026) (@lem3334176 _87026 s t)). Qed.
Lemma lem3334179 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : ((term781 _87026 s t) = (term782 _87026 s t)) = ((term777 _87026 s t) = (term798 _87026 s t)).
Proof. exact (MK_COMB (@lem3334170 _87026 s t) (@lem3334178 _87026 s t)). Qed.
Lemma lem3334180 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term777 _87026 s t) = (term798 _87026 s t).
Proof. exact (EQ_MP (@lem3334179 _87026 s t) (@lem3334157 _87026 s t)). Qed.
Lemma lem3334182 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term336 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3334183 {_87026 : Type'} (P : type686 _87026) (Q : type686 _87026) : (term360 _87026 P Q) = (term359 _87026 P Q).
Proof. exact (@lem3334182 (_87026 -> Prop) P Q). Qed.
Lemma lem3334184 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term799 _87026 s t x) = (term800 _87026 s t x).
Proof. exact (@lem3334183 _87026 (term686 _87026 s t x) (term736 _87026 s t x)). Qed.
Lemma lem3334185 {_87026 : Type'} (t' : _87026 -> Prop) (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term801 _87026 s t x t') = (term684 _87026 t' s t x).
Proof. exact (eq_refl (term801 _87026 s t x t')). Qed.
Lemma lem3334186 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term802 _87026 s t x) = (term686 _87026 s t x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3334185 _87026 t' s t x)). Qed.
Lemma lem3334187 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334188 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term803 _87026 s t x) = (term687 _87026 s t x).
Proof. exact (MK_COMB (@lem3334187 _87026) (@lem3334186 _87026 s t x)). Qed.
Lemma lem3334189 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334190 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term804 _87026 s t x) = (term793 _87026 s t x).
Proof. exact (MK_COMB (@lem3334189) (@lem3334188 _87026 s t x)). Qed.
Lemma lem3334191 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term805 _87026 s t x t') = (term735 _87026 s t x t').
Proof. exact (eq_refl (term805 _87026 s t x t')). Qed.
Lemma lem3334192 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term806 _87026 s t x) = (term736 _87026 s t x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3334191 _87026 s t x t')). Qed.
Lemma lem3334193 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334194 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term807 _87026 s t x) = (term737 _87026 s t x).
Proof. exact (MK_COMB (@lem3334193 _87026) (@lem3334192 _87026 s t x)). Qed.
Lemma lem3334195 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term799 _87026 s t x) = (term795 _87026 s t x).
Proof. exact (MK_COMB (@lem3334190 _87026 s t x) (@lem3334194 _87026 s t x)). Qed.
Lemma lem3334196 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334197 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term808 _87026 s t x) = (term809 _87026 s t x).
Proof. exact (MK_COMB (@lem3334196) (@lem3334195 _87026 s t x)). Qed.
Lemma lem3334198 {_87026 : Type'} (t' : _87026 -> Prop) (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term801 _87026 s t x t') = (term684 _87026 t' s t x).
Proof. exact (eq_refl (term801 _87026 s t x t')). Qed.
Lemma lem3334199 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334200 {_87026 : Type'} (t' : _87026 -> Prop) (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term810 _87026 s t x t') = (term811 _87026 t' s t x).
Proof. exact (MK_COMB (@lem3334199) (@lem3334198 _87026 t' s t x)). Qed.
Lemma lem3334201 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term805 _87026 s t x t') = (term735 _87026 s t x t').
Proof. exact (eq_refl (term805 _87026 s t x t')). Qed.
Lemma lem3334202 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term812 _87026 s t x t') = (term813 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334200 _87026 t' s t x) (@lem3334201 _87026 s t x t')). Qed.
Lemma lem3334203 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term814 _87026 s t x) = (term815 _87026 s t x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3334202 _87026 s t x t')). Qed.
Lemma lem3334204 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334205 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term800 _87026 s t x) = (term816 _87026 s t x).
Proof. exact (MK_COMB (@lem3334204 _87026) (@lem3334203 _87026 s t x)). Qed.
Lemma lem3334206 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : ((term799 _87026 s t x) = (term800 _87026 s t x)) = ((term795 _87026 s t x) = (term816 _87026 s t x)).
Proof. exact (MK_COMB (@lem3334197 _87026 s t x) (@lem3334205 _87026 s t x)). Qed.
Lemma lem3334207 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term795 _87026 s t x) = (term816 _87026 s t x).
Proof. exact (EQ_MP (@lem3334206 _87026 s t x) (@lem3334184 _87026 s t x)). Qed.
Lemma lem3334209 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3334210 {_87026 : Type'} (P : Prop) (Q : type686 _87026) : (term640 _87026 P Q) = (term641 _87026 P Q).
Proof. exact (@lem3334209 (_87026 -> Prop) P Q). Qed.
Lemma lem3334211 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term817 _87026 s t x t') = (term818 _87026 s t x t').
Proof. exact (@lem3334210 _87026 (term684 _87026 t' s t x) (term734 _87026 s t x t')). Qed.
Lemma lem3334212 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026 -> Prop) (x' : _87026) (t' : _87026 -> Prop) : (term819 _87026 s t x' t' x) = (term732 _87026 s t x x' t').
Proof. exact (eq_refl (term819 _87026 s t x' t' x)). Qed.
Lemma lem3334213 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term820 _87026 s t x t') = (term734 _87026 s t x t').
Proof. exact (fun_ext (fun x' : _87026 -> Prop => @lem3334212 _87026 s t x' x t')). Qed.
Lemma lem3334214 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334215 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term821 _87026 s t x t') = (term735 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334214 _87026) (@lem3334213 _87026 s t x t')). Qed.
Lemma lem3334216 {_87026 : Type'} (t' : _87026 -> Prop) (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term811 _87026 t' s t x) = (term811 _87026 t' s t x).
Proof. exact (eq_refl (term811 _87026 t' s t x)). Qed.
Lemma lem3334217 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term817 _87026 s t x t') = (term813 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334216 _87026 t' s t x) (@lem3334215 _87026 s t x t')). Qed.
Lemma lem3334218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334219 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term822 _87026 s t x t') = (term823 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334218) (@lem3334217 _87026 s t x t')). Qed.
Lemma lem3334220 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026 -> Prop) (x' : _87026) (t' : _87026 -> Prop) : (term819 _87026 s t x' t' x) = (term732 _87026 s t x x' t').
Proof. exact (eq_refl (term819 _87026 s t x' t' x)). Qed.
Lemma lem3334221 {_87026 : Type'} (t' : _87026 -> Prop) (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term811 _87026 t' s t x) = (term811 _87026 t' s t x).
Proof. exact (eq_refl (term811 _87026 t' s t x)). Qed.
Lemma lem3334222 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026 -> Prop) (x' : _87026) (t' : _87026 -> Prop) : (term824 _87026 s t x' t' x) = (term825 _87026 s t x x' t').
Proof. exact (MK_COMB (@lem3334221 _87026 t' s t x') (@lem3334220 _87026 s t x x' t')). Qed.
Lemma lem3334223 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term826 _87026 s t x t') = (term827 _87026 s t x t').
Proof. exact (fun_ext (fun x' : _87026 -> Prop => @lem3334222 _87026 s t x' x t')). Qed.
Lemma lem3334224 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334225 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term818 _87026 s t x t') = (term828 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334224 _87026) (@lem3334223 _87026 s t x t')). Qed.
Lemma lem3334226 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : ((term817 _87026 s t x t') = (term818 _87026 s t x t')) = ((term813 _87026 s t x t') = (term828 _87026 s t x t')).
Proof. exact (MK_COMB (@lem3334219 _87026 s t x t') (@lem3334225 _87026 s t x t')). Qed.
Lemma lem3334227 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term813 _87026 s t x t') = (term828 _87026 s t x t').
Proof. exact (EQ_MP (@lem3334226 _87026 s t x t') (@lem3334211 _87026 s t x t')). Qed.
Lemma lem3334228 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term815 _87026 s t x) = (term829 _87026 s t x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3334227 _87026 s t x t')). Qed.
Lemma lem3334229 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334230 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term816 _87026 s t x) = (term830 _87026 s t x).
Proof. exact (MK_COMB (@lem3334229 _87026) (@lem3334228 _87026 s t x)). Qed.
Lemma lem3334231 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term795 _87026 s t x) = (term830 _87026 s t x).
Proof. exact (TRANS (@lem3334207 _87026 s t x) (@lem3334230 _87026 s t x)). Qed.
Lemma lem3334232 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term797 _87026 s t) = (term831 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3334231 _87026 s t x)). Qed.
Lemma lem3334233 {_87026 : Type'} : (@ex _87026) = (@ex _87026).
Proof. exact (eq_refl (@ex _87026)). Qed.
Lemma lem3334234 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term798 _87026 s t) = (term832 _87026 s t).
Proof. exact (MK_COMB (@lem3334233 _87026) (@lem3334232 _87026 s t)). Qed.
Lemma lem3334235 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term777 _87026 s t) = (term832 _87026 s t).
Proof. exact (TRANS (@lem3334180 _87026 s t) (@lem3334234 _87026 s t)). Qed.
Lemma lem3334236 {_87026 : Type'} (s : type686 _87026) : (term779 _87026 s) = (term833 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3334235 _87026 s t)). Qed.
Lemma lem3334237 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334238 {_87026 : Type'} (s : type686 _87026) : (term780 _87026 s) = (term834 _87026 s).
Proof. exact (MK_COMB (@lem3334237 _87026) (@lem3334236 _87026 s)). Qed.
Lemma lem3334239 {_87026 : Type'} (s : type686 _87026) : (term759 _87026 s) = (term834 _87026 s).
Proof. exact (TRANS (@lem3334153 _87026 s) (@lem3334238 _87026 s)). Qed.
Lemma lem3334240 {_87026 : Type'} : (term761 _87026) = (term835 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3334239 _87026 s)). Qed.
Lemma lem3334241 {_87026 : Type'} : (@ex ((_87026 -> Prop) -> Prop)) = (@ex ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3334242 {_87026 : Type'} : (term762 _87026) = (term836 _87026).
Proof. exact (MK_COMB (@lem3334241 _87026) (@lem3334240 _87026)). Qed.
Lemma lem3334243 {_87026 : Type'} : (term744 _87026) = (term836 _87026).
Proof. exact (TRANS (@lem3334126 _87026) (@lem3334242 _87026)). Qed.
Lemma lem3334244 {_87026 : Type'} : (term469 _87026) = (term836 _87026).
Proof. exact (TRANS (@lem3334099 _87026) (@lem3334243 _87026)). Qed.
Lemma lem3334245 {_86990 _87026 : Type'} : (term470 _86990 _87026) = (term837 _86990 _87026).
Proof. exact (MK_COMB (@lem3333955 _86990) (@lem3334244 _87026)). Qed.
Lemma lem3334249 {A : Type'} (P : A -> Prop) (Q : Prop) : (term838 A P Q) = (term839 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3334250 {_86990 : Type'} (P : type180 _86990) (Q : Prop) : (term840 _86990 P Q) = (term841 _86990 P Q).
Proof. exact (@lem3334249 (type686 _86990) P Q). Qed.
Lemma lem3334251 {_86990 _87026 : Type'} : (term842 _86990 _87026) = (term843 _86990 _87026).
Proof. exact (@lem3334250 _86990 (term660 _86990) (term836 _87026)). Qed.
Lemma lem3334252 {_86990 : Type'} (s : type686 _86990) : (term844 _86990 s) = (term659 _86990 s).
Proof. exact (eq_refl (term844 _86990 s)). Qed.
Lemma lem3334253 {_86990 : Type'} : (term845 _86990) = (term660 _86990).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3334252 _86990 s)). Qed.
Lemma lem3334254 {_86990 : Type'} : (@ex ((_86990 -> Prop) -> Prop)) = (@ex ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3334255 {_86990 : Type'} : (term846 _86990) = (term661 _86990).
Proof. exact (MK_COMB (@lem3334254 _86990) (@lem3334253 _86990)). Qed.
Lemma lem3334256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334257 {_86990 : Type'} : (term847 _86990) = (term662 _86990).
Proof. exact (MK_COMB (@lem3334256) (@lem3334255 _86990)). Qed.
Lemma lem3334258 {_87026 : Type'} : (term836 _87026) = (term836 _87026).
Proof. exact (eq_refl (term836 _87026)). Qed.
Lemma lem3334259 {_86990 _87026 : Type'} : (term842 _86990 _87026) = (term837 _86990 _87026).
Proof. exact (MK_COMB (@lem3334257 _86990) (@lem3334258 _87026)). Qed.
Lemma lem3334260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334261 {_86990 _87026 : Type'} : (term848 _86990 _87026) = (term849 _86990 _87026).
Proof. exact (MK_COMB (@lem3334260) (@lem3334259 _86990 _87026)). Qed.
Lemma lem3334262 {_86990 : Type'} (s : type686 _86990) : (term844 _86990 s) = (term659 _86990 s).
Proof. exact (eq_refl (term844 _86990 s)). Qed.
Lemma lem3334263 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334264 {_86990 : Type'} (s : type686 _86990) : (term850 _86990 s) = (term851 _86990 s).
Proof. exact (MK_COMB (@lem3334263) (@lem3334262 _86990 s)). Qed.
Lemma lem3334265 {_87026 : Type'} : (term836 _87026) = (term836 _87026).
Proof. exact (eq_refl (term836 _87026)). Qed.
Lemma lem3334266 {_86990 _87026 : Type'} (s : type686 _86990) : (term852 _86990 _87026 s) = (term853 _86990 _87026 s).
Proof. exact (MK_COMB (@lem3334264 _86990 s) (@lem3334265 _87026)). Qed.
Lemma lem3334267 {_86990 _87026 : Type'} : (term854 _86990 _87026) = (term855 _86990 _87026).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3334266 _86990 _87026 s)). Qed.
Lemma lem3334268 {_86990 : Type'} : (@ex ((_86990 -> Prop) -> Prop)) = (@ex ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3334269 {_86990 _87026 : Type'} : (term843 _86990 _87026) = (term856 _86990 _87026).
Proof. exact (MK_COMB (@lem3334268 _86990) (@lem3334267 _86990 _87026)). Qed.
Lemma lem3334270 {_86990 _87026 : Type'} : ((term842 _86990 _87026) = (term843 _86990 _87026)) = ((term837 _86990 _87026) = (term856 _86990 _87026)).
Proof. exact (MK_COMB (@lem3334261 _86990 _87026) (@lem3334269 _86990 _87026)). Qed.
Lemma lem3334271 {_86990 _87026 : Type'} : (term837 _86990 _87026) = (term856 _86990 _87026).
Proof. exact (EQ_MP (@lem3334270 _86990 _87026) (@lem3334251 _86990 _87026)). Qed.
Lemma lem3334275 {A : Type'} (P : A -> Prop) (Q : Prop) : (term838 A P Q) = (term839 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3334276 {_86990 : Type'} (P : type686 _86990) (Q : Prop) : (term857 _86990 P Q) = (term858 _86990 P Q).
Proof. exact (@lem3334275 (_86990 -> Prop) P Q). Qed.
Lemma lem3334277 {_86990 _87026 : Type'} (s : type686 _86990) : (term859 _86990 _87026 s) = (term860 _86990 _87026 s).
Proof. exact (@lem3334276 _86990 (term658 _86990 s) (term836 _87026)). Qed.
Lemma lem3334278 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term861 _86990 s t) = (term657 _86990 s t).
Proof. exact (eq_refl (term861 _86990 s t)). Qed.
Lemma lem3334279 {_86990 : Type'} (s : type686 _86990) : (term862 _86990 s) = (term658 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3334278 _86990 s t)). Qed.
Lemma lem3334280 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3334281 {_86990 : Type'} (s : type686 _86990) : (term863 _86990 s) = (term659 _86990 s).
Proof. exact (MK_COMB (@lem3334280 _86990) (@lem3334279 _86990 s)). Qed.
Lemma lem3334282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334283 {_86990 : Type'} (s : type686 _86990) : (term864 _86990 s) = (term851 _86990 s).
Proof. exact (MK_COMB (@lem3334282) (@lem3334281 _86990 s)). Qed.
Lemma lem3334284 {_87026 : Type'} : (term836 _87026) = (term836 _87026).
Proof. exact (eq_refl (term836 _87026)). Qed.
Lemma lem3334285 {_86990 _87026 : Type'} (s : type686 _86990) : (term859 _86990 _87026 s) = (term853 _86990 _87026 s).
Proof. exact (MK_COMB (@lem3334283 _86990 s) (@lem3334284 _87026)). Qed.
Lemma lem3334286 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334287 {_86990 _87026 : Type'} (s : type686 _86990) : (term865 _86990 _87026 s) = (term866 _86990 _87026 s).
Proof. exact (MK_COMB (@lem3334286) (@lem3334285 _86990 _87026 s)). Qed.
Lemma lem3334288 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term861 _86990 s t) = (term657 _86990 s t).
Proof. exact (eq_refl (term861 _86990 s t)). Qed.
Lemma lem3334289 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334290 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term867 _86990 s t) = (term868 _86990 s t).
Proof. exact (MK_COMB (@lem3334289) (@lem3334288 _86990 s t)). Qed.
Lemma lem3334291 {_87026 : Type'} : (term836 _87026) = (term836 _87026).
Proof. exact (eq_refl (term836 _87026)). Qed.
Lemma lem3334292 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term869 _86990 _87026 s t) = (term870 _86990 _87026 s t).
Proof. exact (MK_COMB (@lem3334290 _86990 s t) (@lem3334291 _87026)). Qed.
Lemma lem3334293 {_86990 _87026 : Type'} (s : type686 _86990) : (term871 _86990 _87026 s) = (term872 _86990 _87026 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3334292 _86990 _87026 s t)). Qed.
Lemma lem3334294 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3334295 {_86990 _87026 : Type'} (s : type686 _86990) : (term860 _86990 _87026 s) = (term873 _86990 _87026 s).
Proof. exact (MK_COMB (@lem3334294 _86990) (@lem3334293 _86990 _87026 s)). Qed.
Lemma lem3334296 {_86990 _87026 : Type'} (s : type686 _86990) : ((term859 _86990 _87026 s) = (term860 _86990 _87026 s)) = ((term853 _86990 _87026 s) = (term873 _86990 _87026 s)).
Proof. exact (MK_COMB (@lem3334287 _86990 _87026 s) (@lem3334295 _86990 _87026 s)). Qed.
Lemma lem3334297 {_86990 _87026 : Type'} (s : type686 _86990) : (term853 _86990 _87026 s) = (term873 _86990 _87026 s).
Proof. exact (EQ_MP (@lem3334296 _86990 _87026 s) (@lem3334277 _86990 _87026 s)). Qed.
Lemma lem3334301 {A : Type'} (P : A -> Prop) (Q : Prop) : (term838 A P Q) = (term839 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3334302 {_86990 : Type'} (P : _86990 -> Prop) (Q : Prop) : (term838 _86990 P Q) = (term839 _86990 P Q).
Proof. exact (@lem3334301 _86990 P Q). Qed.
Lemma lem3334303 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term874 _86990 _87026 s t) = (term875 _86990 _87026 s t).
Proof. exact (@lem3334302 _86990 (term656 _86990 s t) (term836 _87026)). Qed.
Lemma lem3334304 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term876 _86990 s t x) = (term655 _86990 s t x).
Proof. exact (eq_refl (term876 _86990 s t x)). Qed.
Lemma lem3334305 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term877 _86990 s t) = (term656 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3334304 _86990 s t x)). Qed.
Lemma lem3334306 {_86990 : Type'} : (@ex _86990) = (@ex _86990).
Proof. exact (eq_refl (@ex _86990)). Qed.
Lemma lem3334307 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term878 _86990 s t) = (term657 _86990 s t).
Proof. exact (MK_COMB (@lem3334306 _86990) (@lem3334305 _86990 s t)). Qed.
Lemma lem3334308 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334309 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term879 _86990 s t) = (term868 _86990 s t).
Proof. exact (MK_COMB (@lem3334308) (@lem3334307 _86990 s t)). Qed.
Lemma lem3334310 {_87026 : Type'} : (term836 _87026) = (term836 _87026).
Proof. exact (eq_refl (term836 _87026)). Qed.
Lemma lem3334311 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term874 _86990 _87026 s t) = (term870 _86990 _87026 s t).
Proof. exact (MK_COMB (@lem3334309 _86990 s t) (@lem3334310 _87026)). Qed.
Lemma lem3334312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334313 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term880 _86990 _87026 s t) = (term881 _86990 _87026 s t).
Proof. exact (MK_COMB (@lem3334312) (@lem3334311 _86990 _87026 s t)). Qed.
Lemma lem3334314 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term876 _86990 s t x) = (term655 _86990 s t x).
Proof. exact (eq_refl (term876 _86990 s t x)). Qed.
Lemma lem3334315 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334316 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term882 _86990 s t x) = (term883 _86990 s t x).
Proof. exact (MK_COMB (@lem3334315) (@lem3334314 _86990 s t x)). Qed.
Lemma lem3334317 {_87026 : Type'} : (term836 _87026) = (term836 _87026).
Proof. exact (eq_refl (term836 _87026)). Qed.
Lemma lem3334318 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term884 _86990 _87026 s t x) = (term885 _86990 _87026 s t x).
Proof. exact (MK_COMB (@lem3334316 _86990 s t x) (@lem3334317 _87026)). Qed.
Lemma lem3334319 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term886 _86990 _87026 s t) = (term887 _86990 _87026 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3334318 _86990 _87026 s t x)). Qed.
Lemma lem3334320 {_86990 : Type'} : (@ex _86990) = (@ex _86990).
Proof. exact (eq_refl (@ex _86990)). Qed.
Lemma lem3334321 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term875 _86990 _87026 s t) = (term888 _86990 _87026 s t).
Proof. exact (MK_COMB (@lem3334320 _86990) (@lem3334319 _86990 _87026 s t)). Qed.
Lemma lem3334322 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : ((term874 _86990 _87026 s t) = (term875 _86990 _87026 s t)) = ((term870 _86990 _87026 s t) = (term888 _86990 _87026 s t)).
Proof. exact (MK_COMB (@lem3334313 _86990 _87026 s t) (@lem3334321 _86990 _87026 s t)). Qed.
Lemma lem3334323 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term870 _86990 _87026 s t) = (term888 _86990 _87026 s t).
Proof. exact (EQ_MP (@lem3334322 _86990 _87026 s t) (@lem3334303 _86990 _87026 s t)). Qed.
Lemma lem3334327 {A : Type'} (P : A -> Prop) (Q : Prop) : (term838 A P Q) = (term839 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3334328 {_86990 : Type'} (P : type686 _86990) (Q : Prop) : (term857 _86990 P Q) = (term858 _86990 P Q).
Proof. exact (@lem3334327 (_86990 -> Prop) P Q). Qed.
Lemma lem3334329 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term889 _86990 _87026 s t x) = (term890 _86990 _87026 s t x).
Proof. exact (@lem3334328 _86990 (term654 _86990 s t x) (term836 _87026)). Qed.
Lemma lem3334330 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term891 _86990 s t x t') = (term653 _86990 s t x t').
Proof. exact (eq_refl (term891 _86990 s t x t')). Qed.
Lemma lem3334331 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term892 _86990 s t x) = (term654 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3334330 _86990 s t x t')). Qed.
Lemma lem3334332 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3334333 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term893 _86990 s t x) = (term655 _86990 s t x).
Proof. exact (MK_COMB (@lem3334332 _86990) (@lem3334331 _86990 s t x)). Qed.
Lemma lem3334334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334335 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term894 _86990 s t x) = (term883 _86990 s t x).
Proof. exact (MK_COMB (@lem3334334) (@lem3334333 _86990 s t x)). Qed.
Lemma lem3334336 {_87026 : Type'} : (term836 _87026) = (term836 _87026).
Proof. exact (eq_refl (term836 _87026)). Qed.
Lemma lem3334337 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term889 _86990 _87026 s t x) = (term885 _86990 _87026 s t x).
Proof. exact (MK_COMB (@lem3334335 _86990 s t x) (@lem3334336 _87026)). Qed.
Lemma lem3334338 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334339 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term895 _86990 _87026 s t x) = (term896 _86990 _87026 s t x).
Proof. exact (MK_COMB (@lem3334338) (@lem3334337 _86990 _87026 s t x)). Qed.
Lemma lem3334340 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term891 _86990 s t x t') = (term653 _86990 s t x t').
Proof. exact (eq_refl (term891 _86990 s t x t')). Qed.
Lemma lem3334341 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334342 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term897 _86990 s t x t') = (term898 _86990 s t x t').
Proof. exact (MK_COMB (@lem3334341) (@lem3334340 _86990 s t x t')). Qed.
Lemma lem3334343 {_87026 : Type'} : (term836 _87026) = (term836 _87026).
Proof. exact (eq_refl (term836 _87026)). Qed.
Lemma lem3334344 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term899 _86990 _87026 s t x t') = (term900 _86990 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334342 _86990 s t x t') (@lem3334343 _87026)). Qed.
Lemma lem3334345 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term901 _86990 _87026 s t x) = (term902 _86990 _87026 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3334344 _86990 _87026 s t x t')). Qed.
Lemma lem3334346 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3334347 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term890 _86990 _87026 s t x) = (term903 _86990 _87026 s t x).
Proof. exact (MK_COMB (@lem3334346 _86990) (@lem3334345 _86990 _87026 s t x)). Qed.
Lemma lem3334348 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : ((term889 _86990 _87026 s t x) = (term890 _86990 _87026 s t x)) = ((term885 _86990 _87026 s t x) = (term903 _86990 _87026 s t x)).
Proof. exact (MK_COMB (@lem3334339 _86990 _87026 s t x) (@lem3334347 _86990 _87026 s t x)). Qed.
Lemma lem3334349 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term885 _86990 _87026 s t x) = (term903 _86990 _87026 s t x).
Proof. exact (EQ_MP (@lem3334348 _86990 _87026 s t x) (@lem3334329 _86990 _87026 s t x)). Qed.
Lemma lem3334353 {A : Type'} (P : A -> Prop) (Q : Prop) : (term838 A P Q) = (term839 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3334354 {_86990 : Type'} (P : type686 _86990) (Q : Prop) : (term857 _86990 P Q) = (term858 _86990 P Q).
Proof. exact (@lem3334353 (_86990 -> Prop) P Q). Qed.
Lemma lem3334355 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term904 _86990 _87026 s t x t') = (term905 _86990 _87026 s t x t').
Proof. exact (@lem3334354 _86990 (term652 _86990 s t x t') (term836 _87026)). Qed.
Lemma lem3334356 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term906 _86990 s t x' t' x) = (term650 _86990 s x t x' t').
Proof. exact (eq_refl (term906 _86990 s t x' t' x)). Qed.
Lemma lem3334357 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term907 _86990 s t x t') = (term652 _86990 s t x t').
Proof. exact (fun_ext (fun x' : _86990 -> Prop => @lem3334356 _86990 s x' t x t')). Qed.
Lemma lem3334358 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3334359 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term908 _86990 s t x t') = (term653 _86990 s t x t').
Proof. exact (MK_COMB (@lem3334358 _86990) (@lem3334357 _86990 s t x t')). Qed.
Lemma lem3334360 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334361 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term909 _86990 s t x t') = (term898 _86990 s t x t').
Proof. exact (MK_COMB (@lem3334360) (@lem3334359 _86990 s t x t')). Qed.
Lemma lem3334362 {_87026 : Type'} : (term836 _87026) = (term836 _87026).
Proof. exact (eq_refl (term836 _87026)). Qed.
Lemma lem3334363 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term904 _86990 _87026 s t x t') = (term900 _86990 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334361 _86990 s t x t') (@lem3334362 _87026)). Qed.
Lemma lem3334364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334365 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term910 _86990 _87026 s t x t') = (term911 _86990 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334364) (@lem3334363 _86990 _87026 s t x t')). Qed.
Lemma lem3334366 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term906 _86990 s t x' t' x) = (term650 _86990 s x t x' t').
Proof. exact (eq_refl (term906 _86990 s t x' t' x)). Qed.
Lemma lem3334367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3334368 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term912 _86990 s t x' t' x) = (term913 _86990 s x t x' t').
Proof. exact (MK_COMB (@lem3334367) (@lem3334366 _86990 s x t x' t')). Qed.
Lemma lem3334369 {_87026 : Type'} : (term836 _87026) = (term836 _87026).
Proof. exact (eq_refl (term836 _87026)). Qed.
Lemma lem3334370 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term914 _86990 _87026 s t x' t' x) = (term915 _86990 _87026 s x t x' t').
Proof. exact (MK_COMB (@lem3334368 _86990 s x t x' t') (@lem3334369 _87026)). Qed.
Lemma lem3334371 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term916 _86990 _87026 s t x t') = (term917 _86990 _87026 s t x t').
Proof. exact (fun_ext (fun x' : _86990 -> Prop => @lem3334370 _86990 _87026 s x' t x t')). Qed.
Lemma lem3334372 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3334373 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term905 _86990 _87026 s t x t') = (term918 _86990 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334372 _86990) (@lem3334371 _86990 _87026 s t x t')). Qed.
Lemma lem3334374 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : ((term904 _86990 _87026 s t x t') = (term905 _86990 _87026 s t x t')) = ((term900 _86990 _87026 s t x t') = (term918 _86990 _87026 s t x t')).
Proof. exact (MK_COMB (@lem3334365 _86990 _87026 s t x t') (@lem3334373 _86990 _87026 s t x t')). Qed.
Lemma lem3334375 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term900 _86990 _87026 s t x t') = (term918 _86990 _87026 s t x t').
Proof. exact (EQ_MP (@lem3334374 _86990 _87026 s t x t') (@lem3334355 _86990 _87026 s t x t')). Qed.
Lemma lem3334377 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3334378 {_87026 : Type'} (P : Prop) (Q : type180 _87026) : (term919 _87026 P Q) = (term920 _87026 P Q).
Proof. exact (@lem3334377 (type686 _87026) P Q). Qed.
Lemma lem3334379 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term921 _86990 _87026 s x t x' t') = (term922 _86990 _87026 s x t x' t').
Proof. exact (@lem3334378 _87026 (term650 _86990 s x t x' t') (term835 _87026)). Qed.
Lemma lem3334380 {_87026 : Type'} (s : type686 _87026) : (term923 _87026 s) = (term834 _87026 s).
Proof. exact (eq_refl (term923 _87026 s)). Qed.
Lemma lem3334381 {_87026 : Type'} : (term924 _87026) = (term835 _87026).
Proof. exact (fun_ext (fun s : type686 _87026 => @lem3334380 _87026 s)). Qed.
Lemma lem3334382 {_87026 : Type'} : (@ex ((_87026 -> Prop) -> Prop)) = (@ex ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3334383 {_87026 : Type'} : (term925 _87026) = (term836 _87026).
Proof. exact (MK_COMB (@lem3334382 _87026) (@lem3334381 _87026)). Qed.
Lemma lem3334384 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term913 _86990 s x t x' t') = (term913 _86990 s x t x' t').
Proof. exact (eq_refl (term913 _86990 s x t x' t')). Qed.
Lemma lem3334385 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term921 _86990 _87026 s x t x' t') = (term915 _86990 _87026 s x t x' t').
Proof. exact (MK_COMB (@lem3334384 _86990 s x t x' t') (@lem3334383 _87026)). Qed.
Lemma lem3334386 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334387 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term926 _86990 _87026 s x t x' t') = (term927 _86990 _87026 s x t x' t').
Proof. exact (MK_COMB (@lem3334386) (@lem3334385 _86990 _87026 s x t x' t')). Qed.
Lemma lem3334388 {_87026 : Type'} (s : type686 _87026) : (term923 _87026 s) = (term834 _87026 s).
Proof. exact (eq_refl (term923 _87026 s)). Qed.
Lemma lem3334389 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term913 _86990 s x t x' t') = (term913 _86990 s x t x' t').
Proof. exact (eq_refl (term913 _86990 s x t x' t')). Qed.
Lemma lem3334390 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) : (term928 _86990 _87026 s x t x' t' s') = (term929 _86990 _87026 s x t x' t' s').
Proof. exact (MK_COMB (@lem3334389 _86990 s x t x' t') (@lem3334388 _87026 s')). Qed.
Lemma lem3334391 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term930 _86990 _87026 s x t x' t') = (term931 _86990 _87026 s x t x' t').
Proof. exact (fun_ext (fun s' : type686 _87026 => @lem3334390 _86990 _87026 s x t x' t' s')). Qed.
Lemma lem3334392 {_87026 : Type'} : (@ex ((_87026 -> Prop) -> Prop)) = (@ex ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3334393 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term922 _86990 _87026 s x t x' t') = (term932 _86990 _87026 s x t x' t').
Proof. exact (MK_COMB (@lem3334392 _87026) (@lem3334391 _86990 _87026 s x t x' t')). Qed.
Lemma lem3334394 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : ((term921 _86990 _87026 s x t x' t') = (term922 _86990 _87026 s x t x' t')) = ((term915 _86990 _87026 s x t x' t') = (term932 _86990 _87026 s x t x' t')).
Proof. exact (MK_COMB (@lem3334387 _86990 _87026 s x t x' t') (@lem3334393 _86990 _87026 s x t x' t')). Qed.
Lemma lem3334395 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term915 _86990 _87026 s x t x' t') = (term932 _86990 _87026 s x t x' t').
Proof. exact (EQ_MP (@lem3334394 _86990 _87026 s x t x' t') (@lem3334379 _86990 _87026 s x t x' t')). Qed.
Lemma lem3334397 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3334398 {_87026 : Type'} (P : Prop) (Q : type686 _87026) : (term640 _87026 P Q) = (term641 _87026 P Q).
Proof. exact (@lem3334397 (_87026 -> Prop) P Q). Qed.
Lemma lem3334399 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) : (term933 _86990 _87026 s x t x' t' s') = (term934 _86990 _87026 s x t x' t' s').
Proof. exact (@lem3334398 _87026 (term650 _86990 s x t x' t') (term833 _87026 s')). Qed.
Lemma lem3334400 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term935 _87026 s t) = (term832 _87026 s t).
Proof. exact (eq_refl (term935 _87026 s t)). Qed.
Lemma lem3334401 {_87026 : Type'} (s : type686 _87026) : (term936 _87026 s) = (term833 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3334400 _87026 s t)). Qed.
Lemma lem3334402 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334403 {_87026 : Type'} (s : type686 _87026) : (term937 _87026 s) = (term834 _87026 s).
Proof. exact (MK_COMB (@lem3334402 _87026) (@lem3334401 _87026 s)). Qed.
Lemma lem3334404 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term913 _86990 s x t x' t') = (term913 _86990 s x t x' t').
Proof. exact (eq_refl (term913 _86990 s x t x' t')). Qed.
Lemma lem3334405 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) : (term933 _86990 _87026 s x t x' t' s') = (term929 _86990 _87026 s x t x' t' s').
Proof. exact (MK_COMB (@lem3334404 _86990 s x t x' t') (@lem3334403 _87026 s')). Qed.
Lemma lem3334406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334407 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) : (term938 _86990 _87026 s x t x' t' s') = (term939 _86990 _87026 s x t x' t' s').
Proof. exact (MK_COMB (@lem3334406) (@lem3334405 _86990 _87026 s x t x' t' s')). Qed.
Lemma lem3334408 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term935 _87026 s t) = (term832 _87026 s t).
Proof. exact (eq_refl (term935 _87026 s t)). Qed.
Lemma lem3334409 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term913 _86990 s x t x' t') = (term913 _86990 s x t x' t').
Proof. exact (eq_refl (term913 _86990 s x t x' t')). Qed.
Lemma lem3334410 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) : (term940 _86990 _87026 s x t x' t' s' t'') = (term941 _86990 _87026 s x t x' t' s' t'').
Proof. exact (MK_COMB (@lem3334409 _86990 s x t x' t') (@lem3334408 _87026 s' t'')). Qed.
Lemma lem3334411 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) : (term942 _86990 _87026 s x t x' t' s') = (term943 _86990 _87026 s x t x' t' s').
Proof. exact (fun_ext (fun t'' : _87026 -> Prop => @lem3334410 _86990 _87026 s x t x' t' s' t'')). Qed.
Lemma lem3334412 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334413 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) : (term934 _86990 _87026 s x t x' t' s') = (term944 _86990 _87026 s x t x' t' s').
Proof. exact (MK_COMB (@lem3334412 _87026) (@lem3334411 _86990 _87026 s x t x' t' s')). Qed.
Lemma lem3334414 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) : ((term933 _86990 _87026 s x t x' t' s') = (term934 _86990 _87026 s x t x' t' s')) = ((term929 _86990 _87026 s x t x' t' s') = (term944 _86990 _87026 s x t x' t' s')).
Proof. exact (MK_COMB (@lem3334407 _86990 _87026 s x t x' t' s') (@lem3334413 _86990 _87026 s x t x' t' s')). Qed.
Lemma lem3334415 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) : (term929 _86990 _87026 s x t x' t' s') = (term944 _86990 _87026 s x t x' t' s').
Proof. exact (EQ_MP (@lem3334414 _86990 _87026 s x t x' t' s') (@lem3334399 _86990 _87026 s x t x' t' s')). Qed.
Lemma lem3334417 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3334418 {_87026 : Type'} (P : Prop) (Q : _87026 -> Prop) : (term638 _87026 P Q) = (term639 _87026 P Q).
Proof. exact (@lem3334417 _87026 P Q). Qed.
Lemma lem3334419 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) : (term945 _86990 _87026 s x t x' t' s' t'') = (term946 _86990 _87026 s x t x' t' s' t'').
Proof. exact (@lem3334418 _87026 (term650 _86990 s x t x' t') (term831 _87026 s' t'')). Qed.
Lemma lem3334420 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term947 _87026 s t x) = (term830 _87026 s t x).
Proof. exact (eq_refl (term947 _87026 s t x)). Qed.
Lemma lem3334421 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term948 _87026 s t) = (term831 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3334420 _87026 s t x)). Qed.
Lemma lem3334422 {_87026 : Type'} : (@ex _87026) = (@ex _87026).
Proof. exact (eq_refl (@ex _87026)). Qed.
Lemma lem3334423 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term949 _87026 s t) = (term832 _87026 s t).
Proof. exact (MK_COMB (@lem3334422 _87026) (@lem3334421 _87026 s t)). Qed.
Lemma lem3334424 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term913 _86990 s x t x' t') = (term913 _86990 s x t x' t').
Proof. exact (eq_refl (term913 _86990 s x t x' t')). Qed.
Lemma lem3334425 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) : (term945 _86990 _87026 s x t x' t' s' t'') = (term941 _86990 _87026 s x t x' t' s' t'').
Proof. exact (MK_COMB (@lem3334424 _86990 s x t x' t') (@lem3334423 _87026 s' t'')). Qed.
Lemma lem3334426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334427 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) : (term950 _86990 _87026 s x t x' t' s' t'') = (term951 _86990 _87026 s x t x' t' s' t'').
Proof. exact (MK_COMB (@lem3334426) (@lem3334425 _86990 _87026 s x t x' t' s' t'')). Qed.
Lemma lem3334428 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term947 _87026 s t x) = (term830 _87026 s t x).
Proof. exact (eq_refl (term947 _87026 s t x)). Qed.
Lemma lem3334429 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term913 _86990 s x t x' t') = (term913 _86990 s x t x' t').
Proof. exact (eq_refl (term913 _86990 s x t x' t')). Qed.
Lemma lem3334430 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term952 _86990 _87026 s x t x' t' s' t'' x'') = (term953 _86990 _87026 s x t x' t' s' t'' x'').
Proof. exact (MK_COMB (@lem3334429 _86990 s x t x' t') (@lem3334428 _87026 s' t'' x'')). Qed.
Lemma lem3334431 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) : (term954 _86990 _87026 s x t x' t' s' t'') = (term955 _86990 _87026 s x t x' t' s' t'').
Proof. exact (fun_ext (fun x'' : _87026 => @lem3334430 _86990 _87026 s x t x' t' s' t'' x'')). Qed.
Lemma lem3334432 {_87026 : Type'} : (@ex _87026) = (@ex _87026).
Proof. exact (eq_refl (@ex _87026)). Qed.
Lemma lem3334433 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) : (term946 _86990 _87026 s x t x' t' s' t'') = (term956 _86990 _87026 s x t x' t' s' t'').
Proof. exact (MK_COMB (@lem3334432 _87026) (@lem3334431 _86990 _87026 s x t x' t' s' t'')). Qed.
Lemma lem3334434 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) : ((term945 _86990 _87026 s x t x' t' s' t'') = (term946 _86990 _87026 s x t x' t' s' t'')) = ((term941 _86990 _87026 s x t x' t' s' t'') = (term956 _86990 _87026 s x t x' t' s' t'')).
Proof. exact (MK_COMB (@lem3334427 _86990 _87026 s x t x' t' s' t'') (@lem3334433 _86990 _87026 s x t x' t' s' t'')). Qed.
Lemma lem3334435 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) : (term941 _86990 _87026 s x t x' t' s' t'') = (term956 _86990 _87026 s x t x' t' s' t'').
Proof. exact (EQ_MP (@lem3334434 _86990 _87026 s x t x' t' s' t'') (@lem3334419 _86990 _87026 s x t x' t' s' t'')). Qed.
Lemma lem3334437 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3334438 {_87026 : Type'} (P : Prop) (Q : type686 _87026) : (term640 _87026 P Q) = (term641 _87026 P Q).
Proof. exact (@lem3334437 (_87026 -> Prop) P Q). Qed.
Lemma lem3334439 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term957 _86990 _87026 s x t x' t' s' t'' x'') = (term958 _86990 _87026 s x t x' t' s' t'' x'').
Proof. exact (@lem3334438 _87026 (term650 _86990 s x t x' t') (term829 _87026 s' t'' x'')). Qed.
Lemma lem3334440 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term959 _87026 s t x t') = (term828 _87026 s t x t').
Proof. exact (eq_refl (term959 _87026 s t x t')). Qed.
Lemma lem3334441 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term960 _87026 s t x) = (term829 _87026 s t x).
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3334440 _87026 s t x t')). Qed.
Lemma lem3334442 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334443 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) : (term961 _87026 s t x) = (term830 _87026 s t x).
Proof. exact (MK_COMB (@lem3334442 _87026) (@lem3334441 _87026 s t x)). Qed.
Lemma lem3334444 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term913 _86990 s x t x' t') = (term913 _86990 s x t x' t').
Proof. exact (eq_refl (term913 _86990 s x t x' t')). Qed.
Lemma lem3334445 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term957 _86990 _87026 s x t x' t' s' t'' x'') = (term953 _86990 _87026 s x t x' t' s' t'' x'').
Proof. exact (MK_COMB (@lem3334444 _86990 s x t x' t') (@lem3334443 _87026 s' t'' x'')). Qed.
Lemma lem3334446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334447 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term962 _86990 _87026 s x t x' t' s' t'' x'') = (term963 _86990 _87026 s x t x' t' s' t'' x'').
Proof. exact (MK_COMB (@lem3334446) (@lem3334445 _86990 _87026 s x t x' t' s' t'' x'')). Qed.
Lemma lem3334448 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term959 _87026 s t x t') = (term828 _87026 s t x t').
Proof. exact (eq_refl (term959 _87026 s t x t')). Qed.
Lemma lem3334449 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term913 _86990 s x t x' t') = (term913 _86990 s x t x' t').
Proof. exact (eq_refl (term913 _86990 s x t x' t')). Qed.
Lemma lem3334450 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) : (term964 _86990 _87026 s x t x' t' s' t'' x'' t''') = (term965 _86990 _87026 s x t x' t' s' t'' x'' t''').
Proof. exact (MK_COMB (@lem3334449 _86990 s x t x' t') (@lem3334448 _87026 s' t'' x'' t''')). Qed.
Lemma lem3334451 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term966 _86990 _87026 s x t x' t' s' t'' x'') = (term967 _86990 _87026 s x t x' t' s' t'' x'').
Proof. exact (fun_ext (fun t''' : _87026 -> Prop => @lem3334450 _86990 _87026 s x t x' t' s' t'' x'' t''')). Qed.
Lemma lem3334452 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334453 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term958 _86990 _87026 s x t x' t' s' t'' x'') = (term968 _86990 _87026 s x t x' t' s' t'' x'').
Proof. exact (MK_COMB (@lem3334452 _87026) (@lem3334451 _86990 _87026 s x t x' t' s' t'' x'')). Qed.
Lemma lem3334454 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : ((term957 _86990 _87026 s x t x' t' s' t'' x'') = (term958 _86990 _87026 s x t x' t' s' t'' x'')) = ((term953 _86990 _87026 s x t x' t' s' t'' x'') = (term968 _86990 _87026 s x t x' t' s' t'' x'')).
Proof. exact (MK_COMB (@lem3334447 _86990 _87026 s x t x' t' s' t'' x'') (@lem3334453 _86990 _87026 s x t x' t' s' t'' x'')). Qed.
Lemma lem3334455 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term953 _86990 _87026 s x t x' t' s' t'' x'') = (term968 _86990 _87026 s x t x' t' s' t'' x'').
Proof. exact (EQ_MP (@lem3334454 _86990 _87026 s x t x' t' s' t'' x'') (@lem3334439 _86990 _87026 s x t x' t' s' t'' x'')). Qed.
Lemma lem3334457 {A : Type'} (P : Prop) (Q : A -> Prop) : (term638 A P Q) = (term639 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3334458 {_87026 : Type'} (P : Prop) (Q : type686 _87026) : (term640 _87026 P Q) = (term641 _87026 P Q).
Proof. exact (@lem3334457 (_87026 -> Prop) P Q). Qed.
Lemma lem3334459 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) : (term969 _86990 _87026 s x t x' t' s' t'' x'' t''') = (term970 _86990 _87026 s x t x' t' s' t'' x'' t''').
Proof. exact (@lem3334458 _87026 (term650 _86990 s x t x' t') (term827 _87026 s' t'' x'' t''')). Qed.
Lemma lem3334460 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026 -> Prop) (x' : _87026) (t' : _87026 -> Prop) : (term971 _87026 s t x' t' x) = (term825 _87026 s t x x' t').
Proof. exact (eq_refl (term971 _87026 s t x' t' x)). Qed.
Lemma lem3334461 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term972 _87026 s t x t') = (term827 _87026 s t x t').
Proof. exact (fun_ext (fun x' : _87026 -> Prop => @lem3334460 _87026 s t x' x t')). Qed.
Lemma lem3334462 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334463 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026) (t' : _87026 -> Prop) : (term973 _87026 s t x t') = (term828 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334462 _87026) (@lem3334461 _87026 s t x t')). Qed.
Lemma lem3334464 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term913 _86990 s x t x' t') = (term913 _86990 s x t x' t').
Proof. exact (eq_refl (term913 _86990 s x t x' t')). Qed.
Lemma lem3334465 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) : (term969 _86990 _87026 s x t x' t' s' t'' x'' t''') = (term965 _86990 _87026 s x t x' t' s' t'' x'' t''').
Proof. exact (MK_COMB (@lem3334464 _86990 s x t x' t') (@lem3334463 _87026 s' t'' x'' t''')). Qed.
Lemma lem3334466 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334467 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) : (term974 _86990 _87026 s x t x' t' s' t'' x'' t''') = (term975 _86990 _87026 s x t x' t' s' t'' x'' t''').
Proof. exact (MK_COMB (@lem3334466) (@lem3334465 _86990 _87026 s x t x' t' s' t'' x'' t''')). Qed.
Lemma lem3334468 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) (x : _87026 -> Prop) (x' : _87026) (t' : _87026 -> Prop) : (term971 _87026 s t x' t' x) = (term825 _87026 s t x x' t').
Proof. exact (eq_refl (term971 _87026 s t x' t' x)). Qed.
Lemma lem3334469 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term913 _86990 s x t x' t') = (term913 _86990 s x t x' t').
Proof. exact (eq_refl (term913 _86990 s x t x' t')). Qed.
Lemma lem3334470 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026 -> Prop) (x''' : _87026) (t''' : _87026 -> Prop) : (term976 _86990 _87026 s x t x' t' s' t'' x''' t''' x'') = (term977 _86990 _87026 s x t x' t' s' t'' x'' x''' t''').
Proof. exact (MK_COMB (@lem3334469 _86990 s x t x' t') (@lem3334468 _87026 s' t'' x'' x''' t''')). Qed.
Lemma lem3334471 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) : (term978 _86990 _87026 s x t x' t' s' t'' x'' t''') = (term979 _86990 _87026 s x t x' t' s' t'' x'' t''').
Proof. exact (fun_ext (fun x''' : _87026 -> Prop => @lem3334470 _86990 _87026 s x t x' t' s' t'' x''' x'' t''')). Qed.
Lemma lem3334472 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334473 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) : (term970 _86990 _87026 s x t x' t' s' t'' x'' t''') = (term980 _86990 _87026 s x t x' t' s' t'' x'' t''').
Proof. exact (MK_COMB (@lem3334472 _87026) (@lem3334471 _86990 _87026 s x t x' t' s' t'' x'' t''')). Qed.
Lemma lem3334474 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) : ((term969 _86990 _87026 s x t x' t' s' t'' x'' t''') = (term970 _86990 _87026 s x t x' t' s' t'' x'' t''')) = ((term965 _86990 _87026 s x t x' t' s' t'' x'' t''') = (term980 _86990 _87026 s x t x' t' s' t'' x'' t''')).
Proof. exact (MK_COMB (@lem3334467 _86990 _87026 s x t x' t' s' t'' x'' t''') (@lem3334473 _86990 _87026 s x t x' t' s' t'' x'' t''')). Qed.
Lemma lem3334475 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) : (term965 _86990 _87026 s x t x' t' s' t'' x'' t''') = (term980 _86990 _87026 s x t x' t' s' t'' x'' t''').
Proof. exact (EQ_MP (@lem3334474 _86990 _87026 s x t x' t' s' t'' x'' t''') (@lem3334459 _86990 _87026 s x t x' t' s' t'' x'' t''')). Qed.
Lemma lem3334476 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term967 _86990 _87026 s x t x' t' s' t'' x'') = (term981 _86990 _87026 s x t x' t' s' t'' x'').
Proof. exact (fun_ext (fun t''' : _87026 -> Prop => @lem3334475 _86990 _87026 s x t x' t' s' t'' x'' t''')). Qed.
Lemma lem3334477 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334478 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term968 _86990 _87026 s x t x' t' s' t'' x'') = (term982 _86990 _87026 s x t x' t' s' t'' x'').
Proof. exact (MK_COMB (@lem3334477 _87026) (@lem3334476 _86990 _87026 s x t x' t' s' t'' x'')). Qed.
Lemma lem3334479 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term953 _86990 _87026 s x t x' t' s' t'' x'') = (term982 _86990 _87026 s x t x' t' s' t'' x'').
Proof. exact (TRANS (@lem3334455 _86990 _87026 s x t x' t' s' t'' x'') (@lem3334478 _86990 _87026 s x t x' t' s' t'' x'')). Qed.
Lemma lem3334480 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) : (term955 _86990 _87026 s x t x' t' s' t'') = (term983 _86990 _87026 s x t x' t' s' t'').
Proof. exact (fun_ext (fun x'' : _87026 => @lem3334479 _86990 _87026 s x t x' t' s' t'' x'')). Qed.
Lemma lem3334481 {_87026 : Type'} : (@ex _87026) = (@ex _87026).
Proof. exact (eq_refl (@ex _87026)). Qed.
Lemma lem3334482 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) : (term956 _86990 _87026 s x t x' t' s' t'') = (term984 _86990 _87026 s x t x' t' s' t'').
Proof. exact (MK_COMB (@lem3334481 _87026) (@lem3334480 _86990 _87026 s x t x' t' s' t'')). Qed.
Lemma lem3334483 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) : (term941 _86990 _87026 s x t x' t' s' t'') = (term984 _86990 _87026 s x t x' t' s' t'').
Proof. exact (TRANS (@lem3334435 _86990 _87026 s x t x' t' s' t'') (@lem3334482 _86990 _87026 s x t x' t' s' t'')). Qed.
Lemma lem3334484 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) : (term943 _86990 _87026 s x t x' t' s') = (term985 _86990 _87026 s x t x' t' s').
Proof. exact (fun_ext (fun t'' : _87026 -> Prop => @lem3334483 _86990 _87026 s x t x' t' s' t'')). Qed.
Lemma lem3334485 {_87026 : Type'} : (@ex (_87026 -> Prop)) = (@ex (_87026 -> Prop)).
Proof. exact (eq_refl (@ex (_87026 -> Prop))). Qed.
Lemma lem3334486 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) : (term944 _86990 _87026 s x t x' t' s') = (term986 _86990 _87026 s x t x' t' s').
Proof. exact (MK_COMB (@lem3334485 _87026) (@lem3334484 _86990 _87026 s x t x' t' s')). Qed.
Lemma lem3334487 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) : (term929 _86990 _87026 s x t x' t' s') = (term986 _86990 _87026 s x t x' t' s').
Proof. exact (TRANS (@lem3334415 _86990 _87026 s x t x' t' s') (@lem3334486 _86990 _87026 s x t x' t' s')). Qed.
Lemma lem3334488 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term931 _86990 _87026 s x t x' t') = (term987 _86990 _87026 s x t x' t').
Proof. exact (fun_ext (fun s' : type686 _87026 => @lem3334487 _86990 _87026 s x t x' t' s')). Qed.
Lemma lem3334489 {_87026 : Type'} : (@ex ((_87026 -> Prop) -> Prop)) = (@ex ((_87026 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87026 -> Prop) -> Prop))). Qed.
Lemma lem3334490 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term932 _86990 _87026 s x t x' t') = (term988 _86990 _87026 s x t x' t').
Proof. exact (MK_COMB (@lem3334489 _87026) (@lem3334488 _86990 _87026 s x t x' t')). Qed.
Lemma lem3334491 {_86990 _87026 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term915 _86990 _87026 s x t x' t') = (term988 _86990 _87026 s x t x' t').
Proof. exact (TRANS (@lem3334395 _86990 _87026 s x t x' t') (@lem3334490 _86990 _87026 s x t x' t')). Qed.
Lemma lem3334492 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term917 _86990 _87026 s t x t') = (term989 _86990 _87026 s t x t').
Proof. exact (fun_ext (fun x' : _86990 -> Prop => @lem3334491 _86990 _87026 s x' t x t')). Qed.
Lemma lem3334493 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3334494 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term918 _86990 _87026 s t x t') = (term990 _86990 _87026 s t x t').
Proof. exact (MK_COMB (@lem3334493 _86990) (@lem3334492 _86990 _87026 s t x t')). Qed.
Lemma lem3334495 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term900 _86990 _87026 s t x t') = (term990 _86990 _87026 s t x t').
Proof. exact (TRANS (@lem3334375 _86990 _87026 s t x t') (@lem3334494 _86990 _87026 s t x t')). Qed.
Lemma lem3334496 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term902 _86990 _87026 s t x) = (term991 _86990 _87026 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3334495 _86990 _87026 s t x t')). Qed.
Lemma lem3334497 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3334498 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term903 _86990 _87026 s t x) = (term992 _86990 _87026 s t x).
Proof. exact (MK_COMB (@lem3334497 _86990) (@lem3334496 _86990 _87026 s t x)). Qed.
Lemma lem3334499 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term885 _86990 _87026 s t x) = (term992 _86990 _87026 s t x).
Proof. exact (TRANS (@lem3334349 _86990 _87026 s t x) (@lem3334498 _86990 _87026 s t x)). Qed.
Lemma lem3334500 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term887 _86990 _87026 s t) = (term993 _86990 _87026 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3334499 _86990 _87026 s t x)). Qed.
Lemma lem3334501 {_86990 : Type'} : (@ex _86990) = (@ex _86990).
Proof. exact (eq_refl (@ex _86990)). Qed.
Lemma lem3334502 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term888 _86990 _87026 s t) = (term994 _86990 _87026 s t).
Proof. exact (MK_COMB (@lem3334501 _86990) (@lem3334500 _86990 _87026 s t)). Qed.
Lemma lem3334503 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term870 _86990 _87026 s t) = (term994 _86990 _87026 s t).
Proof. exact (TRANS (@lem3334323 _86990 _87026 s t) (@lem3334502 _86990 _87026 s t)). Qed.
Lemma lem3334504 {_86990 _87026 : Type'} (s : type686 _86990) : (term872 _86990 _87026 s) = (term995 _86990 _87026 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3334503 _86990 _87026 s t)). Qed.
Lemma lem3334505 {_86990 : Type'} : (@ex (_86990 -> Prop)) = (@ex (_86990 -> Prop)).
Proof. exact (eq_refl (@ex (_86990 -> Prop))). Qed.
Lemma lem3334506 {_86990 _87026 : Type'} (s : type686 _86990) : (term873 _86990 _87026 s) = (term996 _86990 _87026 s).
Proof. exact (MK_COMB (@lem3334505 _86990) (@lem3334504 _86990 _87026 s)). Qed.
Lemma lem3334507 {_86990 _87026 : Type'} (s : type686 _86990) : (term853 _86990 _87026 s) = (term996 _86990 _87026 s).
Proof. exact (TRANS (@lem3334297 _86990 _87026 s) (@lem3334506 _86990 _87026 s)). Qed.
Lemma lem3334508 {_86990 _87026 : Type'} : (term855 _86990 _87026) = (term997 _86990 _87026).
Proof. exact (fun_ext (fun s : type686 _86990 => @lem3334507 _86990 _87026 s)). Qed.
Lemma lem3334509 {_86990 : Type'} : (@ex ((_86990 -> Prop) -> Prop)) = (@ex ((_86990 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_86990 -> Prop) -> Prop))). Qed.
Lemma lem3334510 {_86990 _87026 : Type'} : (term856 _86990 _87026) = (term998 _86990 _87026).
Proof. exact (MK_COMB (@lem3334509 _86990) (@lem3334508 _86990 _87026)). Qed.
Lemma lem3334511 {_86990 _87026 : Type'} : (term837 _86990 _87026) = (term998 _86990 _87026).
Proof. exact (TRANS (@lem3334271 _86990 _87026) (@lem3334510 _86990 _87026)). Qed.
Lemma lem3334512 {_86990 _87026 : Type'} : (term470 _86990 _87026) = (term998 _86990 _87026).
Proof. exact (TRANS (@lem3334245 _86990 _87026) (@lem3334511 _86990 _87026)). Qed.
Lemma lem3334513 {_86990 _87026 : Type'} : (term334 _86990 _87026) = (term998 _86990 _87026).
Proof. exact (TRANS (@lem3333660 _86990 _87026) (@lem3334512 _86990 _87026)). Qed.
Lemma lem3334514 {_86990 _87026 : Type'} : (term165 _86990 _87026) = (term998 _86990 _87026).
Proof. exact (TRANS (@lem3331111 _86990 _87026) (@lem3334513 _86990 _87026)). Qed.
Lemma lem3334515 {_86990 _87026 : Type'} (h1 : term165 _86990 _87026) : term998 _86990 _87026.
Proof. exact (EQ_MP (@lem3334514 _86990 _87026) (@lem3330854 _86990 _87026 h1)). Qed.
Lemma lem3334526 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term999 _86990 s x t) = (term1000 _86990 s x t).
Proof. exact (@lem17045 (@IN _86990 x s) (@IN _86990 x t)). Qed.
Lemma lem3334532 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term1001 _86990 s x t) = (term1001 _86990 s x t).
Proof. exact (eq_refl (term1001 _86990 s x t)). Qed.
Lemma lem3334534 {_86990 : Type'} (x : _86990) (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1002 _86990 x s t) = (term1002 _86990 x s t).
Proof. exact (eq_refl (term1002 _86990 x s t)). Qed.
Lemma lem3334535 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term1003 _86990 s x t) = (term1004 _86990 s x t).
Proof. exact (MK_COMB (@lem3334534 _86990 x s t) (@lem3334526 _86990 s x t)). Qed.
Lemma lem3334536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3334537 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term1005 _86990 s x t) = (term1006 _86990 s x t).
Proof. exact (MK_COMB (@lem3334536) (@lem3334535 _86990 s x t)). Qed.
Lemma lem3334538 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term1007 _86990 s x t) = (term1008 _86990 s x t).
Proof. exact (MK_COMB (@lem3334537 _86990 s x t) (@lem3334532 _86990 s x t)). Qed.
Lemma lem3334539 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : ((term12 _86990 x s t) = (term13 _86990 s x t)) = (term1007 _86990 s x t).
Proof. exact (@lem17784 (term12 _86990 x s t) (term13 _86990 s x t)). Qed.
Lemma lem3334540 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : ((term12 _86990 x s t) = (term13 _86990 s x t)) = (term1008 _86990 s x t).
Proof. exact (TRANS (@lem3334539 _86990 s x t) (@lem3334538 _86990 s x t)). Qed.
Lemma lem3334541 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term191 _86990 s t) = (term1009 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3334540 _86990 s x t)). Qed.
Lemma lem3334542 {_86990 : Type'} : (@all _86990) = (@all _86990).
Proof. exact (eq_refl (@all _86990)). Qed.
Lemma lem3334543 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term10 _86990 s t) = (term1010 _86990 s t).
Proof. exact (MK_COMB (@lem3334542 _86990) (@lem3334541 _86990 s t)). Qed.
Lemma lem3334544 {_86990 : Type'} (s : _86990 -> Prop) : (term192 _86990 s) = (term1011 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3334543 _86990 s t)). Qed.
Lemma lem3334545 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3334546 {_86990 : Type'} (s : _86990 -> Prop) : (term8 _86990 s) = (term1012 _86990 s).
Proof. exact (MK_COMB (@lem3334545 _86990) (@lem3334544 _86990 s)). Qed.
Lemma lem3334547 {_86990 : Type'} : (term193 _86990) = (term1013 _86990).
Proof. exact (fun_ext (fun s : _86990 -> Prop => @lem3334546 _86990 s)). Qed.
Lemma lem3334548 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3334549 {_86990 : Type'} : (term167 _86990) = (term1014 _86990).
Proof. exact (MK_COMB (@lem3334548 _86990) (@lem3334547 _86990)). Qed.
Lemma lem3334559 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1015 A P Q) = (term1016 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3334560 {_86990 : Type'} (P : _86990 -> Prop) (Q : _86990 -> Prop) : (term1015 _86990 P Q) = (term1016 _86990 P Q).
Proof. exact (@lem3334559 _86990 P Q). Qed.
Lemma lem3334561 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1017 _86990 s t) = (term1018 _86990 s t).
Proof. exact (@lem3334560 _86990 (term1019 _86990 s t) (term1020 _86990 s t)). Qed.
Lemma lem3334562 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term1021 _86990 s t x) = (term1004 _86990 s x t).
Proof. exact (eq_refl (term1021 _86990 s t x)). Qed.
Lemma lem3334563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3334564 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term1022 _86990 s t x) = (term1006 _86990 s x t).
Proof. exact (MK_COMB (@lem3334563) (@lem3334562 _86990 s x t)). Qed.
Lemma lem3334565 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term1023 _86990 s t x) = (term1001 _86990 s x t).
Proof. exact (eq_refl (term1023 _86990 s t x)). Qed.
Lemma lem3334566 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term1024 _86990 s t x) = (term1008 _86990 s x t).
Proof. exact (MK_COMB (@lem3334564 _86990 s x t) (@lem3334565 _86990 s x t)). Qed.
Lemma lem3334567 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1025 _86990 s t) = (term1009 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3334566 _86990 s x t)). Qed.
Lemma lem3334568 {_86990 : Type'} : (@all _86990) = (@all _86990).
Proof. exact (eq_refl (@all _86990)). Qed.
Lemma lem3334569 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1017 _86990 s t) = (term1010 _86990 s t).
Proof. exact (MK_COMB (@lem3334568 _86990) (@lem3334567 _86990 s t)). Qed.
Lemma lem3334570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334571 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1026 _86990 s t) = (term1027 _86990 s t).
Proof. exact (MK_COMB (@lem3334570) (@lem3334569 _86990 s t)). Qed.
Lemma lem3334572 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term1021 _86990 s t x) = (term1004 _86990 s x t).
Proof. exact (eq_refl (term1021 _86990 s t x)). Qed.
Lemma lem3334573 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1028 _86990 s t) = (term1019 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3334572 _86990 s x t)). Qed.
Lemma lem3334574 {_86990 : Type'} : (@all _86990) = (@all _86990).
Proof. exact (eq_refl (@all _86990)). Qed.
Lemma lem3334575 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1029 _86990 s t) = (term1030 _86990 s t).
Proof. exact (MK_COMB (@lem3334574 _86990) (@lem3334573 _86990 s t)). Qed.
Lemma lem3334576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3334577 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1031 _86990 s t) = (term1032 _86990 s t).
Proof. exact (MK_COMB (@lem3334576) (@lem3334575 _86990 s t)). Qed.
Lemma lem3334578 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term1023 _86990 s t x) = (term1001 _86990 s x t).
Proof. exact (eq_refl (term1023 _86990 s t x)). Qed.
Lemma lem3334579 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1033 _86990 s t) = (term1020 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3334578 _86990 s x t)). Qed.
Lemma lem3334580 {_86990 : Type'} : (@all _86990) = (@all _86990).
Proof. exact (eq_refl (@all _86990)). Qed.
Lemma lem3334581 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1034 _86990 s t) = (term1035 _86990 s t).
Proof. exact (MK_COMB (@lem3334580 _86990) (@lem3334579 _86990 s t)). Qed.
Lemma lem3334582 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1018 _86990 s t) = (term1036 _86990 s t).
Proof. exact (MK_COMB (@lem3334577 _86990 s t) (@lem3334581 _86990 s t)). Qed.
Lemma lem3334583 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : ((term1017 _86990 s t) = (term1018 _86990 s t)) = ((term1010 _86990 s t) = (term1036 _86990 s t)).
Proof. exact (MK_COMB (@lem3334571 _86990 s t) (@lem3334582 _86990 s t)). Qed.
Lemma lem3334584 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1010 _86990 s t) = (term1036 _86990 s t).
Proof. exact (EQ_MP (@lem3334583 _86990 s t) (@lem3334561 _86990 s t)). Qed.
Lemma lem3334681 {_86990 : Type'} (s : _86990 -> Prop) : (term1011 _86990 s) = (term1037 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3334584 _86990 s t)). Qed.
Lemma lem3334682 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3334683 {_86990 : Type'} (s : _86990 -> Prop) : (term1012 _86990 s) = (term1038 _86990 s).
Proof. exact (MK_COMB (@lem3334682 _86990) (@lem3334681 _86990 s)). Qed.
Lemma lem3334685 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1015 A P Q) = (term1016 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3334686 {_86990 : Type'} (P : type686 _86990) (Q : type686 _86990) : (term1039 _86990 P Q) = (term1040 _86990 P Q).
Proof. exact (@lem3334685 (_86990 -> Prop) P Q). Qed.
Lemma lem3334687 {_86990 : Type'} (s : _86990 -> Prop) : (term1041 _86990 s) = (term1042 _86990 s).
Proof. exact (@lem3334686 _86990 (term1043 _86990 s) (term1044 _86990 s)). Qed.
Lemma lem3334688 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1045 _86990 s t) = (term1030 _86990 s t).
Proof. exact (eq_refl (term1045 _86990 s t)). Qed.
Lemma lem3334689 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3334690 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1046 _86990 s t) = (term1032 _86990 s t).
Proof. exact (MK_COMB (@lem3334689) (@lem3334688 _86990 s t)). Qed.
Lemma lem3334691 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1047 _86990 s t) = (term1035 _86990 s t).
Proof. exact (eq_refl (term1047 _86990 s t)). Qed.
Lemma lem3334692 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1048 _86990 s t) = (term1036 _86990 s t).
Proof. exact (MK_COMB (@lem3334690 _86990 s t) (@lem3334691 _86990 s t)). Qed.
Lemma lem3334693 {_86990 : Type'} (s : _86990 -> Prop) : (term1049 _86990 s) = (term1037 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3334692 _86990 s t)). Qed.
Lemma lem3334694 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3334695 {_86990 : Type'} (s : _86990 -> Prop) : (term1041 _86990 s) = (term1038 _86990 s).
Proof. exact (MK_COMB (@lem3334694 _86990) (@lem3334693 _86990 s)). Qed.
Lemma lem3334696 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334697 {_86990 : Type'} (s : _86990 -> Prop) : (term1050 _86990 s) = (term1051 _86990 s).
Proof. exact (MK_COMB (@lem3334696) (@lem3334695 _86990 s)). Qed.
Lemma lem3334698 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1045 _86990 s t) = (term1030 _86990 s t).
Proof. exact (eq_refl (term1045 _86990 s t)). Qed.
Lemma lem3334699 {_86990 : Type'} (s : _86990 -> Prop) : (term1052 _86990 s) = (term1043 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3334698 _86990 s t)). Qed.
Lemma lem3334700 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3334701 {_86990 : Type'} (s : _86990 -> Prop) : (term1053 _86990 s) = (term1054 _86990 s).
Proof. exact (MK_COMB (@lem3334700 _86990) (@lem3334699 _86990 s)). Qed.
Lemma lem3334702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3334703 {_86990 : Type'} (s : _86990 -> Prop) : (term1055 _86990 s) = (term1056 _86990 s).
Proof. exact (MK_COMB (@lem3334702) (@lem3334701 _86990 s)). Qed.
Lemma lem3334704 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1047 _86990 s t) = (term1035 _86990 s t).
Proof. exact (eq_refl (term1047 _86990 s t)). Qed.
Lemma lem3334705 {_86990 : Type'} (s : _86990 -> Prop) : (term1057 _86990 s) = (term1044 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3334704 _86990 s t)). Qed.
Lemma lem3334706 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3334707 {_86990 : Type'} (s : _86990 -> Prop) : (term1058 _86990 s) = (term1059 _86990 s).
Proof. exact (MK_COMB (@lem3334706 _86990) (@lem3334705 _86990 s)). Qed.
Lemma lem3334708 {_86990 : Type'} (s : _86990 -> Prop) : (term1042 _86990 s) = (term1060 _86990 s).
Proof. exact (MK_COMB (@lem3334703 _86990 s) (@lem3334707 _86990 s)). Qed.
Lemma lem3334709 {_86990 : Type'} (s : _86990 -> Prop) : ((term1041 _86990 s) = (term1042 _86990 s)) = ((term1038 _86990 s) = (term1060 _86990 s)).
Proof. exact (MK_COMB (@lem3334697 _86990 s) (@lem3334708 _86990 s)). Qed.
Lemma lem3334710 {_86990 : Type'} (s : _86990 -> Prop) : (term1038 _86990 s) = (term1060 _86990 s).
Proof. exact (EQ_MP (@lem3334709 _86990 s) (@lem3334687 _86990 s)). Qed.
Lemma lem3334815 {_86990 : Type'} (s : _86990 -> Prop) : (term1012 _86990 s) = (term1060 _86990 s).
Proof. exact (TRANS (@lem3334683 _86990 s) (@lem3334710 _86990 s)). Qed.
Lemma lem3334816 {_86990 : Type'} : (term1013 _86990) = (term1061 _86990).
Proof. exact (fun_ext (fun s : _86990 -> Prop => @lem3334815 _86990 s)). Qed.
Lemma lem3334817 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3334818 {_86990 : Type'} : (term1014 _86990) = (term1062 _86990).
Proof. exact (MK_COMB (@lem3334817 _86990) (@lem3334816 _86990)). Qed.
Lemma lem3334820 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1015 A P Q) = (term1016 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3334821 {_86990 : Type'} (P : type686 _86990) (Q : type686 _86990) : (term1039 _86990 P Q) = (term1040 _86990 P Q).
Proof. exact (@lem3334820 (_86990 -> Prop) P Q). Qed.
Lemma lem3334822 {_86990 : Type'} : (term1063 _86990) = (term1064 _86990).
Proof. exact (@lem3334821 _86990 (term1065 _86990) (term1066 _86990)). Qed.
Lemma lem3334823 {_86990 : Type'} (s : _86990 -> Prop) : (term1067 _86990 s) = (term1054 _86990 s).
Proof. exact (eq_refl (term1067 _86990 s)). Qed.
Lemma lem3334824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3334825 {_86990 : Type'} (s : _86990 -> Prop) : (term1068 _86990 s) = (term1056 _86990 s).
Proof. exact (MK_COMB (@lem3334824) (@lem3334823 _86990 s)). Qed.
Lemma lem3334826 {_86990 : Type'} (s : _86990 -> Prop) : (term1069 _86990 s) = (term1059 _86990 s).
Proof. exact (eq_refl (term1069 _86990 s)). Qed.
Lemma lem3334827 {_86990 : Type'} (s : _86990 -> Prop) : (term1070 _86990 s) = (term1060 _86990 s).
Proof. exact (MK_COMB (@lem3334825 _86990 s) (@lem3334826 _86990 s)). Qed.
Lemma lem3334828 {_86990 : Type'} : (term1071 _86990) = (term1061 _86990).
Proof. exact (fun_ext (fun s : _86990 -> Prop => @lem3334827 _86990 s)). Qed.
Lemma lem3334829 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3334830 {_86990 : Type'} : (term1063 _86990) = (term1062 _86990).
Proof. exact (MK_COMB (@lem3334829 _86990) (@lem3334828 _86990)). Qed.
Lemma lem3334831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3334832 {_86990 : Type'} : (term1072 _86990) = (term1073 _86990).
Proof. exact (MK_COMB (@lem3334831) (@lem3334830 _86990)). Qed.
Lemma lem3334833 {_86990 : Type'} (s : _86990 -> Prop) : (term1067 _86990 s) = (term1054 _86990 s).
Proof. exact (eq_refl (term1067 _86990 s)). Qed.
Lemma lem3334834 {_86990 : Type'} : (term1074 _86990) = (term1065 _86990).
Proof. exact (fun_ext (fun s : _86990 -> Prop => @lem3334833 _86990 s)). Qed.
Lemma lem3334835 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3334836 {_86990 : Type'} : (term1075 _86990) = (term1076 _86990).
Proof. exact (MK_COMB (@lem3334835 _86990) (@lem3334834 _86990)). Qed.
Lemma lem3334837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3334838 {_86990 : Type'} : (term1077 _86990) = (term1078 _86990).
Proof. exact (MK_COMB (@lem3334837) (@lem3334836 _86990)). Qed.
Lemma lem3334839 {_86990 : Type'} (s : _86990 -> Prop) : (term1069 _86990 s) = (term1059 _86990 s).
Proof. exact (eq_refl (term1069 _86990 s)). Qed.
Lemma lem3334840 {_86990 : Type'} : (term1079 _86990) = (term1066 _86990).
Proof. exact (fun_ext (fun s : _86990 -> Prop => @lem3334839 _86990 s)). Qed.
Lemma lem3334841 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3334842 {_86990 : Type'} : (term1080 _86990) = (term1081 _86990).
Proof. exact (MK_COMB (@lem3334841 _86990) (@lem3334840 _86990)). Qed.
Lemma lem3334843 {_86990 : Type'} : (term1064 _86990) = (term1082 _86990).
Proof. exact (MK_COMB (@lem3334838 _86990) (@lem3334842 _86990)). Qed.
Lemma lem3334844 {_86990 : Type'} : ((term1063 _86990) = (term1064 _86990)) = ((term1062 _86990) = (term1082 _86990)).
Proof. exact (MK_COMB (@lem3334832 _86990) (@lem3334843 _86990)). Qed.
Lemma lem3334845 {_86990 : Type'} : (term1062 _86990) = (term1082 _86990).
Proof. exact (EQ_MP (@lem3334844 _86990) (@lem3334822 _86990)). Qed.
Lemma lem3334960 {_86990 : Type'} : (term1014 _86990) = (term1082 _86990).
Proof. exact (TRANS (@lem3334818 _86990) (@lem3334845 _86990)). Qed.
Lemma lem3334961 {_86990 : Type'} : (term167 _86990) = (term1082 _86990).
Proof. exact (TRANS (@lem3334549 _86990) (@lem3334960 _86990)). Qed.
Lemma lem3334962 {_86990 : Type'} (h1 : term167 _86990) : term1082 _86990.
Proof. exact (EQ_MP (@lem3334961 _86990) (@lem3330855 _86990 h1)). Qed.
Lemma lem3334973 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term999 _87026 s x t) = (term1000 _87026 s x t).
Proof. exact (@lem17045 (@IN _87026 x s) (@IN _87026 x t)). Qed.
Lemma lem3334979 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term1001 _87026 s x t) = (term1001 _87026 s x t).
Proof. exact (eq_refl (term1001 _87026 s x t)). Qed.
Lemma lem3334981 {_87026 : Type'} (x : _87026) (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1002 _87026 x s t) = (term1002 _87026 x s t).
Proof. exact (eq_refl (term1002 _87026 x s t)). Qed.
Lemma lem3334982 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term1003 _87026 s x t) = (term1004 _87026 s x t).
Proof. exact (MK_COMB (@lem3334981 _87026 x s t) (@lem3334973 _87026 s x t)). Qed.
Lemma lem3334983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3334984 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term1005 _87026 s x t) = (term1006 _87026 s x t).
Proof. exact (MK_COMB (@lem3334983) (@lem3334982 _87026 s x t)). Qed.
Lemma lem3334985 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term1007 _87026 s x t) = (term1008 _87026 s x t).
Proof. exact (MK_COMB (@lem3334984 _87026 s x t) (@lem3334979 _87026 s x t)). Qed.
Lemma lem3334986 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : ((term12 _87026 x s t) = (term13 _87026 s x t)) = (term1007 _87026 s x t).
Proof. exact (@lem17784 (term12 _87026 x s t) (term13 _87026 s x t)). Qed.
Lemma lem3334987 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : ((term12 _87026 x s t) = (term13 _87026 s x t)) = (term1008 _87026 s x t).
Proof. exact (TRANS (@lem3334986 _87026 s x t) (@lem3334985 _87026 s x t)). Qed.
Lemma lem3334988 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term191 _87026 s t) = (term1009 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3334987 _87026 s x t)). Qed.
Lemma lem3334989 {_87026 : Type'} : (@all _87026) = (@all _87026).
Proof. exact (eq_refl (@all _87026)). Qed.
Lemma lem3334990 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term10 _87026 s t) = (term1010 _87026 s t).
Proof. exact (MK_COMB (@lem3334989 _87026) (@lem3334988 _87026 s t)). Qed.
Lemma lem3334991 {_87026 : Type'} (s : _87026 -> Prop) : (term192 _87026 s) = (term1011 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3334990 _87026 s t)). Qed.
Lemma lem3334992 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3334993 {_87026 : Type'} (s : _87026 -> Prop) : (term8 _87026 s) = (term1012 _87026 s).
Proof. exact (MK_COMB (@lem3334992 _87026) (@lem3334991 _87026 s)). Qed.
Lemma lem3334994 {_87026 : Type'} : (term193 _87026) = (term1013 _87026).
Proof. exact (fun_ext (fun s : _87026 -> Prop => @lem3334993 _87026 s)). Qed.
Lemma lem3334995 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3334996 {_87026 : Type'} : (term167 _87026) = (term1014 _87026).
Proof. exact (MK_COMB (@lem3334995 _87026) (@lem3334994 _87026)). Qed.
Lemma lem3335006 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1015 A P Q) = (term1016 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3335007 {_87026 : Type'} (P : _87026 -> Prop) (Q : _87026 -> Prop) : (term1015 _87026 P Q) = (term1016 _87026 P Q).
Proof. exact (@lem3335006 _87026 P Q). Qed.
Lemma lem3335008 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1017 _87026 s t) = (term1018 _87026 s t).
Proof. exact (@lem3335007 _87026 (term1019 _87026 s t) (term1020 _87026 s t)). Qed.
Lemma lem3335009 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term1021 _87026 s t x) = (term1004 _87026 s x t).
Proof. exact (eq_refl (term1021 _87026 s t x)). Qed.
Lemma lem3335010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3335011 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term1022 _87026 s t x) = (term1006 _87026 s x t).
Proof. exact (MK_COMB (@lem3335010) (@lem3335009 _87026 s x t)). Qed.
Lemma lem3335012 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term1023 _87026 s t x) = (term1001 _87026 s x t).
Proof. exact (eq_refl (term1023 _87026 s t x)). Qed.
Lemma lem3335013 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term1024 _87026 s t x) = (term1008 _87026 s x t).
Proof. exact (MK_COMB (@lem3335011 _87026 s x t) (@lem3335012 _87026 s x t)). Qed.
Lemma lem3335014 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1025 _87026 s t) = (term1009 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3335013 _87026 s x t)). Qed.
Lemma lem3335015 {_87026 : Type'} : (@all _87026) = (@all _87026).
Proof. exact (eq_refl (@all _87026)). Qed.
Lemma lem3335016 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1017 _87026 s t) = (term1010 _87026 s t).
Proof. exact (MK_COMB (@lem3335015 _87026) (@lem3335014 _87026 s t)). Qed.
Lemma lem3335017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3335018 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1026 _87026 s t) = (term1027 _87026 s t).
Proof. exact (MK_COMB (@lem3335017) (@lem3335016 _87026 s t)). Qed.
Lemma lem3335019 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term1021 _87026 s t x) = (term1004 _87026 s x t).
Proof. exact (eq_refl (term1021 _87026 s t x)). Qed.
Lemma lem3335020 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1028 _87026 s t) = (term1019 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3335019 _87026 s x t)). Qed.
Lemma lem3335021 {_87026 : Type'} : (@all _87026) = (@all _87026).
Proof. exact (eq_refl (@all _87026)). Qed.
Lemma lem3335022 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1029 _87026 s t) = (term1030 _87026 s t).
Proof. exact (MK_COMB (@lem3335021 _87026) (@lem3335020 _87026 s t)). Qed.
Lemma lem3335023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3335024 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1031 _87026 s t) = (term1032 _87026 s t).
Proof. exact (MK_COMB (@lem3335023) (@lem3335022 _87026 s t)). Qed.
Lemma lem3335025 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term1023 _87026 s t x) = (term1001 _87026 s x t).
Proof. exact (eq_refl (term1023 _87026 s t x)). Qed.
Lemma lem3335026 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1033 _87026 s t) = (term1020 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3335025 _87026 s x t)). Qed.
Lemma lem3335027 {_87026 : Type'} : (@all _87026) = (@all _87026).
Proof. exact (eq_refl (@all _87026)). Qed.
Lemma lem3335028 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1034 _87026 s t) = (term1035 _87026 s t).
Proof. exact (MK_COMB (@lem3335027 _87026) (@lem3335026 _87026 s t)). Qed.
Lemma lem3335029 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1018 _87026 s t) = (term1036 _87026 s t).
Proof. exact (MK_COMB (@lem3335024 _87026 s t) (@lem3335028 _87026 s t)). Qed.
Lemma lem3335030 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : ((term1017 _87026 s t) = (term1018 _87026 s t)) = ((term1010 _87026 s t) = (term1036 _87026 s t)).
Proof. exact (MK_COMB (@lem3335018 _87026 s t) (@lem3335029 _87026 s t)). Qed.
Lemma lem3335031 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1010 _87026 s t) = (term1036 _87026 s t).
Proof. exact (EQ_MP (@lem3335030 _87026 s t) (@lem3335008 _87026 s t)). Qed.
Lemma lem3335128 {_87026 : Type'} (s : _87026 -> Prop) : (term1011 _87026 s) = (term1037 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3335031 _87026 s t)). Qed.
Lemma lem3335129 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3335130 {_87026 : Type'} (s : _87026 -> Prop) : (term1012 _87026 s) = (term1038 _87026 s).
Proof. exact (MK_COMB (@lem3335129 _87026) (@lem3335128 _87026 s)). Qed.
Lemma lem3335132 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1015 A P Q) = (term1016 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3335133 {_87026 : Type'} (P : type686 _87026) (Q : type686 _87026) : (term1039 _87026 P Q) = (term1040 _87026 P Q).
Proof. exact (@lem3335132 (_87026 -> Prop) P Q). Qed.
Lemma lem3335134 {_87026 : Type'} (s : _87026 -> Prop) : (term1041 _87026 s) = (term1042 _87026 s).
Proof. exact (@lem3335133 _87026 (term1043 _87026 s) (term1044 _87026 s)). Qed.
Lemma lem3335135 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1045 _87026 s t) = (term1030 _87026 s t).
Proof. exact (eq_refl (term1045 _87026 s t)). Qed.
Lemma lem3335136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3335137 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1046 _87026 s t) = (term1032 _87026 s t).
Proof. exact (MK_COMB (@lem3335136) (@lem3335135 _87026 s t)). Qed.
Lemma lem3335138 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1047 _87026 s t) = (term1035 _87026 s t).
Proof. exact (eq_refl (term1047 _87026 s t)). Qed.
Lemma lem3335139 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1048 _87026 s t) = (term1036 _87026 s t).
Proof. exact (MK_COMB (@lem3335137 _87026 s t) (@lem3335138 _87026 s t)). Qed.
Lemma lem3335140 {_87026 : Type'} (s : _87026 -> Prop) : (term1049 _87026 s) = (term1037 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3335139 _87026 s t)). Qed.
Lemma lem3335141 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3335142 {_87026 : Type'} (s : _87026 -> Prop) : (term1041 _87026 s) = (term1038 _87026 s).
Proof. exact (MK_COMB (@lem3335141 _87026) (@lem3335140 _87026 s)). Qed.
Lemma lem3335143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3335144 {_87026 : Type'} (s : _87026 -> Prop) : (term1050 _87026 s) = (term1051 _87026 s).
Proof. exact (MK_COMB (@lem3335143) (@lem3335142 _87026 s)). Qed.
Lemma lem3335145 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1045 _87026 s t) = (term1030 _87026 s t).
Proof. exact (eq_refl (term1045 _87026 s t)). Qed.
Lemma lem3335146 {_87026 : Type'} (s : _87026 -> Prop) : (term1052 _87026 s) = (term1043 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3335145 _87026 s t)). Qed.
Lemma lem3335147 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3335148 {_87026 : Type'} (s : _87026 -> Prop) : (term1053 _87026 s) = (term1054 _87026 s).
Proof. exact (MK_COMB (@lem3335147 _87026) (@lem3335146 _87026 s)). Qed.
Lemma lem3335149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3335150 {_87026 : Type'} (s : _87026 -> Prop) : (term1055 _87026 s) = (term1056 _87026 s).
Proof. exact (MK_COMB (@lem3335149) (@lem3335148 _87026 s)). Qed.
Lemma lem3335151 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1047 _87026 s t) = (term1035 _87026 s t).
Proof. exact (eq_refl (term1047 _87026 s t)). Qed.
Lemma lem3335152 {_87026 : Type'} (s : _87026 -> Prop) : (term1057 _87026 s) = (term1044 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3335151 _87026 s t)). Qed.
Lemma lem3335153 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3335154 {_87026 : Type'} (s : _87026 -> Prop) : (term1058 _87026 s) = (term1059 _87026 s).
Proof. exact (MK_COMB (@lem3335153 _87026) (@lem3335152 _87026 s)). Qed.
Lemma lem3335155 {_87026 : Type'} (s : _87026 -> Prop) : (term1042 _87026 s) = (term1060 _87026 s).
Proof. exact (MK_COMB (@lem3335150 _87026 s) (@lem3335154 _87026 s)). Qed.
Lemma lem3335156 {_87026 : Type'} (s : _87026 -> Prop) : ((term1041 _87026 s) = (term1042 _87026 s)) = ((term1038 _87026 s) = (term1060 _87026 s)).
Proof. exact (MK_COMB (@lem3335144 _87026 s) (@lem3335155 _87026 s)). Qed.
Lemma lem3335157 {_87026 : Type'} (s : _87026 -> Prop) : (term1038 _87026 s) = (term1060 _87026 s).
Proof. exact (EQ_MP (@lem3335156 _87026 s) (@lem3335134 _87026 s)). Qed.
Lemma lem3335262 {_87026 : Type'} (s : _87026 -> Prop) : (term1012 _87026 s) = (term1060 _87026 s).
Proof. exact (TRANS (@lem3335130 _87026 s) (@lem3335157 _87026 s)). Qed.
Lemma lem3335263 {_87026 : Type'} : (term1013 _87026) = (term1061 _87026).
Proof. exact (fun_ext (fun s : _87026 -> Prop => @lem3335262 _87026 s)). Qed.
Lemma lem3335264 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3335265 {_87026 : Type'} : (term1014 _87026) = (term1062 _87026).
Proof. exact (MK_COMB (@lem3335264 _87026) (@lem3335263 _87026)). Qed.
Lemma lem3335267 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1015 A P Q) = (term1016 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3335268 {_87026 : Type'} (P : type686 _87026) (Q : type686 _87026) : (term1039 _87026 P Q) = (term1040 _87026 P Q).
Proof. exact (@lem3335267 (_87026 -> Prop) P Q). Qed.
Lemma lem3335269 {_87026 : Type'} : (term1063 _87026) = (term1064 _87026).
Proof. exact (@lem3335268 _87026 (term1065 _87026) (term1066 _87026)). Qed.
Lemma lem3335270 {_87026 : Type'} (s : _87026 -> Prop) : (term1067 _87026 s) = (term1054 _87026 s).
Proof. exact (eq_refl (term1067 _87026 s)). Qed.
Lemma lem3335271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3335272 {_87026 : Type'} (s : _87026 -> Prop) : (term1068 _87026 s) = (term1056 _87026 s).
Proof. exact (MK_COMB (@lem3335271) (@lem3335270 _87026 s)). Qed.
Lemma lem3335273 {_87026 : Type'} (s : _87026 -> Prop) : (term1069 _87026 s) = (term1059 _87026 s).
Proof. exact (eq_refl (term1069 _87026 s)). Qed.
Lemma lem3335274 {_87026 : Type'} (s : _87026 -> Prop) : (term1070 _87026 s) = (term1060 _87026 s).
Proof. exact (MK_COMB (@lem3335272 _87026 s) (@lem3335273 _87026 s)). Qed.
Lemma lem3335275 {_87026 : Type'} : (term1071 _87026) = (term1061 _87026).
Proof. exact (fun_ext (fun s : _87026 -> Prop => @lem3335274 _87026 s)). Qed.
Lemma lem3335276 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3335277 {_87026 : Type'} : (term1063 _87026) = (term1062 _87026).
Proof. exact (MK_COMB (@lem3335276 _87026) (@lem3335275 _87026)). Qed.
Lemma lem3335278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3335279 {_87026 : Type'} : (term1072 _87026) = (term1073 _87026).
Proof. exact (MK_COMB (@lem3335278) (@lem3335277 _87026)). Qed.
Lemma lem3335280 {_87026 : Type'} (s : _87026 -> Prop) : (term1067 _87026 s) = (term1054 _87026 s).
Proof. exact (eq_refl (term1067 _87026 s)). Qed.
Lemma lem3335281 {_87026 : Type'} : (term1074 _87026) = (term1065 _87026).
Proof. exact (fun_ext (fun s : _87026 -> Prop => @lem3335280 _87026 s)). Qed.
Lemma lem3335282 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3335283 {_87026 : Type'} : (term1075 _87026) = (term1076 _87026).
Proof. exact (MK_COMB (@lem3335282 _87026) (@lem3335281 _87026)). Qed.
Lemma lem3335284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3335285 {_87026 : Type'} : (term1077 _87026) = (term1078 _87026).
Proof. exact (MK_COMB (@lem3335284) (@lem3335283 _87026)). Qed.
Lemma lem3335286 {_87026 : Type'} (s : _87026 -> Prop) : (term1069 _87026 s) = (term1059 _87026 s).
Proof. exact (eq_refl (term1069 _87026 s)). Qed.
Lemma lem3335287 {_87026 : Type'} : (term1079 _87026) = (term1066 _87026).
Proof. exact (fun_ext (fun s : _87026 -> Prop => @lem3335286 _87026 s)). Qed.
Lemma lem3335288 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3335289 {_87026 : Type'} : (term1080 _87026) = (term1081 _87026).
Proof. exact (MK_COMB (@lem3335288 _87026) (@lem3335287 _87026)). Qed.
Lemma lem3335290 {_87026 : Type'} : (term1064 _87026) = (term1082 _87026).
Proof. exact (MK_COMB (@lem3335285 _87026) (@lem3335289 _87026)). Qed.
Lemma lem3335291 {_87026 : Type'} : ((term1063 _87026) = (term1064 _87026)) = ((term1062 _87026) = (term1082 _87026)).
Proof. exact (MK_COMB (@lem3335279 _87026) (@lem3335290 _87026)). Qed.
Lemma lem3335292 {_87026 : Type'} : (term1062 _87026) = (term1082 _87026).
Proof. exact (EQ_MP (@lem3335291 _87026) (@lem3335269 _87026)). Qed.
Lemma lem3335407 {_87026 : Type'} : (term1014 _87026) = (term1082 _87026).
Proof. exact (TRANS (@lem3335265 _87026) (@lem3335292 _87026)). Qed.
Lemma lem3335408 {_87026 : Type'} : (term167 _87026) = (term1082 _87026).
Proof. exact (TRANS (@lem3334996 _87026) (@lem3335407 _87026)). Qed.
Lemma lem3335409 {_87026 : Type'} (h1 : term167 _87026) : term1082 _87026.
Proof. exact (EQ_MP (@lem3335408 _87026) (@lem3330856 _87026 h1)). Qed.
Lemma lem3336304 {_86990 _87026 : Type'} (s : type686 _86990) (h1 : term996 _86990 _87026 s) : term996 _86990 _87026 s.
Proof. exact (h1). Qed.
Lemma lem3336305 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (h1 : term994 _86990 _87026 s t) : term994 _86990 _87026 s t.
Proof. exact (h1). Qed.
Lemma lem3336306 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term992 _86990 _87026 s t x) : term992 _86990 _87026 s t x.
Proof. exact (h1). Qed.
Lemma lem3336307 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term990 _86990 _87026 s t x t') : term990 _86990 _87026 s t x t'.
Proof. exact (h1). Qed.
Lemma lem3336308 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term988 _86990 _87026 s x' t x t') : term988 _86990 _87026 s x' t x t'.
Proof. exact (h1). Qed.
Lemma lem3336309 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (h1 : term986 _86990 _87026 s x' t x t' s') : term986 _86990 _87026 s x' t x t' s'.
Proof. exact (h1). Qed.
Lemma lem3336310 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (h1 : term984 _86990 _87026 s x' t x t' s' t'') : term984 _86990 _87026 s x' t x t' s' t''.
Proof. exact (h1). Qed.
Lemma lem3336311 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term982 _86990 _87026 s x' t x t' s' t'' x'') : term982 _86990 _87026 s x' t x t' s' t'' x''.
Proof. exact (h1). Qed.
Lemma lem3336312 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term980 _86990 _87026 s x' t x t' s' t'' x'' t''') : term980 _86990 _87026 s x' t x t' s' t'' x'' t'''.
Proof. exact (h1). Qed.
Lemma lem3336313 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term977 _86990 _87026 s x' t x t' s' t'' x''' x'' t''') : term977 _86990 _87026 s x' t x t' s' t'' x''' x'' t'''.
Proof. exact (h1). Qed.
Lemma lem3336340 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term1001 _86990 s x t) = (term1001 _86990 s x t).
Proof. exact (eq_refl (term1001 _86990 s x t)). Qed.
Lemma lem3336341 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1020 _86990 s t) = (term1020 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3336340 _86990 s x t)). Qed.
Lemma lem3336342 {_86990 : Type'} : (@all _86990) = (@all _86990).
Proof. exact (eq_refl (@all _86990)). Qed.
Lemma lem3336343 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1035 _86990 s t) = (term1035 _86990 s t).
Proof. exact (MK_COMB (@lem3336342 _86990) (@lem3336341 _86990 s t)). Qed.
Lemma lem3336344 {_86990 : Type'} (s : _86990 -> Prop) : (term1044 _86990 s) = (term1044 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3336343 _86990 s t)). Qed.
Lemma lem3336345 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3336346 {_86990 : Type'} (s : _86990 -> Prop) : (term1059 _86990 s) = (term1059 _86990 s).
Proof. exact (MK_COMB (@lem3336345 _86990) (@lem3336344 _86990 s)). Qed.
Lemma lem3336347 {_86990 : Type'} : (term1066 _86990) = (term1066 _86990).
Proof. exact (fun_ext (fun s : _86990 -> Prop => @lem3336346 _86990 s)). Qed.
Lemma lem3336348 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3336349 {_86990 : Type'} : (term1081 _86990) = (term1081 _86990).
Proof. exact (MK_COMB (@lem3336348 _86990) (@lem3336347 _86990)). Qed.
Lemma lem3336378 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term1004 _86990 s x t) = (term1004 _86990 s x t).
Proof. exact (eq_refl (term1004 _86990 s x t)). Qed.
Lemma lem3336379 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1019 _86990 s t) = (term1019 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3336378 _86990 s x t)). Qed.
Lemma lem3336380 {_86990 : Type'} : (@all _86990) = (@all _86990).
Proof. exact (eq_refl (@all _86990)). Qed.
Lemma lem3336381 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1030 _86990 s t) = (term1030 _86990 s t).
Proof. exact (MK_COMB (@lem3336380 _86990) (@lem3336379 _86990 s t)). Qed.
Lemma lem3336382 {_86990 : Type'} (s : _86990 -> Prop) : (term1043 _86990 s) = (term1043 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3336381 _86990 s t)). Qed.
Lemma lem3336383 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3336384 {_86990 : Type'} (s : _86990 -> Prop) : (term1054 _86990 s) = (term1054 _86990 s).
Proof. exact (MK_COMB (@lem3336383 _86990) (@lem3336382 _86990 s)). Qed.
Lemma lem3336385 {_86990 : Type'} : (term1065 _86990) = (term1065 _86990).
Proof. exact (fun_ext (fun s : _86990 -> Prop => @lem3336384 _86990 s)). Qed.
Lemma lem3336386 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3336387 {_86990 : Type'} : (term1076 _86990) = (term1076 _86990).
Proof. exact (MK_COMB (@lem3336386 _86990) (@lem3336385 _86990)). Qed.
Lemma lem3336388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3336389 {_86990 : Type'} : (term1078 _86990) = (term1078 _86990).
Proof. exact (MK_COMB (@lem3336388) (@lem3336387 _86990)). Qed.
Lemma lem3336390 {_86990 : Type'} : (term1082 _86990) = (term1082 _86990).
Proof. exact (MK_COMB (@lem3336389 _86990) (@lem3336349 _86990)). Qed.
Lemma lem3336391 {_86990 : Type'} (h1 : term167 _86990) : term1082 _86990.
Proof. exact (EQ_MP (@lem3336390 _86990) (@lem3334962 _86990 h1)). Qed.
Lemma lem3336418 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term1001 _87026 s x t) = (term1001 _87026 s x t).
Proof. exact (eq_refl (term1001 _87026 s x t)). Qed.
Lemma lem3336419 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1020 _87026 s t) = (term1020 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3336418 _87026 s x t)). Qed.
Lemma lem3336420 {_87026 : Type'} : (@all _87026) = (@all _87026).
Proof. exact (eq_refl (@all _87026)). Qed.
Lemma lem3336421 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1035 _87026 s t) = (term1035 _87026 s t).
Proof. exact (MK_COMB (@lem3336420 _87026) (@lem3336419 _87026 s t)). Qed.
Lemma lem3336422 {_87026 : Type'} (s : _87026 -> Prop) : (term1044 _87026 s) = (term1044 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3336421 _87026 s t)). Qed.
Lemma lem3336423 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3336424 {_87026 : Type'} (s : _87026 -> Prop) : (term1059 _87026 s) = (term1059 _87026 s).
Proof. exact (MK_COMB (@lem3336423 _87026) (@lem3336422 _87026 s)). Qed.
Lemma lem3336425 {_87026 : Type'} : (term1066 _87026) = (term1066 _87026).
Proof. exact (fun_ext (fun s : _87026 -> Prop => @lem3336424 _87026 s)). Qed.
Lemma lem3336426 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3336427 {_87026 : Type'} : (term1081 _87026) = (term1081 _87026).
Proof. exact (MK_COMB (@lem3336426 _87026) (@lem3336425 _87026)). Qed.
Lemma lem3336456 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term1004 _87026 s x t) = (term1004 _87026 s x t).
Proof. exact (eq_refl (term1004 _87026 s x t)). Qed.
Lemma lem3336457 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1019 _87026 s t) = (term1019 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3336456 _87026 s x t)). Qed.
Lemma lem3336458 {_87026 : Type'} : (@all _87026) = (@all _87026).
Proof. exact (eq_refl (@all _87026)). Qed.
Lemma lem3336459 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1030 _87026 s t) = (term1030 _87026 s t).
Proof. exact (MK_COMB (@lem3336458 _87026) (@lem3336457 _87026 s t)). Qed.
Lemma lem3336460 {_87026 : Type'} (s : _87026 -> Prop) : (term1043 _87026 s) = (term1043 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3336459 _87026 s t)). Qed.
Lemma lem3336461 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3336462 {_87026 : Type'} (s : _87026 -> Prop) : (term1054 _87026 s) = (term1054 _87026 s).
Proof. exact (MK_COMB (@lem3336461 _87026) (@lem3336460 _87026 s)). Qed.
Lemma lem3336463 {_87026 : Type'} : (term1065 _87026) = (term1065 _87026).
Proof. exact (fun_ext (fun s : _87026 -> Prop => @lem3336462 _87026 s)). Qed.
Lemma lem3336464 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3336465 {_87026 : Type'} : (term1076 _87026) = (term1076 _87026).
Proof. exact (MK_COMB (@lem3336464 _87026) (@lem3336463 _87026)). Qed.
Lemma lem3336466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3336467 {_87026 : Type'} : (term1078 _87026) = (term1078 _87026).
Proof. exact (MK_COMB (@lem3336466) (@lem3336465 _87026)). Qed.
Lemma lem3336468 {_87026 : Type'} : (term1082 _87026) = (term1082 _87026).
Proof. exact (MK_COMB (@lem3336467 _87026) (@lem3336427 _87026)). Qed.
Lemma lem3336469 {_87026 : Type'} (h1 : term167 _87026) : term1082 _87026.
Proof. exact (EQ_MP (@lem3336468 _87026) (@lem3335409 _87026 h1)). Qed.
Lemma lem3336650 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) : (term705 _87026 s' t'' x''' x'' t''') = (term705 _87026 s' t'' x''' x'' t''').
Proof. exact (eq_refl (term705 _87026 s' t'' x''' x'' t''')). Qed.
Lemma lem3336667 {_87026 : Type'} (s' : type686 _87026) (x'' : _87026) (t : _87026 -> Prop) : (term197 _87026 s' x'' t) = (term197 _87026 s' x'' t).
Proof. exact (eq_refl (term197 _87026 s' x'' t)). Qed.
Lemma lem3336668 {_87026 : Type'} (s' : type686 _87026) (x'' : _87026) : (term205 _87026 s' x'') = (term205 _87026 s' x'').
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3336667 _87026 s' x'' t)). Qed.
Lemma lem3336669 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3336670 {_87026 : Type'} (s' : type686 _87026) (x'' : _87026) : (term206 _87026 s' x'') = (term206 _87026 s' x'').
Proof. exact (MK_COMB (@lem3336669 _87026) (@lem3336668 _87026 s' x'')). Qed.
Lemma lem3336679 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) : (term273 _87026 x'' t'') = (term273 _87026 x'' t'').
Proof. exact (eq_refl (term273 _87026 x'' t'')). Qed.
Lemma lem3336680 {_87026 : Type'} (t'' : _87026 -> Prop) (s' : type686 _87026) (x'' : _87026) : (term275 _87026 t'' s' x'') = (term275 _87026 t'' s' x'').
Proof. exact (MK_COMB (@lem3336679 _87026 x'' t'') (@lem3336670 _87026 s' x'')). Qed.
Lemma lem3336681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3336682 {_87026 : Type'} (t'' : _87026 -> Prop) (s' : type686 _87026) (x'' : _87026) : (term299 _87026 t'' s' x'') = (term299 _87026 t'' s' x'').
Proof. exact (MK_COMB (@lem3336681) (@lem3336680 _87026 t'' s' x'')). Qed.
Lemma lem3336683 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) : (term732 _87026 s' t'' x''' x'' t''') = (term732 _87026 s' t'' x''' x'' t''').
Proof. exact (MK_COMB (@lem3336682 _87026 t'' s' x'') (@lem3336650 _87026 s' t'' x''' x'' t''')). Qed.
Lemma lem3336690 {_87026 : Type'} (x'' : _87026) (t' : _87026 -> Prop) : (term207 _87026 x'' t') = (term207 _87026 x'' t').
Proof. exact (eq_refl (term207 _87026 x'' t')). Qed.
Lemma lem3336711 {_87026 : Type'} (s' : type686 _87026) (t' : _87026 -> Prop) (t'' : _87026 -> Prop) (x : _87026 -> Prop) : (term278 _87026 s' t' t'' x) = (term278 _87026 s' t' t'' x).
Proof. exact (eq_refl (term278 _87026 s' t' t'' x)). Qed.
Lemma lem3336712 {_87026 : Type'} (s' : type686 _87026) (t' : _87026 -> Prop) (t'' : _87026 -> Prop) : (term284 _87026 s' t' t'') = (term284 _87026 s' t' t'').
Proof. exact (fun_ext (fun x : _87026 -> Prop => @lem3336711 _87026 s' t' t'' x)). Qed.
Lemma lem3336713 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3336714 {_87026 : Type'} (s' : type686 _87026) (t' : _87026 -> Prop) (t'' : _87026 -> Prop) : (term285 _87026 s' t' t'') = (term285 _87026 s' t' t'').
Proof. exact (MK_COMB (@lem3336713 _87026) (@lem3336712 _87026 s' t' t'')). Qed.
Lemma lem3336715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3336716 {_87026 : Type'} (s' : type686 _87026) (t' : _87026 -> Prop) (t'' : _87026 -> Prop) : (term287 _87026 s' t' t'') = (term287 _87026 s' t' t'').
Proof. exact (MK_COMB (@lem3336715) (@lem3336714 _87026 s' t' t'')). Qed.
Lemma lem3336717 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t' : _87026 -> Prop) : (term289 _87026 s' t'' x'' t') = (term289 _87026 s' t'' x'' t').
Proof. exact (MK_COMB (@lem3336716 _87026 s' t' t'') (@lem3336690 _87026 x'' t')). Qed.
Lemma lem3336718 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term296 _87026 s' t'' x'') = (term296 _87026 s' t'' x'').
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3336717 _87026 s' t'' x'' t')). Qed.
Lemma lem3336719 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3336720 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term297 _87026 s' t'' x'') = (term297 _87026 s' t'' x'').
Proof. exact (MK_COMB (@lem3336719 _87026) (@lem3336718 _87026 s' t'' x'')). Qed.
Lemma lem3336743 {_87026 : Type'} (t'' : _87026 -> Prop) (s' : type686 _87026) (x'' : _87026) (t''' : _87026 -> Prop) : (term682 _87026 t'' s' x'' t''') = (term682 _87026 t'' s' x'' t''').
Proof. exact (eq_refl (term682 _87026 t'' s' x'' t''')). Qed.
Lemma lem3336744 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term684 _87026 t''' s' t'' x'') = (term684 _87026 t''' s' t'' x'').
Proof. exact (MK_COMB (@lem3336743 _87026 t'' s' x'' t''') (@lem3336720 _87026 s' t'' x'')). Qed.
Lemma lem3336745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3336746 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term811 _87026 t''' s' t'' x'') = (term811 _87026 t''' s' t'' x'').
Proof. exact (MK_COMB (@lem3336745) (@lem3336744 _87026 t''' s' t'' x'')). Qed.
Lemma lem3336747 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) : (term825 _87026 s' t'' x''' x'' t''') = (term825 _87026 s' t'' x''' x'' t''').
Proof. exact (MK_COMB (@lem3336746 _87026 t''' s' t'' x'') (@lem3336683 _87026 s' t'' x''' x'' t''')). Qed.
Lemma lem3336772 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term522 _86990 s x' t x t') = (term522 _86990 s x' t x t').
Proof. exact (eq_refl (term522 _86990 s x' t x t')). Qed.
Lemma lem3336779 {_86990 : Type'} (x : _86990) (t : _86990 -> Prop) : (term207 _86990 x t) = (term207 _86990 x t).
Proof. exact (eq_refl (term207 _86990 x t)). Qed.
Lemma lem3336796 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term197 _86990 s x t) = (term197 _86990 s x t).
Proof. exact (eq_refl (term197 _86990 s x t)). Qed.
Lemma lem3336797 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term205 _86990 s x) = (term205 _86990 s x).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3336796 _86990 s x t)). Qed.
Lemma lem3336798 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3336799 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term206 _86990 s x) = (term206 _86990 s x).
Proof. exact (MK_COMB (@lem3336798 _86990) (@lem3336797 _86990 s x)). Qed.
Lemma lem3336800 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3336801 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term209 _86990 s x) = (term209 _86990 s x).
Proof. exact (MK_COMB (@lem3336800) (@lem3336799 _86990 s x)). Qed.
Lemma lem3336802 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term211 _86990 s x t) = (term211 _86990 s x t).
Proof. exact (MK_COMB (@lem3336801 _86990 s x) (@lem3336779 _86990 x t)). Qed.
Lemma lem3336803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3336804 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term235 _86990 s x t) = (term235 _86990 s x t).
Proof. exact (MK_COMB (@lem3336803) (@lem3336802 _86990 s x t)). Qed.
Lemma lem3336805 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term553 _86990 s x' t x t') = (term553 _86990 s x' t x t').
Proof. exact (MK_COMB (@lem3336804 _86990 s x t) (@lem3336772 _86990 s x' t x t')). Qed.
Lemma lem3336812 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (term207 _86990 x t') = (term207 _86990 x t').
Proof. exact (eq_refl (term207 _86990 x t')). Qed.
Lemma lem3336833 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term214 _86990 s t' x t) = (term214 _86990 s t' x t).
Proof. exact (eq_refl (term214 _86990 s t' x t)). Qed.
Lemma lem3336834 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term220 _86990 s t' t) = (term220 _86990 s t' t).
Proof. exact (fun_ext (fun x : _86990 -> Prop => @lem3336833 _86990 s t' x t)). Qed.
Lemma lem3336835 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3336836 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term221 _86990 s t' t) = (term221 _86990 s t' t).
Proof. exact (MK_COMB (@lem3336835 _86990) (@lem3336834 _86990 s t' t)). Qed.
Lemma lem3336837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3336838 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term223 _86990 s t' t) = (term223 _86990 s t' t).
Proof. exact (MK_COMB (@lem3336837) (@lem3336836 _86990 s t' t)). Qed.
Lemma lem3336839 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term225 _86990 s t x t') = (term225 _86990 s t x t').
Proof. exact (MK_COMB (@lem3336838 _86990 s t' t) (@lem3336812 _86990 x t')). Qed.
Lemma lem3336840 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term232 _86990 s t x) = (term232 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3336839 _86990 s t x t')). Qed.
Lemma lem3336841 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3336842 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term233 _86990 s t x) = (term233 _86990 s t x).
Proof. exact (MK_COMB (@lem3336841 _86990) (@lem3336840 _86990 s t x)). Qed.
Lemma lem3336865 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term499 _86990 s t' x t) = (term499 _86990 s t' x t).
Proof. exact (eq_refl (term499 _86990 s t' x t)). Qed.
Lemma lem3336866 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term501 _86990 t' s t x) = (term501 _86990 t' s t x).
Proof. exact (MK_COMB (@lem3336865 _86990 s t' x t) (@lem3336842 _86990 s t x)). Qed.
Lemma lem3336867 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3336868 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term632 _86990 t' s t x) = (term632 _86990 t' s t x).
Proof. exact (MK_COMB (@lem3336867) (@lem3336866 _86990 t' s t x)). Qed.
Lemma lem3336869 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term650 _86990 s x' t x t') = (term650 _86990 s x' t x t').
Proof. exact (MK_COMB (@lem3336868 _86990 t' s t x) (@lem3336805 _86990 s x' t x t')). Qed.
Lemma lem3336870 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3336871 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term913 _86990 s x' t x t') = (term913 _86990 s x' t x t').
Proof. exact (MK_COMB (@lem3336870) (@lem3336869 _86990 s x' t x t')). Qed.
Lemma lem3336872 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) : (term977 _86990 _87026 s x' t x t' s' t'' x''' x'' t''') = (term977 _86990 _87026 s x' t x t' s' t'' x''' x'' t''').
Proof. exact (MK_COMB (@lem3336871 _86990 s x' t x t') (@lem3336747 _87026 s' t'' x''' x'' t''')). Qed.
Lemma lem3336873 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term977 _86990 _87026 s x' t x t' s' t'' x''' x'' t''') : term977 _86990 _87026 s x' t x t' s' t'' x''' x'' t'''.
Proof. exact (EQ_MP (@lem3336872 _86990 _87026 s x' t x t' s' t'' x''' x'' t''') (@lem3336313 _86990 _87026 s x' t x t' s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3336878 {_87026 : Type'} (h1 : term167 _87026) : term1081 _87026.
Proof. exact (proj2 (@lem3336469 _87026 h1)). Qed.
Lemma lem3336879 {_87026 : Type'} (h1 : term167 _87026) : term1076 _87026.
Proof. exact (proj1 (@lem3336469 _87026 h1)). Qed.
Lemma lem3336880 {_86990 : Type'} (h1 : term167 _86990) : term1081 _86990.
Proof. exact (proj2 (@lem3336391 _86990 h1)). Qed.
Lemma lem3336881 {_86990 : Type'} (h1 : term167 _86990) : term1076 _86990.
Proof. exact (proj1 (@lem3336391 _86990 h1)). Qed.
Lemma lem3336882 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term650 _86990 s x' t x t') : term650 _86990 s x' t x t'.
Proof. exact (h1). Qed.
Lemma lem3336883 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term825 _87026 s' t'' x''' x'' t''') : term825 _87026 s' t'' x''' x'' t'''.
Proof. exact (h1). Qed.
Lemma lem3336884 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term501 _86990 t' s t x.
Proof. exact (h1). Qed.
Lemma lem3336885 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : term553 _86990 s x' t x t'.
Proof. exact (h1). Qed.
Lemma lem3336886 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term233 _86990 s t x.
Proof. exact (proj2 (@lem3336884 _86990 t' s t x h1)). Qed.
Lemma lem3336887 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term484 _86990 s t' x t.
Proof. exact (proj1 (@lem3336884 _86990 t' s t x h1)). Qed.
Lemma lem3336889 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term194 _86990 s x t'.
Proof. exact (proj1 (@lem3336887 _86990 t' s t x h1)). Qed.
Lemma lem3336892 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : term522 _86990 s x' t x t'.
Proof. exact (proj2 (@lem3336885 _86990 s x' t x t' h1)). Qed.
Lemma lem3336893 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : term211 _86990 s x t.
Proof. exact (proj1 (@lem3336885 _86990 s x' t x t' h1)). Qed.
Lemma lem3336895 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : term99 _86990 s t' x' t.
Proof. exact (proj1 (@lem3336892 _86990 s x' t x t' h1)). Qed.
Lemma lem3336898 {_86990 : Type'} (s : type686 _86990) (x : _86990) (h1 : term206 _86990 s x) : term206 _86990 s x.
Proof. exact (h1). Qed.
Lemma lem3336900 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term684 _87026 t''' s' t'' x''.
Proof. exact (h1). Qed.
Lemma lem3336901 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : term732 _87026 s' t'' x''' x'' t'''.
Proof. exact (h1). Qed.
Lemma lem3336902 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term297 _87026 s' t'' x''.
Proof. exact (proj2 (@lem3336900 _87026 t''' s' t'' x'' h1)). Qed.
Lemma lem3336903 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term667 _87026 t'' s' x'' t'''.
Proof. exact (proj1 (@lem3336900 _87026 t''' s' t'' x'' h1)). Qed.
Lemma lem3336904 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term194 _87026 s' x'' t'''.
Proof. exact (proj2 (@lem3336903 _87026 t''' s' t'' x'' h1)). Qed.
Lemma lem3336908 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : term705 _87026 s' t'' x''' x'' t'''.
Proof. exact (proj2 (@lem3336901 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3336909 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : term275 _87026 t'' s' x''.
Proof. exact (proj1 (@lem3336901 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3336911 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : term144 _87026 s' t''' t'' x'''.
Proof. exact (proj1 (@lem3336908 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3336915 {_87026 : Type'} (s' : type686 _87026) (x'' : _87026) (h1 : term206 _87026 s' x'') : term206 _87026 s' x''.
Proof. exact (h1). Qed.
Lemma lem3337091 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term1004 _86990 s x t) = (term1004 _86990 s x t).
Proof. exact (eq_refl (term1004 _86990 s x t)). Qed.
Lemma lem3337092 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1019 _86990 s t) = (term1019 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3337091 _86990 s x t)). Qed.
Lemma lem3337093 {_86990 : Type'} : (@all _86990) = (@all _86990).
Proof. exact (eq_refl (@all _86990)). Qed.
Lemma lem3337094 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1030 _86990 s t) = (term1030 _86990 s t).
Proof. exact (MK_COMB (@lem3337093 _86990) (@lem3337092 _86990 s t)). Qed.
Lemma lem3337095 {_86990 : Type'} (s : _86990 -> Prop) : (term1043 _86990 s) = (term1043 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3337094 _86990 s t)). Qed.
Lemma lem3337096 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3337097 {_86990 : Type'} (s : _86990 -> Prop) : (term1054 _86990 s) = (term1054 _86990 s).
Proof. exact (MK_COMB (@lem3337096 _86990) (@lem3337095 _86990 s)). Qed.
Lemma lem3337098 {_86990 : Type'} : (term1065 _86990) = (term1065 _86990).
Proof. exact (fun_ext (fun s : _86990 -> Prop => @lem3337097 _86990 s)). Qed.
Lemma lem3337099 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3337101 {_86990 : Type'} : (term1076 _86990) = (term1076 _86990).
Proof. exact (MK_COMB (@lem3337099 _86990) (@lem3337098 _86990)). Qed.
Lemma lem3337102 {_86990 : Type'} (h1 : term167 _86990) : term1076 _86990.
Proof. exact (EQ_MP (@lem3337101 _86990) (@lem3336881 _86990 h1)). Qed.
Lemma lem3337133 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1083 A P Q) = (term1084 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3337134 {_86990 : Type'} (P : type686 _86990) (Q : Prop) : (term1085 _86990 P Q) = (term1086 _86990 P Q).
Proof. exact (@lem3337133 (_86990 -> Prop) P Q). Qed.
Lemma lem3337135 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term1087 _86990 s t x t') = (term1088 _86990 s t x t').
Proof. exact (@lem3337134 _86990 (term220 _86990 s t' t) (term207 _86990 x t')). Qed.
Lemma lem3337136 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term1089 _86990 s t' t x) = (term214 _86990 s t' x t).
Proof. exact (eq_refl (term1089 _86990 s t' t x)). Qed.
Lemma lem3337137 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term1090 _86990 s t' t) = (term220 _86990 s t' t).
Proof. exact (fun_ext (fun x : _86990 -> Prop => @lem3337136 _86990 s t' x t)). Qed.
Lemma lem3337138 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3337139 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term1091 _86990 s t' t) = (term221 _86990 s t' t).
Proof. exact (MK_COMB (@lem3337138 _86990) (@lem3337137 _86990 s t' t)). Qed.
Lemma lem3337140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3337141 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term1092 _86990 s t' t) = (term223 _86990 s t' t).
Proof. exact (MK_COMB (@lem3337140) (@lem3337139 _86990 s t' t)). Qed.
Lemma lem3337142 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (term207 _86990 x t') = (term207 _86990 x t').
Proof. exact (eq_refl (term207 _86990 x t')). Qed.
Lemma lem3337143 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term1087 _86990 s t x t') = (term225 _86990 s t x t').
Proof. exact (MK_COMB (@lem3337141 _86990 s t' t) (@lem3337142 _86990 x t')). Qed.
Lemma lem3337144 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3337145 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term1093 _86990 s t x t') = (term1094 _86990 s t x t').
Proof. exact (MK_COMB (@lem3337144) (@lem3337143 _86990 s t x t')). Qed.
Lemma lem3337146 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term1089 _86990 s t' t x) = (term214 _86990 s t' x t).
Proof. exact (eq_refl (term1089 _86990 s t' t x)). Qed.
Lemma lem3337147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3337148 {_86990 : Type'} (s : type686 _86990) (t' : _86990 -> Prop) (x : _86990 -> Prop) (t : _86990 -> Prop) : (term1095 _86990 s t' t x) = (term1096 _86990 s t' x t).
Proof. exact (MK_COMB (@lem3337147) (@lem3337146 _86990 s t' x t)). Qed.
Lemma lem3337149 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (term207 _86990 x t') = (term207 _86990 x t').
Proof. exact (eq_refl (term207 _86990 x t')). Qed.
Lemma lem3337150 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term1097 _86990 s t x x' t') = (term1098 _86990 s x t x' t').
Proof. exact (MK_COMB (@lem3337148 _86990 s t' x t) (@lem3337149 _86990 x' t')). Qed.
Lemma lem3337151 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term1099 _86990 s t x t') = (term1100 _86990 s t x t').
Proof. exact (fun_ext (fun x' : _86990 -> Prop => @lem3337150 _86990 s x' t x t')). Qed.
Lemma lem3337152 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3337153 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term1088 _86990 s t x t') = (term1101 _86990 s t x t').
Proof. exact (MK_COMB (@lem3337152 _86990) (@lem3337151 _86990 s t x t')). Qed.
Lemma lem3337154 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : ((term1087 _86990 s t x t') = (term1088 _86990 s t x t')) = ((term225 _86990 s t x t') = (term1101 _86990 s t x t')).
Proof. exact (MK_COMB (@lem3337145 _86990 s t x t') (@lem3337153 _86990 s t x t')). Qed.
Lemma lem3337155 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term225 _86990 s t x t') = (term1101 _86990 s t x t').
Proof. exact (EQ_MP (@lem3337154 _86990 s t x t') (@lem3337135 _86990 s t x t')). Qed.
Lemma lem3337156 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term232 _86990 s t x) = (term1102 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3337155 _86990 s t x t')). Qed.
Lemma lem3337157 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3337158 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term233 _86990 s t x) = (term1103 _86990 s t x).
Proof. exact (MK_COMB (@lem3337157 _86990) (@lem3337156 _86990 s t x)). Qed.
Lemma lem3337171 {_86990 : Type'} (s : type686 _86990) (x : _86990 -> Prop) (t : _86990 -> Prop) (x' : _86990) (t' : _86990 -> Prop) : (term1098 _86990 s x t x' t') = (term1098 _86990 s x t x' t').
Proof. exact (eq_refl (term1098 _86990 s x t x' t')). Qed.
Lemma lem3337172 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term1100 _86990 s t x t') = (term1100 _86990 s t x t').
Proof. exact (fun_ext (fun x' : _86990 -> Prop => @lem3337171 _86990 s x' t x t')). Qed.
Lemma lem3337173 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3337174 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) : (term1101 _86990 s t x t') = (term1101 _86990 s t x t').
Proof. exact (MK_COMB (@lem3337173 _86990) (@lem3337172 _86990 s t x t')). Qed.
Lemma lem3337175 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term1102 _86990 s t x) = (term1102 _86990 s t x).
Proof. exact (fun_ext (fun t' : _86990 -> Prop => @lem3337174 _86990 s t x t')). Qed.
Lemma lem3337176 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3337177 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term1103 _86990 s t x) = (term1103 _86990 s t x).
Proof. exact (MK_COMB (@lem3337176 _86990) (@lem3337175 _86990 s t x)). Qed.
Lemma lem3337178 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) : (term233 _86990 s t x) = (term1103 _86990 s t x).
Proof. exact (TRANS (@lem3337158 _86990 s t x) (@lem3337177 _86990 s t x)). Qed.
Lemma lem3337179 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term1103 _86990 s t x.
Proof. exact (EQ_MP (@lem3337178 _86990 s t x) (@lem3336886 _86990 t' s t x h1)). Qed.
Lemma lem3337396 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term1001 _86990 s x t) = (term1104 _86990 s x t).
Proof. exact (@lem19490 (@IN _86990 x s) (term1105 _86990 x s t) (@IN _86990 x t)). Qed.
Lemma lem3337397 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1020 _86990 s t) = (term1106 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3337396 _86990 s x t)). Qed.
Lemma lem3337398 {_86990 : Type'} : (@all _86990) = (@all _86990).
Proof. exact (eq_refl (@all _86990)). Qed.
Lemma lem3337399 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1035 _86990 s t) = (term1107 _86990 s t).
Proof. exact (MK_COMB (@lem3337398 _86990) (@lem3337397 _86990 s t)). Qed.
Lemma lem3337400 {_86990 : Type'} (s : _86990 -> Prop) : (term1044 _86990 s) = (term1108 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3337399 _86990 s t)). Qed.
Lemma lem3337401 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3337402 {_86990 : Type'} (s : _86990 -> Prop) : (term1059 _86990 s) = (term1109 _86990 s).
Proof. exact (MK_COMB (@lem3337401 _86990) (@lem3337400 _86990 s)). Qed.
Lemma lem3337403 {_86990 : Type'} : (term1066 _86990) = (term1110 _86990).
Proof. exact (fun_ext (fun s : _86990 -> Prop => @lem3337402 _86990 s)). Qed.
Lemma lem3337404 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3337406 {_86990 : Type'} : (term1081 _86990) = (term1111 _86990).
Proof. exact (MK_COMB (@lem3337404 _86990) (@lem3337403 _86990)). Qed.
Lemma lem3337407 {_86990 : Type'} (h1 : term167 _86990) : term1111 _86990.
Proof. exact (EQ_MP (@lem3337406 _86990) (@lem3336880 _86990 h1)). Qed.
Lemma lem3337427 {_86990 : Type'} (s : type686 _86990) (x : _86990) (t : _86990 -> Prop) : (term197 _86990 s x t) = (term197 _86990 s x t).
Proof. exact (eq_refl (term197 _86990 s x t)). Qed.
Lemma lem3337428 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term205 _86990 s x) = (term205 _86990 s x).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3337427 _86990 s x t)). Qed.
Lemma lem3337429 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3337431 {_86990 : Type'} (s : type686 _86990) (x : _86990) : (term206 _86990 s x) = (term206 _86990 s x).
Proof. exact (MK_COMB (@lem3337429 _86990) (@lem3337428 _86990 s x)). Qed.
Lemma lem3337432 {_86990 : Type'} (s : type686 _86990) (x : _86990) (h1 : term206 _86990 s x) : term206 _86990 s x.
Proof. exact (EQ_MP (@lem3337431 _86990 s x) (@lem3336898 _86990 s x h1)). Qed.
Lemma lem3337637 {_86990 : Type'} (s : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) : (term1001 _86990 s x t) = (term1104 _86990 s x t).
Proof. exact (@lem19490 (@IN _86990 x s) (term1105 _86990 x s t) (@IN _86990 x t)). Qed.
Lemma lem3337638 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1020 _86990 s t) = (term1106 _86990 s t).
Proof. exact (fun_ext (fun x : _86990 => @lem3337637 _86990 s x t)). Qed.
Lemma lem3337639 {_86990 : Type'} : (@all _86990) = (@all _86990).
Proof. exact (eq_refl (@all _86990)). Qed.
Lemma lem3337640 {_86990 : Type'} (s : _86990 -> Prop) (t : _86990 -> Prop) : (term1035 _86990 s t) = (term1107 _86990 s t).
Proof. exact (MK_COMB (@lem3337639 _86990) (@lem3337638 _86990 s t)). Qed.
Lemma lem3337641 {_86990 : Type'} (s : _86990 -> Prop) : (term1044 _86990 s) = (term1108 _86990 s).
Proof. exact (fun_ext (fun t : _86990 -> Prop => @lem3337640 _86990 s t)). Qed.
Lemma lem3337642 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3337643 {_86990 : Type'} (s : _86990 -> Prop) : (term1059 _86990 s) = (term1109 _86990 s).
Proof. exact (MK_COMB (@lem3337642 _86990) (@lem3337641 _86990 s)). Qed.
Lemma lem3337644 {_86990 : Type'} : (term1066 _86990) = (term1110 _86990).
Proof. exact (fun_ext (fun s : _86990 -> Prop => @lem3337643 _86990 s)). Qed.
Lemma lem3337645 {_86990 : Type'} : (@all (_86990 -> Prop)) = (@all (_86990 -> Prop)).
Proof. exact (eq_refl (@all (_86990 -> Prop))). Qed.
Lemma lem3337647 {_86990 : Type'} : (term1081 _86990) = (term1111 _86990).
Proof. exact (MK_COMB (@lem3337645 _86990) (@lem3337644 _86990)). Qed.
Lemma lem3337648 {_86990 : Type'} (h1 : term167 _86990) : term1111 _86990.
Proof. exact (EQ_MP (@lem3337647 _86990) (@lem3336880 _86990 h1)). Qed.
Lemma lem3337664 {_86990 : Type'} (x : _86990) (t : _86990 -> Prop) (h1 : term207 _86990 x t) : term207 _86990 x t.
Proof. exact (h1). Qed.
Lemma lem3337786 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term1004 _87026 s x t) = (term1004 _87026 s x t).
Proof. exact (eq_refl (term1004 _87026 s x t)). Qed.
Lemma lem3337787 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1019 _87026 s t) = (term1019 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3337786 _87026 s x t)). Qed.
Lemma lem3337788 {_87026 : Type'} : (@all _87026) = (@all _87026).
Proof. exact (eq_refl (@all _87026)). Qed.
Lemma lem3337789 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1030 _87026 s t) = (term1030 _87026 s t).
Proof. exact (MK_COMB (@lem3337788 _87026) (@lem3337787 _87026 s t)). Qed.
Lemma lem3337790 {_87026 : Type'} (s : _87026 -> Prop) : (term1043 _87026 s) = (term1043 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3337789 _87026 s t)). Qed.
Lemma lem3337791 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3337792 {_87026 : Type'} (s : _87026 -> Prop) : (term1054 _87026 s) = (term1054 _87026 s).
Proof. exact (MK_COMB (@lem3337791 _87026) (@lem3337790 _87026 s)). Qed.
Lemma lem3337793 {_87026 : Type'} : (term1065 _87026) = (term1065 _87026).
Proof. exact (fun_ext (fun s : _87026 -> Prop => @lem3337792 _87026 s)). Qed.
Lemma lem3337794 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3337796 {_87026 : Type'} : (term1076 _87026) = (term1076 _87026).
Proof. exact (MK_COMB (@lem3337794 _87026) (@lem3337793 _87026)). Qed.
Lemma lem3337797 {_87026 : Type'} (h1 : term167 _87026) : term1076 _87026.
Proof. exact (EQ_MP (@lem3337796 _87026) (@lem3336879 _87026 h1)). Qed.
Lemma lem3337882 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1083 A P Q) = (term1084 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3337883 {_87026 : Type'} (P : type686 _87026) (Q : Prop) : (term1085 _87026 P Q) = (term1086 _87026 P Q).
Proof. exact (@lem3337882 (_87026 -> Prop) P Q). Qed.
Lemma lem3337884 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t' : _87026 -> Prop) : (term1112 _87026 s' t'' x'' t') = (term1113 _87026 s' t'' x'' t').
Proof. exact (@lem3337883 _87026 (term284 _87026 s' t' t'') (term207 _87026 x'' t')). Qed.
Lemma lem3337885 {_87026 : Type'} (s' : type686 _87026) (t' : _87026 -> Prop) (t'' : _87026 -> Prop) (x : _87026 -> Prop) : (term1114 _87026 s' t' t'' x) = (term278 _87026 s' t' t'' x).
Proof. exact (eq_refl (term1114 _87026 s' t' t'' x)). Qed.
Lemma lem3337886 {_87026 : Type'} (s' : type686 _87026) (t' : _87026 -> Prop) (t'' : _87026 -> Prop) : (term1115 _87026 s' t' t'') = (term284 _87026 s' t' t'').
Proof. exact (fun_ext (fun x : _87026 -> Prop => @lem3337885 _87026 s' t' t'' x)). Qed.
Lemma lem3337887 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3337888 {_87026 : Type'} (s' : type686 _87026) (t' : _87026 -> Prop) (t'' : _87026 -> Prop) : (term1116 _87026 s' t' t'') = (term285 _87026 s' t' t'').
Proof. exact (MK_COMB (@lem3337887 _87026) (@lem3337886 _87026 s' t' t'')). Qed.
Lemma lem3337889 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3337890 {_87026 : Type'} (s' : type686 _87026) (t' : _87026 -> Prop) (t'' : _87026 -> Prop) : (term1117 _87026 s' t' t'') = (term287 _87026 s' t' t'').
Proof. exact (MK_COMB (@lem3337889) (@lem3337888 _87026 s' t' t'')). Qed.
Lemma lem3337891 {_87026 : Type'} (x'' : _87026) (t' : _87026 -> Prop) : (term207 _87026 x'' t') = (term207 _87026 x'' t').
Proof. exact (eq_refl (term207 _87026 x'' t')). Qed.
Lemma lem3337892 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t' : _87026 -> Prop) : (term1112 _87026 s' t'' x'' t') = (term289 _87026 s' t'' x'' t').
Proof. exact (MK_COMB (@lem3337890 _87026 s' t' t'') (@lem3337891 _87026 x'' t')). Qed.
Lemma lem3337893 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3337894 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t' : _87026 -> Prop) : (term1118 _87026 s' t'' x'' t') = (term1119 _87026 s' t'' x'' t').
Proof. exact (MK_COMB (@lem3337893) (@lem3337892 _87026 s' t'' x'' t')). Qed.
Lemma lem3337895 {_87026 : Type'} (s' : type686 _87026) (t' : _87026 -> Prop) (t'' : _87026 -> Prop) (x : _87026 -> Prop) : (term1114 _87026 s' t' t'' x) = (term278 _87026 s' t' t'' x).
Proof. exact (eq_refl (term1114 _87026 s' t' t'' x)). Qed.
Lemma lem3337896 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3337897 {_87026 : Type'} (s' : type686 _87026) (t' : _87026 -> Prop) (t'' : _87026 -> Prop) (x : _87026 -> Prop) : (term1120 _87026 s' t' t'' x) = (term1121 _87026 s' t' t'' x).
Proof. exact (MK_COMB (@lem3337896) (@lem3337895 _87026 s' t' t'' x)). Qed.
Lemma lem3337898 {_87026 : Type'} (x'' : _87026) (t' : _87026 -> Prop) : (term207 _87026 x'' t') = (term207 _87026 x'' t').
Proof. exact (eq_refl (term207 _87026 x'' t')). Qed.
Lemma lem3337899 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x : _87026 -> Prop) (x'' : _87026) (t' : _87026 -> Prop) : (term1122 _87026 s' t'' x x'' t') = (term1123 _87026 s' t'' x x'' t').
Proof. exact (MK_COMB (@lem3337897 _87026 s' t' t'' x) (@lem3337898 _87026 x'' t')). Qed.
Lemma lem3337900 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t' : _87026 -> Prop) : (term1124 _87026 s' t'' x'' t') = (term1125 _87026 s' t'' x'' t').
Proof. exact (fun_ext (fun x : _87026 -> Prop => @lem3337899 _87026 s' t'' x x'' t')). Qed.
Lemma lem3337901 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3337902 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t' : _87026 -> Prop) : (term1113 _87026 s' t'' x'' t') = (term1126 _87026 s' t'' x'' t').
Proof. exact (MK_COMB (@lem3337901 _87026) (@lem3337900 _87026 s' t'' x'' t')). Qed.
Lemma lem3337903 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t' : _87026 -> Prop) : ((term1112 _87026 s' t'' x'' t') = (term1113 _87026 s' t'' x'' t')) = ((term289 _87026 s' t'' x'' t') = (term1126 _87026 s' t'' x'' t')).
Proof. exact (MK_COMB (@lem3337894 _87026 s' t'' x'' t') (@lem3337902 _87026 s' t'' x'' t')). Qed.
Lemma lem3337904 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t' : _87026 -> Prop) : (term289 _87026 s' t'' x'' t') = (term1126 _87026 s' t'' x'' t').
Proof. exact (EQ_MP (@lem3337903 _87026 s' t'' x'' t') (@lem3337884 _87026 s' t'' x'' t')). Qed.
Lemma lem3337905 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term296 _87026 s' t'' x'') = (term1127 _87026 s' t'' x'').
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3337904 _87026 s' t'' x'' t')). Qed.
Lemma lem3337906 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3337907 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term297 _87026 s' t'' x'') = (term1128 _87026 s' t'' x'').
Proof. exact (MK_COMB (@lem3337906 _87026) (@lem3337905 _87026 s' t'' x'')). Qed.
Lemma lem3337920 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x : _87026 -> Prop) (x'' : _87026) (t' : _87026 -> Prop) : (term1123 _87026 s' t'' x x'' t') = (term1123 _87026 s' t'' x x'' t').
Proof. exact (eq_refl (term1123 _87026 s' t'' x x'' t')). Qed.
Lemma lem3337921 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t' : _87026 -> Prop) : (term1125 _87026 s' t'' x'' t') = (term1125 _87026 s' t'' x'' t').
Proof. exact (fun_ext (fun x : _87026 -> Prop => @lem3337920 _87026 s' t'' x x'' t')). Qed.
Lemma lem3337922 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3337923 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t' : _87026 -> Prop) : (term1126 _87026 s' t'' x'' t') = (term1126 _87026 s' t'' x'' t').
Proof. exact (MK_COMB (@lem3337922 _87026) (@lem3337921 _87026 s' t'' x'' t')). Qed.
Lemma lem3337924 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term1127 _87026 s' t'' x'') = (term1127 _87026 s' t'' x'').
Proof. exact (fun_ext (fun t' : _87026 -> Prop => @lem3337923 _87026 s' t'' x'' t')). Qed.
Lemma lem3337925 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3337926 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term1128 _87026 s' t'' x'') = (term1128 _87026 s' t'' x'').
Proof. exact (MK_COMB (@lem3337925 _87026) (@lem3337924 _87026 s' t'' x'')). Qed.
Lemma lem3337927 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) : (term297 _87026 s' t'' x'') = (term1128 _87026 s' t'' x'').
Proof. exact (TRANS (@lem3337907 _87026 s' t'' x'') (@lem3337926 _87026 s' t'' x'')). Qed.
Lemma lem3337928 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term1128 _87026 s' t'' x''.
Proof. exact (EQ_MP (@lem3337927 _87026 s' t'' x'') (@lem3336902 _87026 t''' s' t'' x'' h1)). Qed.
Lemma lem3338091 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term1001 _87026 s x t) = (term1104 _87026 s x t).
Proof. exact (@lem19490 (@IN _87026 x s) (term1105 _87026 x s t) (@IN _87026 x t)). Qed.
Lemma lem3338092 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1020 _87026 s t) = (term1106 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3338091 _87026 s x t)). Qed.
Lemma lem3338093 {_87026 : Type'} : (@all _87026) = (@all _87026).
Proof. exact (eq_refl (@all _87026)). Qed.
Lemma lem3338094 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1035 _87026 s t) = (term1107 _87026 s t).
Proof. exact (MK_COMB (@lem3338093 _87026) (@lem3338092 _87026 s t)). Qed.
Lemma lem3338095 {_87026 : Type'} (s : _87026 -> Prop) : (term1044 _87026 s) = (term1108 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3338094 _87026 s t)). Qed.
Lemma lem3338096 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3338097 {_87026 : Type'} (s : _87026 -> Prop) : (term1059 _87026 s) = (term1109 _87026 s).
Proof. exact (MK_COMB (@lem3338096 _87026) (@lem3338095 _87026 s)). Qed.
Lemma lem3338098 {_87026 : Type'} : (term1066 _87026) = (term1110 _87026).
Proof. exact (fun_ext (fun s : _87026 -> Prop => @lem3338097 _87026 s)). Qed.
Lemma lem3338099 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3338101 {_87026 : Type'} : (term1081 _87026) = (term1111 _87026).
Proof. exact (MK_COMB (@lem3338099 _87026) (@lem3338098 _87026)). Qed.
Lemma lem3338102 {_87026 : Type'} (h1 : term167 _87026) : term1111 _87026.
Proof. exact (EQ_MP (@lem3338101 _87026) (@lem3336878 _87026 h1)). Qed.
Lemma lem3338172 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) (h1 : term207 _87026 x'' t'') : term207 _87026 x'' t''.
Proof. exact (h1). Qed.
Lemma lem3338323 {_87026 : Type'} (s : _87026 -> Prop) (x : _87026) (t : _87026 -> Prop) : (term1001 _87026 s x t) = (term1104 _87026 s x t).
Proof. exact (@lem19490 (@IN _87026 x s) (term1105 _87026 x s t) (@IN _87026 x t)). Qed.
Lemma lem3338324 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1020 _87026 s t) = (term1106 _87026 s t).
Proof. exact (fun_ext (fun x : _87026 => @lem3338323 _87026 s x t)). Qed.
Lemma lem3338325 {_87026 : Type'} : (@all _87026) = (@all _87026).
Proof. exact (eq_refl (@all _87026)). Qed.
Lemma lem3338326 {_87026 : Type'} (s : _87026 -> Prop) (t : _87026 -> Prop) : (term1035 _87026 s t) = (term1107 _87026 s t).
Proof. exact (MK_COMB (@lem3338325 _87026) (@lem3338324 _87026 s t)). Qed.
Lemma lem3338327 {_87026 : Type'} (s : _87026 -> Prop) : (term1044 _87026 s) = (term1108 _87026 s).
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3338326 _87026 s t)). Qed.
Lemma lem3338328 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3338329 {_87026 : Type'} (s : _87026 -> Prop) : (term1059 _87026 s) = (term1109 _87026 s).
Proof. exact (MK_COMB (@lem3338328 _87026) (@lem3338327 _87026 s)). Qed.
Lemma lem3338330 {_87026 : Type'} : (term1066 _87026) = (term1110 _87026).
Proof. exact (fun_ext (fun s : _87026 -> Prop => @lem3338329 _87026 s)). Qed.
Lemma lem3338331 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3338333 {_87026 : Type'} : (term1081 _87026) = (term1111 _87026).
Proof. exact (MK_COMB (@lem3338331 _87026) (@lem3338330 _87026)). Qed.
Lemma lem3338334 {_87026 : Type'} (h1 : term167 _87026) : term1111 _87026.
Proof. exact (EQ_MP (@lem3338333 _87026) (@lem3336878 _87026 h1)). Qed.
Lemma lem3338408 {_87026 : Type'} (s' : type686 _87026) (x'' : _87026) (t : _87026 -> Prop) : (term197 _87026 s' x'' t) = (term197 _87026 s' x'' t).
Proof. exact (eq_refl (term197 _87026 s' x'' t)). Qed.
Lemma lem3338409 {_87026 : Type'} (s' : type686 _87026) (x'' : _87026) : (term205 _87026 s' x'') = (term205 _87026 s' x'').
Proof. exact (fun_ext (fun t : _87026 -> Prop => @lem3338408 _87026 s' x'' t)). Qed.
Lemma lem3338410 {_87026 : Type'} : (@all (_87026 -> Prop)) = (@all (_87026 -> Prop)).
Proof. exact (eq_refl (@all (_87026 -> Prop))). Qed.
Lemma lem3338412 {_87026 : Type'} (s' : type686 _87026) (x'' : _87026) : (term206 _87026 s' x'') = (term206 _87026 s' x'').
Proof. exact (MK_COMB (@lem3338410 _87026) (@lem3338409 _87026 s' x'')). Qed.
Lemma lem3338413 {_87026 : Type'} (s' : type686 _87026) (x'' : _87026) (h1 : term206 _87026 s' x'') : term206 _87026 s' x''.
Proof. exact (EQ_MP (@lem3338412 _87026 s' x'') (@lem3336915 _87026 s' x'' h1)). Qed.
Lemma lem3338468 {_86990 : Type'} (_34563 : _86990 -> Prop) (h1 : term167 _86990) : term1067 _86990 _34563.
Proof. exact (@lem3337102 _86990 h1 _34563). Qed.
Lemma lem3338469 {_86990 : Type'} (_34563 : _86990 -> Prop) : (term1067 _86990 _34563) = (term1054 _86990 _34563).
Proof. exact (eq_refl (term1067 _86990 _34563)). Qed.
Lemma lem3338470 {_86990 : Type'} (_34563 : _86990 -> Prop) (h1 : term167 _86990) : term1054 _86990 _34563.
Proof. exact (EQ_MP (@lem3338469 _86990 _34563) (@lem3338468 _86990 _34563 h1)). Qed.
Lemma lem3338471 {_86990 : Type'} (_34563 : _86990 -> Prop) (_34564 : _86990 -> Prop) (h1 : term167 _86990) : term1045 _86990 _34563 _34564.
Proof. exact (@lem3338470 _86990 _34563 h1 _34564). Qed.
Lemma lem3338472 {_86990 : Type'} (_34563 : _86990 -> Prop) (_34564 : _86990 -> Prop) : (term1045 _86990 _34563 _34564) = (term1030 _86990 _34563 _34564).
Proof. exact (eq_refl (term1045 _86990 _34563 _34564)). Qed.
Lemma lem3338473 {_86990 : Type'} (_34563 : _86990 -> Prop) (_34564 : _86990 -> Prop) (h1 : term167 _86990) : term1030 _86990 _34563 _34564.
Proof. exact (EQ_MP (@lem3338472 _86990 _34563 _34564) (@lem3338471 _86990 _34563 _34564 h1)). Qed.
Lemma lem3338474 {_86990 : Type'} (_34563 : _86990 -> Prop) (_34564 : _86990 -> Prop) (_34565 : _86990) (h1 : term167 _86990) : term1021 _86990 _34563 _34564 _34565.
Proof. exact (@lem3338473 _86990 _34563 _34564 h1 _34565). Qed.
Lemma lem3338475 {_86990 : Type'} (_34563 : _86990 -> Prop) (_34565 : _86990) (_34564 : _86990 -> Prop) : (term1021 _86990 _34563 _34564 _34565) = (term1004 _86990 _34563 _34565 _34564).
Proof. exact (eq_refl (term1021 _86990 _34563 _34564 _34565)). Qed.
Lemma lem3338486 {_86990 : Type'} (_34569 : _86990 -> Prop) (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term1129 _86990 s t x _34569.
Proof. exact (@lem3337179 _86990 t' s t x h1 _34569). Qed.
Lemma lem3338487 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (_34569 : _86990 -> Prop) : (term1129 _86990 s t x _34569) = (term1101 _86990 s t x _34569).
Proof. exact (eq_refl (term1129 _86990 s t x _34569)). Qed.
Lemma lem3338488 {_86990 : Type'} (_34569 : _86990 -> Prop) (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term1101 _86990 s t x _34569.
Proof. exact (EQ_MP (@lem3338487 _86990 s t x _34569) (@lem3338486 _86990 _34569 t' s t x h1)). Qed.
Lemma lem3338489 {_86990 : Type'} (_34569 : _86990 -> Prop) (_34570 : _86990 -> Prop) (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term1130 _86990 s t x _34569 _34570.
Proof. exact (@lem3338488 _86990 _34569 t' s t x h1 _34570). Qed.
Lemma lem3338490 {_86990 : Type'} (s : type686 _86990) (_34570 : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (_34569 : _86990 -> Prop) : (term1130 _86990 s t x _34569 _34570) = (term1098 _86990 s _34570 t x _34569).
Proof. exact (eq_refl (term1130 _86990 s t x _34569 _34570)). Qed.
Lemma lem3338491 {_86990 : Type'} (_34570 : _86990 -> Prop) (_34569 : _86990 -> Prop) (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term1098 _86990 s _34570 t x _34569.
Proof. exact (EQ_MP (@lem3338490 _86990 s _34570 t x _34569) (@lem3338489 _86990 _34569 _34570 t' s t x h1)). Qed.
Lemma lem3338555 {_86990 : Type'} (_34592 : _86990 -> Prop) (h1 : term167 _86990) : term1131 _86990 _34592.
Proof. exact (@lem3337407 _86990 h1 _34592). Qed.
Lemma lem3338556 {_86990 : Type'} (_34592 : _86990 -> Prop) : (term1131 _86990 _34592) = (term1109 _86990 _34592).
Proof. exact (eq_refl (term1131 _86990 _34592)). Qed.
Lemma lem3338557 {_86990 : Type'} (_34592 : _86990 -> Prop) (h1 : term167 _86990) : term1109 _86990 _34592.
Proof. exact (EQ_MP (@lem3338556 _86990 _34592) (@lem3338555 _86990 _34592 h1)). Qed.
Lemma lem3338558 {_86990 : Type'} (_34592 : _86990 -> Prop) (_34593 : _86990 -> Prop) (h1 : term167 _86990) : term1132 _86990 _34592 _34593.
Proof. exact (@lem3338557 _86990 _34592 h1 _34593). Qed.
Lemma lem3338559 {_86990 : Type'} (_34592 : _86990 -> Prop) (_34593 : _86990 -> Prop) : (term1132 _86990 _34592 _34593) = (term1107 _86990 _34592 _34593).
Proof. exact (eq_refl (term1132 _86990 _34592 _34593)). Qed.
Lemma lem3338560 {_86990 : Type'} (_34592 : _86990 -> Prop) (_34593 : _86990 -> Prop) (h1 : term167 _86990) : term1107 _86990 _34592 _34593.
Proof. exact (EQ_MP (@lem3338559 _86990 _34592 _34593) (@lem3338558 _86990 _34592 _34593 h1)). Qed.
Lemma lem3338561 {_86990 : Type'} (_34592 : _86990 -> Prop) (_34593 : _86990 -> Prop) (_34594 : _86990) (h1 : term167 _86990) : term1133 _86990 _34592 _34593 _34594.
Proof. exact (@lem3338560 _86990 _34592 _34593 h1 _34594). Qed.
Lemma lem3338562 {_86990 : Type'} (_34592 : _86990 -> Prop) (_34594 : _86990) (_34593 : _86990 -> Prop) : (term1133 _86990 _34592 _34593 _34594) = (term1104 _86990 _34592 _34594 _34593).
Proof. exact (eq_refl (term1133 _86990 _34592 _34593 _34594)). Qed.
Lemma lem3338563 {_86990 : Type'} (_34592 : _86990 -> Prop) (_34594 : _86990) (_34593 : _86990 -> Prop) (h1 : term167 _86990) : term1104 _86990 _34592 _34594 _34593.
Proof. exact (EQ_MP (@lem3338562 _86990 _34592 _34594 _34593) (@lem3338561 _86990 _34592 _34593 _34594 h1)). Qed.
Lemma lem3338564 {_86990 : Type'} (_34595 : _86990 -> Prop) (s : type686 _86990) (x : _86990) (h1 : term206 _86990 s x) : term1134 _86990 s x _34595.
Proof. exact (@lem3337432 _86990 s x h1 _34595). Qed.
Lemma lem3338565 {_86990 : Type'} (s : type686 _86990) (x : _86990) (_34595 : _86990 -> Prop) : (term1134 _86990 s x _34595) = (term197 _86990 s x _34595).
Proof. exact (eq_refl (term1134 _86990 s x _34595)). Qed.
Lemma lem3338630 {_86990 : Type'} (_34617 : _86990 -> Prop) (h1 : term167 _86990) : term1131 _86990 _34617.
Proof. exact (@lem3337648 _86990 h1 _34617). Qed.
Lemma lem3338631 {_86990 : Type'} (_34617 : _86990 -> Prop) : (term1131 _86990 _34617) = (term1109 _86990 _34617).
Proof. exact (eq_refl (term1131 _86990 _34617)). Qed.
Lemma lem3338632 {_86990 : Type'} (_34617 : _86990 -> Prop) (h1 : term167 _86990) : term1109 _86990 _34617.
Proof. exact (EQ_MP (@lem3338631 _86990 _34617) (@lem3338630 _86990 _34617 h1)). Qed.
Lemma lem3338633 {_86990 : Type'} (_34617 : _86990 -> Prop) (_34618 : _86990 -> Prop) (h1 : term167 _86990) : term1132 _86990 _34617 _34618.
Proof. exact (@lem3338632 _86990 _34617 h1 _34618). Qed.
Lemma lem3338634 {_86990 : Type'} (_34617 : _86990 -> Prop) (_34618 : _86990 -> Prop) : (term1132 _86990 _34617 _34618) = (term1107 _86990 _34617 _34618).
Proof. exact (eq_refl (term1132 _86990 _34617 _34618)). Qed.
Lemma lem3338635 {_86990 : Type'} (_34617 : _86990 -> Prop) (_34618 : _86990 -> Prop) (h1 : term167 _86990) : term1107 _86990 _34617 _34618.
Proof. exact (EQ_MP (@lem3338634 _86990 _34617 _34618) (@lem3338633 _86990 _34617 _34618 h1)). Qed.
Lemma lem3338636 {_86990 : Type'} (_34617 : _86990 -> Prop) (_34618 : _86990 -> Prop) (_34619 : _86990) (h1 : term167 _86990) : term1133 _86990 _34617 _34618 _34619.
Proof. exact (@lem3338635 _86990 _34617 _34618 h1 _34619). Qed.
Lemma lem3338637 {_86990 : Type'} (_34617 : _86990 -> Prop) (_34619 : _86990) (_34618 : _86990 -> Prop) : (term1133 _86990 _34617 _34618 _34619) = (term1104 _86990 _34617 _34619 _34618).
Proof. exact (eq_refl (term1133 _86990 _34617 _34618 _34619)). Qed.
Lemma lem3338638 {_86990 : Type'} (_34617 : _86990 -> Prop) (_34619 : _86990) (_34618 : _86990 -> Prop) (h1 : term167 _86990) : term1104 _86990 _34617 _34619 _34618.
Proof. exact (EQ_MP (@lem3338637 _86990 _34617 _34619 _34618) (@lem3338636 _86990 _34617 _34618 _34619 h1)). Qed.
Lemma lem3338675 {_87026 : Type'} (_34632 : _87026 -> Prop) (h1 : term167 _87026) : term1067 _87026 _34632.
Proof. exact (@lem3337797 _87026 h1 _34632). Qed.
Lemma lem3338676 {_87026 : Type'} (_34632 : _87026 -> Prop) : (term1067 _87026 _34632) = (term1054 _87026 _34632).
Proof. exact (eq_refl (term1067 _87026 _34632)). Qed.
Lemma lem3338677 {_87026 : Type'} (_34632 : _87026 -> Prop) (h1 : term167 _87026) : term1054 _87026 _34632.
Proof. exact (EQ_MP (@lem3338676 _87026 _34632) (@lem3338675 _87026 _34632 h1)). Qed.
Lemma lem3338678 {_87026 : Type'} (_34632 : _87026 -> Prop) (_34633 : _87026 -> Prop) (h1 : term167 _87026) : term1045 _87026 _34632 _34633.
Proof. exact (@lem3338677 _87026 _34632 h1 _34633). Qed.
Lemma lem3338679 {_87026 : Type'} (_34632 : _87026 -> Prop) (_34633 : _87026 -> Prop) : (term1045 _87026 _34632 _34633) = (term1030 _87026 _34632 _34633).
Proof. exact (eq_refl (term1045 _87026 _34632 _34633)). Qed.
Lemma lem3338680 {_87026 : Type'} (_34632 : _87026 -> Prop) (_34633 : _87026 -> Prop) (h1 : term167 _87026) : term1030 _87026 _34632 _34633.
Proof. exact (EQ_MP (@lem3338679 _87026 _34632 _34633) (@lem3338678 _87026 _34632 _34633 h1)). Qed.
Lemma lem3338681 {_87026 : Type'} (_34632 : _87026 -> Prop) (_34633 : _87026 -> Prop) (_34634 : _87026) (h1 : term167 _87026) : term1021 _87026 _34632 _34633 _34634.
Proof. exact (@lem3338680 _87026 _34632 _34633 h1 _34634). Qed.
Lemma lem3338682 {_87026 : Type'} (_34632 : _87026 -> Prop) (_34634 : _87026) (_34633 : _87026 -> Prop) : (term1021 _87026 _34632 _34633 _34634) = (term1004 _87026 _34632 _34634 _34633).
Proof. exact (eq_refl (term1021 _87026 _34632 _34633 _34634)). Qed.
Lemma lem3338711 {_87026 : Type'} (_34644 : _87026 -> Prop) (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term1135 _87026 s' t'' x'' _34644.
Proof. exact (@lem3337928 _87026 t''' s' t'' x'' h1 _34644). Qed.
Lemma lem3338712 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (_34644 : _87026 -> Prop) : (term1135 _87026 s' t'' x'' _34644) = (term1126 _87026 s' t'' x'' _34644).
Proof. exact (eq_refl (term1135 _87026 s' t'' x'' _34644)). Qed.
Lemma lem3338713 {_87026 : Type'} (_34644 : _87026 -> Prop) (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term1126 _87026 s' t'' x'' _34644.
Proof. exact (EQ_MP (@lem3338712 _87026 s' t'' x'' _34644) (@lem3338711 _87026 _34644 t''' s' t'' x'' h1)). Qed.
Lemma lem3338714 {_87026 : Type'} (_34644 : _87026 -> Prop) (_34645 : _87026 -> Prop) (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term1136 _87026 s' t'' x'' _34644 _34645.
Proof. exact (@lem3338713 _87026 _34644 t''' s' t'' x'' h1 _34645). Qed.
Lemma lem3338715 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (_34645 : _87026 -> Prop) (x'' : _87026) (_34644 : _87026 -> Prop) : (term1136 _87026 s' t'' x'' _34644 _34645) = (term1123 _87026 s' t'' _34645 x'' _34644).
Proof. exact (eq_refl (term1136 _87026 s' t'' x'' _34644 _34645)). Qed.
Lemma lem3338716 {_87026 : Type'} (_34645 : _87026 -> Prop) (_34644 : _87026 -> Prop) (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term1123 _87026 s' t'' _34645 x'' _34644.
Proof. exact (EQ_MP (@lem3338715 _87026 s' t'' _34645 x'' _34644) (@lem3338714 _87026 _34644 _34645 t''' s' t'' x'' h1)). Qed.
Lemma lem3338762 {_87026 : Type'} (_34661 : _87026 -> Prop) (h1 : term167 _87026) : term1131 _87026 _34661.
Proof. exact (@lem3338102 _87026 h1 _34661). Qed.
Lemma lem3338763 {_87026 : Type'} (_34661 : _87026 -> Prop) : (term1131 _87026 _34661) = (term1109 _87026 _34661).
Proof. exact (eq_refl (term1131 _87026 _34661)). Qed.
Lemma lem3338764 {_87026 : Type'} (_34661 : _87026 -> Prop) (h1 : term167 _87026) : term1109 _87026 _34661.
Proof. exact (EQ_MP (@lem3338763 _87026 _34661) (@lem3338762 _87026 _34661 h1)). Qed.
Lemma lem3338765 {_87026 : Type'} (_34661 : _87026 -> Prop) (_34662 : _87026 -> Prop) (h1 : term167 _87026) : term1132 _87026 _34661 _34662.
Proof. exact (@lem3338764 _87026 _34661 h1 _34662). Qed.
Lemma lem3338766 {_87026 : Type'} (_34661 : _87026 -> Prop) (_34662 : _87026 -> Prop) : (term1132 _87026 _34661 _34662) = (term1107 _87026 _34661 _34662).
Proof. exact (eq_refl (term1132 _87026 _34661 _34662)). Qed.
Lemma lem3338767 {_87026 : Type'} (_34661 : _87026 -> Prop) (_34662 : _87026 -> Prop) (h1 : term167 _87026) : term1107 _87026 _34661 _34662.
Proof. exact (EQ_MP (@lem3338766 _87026 _34661 _34662) (@lem3338765 _87026 _34661 _34662 h1)). Qed.
Lemma lem3338768 {_87026 : Type'} (_34661 : _87026 -> Prop) (_34662 : _87026 -> Prop) (_34663 : _87026) (h1 : term167 _87026) : term1133 _87026 _34661 _34662 _34663.
Proof. exact (@lem3338767 _87026 _34661 _34662 h1 _34663). Qed.
Lemma lem3338769 {_87026 : Type'} (_34661 : _87026 -> Prop) (_34663 : _87026) (_34662 : _87026 -> Prop) : (term1133 _87026 _34661 _34662 _34663) = (term1104 _87026 _34661 _34663 _34662).
Proof. exact (eq_refl (term1133 _87026 _34661 _34662 _34663)). Qed.
Lemma lem3338770 {_87026 : Type'} (_34661 : _87026 -> Prop) (_34663 : _87026) (_34662 : _87026 -> Prop) (h1 : term167 _87026) : term1104 _87026 _34661 _34663 _34662.
Proof. exact (EQ_MP (@lem3338769 _87026 _34661 _34663 _34662) (@lem3338768 _87026 _34661 _34662 _34663 h1)). Qed.
Lemma lem3338834 {_87026 : Type'} (_34685 : _87026 -> Prop) (h1 : term167 _87026) : term1131 _87026 _34685.
Proof. exact (@lem3338334 _87026 h1 _34685). Qed.
Lemma lem3338835 {_87026 : Type'} (_34685 : _87026 -> Prop) : (term1131 _87026 _34685) = (term1109 _87026 _34685).
Proof. exact (eq_refl (term1131 _87026 _34685)). Qed.
Lemma lem3338836 {_87026 : Type'} (_34685 : _87026 -> Prop) (h1 : term167 _87026) : term1109 _87026 _34685.
Proof. exact (EQ_MP (@lem3338835 _87026 _34685) (@lem3338834 _87026 _34685 h1)). Qed.
Lemma lem3338837 {_87026 : Type'} (_34685 : _87026 -> Prop) (_34686 : _87026 -> Prop) (h1 : term167 _87026) : term1132 _87026 _34685 _34686.
Proof. exact (@lem3338836 _87026 _34685 h1 _34686). Qed.
Lemma lem3338838 {_87026 : Type'} (_34685 : _87026 -> Prop) (_34686 : _87026 -> Prop) : (term1132 _87026 _34685 _34686) = (term1107 _87026 _34685 _34686).
Proof. exact (eq_refl (term1132 _87026 _34685 _34686)). Qed.
Lemma lem3338839 {_87026 : Type'} (_34685 : _87026 -> Prop) (_34686 : _87026 -> Prop) (h1 : term167 _87026) : term1107 _87026 _34685 _34686.
Proof. exact (EQ_MP (@lem3338838 _87026 _34685 _34686) (@lem3338837 _87026 _34685 _34686 h1)). Qed.
Lemma lem3338840 {_87026 : Type'} (_34685 : _87026 -> Prop) (_34686 : _87026 -> Prop) (_34687 : _87026) (h1 : term167 _87026) : term1133 _87026 _34685 _34686 _34687.
Proof. exact (@lem3338839 _87026 _34685 _34686 h1 _34687). Qed.
Lemma lem3338841 {_87026 : Type'} (_34685 : _87026 -> Prop) (_34687 : _87026) (_34686 : _87026 -> Prop) : (term1133 _87026 _34685 _34686 _34687) = (term1104 _87026 _34685 _34687 _34686).
Proof. exact (eq_refl (term1133 _87026 _34685 _34686 _34687)). Qed.
Lemma lem3338842 {_87026 : Type'} (_34685 : _87026 -> Prop) (_34687 : _87026) (_34686 : _87026 -> Prop) (h1 : term167 _87026) : term1104 _87026 _34685 _34687 _34686.
Proof. exact (EQ_MP (@lem3338841 _87026 _34685 _34687 _34686) (@lem3338840 _87026 _34685 _34686 _34687 h1)). Qed.
Lemma lem3338861 {_87026 : Type'} (_34694 : _87026 -> Prop) (s' : type686 _87026) (x'' : _87026) (h1 : term206 _87026 s' x'') : term1134 _87026 s' x'' _34694.
Proof. exact (@lem3338413 _87026 s' x'' h1 _34694). Qed.
Lemma lem3338862 {_87026 : Type'} (s' : type686 _87026) (x'' : _87026) (_34694 : _87026 -> Prop) : (term1134 _87026 s' x'' _34694) = (term197 _87026 s' x'' _34694).
Proof. exact (eq_refl (term1134 _87026 s' x'' _34694)). Qed.
Lemma lem3338951 {_86990 : Type'} (_34563 : _86990 -> Prop) (_34565 : _86990) (_34564 : _86990 -> Prop) (h1 : term167 _86990) : term1004 _86990 _34563 _34565 _34564.
Proof. exact (EQ_MP (@lem3338475 _86990 _34563 _34565 _34564) (@lem3338474 _86990 _34563 _34564 _34565 h1)). Qed.
Lemma lem3338962 {_86990 : Type'} (s : type686 _86990) (_34570 : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (_34569 : _86990 -> Prop) : (term1098 _86990 s _34570 t x _34569) = (term1137 _86990 s _34570 t x _34569).
Proof. exact (@lem3329643 (term1138 _86990 _34570 s) (term1139 _86990 _34569 _34570 t) (term207 _86990 x _34569)). Qed.
Lemma lem3338963 {_86990 : Type'} (_34570 : _86990 -> Prop) (_34569 : _86990 -> Prop) (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term1137 _86990 s _34570 t x _34569.
Proof. exact (EQ_MP (@lem3338962 _86990 s _34570 t x _34569) (@lem3338491 _86990 _34570 _34569 t' s t x h1)). Qed.
Lemma lem3339059 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : @IN _86990 x t'.
Proof. exact (proj2 (@lem3336892 _86990 s x' t x t' h1)). Qed.
Lemma lem3339063 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : t' = (@INTER _86990 x' t).
Proof. exact (proj2 (@lem3336895 _86990 s x' t x t' h1)). Qed.
Lemma lem3339159 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : @IN _86990 x t'.
Proof. exact (proj2 (@lem3336892 _86990 s x' t x t' h1)). Qed.
Lemma lem3339163 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : t' = (@INTER _86990 x' t).
Proof. exact (proj2 (@lem3336895 _86990 s x' t x t' h1)). Qed.
Lemma lem3339165 {_86990 : Type'} (x : _86990) (t : _86990 -> Prop) (h1 : term207 _86990 x t) : term207 _86990 x t.
Proof. exact (h1). Qed.
Lemma lem3339243 {_87026 : Type'} (_34632 : _87026 -> Prop) (_34634 : _87026) (_34633 : _87026 -> Prop) (h1 : term167 _87026) : term1004 _87026 _34632 _34634 _34633.
Proof. exact (EQ_MP (@lem3338682 _87026 _34632 _34634 _34633) (@lem3338681 _87026 _34632 _34633 _34634 h1)). Qed.
Lemma lem3339264 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (_34645 : _87026 -> Prop) (x'' : _87026) (_34644 : _87026 -> Prop) : (term1123 _87026 s' t'' _34645 x'' _34644) = (term1140 _87026 s' t'' _34645 x'' _34644).
Proof. exact (@lem3329643 (term1138 _87026 _34645 s') (term1139 _87026 _34644 t'' _34645) (term207 _87026 x'' _34644)). Qed.
Lemma lem3339265 {_87026 : Type'} (_34645 : _87026 -> Prop) (_34644 : _87026 -> Prop) (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term1140 _87026 s' t'' _34645 x'' _34644.
Proof. exact (EQ_MP (@lem3339264 _87026 s' t'' _34645 x'' _34644) (@lem3338716 _87026 _34645 _34644 t''' s' t'' x'' h1)). Qed.
Lemma lem3339361 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : @IN _87026 x'' t'''.
Proof. exact (proj2 (@lem3336908 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3339365 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : t''' = (@INTER _87026 t'' x''').
Proof. exact (proj2 (@lem3336911 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3339367 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) (h1 : term207 _87026 x'' t'') : term207 _87026 x'' t''.
Proof. exact (h1). Qed.
Lemma lem3339457 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : @IN _87026 x'' t'''.
Proof. exact (proj2 (@lem3336908 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3339461 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : t''' = (@INTER _87026 t'' x''').
Proof. exact (proj2 (@lem3336911 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3339586 {_86990 : Type'} (x : _86990) : (term1141 _86990 x) = (term1141 _86990 x).
Proof. exact (eq_refl (term1141 _86990 x)). Qed.
Lemma lem3339587 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : (term1142 _86990 x t') = (term1143 _86990 x x' t).
Proof. exact (MK_COMB (@lem3339586 _86990 x) (@lem3339063 _86990 s x' t x t' h1)). Qed.
Lemma lem3339588 {_86990 : Type'} (x : _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) : (term1143 _86990 x x' t) = (term12 _86990 x x' t).
Proof. exact (eq_refl (term1143 _86990 x x' t)). Qed.
Lemma lem3339589 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (term1144 _86990 x t') = (term1144 _86990 x t').
Proof. exact (eq_refl (term1144 _86990 x t')). Qed.
Lemma lem3339590 {_86990 : Type'} (t' : _86990 -> Prop) (x : _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) : ((term1142 _86990 x t') = (term1143 _86990 x x' t)) = ((term1142 _86990 x t') = (term12 _86990 x x' t)).
Proof. exact (MK_COMB (@lem3339589 _86990 x t') (@lem3339588 _86990 x x' t)). Qed.
Lemma lem3339591 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (term1142 _86990 x t') = (@IN _86990 x t').
Proof. exact (eq_refl (term1142 _86990 x t')). Qed.
Lemma lem3339592 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3339593 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (term1144 _86990 x t') = (term1145 _86990 x t').
Proof. exact (MK_COMB (@lem3339592) (@lem3339591 _86990 x t')). Qed.
Lemma lem3339594 {_86990 : Type'} (x : _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) : (term12 _86990 x x' t) = (term12 _86990 x x' t).
Proof. exact (eq_refl (term12 _86990 x x' t)). Qed.
Lemma lem3339595 {_86990 : Type'} (t' : _86990 -> Prop) (x : _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) : ((term1142 _86990 x t') = (term12 _86990 x x' t)) = ((@IN _86990 x t') = (term12 _86990 x x' t)).
Proof. exact (MK_COMB (@lem3339593 _86990 x t') (@lem3339594 _86990 x x' t)). Qed.
Lemma lem3339596 {_86990 : Type'} (t' : _86990 -> Prop) (x : _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) : ((term1142 _86990 x t') = (term1143 _86990 x x' t)) = ((@IN _86990 x t') = (term12 _86990 x x' t)).
Proof. exact (TRANS (@lem3339590 _86990 t' x x' t) (@lem3339595 _86990 t' x x' t)). Qed.
Lemma lem3339597 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : (@IN _86990 x t') = (term12 _86990 x x' t).
Proof. exact (EQ_MP (@lem3339596 _86990 t' x x' t) (@lem3339587 _86990 s x' t x t' h1)). Qed.
Lemma lem3339626 {_86990 : Type'} (_34595 : _86990 -> Prop) (s : type686 _86990) (x : _86990) (h1 : term206 _86990 s x) : term197 _86990 s x _34595.
Proof. exact (EQ_MP (@lem3338565 _86990 s x _34595) (@lem3338564 _86990 _34595 s x h1)). Qed.
Lemma lem3339640 {_86990 : Type'} (_34593 : _86990 -> Prop) (_34594 : _86990) (_34592 : _86990 -> Prop) (h1 : term167 _86990) : term1146 _86990 _34593 _34594 _34592.
Proof. exact (proj1 (@lem3338563 _86990 _34592 _34594 _34593 h1)). Qed.
Lemma lem3339809 {_86990 : Type'} (x : _86990) : (term1141 _86990 x) = (term1141 _86990 x).
Proof. exact (eq_refl (term1141 _86990 x)). Qed.
Lemma lem3339810 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : (term1142 _86990 x t') = (term1143 _86990 x x' t).
Proof. exact (MK_COMB (@lem3339809 _86990 x) (@lem3339163 _86990 s x' t x t' h1)). Qed.
Lemma lem3339811 {_86990 : Type'} (x : _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) : (term1143 _86990 x x' t) = (term12 _86990 x x' t).
Proof. exact (eq_refl (term1143 _86990 x x' t)). Qed.
Lemma lem3339812 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (term1144 _86990 x t') = (term1144 _86990 x t').
Proof. exact (eq_refl (term1144 _86990 x t')). Qed.
Lemma lem3339813 {_86990 : Type'} (t' : _86990 -> Prop) (x : _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) : ((term1142 _86990 x t') = (term1143 _86990 x x' t)) = ((term1142 _86990 x t') = (term12 _86990 x x' t)).
Proof. exact (MK_COMB (@lem3339812 _86990 x t') (@lem3339811 _86990 x x' t)). Qed.
Lemma lem3339814 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (term1142 _86990 x t') = (@IN _86990 x t').
Proof. exact (eq_refl (term1142 _86990 x t')). Qed.
Lemma lem3339815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3339816 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (term1144 _86990 x t') = (term1145 _86990 x t').
Proof. exact (MK_COMB (@lem3339815) (@lem3339814 _86990 x t')). Qed.
Lemma lem3339817 {_86990 : Type'} (x : _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) : (term12 _86990 x x' t) = (term12 _86990 x x' t).
Proof. exact (eq_refl (term12 _86990 x x' t)). Qed.
Lemma lem3339818 {_86990 : Type'} (t' : _86990 -> Prop) (x : _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) : ((term1142 _86990 x t') = (term12 _86990 x x' t)) = ((@IN _86990 x t') = (term12 _86990 x x' t)).
Proof. exact (MK_COMB (@lem3339816 _86990 x t') (@lem3339817 _86990 x x' t)). Qed.
Lemma lem3339819 {_86990 : Type'} (t' : _86990 -> Prop) (x : _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) : ((term1142 _86990 x t') = (term1143 _86990 x x' t)) = ((@IN _86990 x t') = (term12 _86990 x x' t)).
Proof. exact (TRANS (@lem3339813 _86990 t' x x' t) (@lem3339818 _86990 t' x x' t)). Qed.
Lemma lem3339820 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : (@IN _86990 x t') = (term12 _86990 x x' t).
Proof. exact (EQ_MP (@lem3339819 _86990 t' x x' t) (@lem3339810 _86990 s x' t x t' h1)). Qed.
Lemma lem3339849 {_86990 : Type'} (x : _86990) (t : _86990 -> Prop) (h1 : term207 _86990 x t) : term207 _86990 x t.
Proof. exact (h1). Qed.
Lemma lem3339877 {_86990 : Type'} (_34617 : _86990 -> Prop) (_34619 : _86990) (_34618 : _86990 -> Prop) (h1 : term167 _86990) : term1147 _86990 _34617 _34619 _34618.
Proof. exact (proj2 (@lem3338638 _86990 _34617 _34619 _34618 h1)). Qed.
Lemma lem3340032 {_87026 : Type'} (x'' : _87026) : (term1141 _87026 x'') = (term1141 _87026 x'').
Proof. exact (eq_refl (term1141 _87026 x'')). Qed.
Lemma lem3340033 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : (term1142 _87026 x'' t''') = (term1143 _87026 x'' t'' x''').
Proof. exact (MK_COMB (@lem3340032 _87026 x'') (@lem3339365 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3340034 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) : (term1143 _87026 x'' t'' x''') = (term12 _87026 x'' t'' x''').
Proof. exact (eq_refl (term1143 _87026 x'' t'' x''')). Qed.
Lemma lem3340035 {_87026 : Type'} (x'' : _87026) (t''' : _87026 -> Prop) : (term1144 _87026 x'' t''') = (term1144 _87026 x'' t''').
Proof. exact (eq_refl (term1144 _87026 x'' t''')). Qed.
Lemma lem3340036 {_87026 : Type'} (t''' : _87026 -> Prop) (x'' : _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) : ((term1142 _87026 x'' t''') = (term1143 _87026 x'' t'' x''')) = ((term1142 _87026 x'' t''') = (term12 _87026 x'' t'' x''')).
Proof. exact (MK_COMB (@lem3340035 _87026 x'' t''') (@lem3340034 _87026 x'' t'' x''')). Qed.
Lemma lem3340037 {_87026 : Type'} (x'' : _87026) (t''' : _87026 -> Prop) : (term1142 _87026 x'' t''') = (@IN _87026 x'' t''').
Proof. exact (eq_refl (term1142 _87026 x'' t''')). Qed.
Lemma lem3340038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3340039 {_87026 : Type'} (x'' : _87026) (t''' : _87026 -> Prop) : (term1144 _87026 x'' t''') = (term1145 _87026 x'' t''').
Proof. exact (MK_COMB (@lem3340038) (@lem3340037 _87026 x'' t''')). Qed.
Lemma lem3340040 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) : (term12 _87026 x'' t'' x''') = (term12 _87026 x'' t'' x''').
Proof. exact (eq_refl (term12 _87026 x'' t'' x''')). Qed.
Lemma lem3340041 {_87026 : Type'} (t''' : _87026 -> Prop) (x'' : _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) : ((term1142 _87026 x'' t''') = (term12 _87026 x'' t'' x''')) = ((@IN _87026 x'' t''') = (term12 _87026 x'' t'' x''')).
Proof. exact (MK_COMB (@lem3340039 _87026 x'' t''') (@lem3340040 _87026 x'' t'' x''')). Qed.
Lemma lem3340042 {_87026 : Type'} (t''' : _87026 -> Prop) (x'' : _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) : ((term1142 _87026 x'' t''') = (term1143 _87026 x'' t'' x''')) = ((@IN _87026 x'' t''') = (term12 _87026 x'' t'' x''')).
Proof. exact (TRANS (@lem3340036 _87026 t''' x'' t'' x''') (@lem3340041 _87026 t''' x'' t'' x''')). Qed.
Lemma lem3340043 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : (@IN _87026 x'' t''') = (term12 _87026 x'' t'' x''').
Proof. exact (EQ_MP (@lem3340042 _87026 t''' x'' t'' x''') (@lem3340033 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3340072 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) (h1 : term207 _87026 x'' t'') : term207 _87026 x'' t''.
Proof. exact (h1). Qed.
Lemma lem3340114 {_87026 : Type'} (_34662 : _87026 -> Prop) (_34663 : _87026) (_34661 : _87026 -> Prop) (h1 : term167 _87026) : term1146 _87026 _34662 _34663 _34661.
Proof. exact (proj1 (@lem3338770 _87026 _34661 _34663 _34662 h1)). Qed.
Lemma lem3340255 {_87026 : Type'} (x'' : _87026) : (term1141 _87026 x'') = (term1141 _87026 x'').
Proof. exact (eq_refl (term1141 _87026 x'')). Qed.
Lemma lem3340256 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : (term1142 _87026 x'' t''') = (term1143 _87026 x'' t'' x''').
Proof. exact (MK_COMB (@lem3340255 _87026 x'') (@lem3339461 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3340257 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) : (term1143 _87026 x'' t'' x''') = (term12 _87026 x'' t'' x''').
Proof. exact (eq_refl (term1143 _87026 x'' t'' x''')). Qed.
Lemma lem3340258 {_87026 : Type'} (x'' : _87026) (t''' : _87026 -> Prop) : (term1144 _87026 x'' t''') = (term1144 _87026 x'' t''').
Proof. exact (eq_refl (term1144 _87026 x'' t''')). Qed.
Lemma lem3340259 {_87026 : Type'} (t''' : _87026 -> Prop) (x'' : _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) : ((term1142 _87026 x'' t''') = (term1143 _87026 x'' t'' x''')) = ((term1142 _87026 x'' t''') = (term12 _87026 x'' t'' x''')).
Proof. exact (MK_COMB (@lem3340258 _87026 x'' t''') (@lem3340257 _87026 x'' t'' x''')). Qed.
Lemma lem3340260 {_87026 : Type'} (x'' : _87026) (t''' : _87026 -> Prop) : (term1142 _87026 x'' t''') = (@IN _87026 x'' t''').
Proof. exact (eq_refl (term1142 _87026 x'' t''')). Qed.
Lemma lem3340261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3340262 {_87026 : Type'} (x'' : _87026) (t''' : _87026 -> Prop) : (term1144 _87026 x'' t''') = (term1145 _87026 x'' t''').
Proof. exact (MK_COMB (@lem3340261) (@lem3340260 _87026 x'' t''')). Qed.
Lemma lem3340263 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) : (term12 _87026 x'' t'' x''') = (term12 _87026 x'' t'' x''').
Proof. exact (eq_refl (term12 _87026 x'' t'' x''')). Qed.
Lemma lem3340264 {_87026 : Type'} (t''' : _87026 -> Prop) (x'' : _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) : ((term1142 _87026 x'' t''') = (term12 _87026 x'' t'' x''')) = ((@IN _87026 x'' t''') = (term12 _87026 x'' t'' x''')).
Proof. exact (MK_COMB (@lem3340262 _87026 x'' t''') (@lem3340263 _87026 x'' t'' x''')). Qed.
Lemma lem3340265 {_87026 : Type'} (t''' : _87026 -> Prop) (x'' : _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) : ((term1142 _87026 x'' t''') = (term1143 _87026 x'' t'' x''')) = ((@IN _87026 x'' t''') = (term12 _87026 x'' t'' x''')).
Proof. exact (TRANS (@lem3340259 _87026 t''' x'' t'' x''') (@lem3340264 _87026 t''' x'' t'' x''')). Qed.
Lemma lem3340266 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : (@IN _87026 x'' t''') = (term12 _87026 x'' t'' x''').
Proof. exact (EQ_MP (@lem3340265 _87026 t''' x'' t'' x''') (@lem3340256 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3340295 {_87026 : Type'} (_34694 : _87026 -> Prop) (s' : type686 _87026) (x'' : _87026) (h1 : term206 _87026 s' x'') : term197 _87026 s' x'' _34694.
Proof. exact (EQ_MP (@lem3338862 _87026 s' x'' _34694) (@lem3338861 _87026 _34694 s' x'' h1)). Qed.
Lemma lem3340351 {_87026 : Type'} (_34685 : _87026 -> Prop) (_34687 : _87026) (_34686 : _87026 -> Prop) (h1 : term167 _87026) : term1147 _87026 _34685 _34687 _34686.
Proof. exact (proj2 (@lem3338842 _87026 _34685 _34687 _34686 h1)). Qed.
Lemma lem3340557 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : @IN (_86990 -> Prop) t' s.
Proof. exact (proj1 (@lem3336889 _86990 t' s t x h1)). Qed.
Lemma lem3340558 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term1148 _86990 t' s.
Proof. exact (fun h0 : term1138 _86990 t' s => @lem3340557 _86990 t' s t x h1). Qed.
Lemma lem3340560 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340561 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) : (term1148 _86990 t' s) = (@IN (_86990 -> Prop) t' s).
Proof. exact (@lem3340560 (@IN (_86990 -> Prop) t' s)). Qed.
Lemma lem3340562 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : @IN (_86990 -> Prop) t' s.
Proof. exact (EQ_MP (@lem3340561 _86990 t' s) (@lem3340558 _86990 t' s t x h1)). Qed.
Lemma lem3340564 {_86990 : Type'} (x : _86990 -> Prop) : x = x.
Proof. exact (@lem21386 (_86990 -> Prop) x). Qed.
Lemma lem3340565 {_86990 : Type'} (x : _86990 -> Prop) : x = x.
Proof. exact (@lem3340564 _86990 x). Qed.
Lemma lem3340566 {_86990 : Type'} (t' : _86990 -> Prop) (t : _86990 -> Prop) : (@INTER _86990 t' t) = (@INTER _86990 t' t).
Proof. exact (@lem3340565 _86990 (@INTER _86990 t' t)). Qed.
Lemma lem3340567 {_86990 : Type'} (t' : _86990 -> Prop) (t : _86990 -> Prop) : term1150 _86990 t' t.
Proof. exact (fun h0 : term1151 _86990 t' t => @lem3340566 _86990 t' t). Qed.
Lemma lem3340569 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340570 {_86990 : Type'} (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term1150 _86990 t' t) = ((@INTER _86990 t' t) = (@INTER _86990 t' t)).
Proof. exact (@lem3340569 ((@INTER _86990 t' t) = (@INTER _86990 t' t))). Qed.
Lemma lem3340571 {_86990 : Type'} (t' : _86990 -> Prop) (t : _86990 -> Prop) : (@INTER _86990 t' t) = (@INTER _86990 t' t).
Proof. exact (EQ_MP (@lem3340570 _86990 t' t) (@lem3340567 _86990 t' t)). Qed.
Lemma lem3340573 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : @IN _86990 x t'.
Proof. exact (proj2 (@lem3336889 _86990 t' s t x h1)). Qed.
Lemma lem3340574 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term1152 _86990 x t'.
Proof. exact (fun h0 : term207 _86990 x t' => @lem3340573 _86990 t' s t x h1). Qed.
Lemma lem3340576 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340577 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) : (term1152 _86990 x t') = (@IN _86990 x t').
Proof. exact (@lem3340576 (@IN _86990 x t')). Qed.
Lemma lem3340578 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : @IN _86990 x t'.
Proof. exact (EQ_MP (@lem3340577 _86990 x t') (@lem3340574 _86990 t' s t x h1)). Qed.
Lemma lem3340580 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : @IN _86990 x t.
Proof. exact (proj2 (@lem3336887 _86990 t' s t x h1)). Qed.
Lemma lem3340581 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term1152 _86990 x t.
Proof. exact (fun h0 : term207 _86990 x t => @lem3340580 _86990 t' s t x h1). Qed.
Lemma lem3340583 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340584 {_86990 : Type'} (x : _86990) (t : _86990 -> Prop) : (term1152 _86990 x t) = (@IN _86990 x t).
Proof. exact (@lem3340583 (@IN _86990 x t)). Qed.
Lemma lem3340585 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : @IN _86990 x t.
Proof. exact (EQ_MP (@lem3340584 _86990 x t) (@lem3340581 _86990 t' s t x h1)). Qed.
Lemma lem3340587 (b : Prop) (a : Prop) : (a \/ b) = (term1153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3340588 {_86990 : Type'} (_34565 : _86990) (_34563 : _86990 -> Prop) (_34564 : _86990 -> Prop) : (term1004 _86990 _34563 _34565 _34564) = (term1154 _86990 _34565 _34563 _34564).
Proof. exact (@lem3340587 (term1000 _86990 _34563 _34565 _34564) (term12 _86990 _34565 _34563 _34564)). Qed.
Lemma lem3340590 (a : Prop) (b : Prop) : (term1155 a b) = (term1156 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3340591 {_86990 : Type'} (_34563 : _86990 -> Prop) (_34565 : _86990) (_34564 : _86990 -> Prop) : (term1157 _86990 _34563 _34565 _34564) = (term1158 _86990 _34563 _34565 _34564).
Proof. exact (@lem3340590 (term207 _86990 _34565 _34563) (term207 _86990 _34565 _34564)). Qed.
Lemma lem3340593 (a : Prop) : (term1159 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3340594 {_86990 : Type'} (_34565 : _86990) (_34563 : _86990 -> Prop) : (term1160 _86990 _34565 _34563) = (@IN _86990 _34565 _34563).
Proof. exact (@lem3340593 (@IN _86990 _34565 _34563)). Qed.
Lemma lem3340595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3340596 {_86990 : Type'} (_34565 : _86990) (_34563 : _86990 -> Prop) : (term1161 _86990 _34565 _34563) = (term120 _86990 _34565 _34563).
Proof. exact (MK_COMB (@lem3340595) (@lem3340594 _86990 _34565 _34563)). Qed.
Lemma lem3340598 (a : Prop) : (term1159 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3340599 {_86990 : Type'} (_34565 : _86990) (_34564 : _86990 -> Prop) : (term1160 _86990 _34565 _34564) = (@IN _86990 _34565 _34564).
Proof. exact (@lem3340598 (@IN _86990 _34565 _34564)). Qed.
Lemma lem3340600 {_86990 : Type'} (_34563 : _86990 -> Prop) (_34565 : _86990) (_34564 : _86990 -> Prop) : (term1158 _86990 _34563 _34565 _34564) = (term13 _86990 _34563 _34565 _34564).
Proof. exact (MK_COMB (@lem3340596 _86990 _34565 _34563) (@lem3340599 _86990 _34565 _34564)). Qed.
Lemma lem3340601 {_86990 : Type'} (_34563 : _86990 -> Prop) (_34565 : _86990) (_34564 : _86990 -> Prop) : (term1157 _86990 _34563 _34565 _34564) = (term13 _86990 _34563 _34565 _34564).
Proof. exact (TRANS (@lem3340591 _86990 _34563 _34565 _34564) (@lem3340600 _86990 _34563 _34565 _34564)). Qed.
Lemma lem3340602 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3340603 {_86990 : Type'} (_34563 : _86990 -> Prop) (_34565 : _86990) (_34564 : _86990 -> Prop) : (term1162 _86990 _34563 _34565 _34564) = (term1163 _86990 _34563 _34565 _34564).
Proof. exact (MK_COMB (@lem3340602) (@lem3340601 _86990 _34563 _34565 _34564)). Qed.
Lemma lem3340604 {_86990 : Type'} (_34565 : _86990) (_34563 : _86990 -> Prop) (_34564 : _86990 -> Prop) : (term12 _86990 _34565 _34563 _34564) = (term12 _86990 _34565 _34563 _34564).
Proof. exact (eq_refl (term12 _86990 _34565 _34563 _34564)). Qed.
Lemma lem3340605 {_86990 : Type'} (_34565 : _86990) (_34563 : _86990 -> Prop) (_34564 : _86990 -> Prop) : (term1154 _86990 _34565 _34563 _34564) = (term1164 _86990 _34565 _34563 _34564).
Proof. exact (MK_COMB (@lem3340603 _86990 _34563 _34565 _34564) (@lem3340604 _86990 _34565 _34563 _34564)). Qed.
Lemma lem3340606 {_86990 : Type'} (_34565 : _86990) (_34563 : _86990 -> Prop) (_34564 : _86990 -> Prop) : (term1004 _86990 _34563 _34565 _34564) = (term1164 _86990 _34565 _34563 _34564).
Proof. exact (TRANS (@lem3340588 _86990 _34565 _34563 _34564) (@lem3340605 _86990 _34565 _34563 _34564)). Qed.
Lemma lem3340608 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term13 _86990 t' x t.
Proof. exact (conj (@lem3340578 _86990 t' s t x h1) (@lem3340585 _86990 t' s t x h1)). Qed.
Lemma lem3340610 {_86990 : Type'} (_34565 : _86990) (_34563 : _86990 -> Prop) (_34564 : _86990 -> Prop) (h1 : term167 _86990) : term1164 _86990 _34565 _34563 _34564.
Proof. exact (EQ_MP (@lem3340606 _86990 _34565 _34563 _34564) (@lem3338951 _86990 _34563 _34565 _34564 h1)). Qed.
Lemma lem3340611 {_86990 : Type'} (_34565 : _86990) (_34563 : _86990 -> Prop) (_34564 : _86990 -> Prop) (h1 : term167 _86990) : term1164 _86990 _34565 _34563 _34564.
Proof. exact (@lem3340610 _86990 _34565 _34563 _34564 h1). Qed.
Lemma lem3340612 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) (h1 : term167 _86990) : term1164 _86990 x t' t.
Proof. exact (@lem3340611 _86990 x t' t h1). Qed.
Lemma lem3340615 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term167 _86990) (h2 : term501 _86990 t' s t x) : term12 _86990 x t' t.
Proof. exact (@lem3340612 _86990 x t' t h1 (@lem3340608 _86990 t' s t x h2)). Qed.
Lemma lem3340616 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term167 _86990) (h2 : term501 _86990 t' s t x) : term1165 _86990 x t' t.
Proof. exact (fun h0 : term1105 _86990 x t' t => @lem3340615 _86990 t' s t x h1 h2). Qed.
Lemma lem3340618 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340619 {_86990 : Type'} (x : _86990) (t' : _86990 -> Prop) (t : _86990 -> Prop) : (term1165 _86990 x t' t) = (term12 _86990 x t' t).
Proof. exact (@lem3340618 (term12 _86990 x t' t)). Qed.
Lemma lem3340620 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term167 _86990) (h2 : term501 _86990 t' s t x) : term12 _86990 x t' t.
Proof. exact (EQ_MP (@lem3340619 _86990 x t' t) (@lem3340616 _86990 t' s t x h1 h2)). Qed.
Lemma lem3340622 (a : Prop) (b : Prop) : (term1166 a b) = (term1167 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3340623 {_86990 : Type'} (_34570 : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (_34569 : _86990 -> Prop) : (term1168 _86990 _34570 t x _34569) = (term1169 _86990 _34570 t x _34569).
Proof. exact (@lem3340622 (_34569 = (@INTER _86990 _34570 t)) (@IN _86990 x _34569)). Qed.
Lemma lem3340624 {_86990 : Type'} (_34570 : _86990 -> Prop) (s : type686 _86990) : (term1170 _86990 _34570 s) = (term1170 _86990 _34570 s).
Proof. exact (eq_refl (term1170 _86990 _34570 s)). Qed.
Lemma lem3340625 {_86990 : Type'} (s : type686 _86990) (_34570 : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (_34569 : _86990 -> Prop) : (term1137 _86990 s _34570 t x _34569) = (term1171 _86990 s _34570 t x _34569).
Proof. exact (MK_COMB (@lem3340624 _86990 _34570 s) (@lem3340623 _86990 _34570 t x _34569)). Qed.
Lemma lem3340627 (a : Prop) (b : Prop) : (term1166 a b) = (term1167 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3340628 {_86990 : Type'} (s : type686 _86990) (_34570 : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (_34569 : _86990 -> Prop) : (term1171 _86990 s _34570 t x _34569) = (term1172 _86990 s _34570 t x _34569).
Proof. exact (@lem3340627 (@IN (_86990 -> Prop) _34570 s) (term1173 _86990 _34570 t x _34569)). Qed.
Lemma lem3340629 {_86990 : Type'} (s : type686 _86990) (_34570 : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (_34569 : _86990 -> Prop) : (term1137 _86990 s _34570 t x _34569) = (term1172 _86990 s _34570 t x _34569).
Proof. exact (TRANS (@lem3340625 _86990 s _34570 t x _34569) (@lem3340628 _86990 s _34570 t x _34569)). Qed.
Lemma lem3340631 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3340632 {_86990 : Type'} (s : type686 _86990) (_34570 : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (_34569 : _86990 -> Prop) : (term1172 _86990 s _34570 t x _34569) = (term1174 _86990 s _34570 t x _34569).
Proof. exact (@lem3340631 (term1175 _86990 s _34570 t x _34569)). Qed.
Lemma lem3340633 {_86990 : Type'} (s : type686 _86990) (_34570 : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (_34569 : _86990 -> Prop) : (term1137 _86990 s _34570 t x _34569) = (term1174 _86990 s _34570 t x _34569).
Proof. exact (TRANS (@lem3340629 _86990 s _34570 t x _34569) (@lem3340632 _86990 s _34570 t x _34569)). Qed.
Lemma lem3340635 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term167 _86990) (h2 : term501 _86990 t' s t x) : term1176 _86990 x t' t.
Proof. exact (conj (@lem3340571 _86990 t' t) (@lem3340620 _86990 t' s t x h1 h2)). Qed.
Lemma lem3340636 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term167 _86990) (h2 : term501 _86990 t' s t x) : term1177 _86990 s x t' t.
Proof. exact (conj (@lem3340562 _86990 t' s t x h2) (@lem3340635 _86990 t' s t x h1 h2)). Qed.
Lemma lem3340638 {_86990 : Type'} (_34570 : _86990 -> Prop) (_34569 : _86990 -> Prop) (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term1174 _86990 s _34570 t x _34569.
Proof. exact (EQ_MP (@lem3340633 _86990 s _34570 t x _34569) (@lem3338963 _86990 _34570 _34569 t' s t x h1)). Qed.
Lemma lem3340639 {_86990 : Type'} (_34570 : _86990 -> Prop) (_34569 : _86990 -> Prop) (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term1174 _86990 s _34570 t x _34569.
Proof. exact (@lem3340638 _86990 _34570 _34569 t' s t x h1). Qed.
Lemma lem3340640 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term501 _86990 t' s t x) : term1178 _86990 s x t' t.
Proof. exact (@lem3340639 _86990 t' (@INTER _86990 t' t) t' s t x h1). Qed.
Lemma lem3340643 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term167 _86990) (h2 : term501 _86990 t' s t x) : False.
Proof. exact (@lem3340640 _86990 t' s t x h2 (@lem3340636 _86990 t' s t x h1 h2)). Qed.
Lemma lem3340644 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term167 _86990) (h2 : term501 _86990 t' s t x) : term1179.
Proof. exact (fun h0 : ~ False => @lem3340643 _86990 t' s t x h1 h2). Qed.
Lemma lem3340646 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340647 : term1179 = False.
Proof. exact (@lem3340646 False). Qed.
Lemma lem3340648 {_86990 : Type'} (t' : _86990 -> Prop) (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term167 _86990) (h2 : term501 _86990 t' s t x) : False.
Proof. exact (EQ_MP (@lem3340647) (@lem3340644 _86990 t' s t x h1 h2)). Qed.
Lemma lem3340650 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : @IN (_86990 -> Prop) x' s.
Proof. exact (proj1 (@lem3336895 _86990 s x' t x t' h1)). Qed.
Lemma lem3340651 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : term1148 _86990 x' s.
Proof. exact (fun h0 : term1138 _86990 x' s => @lem3340650 _86990 s x' t x t' h1). Qed.
Lemma lem3340653 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340654 {_86990 : Type'} (x' : _86990 -> Prop) (s : type686 _86990) : (term1148 _86990 x' s) = (@IN (_86990 -> Prop) x' s).
Proof. exact (@lem3340653 (@IN (_86990 -> Prop) x' s)). Qed.
Lemma lem3340655 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : @IN (_86990 -> Prop) x' s.
Proof. exact (EQ_MP (@lem3340654 _86990 x' s) (@lem3340651 _86990 s x' t x t' h1)). Qed.
Lemma lem3340657 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : term12 _86990 x x' t.
Proof. exact (EQ_MP (@lem3339597 _86990 s x' t x t' h1) (@lem3339059 _86990 s x' t x t' h1)). Qed.
Lemma lem3340658 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : term1165 _86990 x x' t.
Proof. exact (fun h0 : term1105 _86990 x x' t => @lem3340657 _86990 s x' t x t' h1). Qed.
Lemma lem3340660 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340661 {_86990 : Type'} (x : _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) : (term1165 _86990 x x' t) = (term12 _86990 x x' t).
Proof. exact (@lem3340660 (term12 _86990 x x' t)). Qed.
Lemma lem3340662 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : term12 _86990 x x' t.
Proof. exact (EQ_MP (@lem3340661 _86990 x x' t) (@lem3340658 _86990 s x' t x t' h1)). Qed.
Lemma lem3340668 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3340669 {_86990 : Type'} (_34594 : _86990) (_34592 : _86990 -> Prop) (_34593 : _86990 -> Prop) : (term1146 _86990 _34593 _34594 _34592) = (term1180 _86990 _34594 _34592 _34593).
Proof. exact (@lem3340668 (@IN _86990 _34594 _34592) (term1105 _86990 _34594 _34592 _34593)). Qed.
Lemma lem3340675 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3340676 {_86990 : Type'} (_34594 : _86990) (_34592 : _86990 -> Prop) (_34593 : _86990 -> Prop) : (term1181 _86990 _34593 _34594 _34592) = (term1182 _86990 _34594 _34592 _34593).
Proof. exact (MK_COMB (@lem3340675) (@lem3340669 _86990 _34594 _34592 _34593)). Qed.
Lemma lem3340682 {_86990 : Type'} (_34594 : _86990) (_34592 : _86990 -> Prop) (_34593 : _86990 -> Prop) : (term1180 _86990 _34594 _34592 _34593) = (term1180 _86990 _34594 _34592 _34593).
Proof. exact (eq_refl (term1180 _86990 _34594 _34592 _34593)). Qed.
Lemma lem3340683 {_86990 : Type'} (_34594 : _86990) (_34592 : _86990 -> Prop) (_34593 : _86990 -> Prop) : ((term1146 _86990 _34593 _34594 _34592) = (term1180 _86990 _34594 _34592 _34593)) = ((term1180 _86990 _34594 _34592 _34593) = (term1180 _86990 _34594 _34592 _34593)).
Proof. exact (MK_COMB (@lem3340676 _86990 _34594 _34592 _34593) (@lem3340682 _86990 _34594 _34592 _34593)). Qed.
Lemma lem3340685 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3340686 (x : Prop) : (x = x) = True.
Proof. exact (@lem3340685 Prop x). Qed.
Lemma lem3340687 {_86990 : Type'} (_34594 : _86990) (_34592 : _86990 -> Prop) (_34593 : _86990 -> Prop) : ((term1180 _86990 _34594 _34592 _34593) = (term1180 _86990 _34594 _34592 _34593)) = True.
Proof. exact (@lem3340686 (term1180 _86990 _34594 _34592 _34593)). Qed.
Lemma lem3340688 {_86990 : Type'} (_34594 : _86990) (_34592 : _86990 -> Prop) (_34593 : _86990 -> Prop) : ((term1146 _86990 _34593 _34594 _34592) = (term1180 _86990 _34594 _34592 _34593)) = True.
Proof. exact (TRANS (@lem3340683 _86990 _34594 _34592 _34593) (@lem3340687 _86990 _34594 _34592 _34593)). Qed.
Lemma lem3340689 {_86990 : Type'} (_34594 : _86990) (_34592 : _86990 -> Prop) (_34593 : _86990 -> Prop) : True = ((term1146 _86990 _34593 _34594 _34592) = (term1180 _86990 _34594 _34592 _34593)).
Proof. exact (SYM (@lem3340688 _86990 _34594 _34592 _34593)). Qed.
Lemma lem3340690 {_86990 : Type'} (_34594 : _86990) (_34592 : _86990 -> Prop) (_34593 : _86990 -> Prop) : (term1146 _86990 _34593 _34594 _34592) = (term1180 _86990 _34594 _34592 _34593).
Proof. exact (EQ_MP (@lem3340689 _86990 _34594 _34592 _34593) (@lem0)). Qed.
Lemma lem3340691 {_86990 : Type'} (_34594 : _86990) (_34592 : _86990 -> Prop) (_34593 : _86990 -> Prop) (h1 : term167 _86990) : term1180 _86990 _34594 _34592 _34593.
Proof. exact (EQ_MP (@lem3340690 _86990 _34594 _34592 _34593) (@lem3339640 _86990 _34593 _34594 _34592 h1)). Qed.
Lemma lem3340693 (b : Prop) (a : Prop) : (a \/ b) = (term1153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3340694 {_86990 : Type'} (_34593 : _86990 -> Prop) (_34594 : _86990) (_34592 : _86990 -> Prop) : (term1180 _86990 _34594 _34592 _34593) = (term1183 _86990 _34593 _34594 _34592).
Proof. exact (@lem3340693 (term1105 _86990 _34594 _34592 _34593) (@IN _86990 _34594 _34592)). Qed.
Lemma lem3340696 (a : Prop) : (term1159 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3340697 {_86990 : Type'} (_34594 : _86990) (_34592 : _86990 -> Prop) (_34593 : _86990 -> Prop) : (term1184 _86990 _34594 _34592 _34593) = (term12 _86990 _34594 _34592 _34593).
Proof. exact (@lem3340696 (term12 _86990 _34594 _34592 _34593)). Qed.
Lemma lem3340698 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3340699 {_86990 : Type'} (_34594 : _86990) (_34592 : _86990 -> Prop) (_34593 : _86990 -> Prop) : (term1185 _86990 _34594 _34592 _34593) = (term1186 _86990 _34594 _34592 _34593).
Proof. exact (MK_COMB (@lem3340698) (@lem3340697 _86990 _34594 _34592 _34593)). Qed.
Lemma lem3340700 {_86990 : Type'} (_34594 : _86990) (_34592 : _86990 -> Prop) : (@IN _86990 _34594 _34592) = (@IN _86990 _34594 _34592).
Proof. exact (eq_refl (@IN _86990 _34594 _34592)). Qed.
Lemma lem3340701 {_86990 : Type'} (_34593 : _86990 -> Prop) (_34594 : _86990) (_34592 : _86990 -> Prop) : (term1183 _86990 _34593 _34594 _34592) = (term1187 _86990 _34593 _34594 _34592).
Proof. exact (MK_COMB (@lem3340699 _86990 _34594 _34592 _34593) (@lem3340700 _86990 _34594 _34592)). Qed.
Lemma lem3340702 {_86990 : Type'} (_34593 : _86990 -> Prop) (_34594 : _86990) (_34592 : _86990 -> Prop) : (term1180 _86990 _34594 _34592 _34593) = (term1187 _86990 _34593 _34594 _34592).
Proof. exact (TRANS (@lem3340694 _86990 _34593 _34594 _34592) (@lem3340701 _86990 _34593 _34594 _34592)). Qed.
Lemma lem3340705 {_86990 : Type'} (_34593 : _86990 -> Prop) (_34594 : _86990) (_34592 : _86990 -> Prop) (h1 : term167 _86990) : term1187 _86990 _34593 _34594 _34592.
Proof. exact (EQ_MP (@lem3340702 _86990 _34593 _34594 _34592) (@lem3340691 _86990 _34594 _34592 _34593 h1)). Qed.
Lemma lem3340706 {_86990 : Type'} (_34593 : _86990 -> Prop) (_34594 : _86990) (_34592 : _86990 -> Prop) (h1 : term167 _86990) : term1187 _86990 _34593 _34594 _34592.
Proof. exact (@lem3340705 _86990 _34593 _34594 _34592 h1). Qed.
Lemma lem3340707 {_86990 : Type'} (t : _86990 -> Prop) (x : _86990) (x' : _86990 -> Prop) (h1 : term167 _86990) : term1187 _86990 t x x'.
Proof. exact (@lem3340706 _86990 t x x' h1). Qed.
Lemma lem3340710 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term553 _86990 s x' t x t') : @IN _86990 x x'.
Proof. exact (@lem3340707 _86990 t x x' h1 (@lem3340662 _86990 s x' t x t' h2)). Qed.
Lemma lem3340711 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term553 _86990 s x' t x t') : term1152 _86990 x x'.
Proof. exact (fun h0 : term207 _86990 x x' => @lem3340710 _86990 s x' t x t' h1 h2). Qed.
Lemma lem3340713 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340714 {_86990 : Type'} (x : _86990) (x' : _86990 -> Prop) : (term1152 _86990 x x') = (@IN _86990 x x').
Proof. exact (@lem3340713 (@IN _86990 x x')). Qed.
Lemma lem3340715 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term553 _86990 s x' t x t') : @IN _86990 x x'.
Proof. exact (EQ_MP (@lem3340714 _86990 x x') (@lem3340711 _86990 s x' t x t' h1 h2)). Qed.
Lemma lem3340717 (a : Prop) (b : Prop) : (term1166 a b) = (term1167 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3340718 {_86990 : Type'} (s : type686 _86990) (x : _86990) (_34595 : _86990 -> Prop) : (term197 _86990 s x _34595) = (term196 _86990 s x _34595).
Proof. exact (@lem3340717 (@IN (_86990 -> Prop) _34595 s) (@IN _86990 x _34595)). Qed.
Lemma lem3340720 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3340721 {_86990 : Type'} (s : type686 _86990) (x : _86990) (_34595 : _86990 -> Prop) : (term196 _86990 s x _34595) = (term1188 _86990 s x _34595).
Proof. exact (@lem3340720 (term194 _86990 s x _34595)). Qed.
Lemma lem3340722 {_86990 : Type'} (s : type686 _86990) (x : _86990) (_34595 : _86990 -> Prop) : (term197 _86990 s x _34595) = (term1188 _86990 s x _34595).
Proof. exact (TRANS (@lem3340718 _86990 s x _34595) (@lem3340721 _86990 s x _34595)). Qed.
Lemma lem3340724 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term553 _86990 s x' t x t') : term194 _86990 s x x'.
Proof. exact (conj (@lem3340655 _86990 s x' t x t' h2) (@lem3340715 _86990 s x' t x t' h1 h2)). Qed.
Lemma lem3340726 {_86990 : Type'} (_34595 : _86990 -> Prop) (s : type686 _86990) (x : _86990) (h1 : term206 _86990 s x) : term1188 _86990 s x _34595.
Proof. exact (EQ_MP (@lem3340722 _86990 s x _34595) (@lem3339626 _86990 _34595 s x h1)). Qed.
Lemma lem3340727 {_86990 : Type'} (_34595 : _86990 -> Prop) (s : type686 _86990) (x : _86990) (h1 : term206 _86990 s x) : term1188 _86990 s x _34595.
Proof. exact (@lem3340726 _86990 _34595 s x h1). Qed.
Lemma lem3340728 {_86990 : Type'} (x' : _86990 -> Prop) (s : type686 _86990) (x : _86990) (h1 : term206 _86990 s x) : term1188 _86990 s x x'.
Proof. exact (@lem3340727 _86990 x' s x h1). Qed.
Lemma lem3340731 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term206 _86990 s x) (h3 : term553 _86990 s x' t x t') : False.
Proof. exact (@lem3340728 _86990 x' s x h2 (@lem3340724 _86990 s x' t x t' h1 h3)). Qed.
Lemma lem3340732 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term206 _86990 s x) (h3 : term553 _86990 s x' t x t') : term1179.
Proof. exact (fun h0 : ~ False => @lem3340731 _86990 s x' t x t' h1 h2 h3). Qed.
Lemma lem3340734 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340735 : term1179 = False.
Proof. exact (@lem3340734 False). Qed.
Lemma lem3340738 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : term12 _86990 x x' t.
Proof. exact (EQ_MP (@lem3339820 _86990 s x' t x t' h1) (@lem3339159 _86990 s x' t x t' h1)). Qed.
Lemma lem3340739 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : term1165 _86990 x x' t.
Proof. exact (fun h0 : term1105 _86990 x x' t => @lem3340738 _86990 s x' t x t' h1). Qed.
Lemma lem3340741 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340742 {_86990 : Type'} (x : _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) : (term1165 _86990 x x' t) = (term12 _86990 x x' t).
Proof. exact (@lem3340741 (term12 _86990 x x' t)). Qed.
Lemma lem3340743 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term553 _86990 s x' t x t') : term12 _86990 x x' t.
Proof. exact (EQ_MP (@lem3340742 _86990 x x' t) (@lem3340739 _86990 s x' t x t' h1)). Qed.
Lemma lem3340749 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3340750 {_86990 : Type'} (_34619 : _86990) (_34617 : _86990 -> Prop) (_34618 : _86990 -> Prop) : (term1147 _86990 _34617 _34619 _34618) = (term1189 _86990 _34619 _34617 _34618).
Proof. exact (@lem3340749 (@IN _86990 _34619 _34618) (term1105 _86990 _34619 _34617 _34618)). Qed.
Lemma lem3340756 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3340757 {_86990 : Type'} (_34619 : _86990) (_34617 : _86990 -> Prop) (_34618 : _86990 -> Prop) : (term1190 _86990 _34617 _34619 _34618) = (term1191 _86990 _34619 _34617 _34618).
Proof. exact (MK_COMB (@lem3340756) (@lem3340750 _86990 _34619 _34617 _34618)). Qed.
Lemma lem3340763 {_86990 : Type'} (_34619 : _86990) (_34617 : _86990 -> Prop) (_34618 : _86990 -> Prop) : (term1189 _86990 _34619 _34617 _34618) = (term1189 _86990 _34619 _34617 _34618).
Proof. exact (eq_refl (term1189 _86990 _34619 _34617 _34618)). Qed.
Lemma lem3340764 {_86990 : Type'} (_34619 : _86990) (_34617 : _86990 -> Prop) (_34618 : _86990 -> Prop) : ((term1147 _86990 _34617 _34619 _34618) = (term1189 _86990 _34619 _34617 _34618)) = ((term1189 _86990 _34619 _34617 _34618) = (term1189 _86990 _34619 _34617 _34618)).
Proof. exact (MK_COMB (@lem3340757 _86990 _34619 _34617 _34618) (@lem3340763 _86990 _34619 _34617 _34618)). Qed.
Lemma lem3340766 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3340767 (x : Prop) : (x = x) = True.
Proof. exact (@lem3340766 Prop x). Qed.
Lemma lem3340768 {_86990 : Type'} (_34619 : _86990) (_34617 : _86990 -> Prop) (_34618 : _86990 -> Prop) : ((term1189 _86990 _34619 _34617 _34618) = (term1189 _86990 _34619 _34617 _34618)) = True.
Proof. exact (@lem3340767 (term1189 _86990 _34619 _34617 _34618)). Qed.
Lemma lem3340769 {_86990 : Type'} (_34619 : _86990) (_34617 : _86990 -> Prop) (_34618 : _86990 -> Prop) : ((term1147 _86990 _34617 _34619 _34618) = (term1189 _86990 _34619 _34617 _34618)) = True.
Proof. exact (TRANS (@lem3340764 _86990 _34619 _34617 _34618) (@lem3340768 _86990 _34619 _34617 _34618)). Qed.
Lemma lem3340770 {_86990 : Type'} (_34619 : _86990) (_34617 : _86990 -> Prop) (_34618 : _86990 -> Prop) : True = ((term1147 _86990 _34617 _34619 _34618) = (term1189 _86990 _34619 _34617 _34618)).
Proof. exact (SYM (@lem3340769 _86990 _34619 _34617 _34618)). Qed.
Lemma lem3340771 {_86990 : Type'} (_34619 : _86990) (_34617 : _86990 -> Prop) (_34618 : _86990 -> Prop) : (term1147 _86990 _34617 _34619 _34618) = (term1189 _86990 _34619 _34617 _34618).
Proof. exact (EQ_MP (@lem3340770 _86990 _34619 _34617 _34618) (@lem0)). Qed.
Lemma lem3340772 {_86990 : Type'} (_34619 : _86990) (_34617 : _86990 -> Prop) (_34618 : _86990 -> Prop) (h1 : term167 _86990) : term1189 _86990 _34619 _34617 _34618.
Proof. exact (EQ_MP (@lem3340771 _86990 _34619 _34617 _34618) (@lem3339877 _86990 _34617 _34619 _34618 h1)). Qed.
Lemma lem3340774 (b : Prop) (a : Prop) : (a \/ b) = (term1153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3340775 {_86990 : Type'} (_34617 : _86990 -> Prop) (_34619 : _86990) (_34618 : _86990 -> Prop) : (term1189 _86990 _34619 _34617 _34618) = (term1192 _86990 _34617 _34619 _34618).
Proof. exact (@lem3340774 (term1105 _86990 _34619 _34617 _34618) (@IN _86990 _34619 _34618)). Qed.
Lemma lem3340777 (a : Prop) : (term1159 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3340778 {_86990 : Type'} (_34619 : _86990) (_34617 : _86990 -> Prop) (_34618 : _86990 -> Prop) : (term1184 _86990 _34619 _34617 _34618) = (term12 _86990 _34619 _34617 _34618).
Proof. exact (@lem3340777 (term12 _86990 _34619 _34617 _34618)). Qed.
Lemma lem3340779 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3340780 {_86990 : Type'} (_34619 : _86990) (_34617 : _86990 -> Prop) (_34618 : _86990 -> Prop) : (term1185 _86990 _34619 _34617 _34618) = (term1186 _86990 _34619 _34617 _34618).
Proof. exact (MK_COMB (@lem3340779) (@lem3340778 _86990 _34619 _34617 _34618)). Qed.
Lemma lem3340781 {_86990 : Type'} (_34619 : _86990) (_34618 : _86990 -> Prop) : (@IN _86990 _34619 _34618) = (@IN _86990 _34619 _34618).
Proof. exact (eq_refl (@IN _86990 _34619 _34618)). Qed.
Lemma lem3340782 {_86990 : Type'} (_34617 : _86990 -> Prop) (_34619 : _86990) (_34618 : _86990 -> Prop) : (term1192 _86990 _34617 _34619 _34618) = (term1193 _86990 _34617 _34619 _34618).
Proof. exact (MK_COMB (@lem3340780 _86990 _34619 _34617 _34618) (@lem3340781 _86990 _34619 _34618)). Qed.
Lemma lem3340783 {_86990 : Type'} (_34617 : _86990 -> Prop) (_34619 : _86990) (_34618 : _86990 -> Prop) : (term1189 _86990 _34619 _34617 _34618) = (term1193 _86990 _34617 _34619 _34618).
Proof. exact (TRANS (@lem3340775 _86990 _34617 _34619 _34618) (@lem3340782 _86990 _34617 _34619 _34618)). Qed.
Lemma lem3340786 {_86990 : Type'} (_34617 : _86990 -> Prop) (_34619 : _86990) (_34618 : _86990 -> Prop) (h1 : term167 _86990) : term1193 _86990 _34617 _34619 _34618.
Proof. exact (EQ_MP (@lem3340783 _86990 _34617 _34619 _34618) (@lem3340772 _86990 _34619 _34617 _34618 h1)). Qed.
Lemma lem3340787 {_86990 : Type'} (_34617 : _86990 -> Prop) (_34619 : _86990) (_34618 : _86990 -> Prop) (h1 : term167 _86990) : term1193 _86990 _34617 _34619 _34618.
Proof. exact (@lem3340786 _86990 _34617 _34619 _34618 h1). Qed.
Lemma lem3340788 {_86990 : Type'} (x' : _86990 -> Prop) (x : _86990) (t : _86990 -> Prop) (h1 : term167 _86990) : term1193 _86990 x' x t.
Proof. exact (@lem3340787 _86990 x' x t h1). Qed.
Lemma lem3340791 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term553 _86990 s x' t x t') : @IN _86990 x t.
Proof. exact (@lem3340788 _86990 x' x t h1 (@lem3340743 _86990 s x' t x t' h2)). Qed.
Lemma lem3340792 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term553 _86990 s x' t x t') : term1152 _86990 x t.
Proof. exact (fun h0 : term207 _86990 x t => @lem3340791 _86990 s x' t x t' h1 h2). Qed.
Lemma lem3340794 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340795 {_86990 : Type'} (x : _86990) (t : _86990 -> Prop) : (term1152 _86990 x t) = (@IN _86990 x t).
Proof. exact (@lem3340794 (@IN _86990 x t)). Qed.
Lemma lem3340796 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term553 _86990 s x' t x t') : @IN _86990 x t.
Proof. exact (EQ_MP (@lem3340795 _86990 x t) (@lem3340792 _86990 s x' t x t' h1 h2)). Qed.
Lemma lem3340799 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3340801 {_86990 : Type'} (x : _86990) (t : _86990 -> Prop) : (term207 _86990 x t) = (term1194 _86990 x t).
Proof. exact (@lem3340799 (@IN _86990 x t)). Qed.
Lemma lem3340804 {_86990 : Type'} (x : _86990) (t : _86990 -> Prop) (h1 : term207 _86990 x t) : term1194 _86990 x t.
Proof. exact (EQ_MP (@lem3340801 _86990 x t) (@lem3339849 _86990 x t h1)). Qed.
Lemma lem3340807 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term207 _86990 x t) (h3 : term553 _86990 s x' t x t') : False.
Proof. exact (@lem3340804 _86990 x t h2 (@lem3340796 _86990 s x' t x t' h1 h3)). Qed.
Lemma lem3340808 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term207 _86990 x t) (h3 : term553 _86990 s x' t x t') : term1179.
Proof. exact (fun h0 : ~ False => @lem3340807 _86990 s x' t x t' h1 h2 h3). Qed.
Lemma lem3340810 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340811 : term1179 = False.
Proof. exact (@lem3340810 False). Qed.
Lemma lem3340812 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term207 _86990 x t) (h3 : term553 _86990 s x' t x t') : False.
Proof. exact (EQ_MP (@lem3340811) (@lem3340808 _86990 s x' t x t' h1 h2 h3)). Qed.
Lemma lem3340962 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : @IN (_87026 -> Prop) t''' s'.
Proof. exact (proj1 (@lem3336904 _87026 t''' s' t'' x'' h1)). Qed.
Lemma lem3340963 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term1148 _87026 t''' s'.
Proof. exact (fun h0 : term1138 _87026 t''' s' => @lem3340962 _87026 t''' s' t'' x'' h1). Qed.
Lemma lem3340965 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340966 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) : (term1148 _87026 t''' s') = (@IN (_87026 -> Prop) t''' s').
Proof. exact (@lem3340965 (@IN (_87026 -> Prop) t''' s')). Qed.
Lemma lem3340967 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : @IN (_87026 -> Prop) t''' s'.
Proof. exact (EQ_MP (@lem3340966 _87026 t''' s') (@lem3340963 _87026 t''' s' t'' x'' h1)). Qed.
Lemma lem3340969 {_87026 : Type'} (x : _87026 -> Prop) : x = x.
Proof. exact (@lem21386 (_87026 -> Prop) x). Qed.
Lemma lem3340970 {_87026 : Type'} (x : _87026 -> Prop) : x = x.
Proof. exact (@lem3340969 _87026 x). Qed.
Lemma lem3340971 {_87026 : Type'} (t'' : _87026 -> Prop) (t''' : _87026 -> Prop) : (@INTER _87026 t'' t''') = (@INTER _87026 t'' t''').
Proof. exact (@lem3340970 _87026 (@INTER _87026 t'' t''')). Qed.
Lemma lem3340972 {_87026 : Type'} (t'' : _87026 -> Prop) (t''' : _87026 -> Prop) : term1150 _87026 t'' t'''.
Proof. exact (fun h0 : term1151 _87026 t'' t''' => @lem3340971 _87026 t'' t'''). Qed.
Lemma lem3340974 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340975 {_87026 : Type'} (t'' : _87026 -> Prop) (t''' : _87026 -> Prop) : (term1150 _87026 t'' t''') = ((@INTER _87026 t'' t''') = (@INTER _87026 t'' t''')).
Proof. exact (@lem3340974 ((@INTER _87026 t'' t''') = (@INTER _87026 t'' t'''))). Qed.
Lemma lem3340976 {_87026 : Type'} (t'' : _87026 -> Prop) (t''' : _87026 -> Prop) : (@INTER _87026 t'' t''') = (@INTER _87026 t'' t''').
Proof. exact (EQ_MP (@lem3340975 _87026 t'' t''') (@lem3340972 _87026 t'' t''')). Qed.
Lemma lem3340978 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : @IN _87026 x'' t''.
Proof. exact (proj1 (@lem3336903 _87026 t''' s' t'' x'' h1)). Qed.
Lemma lem3340979 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term1152 _87026 x'' t''.
Proof. exact (fun h0 : term207 _87026 x'' t'' => @lem3340978 _87026 t''' s' t'' x'' h1). Qed.
Lemma lem3340981 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340982 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) : (term1152 _87026 x'' t'') = (@IN _87026 x'' t'').
Proof. exact (@lem3340981 (@IN _87026 x'' t'')). Qed.
Lemma lem3340983 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : @IN _87026 x'' t''.
Proof. exact (EQ_MP (@lem3340982 _87026 x'' t'') (@lem3340979 _87026 t''' s' t'' x'' h1)). Qed.
Lemma lem3340985 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : @IN _87026 x'' t'''.
Proof. exact (proj2 (@lem3336904 _87026 t''' s' t'' x'' h1)). Qed.
Lemma lem3340986 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term1152 _87026 x'' t'''.
Proof. exact (fun h0 : term207 _87026 x'' t''' => @lem3340985 _87026 t''' s' t'' x'' h1). Qed.
Lemma lem3340988 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3340989 {_87026 : Type'} (x'' : _87026) (t''' : _87026 -> Prop) : (term1152 _87026 x'' t''') = (@IN _87026 x'' t''').
Proof. exact (@lem3340988 (@IN _87026 x'' t''')). Qed.
Lemma lem3340990 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : @IN _87026 x'' t'''.
Proof. exact (EQ_MP (@lem3340989 _87026 x'' t''') (@lem3340986 _87026 t''' s' t'' x'' h1)). Qed.
Lemma lem3340992 (b : Prop) (a : Prop) : (a \/ b) = (term1153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3340993 {_87026 : Type'} (_34634 : _87026) (_34632 : _87026 -> Prop) (_34633 : _87026 -> Prop) : (term1004 _87026 _34632 _34634 _34633) = (term1154 _87026 _34634 _34632 _34633).
Proof. exact (@lem3340992 (term1000 _87026 _34632 _34634 _34633) (term12 _87026 _34634 _34632 _34633)). Qed.
Lemma lem3340995 (a : Prop) (b : Prop) : (term1155 a b) = (term1156 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3340996 {_87026 : Type'} (_34632 : _87026 -> Prop) (_34634 : _87026) (_34633 : _87026 -> Prop) : (term1157 _87026 _34632 _34634 _34633) = (term1158 _87026 _34632 _34634 _34633).
Proof. exact (@lem3340995 (term207 _87026 _34634 _34632) (term207 _87026 _34634 _34633)). Qed.
Lemma lem3340998 (a : Prop) : (term1159 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3340999 {_87026 : Type'} (_34634 : _87026) (_34632 : _87026 -> Prop) : (term1160 _87026 _34634 _34632) = (@IN _87026 _34634 _34632).
Proof. exact (@lem3340998 (@IN _87026 _34634 _34632)). Qed.
Lemma lem3341000 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3341001 {_87026 : Type'} (_34634 : _87026) (_34632 : _87026 -> Prop) : (term1161 _87026 _34634 _34632) = (term120 _87026 _34634 _34632).
Proof. exact (MK_COMB (@lem3341000) (@lem3340999 _87026 _34634 _34632)). Qed.
Lemma lem3341003 (a : Prop) : (term1159 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3341004 {_87026 : Type'} (_34634 : _87026) (_34633 : _87026 -> Prop) : (term1160 _87026 _34634 _34633) = (@IN _87026 _34634 _34633).
Proof. exact (@lem3341003 (@IN _87026 _34634 _34633)). Qed.
Lemma lem3341005 {_87026 : Type'} (_34632 : _87026 -> Prop) (_34634 : _87026) (_34633 : _87026 -> Prop) : (term1158 _87026 _34632 _34634 _34633) = (term13 _87026 _34632 _34634 _34633).
Proof. exact (MK_COMB (@lem3341001 _87026 _34634 _34632) (@lem3341004 _87026 _34634 _34633)). Qed.
Lemma lem3341006 {_87026 : Type'} (_34632 : _87026 -> Prop) (_34634 : _87026) (_34633 : _87026 -> Prop) : (term1157 _87026 _34632 _34634 _34633) = (term13 _87026 _34632 _34634 _34633).
Proof. exact (TRANS (@lem3340996 _87026 _34632 _34634 _34633) (@lem3341005 _87026 _34632 _34634 _34633)). Qed.
Lemma lem3341007 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3341008 {_87026 : Type'} (_34632 : _87026 -> Prop) (_34634 : _87026) (_34633 : _87026 -> Prop) : (term1162 _87026 _34632 _34634 _34633) = (term1163 _87026 _34632 _34634 _34633).
Proof. exact (MK_COMB (@lem3341007) (@lem3341006 _87026 _34632 _34634 _34633)). Qed.
Lemma lem3341009 {_87026 : Type'} (_34634 : _87026) (_34632 : _87026 -> Prop) (_34633 : _87026 -> Prop) : (term12 _87026 _34634 _34632 _34633) = (term12 _87026 _34634 _34632 _34633).
Proof. exact (eq_refl (term12 _87026 _34634 _34632 _34633)). Qed.
Lemma lem3341010 {_87026 : Type'} (_34634 : _87026) (_34632 : _87026 -> Prop) (_34633 : _87026 -> Prop) : (term1154 _87026 _34634 _34632 _34633) = (term1164 _87026 _34634 _34632 _34633).
Proof. exact (MK_COMB (@lem3341008 _87026 _34632 _34634 _34633) (@lem3341009 _87026 _34634 _34632 _34633)). Qed.
Lemma lem3341011 {_87026 : Type'} (_34634 : _87026) (_34632 : _87026 -> Prop) (_34633 : _87026 -> Prop) : (term1004 _87026 _34632 _34634 _34633) = (term1164 _87026 _34634 _34632 _34633).
Proof. exact (TRANS (@lem3340993 _87026 _34634 _34632 _34633) (@lem3341010 _87026 _34634 _34632 _34633)). Qed.
Lemma lem3341013 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term13 _87026 t'' x'' t'''.
Proof. exact (conj (@lem3340983 _87026 t''' s' t'' x'' h1) (@lem3340990 _87026 t''' s' t'' x'' h1)). Qed.
Lemma lem3341015 {_87026 : Type'} (_34634 : _87026) (_34632 : _87026 -> Prop) (_34633 : _87026 -> Prop) (h1 : term167 _87026) : term1164 _87026 _34634 _34632 _34633.
Proof. exact (EQ_MP (@lem3341011 _87026 _34634 _34632 _34633) (@lem3339243 _87026 _34632 _34634 _34633 h1)). Qed.
Lemma lem3341016 {_87026 : Type'} (_34634 : _87026) (_34632 : _87026 -> Prop) (_34633 : _87026 -> Prop) (h1 : term167 _87026) : term1164 _87026 _34634 _34632 _34633.
Proof. exact (@lem3341015 _87026 _34634 _34632 _34633 h1). Qed.
Lemma lem3341017 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) (t''' : _87026 -> Prop) (h1 : term167 _87026) : term1164 _87026 x'' t'' t'''.
Proof. exact (@lem3341016 _87026 x'' t'' t''' h1). Qed.
Lemma lem3341020 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term167 _87026) (h2 : term684 _87026 t''' s' t'' x'') : term12 _87026 x'' t'' t'''.
Proof. exact (@lem3341017 _87026 x'' t'' t''' h1 (@lem3341013 _87026 t''' s' t'' x'' h2)). Qed.
Lemma lem3341021 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term167 _87026) (h2 : term684 _87026 t''' s' t'' x'') : term1165 _87026 x'' t'' t'''.
Proof. exact (fun h0 : term1105 _87026 x'' t'' t''' => @lem3341020 _87026 t''' s' t'' x'' h1 h2). Qed.
Lemma lem3341023 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3341024 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) (t''' : _87026 -> Prop) : (term1165 _87026 x'' t'' t''') = (term12 _87026 x'' t'' t''').
Proof. exact (@lem3341023 (term12 _87026 x'' t'' t''')). Qed.
Lemma lem3341025 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term167 _87026) (h2 : term684 _87026 t''' s' t'' x'') : term12 _87026 x'' t'' t'''.
Proof. exact (EQ_MP (@lem3341024 _87026 x'' t'' t''') (@lem3341021 _87026 t''' s' t'' x'' h1 h2)). Qed.
Lemma lem3341027 (a : Prop) (b : Prop) : (term1166 a b) = (term1167 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3341028 {_87026 : Type'} (t'' : _87026 -> Prop) (_34645 : _87026 -> Prop) (x'' : _87026) (_34644 : _87026 -> Prop) : (term1168 _87026 t'' _34645 x'' _34644) = (term1169 _87026 t'' _34645 x'' _34644).
Proof. exact (@lem3341027 (_34644 = (@INTER _87026 t'' _34645)) (@IN _87026 x'' _34644)). Qed.
Lemma lem3341029 {_87026 : Type'} (_34645 : _87026 -> Prop) (s' : type686 _87026) : (term1170 _87026 _34645 s') = (term1170 _87026 _34645 s').
Proof. exact (eq_refl (term1170 _87026 _34645 s')). Qed.
Lemma lem3341030 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (_34645 : _87026 -> Prop) (x'' : _87026) (_34644 : _87026 -> Prop) : (term1140 _87026 s' t'' _34645 x'' _34644) = (term1195 _87026 s' t'' _34645 x'' _34644).
Proof. exact (MK_COMB (@lem3341029 _87026 _34645 s') (@lem3341028 _87026 t'' _34645 x'' _34644)). Qed.
Lemma lem3341032 (a : Prop) (b : Prop) : (term1166 a b) = (term1167 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3341033 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (_34645 : _87026 -> Prop) (x'' : _87026) (_34644 : _87026 -> Prop) : (term1195 _87026 s' t'' _34645 x'' _34644) = (term1196 _87026 s' t'' _34645 x'' _34644).
Proof. exact (@lem3341032 (@IN (_87026 -> Prop) _34645 s') (term1173 _87026 t'' _34645 x'' _34644)). Qed.
Lemma lem3341034 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (_34645 : _87026 -> Prop) (x'' : _87026) (_34644 : _87026 -> Prop) : (term1140 _87026 s' t'' _34645 x'' _34644) = (term1196 _87026 s' t'' _34645 x'' _34644).
Proof. exact (TRANS (@lem3341030 _87026 s' t'' _34645 x'' _34644) (@lem3341033 _87026 s' t'' _34645 x'' _34644)). Qed.
Lemma lem3341036 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3341037 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (_34645 : _87026 -> Prop) (x'' : _87026) (_34644 : _87026 -> Prop) : (term1196 _87026 s' t'' _34645 x'' _34644) = (term1197 _87026 s' t'' _34645 x'' _34644).
Proof. exact (@lem3341036 (term1198 _87026 s' t'' _34645 x'' _34644)). Qed.
Lemma lem3341038 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (_34645 : _87026 -> Prop) (x'' : _87026) (_34644 : _87026 -> Prop) : (term1140 _87026 s' t'' _34645 x'' _34644) = (term1197 _87026 s' t'' _34645 x'' _34644).
Proof. exact (TRANS (@lem3341034 _87026 s' t'' _34645 x'' _34644) (@lem3341037 _87026 s' t'' _34645 x'' _34644)). Qed.
Lemma lem3341040 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term167 _87026) (h2 : term684 _87026 t''' s' t'' x'') : term1176 _87026 x'' t'' t'''.
Proof. exact (conj (@lem3340976 _87026 t'' t''') (@lem3341025 _87026 t''' s' t'' x'' h1 h2)). Qed.
Lemma lem3341041 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term167 _87026) (h2 : term684 _87026 t''' s' t'' x'') : term1199 _87026 s' x'' t'' t'''.
Proof. exact (conj (@lem3340967 _87026 t''' s' t'' x'' h2) (@lem3341040 _87026 t''' s' t'' x'' h1 h2)). Qed.
Lemma lem3341043 {_87026 : Type'} (_34645 : _87026 -> Prop) (_34644 : _87026 -> Prop) (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term1197 _87026 s' t'' _34645 x'' _34644.
Proof. exact (EQ_MP (@lem3341038 _87026 s' t'' _34645 x'' _34644) (@lem3339265 _87026 _34645 _34644 t''' s' t'' x'' h1)). Qed.
Lemma lem3341044 {_87026 : Type'} (_34645 : _87026 -> Prop) (_34644 : _87026 -> Prop) (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term1197 _87026 s' t'' _34645 x'' _34644.
Proof. exact (@lem3341043 _87026 _34645 _34644 t''' s' t'' x'' h1). Qed.
Lemma lem3341045 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term684 _87026 t''' s' t'' x'') : term1200 _87026 s' x'' t'' t'''.
Proof. exact (@lem3341044 _87026 t''' (@INTER _87026 t'' t''') t''' s' t'' x'' h1). Qed.
Lemma lem3341048 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term167 _87026) (h2 : term684 _87026 t''' s' t'' x'') : False.
Proof. exact (@lem3341045 _87026 t''' s' t'' x'' h2 (@lem3341041 _87026 t''' s' t'' x'' h1 h2)). Qed.
Lemma lem3341049 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term167 _87026) (h2 : term684 _87026 t''' s' t'' x'') : term1179.
Proof. exact (fun h0 : ~ False => @lem3341048 _87026 t''' s' t'' x'' h1 h2). Qed.
Lemma lem3341051 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3341052 : term1179 = False.
Proof. exact (@lem3341051 False). Qed.
Lemma lem3341053 {_87026 : Type'} (t''' : _87026 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term167 _87026) (h2 : term684 _87026 t''' s' t'' x'') : False.
Proof. exact (EQ_MP (@lem3341052) (@lem3341049 _87026 t''' s' t'' x'' h1 h2)). Qed.
Lemma lem3341055 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : term12 _87026 x'' t'' x'''.
Proof. exact (EQ_MP (@lem3340043 _87026 s' t'' x''' x'' t''' h1) (@lem3339361 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3341056 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : term1165 _87026 x'' t'' x'''.
Proof. exact (fun h0 : term1105 _87026 x'' t'' x''' => @lem3341055 _87026 s' t'' x''' x'' t''' h1). Qed.
Lemma lem3341058 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3341059 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) : (term1165 _87026 x'' t'' x''') = (term12 _87026 x'' t'' x''').
Proof. exact (@lem3341058 (term12 _87026 x'' t'' x''')). Qed.
Lemma lem3341060 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : term12 _87026 x'' t'' x'''.
Proof. exact (EQ_MP (@lem3341059 _87026 x'' t'' x''') (@lem3341056 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3341066 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3341067 {_87026 : Type'} (_34663 : _87026) (_34661 : _87026 -> Prop) (_34662 : _87026 -> Prop) : (term1146 _87026 _34662 _34663 _34661) = (term1180 _87026 _34663 _34661 _34662).
Proof. exact (@lem3341066 (@IN _87026 _34663 _34661) (term1105 _87026 _34663 _34661 _34662)). Qed.
Lemma lem3341073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3341074 {_87026 : Type'} (_34663 : _87026) (_34661 : _87026 -> Prop) (_34662 : _87026 -> Prop) : (term1181 _87026 _34662 _34663 _34661) = (term1182 _87026 _34663 _34661 _34662).
Proof. exact (MK_COMB (@lem3341073) (@lem3341067 _87026 _34663 _34661 _34662)). Qed.
Lemma lem3341080 {_87026 : Type'} (_34663 : _87026) (_34661 : _87026 -> Prop) (_34662 : _87026 -> Prop) : (term1180 _87026 _34663 _34661 _34662) = (term1180 _87026 _34663 _34661 _34662).
Proof. exact (eq_refl (term1180 _87026 _34663 _34661 _34662)). Qed.
Lemma lem3341081 {_87026 : Type'} (_34663 : _87026) (_34661 : _87026 -> Prop) (_34662 : _87026 -> Prop) : ((term1146 _87026 _34662 _34663 _34661) = (term1180 _87026 _34663 _34661 _34662)) = ((term1180 _87026 _34663 _34661 _34662) = (term1180 _87026 _34663 _34661 _34662)).
Proof. exact (MK_COMB (@lem3341074 _87026 _34663 _34661 _34662) (@lem3341080 _87026 _34663 _34661 _34662)). Qed.
Lemma lem3341083 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3341084 (x : Prop) : (x = x) = True.
Proof. exact (@lem3341083 Prop x). Qed.
Lemma lem3341085 {_87026 : Type'} (_34663 : _87026) (_34661 : _87026 -> Prop) (_34662 : _87026 -> Prop) : ((term1180 _87026 _34663 _34661 _34662) = (term1180 _87026 _34663 _34661 _34662)) = True.
Proof. exact (@lem3341084 (term1180 _87026 _34663 _34661 _34662)). Qed.
Lemma lem3341086 {_87026 : Type'} (_34663 : _87026) (_34661 : _87026 -> Prop) (_34662 : _87026 -> Prop) : ((term1146 _87026 _34662 _34663 _34661) = (term1180 _87026 _34663 _34661 _34662)) = True.
Proof. exact (TRANS (@lem3341081 _87026 _34663 _34661 _34662) (@lem3341085 _87026 _34663 _34661 _34662)). Qed.
Lemma lem3341087 {_87026 : Type'} (_34663 : _87026) (_34661 : _87026 -> Prop) (_34662 : _87026 -> Prop) : True = ((term1146 _87026 _34662 _34663 _34661) = (term1180 _87026 _34663 _34661 _34662)).
Proof. exact (SYM (@lem3341086 _87026 _34663 _34661 _34662)). Qed.
Lemma lem3341088 {_87026 : Type'} (_34663 : _87026) (_34661 : _87026 -> Prop) (_34662 : _87026 -> Prop) : (term1146 _87026 _34662 _34663 _34661) = (term1180 _87026 _34663 _34661 _34662).
Proof. exact (EQ_MP (@lem3341087 _87026 _34663 _34661 _34662) (@lem0)). Qed.
Lemma lem3341089 {_87026 : Type'} (_34663 : _87026) (_34661 : _87026 -> Prop) (_34662 : _87026 -> Prop) (h1 : term167 _87026) : term1180 _87026 _34663 _34661 _34662.
Proof. exact (EQ_MP (@lem3341088 _87026 _34663 _34661 _34662) (@lem3340114 _87026 _34662 _34663 _34661 h1)). Qed.
Lemma lem3341091 (b : Prop) (a : Prop) : (a \/ b) = (term1153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3341092 {_87026 : Type'} (_34662 : _87026 -> Prop) (_34663 : _87026) (_34661 : _87026 -> Prop) : (term1180 _87026 _34663 _34661 _34662) = (term1183 _87026 _34662 _34663 _34661).
Proof. exact (@lem3341091 (term1105 _87026 _34663 _34661 _34662) (@IN _87026 _34663 _34661)). Qed.
Lemma lem3341094 (a : Prop) : (term1159 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3341095 {_87026 : Type'} (_34663 : _87026) (_34661 : _87026 -> Prop) (_34662 : _87026 -> Prop) : (term1184 _87026 _34663 _34661 _34662) = (term12 _87026 _34663 _34661 _34662).
Proof. exact (@lem3341094 (term12 _87026 _34663 _34661 _34662)). Qed.
Lemma lem3341096 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3341097 {_87026 : Type'} (_34663 : _87026) (_34661 : _87026 -> Prop) (_34662 : _87026 -> Prop) : (term1185 _87026 _34663 _34661 _34662) = (term1186 _87026 _34663 _34661 _34662).
Proof. exact (MK_COMB (@lem3341096) (@lem3341095 _87026 _34663 _34661 _34662)). Qed.
Lemma lem3341098 {_87026 : Type'} (_34663 : _87026) (_34661 : _87026 -> Prop) : (@IN _87026 _34663 _34661) = (@IN _87026 _34663 _34661).
Proof. exact (eq_refl (@IN _87026 _34663 _34661)). Qed.
Lemma lem3341099 {_87026 : Type'} (_34662 : _87026 -> Prop) (_34663 : _87026) (_34661 : _87026 -> Prop) : (term1183 _87026 _34662 _34663 _34661) = (term1187 _87026 _34662 _34663 _34661).
Proof. exact (MK_COMB (@lem3341097 _87026 _34663 _34661 _34662) (@lem3341098 _87026 _34663 _34661)). Qed.
Lemma lem3341100 {_87026 : Type'} (_34662 : _87026 -> Prop) (_34663 : _87026) (_34661 : _87026 -> Prop) : (term1180 _87026 _34663 _34661 _34662) = (term1187 _87026 _34662 _34663 _34661).
Proof. exact (TRANS (@lem3341092 _87026 _34662 _34663 _34661) (@lem3341099 _87026 _34662 _34663 _34661)). Qed.
Lemma lem3341103 {_87026 : Type'} (_34662 : _87026 -> Prop) (_34663 : _87026) (_34661 : _87026 -> Prop) (h1 : term167 _87026) : term1187 _87026 _34662 _34663 _34661.
Proof. exact (EQ_MP (@lem3341100 _87026 _34662 _34663 _34661) (@lem3341089 _87026 _34663 _34661 _34662 h1)). Qed.
Lemma lem3341104 {_87026 : Type'} (_34662 : _87026 -> Prop) (_34663 : _87026) (_34661 : _87026 -> Prop) (h1 : term167 _87026) : term1187 _87026 _34662 _34663 _34661.
Proof. exact (@lem3341103 _87026 _34662 _34663 _34661 h1). Qed.
Lemma lem3341105 {_87026 : Type'} (x''' : _87026 -> Prop) (x'' : _87026) (t'' : _87026 -> Prop) (h1 : term167 _87026) : term1187 _87026 x''' x'' t''.
Proof. exact (@lem3341104 _87026 x''' x'' t'' h1). Qed.
Lemma lem3341108 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term732 _87026 s' t'' x''' x'' t''') : @IN _87026 x'' t''.
Proof. exact (@lem3341105 _87026 x''' x'' t'' h1 (@lem3341060 _87026 s' t'' x''' x'' t''' h2)). Qed.
Lemma lem3341109 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term732 _87026 s' t'' x''' x'' t''') : term1152 _87026 x'' t''.
Proof. exact (fun h0 : term207 _87026 x'' t'' => @lem3341108 _87026 s' t'' x''' x'' t''' h1 h2). Qed.
Lemma lem3341111 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3341112 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) : (term1152 _87026 x'' t'') = (@IN _87026 x'' t'').
Proof. exact (@lem3341111 (@IN _87026 x'' t'')). Qed.
Lemma lem3341113 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term732 _87026 s' t'' x''' x'' t''') : @IN _87026 x'' t''.
Proof. exact (EQ_MP (@lem3341112 _87026 x'' t'') (@lem3341109 _87026 s' t'' x''' x'' t''' h1 h2)). Qed.
Lemma lem3341116 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3341118 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) : (term207 _87026 x'' t'') = (term1194 _87026 x'' t'').
Proof. exact (@lem3341116 (@IN _87026 x'' t'')). Qed.
Lemma lem3341121 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) (h1 : term207 _87026 x'' t'') : term1194 _87026 x'' t''.
Proof. exact (EQ_MP (@lem3341118 _87026 x'' t'') (@lem3340072 _87026 x'' t'' h1)). Qed.
Lemma lem3341124 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term207 _87026 x'' t'') (h3 : term732 _87026 s' t'' x''' x'' t''') : False.
Proof. exact (@lem3341121 _87026 x'' t'' h2 (@lem3341113 _87026 s' t'' x''' x'' t''' h1 h3)). Qed.
Lemma lem3341125 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term207 _87026 x'' t'') (h3 : term732 _87026 s' t'' x''' x'' t''') : term1179.
Proof. exact (fun h0 : ~ False => @lem3341124 _87026 s' t'' x''' x'' t''' h1 h2 h3). Qed.
Lemma lem3341127 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3341128 : term1179 = False.
Proof. exact (@lem3341127 False). Qed.
Lemma lem3341129 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term207 _87026 x'' t'') (h3 : term732 _87026 s' t'' x''' x'' t''') : False.
Proof. exact (EQ_MP (@lem3341128) (@lem3341125 _87026 s' t'' x''' x'' t''' h1 h2 h3)). Qed.
Lemma lem3341131 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : @IN (_87026 -> Prop) x''' s'.
Proof. exact (proj1 (@lem3336911 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3341132 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : term1148 _87026 x''' s'.
Proof. exact (fun h0 : term1138 _87026 x''' s' => @lem3341131 _87026 s' t'' x''' x'' t''' h1). Qed.
Lemma lem3341134 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3341135 {_87026 : Type'} (x''' : _87026 -> Prop) (s' : type686 _87026) : (term1148 _87026 x''' s') = (@IN (_87026 -> Prop) x''' s').
Proof. exact (@lem3341134 (@IN (_87026 -> Prop) x''' s')). Qed.
Lemma lem3341136 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : @IN (_87026 -> Prop) x''' s'.
Proof. exact (EQ_MP (@lem3341135 _87026 x''' s') (@lem3341132 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3341138 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : term12 _87026 x'' t'' x'''.
Proof. exact (EQ_MP (@lem3340266 _87026 s' t'' x''' x'' t''' h1) (@lem3339457 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3341139 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : term1165 _87026 x'' t'' x'''.
Proof. exact (fun h0 : term1105 _87026 x'' t'' x''' => @lem3341138 _87026 s' t'' x''' x'' t''' h1). Qed.
Lemma lem3341141 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3341142 {_87026 : Type'} (x'' : _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) : (term1165 _87026 x'' t'' x''') = (term12 _87026 x'' t'' x''').
Proof. exact (@lem3341141 (term12 _87026 x'' t'' x''')). Qed.
Lemma lem3341143 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term732 _87026 s' t'' x''' x'' t''') : term12 _87026 x'' t'' x'''.
Proof. exact (EQ_MP (@lem3341142 _87026 x'' t'' x''') (@lem3341139 _87026 s' t'' x''' x'' t''' h1)). Qed.
Lemma lem3341149 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3341150 {_87026 : Type'} (_34687 : _87026) (_34685 : _87026 -> Prop) (_34686 : _87026 -> Prop) : (term1147 _87026 _34685 _34687 _34686) = (term1189 _87026 _34687 _34685 _34686).
Proof. exact (@lem3341149 (@IN _87026 _34687 _34686) (term1105 _87026 _34687 _34685 _34686)). Qed.
Lemma lem3341156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3341157 {_87026 : Type'} (_34687 : _87026) (_34685 : _87026 -> Prop) (_34686 : _87026 -> Prop) : (term1190 _87026 _34685 _34687 _34686) = (term1191 _87026 _34687 _34685 _34686).
Proof. exact (MK_COMB (@lem3341156) (@lem3341150 _87026 _34687 _34685 _34686)). Qed.
Lemma lem3341163 {_87026 : Type'} (_34687 : _87026) (_34685 : _87026 -> Prop) (_34686 : _87026 -> Prop) : (term1189 _87026 _34687 _34685 _34686) = (term1189 _87026 _34687 _34685 _34686).
Proof. exact (eq_refl (term1189 _87026 _34687 _34685 _34686)). Qed.
Lemma lem3341164 {_87026 : Type'} (_34687 : _87026) (_34685 : _87026 -> Prop) (_34686 : _87026 -> Prop) : ((term1147 _87026 _34685 _34687 _34686) = (term1189 _87026 _34687 _34685 _34686)) = ((term1189 _87026 _34687 _34685 _34686) = (term1189 _87026 _34687 _34685 _34686)).
Proof. exact (MK_COMB (@lem3341157 _87026 _34687 _34685 _34686) (@lem3341163 _87026 _34687 _34685 _34686)). Qed.
Lemma lem3341166 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3341167 (x : Prop) : (x = x) = True.
Proof. exact (@lem3341166 Prop x). Qed.
Lemma lem3341168 {_87026 : Type'} (_34687 : _87026) (_34685 : _87026 -> Prop) (_34686 : _87026 -> Prop) : ((term1189 _87026 _34687 _34685 _34686) = (term1189 _87026 _34687 _34685 _34686)) = True.
Proof. exact (@lem3341167 (term1189 _87026 _34687 _34685 _34686)). Qed.
Lemma lem3341169 {_87026 : Type'} (_34687 : _87026) (_34685 : _87026 -> Prop) (_34686 : _87026 -> Prop) : ((term1147 _87026 _34685 _34687 _34686) = (term1189 _87026 _34687 _34685 _34686)) = True.
Proof. exact (TRANS (@lem3341164 _87026 _34687 _34685 _34686) (@lem3341168 _87026 _34687 _34685 _34686)). Qed.
Lemma lem3341170 {_87026 : Type'} (_34687 : _87026) (_34685 : _87026 -> Prop) (_34686 : _87026 -> Prop) : True = ((term1147 _87026 _34685 _34687 _34686) = (term1189 _87026 _34687 _34685 _34686)).
Proof. exact (SYM (@lem3341169 _87026 _34687 _34685 _34686)). Qed.
Lemma lem3341171 {_87026 : Type'} (_34687 : _87026) (_34685 : _87026 -> Prop) (_34686 : _87026 -> Prop) : (term1147 _87026 _34685 _34687 _34686) = (term1189 _87026 _34687 _34685 _34686).
Proof. exact (EQ_MP (@lem3341170 _87026 _34687 _34685 _34686) (@lem0)). Qed.
Lemma lem3341172 {_87026 : Type'} (_34687 : _87026) (_34685 : _87026 -> Prop) (_34686 : _87026 -> Prop) (h1 : term167 _87026) : term1189 _87026 _34687 _34685 _34686.
Proof. exact (EQ_MP (@lem3341171 _87026 _34687 _34685 _34686) (@lem3340351 _87026 _34685 _34687 _34686 h1)). Qed.
Lemma lem3341174 (b : Prop) (a : Prop) : (a \/ b) = (term1153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3341175 {_87026 : Type'} (_34685 : _87026 -> Prop) (_34687 : _87026) (_34686 : _87026 -> Prop) : (term1189 _87026 _34687 _34685 _34686) = (term1192 _87026 _34685 _34687 _34686).
Proof. exact (@lem3341174 (term1105 _87026 _34687 _34685 _34686) (@IN _87026 _34687 _34686)). Qed.
Lemma lem3341177 (a : Prop) : (term1159 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3341178 {_87026 : Type'} (_34687 : _87026) (_34685 : _87026 -> Prop) (_34686 : _87026 -> Prop) : (term1184 _87026 _34687 _34685 _34686) = (term12 _87026 _34687 _34685 _34686).
Proof. exact (@lem3341177 (term12 _87026 _34687 _34685 _34686)). Qed.
Lemma lem3341179 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3341180 {_87026 : Type'} (_34687 : _87026) (_34685 : _87026 -> Prop) (_34686 : _87026 -> Prop) : (term1185 _87026 _34687 _34685 _34686) = (term1186 _87026 _34687 _34685 _34686).
Proof. exact (MK_COMB (@lem3341179) (@lem3341178 _87026 _34687 _34685 _34686)). Qed.
Lemma lem3341181 {_87026 : Type'} (_34687 : _87026) (_34686 : _87026 -> Prop) : (@IN _87026 _34687 _34686) = (@IN _87026 _34687 _34686).
Proof. exact (eq_refl (@IN _87026 _34687 _34686)). Qed.
Lemma lem3341182 {_87026 : Type'} (_34685 : _87026 -> Prop) (_34687 : _87026) (_34686 : _87026 -> Prop) : (term1192 _87026 _34685 _34687 _34686) = (term1193 _87026 _34685 _34687 _34686).
Proof. exact (MK_COMB (@lem3341180 _87026 _34687 _34685 _34686) (@lem3341181 _87026 _34687 _34686)). Qed.
Lemma lem3341183 {_87026 : Type'} (_34685 : _87026 -> Prop) (_34687 : _87026) (_34686 : _87026 -> Prop) : (term1189 _87026 _34687 _34685 _34686) = (term1193 _87026 _34685 _34687 _34686).
Proof. exact (TRANS (@lem3341175 _87026 _34685 _34687 _34686) (@lem3341182 _87026 _34685 _34687 _34686)). Qed.
Lemma lem3341186 {_87026 : Type'} (_34685 : _87026 -> Prop) (_34687 : _87026) (_34686 : _87026 -> Prop) (h1 : term167 _87026) : term1193 _87026 _34685 _34687 _34686.
Proof. exact (EQ_MP (@lem3341183 _87026 _34685 _34687 _34686) (@lem3341172 _87026 _34687 _34685 _34686 h1)). Qed.
Lemma lem3341187 {_87026 : Type'} (_34685 : _87026 -> Prop) (_34687 : _87026) (_34686 : _87026 -> Prop) (h1 : term167 _87026) : term1193 _87026 _34685 _34687 _34686.
Proof. exact (@lem3341186 _87026 _34685 _34687 _34686 h1). Qed.
Lemma lem3341188 {_87026 : Type'} (t'' : _87026 -> Prop) (x'' : _87026) (x''' : _87026 -> Prop) (h1 : term167 _87026) : term1193 _87026 t'' x'' x'''.
Proof. exact (@lem3341187 _87026 t'' x'' x''' h1). Qed.
Lemma lem3341191 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term732 _87026 s' t'' x''' x'' t''') : @IN _87026 x'' x'''.
Proof. exact (@lem3341188 _87026 t'' x'' x''' h1 (@lem3341143 _87026 s' t'' x''' x'' t''' h2)). Qed.
Lemma lem3341192 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term732 _87026 s' t'' x''' x'' t''') : term1152 _87026 x'' x'''.
Proof. exact (fun h0 : term207 _87026 x'' x''' => @lem3341191 _87026 s' t'' x''' x'' t''' h1 h2). Qed.
Lemma lem3341194 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3341195 {_87026 : Type'} (x'' : _87026) (x''' : _87026 -> Prop) : (term1152 _87026 x'' x''') = (@IN _87026 x'' x''').
Proof. exact (@lem3341194 (@IN _87026 x'' x''')). Qed.
Lemma lem3341196 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term732 _87026 s' t'' x''' x'' t''') : @IN _87026 x'' x'''.
Proof. exact (EQ_MP (@lem3341195 _87026 x'' x''') (@lem3341192 _87026 s' t'' x''' x'' t''' h1 h2)). Qed.
Lemma lem3341198 (a : Prop) (b : Prop) : (term1166 a b) = (term1167 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3341199 {_87026 : Type'} (s' : type686 _87026) (x'' : _87026) (_34694 : _87026 -> Prop) : (term197 _87026 s' x'' _34694) = (term196 _87026 s' x'' _34694).
Proof. exact (@lem3341198 (@IN (_87026 -> Prop) _34694 s') (@IN _87026 x'' _34694)). Qed.
Lemma lem3341201 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3341202 {_87026 : Type'} (s' : type686 _87026) (x'' : _87026) (_34694 : _87026 -> Prop) : (term196 _87026 s' x'' _34694) = (term1188 _87026 s' x'' _34694).
Proof. exact (@lem3341201 (term194 _87026 s' x'' _34694)). Qed.
Lemma lem3341203 {_87026 : Type'} (s' : type686 _87026) (x'' : _87026) (_34694 : _87026 -> Prop) : (term197 _87026 s' x'' _34694) = (term1188 _87026 s' x'' _34694).
Proof. exact (TRANS (@lem3341199 _87026 s' x'' _34694) (@lem3341202 _87026 s' x'' _34694)). Qed.
Lemma lem3341205 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term732 _87026 s' t'' x''' x'' t''') : term194 _87026 s' x'' x'''.
Proof. exact (conj (@lem3341136 _87026 s' t'' x''' x'' t''' h2) (@lem3341196 _87026 s' t'' x''' x'' t''' h1 h2)). Qed.
Lemma lem3341207 {_87026 : Type'} (_34694 : _87026 -> Prop) (s' : type686 _87026) (x'' : _87026) (h1 : term206 _87026 s' x'') : term1188 _87026 s' x'' _34694.
Proof. exact (EQ_MP (@lem3341203 _87026 s' x'' _34694) (@lem3340295 _87026 _34694 s' x'' h1)). Qed.
Lemma lem3341208 {_87026 : Type'} (_34694 : _87026 -> Prop) (s' : type686 _87026) (x'' : _87026) (h1 : term206 _87026 s' x'') : term1188 _87026 s' x'' _34694.
Proof. exact (@lem3341207 _87026 _34694 s' x'' h1). Qed.
Lemma lem3341209 {_87026 : Type'} (x''' : _87026 -> Prop) (s' : type686 _87026) (x'' : _87026) (h1 : term206 _87026 s' x'') : term1188 _87026 s' x'' x'''.
Proof. exact (@lem3341208 _87026 x''' s' x'' h1). Qed.
Lemma lem3341212 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term206 _87026 s' x'') (h3 : term732 _87026 s' t'' x''' x'' t''') : False.
Proof. exact (@lem3341209 _87026 x''' s' x'' h2 (@lem3341205 _87026 s' t'' x''' x'' t''' h1 h3)). Qed.
Lemma lem3341213 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term206 _87026 s' x'') (h3 : term732 _87026 s' t'' x''' x'' t''') : term1179.
Proof. exact (fun h0 : ~ False => @lem3341212 _87026 s' t'' x''' x'' t''' h1 h2 h3). Qed.
Lemma lem3341215 (p : Prop) : (term1149 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3341216 : term1179 = False.
Proof. exact (@lem3341215 False). Qed.
Lemma lem3341218 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term206 _87026 s' x'') (h3 : term732 _87026 s' t'' x''' x'' t''') : False.
Proof. exact (EQ_MP (@lem3341216) (@lem3341213 _87026 s' t'' x''' x'' t''' h1 h2 h3)). Qed.
Lemma lem3341219 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term207 _87026 x'' t'') (h3 : term732 _87026 s' t'' x''' x'' t''') : (term207 _87026 x'' t'') = False.
Proof. exact (prop_ext (fun h4 : term207 _87026 x'' t'' => @lem3341129 _87026 s' t'' x''' x'' t''' h1 h2 h3) (fun h4 : False => @lem3340072 _87026 x'' t'' h2)). Qed.
Lemma lem3341221 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term207 _87026 x'' t'') (h3 : term732 _87026 s' t'' x''' x'' t''') : False.
Proof. exact (EQ_MP (@lem3341219 _87026 s' t'' x''' x'' t''' h1 h2 h3) (@lem3340072 _87026 x'' t'' h2)). Qed.
Lemma lem3341222 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term207 _86990 x t) (h3 : term553 _86990 s x' t x t') : (term207 _86990 x t) = False.
Proof. exact (prop_ext (fun h4 : term207 _86990 x t => @lem3340812 _86990 s x' t x t' h1 h2 h3) (fun h4 : False => @lem3339849 _86990 x t h2)). Qed.
Lemma lem3341224 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term207 _86990 x t) (h3 : term553 _86990 s x' t x t') : False.
Proof. exact (EQ_MP (@lem3341222 _86990 s x' t x t' h1 h2 h3) (@lem3339849 _86990 x t h2)). Qed.
Lemma lem3341225 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term206 _86990 s x) (h3 : term553 _86990 s x' t x t') : False.
Proof. exact (EQ_MP (@lem3340735) (@lem3340732 _86990 s x' t x t' h1 h2 h3)). Qed.
Lemma lem3341226 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term207 _87026 x'' t'') (h3 : term732 _87026 s' t'' x''' x'' t''') : (term207 _87026 x'' t'') = False.
Proof. exact (prop_ext (fun h4 : term207 _87026 x'' t'' => @lem3341221 _87026 s' t'' x''' x'' t''' h1 h2 h3) (fun h4 : False => @lem3339367 _87026 x'' t'' h2)). Qed.
Lemma lem3341227 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term207 _87026 x'' t'') (h3 : term732 _87026 s' t'' x''' x'' t''') : False.
Proof. exact (EQ_MP (@lem3341226 _87026 s' t'' x''' x'' t''' h1 h2 h3) (@lem3339367 _87026 x'' t'' h2)). Qed.
Lemma lem3341228 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term207 _86990 x t) (h3 : term553 _86990 s x' t x t') : (term207 _86990 x t) = False.
Proof. exact (prop_ext (fun h4 : term207 _86990 x t => @lem3341224 _86990 s x' t x t' h1 h2 h3) (fun h4 : False => @lem3339165 _86990 x t h2)). Qed.
Lemma lem3341229 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term207 _86990 x t) (h3 : term553 _86990 s x' t x t') : False.
Proof. exact (EQ_MP (@lem3341228 _86990 s x' t x t' h1 h2 h3) (@lem3339165 _86990 x t h2)). Qed.
Lemma lem3341230 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term207 _87026 x'' t'') (h3 : term732 _87026 s' t'' x''' x'' t''') : (term207 _87026 x'' t'') = False.
Proof. exact (prop_ext (fun h4 : term207 _87026 x'' t'' => @lem3341227 _87026 s' t'' x''' x'' t''' h1 h2 h3) (fun h4 : False => @lem3338172 _87026 x'' t'' h2)). Qed.
Lemma lem3341231 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term207 _87026 x'' t'') (h3 : term732 _87026 s' t'' x''' x'' t''') : False.
Proof. exact (EQ_MP (@lem3341230 _87026 s' t'' x''' x'' t''' h1 h2 h3) (@lem3338172 _87026 x'' t'' h2)). Qed.
Lemma lem3341232 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term207 _86990 x t) (h3 : term553 _86990 s x' t x t') : (term207 _86990 x t) = False.
Proof. exact (prop_ext (fun h4 : term207 _86990 x t => @lem3341229 _86990 s x' t x t' h1 h2 h3) (fun h4 : False => @lem3337664 _86990 x t h2)). Qed.
Lemma lem3341233 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term207 _86990 x t) (h3 : term553 _86990 s x' t x t') : False.
Proof. exact (EQ_MP (@lem3341232 _86990 s x' t x t' h1 h2 h3) (@lem3337664 _86990 x t h2)). Qed.
Lemma lem3341234 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term206 _87026 s' x'') (h3 : term732 _87026 s' t'' x''' x'' t''') : (term206 _87026 s' x'') = False.
Proof. exact (prop_ext (fun h4 : term206 _87026 s' x'' => @lem3341218 _87026 s' t'' x''' x'' t''' h1 h2 h3) (fun h4 : False => @lem3338413 _87026 s' x'' h2)). Qed.
Lemma lem3341235 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term206 _87026 s' x'') (h3 : term732 _87026 s' t'' x''' x'' t''') : False.
Proof. exact (EQ_MP (@lem3341234 _87026 s' t'' x''' x'' t''' h1 h2 h3) (@lem3338413 _87026 s' x'' h2)). Qed.
Lemma lem3341236 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term207 _87026 x'' t'') (h3 : term732 _87026 s' t'' x''' x'' t''') : (term207 _87026 x'' t'') = False.
Proof. exact (prop_ext (fun h4 : term207 _87026 x'' t'' => @lem3341231 _87026 s' t'' x''' x'' t''' h1 h2 h3) (fun h4 : False => @lem3338172 _87026 x'' t'' h2)). Qed.
Lemma lem3341237 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term207 _87026 x'' t'') (h3 : term732 _87026 s' t'' x''' x'' t''') : False.
Proof. exact (EQ_MP (@lem3341236 _87026 s' t'' x''' x'' t''' h1 h2 h3) (@lem3338172 _87026 x'' t'' h2)). Qed.
Lemma lem3341238 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term207 _86990 x t) (h3 : term553 _86990 s x' t x t') : (term207 _86990 x t) = False.
Proof. exact (prop_ext (fun h4 : term207 _86990 x t => @lem3341233 _86990 s x' t x t' h1 h2 h3) (fun h4 : False => @lem3337664 _86990 x t h2)). Qed.
Lemma lem3341239 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term207 _86990 x t) (h3 : term553 _86990 s x' t x t') : False.
Proof. exact (EQ_MP (@lem3341238 _86990 s x' t x t' h1 h2 h3) (@lem3337664 _86990 x t h2)). Qed.
Lemma lem3341240 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term206 _86990 s x) (h3 : term553 _86990 s x' t x t') : (term206 _86990 s x) = False.
Proof. exact (prop_ext (fun h4 : term206 _86990 s x => @lem3341225 _86990 s x' t x t' h1 h2 h3) (fun h4 : False => @lem3337432 _86990 s x h2)). Qed.
Lemma lem3341241 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term206 _86990 s x) (h3 : term553 _86990 s x' t x t') : False.
Proof. exact (EQ_MP (@lem3341240 _86990 s x' t x t' h1 h2 h3) (@lem3337432 _86990 s x h2)). Qed.
Lemma lem3341242 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term732 _87026 s' t'' x''' x'' t''') : False.
Proof. exact (or_elim (@lem3336909 _87026 s' t'' x''' x'' t''' h2) (fun h0 : term207 _87026 x'' t'' => @lem3341237 _87026 s' t'' x''' x'' t''' h1 h0 h2) (fun h0 : term206 _87026 s' x'' => @lem3341235 _87026 s' t'' x''' x'' t''' h1 h0 h2)). Qed.
Lemma lem3341243 {_87026 : Type'} (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _87026) (h2 : term825 _87026 s' t'' x''' x'' t''') : False.
Proof. exact (or_elim (@lem3336883 _87026 s' t'' x''' x'' t''' h2) (fun h0 : term684 _87026 t''' s' t'' x'' => @lem3341053 _87026 t''' s' t'' x'' h1 h0) (fun h0 : term732 _87026 s' t'' x''' x'' t''' => @lem3341242 _87026 s' t'' x''' x'' t''' h1 h0)). Qed.
Lemma lem3341244 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term553 _86990 s x' t x t') : False.
Proof. exact (or_elim (@lem3336893 _86990 s x' t x t' h2) (fun h0 : term206 _86990 s x => @lem3341241 _86990 s x' t x t' h1 h0 h2) (fun h0 : term207 _86990 x t => @lem3341239 _86990 s x' t x t' h1 h0 h2)). Qed.
Lemma lem3341245 {_86990 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term650 _86990 s x' t x t') : False.
Proof. exact (or_elim (@lem3336882 _86990 s x' t x t' h2) (fun h0 : term501 _86990 t' s t x => @lem3340648 _86990 t' s t x h1 h0) (fun h0 : term553 _86990 s x' t x t' => @lem3341244 _86990 s x' t x t' h1 h0)). Qed.
Lemma lem3341246 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term977 _86990 _87026 s x' t x t' s' t'' x''' x'' t''') : False.
Proof. exact (or_elim (@lem3336873 _86990 _87026 s x' t x t' s' t'' x''' x'' t''' h3) (fun h0 : term650 _86990 s x' t x t' => @lem3341245 _86990 s x' t x t' h1 h0) (fun h0 : term825 _87026 s' t'' x''' x'' t''' => @lem3341243 _87026 s' t'' x''' x'' t''' h2 h0)). Qed.
Lemma lem3341247 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term977 _86990 _87026 s x' t x t' s' t'' x''' x'' t''') : (term977 _86990 _87026 s x' t x t' s' t'' x''' x'' t''') = False.
Proof. exact (prop_ext (fun h4 : term977 _86990 _87026 s x' t x t' s' t'' x''' x'' t''' => @lem3341246 _86990 _87026 s x' t x t' s' t'' x''' x'' t''' h1 h2 h3) (fun h4 : False => @lem3336873 _86990 _87026 s x' t x t' s' t'' x''' x'' t''' h3)). Qed.
Lemma lem3341248 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x''' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term977 _86990 _87026 s x' t x t' s' t'' x''' x'' t''') : False.
Proof. exact (EQ_MP (@lem3341247 _86990 _87026 s x' t x t' s' t'' x''' x'' t''' h1 h2 h3) (@lem3336873 _86990 _87026 s x' t x t' s' t'' x''' x'' t''' h3)). Qed.
Lemma lem3341249 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (t''' : _87026 -> Prop) (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term980 _86990 _87026 s x' t x t' s' t'' x'' t''') : False.
Proof. exact (ex_elim (@lem3336312 _86990 _87026 s x' t x t' s' t'' x'' t''' h3) (fun x''' : _87026 -> Prop => fun h0 : term979 _86990 _87026 s x' t x t' s' t'' x'' t''' x''' => @lem3341248 _86990 _87026 s x' t x t' s' t'' x''' x'' t''' h1 h2 h0)). Qed.
Lemma lem3341250 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (x'' : _87026) (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term982 _86990 _87026 s x' t x t' s' t'' x'') : False.
Proof. exact (ex_elim (@lem3336311 _86990 _87026 s x' t x t' s' t'' x'' h3) (fun t''' : _87026 -> Prop => fun h0 : term981 _86990 _87026 s x' t x t' s' t'' x'' t''' => @lem3341249 _86990 _87026 s x' t x t' s' t'' x'' t''' h1 h2 h0)). Qed.
Lemma lem3341251 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (t'' : _87026 -> Prop) (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term984 _86990 _87026 s x' t x t' s' t'') : False.
Proof. exact (ex_elim (@lem3336310 _86990 _87026 s x' t x t' s' t'' h3) (fun x'' : _87026 => fun h0 : term983 _86990 _87026 s x' t x t' s' t'' x'' => @lem3341250 _86990 _87026 s x' t x t' s' t'' x'' h1 h2 h0)). Qed.
Lemma lem3341252 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (s' : type686 _87026) (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term986 _86990 _87026 s x' t x t' s') : False.
Proof. exact (ex_elim (@lem3336309 _86990 _87026 s x' t x t' s' h3) (fun t'' : _87026 -> Prop => fun h0 : term985 _86990 _87026 s x' t x t' s' t'' => @lem3341251 _86990 _87026 s x' t x t' s' t'' h1 h2 h0)). Qed.
Lemma lem3341253 {_86990 _87026 : Type'} (s : type686 _86990) (x' : _86990 -> Prop) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term988 _86990 _87026 s x' t x t') : False.
Proof. exact (ex_elim (@lem3336308 _86990 _87026 s x' t x t' h3) (fun s' : type686 _87026 => fun h0 : term987 _86990 _87026 s x' t x t' s' => @lem3341252 _86990 _87026 s x' t x t' s' h1 h2 h0)). Qed.
Lemma lem3341254 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (t' : _86990 -> Prop) (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term990 _86990 _87026 s t x t') : False.
Proof. exact (ex_elim (@lem3336307 _86990 _87026 s t x t' h3) (fun x' : _86990 -> Prop => fun h0 : term989 _86990 _87026 s t x t' x' => @lem3341253 _86990 _87026 s x' t x t' h1 h2 h0)). Qed.
Lemma lem3341255 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (x : _86990) (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term992 _86990 _87026 s t x) : False.
Proof. exact (ex_elim (@lem3336306 _86990 _87026 s t x h3) (fun t' : _86990 -> Prop => fun h0 : term991 _86990 _87026 s t x t' => @lem3341254 _86990 _87026 s t x t' h1 h2 h0)). Qed.
Lemma lem3341256 {_86990 _87026 : Type'} (s : type686 _86990) (t : _86990 -> Prop) (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term994 _86990 _87026 s t) : False.
Proof. exact (ex_elim (@lem3336305 _86990 _87026 s t h3) (fun x : _86990 => fun h0 : term993 _86990 _87026 s t x => @lem3341255 _86990 _87026 s t x h1 h2 h0)). Qed.
Lemma lem3341257 {_86990 _87026 : Type'} (s : type686 _86990) (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term996 _86990 _87026 s) : False.
Proof. exact (ex_elim (@lem3336304 _86990 _87026 s h3) (fun t : _86990 -> Prop => fun h0 : term995 _86990 _87026 s t => @lem3341256 _86990 _87026 s t h1 h2 h0)). Qed.
Lemma lem3341258 {_86990 _87026 : Type'} (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term165 _86990 _87026) : False.
Proof. exact (ex_elim (@lem3334515 _86990 _87026 h3) (fun s : type686 _86990 => fun h0 : term997 _86990 _87026 s => @lem3341257 _86990 _87026 s h1 h2 h0)). Qed.
Lemma lem3341259 {_86990 _87026 : Type'} (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term165 _86990 _87026) : term172 _87026.
Proof. exact (fun h0 : term166 _87026 => @lem3341258 _86990 _87026 h1 h2 h3). Qed.
Lemma lem3341260 {_87026 : Type'} : (term172 _87026) = (term173 _87026).
Proof. exact (@lem69 (term166 _87026)). Qed.
Lemma lem3341261 {_86990 _87026 : Type'} (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term165 _86990 _87026) : term173 _87026.
Proof. exact (EQ_MP (@lem3341260 _87026) (@lem3341259 _86990 _87026 h1 h2 h3)). Qed.
Lemma lem3341262 {_86990 _87026 : Type'} (h1 : term167 _86990) (h2 : term167 _87026) (h3 : term165 _86990 _87026) : term176 _86990 _87026.
Proof. exact (fun h0 : term166 _86990 => @lem3341261 _86990 _87026 h1 h2 h3). Qed.
Lemma lem3341263 {_86990 _87026 : Type'} (h1 : term167 _86990) (h2 : term165 _86990 _87026) : term179 _86990 _87026.
Proof. exact (fun h0 : term167 _87026 => @lem3341262 _86990 _87026 h1 h0 h2). Qed.
Lemma lem3341264 {_86990 _87026 : Type'} (h1 : term165 _86990 _87026) : term181 _86990 _87026.
Proof. exact (fun h0 : term167 _86990 => @lem3341263 _86990 _87026 h0 h1). Qed.
Lemma lem3341265 {_86990 _87026 : Type'} : term183 _86990 _87026.
Proof. exact (fun h0 : term165 _86990 _87026 => @lem3341264 _86990 _87026 h0). Qed.
Lemma lem3341266 {_86990 _87026 : Type'} : term168 _86990 _87026.
Proof. exact (EQ_MP (@lem3330853 _86990 _87026) (@lem3341265 _86990 _87026)). Qed.
Lemma lem3341268 {_86990 _87026 : Type'} : term168 _86990 _87026.
Proof. exact (@lem3330085 _86990 _87026 (@lem3341266 _86990 _87026)). Qed.
Lemma lem3341269 {_86990 _87026 : Type'} (h1 : term165 _86990 _87026) : term180 _86990 _87026.
Proof. exact (@lem3341268 _86990 _87026 (@lem3330063 _86990 _87026 h1)). Qed.
Lemma lem3341270 {_86990 _87026 : Type'} (h1 : term165 _86990 _87026) : term178 _86990 _87026.
Proof. exact (@lem3341269 _86990 _87026 h1 (@lem3330065 _86990)). Qed.
Lemma lem3341271 {_86990 _87026 : Type'} (h1 : term165 _86990 _87026) : term175 _86990 _87026.
Proof. exact (@lem3341270 _86990 _87026 h1 (@lem3330066 _87026)). Qed.
Lemma lem3341272 {_86990 _87026 : Type'} (h1 : term165 _86990 _87026) : term172 _87026.
Proof. exact (@lem3341271 _86990 _87026 h1 (@lem3330064 _86990)). Qed.
Lemma lem3341273 {_86990 _87026 : Type'} (h1 : term165 _86990 _87026) : False.
Proof. exact (@lem3341272 _86990 _87026 h1 (@lem3330067 _87026)). Qed.
Lemma lem3341274 {_86990 _87026 : Type'} (h1 : term165 _86990 _87026) : (term165 _86990 _87026) = False.
Proof. exact (prop_ext (fun h2 : term165 _86990 _87026 => @lem3341273 _86990 _87026 h1) (fun h2 : False => @lem3330063 _86990 _87026 h1)). Qed.
Lemma lem3341275 {_86990 _87026 : Type'} (h1 : term165 _86990 _87026) : False.
Proof. exact (EQ_MP (@lem3341274 _86990 _87026 h1) (@lem3330063 _86990 _87026 h1)). Qed.
Lemma lem3341276 {_86990 _87026 : Type'} : term164 _86990 _87026.
Proof. exact (fun h0 : term165 _86990 _87026 => @lem3341275 _86990 _87026 h0). Qed.
Lemma lem3341277 {_86990 _87026 : Type'} : term162 _86990 _87026.
Proof. exact (EQ_MP (@lem3330062 _86990 _87026) (@lem3341276 _86990 _87026)). Qed.
Lemma lem3341278 {_86990 _87026 : Type'} : term54 _86990 _87026.
Proof. exact (EQ_MP (@lem3330058 _86990 _87026) (@lem3341277 _86990 _87026)). Qed.
Lemma lem3341279 {_86990 _87026 : Type'} : term53 _86990 _87026.
Proof. exact (EQ_MP (@lem3329748 _86990 _87026) (@lem3341278 _86990 _87026)). Qed.
