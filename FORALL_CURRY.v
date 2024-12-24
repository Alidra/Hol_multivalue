Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_CURRY_term_abbrevs.
Require Import FORALL_UNCURRY_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm52758_spec.
Require Import thm52761_spec.
Lemma lem53660 {_5264 _5271 _5272 : Type'} : term0 _5264 _5271 _5272.
Proof. exact (EQ_MP (@lem52761 _5264 _5271 _5272) (@lem52758 _5264 _5271 _5272)). Qed.
Lemma lem53661 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : term1 _5264 _5271 _5272 f.
Proof. exact (@lem53660 _5264 _5271 _5272 f). Qed.
Lemma lem53662 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term1 _5264 _5271 _5272 f) = ((term2 _5264 _5271 _5272 f) = f).
Proof. exact (eq_refl (term1 _5264 _5271 _5272 f)). Qed.
Lemma lem53664 {A B C : Type'} (P : type443 A B C) : term3 A B C P.
Proof. exact (@lem53018 A B C P). Qed.
Lemma lem53665 {A B C : Type'} (P : type443 A B C) : (term3 A B C P) = ((term4 A B C P) = (term5 A B C P)).
Proof. exact (eq_refl (term3 A B C P)). Qed.
Lemma lem53686 {A B C : Type'} (P : type443 A B C) : (term4 A B C P) = (term5 A B C P).
Proof. exact (EQ_MP (@lem53665 A B C P) (@lem53664 A B C P)). Qed.
Lemma lem53687 {_5456 _5462 _5463 : Type'} (P : type876 _5456 _5462 _5463) : (term6 _5456 _5462 _5463 P) = (term7 _5456 _5462 _5463 P).
Proof. exact (@lem53686 _5463 _5462 _5456 P). Qed.
Lemma lem53688 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : (term8 _5456 _5462 _5463 P) = (term9 _5456 _5462 _5463 P).
Proof. exact (@lem53687 _5456 _5462 _5463 (term10 _5456 _5462 _5463 P)). Qed.
Lemma lem53689 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) (f : type1518 _5456 _5462 _5463) : (term11 _5456 _5462 _5463 P f) = (term12 _5456 _5462 _5463 P f).
Proof. exact (eq_refl (term11 _5456 _5462 _5463 P f)). Qed.
Lemma lem53690 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : (term13 _5456 _5462 _5463 P) = (term10 _5456 _5462 _5463 P).
Proof. exact (fun_ext (fun f : type1518 _5456 _5462 _5463 => @lem53689 _5456 _5462 _5463 P f)). Qed.
Lemma lem53691 {_5456 _5462 _5463 : Type'} : (@all (_5463 -> _5462 -> _5456)) = (@all (_5463 -> _5462 -> _5456)).
Proof. exact (eq_refl (@all (_5463 -> _5462 -> _5456))). Qed.
Lemma lem53692 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : (term8 _5456 _5462 _5463 P) = (term14 _5456 _5462 _5463 P).
Proof. exact (MK_COMB (@lem53691 _5456 _5462 _5463) (@lem53690 _5456 _5462 _5463 P)). Qed.
Lemma lem53693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem53694 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : (term15 _5456 _5462 _5463 P) = (term16 _5456 _5462 _5463 P).
Proof. exact (MK_COMB (@lem53693) (@lem53692 _5456 _5462 _5463 P)). Qed.
Lemma lem53695 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) (f : type1228 _5456 _5462 _5463) : (term17 _5456 _5462 _5463 P f) = (term18 _5456 _5462 _5463 P f).
Proof. exact (eq_refl (term17 _5456 _5462 _5463 P f)). Qed.
Lemma lem53696 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : (term19 _5456 _5462 _5463 P) = (term20 _5456 _5462 _5463 P).
Proof. exact (fun_ext (fun f : type1228 _5456 _5462 _5463 => @lem53695 _5456 _5462 _5463 P f)). Qed.
Lemma lem53697 {_5456 _5462 _5463 : Type'} : (@all ((prod _5463 _5462) -> _5456)) = (@all ((prod _5463 _5462) -> _5456)).
Proof. exact (eq_refl (@all ((prod _5463 _5462) -> _5456))). Qed.
Lemma lem53698 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : (term9 _5456 _5462 _5463 P) = (term21 _5456 _5462 _5463 P).
Proof. exact (MK_COMB (@lem53697 _5456 _5462 _5463) (@lem53696 _5456 _5462 _5463 P)). Qed.
Lemma lem53699 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : ((term8 _5456 _5462 _5463 P) = (term9 _5456 _5462 _5463 P)) = ((term14 _5456 _5462 _5463 P) = (term21 _5456 _5462 _5463 P)).
Proof. exact (MK_COMB (@lem53694 _5456 _5462 _5463 P) (@lem53698 _5456 _5462 _5463 P)). Qed.
Lemma lem53700 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : (term14 _5456 _5462 _5463 P) = (term21 _5456 _5462 _5463 P).
Proof. exact (EQ_MP (@lem53699 _5456 _5462 _5463 P) (@lem53688 _5456 _5462 _5463 P)). Qed.
Lemma lem53741 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem53742 {_5456 _5462 _5463 : Type'} (f : type1518 _5456 _5462 _5463) (y : _5463) : (term23 _5456 _5462 _5463 f y) = (f y).
Proof. exact (@lem53741 _5463 (_5462 -> _5456) f y). Qed.
Lemma lem53743 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) : (term24 _5456 _5462 _5463 f a) = (term25 _5456 _5462 _5463 f a).
Proof. exact (@lem53742 _5456 _5462 _5463 (term26 _5456 _5462 _5463 f) a). Qed.
Lemma lem53744 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) : (term25 _5456 _5462 _5463 f a) = (term27 _5456 _5462 _5463 f a).
Proof. exact (eq_refl (term25 _5456 _5462 _5463 f a)). Qed.
Lemma lem53745 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) : (term28 _5456 _5462 _5463 f) = (term26 _5456 _5462 _5463 f).
Proof. exact (fun_ext (fun a : _5463 => @lem53744 _5456 _5462 _5463 f a)). Qed.
Lemma lem53746 {_5463 : Type'} (a : _5463) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem53747 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) : (term24 _5456 _5462 _5463 f a) = (term25 _5456 _5462 _5463 f a).
Proof. exact (MK_COMB (@lem53745 _5456 _5462 _5463 f) (@lem53746 _5463 a)). Qed.
Lemma lem53748 {_5456 _5462 : Type'} : (@eq (_5462 -> _5456)) = (@eq (_5462 -> _5456)).
Proof. exact (eq_refl (@eq (_5462 -> _5456))). Qed.
Lemma lem53749 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) : (term29 _5456 _5462 _5463 f a) = (term30 _5456 _5462 _5463 f a).
Proof. exact (MK_COMB (@lem53748 _5456 _5462) (@lem53747 _5456 _5462 _5463 f a)). Qed.
Lemma lem53750 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) : (term25 _5456 _5462 _5463 f a) = (term27 _5456 _5462 _5463 f a).
Proof. exact (eq_refl (term25 _5456 _5462 _5463 f a)). Qed.
Lemma lem53751 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) : ((term24 _5456 _5462 _5463 f a) = (term25 _5456 _5462 _5463 f a)) = ((term25 _5456 _5462 _5463 f a) = (term27 _5456 _5462 _5463 f a)).
Proof. exact (MK_COMB (@lem53749 _5456 _5462 _5463 f a) (@lem53750 _5456 _5462 _5463 f a)). Qed.
Lemma lem53752 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) : (term25 _5456 _5462 _5463 f a) = (term27 _5456 _5462 _5463 f a).
Proof. exact (EQ_MP (@lem53751 _5456 _5462 _5463 f a) (@lem53743 _5456 _5462 _5463 f a)). Qed.
Lemma lem53753 {_5462 : Type'} (b : _5462) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem53754 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) (b : _5462) : (term31 _5456 _5462 _5463 f a b) = (term32 _5456 _5462 _5463 f a b).
Proof. exact (MK_COMB (@lem53752 _5456 _5462 _5463 f a) (@lem53753 _5462 b)). Qed.
Lemma lem53756 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem53757 {_5456 _5462 : Type'} (f : _5462 -> _5456) (y : _5462) : (term33 _5456 _5462 f y) = (f y).
Proof. exact (@lem53756 _5462 _5456 f y). Qed.
Lemma lem53758 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) (b : _5462) : (term34 _5456 _5462 _5463 f a b) = (term32 _5456 _5462 _5463 f a b).
Proof. exact (@lem53757 _5456 _5462 (term27 _5456 _5462 _5463 f a) b). Qed.
Lemma lem53759 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) (b : _5462) : (term32 _5456 _5462 _5463 f a b) = (term35 _5456 _5462 _5463 f a b).
Proof. exact (eq_refl (term32 _5456 _5462 _5463 f a b)). Qed.
Lemma lem53760 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) : (term36 _5456 _5462 _5463 f a) = (term27 _5456 _5462 _5463 f a).
Proof. exact (fun_ext (fun b : _5462 => @lem53759 _5456 _5462 _5463 f a b)). Qed.
Lemma lem53761 {_5462 : Type'} (b : _5462) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem53762 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) (b : _5462) : (term34 _5456 _5462 _5463 f a b) = (term32 _5456 _5462 _5463 f a b).
Proof. exact (MK_COMB (@lem53760 _5456 _5462 _5463 f a) (@lem53761 _5462 b)). Qed.
Lemma lem53763 {_5456 : Type'} : (@eq _5456) = (@eq _5456).
Proof. exact (eq_refl (@eq _5456)). Qed.
Lemma lem53764 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) (b : _5462) : (term37 _5456 _5462 _5463 f a b) = (term38 _5456 _5462 _5463 f a b).
Proof. exact (MK_COMB (@lem53763 _5456) (@lem53762 _5456 _5462 _5463 f a b)). Qed.
Lemma lem53765 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) (b : _5462) : (term32 _5456 _5462 _5463 f a b) = (term35 _5456 _5462 _5463 f a b).
Proof. exact (eq_refl (term32 _5456 _5462 _5463 f a b)). Qed.
Lemma lem53766 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) (b : _5462) : ((term34 _5456 _5462 _5463 f a b) = (term32 _5456 _5462 _5463 f a b)) = ((term32 _5456 _5462 _5463 f a b) = (term35 _5456 _5462 _5463 f a b)).
Proof. exact (MK_COMB (@lem53764 _5456 _5462 _5463 f a b) (@lem53765 _5456 _5462 _5463 f a b)). Qed.
Lemma lem53767 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) (b : _5462) : (term32 _5456 _5462 _5463 f a b) = (term35 _5456 _5462 _5463 f a b).
Proof. exact (EQ_MP (@lem53766 _5456 _5462 _5463 f a b) (@lem53758 _5456 _5462 _5463 f a b)). Qed.
Lemma lem53768 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) (a : _5463) (b : _5462) : (term31 _5456 _5462 _5463 f a b) = (term35 _5456 _5462 _5463 f a b).
Proof. exact (TRANS (@lem53754 _5456 _5462 _5463 f a b) (@lem53767 _5456 _5462 _5463 f a b)). Qed.
Lemma lem53769 {_5456 _5462 _5463 : Type'} (f' : type1228 _5456 _5462 _5463) (a : _5463) (b : _5462) : (term39 _5456 _5462 _5463 f' a b) = (term39 _5456 _5462 _5463 f' a b).
Proof. exact (eq_refl (term39 _5456 _5462 _5463 f' a b)). Qed.
Lemma lem53770 {_5456 _5462 _5463 : Type'} (f' : type1228 _5456 _5462 _5463) (f : type1228 _5456 _5462 _5463) (a : _5463) (b : _5462) : (term40 _5456 _5462 _5463 f' f a b) = (term41 _5456 _5462 _5463 f' f a b).
Proof. exact (MK_COMB (@lem53769 _5456 _5462 _5463 f' a b) (@lem53768 _5456 _5462 _5463 f a b)). Qed.
Lemma lem53771 {_5456 _5462 _5463 : Type'} (f' : type1228 _5456 _5462 _5463) (f : type1228 _5456 _5462 _5463) (a : _5463) : (term42 _5456 _5462 _5463 f' f a) = (term43 _5456 _5462 _5463 f' f a).
Proof. exact (fun_ext (fun b : _5462 => @lem53770 _5456 _5462 _5463 f' f a b)). Qed.
Lemma lem53772 {_5462 : Type'} : (@all _5462) = (@all _5462).
Proof. exact (eq_refl (@all _5462)). Qed.
Lemma lem53773 {_5456 _5462 _5463 : Type'} (f' : type1228 _5456 _5462 _5463) (f : type1228 _5456 _5462 _5463) (a : _5463) : (term44 _5456 _5462 _5463 f' f a) = (term45 _5456 _5462 _5463 f' f a).
Proof. exact (MK_COMB (@lem53772 _5462) (@lem53771 _5456 _5462 _5463 f' f a)). Qed.
Lemma lem53780 {_5456 _5462 _5463 : Type'} (f' : type1228 _5456 _5462 _5463) (f : type1228 _5456 _5462 _5463) : (term46 _5456 _5462 _5463 f' f) = (term47 _5456 _5462 _5463 f' f).
Proof. exact (fun_ext (fun a : _5463 => @lem53773 _5456 _5462 _5463 f' f a)). Qed.
Lemma lem53781 {_5463 : Type'} : (@all _5463) = (@all _5463).
Proof. exact (eq_refl (@all _5463)). Qed.
Lemma lem53782 {_5456 _5462 _5463 : Type'} (f' : type1228 _5456 _5462 _5463) (f : type1228 _5456 _5462 _5463) : (term48 _5456 _5462 _5463 f' f) = (term49 _5456 _5462 _5463 f' f).
Proof. exact (MK_COMB (@lem53781 _5463) (@lem53780 _5456 _5462 _5463 f' f)). Qed.
Lemma lem53789 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) : (term50 _5456 _5462 _5463 f) = (term51 _5456 _5462 _5463 f).
Proof. exact (fun_ext (fun f' : type1228 _5456 _5462 _5463 => @lem53782 _5456 _5462 _5463 f' f)). Qed.
Lemma lem53790 {_5456 _5462 _5463 : Type'} : (@GABS ((prod _5463 _5462) -> _5456)) = (@GABS ((prod _5463 _5462) -> _5456)).
Proof. exact (eq_refl (@GABS ((prod _5463 _5462) -> _5456))). Qed.
Lemma lem53791 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) : (term52 _5456 _5462 _5463 f) = (term2 _5456 _5462 _5463 f).
Proof. exact (MK_COMB (@lem53790 _5456 _5462 _5463) (@lem53789 _5456 _5462 _5463 f)). Qed.
Lemma lem53793 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term2 _5264 _5271 _5272 f) = f.
Proof. exact (EQ_MP (@lem53662 _5264 _5271 _5272 f) (@lem53661 _5264 _5271 _5272 f)). Qed.
Lemma lem53794 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) : (term2 _5456 _5462 _5463 f) = f.
Proof. exact (@lem53793 _5456 _5462 _5463 f). Qed.
Lemma lem53795 {_5456 _5462 _5463 : Type'} (f : type1228 _5456 _5462 _5463) : (term52 _5456 _5462 _5463 f) = f.
Proof. exact (TRANS (@lem53791 _5456 _5462 _5463 f) (@lem53794 _5456 _5462 _5463 f)). Qed.
Lemma lem53796 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem53797 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) (f : type1228 _5456 _5462 _5463) : (term18 _5456 _5462 _5463 P f) = (P f).
Proof. exact (MK_COMB (@lem53796 _5456 _5462 _5463 P) (@lem53795 _5456 _5462 _5463 f)). Qed.
Lemma lem53798 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : (term20 _5456 _5462 _5463 P) = (term53 _5456 _5462 _5463 P).
Proof. exact (fun_ext (fun f : type1228 _5456 _5462 _5463 => @lem53797 _5456 _5462 _5463 P f)). Qed.
Lemma lem53799 {_5456 _5462 _5463 : Type'} : (@all ((prod _5463 _5462) -> _5456)) = (@all ((prod _5463 _5462) -> _5456)).
Proof. exact (eq_refl (@all ((prod _5463 _5462) -> _5456))). Qed.
Lemma lem53800 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : (term21 _5456 _5462 _5463 P) = (term54 _5456 _5462 _5463 P).
Proof. exact (MK_COMB (@lem53799 _5456 _5462 _5463) (@lem53798 _5456 _5462 _5463 P)). Qed.
Lemma lem53807 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : (term14 _5456 _5462 _5463 P) = (term54 _5456 _5462 _5463 P).
Proof. exact (TRANS (@lem53700 _5456 _5462 _5463 P) (@lem53800 _5456 _5462 _5463 P)). Qed.
Lemma lem53808 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : (term55 _5456 _5462 _5463 P) = (term55 _5456 _5462 _5463 P).
Proof. exact (eq_refl (term55 _5456 _5462 _5463 P)). Qed.
Lemma lem53809 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : ((term54 _5456 _5462 _5463 P) = (term14 _5456 _5462 _5463 P)) = ((term54 _5456 _5462 _5463 P) = (term54 _5456 _5462 _5463 P)).
Proof. exact (MK_COMB (@lem53808 _5456 _5462 _5463 P) (@lem53807 _5456 _5462 _5463 P)). Qed.
Lemma lem53811 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem53812 (x : Prop) : (x = x) = True.
Proof. exact (@lem53811 Prop x). Qed.
Lemma lem53813 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : ((term54 _5456 _5462 _5463 P) = (term54 _5456 _5462 _5463 P)) = True.
Proof. exact (@lem53812 (term54 _5456 _5462 _5463 P)). Qed.
Lemma lem53814 {_5456 _5462 _5463 : Type'} (P : type333 _5456 _5462 _5463) : ((term54 _5456 _5462 _5463 P) = (term14 _5456 _5462 _5463 P)) = True.
Proof. exact (TRANS (@lem53809 _5456 _5462 _5463 P) (@lem53813 _5456 _5462 _5463 P)). Qed.
Lemma lem53815 {_5456 _5462 _5463 : Type'} : (term56 _5456 _5462 _5463) = (term57 _5456 _5462 _5463).
Proof. exact (fun_ext (fun P : type333 _5456 _5462 _5463 => @lem53814 _5456 _5462 _5463 P)). Qed.
Lemma lem53816 {_5456 _5462 _5463 : Type'} : (@all (((prod _5463 _5462) -> _5456) -> Prop)) = (@all (((prod _5463 _5462) -> _5456) -> Prop)).
Proof. exact (eq_refl (@all (((prod _5463 _5462) -> _5456) -> Prop))). Qed.
Lemma lem53817 {_5456 _5462 _5463 : Type'} : (term58 _5456 _5462 _5463) = (term59 _5456 _5462 _5463).
Proof. exact (MK_COMB (@lem53816 _5456 _5462 _5463) (@lem53815 _5456 _5462 _5463)). Qed.
Lemma lem53819 {A : Type'} (t : Prop) : (term60 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem53820 {_5456 _5462 _5463 : Type'} (t : Prop) : (term61 _5456 _5462 _5463 t) = t.
Proof. exact (@lem53819 (type333 _5456 _5462 _5463) t). Qed.
Lemma lem53821 {_5456 _5462 _5463 : Type'} : (term59 _5456 _5462 _5463) = True.
Proof. exact (@lem53820 _5456 _5462 _5463 True). Qed.
Lemma lem53822 {_5456 _5462 _5463 : Type'} : (term58 _5456 _5462 _5463) = True.
Proof. exact (TRANS (@lem53817 _5456 _5462 _5463) (@lem53821 _5456 _5462 _5463)). Qed.
Lemma lem53823 {_5456 _5462 _5463 : Type'} : True = (term58 _5456 _5462 _5463).
Proof. exact (SYM (@lem53822 _5456 _5462 _5463)). Qed.
Lemma lem53824 {_5456 _5462 _5463 : Type'} : term58 _5456 _5462 _5463.
Proof. exact (EQ_MP (@lem53823 _5456 _5462 _5463) (@lem0)). Qed.
