Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_C_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INJECTIVE_ON_LEFT_INVERSE_spec.
Require Import RIGHT_AND_EXISTS_THM_spec.
Require Import SURJECTIVE_ON_RIGHT_INVERSE_spec.
Require Import le_c_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem5125624 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem5950 A P). Qed.
Lemma lem5125625 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem5125626 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem5125625 A P) (@lem5125624 A P)). Qed.
Lemma lem5125627 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem5125626 A P Q). Qed.
Lemma lem5125628 {A : Type'} (P : Prop) (Q : A -> Prop) : (term2 A P Q) = ((term3 A P Q) = (term4 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem5125639 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : term5 _91307 _91308 s f.
Proof. exact (@lem3562737 _91307 _91308 s f). Qed.
Lemma lem5125640 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : (term5 _91307 _91308 s f) = (term6 _91307 _91308 s f).
Proof. exact (eq_refl (term5 _91307 _91308 s f)). Qed.
Lemma lem5125641 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : term6 _91307 _91308 s f.
Proof. exact (EQ_MP (@lem5125640 _91307 _91308 s f) (@lem5125639 _91307 _91308 s f)). Qed.
Lemma lem5125642 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) (t : _91308 -> Prop) : term7 _91307 _91308 s f t.
Proof. exact (@lem5125641 _91307 _91308 s f t). Qed.
Lemma lem5125643 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term7 _91307 _91308 s f t) = ((term8 _91307 _91308 t s f) = (term9 _91307 _91308 t s f)).
Proof. exact (eq_refl (term7 _91307 _91308 s f t)). Qed.
Lemma lem5125645 {_91401 _91404 : Type'} (f : _91401 -> _91404) : term10 _91401 _91404 f.
Proof. exact (@lem3566182 _91401 _91404 f). Qed.
Lemma lem5125646 {_91401 _91404 : Type'} (f : _91401 -> _91404) : (term10 _91401 _91404 f) = (term11 _91401 _91404 f).
Proof. exact (eq_refl (term10 _91401 _91404 f)). Qed.
Lemma lem5125647 {_91401 _91404 : Type'} (f : _91401 -> _91404) : term11 _91401 _91404 f.
Proof. exact (EQ_MP (@lem5125646 _91401 _91404 f) (@lem5125645 _91401 _91404 f)). Qed.
Lemma lem5125648 {_91401 _91404 : Type'} (f : _91401 -> _91404) (s : _91401 -> Prop) : term12 _91401 _91404 f s.
Proof. exact (@lem5125647 _91401 _91404 f s). Qed.
Lemma lem5125649 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term12 _91401 _91404 f s) = ((term13 _91401 _91404 s f) = (term14 _91401 _91404 s f)).
Proof. exact (eq_refl (term12 _91401 _91404 f s)). Qed.
Lemma lem5125651 {_114929 _114934 : Type'} (t : _114929 -> Prop) : term15 _114929 _114934 t.
Proof. exact (@lem5120869 _114929 _114934 t). Qed.
Lemma lem5125652 {_114929 _114934 : Type'} (t : _114929 -> Prop) : (term15 _114929 _114934 t) = (term16 _114929 _114934 t).
Proof. exact (eq_refl (term15 _114929 _114934 t)). Qed.
Lemma lem5125653 {_114929 _114934 : Type'} (t : _114929 -> Prop) : term16 _114929 _114934 t.
Proof. exact (EQ_MP (@lem5125652 _114929 _114934 t) (@lem5125651 _114929 _114934 t)). Qed.
Lemma lem5125654 {_114929 _114934 : Type'} (t : _114929 -> Prop) (s : _114934 -> Prop) : term17 _114929 _114934 t s.
Proof. exact (@lem5125653 _114929 _114934 t s). Qed.
Lemma lem5125655 {_114929 _114934 : Type'} (t : _114929 -> Prop) (s : _114934 -> Prop) : (term17 _114929 _114934 t s) = ((@le_c _114929 _114934 s t) = (term18 _114929 _114934 t s)).
Proof. exact (eq_refl (term17 _114929 _114934 t s)). Qed.
Lemma lem5125668 {_114929 _114934 : Type'} (t : _114929 -> Prop) (s : _114934 -> Prop) : (@le_c _114929 _114934 s t) = (term18 _114929 _114934 t s).
Proof. exact (EQ_MP (@lem5125655 _114929 _114934 t s) (@lem5125654 _114929 _114934 t s)). Qed.
Lemma lem5125669 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (@le_c _115057 _115054 s t) = (term19 _115054 _115057 t s).
Proof. exact (@lem5125668 _115057 _115054 t s). Qed.
Lemma lem5125683 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term13 _91401 _91404 s f) = (term14 _91401 _91404 s f).
Proof. exact (EQ_MP (@lem5125649 _91401 _91404 s f) (@lem5125648 _91401 _91404 f s)). Qed.
Lemma lem5125684 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term13 _115054 _115057 s f) = (term14 _115054 _115057 s f).
Proof. exact (@lem5125683 _115054 _115057 s f). Qed.
Lemma lem5125697 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term20 _115054 _115057 s f t) = (term20 _115054 _115057 s f t).
Proof. exact (eq_refl (term20 _115054 _115057 s f t)). Qed.
Lemma lem5125698 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term21 _115054 _115057 t s f) = (term22 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5125697 _115054 _115057 s f t) (@lem5125684 _115054 _115057 s f)). Qed.
Lemma lem5125700 {A : Type'} (P : Prop) (Q : A -> Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem5125628 A P Q) (@lem5125627 A P Q)). Qed.
Lemma lem5125701 {_115054 _115057 : Type'} (P : Prop) (Q : type805 _115054 _115057) : (term23 _115054 _115057 P Q) = (term24 _115054 _115057 P Q).
Proof. exact (@lem5125700 (_115057 -> _115054) P Q). Qed.
Lemma lem5125702 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term25 _115054 _115057 t s f) = (term26 _115054 _115057 t s f).
Proof. exact (@lem5125701 _115054 _115057 (term27 _115054 _115057 s f t) (term28 _115054 _115057 s f)). Qed.
Lemma lem5125703 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term29 _115054 _115057 s f g) = (term30 _115054 _115057 s g f).
Proof. exact (eq_refl (term29 _115054 _115057 s f g)). Qed.
Lemma lem5125704 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term31 _115054 _115057 s f) = (term28 _115054 _115057 s f).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5125703 _115054 _115057 s g f)). Qed.
Lemma lem5125705 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5125706 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term32 _115054 _115057 s f) = (term14 _115054 _115057 s f).
Proof. exact (MK_COMB (@lem5125705 _115054 _115057) (@lem5125704 _115054 _115057 s f)). Qed.
Lemma lem5125707 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term20 _115054 _115057 s f t) = (term20 _115054 _115057 s f t).
Proof. exact (eq_refl (term20 _115054 _115057 s f t)). Qed.
Lemma lem5125708 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term25 _115054 _115057 t s f) = (term22 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5125707 _115054 _115057 s f t) (@lem5125706 _115054 _115057 s f)). Qed.
Lemma lem5125709 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5125710 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term33 _115054 _115057 t s f) = (term34 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5125709) (@lem5125708 _115054 _115057 t s f)). Qed.
Lemma lem5125711 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term29 _115054 _115057 s f g) = (term30 _115054 _115057 s g f).
Proof. exact (eq_refl (term29 _115054 _115057 s f g)). Qed.
Lemma lem5125712 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term20 _115054 _115057 s f t) = (term20 _115054 _115057 s f t).
Proof. exact (eq_refl (term20 _115054 _115057 s f t)). Qed.
Lemma lem5125713 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term35 _115054 _115057 t s f g) = (term36 _115054 _115057 t s g f).
Proof. exact (MK_COMB (@lem5125712 _115054 _115057 s f t) (@lem5125711 _115054 _115057 s g f)). Qed.
Lemma lem5125714 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term37 _115054 _115057 t s f) = (term38 _115054 _115057 t s f).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5125713 _115054 _115057 t s g f)). Qed.
Lemma lem5125715 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5125716 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term26 _115054 _115057 t s f) = (term39 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5125715 _115054 _115057) (@lem5125714 _115054 _115057 t s f)). Qed.
Lemma lem5125717 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : ((term25 _115054 _115057 t s f) = (term26 _115054 _115057 t s f)) = ((term22 _115054 _115057 t s f) = (term39 _115054 _115057 t s f)).
Proof. exact (MK_COMB (@lem5125710 _115054 _115057 t s f) (@lem5125716 _115054 _115057 t s f)). Qed.
Lemma lem5125718 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term22 _115054 _115057 t s f) = (term39 _115054 _115057 t s f).
Proof. exact (EQ_MP (@lem5125717 _115054 _115057 t s f) (@lem5125702 _115054 _115057 t s f)). Qed.
Lemma lem5125739 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term21 _115054 _115057 t s f) = (term39 _115054 _115057 t s f).
Proof. exact (TRANS (@lem5125698 _115054 _115057 t s f) (@lem5125718 _115054 _115057 t s f)). Qed.
Lemma lem5125740 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term40 _115054 _115057 t s) = (term41 _115054 _115057 t s).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5125739 _115054 _115057 t s f)). Qed.
Lemma lem5125741 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5125742 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term19 _115054 _115057 t s) = (term42 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5125741 _115054 _115057) (@lem5125740 _115054 _115057 t s)). Qed.
Lemma lem5125747 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (@le_c _115057 _115054 s t) = (term42 _115054 _115057 t s).
Proof. exact (TRANS (@lem5125669 _115054 _115057 t s) (@lem5125742 _115054 _115057 t s)). Qed.
Lemma lem5125748 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5125749 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term43 _115054 _115057 s t) = (term44 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5125748) (@lem5125747 _115054 _115057 t s)). Qed.
Lemma lem5125755 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term8 _91307 _91308 t s f) = (term9 _91307 _91308 t s f).
Proof. exact (EQ_MP (@lem5125643 _91307 _91308 t s f) (@lem5125642 _91307 _91308 s f t)). Qed.
Lemma lem5125756 {_115054 _115057 : Type'} (t : _115054 -> Prop) (s : _115057 -> Prop) (f : _115057 -> _115054) : (term45 _115054 _115057 t s f) = (term46 _115054 _115057 t s f).
Proof. exact (@lem5125755 _115057 _115054 t s f). Qed.
Lemma lem5125757 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term45 _115054 _115057 s t g) = (term46 _115054 _115057 s t g).
Proof. exact (@lem5125756 _115054 _115057 s t g). Qed.
Lemma lem5125772 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term47 _115054 _115057 s t) = (term48 _115054 _115057 s t).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5125757 _115054 _115057 s t g)). Qed.
Lemma lem5125773 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5125774 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term49 _115054 _115057 s t) = (term50 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5125773 _115054 _115057) (@lem5125772 _115054 _115057 s t)). Qed.
Lemma lem5125779 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : ((@le_c _115057 _115054 s t) = (term49 _115054 _115057 s t)) = ((term42 _115054 _115057 t s) = (term50 _115054 _115057 s t)).
Proof. exact (MK_COMB (@lem5125749 _115054 _115057 t s) (@lem5125774 _115054 _115057 s t)). Qed.
Lemma lem5125782 {_115054 _115057 : Type'} (s : _115054 -> Prop) : (term51 _115054 _115057 s) = (term52 _115054 _115057 s).
Proof. exact (fun_ext (fun t : _115057 -> Prop => @lem5125779 _115054 _115057 s t)). Qed.
Lemma lem5125783 {_115057 : Type'} : (@all (_115057 -> Prop)) = (@all (_115057 -> Prop)).
Proof. exact (eq_refl (@all (_115057 -> Prop))). Qed.
Lemma lem5125784 {_115054 _115057 : Type'} (s : _115054 -> Prop) : (term53 _115054 _115057 s) = (term54 _115054 _115057 s).
Proof. exact (MK_COMB (@lem5125783 _115057) (@lem5125782 _115054 _115057 s)). Qed.
Lemma lem5125789 {_115054 _115057 : Type'} : (term55 _115054 _115057) = (term56 _115054 _115057).
Proof. exact (fun_ext (fun s : _115054 -> Prop => @lem5125784 _115054 _115057 s)). Qed.
Lemma lem5125790 {_115054 : Type'} : (@all (_115054 -> Prop)) = (@all (_115054 -> Prop)).
Proof. exact (eq_refl (@all (_115054 -> Prop))). Qed.
Lemma lem5125791 {_115054 _115057 : Type'} : (term57 _115054 _115057) = (term58 _115054 _115057).
Proof. exact (MK_COMB (@lem5125790 _115054) (@lem5125789 _115054 _115057)). Qed.
Lemma lem5125796 {_115054 _115057 : Type'} : (term58 _115054 _115057) = (term57 _115054 _115057).
Proof. exact (SYM (@lem5125791 _115054 _115057)). Qed.
Lemma lem5125798 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5125799 {_115054 _115057 : Type'} : (term58 _115054 _115057) = (term60 _115054 _115057).
Proof. exact (@lem5125798 (term58 _115054 _115057)). Qed.
Lemma lem5125800 {_115054 _115057 : Type'} : (term60 _115054 _115057) = (term58 _115054 _115057).
Proof. exact (SYM (@lem5125799 _115054 _115057)). Qed.
Lemma lem5125801 {_115054 _115057 : Type'} (h1 : term61 _115054 _115057) : term61 _115054 _115057.
Proof. exact (h1). Qed.
Lemma lem5125804 {_115054 _115057 : Type'} (h1 : term60 _115054 _115057) : term60 _115054 _115057.
Proof. exact (h1). Qed.
Lemma lem5125805 {_115054 _115057 : Type'} : term62 _115054 _115057.
Proof. exact (fun h0 : term60 _115054 _115057 => @lem5125804 _115054 _115057 h0). Qed.
Lemma lem5125806 {_115054 _115057 : Type'} (h1 : term62 _115054 _115057) : term62 _115054 _115057.
Proof. exact (h1). Qed.
Lemma lem5125807 {_115054 _115057 : Type'} (h1 : term60 _115054 _115057) : term60 _115054 _115057.
Proof. exact (h1). Qed.
Lemma lem5125808 {_115054 _115057 : Type'} (h1 : term60 _115054 _115057) (h2 : term62 _115054 _115057) : term60 _115054 _115057.
Proof. exact (@lem5125806 _115054 _115057 h2 (@lem5125807 _115054 _115057 h1)). Qed.
Lemma lem5125809 {_115054 _115057 : Type'} (h1 : term60 _115054 _115057) : term63 _115054 _115057.
Proof. exact (fun h0 : term62 _115054 _115057 => @lem5125808 _115054 _115057 h1 h0). Qed.
Lemma lem5125810 {_115054 _115057 : Type'} (h1 : term62 _115054 _115057) : term62 _115054 _115057.
Proof. exact (h1). Qed.
Lemma lem5125811 {_115054 _115057 : Type'} (h1 : term60 _115054 _115057) (h2 : term62 _115054 _115057) : term60 _115054 _115057.
Proof. exact (@lem5125809 _115054 _115057 h1 (@lem5125810 _115054 _115057 h2)). Qed.
Lemma lem5125812 {_115054 _115057 : Type'} (h1 : term62 _115054 _115057) : term62 _115054 _115057.
Proof. exact (fun h0 : term60 _115054 _115057 => @lem5125811 _115054 _115057 h0 h1). Qed.
Lemma lem5125813 {_115054 _115057 : Type'} : term64 _115054 _115057.
Proof. exact (fun h0 : term62 _115054 _115057 => @lem5125812 _115054 _115057 h0). Qed.
Lemma lem5125816 {_115054 _115057 : Type'} : term62 _115054 _115057.
Proof. exact (@lem5125813 _115054 _115057 (@lem5125805 _115054 _115057)). Qed.
Lemma lem5125817 {_115054 _115057 : Type'} : term62 _115054 _115057.
Proof. exact (@lem5125816 _115054 _115057). Qed.
Lemma lem5125819 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5125820 {_115054 _115057 : Type'} : (term60 _115054 _115057) = (term65 _115054 _115057).
Proof. exact (@lem5125819 (term61 _115054 _115057)). Qed.
Lemma lem5125822 (t : Prop) : (term66 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5125823 {_115054 _115057 : Type'} : (term65 _115054 _115057) = (term58 _115054 _115057).
Proof. exact (@lem5125822 (term58 _115054 _115057)). Qed.
Lemma lem5125828 {_115054 _115057 : Type'} : (term60 _115054 _115057) = (term58 _115054 _115057).
Proof. exact (TRANS (@lem5125820 _115054 _115057) (@lem5125823 _115054 _115057)). Qed.
Lemma lem5125838 {A : Type'} (P : Prop) (Q : A -> Prop) : (term4 A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem5125839 {_115054 _115057 : Type'} (P : Prop) (Q : type805 _115054 _115057) : (term24 _115054 _115057 P Q) = (term23 _115054 _115057 P Q).
Proof. exact (@lem5125838 (_115057 -> _115054) P Q). Qed.
Lemma lem5125840 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term26 _115054 _115057 t s f) = (term25 _115054 _115057 t s f).
Proof. exact (@lem5125839 _115054 _115057 (term27 _115054 _115057 s f t) (term28 _115054 _115057 s f)). Qed.
Lemma lem5125841 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term29 _115054 _115057 s f g) = (term30 _115054 _115057 s g f).
Proof. exact (eq_refl (term29 _115054 _115057 s f g)). Qed.
Lemma lem5125842 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term20 _115054 _115057 s f t) = (term20 _115054 _115057 s f t).
Proof. exact (eq_refl (term20 _115054 _115057 s f t)). Qed.
Lemma lem5125843 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term35 _115054 _115057 t s f g) = (term36 _115054 _115057 t s g f).
Proof. exact (MK_COMB (@lem5125842 _115054 _115057 s f t) (@lem5125841 _115054 _115057 s g f)). Qed.
Lemma lem5125844 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term37 _115054 _115057 t s f) = (term38 _115054 _115057 t s f).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5125843 _115054 _115057 t s g f)). Qed.
Lemma lem5125845 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5125846 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term26 _115054 _115057 t s f) = (term39 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5125845 _115054 _115057) (@lem5125844 _115054 _115057 t s f)). Qed.
Lemma lem5125847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5125848 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term67 _115054 _115057 t s f) = (term68 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5125847) (@lem5125846 _115054 _115057 t s f)). Qed.
Lemma lem5125849 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term29 _115054 _115057 s f g) = (term30 _115054 _115057 s g f).
Proof. exact (eq_refl (term29 _115054 _115057 s f g)). Qed.
Lemma lem5125850 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term31 _115054 _115057 s f) = (term28 _115054 _115057 s f).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5125849 _115054 _115057 s g f)). Qed.
Lemma lem5125851 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5125852 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term32 _115054 _115057 s f) = (term14 _115054 _115057 s f).
Proof. exact (MK_COMB (@lem5125851 _115054 _115057) (@lem5125850 _115054 _115057 s f)). Qed.
Lemma lem5125853 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term20 _115054 _115057 s f t) = (term20 _115054 _115057 s f t).
Proof. exact (eq_refl (term20 _115054 _115057 s f t)). Qed.
Lemma lem5125854 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term25 _115054 _115057 t s f) = (term22 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5125853 _115054 _115057 s f t) (@lem5125852 _115054 _115057 s f)). Qed.
Lemma lem5125855 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : ((term26 _115054 _115057 t s f) = (term25 _115054 _115057 t s f)) = ((term39 _115054 _115057 t s f) = (term22 _115054 _115057 t s f)).
Proof. exact (MK_COMB (@lem5125848 _115054 _115057 t s f) (@lem5125854 _115054 _115057 t s f)). Qed.
Lemma lem5125856 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term39 _115054 _115057 t s f) = (term22 _115054 _115057 t s f).
Proof. exact (EQ_MP (@lem5125855 _115054 _115057 t s f) (@lem5125840 _115054 _115057 t s f)). Qed.
Lemma lem5125875 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term41 _115054 _115057 t s) = (term69 _115054 _115057 t s).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5125856 _115054 _115057 t s f)). Qed.
Lemma lem5125876 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5125877 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term42 _115054 _115057 t s) = (term70 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5125876 _115054 _115057) (@lem5125875 _115054 _115057 t s)). Qed.
Lemma lem5125926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5125927 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term44 _115054 _115057 t s) = (term71 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5125926) (@lem5125877 _115054 _115057 t s)). Qed.
Lemma lem5125944 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term50 _115054 _115057 s t) = (term50 _115054 _115057 s t).
Proof. exact (eq_refl (term50 _115054 _115057 s t)). Qed.
Lemma lem5125945 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term42 _115054 _115057 t s) = (term50 _115054 _115057 s t)) = ((term70 _115054 _115057 t s) = (term50 _115054 _115057 s t)).
Proof. exact (MK_COMB (@lem5125927 _115054 _115057 t s) (@lem5125944 _115054 _115057 s t)). Qed.
Lemma lem5125946 {_115054 _115057 : Type'} (s : _115054 -> Prop) : (term52 _115054 _115057 s) = (term72 _115054 _115057 s).
Proof. exact (fun_ext (fun t : _115057 -> Prop => @lem5125945 _115054 _115057 s t)). Qed.
Lemma lem5125947 {_115057 : Type'} : (@all (_115057 -> Prop)) = (@all (_115057 -> Prop)).
Proof. exact (eq_refl (@all (_115057 -> Prop))). Qed.
Lemma lem5125948 {_115054 _115057 : Type'} (s : _115054 -> Prop) : (term54 _115054 _115057 s) = (term73 _115054 _115057 s).
Proof. exact (MK_COMB (@lem5125947 _115057) (@lem5125946 _115054 _115057 s)). Qed.
Lemma lem5125953 {_115054 _115057 : Type'} : (term56 _115054 _115057) = (term74 _115054 _115057).
Proof. exact (fun_ext (fun s : _115054 -> Prop => @lem5125948 _115054 _115057 s)). Qed.
Lemma lem5125954 {_115054 : Type'} : (@all (_115054 -> Prop)) = (@all (_115054 -> Prop)).
Proof. exact (eq_refl (@all (_115054 -> Prop))). Qed.
Lemma lem5125955 {_115054 _115057 : Type'} : (term58 _115054 _115057) = (term75 _115054 _115057).
Proof. exact (MK_COMB (@lem5125954 _115054) (@lem5125953 _115054 _115057)). Qed.
Lemma lem5125964 {_115054 _115057 : Type'} : (term60 _115054 _115057) = (term75 _115054 _115057).
Proof. exact (TRANS (@lem5125828 _115054 _115057) (@lem5125955 _115054 _115057)). Qed.
Lemma lem5125973 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) (x : _115054) : (term76 _115054 _115057 s t g g' x) = (term76 _115054 _115057 s t g g' x).
Proof. exact (eq_refl (term76 _115054 _115057 s t g g' x)). Qed.
Lemma lem5125974 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term77 _115054 _115057 s t g g') = (term77 _115054 _115057 s t g g').
Proof. exact (fun_ext (fun x : _115054 => @lem5125973 _115054 _115057 s t g g' x)). Qed.
Lemma lem5125975 {_115054 : Type'} : (@all _115054) = (@all _115054).
Proof. exact (eq_refl (@all _115054)). Qed.
Lemma lem5125976 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term78 _115054 _115057 s t g g') = (term78 _115054 _115057 s t g g').
Proof. exact (MK_COMB (@lem5125975 _115054) (@lem5125974 _115054 _115057 s t g g')). Qed.
Lemma lem5125977 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term79 _115054 _115057 s t g) = (term79 _115054 _115057 s t g).
Proof. exact (fun_ext (fun g' : _115054 -> _115057 => @lem5125976 _115054 _115057 s t g g')). Qed.
Lemma lem5125978 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5125979 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term46 _115054 _115057 s t g) = (term46 _115054 _115057 s t g).
Proof. exact (MK_COMB (@lem5125978 _115054 _115057) (@lem5125977 _115054 _115057 s t g)). Qed.
Lemma lem5125980 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term48 _115054 _115057 s t) = (term48 _115054 _115057 s t).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5125979 _115054 _115057 s t g)). Qed.
Lemma lem5125981 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5125982 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term50 _115054 _115057 s t) = (term50 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5125981 _115054 _115057) (@lem5125980 _115054 _115057 s t)). Qed.
Lemma lem5125987 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : (term80 _115054 _115057 s g f x) = (term80 _115054 _115057 s g f x).
Proof. exact (eq_refl (term80 _115054 _115057 s g f x)). Qed.
Lemma lem5125988 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term81 _115054 _115057 s g f) = (term81 _115054 _115057 s g f).
Proof. exact (fun_ext (fun x : _115054 => @lem5125987 _115054 _115057 s g f x)). Qed.
Lemma lem5125989 {_115054 : Type'} : (@all _115054) = (@all _115054).
Proof. exact (eq_refl (@all _115054)). Qed.
Lemma lem5125990 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term30 _115054 _115057 s g f) = (term30 _115054 _115057 s g f).
Proof. exact (MK_COMB (@lem5125989 _115054) (@lem5125988 _115054 _115057 s g f)). Qed.
Lemma lem5125991 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term28 _115054 _115057 s f) = (term28 _115054 _115057 s f).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5125990 _115054 _115057 s g f)). Qed.
Lemma lem5125992 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5125993 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term14 _115054 _115057 s f) = (term14 _115054 _115057 s f).
Proof. exact (MK_COMB (@lem5125992 _115054 _115057) (@lem5125991 _115054 _115057 s f)). Qed.
Lemma lem5125998 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term82 _115054 _115057 s f x t) = (term82 _115054 _115057 s f x t).
Proof. exact (eq_refl (term82 _115054 _115057 s f x t)). Qed.
Lemma lem5125999 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term83 _115054 _115057 s f t) = (term83 _115054 _115057 s f t).
Proof. exact (fun_ext (fun x : _115054 => @lem5125998 _115054 _115057 s f x t)). Qed.
Lemma lem5126000 {_115054 : Type'} : (@all _115054) = (@all _115054).
Proof. exact (eq_refl (@all _115054)). Qed.
Lemma lem5126001 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term27 _115054 _115057 s f t) = (term27 _115054 _115057 s f t).
Proof. exact (MK_COMB (@lem5126000 _115054) (@lem5125999 _115054 _115057 s f t)). Qed.
Lemma lem5126002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5126003 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term20 _115054 _115057 s f t) = (term20 _115054 _115057 s f t).
Proof. exact (MK_COMB (@lem5126002) (@lem5126001 _115054 _115057 s f t)). Qed.
Lemma lem5126004 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term22 _115054 _115057 t s f) = (term22 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126003 _115054 _115057 s f t) (@lem5125993 _115054 _115057 s f)). Qed.
Lemma lem5126005 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term69 _115054 _115057 t s) = (term69 _115054 _115057 t s).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5126004 _115054 _115057 t s f)). Qed.
Lemma lem5126006 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5126007 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term70 _115054 _115057 t s) = (term70 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126006 _115054 _115057) (@lem5126005 _115054 _115057 t s)). Qed.
Lemma lem5126008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5126009 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term71 _115054 _115057 t s) = (term71 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126008) (@lem5126007 _115054 _115057 t s)). Qed.
Lemma lem5126010 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term70 _115054 _115057 t s) = (term50 _115054 _115057 s t)) = ((term70 _115054 _115057 t s) = (term50 _115054 _115057 s t)).
Proof. exact (MK_COMB (@lem5126009 _115054 _115057 t s) (@lem5125982 _115054 _115057 s t)). Qed.
Lemma lem5126011 {_115054 _115057 : Type'} (s : _115054 -> Prop) : (term72 _115054 _115057 s) = (term72 _115054 _115057 s).
Proof. exact (fun_ext (fun t : _115057 -> Prop => @lem5126010 _115054 _115057 s t)). Qed.
Lemma lem5126012 {_115057 : Type'} : (@all (_115057 -> Prop)) = (@all (_115057 -> Prop)).
Proof. exact (eq_refl (@all (_115057 -> Prop))). Qed.
Lemma lem5126013 {_115054 _115057 : Type'} (s : _115054 -> Prop) : (term73 _115054 _115057 s) = (term73 _115054 _115057 s).
Proof. exact (MK_COMB (@lem5126012 _115057) (@lem5126011 _115054 _115057 s)). Qed.
Lemma lem5126014 {_115054 _115057 : Type'} : (term74 _115054 _115057) = (term74 _115054 _115057).
Proof. exact (fun_ext (fun s : _115054 -> Prop => @lem5126013 _115054 _115057 s)). Qed.
Lemma lem5126015 {_115054 : Type'} : (@all (_115054 -> Prop)) = (@all (_115054 -> Prop)).
Proof. exact (eq_refl (@all (_115054 -> Prop))). Qed.
Lemma lem5126016 {_115054 _115057 : Type'} : (term75 _115054 _115057) = (term75 _115054 _115057).
Proof. exact (MK_COMB (@lem5126015 _115054) (@lem5126014 _115054 _115057)). Qed.
Lemma lem5126083 {_115054 _115057 : Type'} : (term60 _115054 _115057) = (term75 _115054 _115057).
Proof. exact (TRANS (@lem5125964 _115054 _115057) (@lem5126016 _115054 _115057)). Qed.
Lemma lem5126084 {_115054 _115057 : Type'} : (term75 _115054 _115057) = (term60 _115054 _115057).
Proof. exact (SYM (@lem5126083 _115054 _115057)). Qed.
Lemma lem5126086 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5126087 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term70 _115054 _115057 t s) = (term50 _115054 _115057 s t)) = (term84 _115054 _115057 s t).
Proof. exact (@lem5126086 ((term70 _115054 _115057 t s) = (term50 _115054 _115057 s t))). Qed.
Lemma lem5126088 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term84 _115054 _115057 s t) = ((term70 _115054 _115057 t s) = (term50 _115054 _115057 s t)).
Proof. exact (SYM (@lem5126087 _115054 _115057 s t)). Qed.
Lemma lem5126089 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (h1 : term85 _115054 _115057 s t) : term85 _115054 _115057 s t.
Proof. exact (h1). Qed.
Lemma lem5126098 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term86 _115054 _115057 s f x t) = (term87 _115054 _115057 s f x t).
Proof. exact (@lem17362 (@IN _115054 x s) (term88 _115054 _115057 f x t)). Qed.
Lemma lem5126103 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term82 _115054 _115057 s f x t) = (term89 _115054 _115057 s f x t).
Proof. exact (@lem17265 (@IN _115054 x s) (term88 _115054 _115057 f x t)). Qed.
Lemma lem5126104 {_115054 : Type'} (P : _115054 -> Prop) : (term90 _115054 P) = (term91 _115054 P).
Proof. exact (@lem18392 _115054 P). Qed.
Lemma lem5126105 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term92 _115054 _115057 s f t) = (term93 _115054 _115057 s f t).
Proof. exact (@lem5126104 _115054 (term83 _115054 _115057 s f t)). Qed.
Lemma lem5126106 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term94 _115054 _115057 s f t x) = (term82 _115054 _115057 s f x t).
Proof. exact (eq_refl (term94 _115054 _115057 s f t x)). Qed.
Lemma lem5126107 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5126108 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term95 _115054 _115057 s f t x) = (term86 _115054 _115057 s f x t).
Proof. exact (MK_COMB (@lem5126107) (@lem5126106 _115054 _115057 s f x t)). Qed.
Lemma lem5126109 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term95 _115054 _115057 s f t x) = (term87 _115054 _115057 s f x t).
Proof. exact (TRANS (@lem5126108 _115054 _115057 s f x t) (@lem5126098 _115054 _115057 s f x t)). Qed.
Lemma lem5126110 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term96 _115054 _115057 s f t) = (term97 _115054 _115057 s f t).
Proof. exact (fun_ext (fun x : _115054 => @lem5126109 _115054 _115057 s f x t)). Qed.
Lemma lem5126111 {_115054 : Type'} : (@ex _115054) = (@ex _115054).
Proof. exact (eq_refl (@ex _115054)). Qed.
Lemma lem5126112 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term93 _115054 _115057 s f t) = (term98 _115054 _115057 s f t).
Proof. exact (MK_COMB (@lem5126111 _115054) (@lem5126110 _115054 _115057 s f t)). Qed.
Lemma lem5126113 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term92 _115054 _115057 s f t) = (term98 _115054 _115057 s f t).
Proof. exact (TRANS (@lem5126105 _115054 _115057 s f t) (@lem5126112 _115054 _115057 s f t)). Qed.
Lemma lem5126114 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term83 _115054 _115057 s f t) = (term99 _115054 _115057 s f t).
Proof. exact (fun_ext (fun x : _115054 => @lem5126103 _115054 _115057 s f x t)). Qed.
Lemma lem5126115 {_115054 : Type'} : (@all _115054) = (@all _115054).
Proof. exact (eq_refl (@all _115054)). Qed.
Lemma lem5126116 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term27 _115054 _115057 s f t) = (term100 _115054 _115057 s f t).
Proof. exact (MK_COMB (@lem5126115 _115054) (@lem5126114 _115054 _115057 s f t)). Qed.
Lemma lem5126125 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : (term101 _115054 _115057 s g f x) = (term102 _115054 _115057 s g f x).
Proof. exact (@lem17362 (@IN _115054 x s) ((term103 _115054 _115057 g f x) = x)). Qed.
Lemma lem5126130 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : (term80 _115054 _115057 s g f x) = (term104 _115054 _115057 s g f x).
Proof. exact (@lem17265 (@IN _115054 x s) ((term103 _115054 _115057 g f x) = x)). Qed.
Lemma lem5126131 {_115054 : Type'} (P : _115054 -> Prop) : (term90 _115054 P) = (term91 _115054 P).
Proof. exact (@lem18392 _115054 P). Qed.
Lemma lem5126132 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term105 _115054 _115057 s g f) = (term106 _115054 _115057 s g f).
Proof. exact (@lem5126131 _115054 (term81 _115054 _115057 s g f)). Qed.
Lemma lem5126133 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : (term107 _115054 _115057 s g f x) = (term80 _115054 _115057 s g f x).
Proof. exact (eq_refl (term107 _115054 _115057 s g f x)). Qed.
Lemma lem5126134 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5126135 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : (term108 _115054 _115057 s g f x) = (term101 _115054 _115057 s g f x).
Proof. exact (MK_COMB (@lem5126134) (@lem5126133 _115054 _115057 s g f x)). Qed.
Lemma lem5126136 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : (term108 _115054 _115057 s g f x) = (term102 _115054 _115057 s g f x).
Proof. exact (TRANS (@lem5126135 _115054 _115057 s g f x) (@lem5126125 _115054 _115057 s g f x)). Qed.
Lemma lem5126137 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term109 _115054 _115057 s g f) = (term110 _115054 _115057 s g f).
Proof. exact (fun_ext (fun x : _115054 => @lem5126136 _115054 _115057 s g f x)). Qed.
Lemma lem5126138 {_115054 : Type'} : (@ex _115054) = (@ex _115054).
Proof. exact (eq_refl (@ex _115054)). Qed.
Lemma lem5126139 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term106 _115054 _115057 s g f) = (term111 _115054 _115057 s g f).
Proof. exact (MK_COMB (@lem5126138 _115054) (@lem5126137 _115054 _115057 s g f)). Qed.
Lemma lem5126140 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term105 _115054 _115057 s g f) = (term111 _115054 _115057 s g f).
Proof. exact (TRANS (@lem5126132 _115054 _115057 s g f) (@lem5126139 _115054 _115057 s g f)). Qed.
Lemma lem5126141 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term81 _115054 _115057 s g f) = (term112 _115054 _115057 s g f).
Proof. exact (fun_ext (fun x : _115054 => @lem5126130 _115054 _115057 s g f x)). Qed.
Lemma lem5126142 {_115054 : Type'} : (@all _115054) = (@all _115054).
Proof. exact (eq_refl (@all _115054)). Qed.
Lemma lem5126143 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term30 _115054 _115057 s g f) = (term113 _115054 _115057 s g f).
Proof. exact (MK_COMB (@lem5126142 _115054) (@lem5126141 _115054 _115057 s g f)). Qed.
Lemma lem5126144 {_115054 _115057 : Type'} (P : type805 _115054 _115057) : (term114 _115054 _115057 P) = (term115 _115054 _115057 P).
Proof. exact (@lem18394 (_115057 -> _115054) P). Qed.
Lemma lem5126145 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term116 _115054 _115057 s f) = (term117 _115054 _115057 s f).
Proof. exact (@lem5126144 _115054 _115057 (term28 _115054 _115057 s f)). Qed.
Lemma lem5126146 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term29 _115054 _115057 s f g) = (term30 _115054 _115057 s g f).
Proof. exact (eq_refl (term29 _115054 _115057 s f g)). Qed.
Lemma lem5126147 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5126148 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term118 _115054 _115057 s f g) = (term105 _115054 _115057 s g f).
Proof. exact (MK_COMB (@lem5126147) (@lem5126146 _115054 _115057 s g f)). Qed.
Lemma lem5126149 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term118 _115054 _115057 s f g) = (term111 _115054 _115057 s g f).
Proof. exact (TRANS (@lem5126148 _115054 _115057 s g f) (@lem5126140 _115054 _115057 s g f)). Qed.
Lemma lem5126150 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term119 _115054 _115057 s f) = (term120 _115054 _115057 s f).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5126149 _115054 _115057 s g f)). Qed.
Lemma lem5126151 {_115054 _115057 : Type'} : (@all (_115057 -> _115054)) = (@all (_115057 -> _115054)).
Proof. exact (eq_refl (@all (_115057 -> _115054))). Qed.
Lemma lem5126152 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term117 _115054 _115057 s f) = (term121 _115054 _115057 s f).
Proof. exact (MK_COMB (@lem5126151 _115054 _115057) (@lem5126150 _115054 _115057 s f)). Qed.
Lemma lem5126153 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term116 _115054 _115057 s f) = (term121 _115054 _115057 s f).
Proof. exact (TRANS (@lem5126145 _115054 _115057 s f) (@lem5126152 _115054 _115057 s f)). Qed.
Lemma lem5126154 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term28 _115054 _115057 s f) = (term122 _115054 _115057 s f).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5126143 _115054 _115057 s g f)). Qed.
Lemma lem5126155 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5126156 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term14 _115054 _115057 s f) = (term123 _115054 _115057 s f).
Proof. exact (MK_COMB (@lem5126155 _115054 _115057) (@lem5126154 _115054 _115057 s f)). Qed.
Lemma lem5126157 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5126158 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term124 _115054 _115057 s f t) = (term125 _115054 _115057 s f t).
Proof. exact (MK_COMB (@lem5126157) (@lem5126113 _115054 _115057 s f t)). Qed.
Lemma lem5126159 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term126 _115054 _115057 t s f) = (term127 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126158 _115054 _115057 s f t) (@lem5126153 _115054 _115057 s f)). Qed.
Lemma lem5126160 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term128 _115054 _115057 t s f) = (term126 _115054 _115057 t s f).
Proof. exact (@lem17045 (term27 _115054 _115057 s f t) (term14 _115054 _115057 s f)). Qed.
Lemma lem5126161 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term128 _115054 _115057 t s f) = (term127 _115054 _115057 t s f).
Proof. exact (TRANS (@lem5126160 _115054 _115057 t s f) (@lem5126159 _115054 _115057 t s f)). Qed.
Lemma lem5126162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5126163 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term20 _115054 _115057 s f t) = (term129 _115054 _115057 s f t).
Proof. exact (MK_COMB (@lem5126162) (@lem5126116 _115054 _115057 s f t)). Qed.
Lemma lem5126164 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term22 _115054 _115057 t s f) = (term130 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126163 _115054 _115057 s f t) (@lem5126156 _115054 _115057 s f)). Qed.
Lemma lem5126165 {_115054 _115057 : Type'} (P : type572 _115054 _115057) : (term131 _115054 _115057 P) = (term132 _115054 _115057 P).
Proof. exact (@lem18394 (_115054 -> _115057) P). Qed.
Lemma lem5126166 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term133 _115054 _115057 t s) = (term134 _115054 _115057 t s).
Proof. exact (@lem5126165 _115054 _115057 (term69 _115054 _115057 t s)). Qed.
Lemma lem5126167 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term135 _115054 _115057 t s f) = (term22 _115054 _115057 t s f).
Proof. exact (eq_refl (term135 _115054 _115057 t s f)). Qed.
Lemma lem5126168 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5126169 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term136 _115054 _115057 t s f) = (term128 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126168) (@lem5126167 _115054 _115057 t s f)). Qed.
Lemma lem5126170 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term136 _115054 _115057 t s f) = (term127 _115054 _115057 t s f).
Proof. exact (TRANS (@lem5126169 _115054 _115057 t s f) (@lem5126161 _115054 _115057 t s f)). Qed.
Lemma lem5126171 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term137 _115054 _115057 t s) = (term138 _115054 _115057 t s).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5126170 _115054 _115057 t s f)). Qed.
Lemma lem5126172 {_115054 _115057 : Type'} : (@all (_115054 -> _115057)) = (@all (_115054 -> _115057)).
Proof. exact (eq_refl (@all (_115054 -> _115057))). Qed.
Lemma lem5126173 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term134 _115054 _115057 t s) = (term139 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126172 _115054 _115057) (@lem5126171 _115054 _115057 t s)). Qed.
Lemma lem5126174 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term133 _115054 _115057 t s) = (term139 _115054 _115057 t s).
Proof. exact (TRANS (@lem5126166 _115054 _115057 t s) (@lem5126173 _115054 _115057 t s)). Qed.
Lemma lem5126175 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term69 _115054 _115057 t s) = (term140 _115054 _115057 t s).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5126164 _115054 _115057 t s f)). Qed.
Lemma lem5126176 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5126177 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term70 _115054 _115057 t s) = (term141 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126176 _115054 _115057) (@lem5126175 _115054 _115057 t s)). Qed.
Lemma lem5126188 {_115054 _115057 : Type'} (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) (x : _115054) : (term142 _115054 _115057 t g g' x) = (term143 _115054 _115057 t g g' x).
Proof. exact (@lem17045 (term88 _115054 _115057 g' x t) ((term103 _115054 _115057 g g' x) = x)). Qed.
Lemma lem5126193 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (term144 _115054 x s) = (term144 _115054 x s).
Proof. exact (eq_refl (term144 _115054 x s)). Qed.
Lemma lem5126194 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) (x : _115054) : (term145 _115054 _115057 s t g g' x) = (term146 _115054 _115057 s t g g' x).
Proof. exact (MK_COMB (@lem5126193 _115054 x s) (@lem5126188 _115054 _115057 t g g' x)). Qed.
Lemma lem5126195 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) (x : _115054) : (term147 _115054 _115057 s t g g' x) = (term145 _115054 _115057 s t g g' x).
Proof. exact (@lem17362 (@IN _115054 x s) (term148 _115054 _115057 t g g' x)). Qed.
Lemma lem5126196 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) (x : _115054) : (term147 _115054 _115057 s t g g' x) = (term146 _115054 _115057 s t g g' x).
Proof. exact (TRANS (@lem5126195 _115054 _115057 s t g g' x) (@lem5126194 _115054 _115057 s t g g' x)). Qed.
Lemma lem5126201 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) (x : _115054) : (term76 _115054 _115057 s t g g' x) = (term149 _115054 _115057 s t g g' x).
Proof. exact (@lem17265 (@IN _115054 x s) (term148 _115054 _115057 t g g' x)). Qed.
Lemma lem5126202 {_115054 : Type'} (P : _115054 -> Prop) : (term90 _115054 P) = (term91 _115054 P).
Proof. exact (@lem18392 _115054 P). Qed.
Lemma lem5126203 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term150 _115054 _115057 s t g g') = (term151 _115054 _115057 s t g g').
Proof. exact (@lem5126202 _115054 (term77 _115054 _115057 s t g g')). Qed.
Lemma lem5126204 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) (x : _115054) : (term152 _115054 _115057 s t g g' x) = (term76 _115054 _115057 s t g g' x).
Proof. exact (eq_refl (term152 _115054 _115057 s t g g' x)). Qed.
Lemma lem5126205 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5126206 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) (x : _115054) : (term153 _115054 _115057 s t g g' x) = (term147 _115054 _115057 s t g g' x).
Proof. exact (MK_COMB (@lem5126205) (@lem5126204 _115054 _115057 s t g g' x)). Qed.
Lemma lem5126207 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) (x : _115054) : (term153 _115054 _115057 s t g g' x) = (term146 _115054 _115057 s t g g' x).
Proof. exact (TRANS (@lem5126206 _115054 _115057 s t g g' x) (@lem5126196 _115054 _115057 s t g g' x)). Qed.
Lemma lem5126208 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term154 _115054 _115057 s t g g') = (term155 _115054 _115057 s t g g').
Proof. exact (fun_ext (fun x : _115054 => @lem5126207 _115054 _115057 s t g g' x)). Qed.
Lemma lem5126209 {_115054 : Type'} : (@ex _115054) = (@ex _115054).
Proof. exact (eq_refl (@ex _115054)). Qed.
Lemma lem5126210 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term151 _115054 _115057 s t g g') = (term156 _115054 _115057 s t g g').
Proof. exact (MK_COMB (@lem5126209 _115054) (@lem5126208 _115054 _115057 s t g g')). Qed.
Lemma lem5126211 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term150 _115054 _115057 s t g g') = (term156 _115054 _115057 s t g g').
Proof. exact (TRANS (@lem5126203 _115054 _115057 s t g g') (@lem5126210 _115054 _115057 s t g g')). Qed.
Lemma lem5126212 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term77 _115054 _115057 s t g g') = (term157 _115054 _115057 s t g g').
Proof. exact (fun_ext (fun x : _115054 => @lem5126201 _115054 _115057 s t g g' x)). Qed.
Lemma lem5126213 {_115054 : Type'} : (@all _115054) = (@all _115054).
Proof. exact (eq_refl (@all _115054)). Qed.
Lemma lem5126214 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term78 _115054 _115057 s t g g') = (term158 _115054 _115057 s t g g').
Proof. exact (MK_COMB (@lem5126213 _115054) (@lem5126212 _115054 _115057 s t g g')). Qed.
Lemma lem5126215 {_115054 _115057 : Type'} (P : type572 _115054 _115057) : (term131 _115054 _115057 P) = (term132 _115054 _115057 P).
Proof. exact (@lem18394 (_115054 -> _115057) P). Qed.
Lemma lem5126216 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term159 _115054 _115057 s t g) = (term160 _115054 _115057 s t g).
Proof. exact (@lem5126215 _115054 _115057 (term79 _115054 _115057 s t g)). Qed.
Lemma lem5126217 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term161 _115054 _115057 s t g g') = (term78 _115054 _115057 s t g g').
Proof. exact (eq_refl (term161 _115054 _115057 s t g g')). Qed.
Lemma lem5126218 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5126219 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term162 _115054 _115057 s t g g') = (term150 _115054 _115057 s t g g').
Proof. exact (MK_COMB (@lem5126218) (@lem5126217 _115054 _115057 s t g g')). Qed.
Lemma lem5126220 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term162 _115054 _115057 s t g g') = (term156 _115054 _115057 s t g g').
Proof. exact (TRANS (@lem5126219 _115054 _115057 s t g g') (@lem5126211 _115054 _115057 s t g g')). Qed.
Lemma lem5126221 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term163 _115054 _115057 s t g) = (term164 _115054 _115057 s t g).
Proof. exact (fun_ext (fun g' : _115054 -> _115057 => @lem5126220 _115054 _115057 s t g g')). Qed.
Lemma lem5126222 {_115054 _115057 : Type'} : (@all (_115054 -> _115057)) = (@all (_115054 -> _115057)).
Proof. exact (eq_refl (@all (_115054 -> _115057))). Qed.
Lemma lem5126223 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term160 _115054 _115057 s t g) = (term165 _115054 _115057 s t g).
Proof. exact (MK_COMB (@lem5126222 _115054 _115057) (@lem5126221 _115054 _115057 s t g)). Qed.
Lemma lem5126224 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term159 _115054 _115057 s t g) = (term165 _115054 _115057 s t g).
Proof. exact (TRANS (@lem5126216 _115054 _115057 s t g) (@lem5126223 _115054 _115057 s t g)). Qed.
Lemma lem5126225 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term79 _115054 _115057 s t g) = (term166 _115054 _115057 s t g).
Proof. exact (fun_ext (fun g' : _115054 -> _115057 => @lem5126214 _115054 _115057 s t g g')). Qed.
Lemma lem5126226 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5126227 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term46 _115054 _115057 s t g) = (term167 _115054 _115057 s t g).
Proof. exact (MK_COMB (@lem5126226 _115054 _115057) (@lem5126225 _115054 _115057 s t g)). Qed.
Lemma lem5126228 {_115054 _115057 : Type'} (P : type805 _115054 _115057) : (term114 _115054 _115057 P) = (term115 _115054 _115057 P).
Proof. exact (@lem18394 (_115057 -> _115054) P). Qed.
Lemma lem5126229 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term168 _115054 _115057 s t) = (term169 _115054 _115057 s t).
Proof. exact (@lem5126228 _115054 _115057 (term48 _115054 _115057 s t)). Qed.
Lemma lem5126230 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term170 _115054 _115057 s t g) = (term46 _115054 _115057 s t g).
Proof. exact (eq_refl (term170 _115054 _115057 s t g)). Qed.
Lemma lem5126231 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5126232 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term171 _115054 _115057 s t g) = (term159 _115054 _115057 s t g).
Proof. exact (MK_COMB (@lem5126231) (@lem5126230 _115054 _115057 s t g)). Qed.
Lemma lem5126233 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term171 _115054 _115057 s t g) = (term165 _115054 _115057 s t g).
Proof. exact (TRANS (@lem5126232 _115054 _115057 s t g) (@lem5126224 _115054 _115057 s t g)). Qed.
Lemma lem5126234 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term172 _115054 _115057 s t) = (term173 _115054 _115057 s t).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5126233 _115054 _115057 s t g)). Qed.
Lemma lem5126235 {_115054 _115057 : Type'} : (@all (_115057 -> _115054)) = (@all (_115057 -> _115054)).
Proof. exact (eq_refl (@all (_115057 -> _115054))). Qed.
Lemma lem5126236 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term169 _115054 _115057 s t) = (term174 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126235 _115054 _115057) (@lem5126234 _115054 _115057 s t)). Qed.
Lemma lem5126237 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term168 _115054 _115057 s t) = (term174 _115054 _115057 s t).
Proof. exact (TRANS (@lem5126229 _115054 _115057 s t) (@lem5126236 _115054 _115057 s t)). Qed.
Lemma lem5126238 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term48 _115054 _115057 s t) = (term175 _115054 _115057 s t).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5126227 _115054 _115057 s t g)). Qed.
Lemma lem5126239 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5126240 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term50 _115054 _115057 s t) = (term176 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126239 _115054 _115057) (@lem5126238 _115054 _115057 s t)). Qed.
Lemma lem5126241 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5126242 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term177 _115054 _115057 t s) = (term178 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126241) (@lem5126174 _115054 _115057 t s)). Qed.
Lemma lem5126243 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term179 _115054 _115057 s t) = (term180 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126242 _115054 _115057 t s) (@lem5126240 _115054 _115057 s t)). Qed.
Lemma lem5126244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5126245 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term181 _115054 _115057 t s) = (term182 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126244) (@lem5126177 _115054 _115057 t s)). Qed.
Lemma lem5126246 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term183 _115054 _115057 s t) = (term184 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126245 _115054 _115057 t s) (@lem5126237 _115054 _115057 s t)). Qed.
Lemma lem5126247 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5126248 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term185 _115054 _115057 s t) = (term186 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126247) (@lem5126246 _115054 _115057 s t)). Qed.
Lemma lem5126249 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term187 _115054 _115057 s t) = (term188 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126248 _115054 _115057 s t) (@lem5126243 _115054 _115057 s t)). Qed.
Lemma lem5126250 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term85 _115054 _115057 s t) = (term187 _115054 _115057 s t).
Proof. exact (@lem17646 (term70 _115054 _115057 t s) (term50 _115054 _115057 s t)). Qed.
Lemma lem5126251 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term85 _115054 _115057 s t) = (term188 _115054 _115057 s t).
Proof. exact (TRANS (@lem5126250 _115054 _115057 s t) (@lem5126249 _115054 _115057 s t)). Qed.
Lemma lem5126662 {A : Type'} (P : Prop) (Q : A -> Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5126663 {_115054 _115057 : Type'} (P : Prop) (Q : type805 _115054 _115057) : (term23 _115054 _115057 P Q) = (term24 _115054 _115057 P Q).
Proof. exact (@lem5126662 (_115057 -> _115054) P Q). Qed.
Lemma lem5126664 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term189 _115054 _115057 t s f) = (term190 _115054 _115057 t s f).
Proof. exact (@lem5126663 _115054 _115057 (term100 _115054 _115057 s f t) (term122 _115054 _115057 s f)). Qed.
Lemma lem5126665 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term191 _115054 _115057 s f g) = (term113 _115054 _115057 s g f).
Proof. exact (eq_refl (term191 _115054 _115057 s f g)). Qed.
Lemma lem5126666 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term192 _115054 _115057 s f) = (term122 _115054 _115057 s f).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5126665 _115054 _115057 s g f)). Qed.
Lemma lem5126667 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5126668 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term193 _115054 _115057 s f) = (term123 _115054 _115057 s f).
Proof. exact (MK_COMB (@lem5126667 _115054 _115057) (@lem5126666 _115054 _115057 s f)). Qed.
Lemma lem5126669 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term129 _115054 _115057 s f t) = (term129 _115054 _115057 s f t).
Proof. exact (eq_refl (term129 _115054 _115057 s f t)). Qed.
Lemma lem5126670 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term189 _115054 _115057 t s f) = (term130 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126669 _115054 _115057 s f t) (@lem5126668 _115054 _115057 s f)). Qed.
Lemma lem5126671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5126672 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term194 _115054 _115057 t s f) = (term195 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126671) (@lem5126670 _115054 _115057 t s f)). Qed.
Lemma lem5126673 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term191 _115054 _115057 s f g) = (term113 _115054 _115057 s g f).
Proof. exact (eq_refl (term191 _115054 _115057 s f g)). Qed.
Lemma lem5126674 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term129 _115054 _115057 s f t) = (term129 _115054 _115057 s f t).
Proof. exact (eq_refl (term129 _115054 _115057 s f t)). Qed.
Lemma lem5126675 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term196 _115054 _115057 t s f g) = (term197 _115054 _115057 t s g f).
Proof. exact (MK_COMB (@lem5126674 _115054 _115057 s f t) (@lem5126673 _115054 _115057 s g f)). Qed.
Lemma lem5126676 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term198 _115054 _115057 t s f) = (term199 _115054 _115057 t s f).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5126675 _115054 _115057 t s g f)). Qed.
Lemma lem5126677 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5126678 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term190 _115054 _115057 t s f) = (term200 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126677 _115054 _115057) (@lem5126676 _115054 _115057 t s f)). Qed.
Lemma lem5126679 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : ((term189 _115054 _115057 t s f) = (term190 _115054 _115057 t s f)) = ((term130 _115054 _115057 t s f) = (term200 _115054 _115057 t s f)).
Proof. exact (MK_COMB (@lem5126672 _115054 _115057 t s f) (@lem5126678 _115054 _115057 t s f)). Qed.
Lemma lem5126680 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term130 _115054 _115057 t s f) = (term200 _115054 _115057 t s f).
Proof. exact (EQ_MP (@lem5126679 _115054 _115057 t s f) (@lem5126664 _115054 _115057 t s f)). Qed.
Lemma lem5126681 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term140 _115054 _115057 t s) = (term201 _115054 _115057 t s).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5126680 _115054 _115057 t s f)). Qed.
Lemma lem5126682 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5126683 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term141 _115054 _115057 t s) = (term202 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126682 _115054 _115057) (@lem5126681 _115054 _115057 t s)). Qed.
Lemma lem5126684 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5126685 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term182 _115054 _115057 t s) = (term203 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126684) (@lem5126683 _115054 _115057 t s)). Qed.
Lemma lem5126687 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5126688 {_115054 _115057 : Type'} (P : type551 _115054 _115057) : (term206 _115054 _115057 P) = (term207 _115054 _115057 P).
Proof. exact (@lem5126687 (_115054 -> _115057) _115054 P). Qed.
Lemma lem5126689 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term208 _115054 _115057 s t g) = (term209 _115054 _115057 s t g).
Proof. exact (@lem5126688 _115054 _115057 (term210 _115054 _115057 s t g)). Qed.
Lemma lem5126690 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term211 _115054 _115057 s t g g') = (term155 _115054 _115057 s t g g').
Proof. exact (eq_refl (term211 _115054 _115057 s t g g')). Qed.
Lemma lem5126691 {_115054 : Type'} (x : _115054) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5126692 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) (x : _115054) : (term212 _115054 _115057 s t g g' x) = (term213 _115054 _115057 s t g g' x).
Proof. exact (MK_COMB (@lem5126690 _115054 _115057 s t g g') (@lem5126691 _115054 x)). Qed.
Lemma lem5126693 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) (x : _115054) : (term213 _115054 _115057 s t g g' x) = (term146 _115054 _115057 s t g g' x).
Proof. exact (eq_refl (term213 _115054 _115057 s t g g' x)). Qed.
Lemma lem5126694 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) (x : _115054) : (term212 _115054 _115057 s t g g' x) = (term146 _115054 _115057 s t g g' x).
Proof. exact (TRANS (@lem5126692 _115054 _115057 s t g g' x) (@lem5126693 _115054 _115057 s t g g' x)). Qed.
Lemma lem5126695 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term214 _115054 _115057 s t g g') = (term155 _115054 _115057 s t g g').
Proof. exact (fun_ext (fun x : _115054 => @lem5126694 _115054 _115057 s t g g' x)). Qed.
Lemma lem5126696 {_115054 : Type'} : (@ex _115054) = (@ex _115054).
Proof. exact (eq_refl (@ex _115054)). Qed.
Lemma lem5126697 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term215 _115054 _115057 s t g g') = (term156 _115054 _115057 s t g g').
Proof. exact (MK_COMB (@lem5126696 _115054) (@lem5126695 _115054 _115057 s t g g')). Qed.
Lemma lem5126698 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term216 _115054 _115057 s t g) = (term164 _115054 _115057 s t g).
Proof. exact (fun_ext (fun g' : _115054 -> _115057 => @lem5126697 _115054 _115057 s t g g')). Qed.
Lemma lem5126699 {_115054 _115057 : Type'} : (@all (_115054 -> _115057)) = (@all (_115054 -> _115057)).
Proof. exact (eq_refl (@all (_115054 -> _115057))). Qed.
Lemma lem5126700 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term208 _115054 _115057 s t g) = (term165 _115054 _115057 s t g).
Proof. exact (MK_COMB (@lem5126699 _115054 _115057) (@lem5126698 _115054 _115057 s t g)). Qed.
Lemma lem5126701 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5126702 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term217 _115054 _115057 s t g) = (term218 _115054 _115057 s t g).
Proof. exact (MK_COMB (@lem5126701) (@lem5126700 _115054 _115057 s t g)). Qed.
Lemma lem5126703 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term211 _115054 _115057 s t g g') = (term155 _115054 _115057 s t g g').
Proof. exact (eq_refl (term211 _115054 _115057 s t g g')). Qed.
Lemma lem5126704 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (g : _115054 -> _115057) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem5126705 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (x : type569 _115054 _115057) (g' : _115054 -> _115057) : (term219 _115054 _115057 s t g x g') = (term220 _115054 _115057 s t g x g').
Proof. exact (MK_COMB (@lem5126703 _115054 _115057 s t g g') (@lem5126704 _115054 _115057 x g')). Qed.
Lemma lem5126706 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (x : type569 _115054 _115057) (g' : _115054 -> _115057) : (term220 _115054 _115057 s t g x g') = (term221 _115054 _115057 s t g x g').
Proof. exact (eq_refl (term220 _115054 _115057 s t g x g')). Qed.
Lemma lem5126707 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (x : type569 _115054 _115057) (g' : _115054 -> _115057) : (term219 _115054 _115057 s t g x g') = (term221 _115054 _115057 s t g x g').
Proof. exact (TRANS (@lem5126705 _115054 _115057 s t g x g') (@lem5126706 _115054 _115057 s t g x g')). Qed.
Lemma lem5126708 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (x : type569 _115054 _115057) : (term222 _115054 _115057 s t g x) = (term223 _115054 _115057 s t g x).
Proof. exact (fun_ext (fun g' : _115054 -> _115057 => @lem5126707 _115054 _115057 s t g x g')). Qed.
Lemma lem5126709 {_115054 _115057 : Type'} : (@all (_115054 -> _115057)) = (@all (_115054 -> _115057)).
Proof. exact (eq_refl (@all (_115054 -> _115057))). Qed.
Lemma lem5126710 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (x : type569 _115054 _115057) : (term224 _115054 _115057 s t g x) = (term225 _115054 _115057 s t g x).
Proof. exact (MK_COMB (@lem5126709 _115054 _115057) (@lem5126708 _115054 _115057 s t g x)). Qed.
Lemma lem5126711 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term226 _115054 _115057 s t g) = (term227 _115054 _115057 s t g).
Proof. exact (fun_ext (fun x : type569 _115054 _115057 => @lem5126710 _115054 _115057 s t g x)). Qed.
Lemma lem5126712 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> _115054)) = (@ex ((_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> _115054))). Qed.
Lemma lem5126713 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term209 _115054 _115057 s t g) = (term228 _115054 _115057 s t g).
Proof. exact (MK_COMB (@lem5126712 _115054 _115057) (@lem5126711 _115054 _115057 s t g)). Qed.
Lemma lem5126714 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : ((term208 _115054 _115057 s t g) = (term209 _115054 _115057 s t g)) = ((term165 _115054 _115057 s t g) = (term228 _115054 _115057 s t g)).
Proof. exact (MK_COMB (@lem5126702 _115054 _115057 s t g) (@lem5126713 _115054 _115057 s t g)). Qed.
Lemma lem5126715 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term165 _115054 _115057 s t g) = (term228 _115054 _115057 s t g).
Proof. exact (EQ_MP (@lem5126714 _115054 _115057 s t g) (@lem5126689 _115054 _115057 s t g)). Qed.
Lemma lem5126716 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term173 _115054 _115057 s t) = (term229 _115054 _115057 s t).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5126715 _115054 _115057 s t g)). Qed.
Lemma lem5126717 {_115054 _115057 : Type'} : (@all (_115057 -> _115054)) = (@all (_115057 -> _115054)).
Proof. exact (eq_refl (@all (_115057 -> _115054))). Qed.
Lemma lem5126718 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term174 _115054 _115057 s t) = (term230 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126717 _115054 _115057) (@lem5126716 _115054 _115057 s t)). Qed.
Lemma lem5126720 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5126721 {_115054 _115057 : Type'} (P : type769 _115054 _115057) : (term231 _115054 _115057 P) = (term232 _115054 _115057 P).
Proof. exact (@lem5126720 (_115057 -> _115054) (type569 _115054 _115057) P). Qed.
Lemma lem5126722 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term233 _115054 _115057 s t) = (term234 _115054 _115057 s t).
Proof. exact (@lem5126721 _115054 _115057 (term235 _115054 _115057 s t)). Qed.
Lemma lem5126723 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term236 _115054 _115057 s t g) = (term227 _115054 _115057 s t g).
Proof. exact (eq_refl (term236 _115054 _115057 s t g)). Qed.
Lemma lem5126724 {_115054 _115057 : Type'} (x : type569 _115054 _115057) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5126725 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (x : type569 _115054 _115057) : (term237 _115054 _115057 s t g x) = (term238 _115054 _115057 s t g x).
Proof. exact (MK_COMB (@lem5126723 _115054 _115057 s t g) (@lem5126724 _115054 _115057 x)). Qed.
Lemma lem5126726 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (x : type569 _115054 _115057) : (term238 _115054 _115057 s t g x) = (term225 _115054 _115057 s t g x).
Proof. exact (eq_refl (term238 _115054 _115057 s t g x)). Qed.
Lemma lem5126727 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (x : type569 _115054 _115057) : (term237 _115054 _115057 s t g x) = (term225 _115054 _115057 s t g x).
Proof. exact (TRANS (@lem5126725 _115054 _115057 s t g x) (@lem5126726 _115054 _115057 s t g x)). Qed.
Lemma lem5126728 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term239 _115054 _115057 s t g) = (term227 _115054 _115057 s t g).
Proof. exact (fun_ext (fun x : type569 _115054 _115057 => @lem5126727 _115054 _115057 s t g x)). Qed.
Lemma lem5126729 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> _115054)) = (@ex ((_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> _115054))). Qed.
Lemma lem5126730 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term240 _115054 _115057 s t g) = (term228 _115054 _115057 s t g).
Proof. exact (MK_COMB (@lem5126729 _115054 _115057) (@lem5126728 _115054 _115057 s t g)). Qed.
Lemma lem5126731 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term241 _115054 _115057 s t) = (term229 _115054 _115057 s t).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5126730 _115054 _115057 s t g)). Qed.
Lemma lem5126732 {_115054 _115057 : Type'} : (@all (_115057 -> _115054)) = (@all (_115057 -> _115054)).
Proof. exact (eq_refl (@all (_115057 -> _115054))). Qed.
Lemma lem5126733 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term233 _115054 _115057 s t) = (term230 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126732 _115054 _115057) (@lem5126731 _115054 _115057 s t)). Qed.
Lemma lem5126734 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5126735 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term242 _115054 _115057 s t) = (term243 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126734) (@lem5126733 _115054 _115057 s t)). Qed.
Lemma lem5126736 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term236 _115054 _115057 s t g) = (term227 _115054 _115057 s t g).
Proof. exact (eq_refl (term236 _115054 _115057 s t g)). Qed.
Lemma lem5126737 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem5126738 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (g : _115057 -> _115054) : (term244 _115054 _115057 s t x g) = (term245 _115054 _115057 s t x g).
Proof. exact (MK_COMB (@lem5126736 _115054 _115057 s t g) (@lem5126737 _115054 _115057 x g)). Qed.
Lemma lem5126739 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (g : _115057 -> _115054) : (term245 _115054 _115057 s t x g) = (term246 _115054 _115057 s t x g).
Proof. exact (eq_refl (term245 _115054 _115057 s t x g)). Qed.
Lemma lem5126740 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (g : _115057 -> _115054) : (term244 _115054 _115057 s t x g) = (term246 _115054 _115057 s t x g).
Proof. exact (TRANS (@lem5126738 _115054 _115057 s t x g) (@lem5126739 _115054 _115057 s t x g)). Qed.
Lemma lem5126741 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term247 _115054 _115057 s t x) = (term248 _115054 _115057 s t x).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5126740 _115054 _115057 s t x g)). Qed.
Lemma lem5126742 {_115054 _115057 : Type'} : (@all (_115057 -> _115054)) = (@all (_115057 -> _115054)).
Proof. exact (eq_refl (@all (_115057 -> _115054))). Qed.
Lemma lem5126743 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term249 _115054 _115057 s t x) = (term250 _115054 _115057 s t x).
Proof. exact (MK_COMB (@lem5126742 _115054 _115057) (@lem5126741 _115054 _115057 s t x)). Qed.
Lemma lem5126744 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term251 _115054 _115057 s t) = (term252 _115054 _115057 s t).
Proof. exact (fun_ext (fun x : type779 _115054 _115057 => @lem5126743 _115054 _115057 s t x)). Qed.
Lemma lem5126745 {_115054 _115057 : Type'} : (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054)) = (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054))). Qed.
Lemma lem5126746 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term234 _115054 _115057 s t) = (term253 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126745 _115054 _115057) (@lem5126744 _115054 _115057 s t)). Qed.
Lemma lem5126747 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term233 _115054 _115057 s t) = (term234 _115054 _115057 s t)) = ((term230 _115054 _115057 s t) = (term253 _115054 _115057 s t)).
Proof. exact (MK_COMB (@lem5126735 _115054 _115057 s t) (@lem5126746 _115054 _115057 s t)). Qed.
Lemma lem5126748 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term230 _115054 _115057 s t) = (term253 _115054 _115057 s t).
Proof. exact (EQ_MP (@lem5126747 _115054 _115057 s t) (@lem5126722 _115054 _115057 s t)). Qed.
Lemma lem5126749 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term174 _115054 _115057 s t) = (term253 _115054 _115057 s t).
Proof. exact (TRANS (@lem5126718 _115054 _115057 s t) (@lem5126748 _115054 _115057 s t)). Qed.
Lemma lem5126750 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term184 _115054 _115057 s t) = (term254 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126685 _115054 _115057 t s) (@lem5126749 _115054 _115057 s t)). Qed.
Lemma lem5126752 {A : Type'} (P : A -> Prop) (Q : Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5126753 {_115054 _115057 : Type'} (P : type572 _115054 _115057) (Q : Prop) : (term257 _115054 _115057 P Q) = (term258 _115054 _115057 P Q).
Proof. exact (@lem5126752 (_115054 -> _115057) P Q). Qed.
Lemma lem5126754 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term259 _115054 _115057 s t) = (term260 _115054 _115057 s t).
Proof. exact (@lem5126753 _115054 _115057 (term201 _115054 _115057 t s) (term253 _115054 _115057 s t)). Qed.
Lemma lem5126755 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term261 _115054 _115057 t s f) = (term200 _115054 _115057 t s f).
Proof. exact (eq_refl (term261 _115054 _115057 t s f)). Qed.
Lemma lem5126756 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term262 _115054 _115057 t s) = (term201 _115054 _115057 t s).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5126755 _115054 _115057 t s f)). Qed.
Lemma lem5126757 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5126758 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term263 _115054 _115057 t s) = (term202 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126757 _115054 _115057) (@lem5126756 _115054 _115057 t s)). Qed.
Lemma lem5126759 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5126760 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term264 _115054 _115057 t s) = (term203 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126759) (@lem5126758 _115054 _115057 t s)). Qed.
Lemma lem5126761 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term253 _115054 _115057 s t) = (term253 _115054 _115057 s t).
Proof. exact (eq_refl (term253 _115054 _115057 s t)). Qed.
Lemma lem5126762 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term259 _115054 _115057 s t) = (term254 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126760 _115054 _115057 t s) (@lem5126761 _115054 _115057 s t)). Qed.
Lemma lem5126763 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5126764 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term265 _115054 _115057 s t) = (term266 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126763) (@lem5126762 _115054 _115057 s t)). Qed.
Lemma lem5126765 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term261 _115054 _115057 t s f) = (term200 _115054 _115057 t s f).
Proof. exact (eq_refl (term261 _115054 _115057 t s f)). Qed.
Lemma lem5126766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5126767 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term267 _115054 _115057 t s f) = (term268 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126766) (@lem5126765 _115054 _115057 t s f)). Qed.
Lemma lem5126768 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term253 _115054 _115057 s t) = (term253 _115054 _115057 s t).
Proof. exact (eq_refl (term253 _115054 _115057 s t)). Qed.
Lemma lem5126769 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term269 _115054 _115057 f s t) = (term270 _115054 _115057 f s t).
Proof. exact (MK_COMB (@lem5126767 _115054 _115057 t s f) (@lem5126768 _115054 _115057 s t)). Qed.
Lemma lem5126770 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term271 _115054 _115057 s t) = (term272 _115054 _115057 s t).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5126769 _115054 _115057 f s t)). Qed.
Lemma lem5126771 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5126772 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term260 _115054 _115057 s t) = (term273 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126771 _115054 _115057) (@lem5126770 _115054 _115057 s t)). Qed.
Lemma lem5126773 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term259 _115054 _115057 s t) = (term260 _115054 _115057 s t)) = ((term254 _115054 _115057 s t) = (term273 _115054 _115057 s t)).
Proof. exact (MK_COMB (@lem5126764 _115054 _115057 s t) (@lem5126772 _115054 _115057 s t)). Qed.
Lemma lem5126774 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term254 _115054 _115057 s t) = (term273 _115054 _115057 s t).
Proof. exact (EQ_MP (@lem5126773 _115054 _115057 s t) (@lem5126754 _115054 _115057 s t)). Qed.
Lemma lem5126776 {A : Type'} (P : A -> Prop) (Q : Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5126777 {_115054 _115057 : Type'} (P : type805 _115054 _115057) (Q : Prop) : (term274 _115054 _115057 P Q) = (term275 _115054 _115057 P Q).
Proof. exact (@lem5126776 (_115057 -> _115054) P Q). Qed.
Lemma lem5126778 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term276 _115054 _115057 f s t) = (term277 _115054 _115057 f s t).
Proof. exact (@lem5126777 _115054 _115057 (term199 _115054 _115057 t s f) (term253 _115054 _115057 s t)). Qed.
Lemma lem5126779 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term278 _115054 _115057 t s f g) = (term197 _115054 _115057 t s g f).
Proof. exact (eq_refl (term278 _115054 _115057 t s f g)). Qed.
Lemma lem5126780 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term279 _115054 _115057 t s f) = (term199 _115054 _115057 t s f).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5126779 _115054 _115057 t s g f)). Qed.
Lemma lem5126781 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5126782 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term280 _115054 _115057 t s f) = (term200 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126781 _115054 _115057) (@lem5126780 _115054 _115057 t s f)). Qed.
Lemma lem5126783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5126784 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term281 _115054 _115057 t s f) = (term268 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126783) (@lem5126782 _115054 _115057 t s f)). Qed.
Lemma lem5126785 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term253 _115054 _115057 s t) = (term253 _115054 _115057 s t).
Proof. exact (eq_refl (term253 _115054 _115057 s t)). Qed.
Lemma lem5126786 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term276 _115054 _115057 f s t) = (term270 _115054 _115057 f s t).
Proof. exact (MK_COMB (@lem5126784 _115054 _115057 t s f) (@lem5126785 _115054 _115057 s t)). Qed.
Lemma lem5126787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5126788 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term282 _115054 _115057 f s t) = (term283 _115054 _115057 f s t).
Proof. exact (MK_COMB (@lem5126787) (@lem5126786 _115054 _115057 f s t)). Qed.
Lemma lem5126789 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term278 _115054 _115057 t s f g) = (term197 _115054 _115057 t s g f).
Proof. exact (eq_refl (term278 _115054 _115057 t s f g)). Qed.
Lemma lem5126790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5126791 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term284 _115054 _115057 t s f g) = (term285 _115054 _115057 t s g f).
Proof. exact (MK_COMB (@lem5126790) (@lem5126789 _115054 _115057 t s g f)). Qed.
Lemma lem5126792 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term253 _115054 _115057 s t) = (term253 _115054 _115057 s t).
Proof. exact (eq_refl (term253 _115054 _115057 s t)). Qed.
Lemma lem5126793 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term286 _115054 _115057 f g s t) = (term287 _115054 _115057 g f s t).
Proof. exact (MK_COMB (@lem5126791 _115054 _115057 t s g f) (@lem5126792 _115054 _115057 s t)). Qed.
Lemma lem5126794 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term288 _115054 _115057 f s t) = (term289 _115054 _115057 f s t).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5126793 _115054 _115057 g f s t)). Qed.
Lemma lem5126795 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5126796 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term277 _115054 _115057 f s t) = (term290 _115054 _115057 f s t).
Proof. exact (MK_COMB (@lem5126795 _115054 _115057) (@lem5126794 _115054 _115057 f s t)). Qed.
Lemma lem5126797 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term276 _115054 _115057 f s t) = (term277 _115054 _115057 f s t)) = ((term270 _115054 _115057 f s t) = (term290 _115054 _115057 f s t)).
Proof. exact (MK_COMB (@lem5126788 _115054 _115057 f s t) (@lem5126796 _115054 _115057 f s t)). Qed.
Lemma lem5126798 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term270 _115054 _115057 f s t) = (term290 _115054 _115057 f s t).
Proof. exact (EQ_MP (@lem5126797 _115054 _115057 f s t) (@lem5126778 _115054 _115057 f s t)). Qed.
Lemma lem5126800 {A : Type'} (P : Prop) (Q : A -> Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5126801 {_115054 _115057 : Type'} (P : Prop) (Q : type194 _115054 _115057) : (term291 _115054 _115057 P Q) = (term292 _115054 _115057 P Q).
Proof. exact (@lem5126800 (type779 _115054 _115057) P Q). Qed.
Lemma lem5126802 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term293 _115054 _115057 g f s t) = (term294 _115054 _115057 g f s t).
Proof. exact (@lem5126801 _115054 _115057 (term197 _115054 _115057 t s g f) (term252 _115054 _115057 s t)). Qed.
Lemma lem5126803 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term295 _115054 _115057 s t x) = (term250 _115054 _115057 s t x).
Proof. exact (eq_refl (term295 _115054 _115057 s t x)). Qed.
Lemma lem5126804 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term296 _115054 _115057 s t) = (term252 _115054 _115057 s t).
Proof. exact (fun_ext (fun x : type779 _115054 _115057 => @lem5126803 _115054 _115057 s t x)). Qed.
Lemma lem5126805 {_115054 _115057 : Type'} : (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054)) = (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054))). Qed.
Lemma lem5126806 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term297 _115054 _115057 s t) = (term253 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126805 _115054 _115057) (@lem5126804 _115054 _115057 s t)). Qed.
Lemma lem5126807 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term285 _115054 _115057 t s g f) = (term285 _115054 _115057 t s g f).
Proof. exact (eq_refl (term285 _115054 _115057 t s g f)). Qed.
Lemma lem5126808 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term293 _115054 _115057 g f s t) = (term287 _115054 _115057 g f s t).
Proof. exact (MK_COMB (@lem5126807 _115054 _115057 t s g f) (@lem5126806 _115054 _115057 s t)). Qed.
Lemma lem5126809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5126810 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term298 _115054 _115057 g f s t) = (term299 _115054 _115057 g f s t).
Proof. exact (MK_COMB (@lem5126809) (@lem5126808 _115054 _115057 g f s t)). Qed.
Lemma lem5126811 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term295 _115054 _115057 s t x) = (term250 _115054 _115057 s t x).
Proof. exact (eq_refl (term295 _115054 _115057 s t x)). Qed.
Lemma lem5126812 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term285 _115054 _115057 t s g f) = (term285 _115054 _115057 t s g f).
Proof. exact (eq_refl (term285 _115054 _115057 t s g f)). Qed.
Lemma lem5126813 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term300 _115054 _115057 g f s t x) = (term301 _115054 _115057 g f s t x).
Proof. exact (MK_COMB (@lem5126812 _115054 _115057 t s g f) (@lem5126811 _115054 _115057 s t x)). Qed.
Lemma lem5126814 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term302 _115054 _115057 g f s t) = (term303 _115054 _115057 g f s t).
Proof. exact (fun_ext (fun x : type779 _115054 _115057 => @lem5126813 _115054 _115057 g f s t x)). Qed.
Lemma lem5126815 {_115054 _115057 : Type'} : (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054)) = (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054))). Qed.
Lemma lem5126816 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term294 _115054 _115057 g f s t) = (term304 _115054 _115057 g f s t).
Proof. exact (MK_COMB (@lem5126815 _115054 _115057) (@lem5126814 _115054 _115057 g f s t)). Qed.
Lemma lem5126817 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term293 _115054 _115057 g f s t) = (term294 _115054 _115057 g f s t)) = ((term287 _115054 _115057 g f s t) = (term304 _115054 _115057 g f s t)).
Proof. exact (MK_COMB (@lem5126810 _115054 _115057 g f s t) (@lem5126816 _115054 _115057 g f s t)). Qed.
Lemma lem5126818 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term287 _115054 _115057 g f s t) = (term304 _115054 _115057 g f s t).
Proof. exact (EQ_MP (@lem5126817 _115054 _115057 g f s t) (@lem5126802 _115054 _115057 g f s t)). Qed.
Lemma lem5126819 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term289 _115054 _115057 f s t) = (term305 _115054 _115057 f s t).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5126818 _115054 _115057 g f s t)). Qed.
Lemma lem5126820 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5126821 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term290 _115054 _115057 f s t) = (term306 _115054 _115057 f s t).
Proof. exact (MK_COMB (@lem5126820 _115054 _115057) (@lem5126819 _115054 _115057 f s t)). Qed.
Lemma lem5126822 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term270 _115054 _115057 f s t) = (term306 _115054 _115057 f s t).
Proof. exact (TRANS (@lem5126798 _115054 _115057 f s t) (@lem5126821 _115054 _115057 f s t)). Qed.
Lemma lem5126823 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term272 _115054 _115057 s t) = (term307 _115054 _115057 s t).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5126822 _115054 _115057 f s t)). Qed.
Lemma lem5126824 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5126825 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term273 _115054 _115057 s t) = (term308 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126824 _115054 _115057) (@lem5126823 _115054 _115057 s t)). Qed.
Lemma lem5126826 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term254 _115054 _115057 s t) = (term308 _115054 _115057 s t).
Proof. exact (TRANS (@lem5126774 _115054 _115057 s t) (@lem5126825 _115054 _115057 s t)). Qed.
Lemma lem5126827 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term184 _115054 _115057 s t) = (term308 _115054 _115057 s t).
Proof. exact (TRANS (@lem5126750 _115054 _115057 s t) (@lem5126826 _115054 _115057 s t)). Qed.
Lemma lem5126828 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5126829 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term186 _115054 _115057 s t) = (term309 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126828) (@lem5126827 _115054 _115057 s t)). Qed.
Lemma lem5126831 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5126832 {_115054 _115057 : Type'} (P : type795 _115054 _115057) : (term310 _115054 _115057 P) = (term311 _115054 _115057 P).
Proof. exact (@lem5126831 (_115057 -> _115054) _115054 P). Qed.
Lemma lem5126833 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term312 _115054 _115057 s f) = (term313 _115054 _115057 s f).
Proof. exact (@lem5126832 _115054 _115057 (term314 _115054 _115057 s f)). Qed.
Lemma lem5126834 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term315 _115054 _115057 s f g) = (term110 _115054 _115057 s g f).
Proof. exact (eq_refl (term315 _115054 _115057 s f g)). Qed.
Lemma lem5126835 {_115054 : Type'} (x : _115054) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5126836 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : (term316 _115054 _115057 s f g x) = (term317 _115054 _115057 s g f x).
Proof. exact (MK_COMB (@lem5126834 _115054 _115057 s g f) (@lem5126835 _115054 x)). Qed.
Lemma lem5126837 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : (term317 _115054 _115057 s g f x) = (term102 _115054 _115057 s g f x).
Proof. exact (eq_refl (term317 _115054 _115057 s g f x)). Qed.
Lemma lem5126838 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : (term316 _115054 _115057 s f g x) = (term102 _115054 _115057 s g f x).
Proof. exact (TRANS (@lem5126836 _115054 _115057 s g f x) (@lem5126837 _115054 _115057 s g f x)). Qed.
Lemma lem5126839 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term318 _115054 _115057 s f g) = (term110 _115054 _115057 s g f).
Proof. exact (fun_ext (fun x : _115054 => @lem5126838 _115054 _115057 s g f x)). Qed.
Lemma lem5126840 {_115054 : Type'} : (@ex _115054) = (@ex _115054).
Proof. exact (eq_refl (@ex _115054)). Qed.
Lemma lem5126841 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term319 _115054 _115057 s f g) = (term111 _115054 _115057 s g f).
Proof. exact (MK_COMB (@lem5126840 _115054) (@lem5126839 _115054 _115057 s g f)). Qed.
Lemma lem5126842 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term320 _115054 _115057 s f) = (term120 _115054 _115057 s f).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5126841 _115054 _115057 s g f)). Qed.
Lemma lem5126843 {_115054 _115057 : Type'} : (@all (_115057 -> _115054)) = (@all (_115057 -> _115054)).
Proof. exact (eq_refl (@all (_115057 -> _115054))). Qed.
Lemma lem5126844 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term312 _115054 _115057 s f) = (term121 _115054 _115057 s f).
Proof. exact (MK_COMB (@lem5126843 _115054 _115057) (@lem5126842 _115054 _115057 s f)). Qed.
Lemma lem5126845 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5126846 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term321 _115054 _115057 s f) = (term322 _115054 _115057 s f).
Proof. exact (MK_COMB (@lem5126845) (@lem5126844 _115054 _115057 s f)). Qed.
Lemma lem5126847 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term315 _115054 _115057 s f g) = (term110 _115054 _115057 s g f).
Proof. exact (eq_refl (term315 _115054 _115057 s f g)). Qed.
Lemma lem5126848 {_115054 _115057 : Type'} (x : type802 _115054 _115057) (g : _115057 -> _115054) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem5126849 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : type802 _115054 _115057) (g : _115057 -> _115054) : (term323 _115054 _115057 s f x g) = (term324 _115054 _115057 s f x g).
Proof. exact (MK_COMB (@lem5126847 _115054 _115057 s g f) (@lem5126848 _115054 _115057 x g)). Qed.
Lemma lem5126850 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : type802 _115054 _115057) (g : _115057 -> _115054) : (term324 _115054 _115057 s f x g) = (term325 _115054 _115057 s f x g).
Proof. exact (eq_refl (term324 _115054 _115057 s f x g)). Qed.
Lemma lem5126851 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : type802 _115054 _115057) (g : _115057 -> _115054) : (term323 _115054 _115057 s f x g) = (term325 _115054 _115057 s f x g).
Proof. exact (TRANS (@lem5126849 _115054 _115057 s f x g) (@lem5126850 _115054 _115057 s f x g)). Qed.
Lemma lem5126852 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : type802 _115054 _115057) : (term326 _115054 _115057 s f x) = (term327 _115054 _115057 s f x).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5126851 _115054 _115057 s f x g)). Qed.
Lemma lem5126853 {_115054 _115057 : Type'} : (@all (_115057 -> _115054)) = (@all (_115057 -> _115054)).
Proof. exact (eq_refl (@all (_115057 -> _115054))). Qed.
Lemma lem5126854 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : type802 _115054 _115057) : (term328 _115054 _115057 s f x) = (term329 _115054 _115057 s f x).
Proof. exact (MK_COMB (@lem5126853 _115054 _115057) (@lem5126852 _115054 _115057 s f x)). Qed.
Lemma lem5126855 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term330 _115054 _115057 s f) = (term331 _115054 _115057 s f).
Proof. exact (fun_ext (fun x : type802 _115054 _115057 => @lem5126854 _115054 _115057 s f x)). Qed.
Lemma lem5126856 {_115054 _115057 : Type'} : (@ex ((_115057 -> _115054) -> _115054)) = (@ex ((_115057 -> _115054) -> _115054)).
Proof. exact (eq_refl (@ex ((_115057 -> _115054) -> _115054))). Qed.
Lemma lem5126857 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term313 _115054 _115057 s f) = (term332 _115054 _115057 s f).
Proof. exact (MK_COMB (@lem5126856 _115054 _115057) (@lem5126855 _115054 _115057 s f)). Qed.
Lemma lem5126858 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : ((term312 _115054 _115057 s f) = (term313 _115054 _115057 s f)) = ((term121 _115054 _115057 s f) = (term332 _115054 _115057 s f)).
Proof. exact (MK_COMB (@lem5126846 _115054 _115057 s f) (@lem5126857 _115054 _115057 s f)). Qed.
Lemma lem5126859 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term121 _115054 _115057 s f) = (term332 _115054 _115057 s f).
Proof. exact (EQ_MP (@lem5126858 _115054 _115057 s f) (@lem5126833 _115054 _115057 s f)). Qed.
Lemma lem5126860 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term125 _115054 _115057 s f t) = (term125 _115054 _115057 s f t).
Proof. exact (eq_refl (term125 _115054 _115057 s f t)). Qed.
Lemma lem5126861 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term127 _115054 _115057 t s f) = (term333 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126860 _115054 _115057 s f t) (@lem5126859 _115054 _115057 s f)). Qed.
Lemma lem5126865 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5126866 {_115054 : Type'} (P : _115054 -> Prop) (Q : Prop) : (term334 _115054 P Q) = (term335 _115054 P Q).
Proof. exact (@lem5126865 _115054 P Q). Qed.
Lemma lem5126867 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term336 _115054 _115057 t s f) = (term337 _115054 _115057 t s f).
Proof. exact (@lem5126866 _115054 (term97 _115054 _115057 s f t) (term332 _115054 _115057 s f)). Qed.
Lemma lem5126868 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term338 _115054 _115057 s f t x) = (term87 _115054 _115057 s f x t).
Proof. exact (eq_refl (term338 _115054 _115057 s f t x)). Qed.
Lemma lem5126869 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term339 _115054 _115057 s f t) = (term97 _115054 _115057 s f t).
Proof. exact (fun_ext (fun x : _115054 => @lem5126868 _115054 _115057 s f x t)). Qed.
Lemma lem5126870 {_115054 : Type'} : (@ex _115054) = (@ex _115054).
Proof. exact (eq_refl (@ex _115054)). Qed.
Lemma lem5126871 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term340 _115054 _115057 s f t) = (term98 _115054 _115057 s f t).
Proof. exact (MK_COMB (@lem5126870 _115054) (@lem5126869 _115054 _115057 s f t)). Qed.
Lemma lem5126872 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5126873 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term341 _115054 _115057 s f t) = (term125 _115054 _115057 s f t).
Proof. exact (MK_COMB (@lem5126872) (@lem5126871 _115054 _115057 s f t)). Qed.
Lemma lem5126874 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term332 _115054 _115057 s f) = (term332 _115054 _115057 s f).
Proof. exact (eq_refl (term332 _115054 _115057 s f)). Qed.
Lemma lem5126875 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term336 _115054 _115057 t s f) = (term333 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126873 _115054 _115057 s f t) (@lem5126874 _115054 _115057 s f)). Qed.
Lemma lem5126876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5126877 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term342 _115054 _115057 t s f) = (term343 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126876) (@lem5126875 _115054 _115057 t s f)). Qed.
Lemma lem5126878 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term338 _115054 _115057 s f t x) = (term87 _115054 _115057 s f x t).
Proof. exact (eq_refl (term338 _115054 _115057 s f t x)). Qed.
Lemma lem5126879 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5126880 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term344 _115054 _115057 s f t x) = (term345 _115054 _115057 s f x t).
Proof. exact (MK_COMB (@lem5126879) (@lem5126878 _115054 _115057 s f x t)). Qed.
Lemma lem5126881 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term332 _115054 _115057 s f) = (term332 _115054 _115057 s f).
Proof. exact (eq_refl (term332 _115054 _115057 s f)). Qed.
Lemma lem5126882 {_115054 _115057 : Type'} (x : _115054) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term346 _115054 _115057 t x s f) = (term347 _115054 _115057 x t s f).
Proof. exact (MK_COMB (@lem5126880 _115054 _115057 s f x t) (@lem5126881 _115054 _115057 s f)). Qed.
Lemma lem5126883 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term348 _115054 _115057 t s f) = (term349 _115054 _115057 t s f).
Proof. exact (fun_ext (fun x : _115054 => @lem5126882 _115054 _115057 x t s f)). Qed.
Lemma lem5126884 {_115054 : Type'} : (@ex _115054) = (@ex _115054).
Proof. exact (eq_refl (@ex _115054)). Qed.
Lemma lem5126885 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term337 _115054 _115057 t s f) = (term350 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126884 _115054) (@lem5126883 _115054 _115057 t s f)). Qed.
Lemma lem5126886 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : ((term336 _115054 _115057 t s f) = (term337 _115054 _115057 t s f)) = ((term333 _115054 _115057 t s f) = (term350 _115054 _115057 t s f)).
Proof. exact (MK_COMB (@lem5126877 _115054 _115057 t s f) (@lem5126885 _115054 _115057 t s f)). Qed.
Lemma lem5126887 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term333 _115054 _115057 t s f) = (term350 _115054 _115057 t s f).
Proof. exact (EQ_MP (@lem5126886 _115054 _115057 t s f) (@lem5126867 _115054 _115057 t s f)). Qed.
Lemma lem5126889 {A : Type'} (P : Prop) (Q : A -> Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5126890 {_115054 _115057 : Type'} (P : Prop) (Q : type197 _115054 _115057) : (term353 _115054 _115057 P Q) = (term354 _115054 _115057 P Q).
Proof. exact (@lem5126889 (type802 _115054 _115057) P Q). Qed.
Lemma lem5126891 {_115054 _115057 : Type'} (x : _115054) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term355 _115054 _115057 x t s f) = (term356 _115054 _115057 x t s f).
Proof. exact (@lem5126890 _115054 _115057 (term87 _115054 _115057 s f x t) (term331 _115054 _115057 s f)). Qed.
Lemma lem5126892 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : type802 _115054 _115057) : (term357 _115054 _115057 s f x) = (term329 _115054 _115057 s f x).
Proof. exact (eq_refl (term357 _115054 _115057 s f x)). Qed.
Lemma lem5126893 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term358 _115054 _115057 s f) = (term331 _115054 _115057 s f).
Proof. exact (fun_ext (fun x : type802 _115054 _115057 => @lem5126892 _115054 _115057 s f x)). Qed.
Lemma lem5126894 {_115054 _115057 : Type'} : (@ex ((_115057 -> _115054) -> _115054)) = (@ex ((_115057 -> _115054) -> _115054)).
Proof. exact (eq_refl (@ex ((_115057 -> _115054) -> _115054))). Qed.
Lemma lem5126895 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) : (term359 _115054 _115057 s f) = (term332 _115054 _115057 s f).
Proof. exact (MK_COMB (@lem5126894 _115054 _115057) (@lem5126893 _115054 _115057 s f)). Qed.
Lemma lem5126896 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term345 _115054 _115057 s f x t) = (term345 _115054 _115057 s f x t).
Proof. exact (eq_refl (term345 _115054 _115057 s f x t)). Qed.
Lemma lem5126897 {_115054 _115057 : Type'} (x : _115054) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term355 _115054 _115057 x t s f) = (term347 _115054 _115057 x t s f).
Proof. exact (MK_COMB (@lem5126896 _115054 _115057 s f x t) (@lem5126895 _115054 _115057 s f)). Qed.
Lemma lem5126898 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5126899 {_115054 _115057 : Type'} (x : _115054) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term360 _115054 _115057 x t s f) = (term361 _115054 _115057 x t s f).
Proof. exact (MK_COMB (@lem5126898) (@lem5126897 _115054 _115057 x t s f)). Qed.
Lemma lem5126900 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : type802 _115054 _115057) : (term357 _115054 _115057 s f x) = (term329 _115054 _115057 s f x).
Proof. exact (eq_refl (term357 _115054 _115057 s f x)). Qed.
Lemma lem5126901 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term345 _115054 _115057 s f x t) = (term345 _115054 _115057 s f x t).
Proof. exact (eq_refl (term345 _115054 _115057 s f x t)). Qed.
Lemma lem5126902 {_115054 _115057 : Type'} (x : _115054) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) (x' : type802 _115054 _115057) : (term362 _115054 _115057 x t s f x') = (term363 _115054 _115057 x t s f x').
Proof. exact (MK_COMB (@lem5126901 _115054 _115057 s f x t) (@lem5126900 _115054 _115057 s f x')). Qed.
Lemma lem5126903 {_115054 _115057 : Type'} (x : _115054) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term364 _115054 _115057 x t s f) = (term365 _115054 _115057 x t s f).
Proof. exact (fun_ext (fun x' : type802 _115054 _115057 => @lem5126902 _115054 _115057 x t s f x')). Qed.
Lemma lem5126904 {_115054 _115057 : Type'} : (@ex ((_115057 -> _115054) -> _115054)) = (@ex ((_115057 -> _115054) -> _115054)).
Proof. exact (eq_refl (@ex ((_115057 -> _115054) -> _115054))). Qed.
Lemma lem5126905 {_115054 _115057 : Type'} (x : _115054) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term356 _115054 _115057 x t s f) = (term366 _115054 _115057 x t s f).
Proof. exact (MK_COMB (@lem5126904 _115054 _115057) (@lem5126903 _115054 _115057 x t s f)). Qed.
Lemma lem5126906 {_115054 _115057 : Type'} (x : _115054) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : ((term355 _115054 _115057 x t s f) = (term356 _115054 _115057 x t s f)) = ((term347 _115054 _115057 x t s f) = (term366 _115054 _115057 x t s f)).
Proof. exact (MK_COMB (@lem5126899 _115054 _115057 x t s f) (@lem5126905 _115054 _115057 x t s f)). Qed.
Lemma lem5126907 {_115054 _115057 : Type'} (x : _115054) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term347 _115054 _115057 x t s f) = (term366 _115054 _115057 x t s f).
Proof. exact (EQ_MP (@lem5126906 _115054 _115057 x t s f) (@lem5126891 _115054 _115057 x t s f)). Qed.
Lemma lem5126908 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term349 _115054 _115057 t s f) = (term367 _115054 _115057 t s f).
Proof. exact (fun_ext (fun x : _115054 => @lem5126907 _115054 _115057 x t s f)). Qed.
Lemma lem5126909 {_115054 : Type'} : (@ex _115054) = (@ex _115054).
Proof. exact (eq_refl (@ex _115054)). Qed.
Lemma lem5126910 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term350 _115054 _115057 t s f) = (term368 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126909 _115054) (@lem5126908 _115054 _115057 t s f)). Qed.
Lemma lem5126911 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term333 _115054 _115057 t s f) = (term368 _115054 _115057 t s f).
Proof. exact (TRANS (@lem5126887 _115054 _115057 t s f) (@lem5126910 _115054 _115057 t s f)). Qed.
Lemma lem5126912 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term127 _115054 _115057 t s f) = (term368 _115054 _115057 t s f).
Proof. exact (TRANS (@lem5126861 _115054 _115057 t s f) (@lem5126911 _115054 _115057 t s f)). Qed.
Lemma lem5126913 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term138 _115054 _115057 t s) = (term369 _115054 _115057 t s).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5126912 _115054 _115057 t s f)). Qed.
Lemma lem5126914 {_115054 _115057 : Type'} : (@all (_115054 -> _115057)) = (@all (_115054 -> _115057)).
Proof. exact (eq_refl (@all (_115054 -> _115057))). Qed.
Lemma lem5126915 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term139 _115054 _115057 t s) = (term370 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126914 _115054 _115057) (@lem5126913 _115054 _115057 t s)). Qed.
Lemma lem5126917 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5126918 {_115054 _115057 : Type'} (P : type551 _115054 _115057) : (term206 _115054 _115057 P) = (term207 _115054 _115057 P).
Proof. exact (@lem5126917 (_115054 -> _115057) _115054 P). Qed.
Lemma lem5126919 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term371 _115054 _115057 t s) = (term372 _115054 _115057 t s).
Proof. exact (@lem5126918 _115054 _115057 (term373 _115054 _115057 t s)). Qed.
Lemma lem5126920 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term374 _115054 _115057 t s f) = (term367 _115054 _115057 t s f).
Proof. exact (eq_refl (term374 _115054 _115057 t s f)). Qed.
Lemma lem5126921 {_115054 : Type'} (x : _115054) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5126922 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) (x : _115054) : (term375 _115054 _115057 t s f x) = (term376 _115054 _115057 t s f x).
Proof. exact (MK_COMB (@lem5126920 _115054 _115057 t s f) (@lem5126921 _115054 x)). Qed.
Lemma lem5126923 {_115054 _115057 : Type'} (x : _115054) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term376 _115054 _115057 t s f x) = (term366 _115054 _115057 x t s f).
Proof. exact (eq_refl (term376 _115054 _115057 t s f x)). Qed.
Lemma lem5126924 {_115054 _115057 : Type'} (x : _115054) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term375 _115054 _115057 t s f x) = (term366 _115054 _115057 x t s f).
Proof. exact (TRANS (@lem5126922 _115054 _115057 t s f x) (@lem5126923 _115054 _115057 x t s f)). Qed.
Lemma lem5126925 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term377 _115054 _115057 t s f) = (term367 _115054 _115057 t s f).
Proof. exact (fun_ext (fun x : _115054 => @lem5126924 _115054 _115057 x t s f)). Qed.
Lemma lem5126926 {_115054 : Type'} : (@ex _115054) = (@ex _115054).
Proof. exact (eq_refl (@ex _115054)). Qed.
Lemma lem5126927 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term378 _115054 _115057 t s f) = (term368 _115054 _115057 t s f).
Proof. exact (MK_COMB (@lem5126926 _115054) (@lem5126925 _115054 _115057 t s f)). Qed.
Lemma lem5126928 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term379 _115054 _115057 t s) = (term369 _115054 _115057 t s).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5126927 _115054 _115057 t s f)). Qed.
Lemma lem5126929 {_115054 _115057 : Type'} : (@all (_115054 -> _115057)) = (@all (_115054 -> _115057)).
Proof. exact (eq_refl (@all (_115054 -> _115057))). Qed.
Lemma lem5126930 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term371 _115054 _115057 t s) = (term370 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126929 _115054 _115057) (@lem5126928 _115054 _115057 t s)). Qed.
Lemma lem5126931 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5126932 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term380 _115054 _115057 t s) = (term381 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126931) (@lem5126930 _115054 _115057 t s)). Qed.
Lemma lem5126933 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term374 _115054 _115057 t s f) = (term367 _115054 _115057 t s f).
Proof. exact (eq_refl (term374 _115054 _115057 t s f)). Qed.
Lemma lem5126934 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (f : _115054 -> _115057) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem5126935 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (x : type569 _115054 _115057) (f : _115054 -> _115057) : (term382 _115054 _115057 t s x f) = (term383 _115054 _115057 t s x f).
Proof. exact (MK_COMB (@lem5126933 _115054 _115057 t s f) (@lem5126934 _115054 _115057 x f)). Qed.
Lemma lem5126936 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term383 _115054 _115057 t s x f) = (term384 _115054 _115057 x t s f).
Proof. exact (eq_refl (term383 _115054 _115057 t s x f)). Qed.
Lemma lem5126937 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term382 _115054 _115057 t s x f) = (term384 _115054 _115057 x t s f).
Proof. exact (TRANS (@lem5126935 _115054 _115057 t s x f) (@lem5126936 _115054 _115057 x t s f)). Qed.
Lemma lem5126938 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : (term385 _115054 _115057 t s x) = (term386 _115054 _115057 x t s).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5126937 _115054 _115057 x t s f)). Qed.
Lemma lem5126939 {_115054 _115057 : Type'} : (@all (_115054 -> _115057)) = (@all (_115054 -> _115057)).
Proof. exact (eq_refl (@all (_115054 -> _115057))). Qed.
Lemma lem5126940 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : (term387 _115054 _115057 t s x) = (term388 _115054 _115057 x t s).
Proof. exact (MK_COMB (@lem5126939 _115054 _115057) (@lem5126938 _115054 _115057 x t s)). Qed.
Lemma lem5126941 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term389 _115054 _115057 t s) = (term390 _115054 _115057 t s).
Proof. exact (fun_ext (fun x : type569 _115054 _115057 => @lem5126940 _115054 _115057 x t s)). Qed.
Lemma lem5126942 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> _115054)) = (@ex ((_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> _115054))). Qed.
Lemma lem5126943 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term372 _115054 _115057 t s) = (term391 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126942 _115054 _115057) (@lem5126941 _115054 _115057 t s)). Qed.
Lemma lem5126944 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : ((term371 _115054 _115057 t s) = (term372 _115054 _115057 t s)) = ((term370 _115054 _115057 t s) = (term391 _115054 _115057 t s)).
Proof. exact (MK_COMB (@lem5126932 _115054 _115057 t s) (@lem5126943 _115054 _115057 t s)). Qed.
Lemma lem5126945 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term370 _115054 _115057 t s) = (term391 _115054 _115057 t s).
Proof. exact (EQ_MP (@lem5126944 _115054 _115057 t s) (@lem5126919 _115054 _115057 t s)). Qed.
Lemma lem5126947 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5126948 {_115054 _115057 : Type'} (P : type505 _115054 _115057) : (term392 _115054 _115057 P) = (term393 _115054 _115057 P).
Proof. exact (@lem5126947 (_115054 -> _115057) (type802 _115054 _115057) P). Qed.
Lemma lem5126949 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : (term394 _115054 _115057 x t s) = (term395 _115054 _115057 x t s).
Proof. exact (@lem5126948 _115054 _115057 (term396 _115054 _115057 x t s)). Qed.
Lemma lem5126950 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term397 _115054 _115057 x t s f) = (term398 _115054 _115057 x t s f).
Proof. exact (eq_refl (term397 _115054 _115057 x t s f)). Qed.
Lemma lem5126951 {_115054 _115057 : Type'} (x : type802 _115054 _115057) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5126952 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) (x' : type802 _115054 _115057) : (term399 _115054 _115057 x t s f x') = (term400 _115054 _115057 x t s f x').
Proof. exact (MK_COMB (@lem5126950 _115054 _115057 x t s f) (@lem5126951 _115054 _115057 x')). Qed.
Lemma lem5126953 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) (x' : type802 _115054 _115057) : (term400 _115054 _115057 x t s f x') = (term401 _115054 _115057 x t s f x').
Proof. exact (eq_refl (term400 _115054 _115057 x t s f x')). Qed.
Lemma lem5126954 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) (x' : type802 _115054 _115057) : (term399 _115054 _115057 x t s f x') = (term401 _115054 _115057 x t s f x').
Proof. exact (TRANS (@lem5126952 _115054 _115057 x t s f x') (@lem5126953 _115054 _115057 x t s f x')). Qed.
Lemma lem5126955 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term402 _115054 _115057 x t s f) = (term398 _115054 _115057 x t s f).
Proof. exact (fun_ext (fun x' : type802 _115054 _115057 => @lem5126954 _115054 _115057 x t s f x')). Qed.
Lemma lem5126956 {_115054 _115057 : Type'} : (@ex ((_115057 -> _115054) -> _115054)) = (@ex ((_115057 -> _115054) -> _115054)).
Proof. exact (eq_refl (@ex ((_115057 -> _115054) -> _115054))). Qed.
Lemma lem5126957 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term403 _115054 _115057 x t s f) = (term384 _115054 _115057 x t s f).
Proof. exact (MK_COMB (@lem5126956 _115054 _115057) (@lem5126955 _115054 _115057 x t s f)). Qed.
Lemma lem5126958 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : (term404 _115054 _115057 x t s) = (term386 _115054 _115057 x t s).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5126957 _115054 _115057 x t s f)). Qed.
Lemma lem5126959 {_115054 _115057 : Type'} : (@all (_115054 -> _115057)) = (@all (_115054 -> _115057)).
Proof. exact (eq_refl (@all (_115054 -> _115057))). Qed.
Lemma lem5126960 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : (term394 _115054 _115057 x t s) = (term388 _115054 _115057 x t s).
Proof. exact (MK_COMB (@lem5126959 _115054 _115057) (@lem5126958 _115054 _115057 x t s)). Qed.
Lemma lem5126961 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5126962 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : (term405 _115054 _115057 x t s) = (term406 _115054 _115057 x t s).
Proof. exact (MK_COMB (@lem5126961) (@lem5126960 _115054 _115057 x t s)). Qed.
Lemma lem5126963 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (f : _115054 -> _115057) : (term397 _115054 _115057 x t s f) = (term398 _115054 _115057 x t s f).
Proof. exact (eq_refl (term397 _115054 _115057 x t s f)). Qed.
Lemma lem5126964 {_115054 _115057 : Type'} (x : type530 _115054 _115057) (f : _115054 -> _115057) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem5126965 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x' : type530 _115054 _115057) (f : _115054 -> _115057) : (term407 _115054 _115057 x t s x' f) = (term408 _115054 _115057 x t s x' f).
Proof. exact (MK_COMB (@lem5126963 _115054 _115057 x t s f) (@lem5126964 _115054 _115057 x' f)). Qed.
Lemma lem5126966 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x' : type530 _115054 _115057) (f : _115054 -> _115057) : (term408 _115054 _115057 x t s x' f) = (term409 _115054 _115057 x t s x' f).
Proof. exact (eq_refl (term408 _115054 _115057 x t s x' f)). Qed.
Lemma lem5126967 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x' : type530 _115054 _115057) (f : _115054 -> _115057) : (term407 _115054 _115057 x t s x' f) = (term409 _115054 _115057 x t s x' f).
Proof. exact (TRANS (@lem5126965 _115054 _115057 x t s x' f) (@lem5126966 _115054 _115057 x t s x' f)). Qed.
Lemma lem5126968 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x' : type530 _115054 _115057) : (term410 _115054 _115057 x t s x') = (term411 _115054 _115057 x t s x').
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5126967 _115054 _115057 x t s x' f)). Qed.
Lemma lem5126969 {_115054 _115057 : Type'} : (@all (_115054 -> _115057)) = (@all (_115054 -> _115057)).
Proof. exact (eq_refl (@all (_115054 -> _115057))). Qed.
Lemma lem5126970 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x' : type530 _115054 _115057) : (term412 _115054 _115057 x t s x') = (term413 _115054 _115057 x t s x').
Proof. exact (MK_COMB (@lem5126969 _115054 _115057) (@lem5126968 _115054 _115057 x t s x')). Qed.
Lemma lem5126971 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : (term414 _115054 _115057 x t s) = (term415 _115054 _115057 x t s).
Proof. exact (fun_ext (fun x' : type530 _115054 _115057 => @lem5126970 _115054 _115057 x t s x')). Qed.
Lemma lem5126972 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054)) = (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054))). Qed.
Lemma lem5126973 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : (term395 _115054 _115057 x t s) = (term416 _115054 _115057 x t s).
Proof. exact (MK_COMB (@lem5126972 _115054 _115057) (@lem5126971 _115054 _115057 x t s)). Qed.
Lemma lem5126974 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : ((term394 _115054 _115057 x t s) = (term395 _115054 _115057 x t s)) = ((term388 _115054 _115057 x t s) = (term416 _115054 _115057 x t s)).
Proof. exact (MK_COMB (@lem5126962 _115054 _115057 x t s) (@lem5126973 _115054 _115057 x t s)). Qed.
Lemma lem5126975 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : (term388 _115054 _115057 x t s) = (term416 _115054 _115057 x t s).
Proof. exact (EQ_MP (@lem5126974 _115054 _115057 x t s) (@lem5126949 _115054 _115057 x t s)). Qed.
Lemma lem5126976 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term390 _115054 _115057 t s) = (term417 _115054 _115057 t s).
Proof. exact (fun_ext (fun x : type569 _115054 _115057 => @lem5126975 _115054 _115057 x t s)). Qed.
Lemma lem5126977 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> _115054)) = (@ex ((_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> _115054))). Qed.
Lemma lem5126978 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term391 _115054 _115057 t s) = (term418 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126977 _115054 _115057) (@lem5126976 _115054 _115057 t s)). Qed.
Lemma lem5126979 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term370 _115054 _115057 t s) = (term418 _115054 _115057 t s).
Proof. exact (TRANS (@lem5126945 _115054 _115057 t s) (@lem5126978 _115054 _115057 t s)). Qed.
Lemma lem5126980 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term139 _115054 _115057 t s) = (term418 _115054 _115057 t s).
Proof. exact (TRANS (@lem5126915 _115054 _115057 t s) (@lem5126979 _115054 _115057 t s)). Qed.
Lemma lem5126981 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5126982 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term178 _115054 _115057 t s) = (term419 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126981) (@lem5126980 _115054 _115057 t s)). Qed.
Lemma lem5126983 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term176 _115054 _115057 s t) = (term176 _115054 _115057 s t).
Proof. exact (eq_refl (term176 _115054 _115057 s t)). Qed.
Lemma lem5126984 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term180 _115054 _115057 s t) = (term420 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126982 _115054 _115057 t s) (@lem5126983 _115054 _115057 s t)). Qed.
Lemma lem5126986 {A : Type'} (P : A -> Prop) (Q : Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5126987 {_115054 _115057 : Type'} (P : type118 _115054 _115057) (Q : Prop) : (term421 _115054 _115057 P Q) = (term422 _115054 _115057 P Q).
Proof. exact (@lem5126986 (type569 _115054 _115057) P Q). Qed.
Lemma lem5126988 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term423 _115054 _115057 s t) = (term424 _115054 _115057 s t).
Proof. exact (@lem5126987 _115054 _115057 (term417 _115054 _115057 t s) (term176 _115054 _115057 s t)). Qed.
Lemma lem5126989 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : (term425 _115054 _115057 t s x) = (term416 _115054 _115057 x t s).
Proof. exact (eq_refl (term425 _115054 _115057 t s x)). Qed.
Lemma lem5126990 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term426 _115054 _115057 t s) = (term417 _115054 _115057 t s).
Proof. exact (fun_ext (fun x : type569 _115054 _115057 => @lem5126989 _115054 _115057 x t s)). Qed.
Lemma lem5126991 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> _115054)) = (@ex ((_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> _115054))). Qed.
Lemma lem5126992 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term427 _115054 _115057 t s) = (term418 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126991 _115054 _115057) (@lem5126990 _115054 _115057 t s)). Qed.
Lemma lem5126993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5126994 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) : (term428 _115054 _115057 t s) = (term419 _115054 _115057 t s).
Proof. exact (MK_COMB (@lem5126993) (@lem5126992 _115054 _115057 t s)). Qed.
Lemma lem5126995 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term176 _115054 _115057 s t) = (term176 _115054 _115057 s t).
Proof. exact (eq_refl (term176 _115054 _115057 s t)). Qed.
Lemma lem5126996 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term423 _115054 _115057 s t) = (term420 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126994 _115054 _115057 t s) (@lem5126995 _115054 _115057 s t)). Qed.
Lemma lem5126997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5126998 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term429 _115054 _115057 s t) = (term430 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126997) (@lem5126996 _115054 _115057 s t)). Qed.
Lemma lem5126999 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : (term425 _115054 _115057 t s x) = (term416 _115054 _115057 x t s).
Proof. exact (eq_refl (term425 _115054 _115057 t s x)). Qed.
Lemma lem5127000 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5127001 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : (term431 _115054 _115057 t s x) = (term432 _115054 _115057 x t s).
Proof. exact (MK_COMB (@lem5127000) (@lem5126999 _115054 _115057 x t s)). Qed.
Lemma lem5127002 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term176 _115054 _115057 s t) = (term176 _115054 _115057 s t).
Proof. exact (eq_refl (term176 _115054 _115057 s t)). Qed.
Lemma lem5127003 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term433 _115054 _115057 x s t) = (term434 _115054 _115057 x s t).
Proof. exact (MK_COMB (@lem5127001 _115054 _115057 x t s) (@lem5127002 _115054 _115057 s t)). Qed.
Lemma lem5127004 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term435 _115054 _115057 s t) = (term436 _115054 _115057 s t).
Proof. exact (fun_ext (fun x : type569 _115054 _115057 => @lem5127003 _115054 _115057 x s t)). Qed.
Lemma lem5127005 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> _115054)) = (@ex ((_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> _115054))). Qed.
Lemma lem5127006 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term424 _115054 _115057 s t) = (term437 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5127005 _115054 _115057) (@lem5127004 _115054 _115057 s t)). Qed.
Lemma lem5127007 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term423 _115054 _115057 s t) = (term424 _115054 _115057 s t)) = ((term420 _115054 _115057 s t) = (term437 _115054 _115057 s t)).
Proof. exact (MK_COMB (@lem5126998 _115054 _115057 s t) (@lem5127006 _115054 _115057 s t)). Qed.
Lemma lem5127008 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term420 _115054 _115057 s t) = (term437 _115054 _115057 s t).
Proof. exact (EQ_MP (@lem5127007 _115054 _115057 s t) (@lem5126988 _115054 _115057 s t)). Qed.
Lemma lem5127010 {A : Type'} (P : A -> Prop) (Q : Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5127011 {_115054 _115057 : Type'} (P : type101 _115054 _115057) (Q : Prop) : (term438 _115054 _115057 P Q) = (term439 _115054 _115057 P Q).
Proof. exact (@lem5127010 (type530 _115054 _115057) P Q). Qed.
Lemma lem5127012 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term440 _115054 _115057 x s t) = (term441 _115054 _115057 x s t).
Proof. exact (@lem5127011 _115054 _115057 (term415 _115054 _115057 x t s) (term176 _115054 _115057 s t)). Qed.
Lemma lem5127013 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x' : type530 _115054 _115057) : (term442 _115054 _115057 x t s x') = (term413 _115054 _115057 x t s x').
Proof. exact (eq_refl (term442 _115054 _115057 x t s x')). Qed.
Lemma lem5127014 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : (term443 _115054 _115057 x t s) = (term415 _115054 _115057 x t s).
Proof. exact (fun_ext (fun x' : type530 _115054 _115057 => @lem5127013 _115054 _115057 x t s x')). Qed.
Lemma lem5127015 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054)) = (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054))). Qed.
Lemma lem5127016 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : (term444 _115054 _115057 x t s) = (term416 _115054 _115057 x t s).
Proof. exact (MK_COMB (@lem5127015 _115054 _115057) (@lem5127014 _115054 _115057 x t s)). Qed.
Lemma lem5127017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5127018 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) : (term445 _115054 _115057 x t s) = (term432 _115054 _115057 x t s).
Proof. exact (MK_COMB (@lem5127017) (@lem5127016 _115054 _115057 x t s)). Qed.
Lemma lem5127019 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term176 _115054 _115057 s t) = (term176 _115054 _115057 s t).
Proof. exact (eq_refl (term176 _115054 _115057 s t)). Qed.
Lemma lem5127020 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term440 _115054 _115057 x s t) = (term434 _115054 _115057 x s t).
Proof. exact (MK_COMB (@lem5127018 _115054 _115057 x t s) (@lem5127019 _115054 _115057 s t)). Qed.
Lemma lem5127021 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5127022 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term446 _115054 _115057 x s t) = (term447 _115054 _115057 x s t).
Proof. exact (MK_COMB (@lem5127021) (@lem5127020 _115054 _115057 x s t)). Qed.
Lemma lem5127023 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x' : type530 _115054 _115057) : (term442 _115054 _115057 x t s x') = (term413 _115054 _115057 x t s x').
Proof. exact (eq_refl (term442 _115054 _115057 x t s x')). Qed.
Lemma lem5127024 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5127025 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x' : type530 _115054 _115057) : (term448 _115054 _115057 x t s x') = (term449 _115054 _115057 x t s x').
Proof. exact (MK_COMB (@lem5127024) (@lem5127023 _115054 _115057 x t s x')). Qed.
Lemma lem5127026 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term176 _115054 _115057 s t) = (term176 _115054 _115057 s t).
Proof. exact (eq_refl (term176 _115054 _115057 s t)). Qed.
Lemma lem5127027 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term450 _115054 _115057 x x' s t) = (term451 _115054 _115057 x x' s t).
Proof. exact (MK_COMB (@lem5127025 _115054 _115057 x t s x') (@lem5127026 _115054 _115057 s t)). Qed.
Lemma lem5127028 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term452 _115054 _115057 x s t) = (term453 _115054 _115057 x s t).
Proof. exact (fun_ext (fun x' : type530 _115054 _115057 => @lem5127027 _115054 _115057 x x' s t)). Qed.
Lemma lem5127029 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054)) = (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054))). Qed.
Lemma lem5127030 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term441 _115054 _115057 x s t) = (term454 _115054 _115057 x s t).
Proof. exact (MK_COMB (@lem5127029 _115054 _115057) (@lem5127028 _115054 _115057 x s t)). Qed.
Lemma lem5127031 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term440 _115054 _115057 x s t) = (term441 _115054 _115057 x s t)) = ((term434 _115054 _115057 x s t) = (term454 _115054 _115057 x s t)).
Proof. exact (MK_COMB (@lem5127022 _115054 _115057 x s t) (@lem5127030 _115054 _115057 x s t)). Qed.
Lemma lem5127032 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term434 _115054 _115057 x s t) = (term454 _115054 _115057 x s t).
Proof. exact (EQ_MP (@lem5127031 _115054 _115057 x s t) (@lem5127012 _115054 _115057 x s t)). Qed.
Lemma lem5127034 {A : Type'} (P : Prop) (Q : A -> Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5127035 {_115054 _115057 : Type'} (P : Prop) (Q : type805 _115054 _115057) : (term23 _115054 _115057 P Q) = (term24 _115054 _115057 P Q).
Proof. exact (@lem5127034 (_115057 -> _115054) P Q). Qed.
Lemma lem5127036 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term455 _115054 _115057 x x' s t) = (term456 _115054 _115057 x x' s t).
Proof. exact (@lem5127035 _115054 _115057 (term413 _115054 _115057 x t s x') (term175 _115054 _115057 s t)). Qed.
Lemma lem5127037 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term457 _115054 _115057 s t g) = (term167 _115054 _115057 s t g).
Proof. exact (eq_refl (term457 _115054 _115057 s t g)). Qed.
Lemma lem5127038 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term458 _115054 _115057 s t) = (term175 _115054 _115057 s t).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5127037 _115054 _115057 s t g)). Qed.
Lemma lem5127039 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5127040 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term459 _115054 _115057 s t) = (term176 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5127039 _115054 _115057) (@lem5127038 _115054 _115057 s t)). Qed.
Lemma lem5127041 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x' : type530 _115054 _115057) : (term449 _115054 _115057 x t s x') = (term449 _115054 _115057 x t s x').
Proof. exact (eq_refl (term449 _115054 _115057 x t s x')). Qed.
Lemma lem5127042 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term455 _115054 _115057 x x' s t) = (term451 _115054 _115057 x x' s t).
Proof. exact (MK_COMB (@lem5127041 _115054 _115057 x t s x') (@lem5127040 _115054 _115057 s t)). Qed.
Lemma lem5127043 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5127044 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term460 _115054 _115057 x x' s t) = (term461 _115054 _115057 x x' s t).
Proof. exact (MK_COMB (@lem5127043) (@lem5127042 _115054 _115057 x x' s t)). Qed.
Lemma lem5127045 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term457 _115054 _115057 s t g) = (term167 _115054 _115057 s t g).
Proof. exact (eq_refl (term457 _115054 _115057 s t g)). Qed.
Lemma lem5127046 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x' : type530 _115054 _115057) : (term449 _115054 _115057 x t s x') = (term449 _115054 _115057 x t s x').
Proof. exact (eq_refl (term449 _115054 _115057 x t s x')). Qed.
Lemma lem5127047 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term462 _115054 _115057 x x' s t g) = (term463 _115054 _115057 x x' s t g).
Proof. exact (MK_COMB (@lem5127046 _115054 _115057 x t s x') (@lem5127045 _115054 _115057 s t g)). Qed.
Lemma lem5127048 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term464 _115054 _115057 x x' s t) = (term465 _115054 _115057 x x' s t).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5127047 _115054 _115057 x x' s t g)). Qed.
Lemma lem5127049 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5127050 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term456 _115054 _115057 x x' s t) = (term466 _115054 _115057 x x' s t).
Proof. exact (MK_COMB (@lem5127049 _115054 _115057) (@lem5127048 _115054 _115057 x x' s t)). Qed.
Lemma lem5127051 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term455 _115054 _115057 x x' s t) = (term456 _115054 _115057 x x' s t)) = ((term451 _115054 _115057 x x' s t) = (term466 _115054 _115057 x x' s t)).
Proof. exact (MK_COMB (@lem5127044 _115054 _115057 x x' s t) (@lem5127050 _115054 _115057 x x' s t)). Qed.
Lemma lem5127052 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term451 _115054 _115057 x x' s t) = (term466 _115054 _115057 x x' s t).
Proof. exact (EQ_MP (@lem5127051 _115054 _115057 x x' s t) (@lem5127036 _115054 _115057 x x' s t)). Qed.
Lemma lem5127054 {A : Type'} (P : Prop) (Q : A -> Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5127055 {_115054 _115057 : Type'} (P : Prop) (Q : type572 _115054 _115057) : (term467 _115054 _115057 P Q) = (term468 _115054 _115057 P Q).
Proof. exact (@lem5127054 (_115054 -> _115057) P Q). Qed.
Lemma lem5127056 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term469 _115054 _115057 x x' s t g) = (term470 _115054 _115057 x x' s t g).
Proof. exact (@lem5127055 _115054 _115057 (term413 _115054 _115057 x t s x') (term166 _115054 _115057 s t g)). Qed.
Lemma lem5127057 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term471 _115054 _115057 s t g g') = (term158 _115054 _115057 s t g g').
Proof. exact (eq_refl (term471 _115054 _115057 s t g g')). Qed.
Lemma lem5127058 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term472 _115054 _115057 s t g) = (term166 _115054 _115057 s t g).
Proof. exact (fun_ext (fun g' : _115054 -> _115057 => @lem5127057 _115054 _115057 s t g g')). Qed.
Lemma lem5127059 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5127060 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term473 _115054 _115057 s t g) = (term167 _115054 _115057 s t g).
Proof. exact (MK_COMB (@lem5127059 _115054 _115057) (@lem5127058 _115054 _115057 s t g)). Qed.
Lemma lem5127061 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x' : type530 _115054 _115057) : (term449 _115054 _115057 x t s x') = (term449 _115054 _115057 x t s x').
Proof. exact (eq_refl (term449 _115054 _115057 x t s x')). Qed.
Lemma lem5127062 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term469 _115054 _115057 x x' s t g) = (term463 _115054 _115057 x x' s t g).
Proof. exact (MK_COMB (@lem5127061 _115054 _115057 x t s x') (@lem5127060 _115054 _115057 s t g)). Qed.
Lemma lem5127063 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5127064 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term474 _115054 _115057 x x' s t g) = (term475 _115054 _115057 x x' s t g).
Proof. exact (MK_COMB (@lem5127063) (@lem5127062 _115054 _115057 x x' s t g)). Qed.
Lemma lem5127065 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term471 _115054 _115057 s t g g') = (term158 _115054 _115057 s t g g').
Proof. exact (eq_refl (term471 _115054 _115057 s t g g')). Qed.
Lemma lem5127066 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x' : type530 _115054 _115057) : (term449 _115054 _115057 x t s x') = (term449 _115054 _115057 x t s x').
Proof. exact (eq_refl (term449 _115054 _115057 x t s x')). Qed.
Lemma lem5127067 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term476 _115054 _115057 x x' s t g g') = (term477 _115054 _115057 x x' s t g g').
Proof. exact (MK_COMB (@lem5127066 _115054 _115057 x t s x') (@lem5127065 _115054 _115057 s t g g')). Qed.
Lemma lem5127068 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term478 _115054 _115057 x x' s t g) = (term479 _115054 _115057 x x' s t g).
Proof. exact (fun_ext (fun g' : _115054 -> _115057 => @lem5127067 _115054 _115057 x x' s t g g')). Qed.
Lemma lem5127069 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5127070 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term470 _115054 _115057 x x' s t g) = (term480 _115054 _115057 x x' s t g).
Proof. exact (MK_COMB (@lem5127069 _115054 _115057) (@lem5127068 _115054 _115057 x x' s t g)). Qed.
Lemma lem5127071 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : ((term469 _115054 _115057 x x' s t g) = (term470 _115054 _115057 x x' s t g)) = ((term463 _115054 _115057 x x' s t g) = (term480 _115054 _115057 x x' s t g)).
Proof. exact (MK_COMB (@lem5127064 _115054 _115057 x x' s t g) (@lem5127070 _115054 _115057 x x' s t g)). Qed.
Lemma lem5127072 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term463 _115054 _115057 x x' s t g) = (term480 _115054 _115057 x x' s t g).
Proof. exact (EQ_MP (@lem5127071 _115054 _115057 x x' s t g) (@lem5127056 _115054 _115057 x x' s t g)). Qed.
Lemma lem5127073 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term465 _115054 _115057 x x' s t) = (term481 _115054 _115057 x x' s t).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5127072 _115054 _115057 x x' s t g)). Qed.
Lemma lem5127074 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5127075 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term466 _115054 _115057 x x' s t) = (term482 _115054 _115057 x x' s t).
Proof. exact (MK_COMB (@lem5127074 _115054 _115057) (@lem5127073 _115054 _115057 x x' s t)). Qed.
Lemma lem5127076 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term451 _115054 _115057 x x' s t) = (term482 _115054 _115057 x x' s t).
Proof. exact (TRANS (@lem5127052 _115054 _115057 x x' s t) (@lem5127075 _115054 _115057 x x' s t)). Qed.
Lemma lem5127077 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term453 _115054 _115057 x s t) = (term483 _115054 _115057 x s t).
Proof. exact (fun_ext (fun x' : type530 _115054 _115057 => @lem5127076 _115054 _115057 x x' s t)). Qed.
Lemma lem5127078 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054)) = (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054))). Qed.
Lemma lem5127079 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term454 _115054 _115057 x s t) = (term484 _115054 _115057 x s t).
Proof. exact (MK_COMB (@lem5127078 _115054 _115057) (@lem5127077 _115054 _115057 x s t)). Qed.
Lemma lem5127080 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term434 _115054 _115057 x s t) = (term484 _115054 _115057 x s t).
Proof. exact (TRANS (@lem5127032 _115054 _115057 x s t) (@lem5127079 _115054 _115057 x s t)). Qed.
Lemma lem5127081 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term436 _115054 _115057 s t) = (term485 _115054 _115057 s t).
Proof. exact (fun_ext (fun x : type569 _115054 _115057 => @lem5127080 _115054 _115057 x s t)). Qed.
Lemma lem5127082 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> _115054)) = (@ex ((_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> _115054))). Qed.
Lemma lem5127083 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term437 _115054 _115057 s t) = (term486 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5127082 _115054 _115057) (@lem5127081 _115054 _115057 s t)). Qed.
Lemma lem5127084 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term420 _115054 _115057 s t) = (term486 _115054 _115057 s t).
Proof. exact (TRANS (@lem5127008 _115054 _115057 s t) (@lem5127083 _115054 _115057 s t)). Qed.
Lemma lem5127085 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term180 _115054 _115057 s t) = (term486 _115054 _115057 s t).
Proof. exact (TRANS (@lem5126984 _115054 _115057 s t) (@lem5127084 _115054 _115057 s t)). Qed.
Lemma lem5127086 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term188 _115054 _115057 s t) = (term487 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5126829 _115054 _115057 s t) (@lem5127085 _115054 _115057 s t)). Qed.
Lemma lem5127090 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5127091 {_115054 _115057 : Type'} (P : type572 _115054 _115057) (Q : Prop) : (term488 _115054 _115057 P Q) = (term489 _115054 _115057 P Q).
Proof. exact (@lem5127090 (_115054 -> _115057) P Q). Qed.
Lemma lem5127092 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term490 _115054 _115057 s t) = (term491 _115054 _115057 s t).
Proof. exact (@lem5127091 _115054 _115057 (term307 _115054 _115057 s t) (term486 _115054 _115057 s t)). Qed.
Lemma lem5127093 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term492 _115054 _115057 s t f) = (term306 _115054 _115057 f s t).
Proof. exact (eq_refl (term492 _115054 _115057 s t f)). Qed.
Lemma lem5127094 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term493 _115054 _115057 s t) = (term307 _115054 _115057 s t).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5127093 _115054 _115057 f s t)). Qed.
Lemma lem5127095 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5127096 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term494 _115054 _115057 s t) = (term308 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5127095 _115054 _115057) (@lem5127094 _115054 _115057 s t)). Qed.
Lemma lem5127097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5127098 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term495 _115054 _115057 s t) = (term309 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5127097) (@lem5127096 _115054 _115057 s t)). Qed.
Lemma lem5127099 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term486 _115054 _115057 s t) = (term486 _115054 _115057 s t).
Proof. exact (eq_refl (term486 _115054 _115057 s t)). Qed.
Lemma lem5127100 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term490 _115054 _115057 s t) = (term487 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5127098 _115054 _115057 s t) (@lem5127099 _115054 _115057 s t)). Qed.
Lemma lem5127101 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5127102 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term496 _115054 _115057 s t) = (term497 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5127101) (@lem5127100 _115054 _115057 s t)). Qed.
Lemma lem5127103 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term492 _115054 _115057 s t f) = (term306 _115054 _115057 f s t).
Proof. exact (eq_refl (term492 _115054 _115057 s t f)). Qed.
Lemma lem5127104 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5127105 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term498 _115054 _115057 s t f) = (term499 _115054 _115057 f s t).
Proof. exact (MK_COMB (@lem5127104) (@lem5127103 _115054 _115057 f s t)). Qed.
Lemma lem5127106 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term486 _115054 _115057 s t) = (term486 _115054 _115057 s t).
Proof. exact (eq_refl (term486 _115054 _115057 s t)). Qed.
Lemma lem5127107 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term500 _115054 _115057 f s t) = (term501 _115054 _115057 f s t).
Proof. exact (MK_COMB (@lem5127105 _115054 _115057 f s t) (@lem5127106 _115054 _115057 s t)). Qed.
Lemma lem5127108 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term502 _115054 _115057 s t) = (term503 _115054 _115057 s t).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5127107 _115054 _115057 f s t)). Qed.
Lemma lem5127109 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5127110 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term491 _115054 _115057 s t) = (term504 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5127109 _115054 _115057) (@lem5127108 _115054 _115057 s t)). Qed.
Lemma lem5127111 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term490 _115054 _115057 s t) = (term491 _115054 _115057 s t)) = ((term487 _115054 _115057 s t) = (term504 _115054 _115057 s t)).
Proof. exact (MK_COMB (@lem5127102 _115054 _115057 s t) (@lem5127110 _115054 _115057 s t)). Qed.
Lemma lem5127112 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term487 _115054 _115057 s t) = (term504 _115054 _115057 s t).
Proof. exact (EQ_MP (@lem5127111 _115054 _115057 s t) (@lem5127092 _115054 _115057 s t)). Qed.
Lemma lem5127116 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5127117 {_115054 _115057 : Type'} (P : type805 _115054 _115057) (Q : Prop) : (term505 _115054 _115057 P Q) = (term506 _115054 _115057 P Q).
Proof. exact (@lem5127116 (_115057 -> _115054) P Q). Qed.
Lemma lem5127118 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term507 _115054 _115057 f s t) = (term508 _115054 _115057 f s t).
Proof. exact (@lem5127117 _115054 _115057 (term305 _115054 _115057 f s t) (term486 _115054 _115057 s t)). Qed.
Lemma lem5127119 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term509 _115054 _115057 f s t g) = (term304 _115054 _115057 g f s t).
Proof. exact (eq_refl (term509 _115054 _115057 f s t g)). Qed.
Lemma lem5127120 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term510 _115054 _115057 f s t) = (term305 _115054 _115057 f s t).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5127119 _115054 _115057 g f s t)). Qed.
Lemma lem5127121 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5127122 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term511 _115054 _115057 f s t) = (term306 _115054 _115057 f s t).
Proof. exact (MK_COMB (@lem5127121 _115054 _115057) (@lem5127120 _115054 _115057 f s t)). Qed.
Lemma lem5127123 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5127124 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term512 _115054 _115057 f s t) = (term499 _115054 _115057 f s t).
Proof. exact (MK_COMB (@lem5127123) (@lem5127122 _115054 _115057 f s t)). Qed.
Lemma lem5127125 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term486 _115054 _115057 s t) = (term486 _115054 _115057 s t).
Proof. exact (eq_refl (term486 _115054 _115057 s t)). Qed.
Lemma lem5127126 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term507 _115054 _115057 f s t) = (term501 _115054 _115057 f s t).
Proof. exact (MK_COMB (@lem5127124 _115054 _115057 f s t) (@lem5127125 _115054 _115057 s t)). Qed.
Lemma lem5127127 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5127128 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term513 _115054 _115057 f s t) = (term514 _115054 _115057 f s t).
Proof. exact (MK_COMB (@lem5127127) (@lem5127126 _115054 _115057 f s t)). Qed.
Lemma lem5127129 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term509 _115054 _115057 f s t g) = (term304 _115054 _115057 g f s t).
Proof. exact (eq_refl (term509 _115054 _115057 f s t g)). Qed.
Lemma lem5127130 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5127131 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term515 _115054 _115057 f s t g) = (term516 _115054 _115057 g f s t).
Proof. exact (MK_COMB (@lem5127130) (@lem5127129 _115054 _115057 g f s t)). Qed.
Lemma lem5127132 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term486 _115054 _115057 s t) = (term486 _115054 _115057 s t).
Proof. exact (eq_refl (term486 _115054 _115057 s t)). Qed.
Lemma lem5127133 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term517 _115054 _115057 f g s t) = (term518 _115054 _115057 g f s t).
Proof. exact (MK_COMB (@lem5127131 _115054 _115057 g f s t) (@lem5127132 _115054 _115057 s t)). Qed.
Lemma lem5127134 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term519 _115054 _115057 f s t) = (term520 _115054 _115057 f s t).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5127133 _115054 _115057 g f s t)). Qed.
Lemma lem5127135 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5127136 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term508 _115054 _115057 f s t) = (term521 _115054 _115057 f s t).
Proof. exact (MK_COMB (@lem5127135 _115054 _115057) (@lem5127134 _115054 _115057 f s t)). Qed.
Lemma lem5127137 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term507 _115054 _115057 f s t) = (term508 _115054 _115057 f s t)) = ((term501 _115054 _115057 f s t) = (term521 _115054 _115057 f s t)).
Proof. exact (MK_COMB (@lem5127128 _115054 _115057 f s t) (@lem5127136 _115054 _115057 f s t)). Qed.
Lemma lem5127138 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term501 _115054 _115057 f s t) = (term521 _115054 _115057 f s t).
Proof. exact (EQ_MP (@lem5127137 _115054 _115057 f s t) (@lem5127118 _115054 _115057 f s t)). Qed.
Lemma lem5127142 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5127143 {_115054 _115057 : Type'} (P : type194 _115054 _115057) (Q : Prop) : (term522 _115054 _115057 P Q) = (term523 _115054 _115057 P Q).
Proof. exact (@lem5127142 (type779 _115054 _115057) P Q). Qed.
Lemma lem5127144 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term524 _115054 _115057 g f s t) = (term525 _115054 _115057 g f s t).
Proof. exact (@lem5127143 _115054 _115057 (term303 _115054 _115057 g f s t) (term486 _115054 _115057 s t)). Qed.
Lemma lem5127145 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term526 _115054 _115057 g f s t x) = (term301 _115054 _115057 g f s t x).
Proof. exact (eq_refl (term526 _115054 _115057 g f s t x)). Qed.
Lemma lem5127146 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term527 _115054 _115057 g f s t) = (term303 _115054 _115057 g f s t).
Proof. exact (fun_ext (fun x : type779 _115054 _115057 => @lem5127145 _115054 _115057 g f s t x)). Qed.
Lemma lem5127147 {_115054 _115057 : Type'} : (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054)) = (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054))). Qed.
Lemma lem5127148 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term528 _115054 _115057 g f s t) = (term304 _115054 _115057 g f s t).
Proof. exact (MK_COMB (@lem5127147 _115054 _115057) (@lem5127146 _115054 _115057 g f s t)). Qed.
Lemma lem5127149 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5127150 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term529 _115054 _115057 g f s t) = (term516 _115054 _115057 g f s t).
Proof. exact (MK_COMB (@lem5127149) (@lem5127148 _115054 _115057 g f s t)). Qed.
Lemma lem5127151 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term486 _115054 _115057 s t) = (term486 _115054 _115057 s t).
Proof. exact (eq_refl (term486 _115054 _115057 s t)). Qed.
Lemma lem5127152 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term524 _115054 _115057 g f s t) = (term518 _115054 _115057 g f s t).
Proof. exact (MK_COMB (@lem5127150 _115054 _115057 g f s t) (@lem5127151 _115054 _115057 s t)). Qed.
Lemma lem5127153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5127154 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term530 _115054 _115057 g f s t) = (term531 _115054 _115057 g f s t).
Proof. exact (MK_COMB (@lem5127153) (@lem5127152 _115054 _115057 g f s t)). Qed.
Lemma lem5127155 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term526 _115054 _115057 g f s t x) = (term301 _115054 _115057 g f s t x).
Proof. exact (eq_refl (term526 _115054 _115057 g f s t x)). Qed.
Lemma lem5127156 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5127157 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term532 _115054 _115057 g f s t x) = (term533 _115054 _115057 g f s t x).
Proof. exact (MK_COMB (@lem5127156) (@lem5127155 _115054 _115057 g f s t x)). Qed.
Lemma lem5127158 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term486 _115054 _115057 s t) = (term486 _115054 _115057 s t).
Proof. exact (eq_refl (term486 _115054 _115057 s t)). Qed.
Lemma lem5127159 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term534 _115054 _115057 g f x s t) = (term535 _115054 _115057 g f x s t).
Proof. exact (MK_COMB (@lem5127157 _115054 _115057 g f s t x) (@lem5127158 _115054 _115057 s t)). Qed.
Lemma lem5127160 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term536 _115054 _115057 g f s t) = (term537 _115054 _115057 g f s t).
Proof. exact (fun_ext (fun x : type779 _115054 _115057 => @lem5127159 _115054 _115057 g f x s t)). Qed.
Lemma lem5127161 {_115054 _115057 : Type'} : (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054)) = (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054))). Qed.
Lemma lem5127162 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term525 _115054 _115057 g f s t) = (term538 _115054 _115057 g f s t).
Proof. exact (MK_COMB (@lem5127161 _115054 _115057) (@lem5127160 _115054 _115057 g f s t)). Qed.
Lemma lem5127163 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term524 _115054 _115057 g f s t) = (term525 _115054 _115057 g f s t)) = ((term518 _115054 _115057 g f s t) = (term538 _115054 _115057 g f s t)).
Proof. exact (MK_COMB (@lem5127154 _115054 _115057 g f s t) (@lem5127162 _115054 _115057 g f s t)). Qed.
Lemma lem5127164 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term518 _115054 _115057 g f s t) = (term538 _115054 _115057 g f s t).
Proof. exact (EQ_MP (@lem5127163 _115054 _115057 g f s t) (@lem5127144 _115054 _115057 g f s t)). Qed.
Lemma lem5127166 {A : Type'} (P : Prop) (Q : A -> Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5127167 {_115054 _115057 : Type'} (P : Prop) (Q : type118 _115054 _115057) : (term539 _115054 _115057 P Q) = (term540 _115054 _115057 P Q).
Proof. exact (@lem5127166 (type569 _115054 _115057) P Q). Qed.
Lemma lem5127168 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term541 _115054 _115057 g f x s t) = (term542 _115054 _115057 g f x s t).
Proof. exact (@lem5127167 _115054 _115057 (term301 _115054 _115057 g f s t x) (term485 _115054 _115057 s t)). Qed.
Lemma lem5127169 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term543 _115054 _115057 s t x) = (term484 _115054 _115057 x s t).
Proof. exact (eq_refl (term543 _115054 _115057 s t x)). Qed.
Lemma lem5127170 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term544 _115054 _115057 s t) = (term485 _115054 _115057 s t).
Proof. exact (fun_ext (fun x : type569 _115054 _115057 => @lem5127169 _115054 _115057 x s t)). Qed.
Lemma lem5127171 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> _115054)) = (@ex ((_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> _115054))). Qed.
Lemma lem5127172 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term545 _115054 _115057 s t) = (term486 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5127171 _115054 _115057) (@lem5127170 _115054 _115057 s t)). Qed.
Lemma lem5127173 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term533 _115054 _115057 g f s t x) = (term533 _115054 _115057 g f s t x).
Proof. exact (eq_refl (term533 _115054 _115057 g f s t x)). Qed.
Lemma lem5127174 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term541 _115054 _115057 g f x s t) = (term535 _115054 _115057 g f x s t).
Proof. exact (MK_COMB (@lem5127173 _115054 _115057 g f s t x) (@lem5127172 _115054 _115057 s t)). Qed.
Lemma lem5127175 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5127176 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term546 _115054 _115057 g f x s t) = (term547 _115054 _115057 g f x s t).
Proof. exact (MK_COMB (@lem5127175) (@lem5127174 _115054 _115057 g f x s t)). Qed.
Lemma lem5127177 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term543 _115054 _115057 s t x) = (term484 _115054 _115057 x s t).
Proof. exact (eq_refl (term543 _115054 _115057 s t x)). Qed.
Lemma lem5127178 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term533 _115054 _115057 g f s t x) = (term533 _115054 _115057 g f s t x).
Proof. exact (eq_refl (term533 _115054 _115057 g f s t x)). Qed.
Lemma lem5127179 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term548 _115054 _115057 g f x s t x') = (term549 _115054 _115057 g f x x' s t).
Proof. exact (MK_COMB (@lem5127178 _115054 _115057 g f s t x) (@lem5127177 _115054 _115057 x' s t)). Qed.
Lemma lem5127180 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term550 _115054 _115057 g f x s t) = (term551 _115054 _115057 g f x s t).
Proof. exact (fun_ext (fun x' : type569 _115054 _115057 => @lem5127179 _115054 _115057 g f x x' s t)). Qed.
Lemma lem5127181 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> _115054)) = (@ex ((_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> _115054))). Qed.
Lemma lem5127182 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term542 _115054 _115057 g f x s t) = (term552 _115054 _115057 g f x s t).
Proof. exact (MK_COMB (@lem5127181 _115054 _115057) (@lem5127180 _115054 _115057 g f x s t)). Qed.
Lemma lem5127183 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term541 _115054 _115057 g f x s t) = (term542 _115054 _115057 g f x s t)) = ((term535 _115054 _115057 g f x s t) = (term552 _115054 _115057 g f x s t)).
Proof. exact (MK_COMB (@lem5127176 _115054 _115057 g f x s t) (@lem5127182 _115054 _115057 g f x s t)). Qed.
Lemma lem5127184 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term535 _115054 _115057 g f x s t) = (term552 _115054 _115057 g f x s t).
Proof. exact (EQ_MP (@lem5127183 _115054 _115057 g f x s t) (@lem5127168 _115054 _115057 g f x s t)). Qed.
Lemma lem5127186 {A : Type'} (P : Prop) (Q : A -> Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5127187 {_115054 _115057 : Type'} (P : Prop) (Q : type101 _115054 _115057) : (term553 _115054 _115057 P Q) = (term554 _115054 _115057 P Q).
Proof. exact (@lem5127186 (type530 _115054 _115057) P Q). Qed.
Lemma lem5127188 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term555 _115054 _115057 g f x x' s t) = (term556 _115054 _115057 g f x x' s t).
Proof. exact (@lem5127187 _115054 _115057 (term301 _115054 _115057 g f s t x) (term483 _115054 _115057 x' s t)). Qed.
Lemma lem5127189 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term557 _115054 _115057 x s t x') = (term482 _115054 _115057 x x' s t).
Proof. exact (eq_refl (term557 _115054 _115057 x s t x')). Qed.
Lemma lem5127190 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term558 _115054 _115057 x s t) = (term483 _115054 _115057 x s t).
Proof. exact (fun_ext (fun x' : type530 _115054 _115057 => @lem5127189 _115054 _115057 x x' s t)). Qed.
Lemma lem5127191 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054)) = (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054))). Qed.
Lemma lem5127192 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term559 _115054 _115057 x s t) = (term484 _115054 _115057 x s t).
Proof. exact (MK_COMB (@lem5127191 _115054 _115057) (@lem5127190 _115054 _115057 x s t)). Qed.
Lemma lem5127193 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term533 _115054 _115057 g f s t x) = (term533 _115054 _115057 g f s t x).
Proof. exact (eq_refl (term533 _115054 _115057 g f s t x)). Qed.
Lemma lem5127194 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term555 _115054 _115057 g f x x' s t) = (term549 _115054 _115057 g f x x' s t).
Proof. exact (MK_COMB (@lem5127193 _115054 _115057 g f s t x) (@lem5127192 _115054 _115057 x' s t)). Qed.
Lemma lem5127195 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5127196 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term560 _115054 _115057 g f x x' s t) = (term561 _115054 _115057 g f x x' s t).
Proof. exact (MK_COMB (@lem5127195) (@lem5127194 _115054 _115057 g f x x' s t)). Qed.
Lemma lem5127197 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term557 _115054 _115057 x s t x') = (term482 _115054 _115057 x x' s t).
Proof. exact (eq_refl (term557 _115054 _115057 x s t x')). Qed.
Lemma lem5127198 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term533 _115054 _115057 g f s t x) = (term533 _115054 _115057 g f s t x).
Proof. exact (eq_refl (term533 _115054 _115057 g f s t x)). Qed.
Lemma lem5127199 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term562 _115054 _115057 g f x x' s t x'') = (term563 _115054 _115057 g f x x' x'' s t).
Proof. exact (MK_COMB (@lem5127198 _115054 _115057 g f s t x) (@lem5127197 _115054 _115057 x' x'' s t)). Qed.
Lemma lem5127200 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term564 _115054 _115057 g f x x' s t) = (term565 _115054 _115057 g f x x' s t).
Proof. exact (fun_ext (fun x'' : type530 _115054 _115057 => @lem5127199 _115054 _115057 g f x x' x'' s t)). Qed.
Lemma lem5127201 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054)) = (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054))). Qed.
Lemma lem5127202 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term556 _115054 _115057 g f x x' s t) = (term566 _115054 _115057 g f x x' s t).
Proof. exact (MK_COMB (@lem5127201 _115054 _115057) (@lem5127200 _115054 _115057 g f x x' s t)). Qed.
Lemma lem5127203 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term555 _115054 _115057 g f x x' s t) = (term556 _115054 _115057 g f x x' s t)) = ((term549 _115054 _115057 g f x x' s t) = (term566 _115054 _115057 g f x x' s t)).
Proof. exact (MK_COMB (@lem5127196 _115054 _115057 g f x x' s t) (@lem5127202 _115054 _115057 g f x x' s t)). Qed.
Lemma lem5127204 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term549 _115054 _115057 g f x x' s t) = (term566 _115054 _115057 g f x x' s t).
Proof. exact (EQ_MP (@lem5127203 _115054 _115057 g f x x' s t) (@lem5127188 _115054 _115057 g f x x' s t)). Qed.
Lemma lem5127206 {A : Type'} (P : Prop) (Q : A -> Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5127207 {_115054 _115057 : Type'} (P : Prop) (Q : type805 _115054 _115057) : (term567 _115054 _115057 P Q) = (term568 _115054 _115057 P Q).
Proof. exact (@lem5127206 (_115057 -> _115054) P Q). Qed.
Lemma lem5127208 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term569 _115054 _115057 g f x x' x'' s t) = (term570 _115054 _115057 g f x x' x'' s t).
Proof. exact (@lem5127207 _115054 _115057 (term301 _115054 _115057 g f s t x) (term481 _115054 _115057 x' x'' s t)). Qed.
Lemma lem5127209 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g : _115057 -> _115054) : (term571 _115054 _115057 x x' s t g) = (term480 _115054 _115057 x x' s t g).
Proof. exact (eq_refl (term571 _115054 _115057 x x' s t g)). Qed.
Lemma lem5127210 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term572 _115054 _115057 x x' s t) = (term481 _115054 _115057 x x' s t).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5127209 _115054 _115057 x x' s t g)). Qed.
Lemma lem5127211 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5127212 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term573 _115054 _115057 x x' s t) = (term482 _115054 _115057 x x' s t).
Proof. exact (MK_COMB (@lem5127211 _115054 _115057) (@lem5127210 _115054 _115057 x x' s t)). Qed.
Lemma lem5127213 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term533 _115054 _115057 g f s t x) = (term533 _115054 _115057 g f s t x).
Proof. exact (eq_refl (term533 _115054 _115057 g f s t x)). Qed.
Lemma lem5127214 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term569 _115054 _115057 g f x x' x'' s t) = (term563 _115054 _115057 g f x x' x'' s t).
Proof. exact (MK_COMB (@lem5127213 _115054 _115057 g f s t x) (@lem5127212 _115054 _115057 x' x'' s t)). Qed.
Lemma lem5127215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5127216 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term574 _115054 _115057 g f x x' x'' s t) = (term575 _115054 _115057 g f x x' x'' s t).
Proof. exact (MK_COMB (@lem5127215) (@lem5127214 _115054 _115057 g f x x' x'' s t)). Qed.
Lemma lem5127217 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) : (term571 _115054 _115057 x x' s t g') = (term480 _115054 _115057 x x' s t g').
Proof. exact (eq_refl (term571 _115054 _115057 x x' s t g')). Qed.
Lemma lem5127218 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term533 _115054 _115057 g f s t x) = (term533 _115054 _115057 g f s t x).
Proof. exact (eq_refl (term533 _115054 _115057 g f s t x)). Qed.
Lemma lem5127219 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) : (term576 _115054 _115057 g f x x' x'' s t g') = (term577 _115054 _115057 g f x x' x'' s t g').
Proof. exact (MK_COMB (@lem5127218 _115054 _115057 g f s t x) (@lem5127217 _115054 _115057 x' x'' s t g')). Qed.
Lemma lem5127220 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term578 _115054 _115057 g f x x' x'' s t) = (term579 _115054 _115057 g f x x' x'' s t).
Proof. exact (fun_ext (fun g' : _115057 -> _115054 => @lem5127219 _115054 _115057 g f x x' x'' s t g')). Qed.
Lemma lem5127221 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5127222 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term570 _115054 _115057 g f x x' x'' s t) = (term580 _115054 _115057 g f x x' x'' s t).
Proof. exact (MK_COMB (@lem5127221 _115054 _115057) (@lem5127220 _115054 _115057 g f x x' x'' s t)). Qed.
Lemma lem5127223 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : ((term569 _115054 _115057 g f x x' x'' s t) = (term570 _115054 _115057 g f x x' x'' s t)) = ((term563 _115054 _115057 g f x x' x'' s t) = (term580 _115054 _115057 g f x x' x'' s t)).
Proof. exact (MK_COMB (@lem5127216 _115054 _115057 g f x x' x'' s t) (@lem5127222 _115054 _115057 g f x x' x'' s t)). Qed.
Lemma lem5127224 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term563 _115054 _115057 g f x x' x'' s t) = (term580 _115054 _115057 g f x x' x'' s t).
Proof. exact (EQ_MP (@lem5127223 _115054 _115057 g f x x' x'' s t) (@lem5127208 _115054 _115057 g f x x' x'' s t)). Qed.
Lemma lem5127226 {A : Type'} (P : Prop) (Q : A -> Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5127227 {_115054 _115057 : Type'} (P : Prop) (Q : type572 _115054 _115057) : (term581 _115054 _115057 P Q) = (term582 _115054 _115057 P Q).
Proof. exact (@lem5127226 (_115054 -> _115057) P Q). Qed.
Lemma lem5127228 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) : (term583 _115054 _115057 g f x x' x'' s t g') = (term584 _115054 _115057 g f x x' x'' s t g').
Proof. exact (@lem5127227 _115054 _115057 (term301 _115054 _115057 g f s t x) (term479 _115054 _115057 x' x'' s t g')). Qed.
Lemma lem5127229 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g : _115054 -> _115057) : (term585 _115054 _115057 x x' s t g' g) = (term477 _115054 _115057 x x' s t g' g).
Proof. exact (eq_refl (term585 _115054 _115057 x x' s t g' g)). Qed.
Lemma lem5127230 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) : (term586 _115054 _115057 x x' s t g') = (term479 _115054 _115057 x x' s t g').
Proof. exact (fun_ext (fun g : _115054 -> _115057 => @lem5127229 _115054 _115057 x x' s t g' g)). Qed.
Lemma lem5127231 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5127232 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) : (term587 _115054 _115057 x x' s t g') = (term480 _115054 _115057 x x' s t g').
Proof. exact (MK_COMB (@lem5127231 _115054 _115057) (@lem5127230 _115054 _115057 x x' s t g')). Qed.
Lemma lem5127233 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term533 _115054 _115057 g f s t x) = (term533 _115054 _115057 g f s t x).
Proof. exact (eq_refl (term533 _115054 _115057 g f s t x)). Qed.
Lemma lem5127234 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) : (term583 _115054 _115057 g f x x' x'' s t g') = (term577 _115054 _115057 g f x x' x'' s t g').
Proof. exact (MK_COMB (@lem5127233 _115054 _115057 g f s t x) (@lem5127232 _115054 _115057 x' x'' s t g')). Qed.
Lemma lem5127235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5127236 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) : (term588 _115054 _115057 g f x x' x'' s t g') = (term589 _115054 _115057 g f x x' x'' s t g').
Proof. exact (MK_COMB (@lem5127235) (@lem5127234 _115054 _115057 g f x x' x'' s t g')). Qed.
Lemma lem5127237 {_115054 _115057 : Type'} (x : type569 _115054 _115057) (x' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g : _115054 -> _115057) : (term585 _115054 _115057 x x' s t g' g) = (term477 _115054 _115057 x x' s t g' g).
Proof. exact (eq_refl (term585 _115054 _115057 x x' s t g' g)). Qed.
Lemma lem5127238 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term533 _115054 _115057 g f s t x) = (term533 _115054 _115057 g f s t x).
Proof. exact (eq_refl (term533 _115054 _115057 g f s t x)). Qed.
Lemma lem5127239 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) : (term590 _115054 _115057 g f x x' x'' s t g' g'') = (term591 _115054 _115057 g f x x' x'' s t g' g'').
Proof. exact (MK_COMB (@lem5127238 _115054 _115057 g f s t x) (@lem5127237 _115054 _115057 x' x'' s t g' g'')). Qed.
Lemma lem5127240 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) : (term592 _115054 _115057 g f x x' x'' s t g') = (term593 _115054 _115057 g f x x' x'' s t g').
Proof. exact (fun_ext (fun g'' : _115054 -> _115057 => @lem5127239 _115054 _115057 g f x x' x'' s t g' g'')). Qed.
Lemma lem5127241 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5127242 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) : (term584 _115054 _115057 g f x x' x'' s t g') = (term594 _115054 _115057 g f x x' x'' s t g').
Proof. exact (MK_COMB (@lem5127241 _115054 _115057) (@lem5127240 _115054 _115057 g f x x' x'' s t g')). Qed.
Lemma lem5127243 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) : ((term583 _115054 _115057 g f x x' x'' s t g') = (term584 _115054 _115057 g f x x' x'' s t g')) = ((term577 _115054 _115057 g f x x' x'' s t g') = (term594 _115054 _115057 g f x x' x'' s t g')).
Proof. exact (MK_COMB (@lem5127236 _115054 _115057 g f x x' x'' s t g') (@lem5127242 _115054 _115057 g f x x' x'' s t g')). Qed.
Lemma lem5127244 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) : (term577 _115054 _115057 g f x x' x'' s t g') = (term594 _115054 _115057 g f x x' x'' s t g').
Proof. exact (EQ_MP (@lem5127243 _115054 _115057 g f x x' x'' s t g') (@lem5127228 _115054 _115057 g f x x' x'' s t g')). Qed.
Lemma lem5127245 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term579 _115054 _115057 g f x x' x'' s t) = (term595 _115054 _115057 g f x x' x'' s t).
Proof. exact (fun_ext (fun g' : _115057 -> _115054 => @lem5127244 _115054 _115057 g f x x' x'' s t g')). Qed.
Lemma lem5127246 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5127247 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term580 _115054 _115057 g f x x' x'' s t) = (term596 _115054 _115057 g f x x' x'' s t).
Proof. exact (MK_COMB (@lem5127246 _115054 _115057) (@lem5127245 _115054 _115057 g f x x' x'' s t)). Qed.
Lemma lem5127248 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term563 _115054 _115057 g f x x' x'' s t) = (term596 _115054 _115057 g f x x' x'' s t).
Proof. exact (TRANS (@lem5127224 _115054 _115057 g f x x' x'' s t) (@lem5127247 _115054 _115057 g f x x' x'' s t)). Qed.
Lemma lem5127249 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term565 _115054 _115057 g f x x' s t) = (term597 _115054 _115057 g f x x' s t).
Proof. exact (fun_ext (fun x'' : type530 _115054 _115057 => @lem5127248 _115054 _115057 g f x x' x'' s t)). Qed.
Lemma lem5127250 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054)) = (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054))). Qed.
Lemma lem5127251 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term566 _115054 _115057 g f x x' s t) = (term598 _115054 _115057 g f x x' s t).
Proof. exact (MK_COMB (@lem5127250 _115054 _115057) (@lem5127249 _115054 _115057 g f x x' s t)). Qed.
Lemma lem5127252 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term549 _115054 _115057 g f x x' s t) = (term598 _115054 _115057 g f x x' s t).
Proof. exact (TRANS (@lem5127204 _115054 _115057 g f x x' s t) (@lem5127251 _115054 _115057 g f x x' s t)). Qed.
Lemma lem5127253 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term551 _115054 _115057 g f x s t) = (term599 _115054 _115057 g f x s t).
Proof. exact (fun_ext (fun x' : type569 _115054 _115057 => @lem5127252 _115054 _115057 g f x x' s t)). Qed.
Lemma lem5127254 {_115054 _115057 : Type'} : (@ex ((_115054 -> _115057) -> _115054)) = (@ex ((_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115054 -> _115057) -> _115054))). Qed.
Lemma lem5127255 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term552 _115054 _115057 g f x s t) = (term600 _115054 _115057 g f x s t).
Proof. exact (MK_COMB (@lem5127254 _115054 _115057) (@lem5127253 _115054 _115057 g f x s t)). Qed.
Lemma lem5127256 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term535 _115054 _115057 g f x s t) = (term600 _115054 _115057 g f x s t).
Proof. exact (TRANS (@lem5127184 _115054 _115057 g f x s t) (@lem5127255 _115054 _115057 g f x s t)). Qed.
Lemma lem5127257 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term537 _115054 _115057 g f s t) = (term601 _115054 _115057 g f s t).
Proof. exact (fun_ext (fun x : type779 _115054 _115057 => @lem5127256 _115054 _115057 g f x s t)). Qed.
Lemma lem5127258 {_115054 _115057 : Type'} : (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054)) = (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054)).
Proof. exact (eq_refl (@ex ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054))). Qed.
Lemma lem5127259 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term538 _115054 _115057 g f s t) = (term602 _115054 _115057 g f s t).
Proof. exact (MK_COMB (@lem5127258 _115054 _115057) (@lem5127257 _115054 _115057 g f s t)). Qed.
Lemma lem5127260 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term518 _115054 _115057 g f s t) = (term602 _115054 _115057 g f s t).
Proof. exact (TRANS (@lem5127164 _115054 _115057 g f s t) (@lem5127259 _115054 _115057 g f s t)). Qed.
Lemma lem5127261 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term520 _115054 _115057 f s t) = (term603 _115054 _115057 f s t).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5127260 _115054 _115057 g f s t)). Qed.
Lemma lem5127262 {_115054 _115057 : Type'} : (@ex (_115057 -> _115054)) = (@ex (_115057 -> _115054)).
Proof. exact (eq_refl (@ex (_115057 -> _115054))). Qed.
Lemma lem5127263 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term521 _115054 _115057 f s t) = (term604 _115054 _115057 f s t).
Proof. exact (MK_COMB (@lem5127262 _115054 _115057) (@lem5127261 _115054 _115057 f s t)). Qed.
Lemma lem5127264 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) : (term501 _115054 _115057 f s t) = (term604 _115054 _115057 f s t).
Proof. exact (TRANS (@lem5127138 _115054 _115057 f s t) (@lem5127263 _115054 _115057 f s t)). Qed.
Lemma lem5127265 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term503 _115054 _115057 s t) = (term605 _115054 _115057 s t).
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5127264 _115054 _115057 f s t)). Qed.
Lemma lem5127266 {_115054 _115057 : Type'} : (@ex (_115054 -> _115057)) = (@ex (_115054 -> _115057)).
Proof. exact (eq_refl (@ex (_115054 -> _115057))). Qed.
Lemma lem5127267 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term504 _115054 _115057 s t) = (term606 _115054 _115057 s t).
Proof. exact (MK_COMB (@lem5127266 _115054 _115057) (@lem5127265 _115054 _115057 s t)). Qed.
Lemma lem5127268 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term487 _115054 _115057 s t) = (term606 _115054 _115057 s t).
Proof. exact (TRANS (@lem5127112 _115054 _115057 s t) (@lem5127267 _115054 _115057 s t)). Qed.
Lemma lem5127270 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term188 _115054 _115057 s t) = (term606 _115054 _115057 s t).
Proof. exact (TRANS (@lem5127086 _115054 _115057 s t) (@lem5127268 _115054 _115057 s t)). Qed.
Lemma lem5127271 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term85 _115054 _115057 s t) = (term606 _115054 _115057 s t).
Proof. exact (TRANS (@lem5126251 _115054 _115057 s t) (@lem5127270 _115054 _115057 s t)). Qed.
Lemma lem5127272 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (h1 : term85 _115054 _115057 s t) : term606 _115054 _115057 s t.
Proof. exact (EQ_MP (@lem5127271 _115054 _115057 s t) (@lem5126089 _115054 _115057 s t h1)). Qed.
Lemma lem5127273 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (h1 : term604 _115054 _115057 f s t) : term604 _115054 _115057 f s t.
Proof. exact (h1). Qed.
Lemma lem5127274 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (h1 : term602 _115054 _115057 g f s t) : term602 _115054 _115057 g f s t.
Proof. exact (h1). Qed.
Lemma lem5127275 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (h1 : term600 _115054 _115057 g f x s t) : term600 _115054 _115057 g f x s t.
Proof. exact (h1). Qed.
Lemma lem5127276 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (h1 : term598 _115054 _115057 g f x x' s t) : term598 _115054 _115057 g f x x' s t.
Proof. exact (h1). Qed.
Lemma lem5127277 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (h1 : term596 _115054 _115057 g f x x' x'' s t) : term596 _115054 _115057 g f x x' x'' s t.
Proof. exact (h1). Qed.
Lemma lem5127278 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (h1 : term594 _115054 _115057 g f x x' x'' s t g') : term594 _115054 _115057 g f x x' x'' s t g'.
Proof. exact (h1). Qed.
Lemma lem5127279 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term591 _115054 _115057 g f x x' x'' s t g' g'') : term591 _115054 _115057 g f x x' x'' s t g' g''.
Proof. exact (h1). Qed.
Lemma lem5127280 {_115054 : Type'} : (@eq _115054) = (@eq _115054).
Proof. exact (eq_refl (@eq _115054)). Qed.
Lemma lem5127281 {_115054 _115057 : Type'} (g' : _115057 -> _115054) : g' = g'.
Proof. exact (eq_refl g'). Qed.
Lemma lem5127286 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127287 {_115054 _115057 : Type'} (f : _115054 -> _115057) (x : _115054) : (f x) = (@I (_115054 -> _115057) f x).
Proof. exact (@lem5127286 _115054 _115057 f x). Qed.
Lemma lem5127289 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (x : _115054) : (g'' x) = (@I (_115054 -> _115057) g'' x).
Proof. exact (@lem5127287 _115054 _115057 g'' x). Qed.
Lemma lem5127290 {_115054 _115057 : Type'} (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (x : _115054) : (term103 _115054 _115057 g' g'' x) = (term607 _115054 _115057 g' g'' x).
Proof. exact (MK_COMB (@lem5127281 _115054 _115057 g') (@lem5127289 _115054 _115057 g'' x)). Qed.
Lemma lem5127292 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127293 {_115054 _115057 : Type'} (f : _115057 -> _115054) (x : _115057) : (f x) = (@I (_115057 -> _115054) f x).
Proof. exact (@lem5127292 _115057 _115054 f x). Qed.
Lemma lem5127294 {_115054 _115057 : Type'} (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (x : _115054) : (term607 _115054 _115057 g' g'' x) = (term608 _115054 _115057 g' g'' x).
Proof. exact (@lem5127293 _115054 _115057 g' (@I (_115054 -> _115057) g'' x)). Qed.
Lemma lem5127295 {_115054 _115057 : Type'} (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (x : _115054) : (term103 _115054 _115057 g' g'' x) = (term608 _115054 _115057 g' g'' x).
Proof. exact (TRANS (@lem5127290 _115054 _115057 g' g'' x) (@lem5127294 _115054 _115057 g' g'' x)). Qed.
Lemma lem5127296 {_115054 : Type'} (x : _115054) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5127297 {_115054 _115057 : Type'} (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (x : _115054) : (term609 _115054 _115057 g' g'' x) = (term610 _115054 _115057 g' g'' x).
Proof. exact (MK_COMB (@lem5127280 _115054) (@lem5127295 _115054 _115057 g' g'' x)). Qed.
Lemma lem5127298 {_115054 _115057 : Type'} (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (x : _115054) : ((term103 _115054 _115057 g' g'' x) = x) = ((term608 _115054 _115057 g' g'' x) = x).
Proof. exact (MK_COMB (@lem5127297 _115054 _115057 g' g'' x) (@lem5127296 _115054 x)). Qed.
Lemma lem5127299 {_115057 : Type'} : (@IN _115057) = (@IN _115057).
Proof. exact (eq_refl (@IN _115057)). Qed.
Lemma lem5127304 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127305 {_115054 _115057 : Type'} (f : _115054 -> _115057) (x : _115054) : (f x) = (@I (_115054 -> _115057) f x).
Proof. exact (@lem5127304 _115054 _115057 f x). Qed.
Lemma lem5127307 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (x : _115054) : (g'' x) = (@I (_115054 -> _115057) g'' x).
Proof. exact (@lem5127305 _115054 _115057 g'' x). Qed.
Lemma lem5127308 {_115057 : Type'} (t : _115057 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5127309 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (x : _115054) : (term611 _115054 _115057 g'' x) = (term612 _115054 _115057 g'' x).
Proof. exact (MK_COMB (@lem5127299 _115057) (@lem5127307 _115054 _115057 g'' x)). Qed.
Lemma lem5127310 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term88 _115054 _115057 g'' x t) = (term613 _115054 _115057 g'' x t).
Proof. exact (MK_COMB (@lem5127309 _115054 _115057 g'' x) (@lem5127308 _115057 t)). Qed.
Lemma lem5127312 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127313 {_115057 : Type'} (f : type1364 _115057) (x : _115057) : (f x) = (@I (_115057 -> (_115057 -> Prop) -> Prop) f x).
Proof. exact (@lem5127312 _115057 (type686 _115057) f x). Qed.
Lemma lem5127314 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (x : _115054) : (term612 _115054 _115057 g'' x) = (term614 _115054 _115057 g'' x).
Proof. exact (@lem5127313 _115057 (@IN _115057) (@I (_115054 -> _115057) g'' x)). Qed.
Lemma lem5127315 {_115057 : Type'} (t : _115057 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5127316 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term613 _115054 _115057 g'' x t) = (term615 _115054 _115057 g'' x t).
Proof. exact (MK_COMB (@lem5127314 _115054 _115057 g'' x) (@lem5127315 _115057 t)). Qed.
Lemma lem5127318 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127319 {_115057 : Type'} (f : type686 _115057) (x : _115057 -> Prop) : (f x) = (@I ((_115057 -> Prop) -> Prop) f x).
Proof. exact (@lem5127318 (_115057 -> Prop) Prop f x). Qed.
Lemma lem5127320 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term615 _115054 _115057 g'' x t) = (term616 _115054 _115057 g'' x t).
Proof. exact (@lem5127319 _115057 (term614 _115054 _115057 g'' x) t). Qed.
Lemma lem5127321 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term613 _115054 _115057 g'' x t) = (term616 _115054 _115057 g'' x t).
Proof. exact (TRANS (@lem5127316 _115054 _115057 g'' x t) (@lem5127320 _115054 _115057 g'' x t)). Qed.
Lemma lem5127322 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term88 _115054 _115057 g'' x t) = (term616 _115054 _115057 g'' x t).
Proof. exact (TRANS (@lem5127310 _115054 _115057 g'' x t) (@lem5127321 _115054 _115057 g'' x t)). Qed.
Lemma lem5127323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5127324 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term617 _115054 _115057 g'' x t) = (term618 _115054 _115057 g'' x t).
Proof. exact (MK_COMB (@lem5127323) (@lem5127322 _115054 _115057 g'' x t)). Qed.
Lemma lem5127325 {_115054 _115057 : Type'} (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (x : _115054) : (term148 _115054 _115057 t g' g'' x) = (term619 _115054 _115057 t g' g'' x).
Proof. exact (MK_COMB (@lem5127324 _115054 _115057 g'' x t) (@lem5127298 _115054 _115057 g' g'' x)). Qed.
Lemma lem5127326 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5127333 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127334 {_115054 : Type'} (f : type1364 _115054) (x : _115054) : (f x) = (@I (_115054 -> (_115054 -> Prop) -> Prop) f x).
Proof. exact (@lem5127333 _115054 (type686 _115054) f x). Qed.
Lemma lem5127335 {_115054 : Type'} (x : _115054) : (@IN _115054 x) = (@I (_115054 -> (_115054 -> Prop) -> Prop) (@IN _115054) x).
Proof. exact (@lem5127334 _115054 (@IN _115054) x). Qed.
Lemma lem5127336 {_115054 : Type'} (s : _115054 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5127337 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (@IN _115054 x s) = (@I (_115054 -> (_115054 -> Prop) -> Prop) (@IN _115054) x s).
Proof. exact (MK_COMB (@lem5127335 _115054 x) (@lem5127336 _115054 s)). Qed.
Lemma lem5127339 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127340 {_115054 : Type'} (f : type686 _115054) (x : _115054 -> Prop) : (f x) = (@I ((_115054 -> Prop) -> Prop) f x).
Proof. exact (@lem5127339 (_115054 -> Prop) Prop f x). Qed.
Lemma lem5127341 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (@I (_115054 -> (_115054 -> Prop) -> Prop) (@IN _115054) x s) = (term620 _115054 x s).
Proof. exact (@lem5127340 _115054 (@I (_115054 -> (_115054 -> Prop) -> Prop) (@IN _115054) x) s). Qed.
Lemma lem5127343 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (@IN _115054 x s) = (term620 _115054 x s).
Proof. exact (TRANS (@lem5127337 _115054 x s) (@lem5127341 _115054 x s)). Qed.
Lemma lem5127344 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (term621 _115054 x s) = (term622 _115054 x s).
Proof. exact (MK_COMB (@lem5127326) (@lem5127343 _115054 x s)). Qed.
Lemma lem5127345 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5127346 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (term623 _115054 x s) = (term624 _115054 x s).
Proof. exact (MK_COMB (@lem5127345) (@lem5127344 _115054 x s)). Qed.
Lemma lem5127347 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (x : _115054) : (term149 _115054 _115057 s t g' g'' x) = (term625 _115054 _115057 s t g' g'' x).
Proof. exact (MK_COMB (@lem5127346 _115054 x s) (@lem5127325 _115054 _115057 t g' g'' x)). Qed.
Lemma lem5127348 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) : (term157 _115054 _115057 s t g' g'') = (term626 _115054 _115057 s t g' g'').
Proof. exact (fun_ext (fun x : _115054 => @lem5127347 _115054 _115057 s t g' g'' x)). Qed.
Lemma lem5127349 {_115054 : Type'} : (@all _115054) = (@all _115054).
Proof. exact (eq_refl (@all _115054)). Qed.
Lemma lem5127350 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) : (term158 _115054 _115057 s t g' g'') = (term627 _115054 _115057 s t g' g'').
Proof. exact (MK_COMB (@lem5127349 _115054) (@lem5127348 _115054 _115057 s t g' g'')). Qed.
Lemma lem5127351 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5127352 {_115054 : Type'} : (@eq _115054) = (@eq _115054).
Proof. exact (eq_refl (@eq _115054)). Qed.
Lemma lem5127353 {_115054 _115057 : Type'} (g : _115057 -> _115054) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5127354 {_115054 _115057 : Type'} (f : _115054 -> _115057) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5127361 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127362 {_115054 _115057 : Type'} (f : type530 _115054 _115057) (x : _115054 -> _115057) : (f x) = (@I ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054) f x).
Proof. exact (@lem5127361 (_115054 -> _115057) (type802 _115054 _115057) f x). Qed.
Lemma lem5127363 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (x'' f) = (@I ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054) x'' f).
Proof. exact (@lem5127362 _115054 _115057 x'' f). Qed.
Lemma lem5127364 {_115054 _115057 : Type'} (g : _115057 -> _115054) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5127365 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (x'' f g) = (@I ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054) x'' f g).
Proof. exact (MK_COMB (@lem5127363 _115054 _115057 x'' f) (@lem5127364 _115054 _115057 g)). Qed.
Lemma lem5127367 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127368 {_115054 _115057 : Type'} (f : type802 _115054 _115057) (x : _115057 -> _115054) : (f x) = (@I ((_115057 -> _115054) -> _115054) f x).
Proof. exact (@lem5127367 (_115057 -> _115054) _115054 f x). Qed.
Lemma lem5127369 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (@I ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054) x'' f g) = (term628 _115054 _115057 x'' f g).
Proof. exact (@lem5127368 _115054 _115057 (@I ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054) x'' f) g). Qed.
Lemma lem5127371 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (x'' f g) = (term628 _115054 _115057 x'' f g).
Proof. exact (TRANS (@lem5127365 _115054 _115057 x'' f g) (@lem5127369 _115054 _115057 x'' f g)). Qed.
Lemma lem5127372 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term629 _115054 _115057 x'' f g) = (term630 _115054 _115057 x'' f g).
Proof. exact (MK_COMB (@lem5127354 _115054 _115057 f) (@lem5127371 _115054 _115057 x'' f g)). Qed.
Lemma lem5127374 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127375 {_115054 _115057 : Type'} (f : _115054 -> _115057) (x : _115054) : (f x) = (@I (_115054 -> _115057) f x).
Proof. exact (@lem5127374 _115054 _115057 f x). Qed.
Lemma lem5127376 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term630 _115054 _115057 x'' f g) = (term631 _115054 _115057 x'' f g).
Proof. exact (@lem5127375 _115054 _115057 f (term628 _115054 _115057 x'' f g)). Qed.
Lemma lem5127377 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term629 _115054 _115057 x'' f g) = (term631 _115054 _115057 x'' f g).
Proof. exact (TRANS (@lem5127372 _115054 _115057 x'' f g) (@lem5127376 _115054 _115057 x'' f g)). Qed.
Lemma lem5127378 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term632 _115054 _115057 x'' f g) = (term633 _115054 _115057 x'' f g).
Proof. exact (MK_COMB (@lem5127353 _115054 _115057 g) (@lem5127377 _115054 _115057 x'' f g)). Qed.
Lemma lem5127380 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127381 {_115054 _115057 : Type'} (f : _115057 -> _115054) (x : _115057) : (f x) = (@I (_115057 -> _115054) f x).
Proof. exact (@lem5127380 _115057 _115054 f x). Qed.
Lemma lem5127382 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term633 _115054 _115057 x'' f g) = (term634 _115054 _115057 x'' f g).
Proof. exact (@lem5127381 _115054 _115057 g (term631 _115054 _115057 x'' f g)). Qed.
Lemma lem5127383 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term632 _115054 _115057 x'' f g) = (term634 _115054 _115057 x'' f g).
Proof. exact (TRANS (@lem5127378 _115054 _115057 x'' f g) (@lem5127382 _115054 _115057 x'' f g)). Qed.
Lemma lem5127390 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127391 {_115054 _115057 : Type'} (f : type530 _115054 _115057) (x : _115054 -> _115057) : (f x) = (@I ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054) f x).
Proof. exact (@lem5127390 (_115054 -> _115057) (type802 _115054 _115057) f x). Qed.
Lemma lem5127392 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (x'' f) = (@I ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054) x'' f).
Proof. exact (@lem5127391 _115054 _115057 x'' f). Qed.
Lemma lem5127393 {_115054 _115057 : Type'} (g : _115057 -> _115054) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5127394 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (x'' f g) = (@I ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054) x'' f g).
Proof. exact (MK_COMB (@lem5127392 _115054 _115057 x'' f) (@lem5127393 _115054 _115057 g)). Qed.
Lemma lem5127396 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127397 {_115054 _115057 : Type'} (f : type802 _115054 _115057) (x : _115057 -> _115054) : (f x) = (@I ((_115057 -> _115054) -> _115054) f x).
Proof. exact (@lem5127396 (_115057 -> _115054) _115054 f x). Qed.
Lemma lem5127398 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (@I ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054) x'' f g) = (term628 _115054 _115057 x'' f g).
Proof. exact (@lem5127397 _115054 _115057 (@I ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054) x'' f) g). Qed.
Lemma lem5127400 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (x'' f g) = (term628 _115054 _115057 x'' f g).
Proof. exact (TRANS (@lem5127394 _115054 _115057 x'' f g) (@lem5127398 _115054 _115057 x'' f g)). Qed.
Lemma lem5127401 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term635 _115054 _115057 x'' f g) = (term636 _115054 _115057 x'' f g).
Proof. exact (MK_COMB (@lem5127352 _115054) (@lem5127383 _115054 _115057 x'' f g)). Qed.
Lemma lem5127402 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : ((term632 _115054 _115057 x'' f g) = (x'' f g)) = ((term634 _115054 _115057 x'' f g) = (term628 _115054 _115057 x'' f g)).
Proof. exact (MK_COMB (@lem5127401 _115054 _115057 x'' f g) (@lem5127400 _115054 _115057 x'' f g)). Qed.
Lemma lem5127403 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term637 _115054 _115057 x'' f g) = (term638 _115054 _115057 x'' f g).
Proof. exact (MK_COMB (@lem5127351) (@lem5127402 _115054 _115057 x'' f g)). Qed.
Lemma lem5127404 {_115054 : Type'} : (@IN _115054) = (@IN _115054).
Proof. exact (eq_refl (@IN _115054)). Qed.
Lemma lem5127411 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127412 {_115054 _115057 : Type'} (f : type530 _115054 _115057) (x : _115054 -> _115057) : (f x) = (@I ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054) f x).
Proof. exact (@lem5127411 (_115054 -> _115057) (type802 _115054 _115057) f x). Qed.
Lemma lem5127413 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (x'' f) = (@I ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054) x'' f).
Proof. exact (@lem5127412 _115054 _115057 x'' f). Qed.
Lemma lem5127414 {_115054 _115057 : Type'} (g : _115057 -> _115054) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5127415 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (x'' f g) = (@I ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054) x'' f g).
Proof. exact (MK_COMB (@lem5127413 _115054 _115057 x'' f) (@lem5127414 _115054 _115057 g)). Qed.
Lemma lem5127417 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127418 {_115054 _115057 : Type'} (f : type802 _115054 _115057) (x : _115057 -> _115054) : (f x) = (@I ((_115057 -> _115054) -> _115054) f x).
Proof. exact (@lem5127417 (_115057 -> _115054) _115054 f x). Qed.
Lemma lem5127419 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (@I ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054) x'' f g) = (term628 _115054 _115057 x'' f g).
Proof. exact (@lem5127418 _115054 _115057 (@I ((_115054 -> _115057) -> (_115057 -> _115054) -> _115054) x'' f) g). Qed.
Lemma lem5127421 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (x'' f g) = (term628 _115054 _115057 x'' f g).
Proof. exact (TRANS (@lem5127415 _115054 _115057 x'' f g) (@lem5127419 _115054 _115057 x'' f g)). Qed.
Lemma lem5127422 {_115054 : Type'} (s : _115054 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5127423 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term639 _115054 _115057 x'' f g) = (term640 _115054 _115057 x'' f g).
Proof. exact (MK_COMB (@lem5127404 _115054) (@lem5127421 _115054 _115057 x'' f g)). Qed.
Lemma lem5127424 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) (s : _115054 -> Prop) : (term641 _115054 _115057 x'' f g s) = (term642 _115054 _115057 x'' f g s).
Proof. exact (MK_COMB (@lem5127423 _115054 _115057 x'' f g) (@lem5127422 _115054 s)). Qed.
Lemma lem5127426 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127427 {_115054 : Type'} (f : type1364 _115054) (x : _115054) : (f x) = (@I (_115054 -> (_115054 -> Prop) -> Prop) f x).
Proof. exact (@lem5127426 _115054 (type686 _115054) f x). Qed.
Lemma lem5127428 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term640 _115054 _115057 x'' f g) = (term643 _115054 _115057 x'' f g).
Proof. exact (@lem5127427 _115054 (@IN _115054) (term628 _115054 _115057 x'' f g)). Qed.
Lemma lem5127429 {_115054 : Type'} (s : _115054 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5127430 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) (s : _115054 -> Prop) : (term642 _115054 _115057 x'' f g s) = (term644 _115054 _115057 x'' f g s).
Proof. exact (MK_COMB (@lem5127428 _115054 _115057 x'' f g) (@lem5127429 _115054 s)). Qed.
Lemma lem5127432 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127433 {_115054 : Type'} (f : type686 _115054) (x : _115054 -> Prop) : (f x) = (@I ((_115054 -> Prop) -> Prop) f x).
Proof. exact (@lem5127432 (_115054 -> Prop) Prop f x). Qed.
Lemma lem5127434 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) (s : _115054 -> Prop) : (term644 _115054 _115057 x'' f g s) = (term645 _115054 _115057 x'' f g s).
Proof. exact (@lem5127433 _115054 (term643 _115054 _115057 x'' f g) s). Qed.
Lemma lem5127435 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) (s : _115054 -> Prop) : (term642 _115054 _115057 x'' f g s) = (term645 _115054 _115057 x'' f g s).
Proof. exact (TRANS (@lem5127430 _115054 _115057 x'' f g s) (@lem5127434 _115054 _115057 x'' f g s)). Qed.
Lemma lem5127436 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) (s : _115054 -> Prop) : (term641 _115054 _115057 x'' f g s) = (term645 _115054 _115057 x'' f g s).
Proof. exact (TRANS (@lem5127424 _115054 _115057 x'' f g s) (@lem5127435 _115054 _115057 x'' f g s)). Qed.
Lemma lem5127437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5127438 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) (s : _115054 -> Prop) : (term646 _115054 _115057 x'' f g s) = (term647 _115054 _115057 x'' f g s).
Proof. exact (MK_COMB (@lem5127437) (@lem5127436 _115054 _115057 x'' f g s)). Qed.
Lemma lem5127439 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term648 _115054 _115057 s x'' f g) = (term649 _115054 _115057 s x'' f g).
Proof. exact (MK_COMB (@lem5127438 _115054 _115057 x'' f g s) (@lem5127403 _115054 _115057 x'' f g)). Qed.
Lemma lem5127440 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (term650 _115054 _115057 s x'' f) = (term651 _115054 _115057 s x'' f).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5127439 _115054 _115057 s x'' f g)). Qed.
Lemma lem5127441 {_115054 _115057 : Type'} : (@all (_115057 -> _115054)) = (@all (_115057 -> _115054)).
Proof. exact (eq_refl (@all (_115057 -> _115054))). Qed.
Lemma lem5127442 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (term652 _115054 _115057 s x'' f) = (term653 _115054 _115057 s x'' f).
Proof. exact (MK_COMB (@lem5127441 _115054 _115057) (@lem5127440 _115054 _115057 s x'' f)). Qed.
Lemma lem5127443 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5127444 {_115057 : Type'} : (@IN _115057) = (@IN _115057).
Proof. exact (eq_refl (@IN _115057)). Qed.
Lemma lem5127445 {_115054 _115057 : Type'} (f : _115054 -> _115057) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5127450 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127451 {_115054 _115057 : Type'} (f : type569 _115054 _115057) (x : _115054 -> _115057) : (f x) = (@I ((_115054 -> _115057) -> _115054) f x).
Proof. exact (@lem5127450 (_115054 -> _115057) _115054 f x). Qed.
Lemma lem5127453 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) : (x' f) = (@I ((_115054 -> _115057) -> _115054) x' f).
Proof. exact (@lem5127451 _115054 _115057 x' f). Qed.
Lemma lem5127454 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) : (term654 _115054 _115057 x' f) = (term655 _115054 _115057 x' f).
Proof. exact (MK_COMB (@lem5127445 _115054 _115057 f) (@lem5127453 _115054 _115057 x' f)). Qed.
Lemma lem5127456 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127457 {_115054 _115057 : Type'} (f : _115054 -> _115057) (x : _115054) : (f x) = (@I (_115054 -> _115057) f x).
Proof. exact (@lem5127456 _115054 _115057 f x). Qed.
Lemma lem5127458 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) : (term655 _115054 _115057 x' f) = (term656 _115054 _115057 x' f).
Proof. exact (@lem5127457 _115054 _115057 f (@I ((_115054 -> _115057) -> _115054) x' f)). Qed.
Lemma lem5127459 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) : (term654 _115054 _115057 x' f) = (term656 _115054 _115057 x' f).
Proof. exact (TRANS (@lem5127454 _115054 _115057 x' f) (@lem5127458 _115054 _115057 x' f)). Qed.
Lemma lem5127460 {_115057 : Type'} (t : _115057 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5127461 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) : (term657 _115054 _115057 x' f) = (term658 _115054 _115057 x' f).
Proof. exact (MK_COMB (@lem5127444 _115057) (@lem5127459 _115054 _115057 x' f)). Qed.
Lemma lem5127462 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term659 _115054 _115057 x' f t) = (term660 _115054 _115057 x' f t).
Proof. exact (MK_COMB (@lem5127461 _115054 _115057 x' f) (@lem5127460 _115057 t)). Qed.
Lemma lem5127464 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127465 {_115057 : Type'} (f : type1364 _115057) (x : _115057) : (f x) = (@I (_115057 -> (_115057 -> Prop) -> Prop) f x).
Proof. exact (@lem5127464 _115057 (type686 _115057) f x). Qed.
Lemma lem5127466 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) : (term658 _115054 _115057 x' f) = (term661 _115054 _115057 x' f).
Proof. exact (@lem5127465 _115057 (@IN _115057) (term656 _115054 _115057 x' f)). Qed.
Lemma lem5127467 {_115057 : Type'} (t : _115057 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5127468 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term660 _115054 _115057 x' f t) = (term662 _115054 _115057 x' f t).
Proof. exact (MK_COMB (@lem5127466 _115054 _115057 x' f) (@lem5127467 _115057 t)). Qed.
Lemma lem5127470 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127471 {_115057 : Type'} (f : type686 _115057) (x : _115057 -> Prop) : (f x) = (@I ((_115057 -> Prop) -> Prop) f x).
Proof. exact (@lem5127470 (_115057 -> Prop) Prop f x). Qed.
Lemma lem5127472 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term662 _115054 _115057 x' f t) = (term663 _115054 _115057 x' f t).
Proof. exact (@lem5127471 _115057 (term661 _115054 _115057 x' f) t). Qed.
Lemma lem5127473 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term660 _115054 _115057 x' f t) = (term663 _115054 _115057 x' f t).
Proof. exact (TRANS (@lem5127468 _115054 _115057 x' f t) (@lem5127472 _115054 _115057 x' f t)). Qed.
Lemma lem5127474 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term659 _115054 _115057 x' f t) = (term663 _115054 _115057 x' f t).
Proof. exact (TRANS (@lem5127462 _115054 _115057 x' f t) (@lem5127473 _115054 _115057 x' f t)). Qed.
Lemma lem5127475 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term664 _115054 _115057 x' f t) = (term665 _115054 _115057 x' f t).
Proof. exact (MK_COMB (@lem5127443) (@lem5127474 _115054 _115057 x' f t)). Qed.
Lemma lem5127476 {_115054 : Type'} : (@IN _115054) = (@IN _115054).
Proof. exact (eq_refl (@IN _115054)). Qed.
Lemma lem5127481 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127482 {_115054 _115057 : Type'} (f : type569 _115054 _115057) (x : _115054 -> _115057) : (f x) = (@I ((_115054 -> _115057) -> _115054) f x).
Proof. exact (@lem5127481 (_115054 -> _115057) _115054 f x). Qed.
Lemma lem5127484 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) : (x' f) = (@I ((_115054 -> _115057) -> _115054) x' f).
Proof. exact (@lem5127482 _115054 _115057 x' f). Qed.
Lemma lem5127485 {_115054 : Type'} (s : _115054 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5127486 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) : (term666 _115054 _115057 x' f) = (term667 _115054 _115057 x' f).
Proof. exact (MK_COMB (@lem5127476 _115054) (@lem5127484 _115054 _115057 x' f)). Qed.
Lemma lem5127487 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) (s : _115054 -> Prop) : (term668 _115054 _115057 x' f s) = (term669 _115054 _115057 x' f s).
Proof. exact (MK_COMB (@lem5127486 _115054 _115057 x' f) (@lem5127485 _115054 s)). Qed.
Lemma lem5127489 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127490 {_115054 : Type'} (f : type1364 _115054) (x : _115054) : (f x) = (@I (_115054 -> (_115054 -> Prop) -> Prop) f x).
Proof. exact (@lem5127489 _115054 (type686 _115054) f x). Qed.
Lemma lem5127491 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) : (term667 _115054 _115057 x' f) = (term670 _115054 _115057 x' f).
Proof. exact (@lem5127490 _115054 (@IN _115054) (@I ((_115054 -> _115057) -> _115054) x' f)). Qed.
Lemma lem5127492 {_115054 : Type'} (s : _115054 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5127493 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) (s : _115054 -> Prop) : (term669 _115054 _115057 x' f s) = (term671 _115054 _115057 x' f s).
Proof. exact (MK_COMB (@lem5127491 _115054 _115057 x' f) (@lem5127492 _115054 s)). Qed.
Lemma lem5127495 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127496 {_115054 : Type'} (f : type686 _115054) (x : _115054 -> Prop) : (f x) = (@I ((_115054 -> Prop) -> Prop) f x).
Proof. exact (@lem5127495 (_115054 -> Prop) Prop f x). Qed.
Lemma lem5127497 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) (s : _115054 -> Prop) : (term671 _115054 _115057 x' f s) = (term672 _115054 _115057 x' f s).
Proof. exact (@lem5127496 _115054 (term670 _115054 _115057 x' f) s). Qed.
Lemma lem5127498 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) (s : _115054 -> Prop) : (term669 _115054 _115057 x' f s) = (term672 _115054 _115057 x' f s).
Proof. exact (TRANS (@lem5127493 _115054 _115057 x' f s) (@lem5127497 _115054 _115057 x' f s)). Qed.
Lemma lem5127499 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) (s : _115054 -> Prop) : (term668 _115054 _115057 x' f s) = (term672 _115054 _115057 x' f s).
Proof. exact (TRANS (@lem5127487 _115054 _115057 x' f s) (@lem5127498 _115054 _115057 x' f s)). Qed.
Lemma lem5127500 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5127501 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (f : _115054 -> _115057) (s : _115054 -> Prop) : (term673 _115054 _115057 x' f s) = (term674 _115054 _115057 x' f s).
Proof. exact (MK_COMB (@lem5127500) (@lem5127499 _115054 _115057 x' f s)). Qed.
Lemma lem5127502 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x' : type569 _115054 _115057) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term675 _115054 _115057 s x' f t) = (term676 _115054 _115057 s x' f t).
Proof. exact (MK_COMB (@lem5127501 _115054 _115057 x' f s) (@lem5127475 _115054 _115057 x' f t)). Qed.
Lemma lem5127503 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5127504 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x' : type569 _115054 _115057) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term677 _115054 _115057 s x' f t) = (term678 _115054 _115057 s x' f t).
Proof. exact (MK_COMB (@lem5127503) (@lem5127502 _115054 _115057 s x' f t)). Qed.
Lemma lem5127505 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (term409 _115054 _115057 x' t s x'' f) = (term679 _115054 _115057 x' t s x'' f).
Proof. exact (MK_COMB (@lem5127504 _115054 _115057 s x' f t) (@lem5127442 _115054 _115057 s x'' f)). Qed.
Lemma lem5127506 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) : (term411 _115054 _115057 x' t s x'') = (term680 _115054 _115057 x' t s x'').
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5127505 _115054 _115057 x' t s x'' f)). Qed.
Lemma lem5127507 {_115054 _115057 : Type'} : (@all (_115054 -> _115057)) = (@all (_115054 -> _115057)).
Proof. exact (eq_refl (@all (_115054 -> _115057))). Qed.
Lemma lem5127508 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) : (term413 _115054 _115057 x' t s x'') = (term681 _115054 _115057 x' t s x'').
Proof. exact (MK_COMB (@lem5127507 _115054 _115057) (@lem5127506 _115054 _115057 x' t s x'')). Qed.
Lemma lem5127509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5127510 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) : (term449 _115054 _115057 x' t s x'') = (term682 _115054 _115057 x' t s x'').
Proof. exact (MK_COMB (@lem5127509) (@lem5127508 _115054 _115057 x' t s x'')). Qed.
Lemma lem5127511 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) : (term477 _115054 _115057 x' x'' s t g' g'') = (term683 _115054 _115057 x' x'' s t g' g'').
Proof. exact (MK_COMB (@lem5127510 _115054 _115057 x' t s x'') (@lem5127350 _115054 _115057 s t g' g'')). Qed.
Lemma lem5127512 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5127513 {_115054 : Type'} : (@eq _115054) = (@eq _115054).
Proof. exact (eq_refl (@eq _115054)). Qed.
Lemma lem5127514 {_115054 _115057 : Type'} (g : _115057 -> _115054) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5127515 {_115054 _115057 : Type'} (g : _115054 -> _115057) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5127522 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127523 {_115054 _115057 : Type'} (f : type779 _115054 _115057) (x : _115057 -> _115054) : (f x) = (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) f x).
Proof. exact (@lem5127522 (_115057 -> _115054) (type569 _115054 _115057) f x). Qed.
Lemma lem5127524 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) : (x g) = (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g).
Proof. exact (@lem5127523 _115054 _115057 x g). Qed.
Lemma lem5127525 {_115054 _115057 : Type'} (g : _115054 -> _115057) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5127526 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (x g g') = (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g g').
Proof. exact (MK_COMB (@lem5127524 _115054 _115057 x g) (@lem5127525 _115054 _115057 g')). Qed.
Lemma lem5127528 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127529 {_115054 _115057 : Type'} (f : type569 _115054 _115057) (x : _115054 -> _115057) : (f x) = (@I ((_115054 -> _115057) -> _115054) f x).
Proof. exact (@lem5127528 (_115054 -> _115057) _115054 f x). Qed.
Lemma lem5127530 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g g') = (term684 _115054 _115057 x g g').
Proof. exact (@lem5127529 _115054 _115057 (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g) g'). Qed.
Lemma lem5127532 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (x g g') = (term684 _115054 _115057 x g g').
Proof. exact (TRANS (@lem5127526 _115054 _115057 x g g') (@lem5127530 _115054 _115057 x g g')). Qed.
Lemma lem5127533 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term685 _115054 _115057 x g g') = (term686 _115054 _115057 x g g').
Proof. exact (MK_COMB (@lem5127515 _115054 _115057 g') (@lem5127532 _115054 _115057 x g g')). Qed.
Lemma lem5127535 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127536 {_115054 _115057 : Type'} (f : _115054 -> _115057) (x : _115054) : (f x) = (@I (_115054 -> _115057) f x).
Proof. exact (@lem5127535 _115054 _115057 f x). Qed.
Lemma lem5127537 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term686 _115054 _115057 x g g') = (term687 _115054 _115057 x g g').
Proof. exact (@lem5127536 _115054 _115057 g' (term684 _115054 _115057 x g g')). Qed.
Lemma lem5127538 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term685 _115054 _115057 x g g') = (term687 _115054 _115057 x g g').
Proof. exact (TRANS (@lem5127533 _115054 _115057 x g g') (@lem5127537 _115054 _115057 x g g')). Qed.
Lemma lem5127539 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term688 _115054 _115057 x g g') = (term689 _115054 _115057 x g g').
Proof. exact (MK_COMB (@lem5127514 _115054 _115057 g) (@lem5127538 _115054 _115057 x g g')). Qed.
Lemma lem5127541 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127542 {_115054 _115057 : Type'} (f : _115057 -> _115054) (x : _115057) : (f x) = (@I (_115057 -> _115054) f x).
Proof. exact (@lem5127541 _115057 _115054 f x). Qed.
Lemma lem5127543 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term689 _115054 _115057 x g g') = (term690 _115054 _115057 x g g').
Proof. exact (@lem5127542 _115054 _115057 g (term687 _115054 _115057 x g g')). Qed.
Lemma lem5127544 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term688 _115054 _115057 x g g') = (term690 _115054 _115057 x g g').
Proof. exact (TRANS (@lem5127539 _115054 _115057 x g g') (@lem5127543 _115054 _115057 x g g')). Qed.
Lemma lem5127551 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127552 {_115054 _115057 : Type'} (f : type779 _115054 _115057) (x : _115057 -> _115054) : (f x) = (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) f x).
Proof. exact (@lem5127551 (_115057 -> _115054) (type569 _115054 _115057) f x). Qed.
Lemma lem5127553 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) : (x g) = (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g).
Proof. exact (@lem5127552 _115054 _115057 x g). Qed.
Lemma lem5127554 {_115054 _115057 : Type'} (g : _115054 -> _115057) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5127555 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (x g g') = (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g g').
Proof. exact (MK_COMB (@lem5127553 _115054 _115057 x g) (@lem5127554 _115054 _115057 g')). Qed.
Lemma lem5127557 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127558 {_115054 _115057 : Type'} (f : type569 _115054 _115057) (x : _115054 -> _115057) : (f x) = (@I ((_115054 -> _115057) -> _115054) f x).
Proof. exact (@lem5127557 (_115054 -> _115057) _115054 f x). Qed.
Lemma lem5127559 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g g') = (term684 _115054 _115057 x g g').
Proof. exact (@lem5127558 _115054 _115057 (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g) g'). Qed.
Lemma lem5127561 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (x g g') = (term684 _115054 _115057 x g g').
Proof. exact (TRANS (@lem5127555 _115054 _115057 x g g') (@lem5127559 _115054 _115057 x g g')). Qed.
Lemma lem5127562 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term691 _115054 _115057 x g g') = (term692 _115054 _115057 x g g').
Proof. exact (MK_COMB (@lem5127513 _115054) (@lem5127544 _115054 _115057 x g g')). Qed.
Lemma lem5127563 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : ((term688 _115054 _115057 x g g') = (x g g')) = ((term690 _115054 _115057 x g g') = (term684 _115054 _115057 x g g')).
Proof. exact (MK_COMB (@lem5127562 _115054 _115057 x g g') (@lem5127561 _115054 _115057 x g g')). Qed.
Lemma lem5127564 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term693 _115054 _115057 x g g') = (term694 _115054 _115057 x g g').
Proof. exact (MK_COMB (@lem5127512) (@lem5127563 _115054 _115057 x g g')). Qed.
Lemma lem5127565 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5127566 {_115057 : Type'} : (@IN _115057) = (@IN _115057).
Proof. exact (eq_refl (@IN _115057)). Qed.
Lemma lem5127567 {_115054 _115057 : Type'} (g : _115054 -> _115057) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5127574 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127575 {_115054 _115057 : Type'} (f : type779 _115054 _115057) (x : _115057 -> _115054) : (f x) = (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) f x).
Proof. exact (@lem5127574 (_115057 -> _115054) (type569 _115054 _115057) f x). Qed.
Lemma lem5127576 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) : (x g) = (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g).
Proof. exact (@lem5127575 _115054 _115057 x g). Qed.
Lemma lem5127577 {_115054 _115057 : Type'} (g : _115054 -> _115057) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5127578 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (x g g') = (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g g').
Proof. exact (MK_COMB (@lem5127576 _115054 _115057 x g) (@lem5127577 _115054 _115057 g')). Qed.
Lemma lem5127580 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127581 {_115054 _115057 : Type'} (f : type569 _115054 _115057) (x : _115054 -> _115057) : (f x) = (@I ((_115054 -> _115057) -> _115054) f x).
Proof. exact (@lem5127580 (_115054 -> _115057) _115054 f x). Qed.
Lemma lem5127582 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g g') = (term684 _115054 _115057 x g g').
Proof. exact (@lem5127581 _115054 _115057 (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g) g'). Qed.
Lemma lem5127584 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (x g g') = (term684 _115054 _115057 x g g').
Proof. exact (TRANS (@lem5127578 _115054 _115057 x g g') (@lem5127582 _115054 _115057 x g g')). Qed.
Lemma lem5127585 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term685 _115054 _115057 x g g') = (term686 _115054 _115057 x g g').
Proof. exact (MK_COMB (@lem5127567 _115054 _115057 g') (@lem5127584 _115054 _115057 x g g')). Qed.
Lemma lem5127587 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127588 {_115054 _115057 : Type'} (f : _115054 -> _115057) (x : _115054) : (f x) = (@I (_115054 -> _115057) f x).
Proof. exact (@lem5127587 _115054 _115057 f x). Qed.
Lemma lem5127589 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term686 _115054 _115057 x g g') = (term687 _115054 _115057 x g g').
Proof. exact (@lem5127588 _115054 _115057 g' (term684 _115054 _115057 x g g')). Qed.
Lemma lem5127590 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term685 _115054 _115057 x g g') = (term687 _115054 _115057 x g g').
Proof. exact (TRANS (@lem5127585 _115054 _115057 x g g') (@lem5127589 _115054 _115057 x g g')). Qed.
Lemma lem5127591 {_115057 : Type'} (t : _115057 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5127592 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term695 _115054 _115057 x g g') = (term696 _115054 _115057 x g g').
Proof. exact (MK_COMB (@lem5127566 _115057) (@lem5127590 _115054 _115057 x g g')). Qed.
Lemma lem5127593 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) (t : _115057 -> Prop) : (term697 _115054 _115057 x g g' t) = (term698 _115054 _115057 x g g' t).
Proof. exact (MK_COMB (@lem5127592 _115054 _115057 x g g') (@lem5127591 _115057 t)). Qed.
Lemma lem5127595 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127596 {_115057 : Type'} (f : type1364 _115057) (x : _115057) : (f x) = (@I (_115057 -> (_115057 -> Prop) -> Prop) f x).
Proof. exact (@lem5127595 _115057 (type686 _115057) f x). Qed.
Lemma lem5127597 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term696 _115054 _115057 x g g') = (term699 _115054 _115057 x g g').
Proof. exact (@lem5127596 _115057 (@IN _115057) (term687 _115054 _115057 x g g')). Qed.
Lemma lem5127598 {_115057 : Type'} (t : _115057 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5127599 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) (t : _115057 -> Prop) : (term698 _115054 _115057 x g g' t) = (term700 _115054 _115057 x g g' t).
Proof. exact (MK_COMB (@lem5127597 _115054 _115057 x g g') (@lem5127598 _115057 t)). Qed.
Lemma lem5127601 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127602 {_115057 : Type'} (f : type686 _115057) (x : _115057 -> Prop) : (f x) = (@I ((_115057 -> Prop) -> Prop) f x).
Proof. exact (@lem5127601 (_115057 -> Prop) Prop f x). Qed.
Lemma lem5127603 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) (t : _115057 -> Prop) : (term700 _115054 _115057 x g g' t) = (term701 _115054 _115057 x g g' t).
Proof. exact (@lem5127602 _115057 (term699 _115054 _115057 x g g') t). Qed.
Lemma lem5127604 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) (t : _115057 -> Prop) : (term698 _115054 _115057 x g g' t) = (term701 _115054 _115057 x g g' t).
Proof. exact (TRANS (@lem5127599 _115054 _115057 x g g' t) (@lem5127603 _115054 _115057 x g g' t)). Qed.
Lemma lem5127605 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) (t : _115057 -> Prop) : (term697 _115054 _115057 x g g' t) = (term701 _115054 _115057 x g g' t).
Proof. exact (TRANS (@lem5127593 _115054 _115057 x g g' t) (@lem5127604 _115054 _115057 x g g' t)). Qed.
Lemma lem5127606 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) (t : _115057 -> Prop) : (term702 _115054 _115057 x g g' t) = (term703 _115054 _115057 x g g' t).
Proof. exact (MK_COMB (@lem5127565) (@lem5127605 _115054 _115057 x g g' t)). Qed.
Lemma lem5127607 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5127608 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) (t : _115057 -> Prop) : (term704 _115054 _115057 x g g' t) = (term705 _115054 _115057 x g g' t).
Proof. exact (MK_COMB (@lem5127607) (@lem5127606 _115054 _115057 x g g' t)). Qed.
Lemma lem5127609 {_115054 _115057 : Type'} (t : _115057 -> Prop) (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term706 _115054 _115057 t x g g') = (term707 _115054 _115057 t x g g').
Proof. exact (MK_COMB (@lem5127608 _115054 _115057 x g g' t) (@lem5127564 _115054 _115057 x g g')). Qed.
Lemma lem5127610 {_115054 : Type'} : (@IN _115054) = (@IN _115054).
Proof. exact (eq_refl (@IN _115054)). Qed.
Lemma lem5127617 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127618 {_115054 _115057 : Type'} (f : type779 _115054 _115057) (x : _115057 -> _115054) : (f x) = (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) f x).
Proof. exact (@lem5127617 (_115057 -> _115054) (type569 _115054 _115057) f x). Qed.
Lemma lem5127619 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) : (x g) = (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g).
Proof. exact (@lem5127618 _115054 _115057 x g). Qed.
Lemma lem5127620 {_115054 _115057 : Type'} (g : _115054 -> _115057) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5127621 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (x g g') = (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g g').
Proof. exact (MK_COMB (@lem5127619 _115054 _115057 x g) (@lem5127620 _115054 _115057 g')). Qed.
Lemma lem5127623 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127624 {_115054 _115057 : Type'} (f : type569 _115054 _115057) (x : _115054 -> _115057) : (f x) = (@I ((_115054 -> _115057) -> _115054) f x).
Proof. exact (@lem5127623 (_115054 -> _115057) _115054 f x). Qed.
Lemma lem5127625 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g g') = (term684 _115054 _115057 x g g').
Proof. exact (@lem5127624 _115054 _115057 (@I ((_115057 -> _115054) -> (_115054 -> _115057) -> _115054) x g) g'). Qed.
Lemma lem5127627 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (x g g') = (term684 _115054 _115057 x g g').
Proof. exact (TRANS (@lem5127621 _115054 _115057 x g g') (@lem5127625 _115054 _115057 x g g')). Qed.
Lemma lem5127628 {_115054 : Type'} (s : _115054 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5127629 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term708 _115054 _115057 x g g') = (term709 _115054 _115057 x g g').
Proof. exact (MK_COMB (@lem5127610 _115054) (@lem5127627 _115054 _115057 x g g')). Qed.
Lemma lem5127630 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) (s : _115054 -> Prop) : (term710 _115054 _115057 x g g' s) = (term711 _115054 _115057 x g g' s).
Proof. exact (MK_COMB (@lem5127629 _115054 _115057 x g g') (@lem5127628 _115054 s)). Qed.
Lemma lem5127632 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127633 {_115054 : Type'} (f : type1364 _115054) (x : _115054) : (f x) = (@I (_115054 -> (_115054 -> Prop) -> Prop) f x).
Proof. exact (@lem5127632 _115054 (type686 _115054) f x). Qed.
Lemma lem5127634 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term709 _115054 _115057 x g g') = (term712 _115054 _115057 x g g').
Proof. exact (@lem5127633 _115054 (@IN _115054) (term684 _115054 _115057 x g g')). Qed.
Lemma lem5127635 {_115054 : Type'} (s : _115054 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5127636 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) (s : _115054 -> Prop) : (term711 _115054 _115057 x g g' s) = (term713 _115054 _115057 x g g' s).
Proof. exact (MK_COMB (@lem5127634 _115054 _115057 x g g') (@lem5127635 _115054 s)). Qed.
Lemma lem5127638 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127639 {_115054 : Type'} (f : type686 _115054) (x : _115054 -> Prop) : (f x) = (@I ((_115054 -> Prop) -> Prop) f x).
Proof. exact (@lem5127638 (_115054 -> Prop) Prop f x). Qed.
Lemma lem5127640 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) (s : _115054 -> Prop) : (term713 _115054 _115057 x g g' s) = (term714 _115054 _115057 x g g' s).
Proof. exact (@lem5127639 _115054 (term712 _115054 _115057 x g g') s). Qed.
Lemma lem5127641 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) (s : _115054 -> Prop) : (term711 _115054 _115057 x g g' s) = (term714 _115054 _115057 x g g' s).
Proof. exact (TRANS (@lem5127636 _115054 _115057 x g g' s) (@lem5127640 _115054 _115057 x g g' s)). Qed.
Lemma lem5127642 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) (s : _115054 -> Prop) : (term710 _115054 _115057 x g g' s) = (term714 _115054 _115057 x g g' s).
Proof. exact (TRANS (@lem5127630 _115054 _115057 x g g' s) (@lem5127641 _115054 _115057 x g g' s)). Qed.
Lemma lem5127643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5127644 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) (s : _115054 -> Prop) : (term715 _115054 _115057 x g g' s) = (term716 _115054 _115057 x g g' s).
Proof. exact (MK_COMB (@lem5127643) (@lem5127642 _115054 _115057 x g g' s)). Qed.
Lemma lem5127645 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term717 _115054 _115057 s t x g g') = (term718 _115054 _115057 s t x g g').
Proof. exact (MK_COMB (@lem5127644 _115054 _115057 x g g' s) (@lem5127609 _115054 _115057 t x g g')). Qed.
Lemma lem5127646 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (g : _115057 -> _115054) : (term719 _115054 _115057 s t x g) = (term720 _115054 _115057 s t x g).
Proof. exact (fun_ext (fun g' : _115054 -> _115057 => @lem5127645 _115054 _115057 s t x g g')). Qed.
Lemma lem5127647 {_115054 _115057 : Type'} : (@all (_115054 -> _115057)) = (@all (_115054 -> _115057)).
Proof. exact (eq_refl (@all (_115054 -> _115057))). Qed.
Lemma lem5127648 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (g : _115057 -> _115054) : (term246 _115054 _115057 s t x g) = (term721 _115054 _115057 s t x g).
Proof. exact (MK_COMB (@lem5127647 _115054 _115057) (@lem5127646 _115054 _115057 s t x g)). Qed.
Lemma lem5127649 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term248 _115054 _115057 s t x) = (term722 _115054 _115057 s t x).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5127648 _115054 _115057 s t x g)). Qed.
Lemma lem5127650 {_115054 _115057 : Type'} : (@all (_115057 -> _115054)) = (@all (_115057 -> _115054)).
Proof. exact (eq_refl (@all (_115057 -> _115054))). Qed.
Lemma lem5127651 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term250 _115054 _115057 s t x) = (term723 _115054 _115057 s t x).
Proof. exact (MK_COMB (@lem5127650 _115054 _115057) (@lem5127649 _115054 _115057 s t x)). Qed.
Lemma lem5127652 {_115054 : Type'} : (@eq _115054) = (@eq _115054).
Proof. exact (eq_refl (@eq _115054)). Qed.
Lemma lem5127653 {_115054 _115057 : Type'} (g : _115057 -> _115054) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5127658 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127660 {_115054 _115057 : Type'} (f : _115054 -> _115057) (x : _115054) : (f x) = (@I (_115054 -> _115057) f x).
Proof. exact (@lem5127658 _115054 _115057 f x). Qed.
Lemma lem5127661 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : (term103 _115054 _115057 g f x) = (term607 _115054 _115057 g f x).
Proof. exact (MK_COMB (@lem5127653 _115054 _115057 g) (@lem5127660 _115054 _115057 f x)). Qed.
Lemma lem5127663 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127664 {_115054 _115057 : Type'} (f : _115057 -> _115054) (x : _115057) : (f x) = (@I (_115057 -> _115054) f x).
Proof. exact (@lem5127663 _115057 _115054 f x). Qed.
Lemma lem5127665 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : (term607 _115054 _115057 g f x) = (term608 _115054 _115057 g f x).
Proof. exact (@lem5127664 _115054 _115057 g (@I (_115054 -> _115057) f x)). Qed.
Lemma lem5127666 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : (term103 _115054 _115057 g f x) = (term608 _115054 _115057 g f x).
Proof. exact (TRANS (@lem5127661 _115054 _115057 g f x) (@lem5127665 _115054 _115057 g f x)). Qed.
Lemma lem5127667 {_115054 : Type'} (x : _115054) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5127668 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : (term609 _115054 _115057 g f x) = (term610 _115054 _115057 g f x).
Proof. exact (MK_COMB (@lem5127652 _115054) (@lem5127666 _115054 _115057 g f x)). Qed.
Lemma lem5127669 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : ((term103 _115054 _115057 g f x) = x) = ((term608 _115054 _115057 g f x) = x).
Proof. exact (MK_COMB (@lem5127668 _115054 _115057 g f x) (@lem5127667 _115054 x)). Qed.
Lemma lem5127670 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5127677 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127678 {_115054 : Type'} (f : type1364 _115054) (x : _115054) : (f x) = (@I (_115054 -> (_115054 -> Prop) -> Prop) f x).
Proof. exact (@lem5127677 _115054 (type686 _115054) f x). Qed.
Lemma lem5127679 {_115054 : Type'} (x : _115054) : (@IN _115054 x) = (@I (_115054 -> (_115054 -> Prop) -> Prop) (@IN _115054) x).
Proof. exact (@lem5127678 _115054 (@IN _115054) x). Qed.
Lemma lem5127680 {_115054 : Type'} (s : _115054 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5127681 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (@IN _115054 x s) = (@I (_115054 -> (_115054 -> Prop) -> Prop) (@IN _115054) x s).
Proof. exact (MK_COMB (@lem5127679 _115054 x) (@lem5127680 _115054 s)). Qed.
Lemma lem5127683 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127684 {_115054 : Type'} (f : type686 _115054) (x : _115054 -> Prop) : (f x) = (@I ((_115054 -> Prop) -> Prop) f x).
Proof. exact (@lem5127683 (_115054 -> Prop) Prop f x). Qed.
Lemma lem5127685 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (@I (_115054 -> (_115054 -> Prop) -> Prop) (@IN _115054) x s) = (term620 _115054 x s).
Proof. exact (@lem5127684 _115054 (@I (_115054 -> (_115054 -> Prop) -> Prop) (@IN _115054) x) s). Qed.
Lemma lem5127687 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (@IN _115054 x s) = (term620 _115054 x s).
Proof. exact (TRANS (@lem5127681 _115054 x s) (@lem5127685 _115054 x s)). Qed.
Lemma lem5127688 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (term621 _115054 x s) = (term622 _115054 x s).
Proof. exact (MK_COMB (@lem5127670) (@lem5127687 _115054 x s)). Qed.
Lemma lem5127689 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5127690 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (term623 _115054 x s) = (term624 _115054 x s).
Proof. exact (MK_COMB (@lem5127689) (@lem5127688 _115054 x s)). Qed.
Lemma lem5127691 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : (term104 _115054 _115057 s g f x) = (term724 _115054 _115057 s g f x).
Proof. exact (MK_COMB (@lem5127690 _115054 x s) (@lem5127669 _115054 _115057 g f x)). Qed.
Lemma lem5127692 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term112 _115054 _115057 s g f) = (term725 _115054 _115057 s g f).
Proof. exact (fun_ext (fun x : _115054 => @lem5127691 _115054 _115057 s g f x)). Qed.
Lemma lem5127693 {_115054 : Type'} : (@all _115054) = (@all _115054).
Proof. exact (eq_refl (@all _115054)). Qed.
Lemma lem5127694 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term113 _115054 _115057 s g f) = (term726 _115054 _115057 s g f).
Proof. exact (MK_COMB (@lem5127693 _115054) (@lem5127692 _115054 _115057 s g f)). Qed.
Lemma lem5127695 {_115057 : Type'} : (@IN _115057) = (@IN _115057).
Proof. exact (eq_refl (@IN _115057)). Qed.
Lemma lem5127700 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127702 {_115054 _115057 : Type'} (f : _115054 -> _115057) (x : _115054) : (f x) = (@I (_115054 -> _115057) f x).
Proof. exact (@lem5127700 _115054 _115057 f x). Qed.
Lemma lem5127703 {_115057 : Type'} (t : _115057 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5127704 {_115054 _115057 : Type'} (f : _115054 -> _115057) (x : _115054) : (term611 _115054 _115057 f x) = (term612 _115054 _115057 f x).
Proof. exact (MK_COMB (@lem5127695 _115057) (@lem5127702 _115054 _115057 f x)). Qed.
Lemma lem5127705 {_115054 _115057 : Type'} (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term88 _115054 _115057 f x t) = (term613 _115054 _115057 f x t).
Proof. exact (MK_COMB (@lem5127704 _115054 _115057 f x) (@lem5127703 _115057 t)). Qed.
Lemma lem5127707 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127708 {_115057 : Type'} (f : type1364 _115057) (x : _115057) : (f x) = (@I (_115057 -> (_115057 -> Prop) -> Prop) f x).
Proof. exact (@lem5127707 _115057 (type686 _115057) f x). Qed.
Lemma lem5127709 {_115054 _115057 : Type'} (f : _115054 -> _115057) (x : _115054) : (term612 _115054 _115057 f x) = (term614 _115054 _115057 f x).
Proof. exact (@lem5127708 _115057 (@IN _115057) (@I (_115054 -> _115057) f x)). Qed.
Lemma lem5127710 {_115057 : Type'} (t : _115057 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5127711 {_115054 _115057 : Type'} (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term613 _115054 _115057 f x t) = (term615 _115054 _115057 f x t).
Proof. exact (MK_COMB (@lem5127709 _115054 _115057 f x) (@lem5127710 _115057 t)). Qed.
Lemma lem5127713 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127714 {_115057 : Type'} (f : type686 _115057) (x : _115057 -> Prop) : (f x) = (@I ((_115057 -> Prop) -> Prop) f x).
Proof. exact (@lem5127713 (_115057 -> Prop) Prop f x). Qed.
Lemma lem5127715 {_115054 _115057 : Type'} (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term615 _115054 _115057 f x t) = (term616 _115054 _115057 f x t).
Proof. exact (@lem5127714 _115057 (term614 _115054 _115057 f x) t). Qed.
Lemma lem5127716 {_115054 _115057 : Type'} (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term613 _115054 _115057 f x t) = (term616 _115054 _115057 f x t).
Proof. exact (TRANS (@lem5127711 _115054 _115057 f x t) (@lem5127715 _115054 _115057 f x t)). Qed.
Lemma lem5127717 {_115054 _115057 : Type'} (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term88 _115054 _115057 f x t) = (term616 _115054 _115057 f x t).
Proof. exact (TRANS (@lem5127705 _115054 _115057 f x t) (@lem5127716 _115054 _115057 f x t)). Qed.
Lemma lem5127718 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5127725 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127726 {_115054 : Type'} (f : type1364 _115054) (x : _115054) : (f x) = (@I (_115054 -> (_115054 -> Prop) -> Prop) f x).
Proof. exact (@lem5127725 _115054 (type686 _115054) f x). Qed.
Lemma lem5127727 {_115054 : Type'} (x : _115054) : (@IN _115054 x) = (@I (_115054 -> (_115054 -> Prop) -> Prop) (@IN _115054) x).
Proof. exact (@lem5127726 _115054 (@IN _115054) x). Qed.
Lemma lem5127728 {_115054 : Type'} (s : _115054 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5127729 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (@IN _115054 x s) = (@I (_115054 -> (_115054 -> Prop) -> Prop) (@IN _115054) x s).
Proof. exact (MK_COMB (@lem5127727 _115054 x) (@lem5127728 _115054 s)). Qed.
Lemma lem5127731 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5127732 {_115054 : Type'} (f : type686 _115054) (x : _115054 -> Prop) : (f x) = (@I ((_115054 -> Prop) -> Prop) f x).
Proof. exact (@lem5127731 (_115054 -> Prop) Prop f x). Qed.
Lemma lem5127733 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (@I (_115054 -> (_115054 -> Prop) -> Prop) (@IN _115054) x s) = (term620 _115054 x s).
Proof. exact (@lem5127732 _115054 (@I (_115054 -> (_115054 -> Prop) -> Prop) (@IN _115054) x) s). Qed.
Lemma lem5127735 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (@IN _115054 x s) = (term620 _115054 x s).
Proof. exact (TRANS (@lem5127729 _115054 x s) (@lem5127733 _115054 x s)). Qed.
Lemma lem5127736 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (term621 _115054 x s) = (term622 _115054 x s).
Proof. exact (MK_COMB (@lem5127718) (@lem5127735 _115054 x s)). Qed.
Lemma lem5127737 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5127738 {_115054 : Type'} (x : _115054) (s : _115054 -> Prop) : (term623 _115054 x s) = (term624 _115054 x s).
Proof. exact (MK_COMB (@lem5127737) (@lem5127736 _115054 x s)). Qed.
Lemma lem5127739 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term89 _115054 _115057 s f x t) = (term727 _115054 _115057 s f x t).
Proof. exact (MK_COMB (@lem5127738 _115054 x s) (@lem5127717 _115054 _115057 f x t)). Qed.
Lemma lem5127740 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term99 _115054 _115057 s f t) = (term728 _115054 _115057 s f t).
Proof. exact (fun_ext (fun x : _115054 => @lem5127739 _115054 _115057 s f x t)). Qed.
Lemma lem5127741 {_115054 : Type'} : (@all _115054) = (@all _115054).
Proof. exact (eq_refl (@all _115054)). Qed.
Lemma lem5127742 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term100 _115054 _115057 s f t) = (term729 _115054 _115057 s f t).
Proof. exact (MK_COMB (@lem5127741 _115054) (@lem5127740 _115054 _115057 s f t)). Qed.
Lemma lem5127743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5127744 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term129 _115054 _115057 s f t) = (term730 _115054 _115057 s f t).
Proof. exact (MK_COMB (@lem5127743) (@lem5127742 _115054 _115057 s f t)). Qed.
Lemma lem5127745 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term197 _115054 _115057 t s g f) = (term731 _115054 _115057 t s g f).
Proof. exact (MK_COMB (@lem5127744 _115054 _115057 s f t) (@lem5127694 _115054 _115057 s g f)). Qed.
Lemma lem5127746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5127747 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term285 _115054 _115057 t s g f) = (term732 _115054 _115057 t s g f).
Proof. exact (MK_COMB (@lem5127746) (@lem5127745 _115054 _115057 t s g f)). Qed.
Lemma lem5127748 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term301 _115054 _115057 g f s t x) = (term733 _115054 _115057 g f s t x).
Proof. exact (MK_COMB (@lem5127747 _115054 _115057 t s g f) (@lem5127651 _115054 _115057 s t x)). Qed.
Lemma lem5127749 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5127750 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term533 _115054 _115057 g f s t x) = (term734 _115054 _115057 g f s t x).
Proof. exact (MK_COMB (@lem5127749) (@lem5127748 _115054 _115057 g f s t x)). Qed.
Lemma lem5127751 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) : (term591 _115054 _115057 g f x x' x'' s t g' g'') = (term735 _115054 _115057 g f x x' x'' s t g' g'').
Proof. exact (MK_COMB (@lem5127750 _115054 _115057 g f s t x) (@lem5127511 _115054 _115057 x' x'' s t g' g'')). Qed.
Lemma lem5127752 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term591 _115054 _115057 g f x x' x'' s t g' g'') : term735 _115054 _115057 g f x x' x'' s t g' g''.
Proof. exact (EQ_MP (@lem5127751 _115054 _115057 g f x x' x'' s t g' g'') (@lem5127279 _115054 _115057 g f x x' x'' s t g' g'' h1)). Qed.
Lemma lem5127753 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term733 _115054 _115057 g f s t x.
Proof. exact (h1). Qed.
Lemma lem5127754 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term683 _115054 _115057 x' x'' s t g' g''.
Proof. exact (h1). Qed.
Lemma lem5127755 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term723 _115054 _115057 s t x.
Proof. exact (proj2 (@lem5127753 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5127756 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term731 _115054 _115057 t s g f.
Proof. exact (proj1 (@lem5127753 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5127757 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term726 _115054 _115057 s g f.
Proof. exact (proj2 (@lem5127756 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5127758 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term729 _115054 _115057 s f t.
Proof. exact (proj1 (@lem5127756 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5127759 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term627 _115054 _115057 s t g' g''.
Proof. exact (proj2 (@lem5127754 _115054 _115057 x' x'' s t g' g'' h1)). Qed.
Lemma lem5127760 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term681 _115054 _115057 x' t s x''.
Proof. exact (proj1 (@lem5127754 _115054 _115057 x' x'' s t g' g'' h1)). Qed.
Lemma lem5127772 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (g : _115057 -> _115054) (g' : _115054 -> _115057) : (term718 _115054 _115057 s t x g g') = (term718 _115054 _115057 s t x g g').
Proof. exact (eq_refl (term718 _115054 _115057 s t x g g')). Qed.
Lemma lem5127773 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (g : _115057 -> _115054) : (term720 _115054 _115057 s t x g) = (term720 _115054 _115057 s t x g).
Proof. exact (fun_ext (fun g' : _115054 -> _115057 => @lem5127772 _115054 _115057 s t x g g')). Qed.
Lemma lem5127774 {_115054 _115057 : Type'} : (@all (_115054 -> _115057)) = (@all (_115054 -> _115057)).
Proof. exact (eq_refl (@all (_115054 -> _115057))). Qed.
Lemma lem5127775 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (g : _115057 -> _115054) : (term721 _115054 _115057 s t x g) = (term721 _115054 _115057 s t x g).
Proof. exact (MK_COMB (@lem5127774 _115054 _115057) (@lem5127773 _115054 _115057 s t x g)). Qed.
Lemma lem5127776 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term722 _115054 _115057 s t x) = (term722 _115054 _115057 s t x).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5127775 _115054 _115057 s t x g)). Qed.
Lemma lem5127777 {_115054 _115057 : Type'} : (@all (_115057 -> _115054)) = (@all (_115057 -> _115054)).
Proof. exact (eq_refl (@all (_115057 -> _115054))). Qed.
Lemma lem5127779 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) : (term723 _115054 _115057 s t x) = (term723 _115054 _115057 s t x).
Proof. exact (MK_COMB (@lem5127777 _115054 _115057) (@lem5127776 _115054 _115057 s t x)). Qed.
Lemma lem5127780 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term723 _115054 _115057 s t x.
Proof. exact (EQ_MP (@lem5127779 _115054 _115057 s t x) (@lem5127755 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5127788 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (x : _115054) (t : _115057 -> Prop) : (term727 _115054 _115057 s f x t) = (term727 _115054 _115057 s f x t).
Proof. exact (eq_refl (term727 _115054 _115057 s f x t)). Qed.
Lemma lem5127789 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term728 _115054 _115057 s f t) = (term728 _115054 _115057 s f t).
Proof. exact (fun_ext (fun x : _115054 => @lem5127788 _115054 _115057 s f x t)). Qed.
Lemma lem5127790 {_115054 : Type'} : (@all _115054) = (@all _115054).
Proof. exact (eq_refl (@all _115054)). Qed.
Lemma lem5127792 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term729 _115054 _115057 s f t) = (term729 _115054 _115057 s f t).
Proof. exact (MK_COMB (@lem5127790 _115054) (@lem5127789 _115054 _115057 s f t)). Qed.
Lemma lem5127793 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term729 _115054 _115057 s f t.
Proof. exact (EQ_MP (@lem5127792 _115054 _115057 s f t) (@lem5127758 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5127801 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) (x : _115054) : (term724 _115054 _115057 s g f x) = (term724 _115054 _115057 s g f x).
Proof. exact (eq_refl (term724 _115054 _115057 s g f x)). Qed.
Lemma lem5127802 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term725 _115054 _115057 s g f) = (term725 _115054 _115057 s g f).
Proof. exact (fun_ext (fun x : _115054 => @lem5127801 _115054 _115057 s g f x)). Qed.
Lemma lem5127803 {_115054 : Type'} : (@all _115054) = (@all _115054).
Proof. exact (eq_refl (@all _115054)). Qed.
Lemma lem5127805 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term726 _115054 _115057 s g f) = (term726 _115054 _115057 s g f).
Proof. exact (MK_COMB (@lem5127803 _115054) (@lem5127802 _115054 _115057 s g f)). Qed.
Lemma lem5127806 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term726 _115054 _115057 s g f.
Proof. exact (EQ_MP (@lem5127805 _115054 _115057 s g f) (@lem5127757 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5127808 {A : Type'} (P : Prop) (Q : A -> Prop) : (term736 A P Q) = (term737 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5127809 {_115054 _115057 : Type'} (P : Prop) (Q : type805 _115054 _115057) : (term738 _115054 _115057 P Q) = (term739 _115054 _115057 P Q).
Proof. exact (@lem5127808 (_115057 -> _115054) P Q). Qed.
Lemma lem5127810 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (term740 _115054 _115057 x' t s x'' f) = (term741 _115054 _115057 x' t s x'' f).
Proof. exact (@lem5127809 _115054 _115057 (term676 _115054 _115057 s x' f t) (term651 _115054 _115057 s x'' f)). Qed.
Lemma lem5127811 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term742 _115054 _115057 s x'' f g) = (term649 _115054 _115057 s x'' f g).
Proof. exact (eq_refl (term742 _115054 _115057 s x'' f g)). Qed.
Lemma lem5127812 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (term743 _115054 _115057 s x'' f) = (term651 _115054 _115057 s x'' f).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5127811 _115054 _115057 s x'' f g)). Qed.
Lemma lem5127813 {_115054 _115057 : Type'} : (@all (_115057 -> _115054)) = (@all (_115057 -> _115054)).
Proof. exact (eq_refl (@all (_115057 -> _115054))). Qed.
Lemma lem5127814 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (term744 _115054 _115057 s x'' f) = (term653 _115054 _115057 s x'' f).
Proof. exact (MK_COMB (@lem5127813 _115054 _115057) (@lem5127812 _115054 _115057 s x'' f)). Qed.
Lemma lem5127815 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x' : type569 _115054 _115057) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term678 _115054 _115057 s x' f t) = (term678 _115054 _115057 s x' f t).
Proof. exact (eq_refl (term678 _115054 _115057 s x' f t)). Qed.
Lemma lem5127816 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (term740 _115054 _115057 x' t s x'' f) = (term679 _115054 _115057 x' t s x'' f).
Proof. exact (MK_COMB (@lem5127815 _115054 _115057 s x' f t) (@lem5127814 _115054 _115057 s x'' f)). Qed.
Lemma lem5127817 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5127818 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (term745 _115054 _115057 x' t s x'' f) = (term746 _115054 _115057 x' t s x'' f).
Proof. exact (MK_COMB (@lem5127817) (@lem5127816 _115054 _115057 x' t s x'' f)). Qed.
Lemma lem5127819 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term742 _115054 _115057 s x'' f g) = (term649 _115054 _115057 s x'' f g).
Proof. exact (eq_refl (term742 _115054 _115057 s x'' f g)). Qed.
Lemma lem5127820 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x' : type569 _115054 _115057) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term678 _115054 _115057 s x' f t) = (term678 _115054 _115057 s x' f t).
Proof. exact (eq_refl (term678 _115054 _115057 s x' f t)). Qed.
Lemma lem5127821 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term747 _115054 _115057 x' t s x'' f g) = (term748 _115054 _115057 x' t s x'' f g).
Proof. exact (MK_COMB (@lem5127820 _115054 _115057 s x' f t) (@lem5127819 _115054 _115057 s x'' f g)). Qed.
Lemma lem5127822 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (term749 _115054 _115057 x' t s x'' f) = (term750 _115054 _115057 x' t s x'' f).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5127821 _115054 _115057 x' t s x'' f g)). Qed.
Lemma lem5127823 {_115054 _115057 : Type'} : (@all (_115057 -> _115054)) = (@all (_115057 -> _115054)).
Proof. exact (eq_refl (@all (_115057 -> _115054))). Qed.
Lemma lem5127824 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (term741 _115054 _115057 x' t s x'' f) = (term751 _115054 _115057 x' t s x'' f).
Proof. exact (MK_COMB (@lem5127823 _115054 _115057) (@lem5127822 _115054 _115057 x' t s x'' f)). Qed.
Lemma lem5127825 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : ((term740 _115054 _115057 x' t s x'' f) = (term741 _115054 _115057 x' t s x'' f)) = ((term679 _115054 _115057 x' t s x'' f) = (term751 _115054 _115057 x' t s x'' f)).
Proof. exact (MK_COMB (@lem5127818 _115054 _115057 x' t s x'' f) (@lem5127824 _115054 _115057 x' t s x'' f)). Qed.
Lemma lem5127826 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (term679 _115054 _115057 x' t s x'' f) = (term751 _115054 _115057 x' t s x'' f).
Proof. exact (EQ_MP (@lem5127825 _115054 _115057 x' t s x'' f) (@lem5127810 _115054 _115057 x' t s x'' f)). Qed.
Lemma lem5127827 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) : (term680 _115054 _115057 x' t s x'') = (term752 _115054 _115057 x' t s x'').
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5127826 _115054 _115057 x' t s x'' f)). Qed.
Lemma lem5127828 {_115054 _115057 : Type'} : (@all (_115054 -> _115057)) = (@all (_115054 -> _115057)).
Proof. exact (eq_refl (@all (_115054 -> _115057))). Qed.
Lemma lem5127829 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) : (term681 _115054 _115057 x' t s x'') = (term753 _115054 _115057 x' t s x'').
Proof. exact (MK_COMB (@lem5127828 _115054 _115057) (@lem5127827 _115054 _115057 x' t s x'')). Qed.
Lemma lem5127843 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term748 _115054 _115057 x' t s x'' f g) = (term754 _115054 _115057 s x' t x'' f g).
Proof. exact (@lem19490 (term645 _115054 _115057 x'' f g s) (term676 _115054 _115057 s x' f t) (term638 _115054 _115057 x'' f g)). Qed.
Lemma lem5127850 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term755 _115054 _115057 s x' t x'' f g) = (term756 _115054 _115057 s x' t x'' f g).
Proof. exact (@lem19699 (term672 _115054 _115057 x' f s) (term665 _115054 _115057 x' f t) (term638 _115054 _115057 x'' f g)). Qed.
Lemma lem5127857 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) (s : _115054 -> Prop) : (term757 _115054 _115057 x' t x'' f g s) = (term758 _115054 _115057 x' t x'' f g s).
Proof. exact (@lem19699 (term672 _115054 _115057 x' f s) (term665 _115054 _115057 x' f t) (term645 _115054 _115057 x'' f g s)). Qed.
Lemma lem5127858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5127859 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) (s : _115054 -> Prop) : (term759 _115054 _115057 x' t x'' f g s) = (term760 _115054 _115057 x' t x'' f g s).
Proof. exact (MK_COMB (@lem5127858) (@lem5127857 _115054 _115057 x' t x'' f g s)). Qed.
Lemma lem5127860 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term754 _115054 _115057 s x' t x'' f g) = (term761 _115054 _115057 s x' t x'' f g).
Proof. exact (MK_COMB (@lem5127859 _115054 _115057 x' t x'' f g s) (@lem5127850 _115054 _115057 s x' t x'' f g)). Qed.
Lemma lem5127862 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) (g : _115057 -> _115054) : (term748 _115054 _115057 x' t s x'' f g) = (term761 _115054 _115057 s x' t x'' f g).
Proof. exact (TRANS (@lem5127843 _115054 _115057 s x' t x'' f g) (@lem5127860 _115054 _115057 s x' t x'' f g)). Qed.
Lemma lem5127863 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (term750 _115054 _115057 x' t s x'' f) = (term762 _115054 _115057 s x' t x'' f).
Proof. exact (fun_ext (fun g : _115057 -> _115054 => @lem5127862 _115054 _115057 s x' t x'' f g)). Qed.
Lemma lem5127864 {_115054 _115057 : Type'} : (@all (_115057 -> _115054)) = (@all (_115057 -> _115054)).
Proof. exact (eq_refl (@all (_115057 -> _115054))). Qed.
Lemma lem5127865 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (f : _115054 -> _115057) : (term751 _115054 _115057 x' t s x'' f) = (term763 _115054 _115057 s x' t x'' f).
Proof. exact (MK_COMB (@lem5127864 _115054 _115057) (@lem5127863 _115054 _115057 s x' t x'' f)). Qed.
Lemma lem5127866 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) : (term752 _115054 _115057 x' t s x'') = (term764 _115054 _115057 s x' t x'').
Proof. exact (fun_ext (fun f : _115054 -> _115057 => @lem5127865 _115054 _115057 s x' t x'' f)). Qed.
Lemma lem5127867 {_115054 _115057 : Type'} : (@all (_115054 -> _115057)) = (@all (_115054 -> _115057)).
Proof. exact (eq_refl (@all (_115054 -> _115057))). Qed.
Lemma lem5127868 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) : (term753 _115054 _115057 x' t s x'') = (term765 _115054 _115057 s x' t x'').
Proof. exact (MK_COMB (@lem5127867 _115054 _115057) (@lem5127866 _115054 _115057 s x' t x'')). Qed.
Lemma lem5127869 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) : (term681 _115054 _115057 x' t s x'') = (term765 _115054 _115057 s x' t x'').
Proof. exact (TRANS (@lem5127829 _115054 _115057 x' t s x'') (@lem5127868 _115054 _115057 s x' t x'')). Qed.
Lemma lem5127870 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term765 _115054 _115057 s x' t x''.
Proof. exact (EQ_MP (@lem5127869 _115054 _115057 s x' t x'') (@lem5127760 _115054 _115057 x' x'' s t g' g'' h1)). Qed.
Lemma lem5127888 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (x : _115054) : (term625 _115054 _115057 s t g' g'' x) = (term766 _115054 _115057 t s g' g'' x).
Proof. exact (@lem19490 (term616 _115054 _115057 g'' x t) (term622 _115054 x s) ((term608 _115054 _115057 g' g'' x) = x)). Qed.
Lemma lem5127889 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) : (term626 _115054 _115057 s t g' g'') = (term767 _115054 _115057 t s g' g'').
Proof. exact (fun_ext (fun x : _115054 => @lem5127888 _115054 _115057 t s g' g'' x)). Qed.
Lemma lem5127890 {_115054 : Type'} : (@all _115054) = (@all _115054).
Proof. exact (eq_refl (@all _115054)). Qed.
Lemma lem5127892 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) : (term627 _115054 _115057 s t g' g'') = (term768 _115054 _115057 t s g' g'').
Proof. exact (MK_COMB (@lem5127890 _115054) (@lem5127889 _115054 _115057 t s g' g'')). Qed.
Lemma lem5127893 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term768 _115054 _115057 t s g' g''.
Proof. exact (EQ_MP (@lem5127892 _115054 _115057 t s g' g'') (@lem5127759 _115054 _115057 x' x'' s t g' g'' h1)). Qed.
Lemma lem5127894 {_115054 _115057 : Type'} (_66901 : _115057 -> _115054) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term769 _115054 _115057 s t x _66901.
Proof. exact (@lem5127780 _115054 _115057 g f s t x h1 _66901). Qed.
Lemma lem5127895 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (_66901 : _115057 -> _115054) : (term769 _115054 _115057 s t x _66901) = (term721 _115054 _115057 s t x _66901).
Proof. exact (eq_refl (term769 _115054 _115057 s t x _66901)). Qed.
Lemma lem5127896 {_115054 _115057 : Type'} (_66901 : _115057 -> _115054) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term721 _115054 _115057 s t x _66901.
Proof. exact (EQ_MP (@lem5127895 _115054 _115057 s t x _66901) (@lem5127894 _115054 _115057 _66901 g f s t x h1)). Qed.
Lemma lem5127897 {_115054 _115057 : Type'} (_66901 : _115057 -> _115054) (_66902 : _115054 -> _115057) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term770 _115054 _115057 s t x _66901 _66902.
Proof. exact (@lem5127896 _115054 _115057 _66901 g f s t x h1 _66902). Qed.
Lemma lem5127898 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (_66901 : _115057 -> _115054) (_66902 : _115054 -> _115057) : (term770 _115054 _115057 s t x _66901 _66902) = (term718 _115054 _115057 s t x _66901 _66902).
Proof. exact (eq_refl (term770 _115054 _115057 s t x _66901 _66902)). Qed.
Lemma lem5127899 {_115054 _115057 : Type'} (_66901 : _115057 -> _115054) (_66902 : _115054 -> _115057) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term718 _115054 _115057 s t x _66901 _66902.
Proof. exact (EQ_MP (@lem5127898 _115054 _115057 s t x _66901 _66902) (@lem5127897 _115054 _115057 _66901 _66902 g f s t x h1)). Qed.
Lemma lem5127900 {_115054 _115057 : Type'} (_66903 : _115054) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term771 _115054 _115057 s f t _66903.
Proof. exact (@lem5127793 _115054 _115057 g f s t x h1 _66903). Qed.
Lemma lem5127901 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (_66903 : _115054) (t : _115057 -> Prop) : (term771 _115054 _115057 s f t _66903) = (term727 _115054 _115057 s f _66903 t).
Proof. exact (eq_refl (term771 _115054 _115057 s f t _66903)). Qed.
Lemma lem5127903 {_115054 _115057 : Type'} (_66904 : _115054) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term772 _115054 _115057 s g f _66904.
Proof. exact (@lem5127806 _115054 _115057 g f s t x h1 _66904). Qed.
Lemma lem5127904 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) (_66904 : _115054) : (term772 _115054 _115057 s g f _66904) = (term724 _115054 _115057 s g f _66904).
Proof. exact (eq_refl (term772 _115054 _115057 s g f _66904)). Qed.
Lemma lem5127906 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term773 _115054 _115057 s x' t x'' _66905.
Proof. exact (@lem5127870 _115054 _115057 x' x'' s t g' g'' h1 _66905). Qed.
Lemma lem5127907 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (_66905 : _115054 -> _115057) : (term773 _115054 _115057 s x' t x'' _66905) = (term763 _115054 _115057 s x' t x'' _66905).
Proof. exact (eq_refl (term773 _115054 _115057 s x' t x'' _66905)). Qed.
Lemma lem5127908 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term763 _115054 _115057 s x' t x'' _66905.
Proof. exact (EQ_MP (@lem5127907 _115054 _115057 s x' t x'' _66905) (@lem5127906 _115054 _115057 _66905 x' x'' s t g' g'' h1)). Qed.
Lemma lem5127909 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term774 _115054 _115057 s x' t x'' _66905 _66906.
Proof. exact (@lem5127908 _115054 _115057 _66905 x' x'' s t g' g'' h1 _66906). Qed.
Lemma lem5127910 {_115054 _115057 : Type'} (s : _115054 -> Prop) (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) : (term774 _115054 _115057 s x' t x'' _66905 _66906) = (term761 _115054 _115057 s x' t x'' _66905 _66906).
Proof. exact (eq_refl (term774 _115054 _115057 s x' t x'' _66905 _66906)). Qed.
Lemma lem5127911 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term761 _115054 _115057 s x' t x'' _66905 _66906.
Proof. exact (EQ_MP (@lem5127910 _115054 _115057 s x' t x'' _66905 _66906) (@lem5127909 _115054 _115057 _66905 _66906 x' x'' s t g' g'' h1)). Qed.
Lemma lem5127912 {_115054 _115057 : Type'} (_66907 : _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term775 _115054 _115057 t s g' g'' _66907.
Proof. exact (@lem5127893 _115054 _115057 x' x'' s t g' g'' h1 _66907). Qed.
Lemma lem5127913 {_115054 _115057 : Type'} (t : _115057 -> Prop) (s : _115054 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (_66907 : _115054) : (term775 _115054 _115057 t s g' g'' _66907) = (term766 _115054 _115057 t s g' g'' _66907).
Proof. exact (eq_refl (term775 _115054 _115057 t s g' g'' _66907)). Qed.
Lemma lem5127914 {_115054 _115057 : Type'} (_66907 : _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term766 _115054 _115057 t s g' g'' _66907.
Proof. exact (EQ_MP (@lem5127913 _115054 _115057 t s g' g'' _66907) (@lem5127912 _115054 _115057 _66907 x' x'' s t g' g'' h1)). Qed.
Lemma lem5127919 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term756 _115054 _115057 s x' t x'' _66905 _66906.
Proof. exact (proj2 (@lem5127911 _115054 _115057 _66905 _66906 x' x'' s t g' g'' h1)). Qed.
Lemma lem5127920 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term758 _115054 _115057 x' t x'' _66905 _66906 s.
Proof. exact (proj1 (@lem5127911 _115054 _115057 _66905 _66906 x' x'' s t g' g'' h1)). Qed.
Lemma lem5127930 {_115054 _115057 : Type'} (_66903 : _115054) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term727 _115054 _115057 s f _66903 t.
Proof. exact (EQ_MP (@lem5127901 _115054 _115057 s f _66903 t) (@lem5127900 _115054 _115057 _66903 g f s t x h1)). Qed.
Lemma lem5127936 {_115054 _115057 : Type'} (_66904 : _115054) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term724 _115054 _115057 s g f _66904.
Proof. exact (EQ_MP (@lem5127904 _115054 _115057 s g f _66904) (@lem5127903 _115054 _115057 _66904 g f s t x h1)). Qed.
Lemma lem5127944 {_115054 _115057 : Type'} (_66901 : _115057 -> _115054) (_66902 : _115054 -> _115057) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term707 _115054 _115057 t x _66901 _66902.
Proof. exact (proj2 (@lem5127899 _115054 _115057 _66901 _66902 g f s t x h1)). Qed.
Lemma lem5127950 {_115054 _115057 : Type'} (_66907 : _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term727 _115054 _115057 s g'' _66907 t.
Proof. exact (proj1 (@lem5127914 _115054 _115057 _66907 x' x'' s t g' g'' h1)). Qed.
Lemma lem5127956 {_115054 _115057 : Type'} (_66907 : _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term724 _115054 _115057 s g' g'' _66907.
Proof. exact (proj2 (@lem5127914 _115054 _115057 _66907 x' x'' s t g' g'' h1)). Qed.
Lemma lem5127962 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term776 _115054 _115057 x' s x'' _66905 _66906.
Proof. exact (proj1 (@lem5127919 _115054 _115057 _66905 _66906 x' x'' s t g' g'' h1)). Qed.
Lemma lem5127968 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term777 _115054 _115057 x' t x'' _66905 _66906.
Proof. exact (proj2 (@lem5127919 _115054 _115057 _66905 _66906 x' x'' s t g' g'' h1)). Qed.
Lemma lem5127974 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term778 _115054 _115057 x' x'' _66905 _66906 s.
Proof. exact (proj1 (@lem5127920 _115054 _115057 _66905 _66906 x' x'' s t g' g'' h1)). Qed.
Lemma lem5127980 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term779 _115054 _115057 x' t x'' _66905 _66906 s.
Proof. exact (proj2 (@lem5127920 _115054 _115057 _66905 _66906 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128134 {_115054 _115057 : Type'} (_66901 : _115057 -> _115054) (_66902 : _115054 -> _115057) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term714 _115054 _115057 x _66901 _66902 s.
Proof. exact (proj1 (@lem5127899 _115054 _115057 _66901 _66902 g f s t x h1)). Qed.
Lemma lem5128135 {_115054 _115057 : Type'} (_66901 : _115057 -> _115054) (_66902 : _115054 -> _115057) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term714 _115054 _115057 x _66901 _66902 s.
Proof. exact (@lem5128134 _115054 _115057 _66901 _66902 g f s t x h1). Qed.
Lemma lem5128136 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term714 _115054 _115057 x g f s.
Proof. exact (@lem5128135 _115054 _115057 g f g f s t x h1). Qed.
Lemma lem5128137 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term780 _115054 _115057 x g f s.
Proof. exact (fun h0 : term781 _115054 _115057 x g f s => @lem5128136 _115054 _115057 g f s t x h1). Qed.
Lemma lem5128139 (p : Prop) : (term782 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5128140 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) : (term780 _115054 _115057 x g f s) = (term714 _115054 _115057 x g f s).
Proof. exact (@lem5128139 (term714 _115054 _115057 x g f s)). Qed.
Lemma lem5128141 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term714 _115054 _115057 x g f s.
Proof. exact (EQ_MP (@lem5128140 _115054 _115057 x g f s) (@lem5128137 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5128147 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5128148 {_115054 _115057 : Type'} (f : _115054 -> _115057) (t : _115057 -> Prop) (_66903 : _115054) (s : _115054 -> Prop) : (term727 _115054 _115057 s f _66903 t) = (term783 _115054 _115057 f t _66903 s).
Proof. exact (@lem5128147 (term616 _115054 _115057 f _66903 t) (term622 _115054 _66903 s)). Qed.
Lemma lem5128154 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5128155 {_115054 _115057 : Type'} (f : _115054 -> _115057) (t : _115057 -> Prop) (_66903 : _115054) (s : _115054 -> Prop) : (term784 _115054 _115057 s f _66903 t) = (term785 _115054 _115057 f t _66903 s).
Proof. exact (MK_COMB (@lem5128154) (@lem5128148 _115054 _115057 f t _66903 s)). Qed.
Lemma lem5128161 {_115054 _115057 : Type'} (f : _115054 -> _115057) (t : _115057 -> Prop) (_66903 : _115054) (s : _115054 -> Prop) : (term783 _115054 _115057 f t _66903 s) = (term783 _115054 _115057 f t _66903 s).
Proof. exact (eq_refl (term783 _115054 _115057 f t _66903 s)). Qed.
Lemma lem5128162 {_115054 _115057 : Type'} (f : _115054 -> _115057) (t : _115057 -> Prop) (_66903 : _115054) (s : _115054 -> Prop) : ((term727 _115054 _115057 s f _66903 t) = (term783 _115054 _115057 f t _66903 s)) = ((term783 _115054 _115057 f t _66903 s) = (term783 _115054 _115057 f t _66903 s)).
Proof. exact (MK_COMB (@lem5128155 _115054 _115057 f t _66903 s) (@lem5128161 _115054 _115057 f t _66903 s)). Qed.
Lemma lem5128164 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5128165 (x : Prop) : (x = x) = True.
Proof. exact (@lem5128164 Prop x). Qed.
Lemma lem5128166 {_115054 _115057 : Type'} (f : _115054 -> _115057) (t : _115057 -> Prop) (_66903 : _115054) (s : _115054 -> Prop) : ((term783 _115054 _115057 f t _66903 s) = (term783 _115054 _115057 f t _66903 s)) = True.
Proof. exact (@lem5128165 (term783 _115054 _115057 f t _66903 s)). Qed.
Lemma lem5128167 {_115054 _115057 : Type'} (f : _115054 -> _115057) (t : _115057 -> Prop) (_66903 : _115054) (s : _115054 -> Prop) : ((term727 _115054 _115057 s f _66903 t) = (term783 _115054 _115057 f t _66903 s)) = True.
Proof. exact (TRANS (@lem5128162 _115054 _115057 f t _66903 s) (@lem5128166 _115054 _115057 f t _66903 s)). Qed.
Lemma lem5128168 {_115054 _115057 : Type'} (f : _115054 -> _115057) (t : _115057 -> Prop) (_66903 : _115054) (s : _115054 -> Prop) : True = ((term727 _115054 _115057 s f _66903 t) = (term783 _115054 _115057 f t _66903 s)).
Proof. exact (SYM (@lem5128167 _115054 _115057 f t _66903 s)). Qed.
Lemma lem5128169 {_115054 _115057 : Type'} (f : _115054 -> _115057) (t : _115057 -> Prop) (_66903 : _115054) (s : _115054 -> Prop) : (term727 _115054 _115057 s f _66903 t) = (term783 _115054 _115057 f t _66903 s).
Proof. exact (EQ_MP (@lem5128168 _115054 _115057 f t _66903 s) (@lem0)). Qed.
Lemma lem5128170 {_115054 _115057 : Type'} (_66903 : _115054) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term783 _115054 _115057 f t _66903 s.
Proof. exact (EQ_MP (@lem5128169 _115054 _115057 f t _66903 s) (@lem5127930 _115054 _115057 _66903 g f s t x h1)). Qed.
Lemma lem5128172 (b : Prop) (a : Prop) : (a \/ b) = (term786 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5128173 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (_66903 : _115054) (t : _115057 -> Prop) : (term783 _115054 _115057 f t _66903 s) = (term787 _115054 _115057 s f _66903 t).
Proof. exact (@lem5128172 (term622 _115054 _66903 s) (term616 _115054 _115057 f _66903 t)). Qed.
Lemma lem5128175 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5128176 {_115054 : Type'} (_66903 : _115054) (s : _115054 -> Prop) : (term788 _115054 _66903 s) = (term620 _115054 _66903 s).
Proof. exact (@lem5128175 (term620 _115054 _66903 s)). Qed.
Lemma lem5128177 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5128178 {_115054 : Type'} (_66903 : _115054) (s : _115054 -> Prop) : (term789 _115054 _66903 s) = (term790 _115054 _66903 s).
Proof. exact (MK_COMB (@lem5128177) (@lem5128176 _115054 _66903 s)). Qed.
Lemma lem5128179 {_115054 _115057 : Type'} (f : _115054 -> _115057) (_66903 : _115054) (t : _115057 -> Prop) : (term616 _115054 _115057 f _66903 t) = (term616 _115054 _115057 f _66903 t).
Proof. exact (eq_refl (term616 _115054 _115057 f _66903 t)). Qed.
Lemma lem5128180 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (_66903 : _115054) (t : _115057 -> Prop) : (term787 _115054 _115057 s f _66903 t) = (term791 _115054 _115057 s f _66903 t).
Proof. exact (MK_COMB (@lem5128178 _115054 _66903 s) (@lem5128179 _115054 _115057 f _66903 t)). Qed.
Lemma lem5128181 {_115054 _115057 : Type'} (s : _115054 -> Prop) (f : _115054 -> _115057) (_66903 : _115054) (t : _115057 -> Prop) : (term783 _115054 _115057 f t _66903 s) = (term791 _115054 _115057 s f _66903 t).
Proof. exact (TRANS (@lem5128173 _115054 _115057 s f _66903 t) (@lem5128180 _115054 _115057 s f _66903 t)). Qed.
Lemma lem5128184 {_115054 _115057 : Type'} (_66903 : _115054) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term791 _115054 _115057 s f _66903 t.
Proof. exact (EQ_MP (@lem5128181 _115054 _115057 s f _66903 t) (@lem5128170 _115054 _115057 _66903 g f s t x h1)). Qed.
Lemma lem5128185 {_115054 _115057 : Type'} (_66903 : _115054) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term791 _115054 _115057 s f _66903 t.
Proof. exact (@lem5128184 _115054 _115057 _66903 g f s t x h1). Qed.
Lemma lem5128186 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term792 _115054 _115057 s x g f t.
Proof. exact (@lem5128185 _115054 _115057 (term684 _115054 _115057 x g f) g f s t x h1). Qed.
Lemma lem5128189 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term701 _115054 _115057 x g f t.
Proof. exact (@lem5128186 _115054 _115057 g f s t x h1 (@lem5128141 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5128190 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term793 _115054 _115057 x g f t.
Proof. exact (fun h0 : term703 _115054 _115057 x g f t => @lem5128189 _115054 _115057 g f s t x h1). Qed.
Lemma lem5128192 (p : Prop) : (term782 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5128193 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (f : _115054 -> _115057) (t : _115057 -> Prop) : (term793 _115054 _115057 x g f t) = (term701 _115054 _115057 x g f t).
Proof. exact (@lem5128192 (term701 _115054 _115057 x g f t)). Qed.
Lemma lem5128194 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term701 _115054 _115057 x g f t.
Proof. exact (EQ_MP (@lem5128193 _115054 _115057 x g f t) (@lem5128190 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5128196 {_115054 _115057 : Type'} (_66901 : _115057 -> _115054) (_66902 : _115054 -> _115057) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term714 _115054 _115057 x _66901 _66902 s.
Proof. exact (proj1 (@lem5127899 _115054 _115057 _66901 _66902 g f s t x h1)). Qed.
Lemma lem5128197 {_115054 _115057 : Type'} (_66901 : _115057 -> _115054) (_66902 : _115054 -> _115057) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term714 _115054 _115057 x _66901 _66902 s.
Proof. exact (@lem5128196 _115054 _115057 _66901 _66902 g f s t x h1). Qed.
Lemma lem5128198 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term714 _115054 _115057 x g f s.
Proof. exact (@lem5128197 _115054 _115057 g f g f s t x h1). Qed.
Lemma lem5128199 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term780 _115054 _115057 x g f s.
Proof. exact (fun h0 : term781 _115054 _115057 x g f s => @lem5128198 _115054 _115057 g f s t x h1). Qed.
Lemma lem5128201 (p : Prop) : (term782 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5128202 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) : (term780 _115054 _115057 x g f s) = (term714 _115054 _115057 x g f s).
Proof. exact (@lem5128201 (term714 _115054 _115057 x g f s)). Qed.
Lemma lem5128203 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term714 _115054 _115057 x g f s.
Proof. exact (EQ_MP (@lem5128202 _115054 _115057 x g f s) (@lem5128199 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5128209 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5128210 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (_66904 : _115054) (s : _115054 -> Prop) : (term724 _115054 _115057 s g f _66904) = (term794 _115054 _115057 g f _66904 s).
Proof. exact (@lem5128209 ((term608 _115054 _115057 g f _66904) = _66904) (term622 _115054 _66904 s)). Qed.
Lemma lem5128218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5128219 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (_66904 : _115054) (s : _115054 -> Prop) : (term795 _115054 _115057 s g f _66904) = (term796 _115054 _115057 g f _66904 s).
Proof. exact (MK_COMB (@lem5128218) (@lem5128210 _115054 _115057 g f _66904 s)). Qed.
Lemma lem5128227 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (_66904 : _115054) (s : _115054 -> Prop) : (term794 _115054 _115057 g f _66904 s) = (term794 _115054 _115057 g f _66904 s).
Proof. exact (eq_refl (term794 _115054 _115057 g f _66904 s)). Qed.
Lemma lem5128228 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (_66904 : _115054) (s : _115054 -> Prop) : ((term724 _115054 _115057 s g f _66904) = (term794 _115054 _115057 g f _66904 s)) = ((term794 _115054 _115057 g f _66904 s) = (term794 _115054 _115057 g f _66904 s)).
Proof. exact (MK_COMB (@lem5128219 _115054 _115057 g f _66904 s) (@lem5128227 _115054 _115057 g f _66904 s)). Qed.
Lemma lem5128230 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5128231 (x : Prop) : (x = x) = True.
Proof. exact (@lem5128230 Prop x). Qed.
Lemma lem5128232 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (_66904 : _115054) (s : _115054 -> Prop) : ((term794 _115054 _115057 g f _66904 s) = (term794 _115054 _115057 g f _66904 s)) = True.
Proof. exact (@lem5128231 (term794 _115054 _115057 g f _66904 s)). Qed.
Lemma lem5128233 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (_66904 : _115054) (s : _115054 -> Prop) : ((term724 _115054 _115057 s g f _66904) = (term794 _115054 _115057 g f _66904 s)) = True.
Proof. exact (TRANS (@lem5128228 _115054 _115057 g f _66904 s) (@lem5128232 _115054 _115057 g f _66904 s)). Qed.
Lemma lem5128234 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (_66904 : _115054) (s : _115054 -> Prop) : True = ((term724 _115054 _115057 s g f _66904) = (term794 _115054 _115057 g f _66904 s)).
Proof. exact (SYM (@lem5128233 _115054 _115057 g f _66904 s)). Qed.
Lemma lem5128235 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (_66904 : _115054) (s : _115054 -> Prop) : (term724 _115054 _115057 s g f _66904) = (term794 _115054 _115057 g f _66904 s).
Proof. exact (EQ_MP (@lem5128234 _115054 _115057 g f _66904 s) (@lem0)). Qed.
Lemma lem5128236 {_115054 _115057 : Type'} (_66904 : _115054) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term794 _115054 _115057 g f _66904 s.
Proof. exact (EQ_MP (@lem5128235 _115054 _115057 g f _66904 s) (@lem5127936 _115054 _115057 _66904 g f s t x h1)). Qed.
Lemma lem5128238 (b : Prop) (a : Prop) : (a \/ b) = (term786 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5128239 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) (_66904 : _115054) : (term794 _115054 _115057 g f _66904 s) = (term797 _115054 _115057 s g f _66904).
Proof. exact (@lem5128238 (term622 _115054 _66904 s) ((term608 _115054 _115057 g f _66904) = _66904)). Qed.
Lemma lem5128241 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5128242 {_115054 : Type'} (_66904 : _115054) (s : _115054 -> Prop) : (term788 _115054 _66904 s) = (term620 _115054 _66904 s).
Proof. exact (@lem5128241 (term620 _115054 _66904 s)). Qed.
Lemma lem5128243 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5128244 {_115054 : Type'} (_66904 : _115054) (s : _115054 -> Prop) : (term789 _115054 _66904 s) = (term790 _115054 _66904 s).
Proof. exact (MK_COMB (@lem5128243) (@lem5128242 _115054 _66904 s)). Qed.
Lemma lem5128245 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (_66904 : _115054) : ((term608 _115054 _115057 g f _66904) = _66904) = ((term608 _115054 _115057 g f _66904) = _66904).
Proof. exact (eq_refl ((term608 _115054 _115057 g f _66904) = _66904)). Qed.
Lemma lem5128246 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) (_66904 : _115054) : (term797 _115054 _115057 s g f _66904) = (term798 _115054 _115057 s g f _66904).
Proof. exact (MK_COMB (@lem5128244 _115054 _66904 s) (@lem5128245 _115054 _115057 g f _66904)). Qed.
Lemma lem5128247 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g : _115057 -> _115054) (f : _115054 -> _115057) (_66904 : _115054) : (term794 _115054 _115057 g f _66904 s) = (term798 _115054 _115057 s g f _66904).
Proof. exact (TRANS (@lem5128239 _115054 _115057 s g f _66904) (@lem5128246 _115054 _115057 s g f _66904)). Qed.
Lemma lem5128250 {_115054 _115057 : Type'} (_66904 : _115054) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term798 _115054 _115057 s g f _66904.
Proof. exact (EQ_MP (@lem5128247 _115054 _115057 s g f _66904) (@lem5128236 _115054 _115057 _66904 g f s t x h1)). Qed.
Lemma lem5128251 {_115054 _115057 : Type'} (_66904 : _115054) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term798 _115054 _115057 s g f _66904.
Proof. exact (@lem5128250 _115054 _115057 _66904 g f s t x h1). Qed.
Lemma lem5128252 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term799 _115054 _115057 s x g f.
Proof. exact (@lem5128251 _115054 _115057 (term684 _115054 _115057 x g f) g f s t x h1). Qed.
Lemma lem5128255 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : (term690 _115054 _115057 x g f) = (term684 _115054 _115057 x g f).
Proof. exact (@lem5128252 _115054 _115057 g f s t x h1 (@lem5128203 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5128256 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term800 _115054 _115057 x g f.
Proof. exact (fun h0 : term694 _115054 _115057 x g f => @lem5128255 _115054 _115057 g f s t x h1). Qed.
Lemma lem5128258 (p : Prop) : (term782 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5128259 {_115054 _115057 : Type'} (x : type779 _115054 _115057) (g : _115057 -> _115054) (f : _115054 -> _115057) : (term800 _115054 _115057 x g f) = ((term690 _115054 _115057 x g f) = (term684 _115054 _115057 x g f)).
Proof. exact (@lem5128258 ((term690 _115054 _115057 x g f) = (term684 _115054 _115057 x g f))). Qed.
Lemma lem5128260 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : (term690 _115054 _115057 x g f) = (term684 _115054 _115057 x g f).
Proof. exact (EQ_MP (@lem5128259 _115054 _115057 x g f) (@lem5128256 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5128262 (a : Prop) (b : Prop) : (term801 a b) = (term802 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5128263 {_115054 _115057 : Type'} (t : _115057 -> Prop) (x : type779 _115054 _115057) (_66901 : _115057 -> _115054) (_66902 : _115054 -> _115057) : (term707 _115054 _115057 t x _66901 _66902) = (term803 _115054 _115057 t x _66901 _66902).
Proof. exact (@lem5128262 (term701 _115054 _115057 x _66901 _66902 t) ((term690 _115054 _115057 x _66901 _66902) = (term684 _115054 _115057 x _66901 _66902))). Qed.
Lemma lem5128265 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5128266 {_115054 _115057 : Type'} (t : _115057 -> Prop) (x : type779 _115054 _115057) (_66901 : _115057 -> _115054) (_66902 : _115054 -> _115057) : (term803 _115054 _115057 t x _66901 _66902) = (term804 _115054 _115057 t x _66901 _66902).
Proof. exact (@lem5128265 (term805 _115054 _115057 t x _66901 _66902)). Qed.
Lemma lem5128267 {_115054 _115057 : Type'} (t : _115057 -> Prop) (x : type779 _115054 _115057) (_66901 : _115057 -> _115054) (_66902 : _115054 -> _115057) : (term707 _115054 _115057 t x _66901 _66902) = (term804 _115054 _115057 t x _66901 _66902).
Proof. exact (TRANS (@lem5128263 _115054 _115057 t x _66901 _66902) (@lem5128266 _115054 _115057 t x _66901 _66902)). Qed.
Lemma lem5128269 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term805 _115054 _115057 t x g f.
Proof. exact (conj (@lem5128194 _115054 _115057 g f s t x h1) (@lem5128260 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5128271 {_115054 _115057 : Type'} (_66901 : _115057 -> _115054) (_66902 : _115054 -> _115057) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term804 _115054 _115057 t x _66901 _66902.
Proof. exact (EQ_MP (@lem5128267 _115054 _115057 t x _66901 _66902) (@lem5127944 _115054 _115057 _66901 _66902 g f s t x h1)). Qed.
Lemma lem5128272 {_115054 _115057 : Type'} (_66901 : _115057 -> _115054) (_66902 : _115054 -> _115057) (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term804 _115054 _115057 t x _66901 _66902.
Proof. exact (@lem5128271 _115054 _115057 _66901 _66902 g f s t x h1). Qed.
Lemma lem5128273 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term804 _115054 _115057 t x g f.
Proof. exact (@lem5128272 _115054 _115057 g f g f s t x h1). Qed.
Lemma lem5128276 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : False.
Proof. exact (@lem5128273 _115054 _115057 g f s t x h1 (@lem5128269 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5128277 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : term806.
Proof. exact (fun h0 : ~ False => @lem5128276 _115054 _115057 g f s t x h1). Qed.
Lemma lem5128279 (p : Prop) : (term782 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5128280 : term806 = False.
Proof. exact (@lem5128279 False). Qed.
Lemma lem5128281 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (x : type779 _115054 _115057) (h1 : term733 _115054 _115057 g f s t x) : False.
Proof. exact (EQ_MP (@lem5128280) (@lem5128277 _115054 _115057 g f s t x h1)). Qed.
Lemma lem5128453 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (g'' : _115054 -> _115057) (s : _115054 -> Prop) (h1 : term807 _115054 _115057 x' g'' s) : term807 _115054 _115057 x' g'' s.
Proof. exact (h1). Qed.
Lemma lem5128454 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (g'' : _115054 -> _115057) (s : _115054 -> Prop) (h1 : term807 _115054 _115057 x' g'' s) : term808 _115054 _115057 x' g'' s.
Proof. exact (fun h0 : term672 _115054 _115057 x' g'' s => @lem5128453 _115054 _115057 x' g'' s h1). Qed.
Lemma lem5128456 (p : Prop) : (term809 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5128457 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (g'' : _115054 -> _115057) (s : _115054 -> Prop) : (term808 _115054 _115057 x' g'' s) = (term807 _115054 _115057 x' g'' s).
Proof. exact (@lem5128456 (term672 _115054 _115057 x' g'' s)). Qed.
Lemma lem5128458 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (g'' : _115054 -> _115057) (s : _115054 -> Prop) (h1 : term807 _115054 _115057 x' g'' s) : term807 _115054 _115057 x' g'' s.
Proof. exact (EQ_MP (@lem5128457 _115054 _115057 x' g'' s) (@lem5128454 _115054 _115057 x' g'' s h1)). Qed.
Lemma lem5128471 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5128472 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) : (term810 _115054 _115057 x'' _66906 x' _66905 s) = (term776 _115054 _115057 x' s x'' _66905 _66906).
Proof. exact (@lem5128471 (term672 _115054 _115057 x' _66905 s) (term638 _115054 _115057 x'' _66905 _66906)). Qed.
Lemma lem5128480 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) : (term811 _115054 _115057 x' s x'' _66905 _66906) = (term811 _115054 _115057 x' s x'' _66905 _66906).
Proof. exact (eq_refl (term811 _115054 _115057 x' s x'' _66905 _66906)). Qed.
Lemma lem5128481 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) : ((term776 _115054 _115057 x' s x'' _66905 _66906) = (term810 _115054 _115057 x'' _66906 x' _66905 s)) = ((term776 _115054 _115057 x' s x'' _66905 _66906) = (term776 _115054 _115057 x' s x'' _66905 _66906)).
Proof. exact (MK_COMB (@lem5128480 _115054 _115057 x' s x'' _66905 _66906) (@lem5128472 _115054 _115057 x' s x'' _66905 _66906)). Qed.
Lemma lem5128483 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5128484 (x : Prop) : (x = x) = True.
Proof. exact (@lem5128483 Prop x). Qed.
Lemma lem5128485 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) : ((term776 _115054 _115057 x' s x'' _66905 _66906) = (term776 _115054 _115057 x' s x'' _66905 _66906)) = True.
Proof. exact (@lem5128484 (term776 _115054 _115057 x' s x'' _66905 _66906)). Qed.
Lemma lem5128486 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (_66905 : _115054 -> _115057) (s : _115054 -> Prop) : ((term776 _115054 _115057 x' s x'' _66905 _66906) = (term810 _115054 _115057 x'' _66906 x' _66905 s)) = True.
Proof. exact (TRANS (@lem5128481 _115054 _115057 x' s x'' _66905 _66906) (@lem5128485 _115054 _115057 x' s x'' _66905 _66906)). Qed.
Lemma lem5128487 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (_66905 : _115054 -> _115057) (s : _115054 -> Prop) : True = ((term776 _115054 _115057 x' s x'' _66905 _66906) = (term810 _115054 _115057 x'' _66906 x' _66905 s)).
Proof. exact (SYM (@lem5128486 _115054 _115057 x'' _66906 x' _66905 s)). Qed.
Lemma lem5128488 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (_66905 : _115054 -> _115057) (s : _115054 -> Prop) : (term776 _115054 _115057 x' s x'' _66905 _66906) = (term810 _115054 _115057 x'' _66906 x' _66905 s).
Proof. exact (EQ_MP (@lem5128487 _115054 _115057 x'' _66906 x' _66905 s) (@lem0)). Qed.
Lemma lem5128489 {_115054 _115057 : Type'} (_66906 : _115057 -> _115054) (_66905 : _115054 -> _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term810 _115054 _115057 x'' _66906 x' _66905 s.
Proof. exact (EQ_MP (@lem5128488 _115054 _115057 x'' _66906 x' _66905 s) (@lem5127962 _115054 _115057 _66905 _66906 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128491 (b : Prop) (a : Prop) : (a \/ b) = (term786 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5128494 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (s : _115054 -> Prop) (x'' : type530 _115054 _115057) (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) : (term810 _115054 _115057 x'' _66906 x' _66905 s) = (term812 _115054 _115057 x' s x'' _66905 _66906).
Proof. exact (@lem5128491 (term672 _115054 _115057 x' _66905 s) (term638 _115054 _115057 x'' _66905 _66906)). Qed.
Lemma lem5128497 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term812 _115054 _115057 x' s x'' _66905 _66906.
Proof. exact (EQ_MP (@lem5128494 _115054 _115057 x' s x'' _66905 _66906) (@lem5128489 _115054 _115057 _66906 _66905 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128498 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term812 _115054 _115057 x' s x'' _66905 _66906.
Proof. exact (@lem5128497 _115054 _115057 _66905 _66906 x' x'' s t g' g'' h1). Qed.
Lemma lem5128499 {_115054 _115057 : Type'} (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term812 _115054 _115057 x' s x'' g'' _66906.
Proof. exact (@lem5128498 _115054 _115057 g'' _66906 x' x'' s t g' g'' h1). Qed.
Lemma lem5128502 {_115054 _115057 : Type'} (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term807 _115054 _115057 x' g'' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term638 _115054 _115057 x'' g'' _66906.
Proof. exact (@lem5128499 _115054 _115057 _66906 x' x'' s t g' g'' h2 (@lem5128458 _115054 _115057 x' g'' s h1)). Qed.
Lemma lem5128503 {_115054 _115057 : Type'} (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term807 _115054 _115057 x' g'' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term638 _115054 _115057 x'' g'' _66906.
Proof. exact (@lem5128502 _115054 _115057 _66906 x' x'' s t g' g'' h1 h2). Qed.
Lemma lem5128504 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term807 _115054 _115057 x' g'' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term638 _115054 _115057 x'' g'' g'.
Proof. exact (@lem5128503 _115054 _115057 g' x' x'' s t g' g'' h1 h2). Qed.
Lemma lem5128505 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term807 _115054 _115057 x' g'' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term813 _115054 _115057 x'' g'' g'.
Proof. exact (fun h0 : (term634 _115054 _115057 x'' g'' g') = (term628 _115054 _115057 x'' g'' g') => @lem5128504 _115054 _115057 x' x'' s t g' g'' h1 h2). Qed.
Lemma lem5128507 (p : Prop) : (term809 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5128508 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (g'' : _115054 -> _115057) (g' : _115057 -> _115054) : (term813 _115054 _115057 x'' g'' g') = (term638 _115054 _115057 x'' g'' g').
Proof. exact (@lem5128507 ((term634 _115054 _115057 x'' g'' g') = (term628 _115054 _115057 x'' g'' g'))). Qed.
Lemma lem5128509 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term807 _115054 _115057 x' g'' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term638 _115054 _115057 x'' g'' g'.
Proof. exact (EQ_MP (@lem5128508 _115054 _115057 x'' g'' g') (@lem5128505 _115054 _115057 x' x'' s t g' g'' h1 h2)). Qed.
Lemma lem5128511 (b : Prop) (a : Prop) : (a \/ b) = (term786 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5128514 {_115054 _115057 : Type'} (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (_66907 : _115054) (s : _115054 -> Prop) : (term724 _115054 _115057 s g' g'' _66907) = (term814 _115054 _115057 g' g'' _66907 s).
Proof. exact (@lem5128511 ((term608 _115054 _115057 g' g'' _66907) = _66907) (term622 _115054 _66907 s)). Qed.
Lemma lem5128517 {_115054 _115057 : Type'} (_66907 : _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term814 _115054 _115057 g' g'' _66907 s.
Proof. exact (EQ_MP (@lem5128514 _115054 _115057 g' g'' _66907 s) (@lem5127956 _115054 _115057 _66907 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128518 {_115054 _115057 : Type'} (_66907 : _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term814 _115054 _115057 g' g'' _66907 s.
Proof. exact (@lem5128517 _115054 _115057 _66907 x' x'' s t g' g'' h1). Qed.
Lemma lem5128519 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term815 _115054 _115057 x'' g'' g' s.
Proof. exact (@lem5128518 _115054 _115057 (term628 _115054 _115057 x'' g'' g') x' x'' s t g' g'' h1). Qed.
Lemma lem5128522 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term807 _115054 _115057 x' g'' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term816 _115054 _115057 x'' g'' g' s.
Proof. exact (@lem5128519 _115054 _115057 x' x'' s t g' g'' h2 (@lem5128509 _115054 _115057 x' x'' s t g' g'' h1 h2)). Qed.
Lemma lem5128523 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term807 _115054 _115057 x' g'' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term817 _115054 _115057 x'' g'' g' s.
Proof. exact (fun h0 : term645 _115054 _115057 x'' g'' g' s => @lem5128522 _115054 _115057 x' x'' s t g' g'' h1 h2). Qed.
Lemma lem5128525 (p : Prop) : (term809 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5128526 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (g'' : _115054 -> _115057) (g' : _115057 -> _115054) (s : _115054 -> Prop) : (term817 _115054 _115057 x'' g'' g' s) = (term816 _115054 _115057 x'' g'' g' s).
Proof. exact (@lem5128525 (term645 _115054 _115057 x'' g'' g' s)). Qed.
Lemma lem5128527 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term807 _115054 _115057 x' g'' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term816 _115054 _115057 x'' g'' g' s.
Proof. exact (EQ_MP (@lem5128526 _115054 _115057 x'' g'' g' s) (@lem5128523 _115054 _115057 x' x'' s t g' g'' h1 h2)). Qed.
Lemma lem5128529 (b : Prop) (a : Prop) : (a \/ b) = (term786 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5128532 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (_66905 : _115054 -> _115057) (s : _115054 -> Prop) : (term778 _115054 _115057 x' x'' _66905 _66906 s) = (term818 _115054 _115057 x'' _66906 x' _66905 s).
Proof. exact (@lem5128529 (term645 _115054 _115057 x'' _66905 _66906 s) (term672 _115054 _115057 x' _66905 s)). Qed.
Lemma lem5128535 {_115054 _115057 : Type'} (_66906 : _115057 -> _115054) (_66905 : _115054 -> _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term818 _115054 _115057 x'' _66906 x' _66905 s.
Proof. exact (EQ_MP (@lem5128532 _115054 _115057 x'' _66906 x' _66905 s) (@lem5127974 _115054 _115057 _66905 _66906 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128536 {_115054 _115057 : Type'} (_66906 : _115057 -> _115054) (_66905 : _115054 -> _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term818 _115054 _115057 x'' _66906 x' _66905 s.
Proof. exact (@lem5128535 _115054 _115057 _66906 _66905 x' x'' s t g' g'' h1). Qed.
Lemma lem5128537 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term818 _115054 _115057 x'' g' x' g'' s.
Proof. exact (@lem5128536 _115054 _115057 g' g'' x' x'' s t g' g'' h1). Qed.
Lemma lem5128540 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term807 _115054 _115057 x' g'' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term672 _115054 _115057 x' g'' s.
Proof. exact (@lem5128537 _115054 _115057 x' x'' s t g' g'' h2 (@lem5128527 _115054 _115057 x' x'' s t g' g'' h1 h2)). Qed.
Lemma lem5128541 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term819 _115054 _115057 x' g'' s.
Proof. exact (fun h0 : term807 _115054 _115057 x' g'' s => @lem5128540 _115054 _115057 x' x'' s t g' g'' h0 h1). Qed.
Lemma lem5128543 (p : Prop) : (term782 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5128544 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (g'' : _115054 -> _115057) (s : _115054 -> Prop) : (term819 _115054 _115057 x' g'' s) = (term672 _115054 _115057 x' g'' s).
Proof. exact (@lem5128543 (term672 _115054 _115057 x' g'' s)). Qed.
Lemma lem5128545 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term672 _115054 _115057 x' g'' s.
Proof. exact (EQ_MP (@lem5128544 _115054 _115057 x' g'' s) (@lem5128541 _115054 _115057 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128551 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5128552 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (t : _115057 -> Prop) (_66907 : _115054) (s : _115054 -> Prop) : (term727 _115054 _115057 s g'' _66907 t) = (term783 _115054 _115057 g'' t _66907 s).
Proof. exact (@lem5128551 (term616 _115054 _115057 g'' _66907 t) (term622 _115054 _66907 s)). Qed.
Lemma lem5128558 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5128559 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (t : _115057 -> Prop) (_66907 : _115054) (s : _115054 -> Prop) : (term784 _115054 _115057 s g'' _66907 t) = (term785 _115054 _115057 g'' t _66907 s).
Proof. exact (MK_COMB (@lem5128558) (@lem5128552 _115054 _115057 g'' t _66907 s)). Qed.
Lemma lem5128565 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (t : _115057 -> Prop) (_66907 : _115054) (s : _115054 -> Prop) : (term783 _115054 _115057 g'' t _66907 s) = (term783 _115054 _115057 g'' t _66907 s).
Proof. exact (eq_refl (term783 _115054 _115057 g'' t _66907 s)). Qed.
Lemma lem5128566 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (t : _115057 -> Prop) (_66907 : _115054) (s : _115054 -> Prop) : ((term727 _115054 _115057 s g'' _66907 t) = (term783 _115054 _115057 g'' t _66907 s)) = ((term783 _115054 _115057 g'' t _66907 s) = (term783 _115054 _115057 g'' t _66907 s)).
Proof. exact (MK_COMB (@lem5128559 _115054 _115057 g'' t _66907 s) (@lem5128565 _115054 _115057 g'' t _66907 s)). Qed.
Lemma lem5128568 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5128569 (x : Prop) : (x = x) = True.
Proof. exact (@lem5128568 Prop x). Qed.
Lemma lem5128570 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (t : _115057 -> Prop) (_66907 : _115054) (s : _115054 -> Prop) : ((term783 _115054 _115057 g'' t _66907 s) = (term783 _115054 _115057 g'' t _66907 s)) = True.
Proof. exact (@lem5128569 (term783 _115054 _115057 g'' t _66907 s)). Qed.
Lemma lem5128571 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (t : _115057 -> Prop) (_66907 : _115054) (s : _115054 -> Prop) : ((term727 _115054 _115057 s g'' _66907 t) = (term783 _115054 _115057 g'' t _66907 s)) = True.
Proof. exact (TRANS (@lem5128566 _115054 _115057 g'' t _66907 s) (@lem5128570 _115054 _115057 g'' t _66907 s)). Qed.
Lemma lem5128572 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (t : _115057 -> Prop) (_66907 : _115054) (s : _115054 -> Prop) : True = ((term727 _115054 _115057 s g'' _66907 t) = (term783 _115054 _115057 g'' t _66907 s)).
Proof. exact (SYM (@lem5128571 _115054 _115057 g'' t _66907 s)). Qed.
Lemma lem5128573 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (t : _115057 -> Prop) (_66907 : _115054) (s : _115054 -> Prop) : (term727 _115054 _115057 s g'' _66907 t) = (term783 _115054 _115057 g'' t _66907 s).
Proof. exact (EQ_MP (@lem5128572 _115054 _115057 g'' t _66907 s) (@lem0)). Qed.
Lemma lem5128574 {_115054 _115057 : Type'} (_66907 : _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term783 _115054 _115057 g'' t _66907 s.
Proof. exact (EQ_MP (@lem5128573 _115054 _115057 g'' t _66907 s) (@lem5127950 _115054 _115057 _66907 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128576 (b : Prop) (a : Prop) : (a \/ b) = (term786 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5128577 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g'' : _115054 -> _115057) (_66907 : _115054) (t : _115057 -> Prop) : (term783 _115054 _115057 g'' t _66907 s) = (term787 _115054 _115057 s g'' _66907 t).
Proof. exact (@lem5128576 (term622 _115054 _66907 s) (term616 _115054 _115057 g'' _66907 t)). Qed.
Lemma lem5128579 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5128580 {_115054 : Type'} (_66907 : _115054) (s : _115054 -> Prop) : (term788 _115054 _66907 s) = (term620 _115054 _66907 s).
Proof. exact (@lem5128579 (term620 _115054 _66907 s)). Qed.
Lemma lem5128581 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5128582 {_115054 : Type'} (_66907 : _115054) (s : _115054 -> Prop) : (term789 _115054 _66907 s) = (term790 _115054 _66907 s).
Proof. exact (MK_COMB (@lem5128581) (@lem5128580 _115054 _66907 s)). Qed.
Lemma lem5128583 {_115054 _115057 : Type'} (g'' : _115054 -> _115057) (_66907 : _115054) (t : _115057 -> Prop) : (term616 _115054 _115057 g'' _66907 t) = (term616 _115054 _115057 g'' _66907 t).
Proof. exact (eq_refl (term616 _115054 _115057 g'' _66907 t)). Qed.
Lemma lem5128584 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g'' : _115054 -> _115057) (_66907 : _115054) (t : _115057 -> Prop) : (term787 _115054 _115057 s g'' _66907 t) = (term791 _115054 _115057 s g'' _66907 t).
Proof. exact (MK_COMB (@lem5128582 _115054 _66907 s) (@lem5128583 _115054 _115057 g'' _66907 t)). Qed.
Lemma lem5128585 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g'' : _115054 -> _115057) (_66907 : _115054) (t : _115057 -> Prop) : (term783 _115054 _115057 g'' t _66907 s) = (term791 _115054 _115057 s g'' _66907 t).
Proof. exact (TRANS (@lem5128577 _115054 _115057 s g'' _66907 t) (@lem5128584 _115054 _115057 s g'' _66907 t)). Qed.
Lemma lem5128588 {_115054 _115057 : Type'} (_66907 : _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term791 _115054 _115057 s g'' _66907 t.
Proof. exact (EQ_MP (@lem5128585 _115054 _115057 s g'' _66907 t) (@lem5128574 _115054 _115057 _66907 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128589 {_115054 _115057 : Type'} (_66907 : _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term791 _115054 _115057 s g'' _66907 t.
Proof. exact (@lem5128588 _115054 _115057 _66907 x' x'' s t g' g'' h1). Qed.
Lemma lem5128590 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term820 _115054 _115057 s x' g'' t.
Proof. exact (@lem5128589 _115054 _115057 (@I ((_115054 -> _115057) -> _115054) x' g'') x' x'' s t g' g'' h1). Qed.
Lemma lem5128593 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term663 _115054 _115057 x' g'' t.
Proof. exact (@lem5128590 _115054 _115057 x' x'' s t g' g'' h1 (@lem5128545 _115054 _115057 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128594 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term821 _115054 _115057 x' g'' t.
Proof. exact (fun h0 : term665 _115054 _115057 x' g'' t => @lem5128593 _115054 _115057 x' x'' s t g' g'' h1). Qed.
Lemma lem5128596 (p : Prop) : (term782 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5128597 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (g'' : _115054 -> _115057) (t : _115057 -> Prop) : (term821 _115054 _115057 x' g'' t) = (term663 _115054 _115057 x' g'' t).
Proof. exact (@lem5128596 (term663 _115054 _115057 x' g'' t)). Qed.
Lemma lem5128598 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term663 _115054 _115057 x' g'' t.
Proof. exact (EQ_MP (@lem5128597 _115054 _115057 x' g'' t) (@lem5128594 _115054 _115057 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128601 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (g'' : _115054 -> _115057) (g' : _115057 -> _115054) (s : _115054 -> Prop) (h1 : term816 _115054 _115057 x'' g'' g' s) : term816 _115054 _115057 x'' g'' g' s.
Proof. exact (h1). Qed.
Lemma lem5128602 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (g'' : _115054 -> _115057) (g' : _115057 -> _115054) (s : _115054 -> Prop) (h1 : term816 _115054 _115057 x'' g'' g' s) : term817 _115054 _115057 x'' g'' g' s.
Proof. exact (fun h0 : term645 _115054 _115057 x'' g'' g' s => @lem5128601 _115054 _115057 x'' g'' g' s h1). Qed.
Lemma lem5128604 (p : Prop) : (term809 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5128605 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (g'' : _115054 -> _115057) (g' : _115057 -> _115054) (s : _115054 -> Prop) : (term817 _115054 _115057 x'' g'' g' s) = (term816 _115054 _115057 x'' g'' g' s).
Proof. exact (@lem5128604 (term645 _115054 _115057 x'' g'' g' s)). Qed.
Lemma lem5128606 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (g'' : _115054 -> _115057) (g' : _115057 -> _115054) (s : _115054 -> Prop) (h1 : term816 _115054 _115057 x'' g'' g' s) : term816 _115054 _115057 x'' g'' g' s.
Proof. exact (EQ_MP (@lem5128605 _115054 _115057 x'' g'' g' s) (@lem5128602 _115054 _115057 x'' g'' g' s h1)). Qed.
Lemma lem5128608 {_115054 _115057 : Type'} (_66906 : _115057 -> _115054) (_66905 : _115054 -> _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term818 _115054 _115057 x'' _66906 x' _66905 s.
Proof. exact (EQ_MP (@lem5128532 _115054 _115057 x'' _66906 x' _66905 s) (@lem5127974 _115054 _115057 _66905 _66906 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128609 {_115054 _115057 : Type'} (_66906 : _115057 -> _115054) (_66905 : _115054 -> _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term818 _115054 _115057 x'' _66906 x' _66905 s.
Proof. exact (@lem5128608 _115054 _115057 _66906 _66905 x' x'' s t g' g'' h1). Qed.
Lemma lem5128610 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term818 _115054 _115057 x'' g' x' g'' s.
Proof. exact (@lem5128609 _115054 _115057 g' g'' x' x'' s t g' g'' h1). Qed.
Lemma lem5128613 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term816 _115054 _115057 x'' g'' g' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term672 _115054 _115057 x' g'' s.
Proof. exact (@lem5128610 _115054 _115057 x' x'' s t g' g'' h2 (@lem5128606 _115054 _115057 x'' g'' g' s h1)). Qed.
Lemma lem5128614 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term816 _115054 _115057 x'' g'' g' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term819 _115054 _115057 x' g'' s.
Proof. exact (fun h0 : term807 _115054 _115057 x' g'' s => @lem5128613 _115054 _115057 x' x'' s t g' g'' h1 h2). Qed.
Lemma lem5128616 (p : Prop) : (term782 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5128617 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (g'' : _115054 -> _115057) (s : _115054 -> Prop) : (term819 _115054 _115057 x' g'' s) = (term672 _115054 _115057 x' g'' s).
Proof. exact (@lem5128616 (term672 _115054 _115057 x' g'' s)). Qed.
Lemma lem5128618 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term816 _115054 _115057 x'' g'' g' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term672 _115054 _115057 x' g'' s.
Proof. exact (EQ_MP (@lem5128617 _115054 _115057 x' g'' s) (@lem5128614 _115054 _115057 x' x'' s t g' g'' h1 h2)). Qed.
Lemma lem5128620 {_115054 _115057 : Type'} (_66907 : _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term791 _115054 _115057 s g'' _66907 t.
Proof. exact (EQ_MP (@lem5128585 _115054 _115057 s g'' _66907 t) (@lem5128574 _115054 _115057 _66907 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128621 {_115054 _115057 : Type'} (_66907 : _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term791 _115054 _115057 s g'' _66907 t.
Proof. exact (@lem5128620 _115054 _115057 _66907 x' x'' s t g' g'' h1). Qed.
Lemma lem5128622 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term820 _115054 _115057 s x' g'' t.
Proof. exact (@lem5128621 _115054 _115057 (@I ((_115054 -> _115057) -> _115054) x' g'') x' x'' s t g' g'' h1). Qed.
Lemma lem5128625 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term816 _115054 _115057 x'' g'' g' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term663 _115054 _115057 x' g'' t.
Proof. exact (@lem5128622 _115054 _115057 x' x'' s t g' g'' h2 (@lem5128618 _115054 _115057 x' x'' s t g' g'' h1 h2)). Qed.
Lemma lem5128626 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term816 _115054 _115057 x'' g'' g' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term821 _115054 _115057 x' g'' t.
Proof. exact (fun h0 : term665 _115054 _115057 x' g'' t => @lem5128625 _115054 _115057 x' x'' s t g' g'' h1 h2). Qed.
Lemma lem5128628 (p : Prop) : (term782 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5128629 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (g'' : _115054 -> _115057) (t : _115057 -> Prop) : (term821 _115054 _115057 x' g'' t) = (term663 _115054 _115057 x' g'' t).
Proof. exact (@lem5128628 (term663 _115054 _115057 x' g'' t)). Qed.
Lemma lem5128630 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term816 _115054 _115057 x'' g'' g' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term663 _115054 _115057 x' g'' t.
Proof. exact (EQ_MP (@lem5128629 _115054 _115057 x' g'' t) (@lem5128626 _115054 _115057 x' x'' s t g' g'' h1 h2)). Qed.
Lemma lem5128636 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5128637 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (_66906 : _115057 -> _115054) (s : _115054 -> Prop) (x' : type569 _115054 _115057) (_66905 : _115054 -> _115057) (t : _115057 -> Prop) : (term779 _115054 _115057 x' t x'' _66905 _66906 s) = (term822 _115054 _115057 x'' _66906 s x' _66905 t).
Proof. exact (@lem5128636 (term645 _115054 _115057 x'' _66905 _66906 s) (term665 _115054 _115057 x' _66905 t)). Qed.
Lemma lem5128643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5128644 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (_66906 : _115057 -> _115054) (s : _115054 -> Prop) (x' : type569 _115054 _115057) (_66905 : _115054 -> _115057) (t : _115057 -> Prop) : (term823 _115054 _115057 x' t x'' _66905 _66906 s) = (term824 _115054 _115057 x'' _66906 s x' _66905 t).
Proof. exact (MK_COMB (@lem5128643) (@lem5128637 _115054 _115057 x'' _66906 s x' _66905 t)). Qed.
Lemma lem5128650 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (_66906 : _115057 -> _115054) (s : _115054 -> Prop) (x' : type569 _115054 _115057) (_66905 : _115054 -> _115057) (t : _115057 -> Prop) : (term822 _115054 _115057 x'' _66906 s x' _66905 t) = (term822 _115054 _115057 x'' _66906 s x' _66905 t).
Proof. exact (eq_refl (term822 _115054 _115057 x'' _66906 s x' _66905 t)). Qed.
Lemma lem5128651 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (_66906 : _115057 -> _115054) (s : _115054 -> Prop) (x' : type569 _115054 _115057) (_66905 : _115054 -> _115057) (t : _115057 -> Prop) : ((term779 _115054 _115057 x' t x'' _66905 _66906 s) = (term822 _115054 _115057 x'' _66906 s x' _66905 t)) = ((term822 _115054 _115057 x'' _66906 s x' _66905 t) = (term822 _115054 _115057 x'' _66906 s x' _66905 t)).
Proof. exact (MK_COMB (@lem5128644 _115054 _115057 x'' _66906 s x' _66905 t) (@lem5128650 _115054 _115057 x'' _66906 s x' _66905 t)). Qed.
Lemma lem5128653 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5128654 (x : Prop) : (x = x) = True.
Proof. exact (@lem5128653 Prop x). Qed.
Lemma lem5128655 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (_66906 : _115057 -> _115054) (s : _115054 -> Prop) (x' : type569 _115054 _115057) (_66905 : _115054 -> _115057) (t : _115057 -> Prop) : ((term822 _115054 _115057 x'' _66906 s x' _66905 t) = (term822 _115054 _115057 x'' _66906 s x' _66905 t)) = True.
Proof. exact (@lem5128654 (term822 _115054 _115057 x'' _66906 s x' _66905 t)). Qed.
Lemma lem5128656 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (_66906 : _115057 -> _115054) (s : _115054 -> Prop) (x' : type569 _115054 _115057) (_66905 : _115054 -> _115057) (t : _115057 -> Prop) : ((term779 _115054 _115057 x' t x'' _66905 _66906 s) = (term822 _115054 _115057 x'' _66906 s x' _66905 t)) = True.
Proof. exact (TRANS (@lem5128651 _115054 _115057 x'' _66906 s x' _66905 t) (@lem5128655 _115054 _115057 x'' _66906 s x' _66905 t)). Qed.
Lemma lem5128657 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (_66906 : _115057 -> _115054) (s : _115054 -> Prop) (x' : type569 _115054 _115057) (_66905 : _115054 -> _115057) (t : _115057 -> Prop) : True = ((term779 _115054 _115057 x' t x'' _66905 _66906 s) = (term822 _115054 _115057 x'' _66906 s x' _66905 t)).
Proof. exact (SYM (@lem5128656 _115054 _115057 x'' _66906 s x' _66905 t)). Qed.
Lemma lem5128658 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (_66906 : _115057 -> _115054) (s : _115054 -> Prop) (x' : type569 _115054 _115057) (_66905 : _115054 -> _115057) (t : _115057 -> Prop) : (term779 _115054 _115057 x' t x'' _66905 _66906 s) = (term822 _115054 _115057 x'' _66906 s x' _66905 t).
Proof. exact (EQ_MP (@lem5128657 _115054 _115057 x'' _66906 s x' _66905 t) (@lem0)). Qed.
Lemma lem5128659 {_115054 _115057 : Type'} (_66906 : _115057 -> _115054) (_66905 : _115054 -> _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term822 _115054 _115057 x'' _66906 s x' _66905 t.
Proof. exact (EQ_MP (@lem5128658 _115054 _115057 x'' _66906 s x' _66905 t) (@lem5127980 _115054 _115057 _66905 _66906 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128661 (b : Prop) (a : Prop) : (a \/ b) = (term786 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5128662 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (s : _115054 -> Prop) : (term822 _115054 _115057 x'' _66906 s x' _66905 t) = (term825 _115054 _115057 x' t x'' _66905 _66906 s).
Proof. exact (@lem5128661 (term665 _115054 _115057 x' _66905 t) (term645 _115054 _115057 x'' _66905 _66906 s)). Qed.
Lemma lem5128664 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5128665 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (_66905 : _115054 -> _115057) (t : _115057 -> Prop) : (term826 _115054 _115057 x' _66905 t) = (term663 _115054 _115057 x' _66905 t).
Proof. exact (@lem5128664 (term663 _115054 _115057 x' _66905 t)). Qed.
Lemma lem5128666 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5128667 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (_66905 : _115054 -> _115057) (t : _115057 -> Prop) : (term827 _115054 _115057 x' _66905 t) = (term828 _115054 _115057 x' _66905 t).
Proof. exact (MK_COMB (@lem5128666) (@lem5128665 _115054 _115057 x' _66905 t)). Qed.
Lemma lem5128668 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (s : _115054 -> Prop) : (term645 _115054 _115057 x'' _66905 _66906 s) = (term645 _115054 _115057 x'' _66905 _66906 s).
Proof. exact (eq_refl (term645 _115054 _115057 x'' _66905 _66906 s)). Qed.
Lemma lem5128669 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (s : _115054 -> Prop) : (term825 _115054 _115057 x' t x'' _66905 _66906 s) = (term829 _115054 _115057 x' t x'' _66905 _66906 s).
Proof. exact (MK_COMB (@lem5128667 _115054 _115057 x' _66905 t) (@lem5128668 _115054 _115057 x'' _66905 _66906 s)). Qed.
Lemma lem5128670 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (s : _115054 -> Prop) : (term822 _115054 _115057 x'' _66906 s x' _66905 t) = (term829 _115054 _115057 x' t x'' _66905 _66906 s).
Proof. exact (TRANS (@lem5128662 _115054 _115057 x' t x'' _66905 _66906 s) (@lem5128669 _115054 _115057 x' t x'' _66905 _66906 s)). Qed.
Lemma lem5128673 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term829 _115054 _115057 x' t x'' _66905 _66906 s.
Proof. exact (EQ_MP (@lem5128670 _115054 _115057 x' t x'' _66905 _66906 s) (@lem5128659 _115054 _115057 _66906 _66905 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128674 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term829 _115054 _115057 x' t x'' _66905 _66906 s.
Proof. exact (@lem5128673 _115054 _115057 _66905 _66906 x' x'' s t g' g'' h1). Qed.
Lemma lem5128675 {_115054 _115057 : Type'} (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term829 _115054 _115057 x' t x'' g'' _66906 s.
Proof. exact (@lem5128674 _115054 _115057 g'' _66906 x' x'' s t g' g'' h1). Qed.
Lemma lem5128678 {_115054 _115057 : Type'} (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term816 _115054 _115057 x'' g'' g' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term645 _115054 _115057 x'' g'' _66906 s.
Proof. exact (@lem5128675 _115054 _115057 _66906 x' x'' s t g' g'' h2 (@lem5128630 _115054 _115057 x' x'' s t g' g'' h1 h2)). Qed.
Lemma lem5128679 {_115054 _115057 : Type'} (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term816 _115054 _115057 x'' g'' g' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term645 _115054 _115057 x'' g'' _66906 s.
Proof. exact (@lem5128678 _115054 _115057 _66906 x' x'' s t g' g'' h1 h2). Qed.
Lemma lem5128680 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term816 _115054 _115057 x'' g'' g' s) (h2 : term683 _115054 _115057 x' x'' s t g' g'') : term645 _115054 _115057 x'' g'' g' s.
Proof. exact (@lem5128679 _115054 _115057 g' x' x'' s t g' g'' h1 h2). Qed.
Lemma lem5128681 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term830 _115054 _115057 x'' g'' g' s.
Proof. exact (fun h0 : term816 _115054 _115057 x'' g'' g' s => @lem5128680 _115054 _115057 x' x'' s t g' g'' h0 h1). Qed.
Lemma lem5128683 (p : Prop) : (term782 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5128684 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (g'' : _115054 -> _115057) (g' : _115057 -> _115054) (s : _115054 -> Prop) : (term830 _115054 _115057 x'' g'' g' s) = (term645 _115054 _115057 x'' g'' g' s).
Proof. exact (@lem5128683 (term645 _115054 _115057 x'' g'' g' s)). Qed.
Lemma lem5128685 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term645 _115054 _115057 x'' g'' g' s.
Proof. exact (EQ_MP (@lem5128684 _115054 _115057 x'' g'' g' s) (@lem5128681 _115054 _115057 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128691 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5128692 {_115054 _115057 : Type'} (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (_66907 : _115054) (s : _115054 -> Prop) : (term724 _115054 _115057 s g' g'' _66907) = (term794 _115054 _115057 g' g'' _66907 s).
Proof. exact (@lem5128691 ((term608 _115054 _115057 g' g'' _66907) = _66907) (term622 _115054 _66907 s)). Qed.
Lemma lem5128700 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5128701 {_115054 _115057 : Type'} (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (_66907 : _115054) (s : _115054 -> Prop) : (term795 _115054 _115057 s g' g'' _66907) = (term796 _115054 _115057 g' g'' _66907 s).
Proof. exact (MK_COMB (@lem5128700) (@lem5128692 _115054 _115057 g' g'' _66907 s)). Qed.
Lemma lem5128709 {_115054 _115057 : Type'} (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (_66907 : _115054) (s : _115054 -> Prop) : (term794 _115054 _115057 g' g'' _66907 s) = (term794 _115054 _115057 g' g'' _66907 s).
Proof. exact (eq_refl (term794 _115054 _115057 g' g'' _66907 s)). Qed.
Lemma lem5128710 {_115054 _115057 : Type'} (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (_66907 : _115054) (s : _115054 -> Prop) : ((term724 _115054 _115057 s g' g'' _66907) = (term794 _115054 _115057 g' g'' _66907 s)) = ((term794 _115054 _115057 g' g'' _66907 s) = (term794 _115054 _115057 g' g'' _66907 s)).
Proof. exact (MK_COMB (@lem5128701 _115054 _115057 g' g'' _66907 s) (@lem5128709 _115054 _115057 g' g'' _66907 s)). Qed.
Lemma lem5128712 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5128713 (x : Prop) : (x = x) = True.
Proof. exact (@lem5128712 Prop x). Qed.
Lemma lem5128714 {_115054 _115057 : Type'} (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (_66907 : _115054) (s : _115054 -> Prop) : ((term794 _115054 _115057 g' g'' _66907 s) = (term794 _115054 _115057 g' g'' _66907 s)) = True.
Proof. exact (@lem5128713 (term794 _115054 _115057 g' g'' _66907 s)). Qed.
Lemma lem5128715 {_115054 _115057 : Type'} (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (_66907 : _115054) (s : _115054 -> Prop) : ((term724 _115054 _115057 s g' g'' _66907) = (term794 _115054 _115057 g' g'' _66907 s)) = True.
Proof. exact (TRANS (@lem5128710 _115054 _115057 g' g'' _66907 s) (@lem5128714 _115054 _115057 g' g'' _66907 s)). Qed.
Lemma lem5128716 {_115054 _115057 : Type'} (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (_66907 : _115054) (s : _115054 -> Prop) : True = ((term724 _115054 _115057 s g' g'' _66907) = (term794 _115054 _115057 g' g'' _66907 s)).
Proof. exact (SYM (@lem5128715 _115054 _115057 g' g'' _66907 s)). Qed.
Lemma lem5128717 {_115054 _115057 : Type'} (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (_66907 : _115054) (s : _115054 -> Prop) : (term724 _115054 _115057 s g' g'' _66907) = (term794 _115054 _115057 g' g'' _66907 s).
Proof. exact (EQ_MP (@lem5128716 _115054 _115057 g' g'' _66907 s) (@lem0)). Qed.
Lemma lem5128718 {_115054 _115057 : Type'} (_66907 : _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term794 _115054 _115057 g' g'' _66907 s.
Proof. exact (EQ_MP (@lem5128717 _115054 _115057 g' g'' _66907 s) (@lem5127956 _115054 _115057 _66907 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128720 (b : Prop) (a : Prop) : (a \/ b) = (term786 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5128721 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (_66907 : _115054) : (term794 _115054 _115057 g' g'' _66907 s) = (term797 _115054 _115057 s g' g'' _66907).
Proof. exact (@lem5128720 (term622 _115054 _66907 s) ((term608 _115054 _115057 g' g'' _66907) = _66907)). Qed.
Lemma lem5128723 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5128724 {_115054 : Type'} (_66907 : _115054) (s : _115054 -> Prop) : (term788 _115054 _66907 s) = (term620 _115054 _66907 s).
Proof. exact (@lem5128723 (term620 _115054 _66907 s)). Qed.
Lemma lem5128725 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5128726 {_115054 : Type'} (_66907 : _115054) (s : _115054 -> Prop) : (term789 _115054 _66907 s) = (term790 _115054 _66907 s).
Proof. exact (MK_COMB (@lem5128725) (@lem5128724 _115054 _66907 s)). Qed.
Lemma lem5128727 {_115054 _115057 : Type'} (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (_66907 : _115054) : ((term608 _115054 _115057 g' g'' _66907) = _66907) = ((term608 _115054 _115057 g' g'' _66907) = _66907).
Proof. exact (eq_refl ((term608 _115054 _115057 g' g'' _66907) = _66907)). Qed.
Lemma lem5128728 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (_66907 : _115054) : (term797 _115054 _115057 s g' g'' _66907) = (term798 _115054 _115057 s g' g'' _66907).
Proof. exact (MK_COMB (@lem5128726 _115054 _66907 s) (@lem5128727 _115054 _115057 g' g'' _66907)). Qed.
Lemma lem5128729 {_115054 _115057 : Type'} (s : _115054 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (_66907 : _115054) : (term794 _115054 _115057 g' g'' _66907 s) = (term798 _115054 _115057 s g' g'' _66907).
Proof. exact (TRANS (@lem5128721 _115054 _115057 s g' g'' _66907) (@lem5128728 _115054 _115057 s g' g'' _66907)). Qed.
Lemma lem5128732 {_115054 _115057 : Type'} (_66907 : _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term798 _115054 _115057 s g' g'' _66907.
Proof. exact (EQ_MP (@lem5128729 _115054 _115057 s g' g'' _66907) (@lem5128718 _115054 _115057 _66907 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128733 {_115054 _115057 : Type'} (_66907 : _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term798 _115054 _115057 s g' g'' _66907.
Proof. exact (@lem5128732 _115054 _115057 _66907 x' x'' s t g' g'' h1). Qed.
Lemma lem5128734 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term831 _115054 _115057 s x'' g'' g'.
Proof. exact (@lem5128733 _115054 _115057 (term628 _115054 _115057 x'' g'' g') x' x'' s t g' g'' h1). Qed.
Lemma lem5128737 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : (term634 _115054 _115057 x'' g'' g') = (term628 _115054 _115057 x'' g'' g').
Proof. exact (@lem5128734 _115054 _115057 x' x'' s t g' g'' h1 (@lem5128685 _115054 _115057 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128738 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term832 _115054 _115057 x'' g'' g'.
Proof. exact (fun h0 : term638 _115054 _115057 x'' g'' g' => @lem5128737 _115054 _115057 x' x'' s t g' g'' h1). Qed.
Lemma lem5128740 (p : Prop) : (term782 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5128741 {_115054 _115057 : Type'} (x'' : type530 _115054 _115057) (g'' : _115054 -> _115057) (g' : _115057 -> _115054) : (term832 _115054 _115057 x'' g'' g') = ((term634 _115054 _115057 x'' g'' g') = (term628 _115054 _115057 x'' g'' g')).
Proof. exact (@lem5128740 ((term634 _115054 _115057 x'' g'' g') = (term628 _115054 _115057 x'' g'' g'))). Qed.
Lemma lem5128742 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : (term634 _115054 _115057 x'' g'' g') = (term628 _115054 _115057 x'' g'' g').
Proof. exact (EQ_MP (@lem5128741 _115054 _115057 x'' g'' g') (@lem5128738 _115054 _115057 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128744 (a : Prop) (b : Prop) : (term801 a b) = (term802 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5128745 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) : (term777 _115054 _115057 x' t x'' _66905 _66906) = (term833 _115054 _115057 x' t x'' _66905 _66906).
Proof. exact (@lem5128744 (term663 _115054 _115057 x' _66905 t) ((term634 _115054 _115057 x'' _66905 _66906) = (term628 _115054 _115057 x'' _66905 _66906))). Qed.
Lemma lem5128747 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5128748 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) : (term833 _115054 _115057 x' t x'' _66905 _66906) = (term834 _115054 _115057 x' t x'' _66905 _66906).
Proof. exact (@lem5128747 (term835 _115054 _115057 x' t x'' _66905 _66906)). Qed.
Lemma lem5128749 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (t : _115057 -> Prop) (x'' : type530 _115054 _115057) (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) : (term777 _115054 _115057 x' t x'' _66905 _66906) = (term834 _115054 _115057 x' t x'' _66905 _66906).
Proof. exact (TRANS (@lem5128745 _115054 _115057 x' t x'' _66905 _66906) (@lem5128748 _115054 _115057 x' t x'' _66905 _66906)). Qed.
Lemma lem5128751 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term835 _115054 _115057 x' t x'' g'' g'.
Proof. exact (conj (@lem5128598 _115054 _115057 x' x'' s t g' g'' h1) (@lem5128742 _115054 _115057 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128753 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term834 _115054 _115057 x' t x'' _66905 _66906.
Proof. exact (EQ_MP (@lem5128749 _115054 _115057 x' t x'' _66905 _66906) (@lem5127968 _115054 _115057 _66905 _66906 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128754 {_115054 _115057 : Type'} (_66905 : _115054 -> _115057) (_66906 : _115057 -> _115054) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term834 _115054 _115057 x' t x'' _66905 _66906.
Proof. exact (@lem5128753 _115054 _115057 _66905 _66906 x' x'' s t g' g'' h1). Qed.
Lemma lem5128755 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term834 _115054 _115057 x' t x'' g'' g'.
Proof. exact (@lem5128754 _115054 _115057 g'' g' x' x'' s t g' g'' h1). Qed.
Lemma lem5128758 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : False.
Proof. exact (@lem5128755 _115054 _115057 x' x'' s t g' g'' h1 (@lem5128751 _115054 _115057 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128759 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : term806.
Proof. exact (fun h0 : ~ False => @lem5128758 _115054 _115057 x' x'' s t g' g'' h1). Qed.
Lemma lem5128761 (p : Prop) : (term782 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5128762 : term806 = False.
Proof. exact (@lem5128761 False). Qed.
Lemma lem5128763 {_115054 _115057 : Type'} (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term683 _115054 _115057 x' x'' s t g' g'') : False.
Proof. exact (EQ_MP (@lem5128762) (@lem5128759 _115054 _115057 x' x'' s t g' g'' h1)). Qed.
Lemma lem5128764 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (g'' : _115054 -> _115057) (h1 : term591 _115054 _115057 g f x x' x'' s t g' g'') : False.
Proof. exact (or_elim (@lem5127752 _115054 _115057 g f x x' x'' s t g' g'' h1) (fun h0 : term733 _115054 _115057 g f s t x => @lem5128281 _115054 _115057 g f s t x h0) (fun h0 : term683 _115054 _115057 x' x'' s t g' g'' => @lem5128763 _115054 _115057 x' x'' s t g' g'' h0)). Qed.
Lemma lem5128765 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (g' : _115057 -> _115054) (h1 : term594 _115054 _115057 g f x x' x'' s t g') : False.
Proof. exact (ex_elim (@lem5127278 _115054 _115057 g f x x' x'' s t g' h1) (fun g'' : _115054 -> _115057 => fun h0 : term593 _115054 _115057 g f x x' x'' s t g' g'' => @lem5128764 _115054 _115057 g f x x' x'' s t g' g'' h0)). Qed.
Lemma lem5128766 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (x'' : type530 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (h1 : term596 _115054 _115057 g f x x' x'' s t) : False.
Proof. exact (ex_elim (@lem5127277 _115054 _115057 g f x x' x'' s t h1) (fun g' : _115057 -> _115054 => fun h0 : term595 _115054 _115057 g f x x' x'' s t g' => @lem5128765 _115054 _115057 g f x x' x'' s t g' h0)). Qed.
Lemma lem5128767 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (x' : type569 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (h1 : term598 _115054 _115057 g f x x' s t) : False.
Proof. exact (ex_elim (@lem5127276 _115054 _115057 g f x x' s t h1) (fun x'' : type530 _115054 _115057 => fun h0 : term597 _115054 _115057 g f x x' s t x'' => @lem5128766 _115054 _115057 g f x x' x'' s t h0)). Qed.
Lemma lem5128768 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (x : type779 _115054 _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (h1 : term600 _115054 _115057 g f x s t) : False.
Proof. exact (ex_elim (@lem5127275 _115054 _115057 g f x s t h1) (fun x' : type569 _115054 _115057 => fun h0 : term599 _115054 _115057 g f x s t x' => @lem5128767 _115054 _115057 g f x x' s t h0)). Qed.
Lemma lem5128769 {_115054 _115057 : Type'} (g : _115057 -> _115054) (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (h1 : term602 _115054 _115057 g f s t) : False.
Proof. exact (ex_elim (@lem5127274 _115054 _115057 g f s t h1) (fun x : type779 _115054 _115057 => fun h0 : term601 _115054 _115057 g f s t x => @lem5128768 _115054 _115057 g f x s t h0)). Qed.
Lemma lem5128770 {_115054 _115057 : Type'} (f : _115054 -> _115057) (s : _115054 -> Prop) (t : _115057 -> Prop) (h1 : term604 _115054 _115057 f s t) : False.
Proof. exact (ex_elim (@lem5127273 _115054 _115057 f s t h1) (fun g : _115057 -> _115054 => fun h0 : term603 _115054 _115057 f s t g => @lem5128769 _115054 _115057 g f s t h0)). Qed.
Lemma lem5128771 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (h1 : term85 _115054 _115057 s t) : False.
Proof. exact (ex_elim (@lem5127272 _115054 _115057 s t h1) (fun f : _115054 -> _115057 => fun h0 : term605 _115054 _115057 s t f => @lem5128770 _115054 _115057 f s t h0)). Qed.
Lemma lem5128772 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (h1 : term85 _115054 _115057 s t) : (term85 _115054 _115057 s t) = False.
Proof. exact (prop_ext (fun h2 : term85 _115054 _115057 s t => @lem5128771 _115054 _115057 s t h1) (fun h2 : False => @lem5126089 _115054 _115057 s t h1)). Qed.
Lemma lem5128773 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) (h1 : term85 _115054 _115057 s t) : False.
Proof. exact (EQ_MP (@lem5128772 _115054 _115057 s t h1) (@lem5126089 _115054 _115057 s t h1)). Qed.
Lemma lem5128774 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : term84 _115054 _115057 s t.
Proof. exact (fun h0 : term85 _115054 _115057 s t => @lem5128773 _115054 _115057 s t h0). Qed.
Lemma lem5128775 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term70 _115054 _115057 t s) = (term50 _115054 _115057 s t).
Proof. exact (EQ_MP (@lem5126088 _115054 _115057 s t) (@lem5128774 _115054 _115057 s t)). Qed.
Lemma lem5128780 {_115054 _115057 : Type'} (s : _115054 -> Prop) : term73 _115054 _115057 s.
Proof. exact (fun t : _115057 -> Prop => @lem5128775 _115054 _115057 s t). Qed.
Lemma lem5128785 {_115054 _115057 : Type'} : term75 _115054 _115057.
Proof. exact (fun s : _115054 -> Prop => @lem5128780 _115054 _115057 s). Qed.
Lemma lem5128786 {_115054 _115057 : Type'} : term60 _115054 _115057.
Proof. exact (EQ_MP (@lem5126084 _115054 _115057) (@lem5128785 _115054 _115057)). Qed.
Lemma lem5128788 {_115054 _115057 : Type'} : term60 _115054 _115057.
Proof. exact (@lem5125817 _115054 _115057 (@lem5128786 _115054 _115057)). Qed.
Lemma lem5128789 {_115054 _115057 : Type'} (h1 : term61 _115054 _115057) : False.
Proof. exact (@lem5128788 _115054 _115057 (@lem5125801 _115054 _115057 h1)). Qed.
Lemma lem5128790 {_115054 _115057 : Type'} (h1 : term61 _115054 _115057) : (term61 _115054 _115057) = False.
Proof. exact (prop_ext (fun h2 : term61 _115054 _115057 => @lem5128789 _115054 _115057 h1) (fun h2 : False => @lem5125801 _115054 _115057 h1)). Qed.
Lemma lem5128791 {_115054 _115057 : Type'} (h1 : term61 _115054 _115057) : False.
Proof. exact (EQ_MP (@lem5128790 _115054 _115057 h1) (@lem5125801 _115054 _115057 h1)). Qed.
Lemma lem5128792 {_115054 _115057 : Type'} : term60 _115054 _115057.
Proof. exact (fun h0 : term61 _115054 _115057 => @lem5128791 _115054 _115057 h0). Qed.
Lemma lem5128793 {_115054 _115057 : Type'} : term58 _115054 _115057.
Proof. exact (EQ_MP (@lem5125800 _115054 _115057) (@lem5128792 _115054 _115057)). Qed.
Lemma lem5128794 {_115054 _115057 : Type'} : term57 _115054 _115057.
Proof. exact (EQ_MP (@lem5125796 _115054 _115057) (@lem5128793 _115054 _115057)). Qed.
