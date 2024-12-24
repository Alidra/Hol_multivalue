Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1240755_term_abbrevs.
Require Import thm1240311_spec.
Require Import thm1240705_spec.
Lemma lem1240706 (_22730' : type1539) (h1 : _22730' = term0) : term1 = (term2 _22730').
Proof. exact (SYM (@lem1240311 _22730' h1)). Qed.
Lemma lem1240707 (_22730' : type1539) (h1 : _22730' = term0) : _22730 = (term2 _22730').
Proof. exact (TRANS (@lem1240705) (@lem1240706 _22730' h1)). Qed.
Lemma lem1240708 (a0 : Prop) : a0 = a0.
Proof. exact (eq_refl a0). Qed.
Lemma lem1240709 (a0 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0) = (term3 _22730' a0).
Proof. exact (MK_COMB (@lem1240707 _22730' h1) (@lem1240708 a0)). Qed.
Lemma lem1240710 (_22730' : type1539) (a0 : Prop) : (term3 _22730' a0) = (term4 _22730' a0).
Proof. exact (eq_refl (term3 _22730' a0)). Qed.
Lemma lem1240711 (a0 : Prop) : (term5 a0) = (term5 a0).
Proof. exact (eq_refl (term5 a0)). Qed.
Lemma lem1240712 (_22730' : type1539) (a0 : Prop) : ((_22730 a0) = (term3 _22730' a0)) = ((_22730 a0) = (term4 _22730' a0)).
Proof. exact (MK_COMB (@lem1240711 a0) (@lem1240710 _22730' a0)). Qed.
Lemma lem1240713 (a0 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0) = (term4 _22730' a0).
Proof. exact (EQ_MP (@lem1240712 _22730' a0) (@lem1240709 a0 _22730' h1)). Qed.
Lemma lem1240714 (a1 : Prop) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1240715 (a0 : Prop) (a1 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0 a1) = (term6 _22730' a0 a1).
Proof. exact (MK_COMB (@lem1240713 a0 _22730' h1) (@lem1240714 a1)). Qed.
Lemma lem1240716 (_22730' : type1539) (a0 : Prop) (a1 : Prop) : (term6 _22730' a0 a1) = (term7 _22730' a0 a1).
Proof. exact (eq_refl (term6 _22730' a0 a1)). Qed.
Lemma lem1240717 (a0 : Prop) (a1 : Prop) : (term8 a0 a1) = (term8 a0 a1).
Proof. exact (eq_refl (term8 a0 a1)). Qed.
Lemma lem1240718 (_22730' : type1539) (a0 : Prop) (a1 : Prop) : ((_22730 a0 a1) = (term6 _22730' a0 a1)) = ((_22730 a0 a1) = (term7 _22730' a0 a1)).
Proof. exact (MK_COMB (@lem1240717 a0 a1) (@lem1240716 _22730' a0 a1)). Qed.
Lemma lem1240719 (a0 : Prop) (a1 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0 a1) = (term7 _22730' a0 a1).
Proof. exact (EQ_MP (@lem1240718 _22730' a0 a1) (@lem1240715 a0 a1 _22730' h1)). Qed.
Lemma lem1240720 (a2 : Prop) : a2 = a2.
Proof. exact (eq_refl a2). Qed.
Lemma lem1240721 (a0 : Prop) (a1 : Prop) (a2 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0 a1 a2) = (term9 _22730' a0 a1 a2).
Proof. exact (MK_COMB (@lem1240719 a0 a1 _22730' h1) (@lem1240720 a2)). Qed.
Lemma lem1240722 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) : (term9 _22730' a0 a1 a2) = (term10 _22730' a0 a1 a2).
Proof. exact (eq_refl (term9 _22730' a0 a1 a2)). Qed.
Lemma lem1240723 (a0 : Prop) (a1 : Prop) (a2 : Prop) : (term11 a0 a1 a2) = (term11 a0 a1 a2).
Proof. exact (eq_refl (term11 a0 a1 a2)). Qed.
Lemma lem1240724 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) : ((_22730 a0 a1 a2) = (term9 _22730' a0 a1 a2)) = ((_22730 a0 a1 a2) = (term10 _22730' a0 a1 a2)).
Proof. exact (MK_COMB (@lem1240723 a0 a1 a2) (@lem1240722 _22730' a0 a1 a2)). Qed.
Lemma lem1240725 (a0 : Prop) (a1 : Prop) (a2 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0 a1 a2) = (term10 _22730' a0 a1 a2).
Proof. exact (EQ_MP (@lem1240724 _22730' a0 a1 a2) (@lem1240721 a0 a1 a2 _22730' h1)). Qed.
Lemma lem1240726 (a3 : Prop) : a3 = a3.
Proof. exact (eq_refl a3). Qed.
Lemma lem1240727 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0 a1 a2 a3) = (term12 _22730' a0 a1 a2 a3).
Proof. exact (MK_COMB (@lem1240725 a0 a1 a2 _22730' h1) (@lem1240726 a3)). Qed.
Lemma lem1240728 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) : (term12 _22730' a0 a1 a2 a3) = (term13 _22730' a0 a1 a2 a3).
Proof. exact (eq_refl (term12 _22730' a0 a1 a2 a3)). Qed.
Lemma lem1240729 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) : (term14 a0 a1 a2 a3) = (term14 a0 a1 a2 a3).
Proof. exact (eq_refl (term14 a0 a1 a2 a3)). Qed.
Lemma lem1240730 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) : ((_22730 a0 a1 a2 a3) = (term12 _22730' a0 a1 a2 a3)) = ((_22730 a0 a1 a2 a3) = (term13 _22730' a0 a1 a2 a3)).
Proof. exact (MK_COMB (@lem1240729 a0 a1 a2 a3) (@lem1240728 _22730' a0 a1 a2 a3)). Qed.
Lemma lem1240731 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0 a1 a2 a3) = (term13 _22730' a0 a1 a2 a3).
Proof. exact (EQ_MP (@lem1240730 _22730' a0 a1 a2 a3) (@lem1240727 a0 a1 a2 a3 _22730' h1)). Qed.
Lemma lem1240732 (a4 : Prop) : a4 = a4.
Proof. exact (eq_refl a4). Qed.
Lemma lem1240733 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0 a1 a2 a3 a4) = (term15 _22730' a0 a1 a2 a3 a4).
Proof. exact (MK_COMB (@lem1240731 a0 a1 a2 a3 _22730' h1) (@lem1240732 a4)). Qed.
Lemma lem1240734 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) : (term15 _22730' a0 a1 a2 a3 a4) = (term16 _22730' a0 a1 a2 a3 a4).
Proof. exact (eq_refl (term15 _22730' a0 a1 a2 a3 a4)). Qed.
Lemma lem1240735 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) : (term17 a0 a1 a2 a3 a4) = (term17 a0 a1 a2 a3 a4).
Proof. exact (eq_refl (term17 a0 a1 a2 a3 a4)). Qed.
Lemma lem1240736 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) : ((_22730 a0 a1 a2 a3 a4) = (term15 _22730' a0 a1 a2 a3 a4)) = ((_22730 a0 a1 a2 a3 a4) = (term16 _22730' a0 a1 a2 a3 a4)).
Proof. exact (MK_COMB (@lem1240735 a0 a1 a2 a3 a4) (@lem1240734 _22730' a0 a1 a2 a3 a4)). Qed.
Lemma lem1240737 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0 a1 a2 a3 a4) = (term16 _22730' a0 a1 a2 a3 a4).
Proof. exact (EQ_MP (@lem1240736 _22730' a0 a1 a2 a3 a4) (@lem1240733 a0 a1 a2 a3 a4 _22730' h1)). Qed.
Lemma lem1240738 (a5 : Prop) : a5 = a5.
Proof. exact (eq_refl a5). Qed.
Lemma lem1240739 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0 a1 a2 a3 a4 a5) = (term18 _22730' a0 a1 a2 a3 a4 a5).
Proof. exact (MK_COMB (@lem1240737 a0 a1 a2 a3 a4 _22730' h1) (@lem1240738 a5)). Qed.
Lemma lem1240740 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) : (term18 _22730' a0 a1 a2 a3 a4 a5) = (term19 _22730' a0 a1 a2 a3 a4 a5).
Proof. exact (eq_refl (term18 _22730' a0 a1 a2 a3 a4 a5)). Qed.
Lemma lem1240741 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) : (term20 a0 a1 a2 a3 a4 a5) = (term20 a0 a1 a2 a3 a4 a5).
Proof. exact (eq_refl (term20 a0 a1 a2 a3 a4 a5)). Qed.
Lemma lem1240742 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) : ((_22730 a0 a1 a2 a3 a4 a5) = (term18 _22730' a0 a1 a2 a3 a4 a5)) = ((_22730 a0 a1 a2 a3 a4 a5) = (term19 _22730' a0 a1 a2 a3 a4 a5)).
Proof. exact (MK_COMB (@lem1240741 a0 a1 a2 a3 a4 a5) (@lem1240740 _22730' a0 a1 a2 a3 a4 a5)). Qed.
Lemma lem1240743 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0 a1 a2 a3 a4 a5) = (term19 _22730' a0 a1 a2 a3 a4 a5).
Proof. exact (EQ_MP (@lem1240742 _22730' a0 a1 a2 a3 a4 a5) (@lem1240739 a0 a1 a2 a3 a4 a5 _22730' h1)). Qed.
Lemma lem1240744 (a6 : Prop) : a6 = a6.
Proof. exact (eq_refl a6). Qed.
Lemma lem1240745 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0 a1 a2 a3 a4 a5 a6) = (term21 _22730' a0 a1 a2 a3 a4 a5 a6).
Proof. exact (MK_COMB (@lem1240743 a0 a1 a2 a3 a4 a5 _22730' h1) (@lem1240744 a6)). Qed.
Lemma lem1240746 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) : (term21 _22730' a0 a1 a2 a3 a4 a5 a6) = (term22 _22730' a0 a1 a2 a3 a4 a5 a6).
Proof. exact (eq_refl (term21 _22730' a0 a1 a2 a3 a4 a5 a6)). Qed.
Lemma lem1240747 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) : (term23 a0 a1 a2 a3 a4 a5 a6) = (term23 a0 a1 a2 a3 a4 a5 a6).
Proof. exact (eq_refl (term23 a0 a1 a2 a3 a4 a5 a6)). Qed.
Lemma lem1240748 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) : ((_22730 a0 a1 a2 a3 a4 a5 a6) = (term21 _22730' a0 a1 a2 a3 a4 a5 a6)) = ((_22730 a0 a1 a2 a3 a4 a5 a6) = (term22 _22730' a0 a1 a2 a3 a4 a5 a6)).
Proof. exact (MK_COMB (@lem1240747 a0 a1 a2 a3 a4 a5 a6) (@lem1240746 _22730' a0 a1 a2 a3 a4 a5 a6)). Qed.
Lemma lem1240749 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0 a1 a2 a3 a4 a5 a6) = (term22 _22730' a0 a1 a2 a3 a4 a5 a6).
Proof. exact (EQ_MP (@lem1240748 _22730' a0 a1 a2 a3 a4 a5 a6) (@lem1240745 a0 a1 a2 a3 a4 a5 a6 _22730' h1)). Qed.
Lemma lem1240750 (a7 : Prop) : a7 = a7.
Proof. exact (eq_refl a7). Qed.
Lemma lem1240751 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0 a1 a2 a3 a4 a5 a6 a7) = (term24 _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1240749 a0 a1 a2 a3 a4 a5 a6 _22730' h1) (@lem1240750 a7)). Qed.
Lemma lem1240752 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term24 _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term25 _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term24 _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240753 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term26 a0 a1 a2 a3 a4 a5 a6 a7) = (term26 a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term26 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240754 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : ((_22730 a0 a1 a2 a3 a4 a5 a6 a7) = (term24 _22730' a0 a1 a2 a3 a4 a5 a6 a7)) = ((_22730 a0 a1 a2 a3 a4 a5 a6 a7) = (term25 _22730' a0 a1 a2 a3 a4 a5 a6 a7)).
Proof. exact (MK_COMB (@lem1240753 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1240752 _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240755 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : (_22730 a0 a1 a2 a3 a4 a5 a6 a7) = (term25 _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (EQ_MP (@lem1240754 _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1240751 a0 a1 a2 a3 a4 a5 a6 a7 _22730' h1)). Qed.
