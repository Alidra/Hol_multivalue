Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HREAL_MUL_LZERO_term_abbrevs.
Require Import HREAL_ADD_RDISTRIB_spec.
Require Import HREAL_EQ_ADD_RCANCEL_spec.
Require Import thm1320277_spec.
Lemma lem1321768 (m : hreal) : term0 m.
Proof. exact (@lem1321459 m). Qed.
Lemma lem1321769 (m : hreal) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1321770 (m : hreal) : term1 m.
Proof. exact (EQ_MP (@lem1321769 m) (@lem1321768 m)). Qed.
Lemma lem1321771 (m : hreal) (n : hreal) : term2 m n.
Proof. exact (@lem1321770 m n). Qed.
Lemma lem1321772 (m : hreal) (n : hreal) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1321773 (m : hreal) (n : hreal) : term3 m n.
Proof. exact (EQ_MP (@lem1321772 m n) (@lem1321771 m n)). Qed.
Lemma lem1321774 (m : hreal) (n : hreal) (p : hreal) : term4 m n p.
Proof. exact (@lem1321773 m n p). Qed.
Lemma lem1321775 (p : hreal) (m : hreal) (n : hreal) : (term4 m n p) = (((hreal_add m p) = (hreal_add n p)) = (m = n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem1321778 (x : hreal) (h1 : (term5 x) = x) : (term5 x) = x.
Proof. exact (h1). Qed.
Lemma lem1321779 (x : hreal) (h1 : (term5 x) = x) : x = (term5 x).
Proof. exact (SYM (@lem1321778 x h1)). Qed.
Lemma lem1321780 (x : hreal) (h1 : x = (term5 x)) : x = (term5 x).
Proof. exact (h1). Qed.
Lemma lem1321781 (x : hreal) (h1 : x = (term5 x)) : (term5 x) = x.
Proof. exact (SYM (@lem1321780 x h1)). Qed.
Lemma lem1321782 (x : hreal) : ((term5 x) = x) = (x = (term5 x)).
Proof. exact (prop_ext (fun h1 : (term5 x) = x => @lem1321779 x h1) (fun h1 : x = (term5 x) => @lem1321781 x h1)). Qed.
Lemma lem1321783 : term6 = term7.
Proof. exact (fun_ext (fun x : hreal => @lem1321782 x)). Qed.
Lemma lem1321784 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321785 : term8 = term9.
Proof. exact (MK_COMB (@lem1321784) (@lem1321783)). Qed.
Lemma lem1321786 : term9.
Proof. exact (EQ_MP (@lem1321785) (@lem1320277)). Qed.
Lemma lem1321787 (x : hreal) : term10 x.
Proof. exact (@lem1321786 x). Qed.
Lemma lem1321788 (x : hreal) : (term10 x) = (x = (term5 x)).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1321790 (x : hreal) : term11 x.
Proof. exact (@lem1320277 x). Qed.
Lemma lem1321791 (x : hreal) : (term11 x) = ((term5 x) = x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1321793 : term12.
Proof. exact (@lem1321767 term13). Qed.
Lemma lem1321794 : term12 = term14.
Proof. exact (eq_refl term12). Qed.
Lemma lem1321795 : term14.
Proof. exact (EQ_MP (@lem1321794) (@lem1321793)). Qed.
Lemma lem1321796 : term15.
Proof. exact (@lem1321795 term16). Qed.
Lemma lem1321797 : term15 = term17.
Proof. exact (eq_refl term15). Qed.
Lemma lem1321798 : term17.
Proof. exact (EQ_MP (@lem1321797) (@lem1321796)). Qed.
Lemma lem1321799 (m : hreal) : term18 m.
Proof. exact (@lem1321798 m). Qed.
Lemma lem1321800 (m : hreal) : (term18 m) = ((term19 m) = (term20 m)).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1321801 (m : hreal) : (term19 m) = (term20 m).
Proof. exact (EQ_MP (@lem1321800 m) (@lem1321799 m)). Qed.
Lemma lem1321809 (x : hreal) : (term5 x) = x.
Proof. exact (EQ_MP (@lem1321791 x) (@lem1321790 x)). Qed.
Lemma lem1321810 : term21 = term16.
Proof. exact (@lem1321809 term16). Qed.
Lemma lem1321811 : hreal_mul = hreal_mul.
Proof. exact (eq_refl hreal_mul). Qed.
Lemma lem1321812 : term22 = term23.
Proof. exact (MK_COMB (@lem1321811) (@lem1321810)). Qed.
Lemma lem1321813 (m : hreal) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1321814 (m : hreal) : (term19 m) = (term24 m).
Proof. exact (MK_COMB (@lem1321812) (@lem1321813 m)). Qed.
Lemma lem1321815 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1321816 (m : hreal) : (term25 m) = (term26 m).
Proof. exact (MK_COMB (@lem1321815) (@lem1321814 m)). Qed.
Lemma lem1321817 (m : hreal) : (term20 m) = (term20 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem1321818 (m : hreal) : ((term19 m) = (term20 m)) = ((term24 m) = (term20 m)).
Proof. exact (MK_COMB (@lem1321816 m) (@lem1321817 m)). Qed.
Lemma lem1321821 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1321822 (m : hreal) : (term27 m) = (term28 m).
Proof. exact (MK_COMB (@lem1321821) (@lem1321818 m)). Qed.
Lemma lem1321825 (m : hreal) : ((term29 m) = term13) = ((term29 m) = term13).
Proof. exact (eq_refl ((term29 m) = term13)). Qed.
Lemma lem1321826 (m : hreal) : (term30 m) = (term31 m).
Proof. exact (MK_COMB (@lem1321822 m) (@lem1321825 m)). Qed.
Lemma lem1321831 (m : hreal) : (term31 m) = (term30 m).
Proof. exact (SYM (@lem1321826 m)). Qed.
Lemma lem1321833 (x : hreal) : x = (term5 x).
Proof. exact (EQ_MP (@lem1321788 x) (@lem1321787 x)). Qed.
Lemma lem1321834 (m : hreal) : (term24 m) = (term32 m).
Proof. exact (@lem1321833 (term24 m)). Qed.
Lemma lem1321835 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1321836 (m : hreal) : (term26 m) = (term33 m).
Proof. exact (MK_COMB (@lem1321835) (@lem1321834 m)). Qed.
Lemma lem1321837 (m : hreal) : (term20 m) = (term20 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem1321838 (m : hreal) : ((term24 m) = (term20 m)) = ((term32 m) = (term20 m)).
Proof. exact (MK_COMB (@lem1321836 m) (@lem1321837 m)). Qed.
Lemma lem1321839 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1321840 (m : hreal) : (term28 m) = (term34 m).
Proof. exact (MK_COMB (@lem1321839) (@lem1321838 m)). Qed.
Lemma lem1321841 (m : hreal) : ((term29 m) = term13) = ((term29 m) = term13).
Proof. exact (eq_refl ((term29 m) = term13)). Qed.
Lemma lem1321842 (m : hreal) : (term31 m) = (term35 m).
Proof. exact (MK_COMB (@lem1321840 m) (@lem1321841 m)). Qed.
Lemma lem1321843 (m : hreal) : (term35 m) = (term31 m).
Proof. exact (SYM (@lem1321842 m)). Qed.
Lemma lem1321849 (p : hreal) (m : hreal) (n : hreal) : ((hreal_add m p) = (hreal_add n p)) = (m = n).
Proof. exact (EQ_MP (@lem1321775 p m n) (@lem1321774 m n p)). Qed.
Lemma lem1321850 (m : hreal) : ((term32 m) = (term20 m)) = (term13 = (term29 m)).
Proof. exact (@lem1321849 (term24 m) term13 (term29 m)). Qed.
Lemma lem1321853 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1321854 (m : hreal) : (term34 m) = (term36 m).
Proof. exact (MK_COMB (@lem1321853) (@lem1321850 m)). Qed.
Lemma lem1321857 (m : hreal) : ((term29 m) = term13) = ((term29 m) = term13).
Proof. exact (eq_refl ((term29 m) = term13)). Qed.
Lemma lem1321858 (m : hreal) : (term35 m) = (term37 m).
Proof. exact (MK_COMB (@lem1321854 m) (@lem1321857 m)). Qed.
Lemma lem1321863 (m : hreal) : (term37 m) = (term35 m).
Proof. exact (SYM (@lem1321858 m)). Qed.
Lemma lem1321864 (m : hreal) (h1 : term13 = (term29 m)) : term13 = (term29 m).
Proof. exact (h1). Qed.
Lemma lem1321865 (m : hreal) (h1 : term13 = (term29 m)) : (term29 m) = term13.
Proof. exact (SYM (@lem1321864 m h1)). Qed.
Lemma lem1321866 (m : hreal) : term37 m.
Proof. exact (fun h0 : term13 = (term29 m) => @lem1321865 m h0). Qed.
Lemma lem1321867 (m : hreal) : term35 m.
Proof. exact (EQ_MP (@lem1321863 m) (@lem1321866 m)). Qed.
Lemma lem1321868 (m : hreal) : term31 m.
Proof. exact (EQ_MP (@lem1321843 m) (@lem1321867 m)). Qed.
Lemma lem1321869 (m : hreal) : term30 m.
Proof. exact (EQ_MP (@lem1321831 m) (@lem1321868 m)). Qed.
Lemma lem1321870 (m : hreal) : (term29 m) = term13.
Proof. exact (@lem1321869 m (@lem1321801 m)). Qed.
Lemma lem1321875 : term38.
Proof. exact (fun m : hreal => @lem1321870 m). Qed.
