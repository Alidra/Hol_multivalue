Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm71254_term_abbrevs.
Require Import thm0_spec.
Require Import thm32_spec.
Require Import thm37_spec.
Require Import thm51_spec.
Require Import thm7_spec.
Require Import thm7058_spec.
Require Import thm7129_spec.
Require Import thm7400_spec.
Require Import thm9103_spec.
Require Import thm9104_spec.
Require Import thm9120_spec.
Lemma lem70829 (a : ind) (h1 : a = IND_0) : a = IND_0.
Proof. exact (h1). Qed.
Lemma lem70830 (NUM_REP' : ind -> Prop) (h1 : NUM_REP' IND_0) : NUM_REP' IND_0.
Proof. exact (h1). Qed.
Lemma lem70831 (NUM_REP' : ind -> Prop) : NUM_REP' = NUM_REP'.
Proof. exact (eq_refl NUM_REP'). Qed.
Lemma lem70832 (NUM_REP' : ind -> Prop) (a : ind) (h1 : a = IND_0) : (NUM_REP' a) = (NUM_REP' IND_0).
Proof. exact (MK_COMB (@lem70831 NUM_REP') (@lem70829 a h1)). Qed.
Lemma lem70833 (NUM_REP' : ind -> Prop) (a : ind) (h1 : a = IND_0) : (NUM_REP' IND_0) = (NUM_REP' a).
Proof. exact (SYM (@lem70832 NUM_REP' a h1)). Qed.
Lemma lem70834 (NUM_REP' : ind -> Prop) (a : ind) (h1 : NUM_REP' IND_0) (h2 : a = IND_0) : NUM_REP' a.
Proof. exact (EQ_MP (@lem70833 NUM_REP' a h2) (@lem70830 NUM_REP' h1)). Qed.
Lemma lem70835 (a : ind) (NUM_REP' : ind -> Prop) (h1 : NUM_REP' IND_0) : term0 NUM_REP' a.
Proof. exact (fun h0 : a = IND_0 => @lem70834 NUM_REP' a h1 h0). Qed.
Lemma lem70836 (a : ind) (h1 : a = IND_0) : a = IND_0.
Proof. exact (h1). Qed.
Lemma lem70837 (NUM_REP' : ind -> Prop) (a : ind) (h1 : NUM_REP' IND_0) (h2 : a = IND_0) : NUM_REP' a.
Proof. exact (@lem70835 a NUM_REP' h1 (@lem70836 a h2)). Qed.
Lemma lem70838 (a : ind) (NUM_REP' : ind -> Prop) (h1 : NUM_REP' IND_0) : term0 NUM_REP' a.
Proof. exact (fun h0 : a = IND_0 => @lem70837 NUM_REP' a h1 h0). Qed.
Lemma lem70839 (NUM_REP' : ind -> Prop) (h1 : NUM_REP' IND_0) : term1 NUM_REP'.
Proof. exact (fun a : ind => @lem70838 a NUM_REP' h1). Qed.
Lemma lem70840 (NUM_REP' : ind -> Prop) (h1 : term1 NUM_REP') : term1 NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem70841 (NUM_REP' : ind -> Prop) (h1 : term1 NUM_REP') : term2 NUM_REP'.
Proof. exact (@lem70840 NUM_REP' h1 IND_0). Qed.
Lemma lem70842 (NUM_REP' : ind -> Prop) : (term2 NUM_REP') = (term3 NUM_REP').
Proof. exact (eq_refl (term2 NUM_REP')). Qed.
Lemma lem70843 (NUM_REP' : ind -> Prop) (h1 : term1 NUM_REP') : term3 NUM_REP'.
Proof. exact (EQ_MP (@lem70842 NUM_REP') (@lem70841 NUM_REP' h1)). Qed.
Lemma lem70844 : IND_0 = IND_0.
Proof. exact (eq_refl IND_0). Qed.
Lemma lem70845 (NUM_REP' : ind -> Prop) (h1 : term1 NUM_REP') : NUM_REP' IND_0.
Proof. exact (@lem70843 NUM_REP' h1 (@lem70844)). Qed.
Lemma lem70846 (NUM_REP' : ind -> Prop) : term4 NUM_REP'.
Proof. exact (fun h0 : term1 NUM_REP' => @lem70845 NUM_REP' h0). Qed.
Lemma lem70847 (NUM_REP' : ind -> Prop) : term5 NUM_REP'.
Proof. exact (fun h0 : NUM_REP' IND_0 => @lem70839 NUM_REP' h0). Qed.
Lemma lem70848 (NUM_REP' : ind -> Prop) : term6 NUM_REP'.
Proof. exact (conj (@lem70847 NUM_REP') (@lem70846 NUM_REP')). Qed.
Lemma lem70849 (NUM_REP' : ind -> Prop) : (term6 NUM_REP') = ((NUM_REP' IND_0) = (term1 NUM_REP')).
Proof. exact (@lem32 (NUM_REP' IND_0) (term1 NUM_REP')). Qed.
Lemma lem70850 (NUM_REP' : ind -> Prop) : (NUM_REP' IND_0) = (term1 NUM_REP').
Proof. exact (EQ_MP (@lem70849 NUM_REP') (@lem70848 NUM_REP')). Qed.
Lemma lem70851 (NUM_REP' : ind -> Prop) (a : ind) (h1 : term0 NUM_REP' a) : term0 NUM_REP' a.
Proof. exact (h1). Qed.
Lemma lem70852 (a : ind) (h1 : a = IND_0) : a = IND_0.
Proof. exact (h1). Qed.
Lemma lem70853 (NUM_REP' : ind -> Prop) (a : ind) (h1 : a = IND_0) (h2 : term0 NUM_REP' a) : NUM_REP' a.
Proof. exact (@lem70851 NUM_REP' a h2 (@lem70852 a h1)). Qed.
Lemma lem70854 (NUM_REP' : ind -> Prop) (a : ind) (h1 : a = IND_0) : term7 NUM_REP' a.
Proof. exact (fun h0 : term0 NUM_REP' a => @lem70853 NUM_REP' a h1 h0). Qed.
Lemma lem70855 (NUM_REP' : ind -> Prop) (a : ind) (h1 : term0 NUM_REP' a) : term0 NUM_REP' a.
Proof. exact (h1). Qed.
Lemma lem70856 (NUM_REP' : ind -> Prop) (a : ind) (h1 : a = IND_0) (h2 : term0 NUM_REP' a) : NUM_REP' a.
Proof. exact (@lem70854 NUM_REP' a h1 (@lem70855 NUM_REP' a h2)). Qed.
Lemma lem70857 (NUM_REP' : ind -> Prop) (a : ind) (h1 : term0 NUM_REP' a) : term0 NUM_REP' a.
Proof. exact (fun h0 : a = IND_0 => @lem70856 NUM_REP' a h0 h1). Qed.
Lemma lem70858 (NUM_REP' : ind -> Prop) (a : ind) (h1 : term0 NUM_REP' a) : term0 NUM_REP' a.
Proof. exact (h1). Qed.
Lemma lem70859 (a : ind) (h1 : a = IND_0) : a = IND_0.
Proof. exact (h1). Qed.
Lemma lem70860 (NUM_REP' : ind -> Prop) (a : ind) (h1 : a = IND_0) (h2 : term0 NUM_REP' a) : NUM_REP' a.
Proof. exact (@lem70858 NUM_REP' a h2 (@lem70859 a h1)). Qed.
Lemma lem70861 (NUM_REP' : ind -> Prop) (a : ind) (h1 : term0 NUM_REP' a) : term0 NUM_REP' a.
Proof. exact (fun h0 : a = IND_0 => @lem70860 NUM_REP' a h0 h1). Qed.
Lemma lem70862 (NUM_REP' : ind -> Prop) (a : ind) : term8 NUM_REP' a.
Proof. exact (fun h0 : term0 NUM_REP' a => @lem70861 NUM_REP' a h0). Qed.
Lemma lem70863 (NUM_REP' : ind -> Prop) (a : ind) : term8 NUM_REP' a.
Proof. exact (fun h0 : term0 NUM_REP' a => @lem70857 NUM_REP' a h0). Qed.
Lemma lem70864 (NUM_REP' : ind -> Prop) (a : ind) : term9 NUM_REP' a.
Proof. exact (conj (@lem70863 NUM_REP' a) (@lem70862 NUM_REP' a)). Qed.
Lemma lem70865 (NUM_REP' : ind -> Prop) (a : ind) : (term9 NUM_REP' a) = ((term0 NUM_REP' a) = (term0 NUM_REP' a)).
Proof. exact (@lem32 (term0 NUM_REP' a) (term0 NUM_REP' a)). Qed.
Lemma lem70866 (NUM_REP' : ind -> Prop) (a : ind) : (term0 NUM_REP' a) = (term0 NUM_REP' a).
Proof. exact (EQ_MP (@lem70865 NUM_REP' a) (@lem70864 NUM_REP' a)). Qed.
Lemma lem70867 (NUM_REP' : ind -> Prop) : (term10 NUM_REP') = (term10 NUM_REP').
Proof. exact (fun_ext (fun a : ind => @lem70866 NUM_REP' a)). Qed.
Lemma lem70868 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem70869 (NUM_REP' : ind -> Prop) : (term1 NUM_REP') = (term1 NUM_REP').
Proof. exact (MK_COMB (@lem70868) (@lem70867 NUM_REP')). Qed.
Lemma lem70870 (NUM_REP' : ind -> Prop) : (NUM_REP' IND_0) = (term1 NUM_REP').
Proof. exact (TRANS (@lem70850 NUM_REP') (@lem70869 NUM_REP')). Qed.
Lemma lem70871 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) (h1 : term11 a NUM_REP' i) : term11 a NUM_REP' i.
Proof. exact (h1). Qed.
Lemma lem70872 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) (h1 : term11 a NUM_REP' i) : NUM_REP' i.
Proof. exact (proj2 (@lem70871 a NUM_REP' i h1)). Qed.
Lemma lem70873 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) (h1 : term11 a NUM_REP' i) : a = (IND_SUC i).
Proof. exact (proj1 (@lem70871 a NUM_REP' i h1)). Qed.
Lemma lem70874 (NUM_REP' : ind -> Prop) (h1 : term12 NUM_REP') : term12 NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem70875 (i : ind) (NUM_REP' : ind -> Prop) (h1 : term12 NUM_REP') : term13 NUM_REP' i.
Proof. exact (@lem70874 NUM_REP' h1 i). Qed.
Lemma lem70876 (NUM_REP' : ind -> Prop) (i : ind) : (term13 NUM_REP' i) = (term14 NUM_REP' i).
Proof. exact (eq_refl (term13 NUM_REP' i)). Qed.
Lemma lem70877 (i : ind) (NUM_REP' : ind -> Prop) (h1 : term12 NUM_REP') : term14 NUM_REP' i.
Proof. exact (EQ_MP (@lem70876 NUM_REP' i) (@lem70875 i NUM_REP' h1)). Qed.
Lemma lem70878 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) (h1 : term12 NUM_REP') (h2 : term11 a NUM_REP' i) : term15 NUM_REP' i.
Proof. exact (@lem70877 i NUM_REP' h1 (@lem70872 a NUM_REP' i h2)). Qed.
Lemma lem70879 (NUM_REP' : ind -> Prop) : NUM_REP' = NUM_REP'.
Proof. exact (eq_refl NUM_REP'). Qed.
Lemma lem70880 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) (h1 : term11 a NUM_REP' i) : (NUM_REP' a) = (term15 NUM_REP' i).
Proof. exact (MK_COMB (@lem70879 NUM_REP') (@lem70873 a NUM_REP' i h1)). Qed.
Lemma lem70881 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) (h1 : term11 a NUM_REP' i) : (term15 NUM_REP' i) = (NUM_REP' a).
Proof. exact (SYM (@lem70880 a NUM_REP' i h1)). Qed.
Lemma lem70882 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) (h1 : term12 NUM_REP') (h2 : term11 a NUM_REP' i) : NUM_REP' a.
Proof. exact (EQ_MP (@lem70881 a NUM_REP' i h2) (@lem70878 a NUM_REP' i h1 h2)). Qed.
Lemma lem70883 (i : ind) (a : ind) (NUM_REP' : ind -> Prop) (h1 : term12 NUM_REP') : term16 i NUM_REP' a.
Proof. exact (fun h0 : term11 a NUM_REP' i => @lem70882 a NUM_REP' i h1 h0). Qed.
Lemma lem70884 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) (h1 : term11 a NUM_REP' i) : term11 a NUM_REP' i.
Proof. exact (h1). Qed.
Lemma lem70885 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) (h1 : term12 NUM_REP') (h2 : term11 a NUM_REP' i) : NUM_REP' a.
Proof. exact (@lem70883 i a NUM_REP' h1 (@lem70884 a NUM_REP' i h2)). Qed.
Lemma lem70886 (i : ind) (a : ind) (NUM_REP' : ind -> Prop) (h1 : term12 NUM_REP') : term16 i NUM_REP' a.
Proof. exact (fun h0 : term11 a NUM_REP' i => @lem70885 a NUM_REP' i h1 h0). Qed.
Lemma lem70887 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term12 NUM_REP') : term17 NUM_REP' a.
Proof. exact (fun i : ind => @lem70886 i a NUM_REP' h1). Qed.
Lemma lem70888 (NUM_REP' : ind -> Prop) (h1 : term12 NUM_REP') : term18 NUM_REP'.
Proof. exact (fun a : ind => @lem70887 a NUM_REP' h1). Qed.
Lemma lem70889 (NUM_REP' : ind -> Prop) (h1 : term18 NUM_REP') : term18 NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem70890 (i : ind) (NUM_REP' : ind -> Prop) (h1 : term18 NUM_REP') : term19 NUM_REP' i.
Proof. exact (@lem70889 NUM_REP' h1 (IND_SUC i)). Qed.
Lemma lem70891 (NUM_REP' : ind -> Prop) (i : ind) : (term19 NUM_REP' i) = (term20 NUM_REP' i).
Proof. exact (eq_refl (term19 NUM_REP' i)). Qed.
Lemma lem70892 (i : ind) (NUM_REP' : ind -> Prop) (h1 : term18 NUM_REP') : term20 NUM_REP' i.
Proof. exact (EQ_MP (@lem70891 NUM_REP' i) (@lem70890 i NUM_REP' h1)). Qed.
Lemma lem70893 (i : ind) (NUM_REP' : ind -> Prop) (h1 : term18 NUM_REP') : term21 NUM_REP' i.
Proof. exact (@lem70892 i NUM_REP' h1 i). Qed.
Lemma lem70894 (NUM_REP' : ind -> Prop) (i : ind) : (term21 NUM_REP' i) = (term22 NUM_REP' i).
Proof. exact (eq_refl (term21 NUM_REP' i)). Qed.
Lemma lem70895 (i : ind) (NUM_REP' : ind -> Prop) (h1 : term18 NUM_REP') : term22 NUM_REP' i.
Proof. exact (EQ_MP (@lem70894 NUM_REP' i) (@lem70893 i NUM_REP' h1)). Qed.
Lemma lem70896 (NUM_REP' : ind -> Prop) (i : ind) (h1 : NUM_REP' i) : NUM_REP' i.
Proof. exact (h1). Qed.
Lemma lem70897 (i : ind) : (IND_SUC i) = (IND_SUC i).
Proof. exact (eq_refl (IND_SUC i)). Qed.
Lemma lem70898 (NUM_REP' : ind -> Prop) (i : ind) (h1 : NUM_REP' i) : term23 NUM_REP' i.
Proof. exact (conj (@lem70897 i) (@lem70896 NUM_REP' i h1)). Qed.
Lemma lem70899 (NUM_REP' : ind -> Prop) (i : ind) (h1 : term18 NUM_REP') (h2 : NUM_REP' i) : term15 NUM_REP' i.
Proof. exact (@lem70895 i NUM_REP' h1 (@lem70898 NUM_REP' i h2)). Qed.
Lemma lem70900 (i : ind) (NUM_REP' : ind -> Prop) (h1 : term18 NUM_REP') : term14 NUM_REP' i.
Proof. exact (fun h0 : NUM_REP' i => @lem70899 NUM_REP' i h1 h0). Qed.
Lemma lem70901 (NUM_REP' : ind -> Prop) (h1 : term18 NUM_REP') : term12 NUM_REP'.
Proof. exact (fun i : ind => @lem70900 i NUM_REP' h1). Qed.
Lemma lem70902 (NUM_REP' : ind -> Prop) : term24 NUM_REP'.
Proof. exact (fun h0 : term18 NUM_REP' => @lem70901 NUM_REP' h0). Qed.
Lemma lem70903 (NUM_REP' : ind -> Prop) : term25 NUM_REP'.
Proof. exact (fun h0 : term12 NUM_REP' => @lem70888 NUM_REP' h0). Qed.
Lemma lem70904 (NUM_REP' : ind -> Prop) : term26 NUM_REP'.
Proof. exact (conj (@lem70903 NUM_REP') (@lem70902 NUM_REP')). Qed.
Lemma lem70905 (NUM_REP' : ind -> Prop) : (term26 NUM_REP') = ((term12 NUM_REP') = (term18 NUM_REP')).
Proof. exact (@lem32 (term12 NUM_REP') (term18 NUM_REP')). Qed.
Lemma lem70906 (NUM_REP' : ind -> Prop) : (term12 NUM_REP') = (term18 NUM_REP').
Proof. exact (EQ_MP (@lem70905 NUM_REP') (@lem70904 NUM_REP')). Qed.
Lemma lem70907 (NUM_REP' : ind -> Prop) (a : ind) (h1 : term17 NUM_REP' a) : term17 NUM_REP' a.
Proof. exact (h1). Qed.
Lemma lem70908 (i : ind) (NUM_REP' : ind -> Prop) (a : ind) (h1 : term17 NUM_REP' a) : term27 NUM_REP' a i.
Proof. exact (@lem70907 NUM_REP' a h1 i). Qed.
Lemma lem70909 (i : ind) (NUM_REP' : ind -> Prop) (a : ind) : (term27 NUM_REP' a i) = (term16 i NUM_REP' a).
Proof. exact (eq_refl (term27 NUM_REP' a i)). Qed.
Lemma lem70910 (i : ind) (NUM_REP' : ind -> Prop) (a : ind) (h1 : term17 NUM_REP' a) : term16 i NUM_REP' a.
Proof. exact (EQ_MP (@lem70909 i NUM_REP' a) (@lem70908 i NUM_REP' a h1)). Qed.
Lemma lem70911 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) (h1 : term11 a NUM_REP' i) : term11 a NUM_REP' i.
Proof. exact (h1). Qed.
Lemma lem70912 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) (h1 : term17 NUM_REP' a) (h2 : term11 a NUM_REP' i) : NUM_REP' a.
Proof. exact (@lem70910 i NUM_REP' a h1 (@lem70911 a NUM_REP' i h2)). Qed.
Lemma lem70913 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) (h1 : term11 a NUM_REP' i) : term28 NUM_REP' a.
Proof. exact (fun h0 : term17 NUM_REP' a => @lem70912 a NUM_REP' i h0 h1). Qed.
Lemma lem70914 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term29 a NUM_REP') : term29 a NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem70915 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term29 a NUM_REP') : term28 NUM_REP' a.
Proof. exact (ex_elim (@lem70914 a NUM_REP' h1) (fun i : ind => fun h0 : term30 a NUM_REP' i => @lem70913 a NUM_REP' i h0)). Qed.
Lemma lem70916 (NUM_REP' : ind -> Prop) (a : ind) (h1 : term17 NUM_REP' a) : term17 NUM_REP' a.
Proof. exact (h1). Qed.
Lemma lem70917 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term17 NUM_REP' a) (h2 : term29 a NUM_REP') : NUM_REP' a.
Proof. exact (@lem70915 a NUM_REP' h2 (@lem70916 NUM_REP' a h1)). Qed.
Lemma lem70918 (NUM_REP' : ind -> Prop) (a : ind) (h1 : term17 NUM_REP' a) : term31 NUM_REP' a.
Proof. exact (fun h0 : term29 a NUM_REP' => @lem70917 a NUM_REP' h1 h0). Qed.
Lemma lem70919 (NUM_REP' : ind -> Prop) (a : ind) (h1 : term31 NUM_REP' a) : term31 NUM_REP' a.
Proof. exact (h1). Qed.
Lemma lem70920 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) (h1 : term11 a NUM_REP' i) : term11 a NUM_REP' i.
Proof. exact (h1). Qed.
Lemma lem70921 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) (h1 : term11 a NUM_REP' i) : term29 a NUM_REP'.
Proof. exact (ex_intro (term30 a NUM_REP') i (@lem70920 a NUM_REP' i h1)). Qed.
Lemma lem70922 (i : ind) (NUM_REP' : ind -> Prop) (a : ind) (h1 : term11 a NUM_REP' i) (h2 : term31 NUM_REP' a) : NUM_REP' a.
Proof. exact (@lem70919 NUM_REP' a h2 (@lem70921 a NUM_REP' i h1)). Qed.
Lemma lem70923 (i : ind) (NUM_REP' : ind -> Prop) (a : ind) (h1 : term31 NUM_REP' a) : term16 i NUM_REP' a.
Proof. exact (fun h0 : term11 a NUM_REP' i => @lem70922 i NUM_REP' a h0 h1). Qed.
Lemma lem70924 (NUM_REP' : ind -> Prop) (a : ind) (h1 : term31 NUM_REP' a) : term17 NUM_REP' a.
Proof. exact (fun i : ind => @lem70923 i NUM_REP' a h1). Qed.
Lemma lem70925 (NUM_REP' : ind -> Prop) (a : ind) : term32 NUM_REP' a.
Proof. exact (fun h0 : term31 NUM_REP' a => @lem70924 NUM_REP' a h0). Qed.
Lemma lem70926 (NUM_REP' : ind -> Prop) (a : ind) : term33 NUM_REP' a.
Proof. exact (fun h0 : term17 NUM_REP' a => @lem70918 NUM_REP' a h0). Qed.
Lemma lem70927 (NUM_REP' : ind -> Prop) (a : ind) : term34 NUM_REP' a.
Proof. exact (conj (@lem70926 NUM_REP' a) (@lem70925 NUM_REP' a)). Qed.
Lemma lem70928 (NUM_REP' : ind -> Prop) (a : ind) : (term34 NUM_REP' a) = ((term17 NUM_REP' a) = (term31 NUM_REP' a)).
Proof. exact (@lem32 (term17 NUM_REP' a) (term31 NUM_REP' a)). Qed.
Lemma lem70929 (NUM_REP' : ind -> Prop) (a : ind) : (term17 NUM_REP' a) = (term31 NUM_REP' a).
Proof. exact (EQ_MP (@lem70928 NUM_REP' a) (@lem70927 NUM_REP' a)). Qed.
Lemma lem70930 (NUM_REP' : ind -> Prop) : (term35 NUM_REP') = (term36 NUM_REP').
Proof. exact (fun_ext (fun a : ind => @lem70929 NUM_REP' a)). Qed.
Lemma lem70931 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem70932 (NUM_REP' : ind -> Prop) : (term18 NUM_REP') = (term37 NUM_REP').
Proof. exact (MK_COMB (@lem70931) (@lem70930 NUM_REP')). Qed.
Lemma lem70933 (NUM_REP' : ind -> Prop) : (term12 NUM_REP') = (term37 NUM_REP').
Proof. exact (TRANS (@lem70906 NUM_REP') (@lem70932 NUM_REP')). Qed.
Lemma lem70935 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem9104 A x) (@lem9103 A x)). Qed.
Lemma lem70936 (x : Prop) : (x = x) = True.
Proof. exact (@lem70935 Prop x). Qed.
Lemma lem70937 (NUM_REP' : ind -> Prop) : ((term38 NUM_REP') = (term38 NUM_REP')) = True.
Proof. exact (@lem70936 (term38 NUM_REP')). Qed.
Lemma lem70938 (NUM_REP' : ind -> Prop) : True = ((term38 NUM_REP') = (term38 NUM_REP')).
Proof. exact (SYM (@lem70937 NUM_REP')). Qed.
Lemma lem70939 (NUM_REP' : ind -> Prop) : (term38 NUM_REP') = (term38 NUM_REP').
Proof. exact (EQ_MP (@lem70938 NUM_REP') (@lem0)). Qed.
Lemma lem70940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem70941 (NUM_REP' : ind -> Prop) : (term39 NUM_REP') = (term40 NUM_REP').
Proof. exact (MK_COMB (@lem70940) (@lem70870 NUM_REP')). Qed.
Lemma lem70942 (NUM_REP' : ind -> Prop) : (term41 NUM_REP') = (term38 NUM_REP').
Proof. exact (MK_COMB (@lem70941 NUM_REP') (@lem70933 NUM_REP')). Qed.
Lemma lem70943 (NUM_REP' : ind -> Prop) : (term41 NUM_REP') = (term38 NUM_REP').
Proof. exact (TRANS (@lem70942 NUM_REP') (@lem70939 NUM_REP')). Qed.
Lemma lem70944 (NUM_REP' : ind -> Prop) (h1 : term38 NUM_REP') : term38 NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem70945 (NUM_REP' : ind -> Prop) (h1 : term38 NUM_REP') : term37 NUM_REP'.
Proof. exact (proj2 (@lem70944 NUM_REP' h1)). Qed.
Lemma lem70946 (NUM_REP' : ind -> Prop) (h1 : term38 NUM_REP') : term1 NUM_REP'.
Proof. exact (proj1 (@lem70944 NUM_REP' h1)). Qed.
Lemma lem70947 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term38 NUM_REP') : term42 NUM_REP' a.
Proof. exact (@lem70946 NUM_REP' h1 a). Qed.
Lemma lem70948 (NUM_REP' : ind -> Prop) (a : ind) : (term42 NUM_REP' a) = (term0 NUM_REP' a).
Proof. exact (eq_refl (term42 NUM_REP' a)). Qed.
Lemma lem70949 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term38 NUM_REP') : term0 NUM_REP' a.
Proof. exact (EQ_MP (@lem70948 NUM_REP' a) (@lem70947 a NUM_REP' h1)). Qed.
Lemma lem70950 (a : ind) (h1 : a = IND_0) : a = IND_0.
Proof. exact (h1). Qed.
Lemma lem70951 (NUM_REP' : ind -> Prop) (a : ind) (h1 : term38 NUM_REP') (h2 : a = IND_0) : NUM_REP' a.
Proof. exact (@lem70949 a NUM_REP' h1 (@lem70950 a h2)). Qed.
Lemma lem70952 (NUM_REP' : ind -> Prop) (a : ind) (h1 : a = IND_0) : term43 NUM_REP' a.
Proof. exact (fun h0 : term38 NUM_REP' => @lem70951 NUM_REP' a h0 h1). Qed.
Lemma lem70953 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term38 NUM_REP') : term44 NUM_REP' a.
Proof. exact (@lem70945 NUM_REP' h1 a). Qed.
Lemma lem70954 (NUM_REP' : ind -> Prop) (a : ind) : (term44 NUM_REP' a) = (term31 NUM_REP' a).
Proof. exact (eq_refl (term44 NUM_REP' a)). Qed.
Lemma lem70955 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term38 NUM_REP') : term31 NUM_REP' a.
Proof. exact (EQ_MP (@lem70954 NUM_REP' a) (@lem70953 a NUM_REP' h1)). Qed.
Lemma lem70956 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term29 a NUM_REP') : term29 a NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem70957 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term29 a NUM_REP') (h2 : term38 NUM_REP') : NUM_REP' a.
Proof. exact (@lem70955 a NUM_REP' h2 (@lem70956 a NUM_REP' h1)). Qed.
Lemma lem70958 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term29 a NUM_REP') : term43 NUM_REP' a.
Proof. exact (fun h0 : term38 NUM_REP' => @lem70957 a NUM_REP' h1 h0). Qed.
Lemma lem70959 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term45 a NUM_REP') : term45 a NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem70960 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term45 a NUM_REP') : term43 NUM_REP' a.
Proof. exact (or_elim (@lem70959 a NUM_REP' h1) (fun h0 : a = IND_0 => @lem70952 NUM_REP' a h0) (fun h0 : term29 a NUM_REP' => @lem70958 a NUM_REP' h0)). Qed.
Lemma lem70961 (NUM_REP' : ind -> Prop) (h1 : term38 NUM_REP') : term38 NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem70962 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term38 NUM_REP') (h2 : term45 a NUM_REP') : NUM_REP' a.
Proof. exact (@lem70960 a NUM_REP' h2 (@lem70961 NUM_REP' h1)). Qed.
Lemma lem70963 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term38 NUM_REP') : term46 NUM_REP' a.
Proof. exact (fun h0 : term45 a NUM_REP' => @lem70962 a NUM_REP' h1 h0). Qed.
Lemma lem70964 (NUM_REP' : ind -> Prop) (h1 : term38 NUM_REP') : term47 NUM_REP'.
Proof. exact (fun a : ind => @lem70963 a NUM_REP' h1). Qed.
Lemma lem70965 (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') : term47 NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem70966 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') : term48 NUM_REP' a.
Proof. exact (@lem70965 NUM_REP' h1 a). Qed.
Lemma lem70967 (NUM_REP' : ind -> Prop) (a : ind) : (term48 NUM_REP' a) = (term46 NUM_REP' a).
Proof. exact (eq_refl (term48 NUM_REP' a)). Qed.
Lemma lem70968 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') : term46 NUM_REP' a.
Proof. exact (EQ_MP (@lem70967 NUM_REP' a) (@lem70966 a NUM_REP' h1)). Qed.
Lemma lem70969 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term45 a NUM_REP') : term45 a NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem70970 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') (h2 : term45 a NUM_REP') : NUM_REP' a.
Proof. exact (@lem70968 a NUM_REP' h1 (@lem70969 a NUM_REP' h2)). Qed.
Lemma lem70971 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term45 a NUM_REP') : term49 NUM_REP' a.
Proof. exact (fun h0 : term47 NUM_REP' => @lem70970 a NUM_REP' h0 h1). Qed.
Lemma lem70972 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term29 a NUM_REP') : term29 a NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem70973 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term29 a NUM_REP') : term45 a NUM_REP'.
Proof. exact (or_intro2 (a = IND_0) (@lem70972 a NUM_REP' h1)). Qed.
Lemma lem70974 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term29 a NUM_REP') : (term45 a NUM_REP') = (term49 NUM_REP' a).
Proof. exact (prop_ext (fun h2 : term45 a NUM_REP' => @lem70971 a NUM_REP' h2) (fun h2 : term49 NUM_REP' a => @lem70973 a NUM_REP' h1)). Qed.
Lemma lem70975 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term29 a NUM_REP') : term49 NUM_REP' a.
Proof. exact (EQ_MP (@lem70974 a NUM_REP' h1) (@lem70973 a NUM_REP' h1)). Qed.
Lemma lem70976 (a : ind) (h1 : a = IND_0) : a = IND_0.
Proof. exact (h1). Qed.
Lemma lem70977 (NUM_REP' : ind -> Prop) (a : ind) (h1 : a = IND_0) : term45 a NUM_REP'.
Proof. exact (or_intro1 (@lem70976 a h1) (term29 a NUM_REP')). Qed.
Lemma lem70978 (NUM_REP' : ind -> Prop) (a : ind) (h1 : a = IND_0) : (term45 a NUM_REP') = (term49 NUM_REP' a).
Proof. exact (prop_ext (fun h2 : term45 a NUM_REP' => @lem70971 a NUM_REP' h2) (fun h2 : term49 NUM_REP' a => @lem70977 NUM_REP' a h1)). Qed.
Lemma lem70979 (NUM_REP' : ind -> Prop) (a : ind) (h1 : a = IND_0) : term49 NUM_REP' a.
Proof. exact (EQ_MP (@lem70978 NUM_REP' a h1) (@lem70977 NUM_REP' a h1)). Qed.
Lemma lem70980 (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') : term47 NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem70981 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') (h2 : term29 a NUM_REP') : NUM_REP' a.
Proof. exact (@lem70975 a NUM_REP' h2 (@lem70980 NUM_REP' h1)). Qed.
Lemma lem70982 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') : term31 NUM_REP' a.
Proof. exact (fun h0 : term29 a NUM_REP' => @lem70981 a NUM_REP' h1 h0). Qed.
Lemma lem70983 (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') : term37 NUM_REP'.
Proof. exact (fun a : ind => @lem70982 a NUM_REP' h1). Qed.
Lemma lem70984 (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') : term47 NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem70985 (NUM_REP' : ind -> Prop) (a : ind) (h1 : term47 NUM_REP') (h2 : a = IND_0) : NUM_REP' a.
Proof. exact (@lem70979 NUM_REP' a h2 (@lem70984 NUM_REP' h1)). Qed.
Lemma lem70986 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') : term0 NUM_REP' a.
Proof. exact (fun h0 : a = IND_0 => @lem70985 NUM_REP' a h1 h0). Qed.
Lemma lem70987 (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') : term1 NUM_REP'.
Proof. exact (fun a : ind => @lem70986 a NUM_REP' h1). Qed.
Lemma lem70988 (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') : term38 NUM_REP'.
Proof. exact (conj (@lem70987 NUM_REP' h1) (@lem70983 NUM_REP' h1)). Qed.
Lemma lem70989 (NUM_REP' : ind -> Prop) : term50 NUM_REP'.
Proof. exact (fun h0 : term47 NUM_REP' => @lem70988 NUM_REP' h0). Qed.
Lemma lem70990 (NUM_REP' : ind -> Prop) : term51 NUM_REP'.
Proof. exact (fun h0 : term38 NUM_REP' => @lem70964 NUM_REP' h0). Qed.
Lemma lem70991 (NUM_REP' : ind -> Prop) : term52 NUM_REP'.
Proof. exact (conj (@lem70990 NUM_REP') (@lem70989 NUM_REP')). Qed.
Lemma lem70992 (NUM_REP' : ind -> Prop) : (term52 NUM_REP') = ((term38 NUM_REP') = (term47 NUM_REP')).
Proof. exact (@lem32 (term38 NUM_REP') (term47 NUM_REP')). Qed.
Lemma lem70993 (NUM_REP' : ind -> Prop) : (term38 NUM_REP') = (term47 NUM_REP').
Proof. exact (EQ_MP (@lem70992 NUM_REP') (@lem70991 NUM_REP')). Qed.
Lemma lem70994 (NUM_REP' : ind -> Prop) : (term41 NUM_REP') = (term47 NUM_REP').
Proof. exact (TRANS (@lem70943 NUM_REP') (@lem70993 NUM_REP')). Qed.
Lemma lem70995 (NUM_REP' : ind -> Prop) : (term47 NUM_REP') = (term41 NUM_REP').
Proof. exact (SYM (@lem70994 NUM_REP')). Qed.
Lemma lem70996 (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : NUM_REP' = term53.
Proof. exact (h1). Qed.
Lemma lem70997 (a : ind) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem70998 (a : ind) (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : (NUM_REP' a) = (term54 a).
Proof. exact (MK_COMB (@lem70996 NUM_REP' h1) (@lem70997 a)). Qed.
Lemma lem70999 (a : ind) : (term54 a) = (term55 a).
Proof. exact (eq_refl (term54 a)). Qed.
Lemma lem71000 (NUM_REP' : ind -> Prop) (a : ind) : (term56 NUM_REP' a) = (term56 NUM_REP' a).
Proof. exact (eq_refl (term56 NUM_REP' a)). Qed.
Lemma lem71001 (NUM_REP' : ind -> Prop) (a : ind) : ((NUM_REP' a) = (term54 a)) = ((NUM_REP' a) = (term55 a)).
Proof. exact (MK_COMB (@lem71000 NUM_REP' a) (@lem70999 a)). Qed.
Lemma lem71002 (a : ind) (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : (NUM_REP' a) = (term55 a).
Proof. exact (EQ_MP (@lem71001 NUM_REP' a) (@lem70998 a NUM_REP' h1)). Qed.
Lemma lem71003 (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : term57 NUM_REP'.
Proof. exact (fun a : ind => @lem71002 a NUM_REP' h1). Qed.
Lemma lem71004 (a : ind) (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : term58 NUM_REP' a.
Proof. exact (@lem71003 NUM_REP' h1 a). Qed.
Lemma lem71005 (NUM_REP' : ind -> Prop) (a : ind) : (term58 NUM_REP' a) = ((NUM_REP' a) = (term55 a)).
Proof. exact (eq_refl (term58 NUM_REP' a)). Qed.
Lemma lem71006 (a : ind) (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : (NUM_REP' a) = (term55 a).
Proof. exact (EQ_MP (@lem71005 NUM_REP' a) (@lem71004 a NUM_REP' h1)). Qed.
Lemma lem71009 (NUM_REP' : ind -> Prop) (a : ind) : term59 NUM_REP' a.
Proof. exact (@lem37 (NUM_REP' a) (term55 a)). Qed.
Lemma lem71010 (a : ind) (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : term60 NUM_REP' a.
Proof. exact (@lem71009 NUM_REP' a (@lem71006 a NUM_REP' h1)). Qed.
Lemma lem71011 (NUM_REP' : ind -> Prop) (a : ind) (h1 : NUM_REP' a) : NUM_REP' a.
Proof. exact (h1). Qed.
Lemma lem71012 (a : ind) (NUM_REP' : ind -> Prop) (h1 : NUM_REP' a) (h2 : NUM_REP' = term53) : term55 a.
Proof. exact (@lem71010 a NUM_REP' h2 (@lem71011 NUM_REP' a h1)). Qed.
Lemma lem71013 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) (h1 : NUM_REP'' a) (h2 : NUM_REP'' = term53) : term61 a NUM_REP'.
Proof. exact (@lem71012 a NUM_REP'' h1 h2 NUM_REP'). Qed.
Lemma lem71014 (NUM_REP' : ind -> Prop) (a : ind) : (term61 a NUM_REP') = (term49 NUM_REP' a).
Proof. exact (eq_refl (term61 a NUM_REP')). Qed.
Lemma lem71015 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) (h1 : NUM_REP'' a) (h2 : NUM_REP'' = term53) : term49 NUM_REP' a.
Proof. exact (EQ_MP (@lem71014 NUM_REP' a) (@lem71013 NUM_REP' a NUM_REP'' h1 h2)). Qed.
Lemma lem71016 (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') : term47 NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem71017 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) (h1 : term47 NUM_REP') (h2 : NUM_REP'' a) (h3 : NUM_REP'' = term53) : NUM_REP' a.
Proof. exact (@lem71015 NUM_REP' a NUM_REP'' h2 h3 (@lem71016 NUM_REP' h1)). Qed.
Lemma lem71018 (a : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term47 NUM_REP') (h2 : NUM_REP'' = term53) : term62 NUM_REP'' NUM_REP' a.
Proof. exact (fun h0 : NUM_REP'' a => @lem71017 NUM_REP' a NUM_REP'' h1 h0 h2). Qed.
Lemma lem71019 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term47 NUM_REP') (h2 : NUM_REP'' = term53) : term63 NUM_REP'' NUM_REP'.
Proof. exact (fun a : ind => @lem71018 a NUM_REP' NUM_REP'' h1 h2). Qed.
Lemma lem71020 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : NUM_REP'' = term53) : term64 NUM_REP'' NUM_REP'.
Proof. exact (fun h0 : term47 NUM_REP' => @lem71019 NUM_REP' NUM_REP'' h0 h1). Qed.
Lemma lem71021 (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : term65 NUM_REP'.
Proof. exact (fun NUM_REP'' : ind -> Prop => @lem71020 NUM_REP'' NUM_REP' h1). Qed.
Lemma lem71022 (h1 : term66) : term66.
Proof. exact (h1). Qed.
Lemma lem71023 (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') : term47 NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem71024 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : NUM_REP'' = term53) : term67 NUM_REP'' NUM_REP'.
Proof. exact (@lem71021 NUM_REP'' h1 NUM_REP'). Qed.
Lemma lem71025 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) : (term67 NUM_REP' NUM_REP'') = (term64 NUM_REP' NUM_REP'').
Proof. exact (eq_refl (term67 NUM_REP' NUM_REP'')). Qed.
Lemma lem71026 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : NUM_REP'' = term53) : term64 NUM_REP'' NUM_REP'.
Proof. exact (EQ_MP (@lem71025 NUM_REP'' NUM_REP') (@lem71024 NUM_REP' NUM_REP'' h1)). Qed.
Lemma lem71027 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term47 NUM_REP') (h2 : NUM_REP'' = term53) : term63 NUM_REP'' NUM_REP'.
Proof. exact (@lem71026 NUM_REP' NUM_REP'' h2 (@lem71023 NUM_REP' h1)). Qed.
Lemma lem71028 (NUM_REP' : ind -> Prop) (h1 : term66) : term68 NUM_REP'.
Proof. exact (@lem71022 h1 NUM_REP'). Qed.
Lemma lem71029 (NUM_REP' : ind -> Prop) : (term68 NUM_REP') = (term69 NUM_REP').
Proof. exact (eq_refl (term68 NUM_REP')). Qed.
Lemma lem71030 (NUM_REP' : ind -> Prop) (h1 : term66) : term69 NUM_REP'.
Proof. exact (EQ_MP (@lem71029 NUM_REP') (@lem71028 NUM_REP' h1)). Qed.
Lemma lem71031 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term66) : term70 NUM_REP' NUM_REP''.
Proof. exact (@lem71030 NUM_REP' h1 NUM_REP''). Qed.
Lemma lem71032 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) : (term70 NUM_REP' NUM_REP'') = (term71 NUM_REP' NUM_REP'').
Proof. exact (eq_refl (term70 NUM_REP' NUM_REP'')). Qed.
Lemma lem71033 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term66) : term71 NUM_REP' NUM_REP''.
Proof. exact (EQ_MP (@lem71032 NUM_REP' NUM_REP'') (@lem71031 NUM_REP' NUM_REP'' h1)). Qed.
Lemma lem71034 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term66) (h2 : term47 NUM_REP') (h3 : NUM_REP'' = term53) : term72 NUM_REP'' NUM_REP'.
Proof. exact (@lem71033 NUM_REP'' NUM_REP' h1 (@lem71027 NUM_REP' NUM_REP'' h2 h3)). Qed.
Lemma lem71035 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') : term48 NUM_REP' a.
Proof. exact (@lem71023 NUM_REP' h1 a). Qed.
Lemma lem71036 (NUM_REP' : ind -> Prop) (a : ind) : (term48 NUM_REP' a) = (term46 NUM_REP' a).
Proof. exact (eq_refl (term48 NUM_REP' a)). Qed.
Lemma lem71037 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term47 NUM_REP') : term46 NUM_REP' a.
Proof. exact (EQ_MP (@lem71036 NUM_REP' a) (@lem71035 a NUM_REP' h1)). Qed.
Lemma lem71038 (a : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term66) (h2 : term47 NUM_REP') (h3 : NUM_REP'' = term53) : term73 NUM_REP'' NUM_REP' a.
Proof. exact (@lem71034 NUM_REP' NUM_REP'' h1 h2 h3 a). Qed.
Lemma lem71039 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) : (term73 NUM_REP' NUM_REP'' a) = (term74 NUM_REP' a NUM_REP'').
Proof. exact (eq_refl (term73 NUM_REP' NUM_REP'' a)). Qed.
Lemma lem71040 (a : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term66) (h2 : term47 NUM_REP') (h3 : NUM_REP'' = term53) : term74 NUM_REP'' a NUM_REP'.
Proof. exact (EQ_MP (@lem71039 NUM_REP'' a NUM_REP') (@lem71038 a NUM_REP' NUM_REP'' h1 h2 h3)). Qed.
Lemma lem71041 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (a : ind) : term75 NUM_REP' NUM_REP'' a.
Proof. exact (@lem51 (term45 a NUM_REP'') (term45 a NUM_REP') (NUM_REP'' a)). Qed.
Lemma lem71042 (a : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term66) (h2 : term47 NUM_REP') (h3 : NUM_REP'' = term53) : term76 NUM_REP'' NUM_REP' a.
Proof. exact (@lem71041 NUM_REP'' NUM_REP' a (@lem71040 a NUM_REP' NUM_REP'' h1 h2 h3)). Qed.
Lemma lem71043 (a : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term66) (h2 : term47 NUM_REP') (h3 : NUM_REP'' = term53) : term77 NUM_REP'' NUM_REP' a.
Proof. exact (@lem71042 a NUM_REP' NUM_REP'' h1 h2 h3 (@lem71037 a NUM_REP' h2)). Qed.
Lemma lem71044 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term45 a NUM_REP') : term45 a NUM_REP'.
Proof. exact (h1). Qed.
Lemma lem71045 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) (h1 : term66) (h2 : term47 NUM_REP') (h3 : NUM_REP'' = term53) (h4 : term45 a NUM_REP'') : NUM_REP' a.
Proof. exact (@lem71043 a NUM_REP' NUM_REP'' h1 h2 h3 (@lem71044 a NUM_REP'' h4)). Qed.
Lemma lem71046 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) (h1 : term66) (h2 : NUM_REP'' = term53) (h3 : term45 a NUM_REP'') : term49 NUM_REP' a.
Proof. exact (fun h0 : term47 NUM_REP' => @lem71045 NUM_REP' a NUM_REP'' h1 h0 h2 h3). Qed.
Lemma lem71047 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) (h3 : term45 a NUM_REP') : term55 a.
Proof. exact (fun NUM_REP'' : ind -> Prop => @lem71046 NUM_REP'' a NUM_REP' h1 h2 h3). Qed.
Lemma lem71048 (a : ind) (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : term58 NUM_REP' a.
Proof. exact (@lem71003 NUM_REP' h1 a). Qed.
Lemma lem71049 (NUM_REP' : ind -> Prop) (a : ind) : (term58 NUM_REP' a) = ((NUM_REP' a) = (term55 a)).
Proof. exact (eq_refl (term58 NUM_REP' a)). Qed.
Lemma lem71050 (a : ind) (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : (NUM_REP' a) = (term55 a).
Proof. exact (EQ_MP (@lem71049 NUM_REP' a) (@lem71048 a NUM_REP' h1)). Qed.
Lemma lem71051 (a : ind) (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : (term55 a) = (NUM_REP' a).
Proof. exact (SYM (@lem71050 a NUM_REP' h1)). Qed.
Lemma lem71052 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) (h3 : term45 a NUM_REP') : NUM_REP' a.
Proof. exact (EQ_MP (@lem71051 a NUM_REP' h2) (@lem71047 a NUM_REP' h1 h2 h3)). Qed.
Lemma lem71053 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term46 NUM_REP' a.
Proof. exact (fun h0 : term45 a NUM_REP' => @lem71052 a NUM_REP' h1 h2 h0). Qed.
Lemma lem71054 (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term47 NUM_REP'.
Proof. exact (fun a : ind => @lem71053 a NUM_REP' h1 h2). Qed.
Lemma lem71057 (NUM_REP' : ind -> Prop) (a : ind) : (term78 NUM_REP' a) = (term78 NUM_REP' a).
Proof. exact (eq_refl (term78 NUM_REP' a)). Qed.
Lemma lem71058 (a : ind) (NUM_REP' : ind -> Prop) : (term78 NUM_REP' a) = (term45 a NUM_REP').
Proof. exact (eq_refl (term78 NUM_REP' a)). Qed.
Lemma lem71059 (NUM_REP' : ind -> Prop) (a : ind) : (term79 NUM_REP' a) = (term79 NUM_REP' a).
Proof. exact (eq_refl (term79 NUM_REP' a)). Qed.
Lemma lem71060 (a : ind) (NUM_REP' : ind -> Prop) : ((term78 NUM_REP' a) = (term78 NUM_REP' a)) = ((term78 NUM_REP' a) = (term45 a NUM_REP')).
Proof. exact (MK_COMB (@lem71059 NUM_REP' a) (@lem71058 a NUM_REP')). Qed.
Lemma lem71061 (a : ind) (NUM_REP' : ind -> Prop) : (term78 NUM_REP' a) = (term45 a NUM_REP').
Proof. exact (EQ_MP (@lem71060 a NUM_REP') (@lem71057 NUM_REP' a)). Qed.
Lemma lem71062 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem71063 (a : ind) (NUM_REP' : ind -> Prop) : (term80 NUM_REP' a) = (term81 a NUM_REP').
Proof. exact (MK_COMB (@lem71062) (@lem71061 a NUM_REP')). Qed.
Lemma lem71064 (NUM_REP' : ind -> Prop) (a : ind) : (NUM_REP' a) = (NUM_REP' a).
Proof. exact (eq_refl (NUM_REP' a)). Qed.
Lemma lem71065 (NUM_REP' : ind -> Prop) (a : ind) : (term82 NUM_REP' a) = (term46 NUM_REP' a).
Proof. exact (MK_COMB (@lem71063 a NUM_REP') (@lem71064 NUM_REP' a)). Qed.
Lemma lem71066 (a : ind) (NUM_REP' : ind -> Prop) : (term83 a NUM_REP') = (term83 a NUM_REP').
Proof. exact (eq_refl (term83 a NUM_REP')). Qed.
Lemma lem71067 (a : ind) (NUM_REP' : ind -> Prop) : (term84 NUM_REP' a) = (term85 a NUM_REP').
Proof. exact (MK_COMB (@lem71066 a NUM_REP') (@lem71061 a NUM_REP')). Qed.
Lemma lem71068 (NUM_REP' : ind -> Prop) (a : ind) : (term86 NUM_REP' a) = (term86 NUM_REP' a).
Proof. exact (eq_refl (term86 NUM_REP' a)). Qed.
Lemma lem71069 (a : ind) (NUM_REP' : ind -> Prop) : (term87 NUM_REP' a) = (term88 a NUM_REP').
Proof. exact (MK_COMB (@lem71068 NUM_REP' a) (@lem71061 a NUM_REP')). Qed.
Lemma lem71070 (NUM_REP' : ind -> Prop) : (term89 NUM_REP') = (term90 NUM_REP').
Proof. exact (fun_ext (fun a : ind => @lem71069 a NUM_REP')). Qed.
Lemma lem71071 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem71072 (NUM_REP' : ind -> Prop) : (term91 NUM_REP') = (term92 NUM_REP').
Proof. exact (MK_COMB (@lem71071) (@lem71070 NUM_REP')). Qed.
Lemma lem71073 (NUM_REP' : ind -> Prop) : (term93 NUM_REP') = (term94 NUM_REP').
Proof. exact (fun_ext (fun a : ind => @lem71067 a NUM_REP')). Qed.
Lemma lem71074 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem71075 (NUM_REP' : ind -> Prop) : (term95 NUM_REP') = (term96 NUM_REP').
Proof. exact (MK_COMB (@lem71074) (@lem71073 NUM_REP')). Qed.
Lemma lem71076 (NUM_REP' : ind -> Prop) : (term97 NUM_REP') = (term98 NUM_REP').
Proof. exact (fun_ext (fun a : ind => @lem71065 NUM_REP' a)). Qed.
Lemma lem71077 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem71078 (NUM_REP' : ind -> Prop) : (term99 NUM_REP') = (term47 NUM_REP').
Proof. exact (MK_COMB (@lem71077) (@lem71076 NUM_REP')). Qed.
Lemma lem71079 (NUM_REP' : ind -> Prop) : (term47 NUM_REP') = (term99 NUM_REP').
Proof. exact (SYM (@lem71078 NUM_REP')). Qed.
Lemma lem71080 (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term99 NUM_REP'.
Proof. exact (EQ_MP (@lem71079 NUM_REP') (@lem71054 NUM_REP' h1 h2)). Qed.
Lemma lem71081 (NUM_REP' : ind -> Prop) (h1 : term66) : term100 NUM_REP'.
Proof. exact (@lem71022 h1 (term101 NUM_REP')). Qed.
Lemma lem71082 (NUM_REP' : ind -> Prop) : (term100 NUM_REP') = (term102 NUM_REP').
Proof. exact (eq_refl (term100 NUM_REP')). Qed.
Lemma lem71083 (NUM_REP' : ind -> Prop) (h1 : term66) : term102 NUM_REP'.
Proof. exact (EQ_MP (@lem71082 NUM_REP') (@lem71081 NUM_REP' h1)). Qed.
Lemma lem71084 (NUM_REP' : ind -> Prop) (h1 : term66) : term103 NUM_REP'.
Proof. exact (@lem71083 NUM_REP' h1 NUM_REP'). Qed.
Lemma lem71085 (NUM_REP' : ind -> Prop) : (term103 NUM_REP') = (term104 NUM_REP').
Proof. exact (eq_refl (term103 NUM_REP')). Qed.
Lemma lem71086 (NUM_REP' : ind -> Prop) (h1 : term66) : term104 NUM_REP'.
Proof. exact (EQ_MP (@lem71085 NUM_REP') (@lem71084 NUM_REP' h1)). Qed.
Lemma lem71087 (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term96 NUM_REP'.
Proof. exact (@lem71086 NUM_REP' h1 (@lem71080 NUM_REP' h1 h2)). Qed.
Lemma lem71088 (NUM_REP' : ind -> Prop) : (term96 NUM_REP') = (term95 NUM_REP').
Proof. exact (SYM (@lem71075 NUM_REP')). Qed.
Lemma lem71089 (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term95 NUM_REP'.
Proof. exact (EQ_MP (@lem71088 NUM_REP') (@lem71087 NUM_REP' h1 h2)). Qed.
Lemma lem71090 (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : term105 NUM_REP'.
Proof. exact (@lem71021 NUM_REP' h1 (term101 NUM_REP')). Qed.
Lemma lem71091 (NUM_REP' : ind -> Prop) : (term105 NUM_REP') = (term106 NUM_REP').
Proof. exact (eq_refl (term105 NUM_REP')). Qed.
Lemma lem71092 (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : term106 NUM_REP'.
Proof. exact (EQ_MP (@lem71091 NUM_REP') (@lem71090 NUM_REP' h1)). Qed.
Lemma lem71093 (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term91 NUM_REP'.
Proof. exact (@lem71092 NUM_REP' h2 (@lem71089 NUM_REP' h1 h2)). Qed.
Lemma lem71094 (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term92 NUM_REP'.
Proof. exact (EQ_MP (@lem71072 NUM_REP') (@lem71093 NUM_REP' h1 h2)). Qed.
Lemma lem71095 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term48 NUM_REP' a.
Proof. exact (@lem71054 NUM_REP' h1 h2 a). Qed.
Lemma lem71096 (NUM_REP' : ind -> Prop) (a : ind) : (term48 NUM_REP' a) = (term46 NUM_REP' a).
Proof. exact (eq_refl (term48 NUM_REP' a)). Qed.
Lemma lem71097 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term46 NUM_REP' a.
Proof. exact (EQ_MP (@lem71096 NUM_REP' a) (@lem71095 a NUM_REP' h1 h2)). Qed.
Lemma lem71098 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term107 NUM_REP' a.
Proof. exact (@lem71094 NUM_REP' h1 h2 a). Qed.
Lemma lem71099 (a : ind) (NUM_REP' : ind -> Prop) : (term107 NUM_REP' a) = (term88 a NUM_REP').
Proof. exact (eq_refl (term107 NUM_REP' a)). Qed.
Lemma lem71100 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term88 a NUM_REP'.
Proof. exact (EQ_MP (@lem71099 a NUM_REP') (@lem71098 a NUM_REP' h1 h2)). Qed.
Lemma lem71101 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term108 NUM_REP' a.
Proof. exact (conj (@lem71100 a NUM_REP' h1 h2) (@lem71097 a NUM_REP' h1 h2)). Qed.
Lemma lem71102 (a : ind) (NUM_REP' : ind -> Prop) : (term108 NUM_REP' a) = ((NUM_REP' a) = (term45 a NUM_REP')).
Proof. exact (@lem32 (NUM_REP' a) (term45 a NUM_REP')). Qed.
Lemma lem71103 (a : ind) (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : (NUM_REP' a) = (term45 a NUM_REP').
Proof. exact (EQ_MP (@lem71102 a NUM_REP') (@lem71101 a NUM_REP' h1 h2)). Qed.
Lemma lem71108 (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term47 NUM_REP'.
Proof. exact (fun a : ind => @lem71053 a NUM_REP' h1 h2). Qed.
Lemma lem71109 (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term109 NUM_REP'.
Proof. exact (fun a : ind => @lem71103 a NUM_REP' h1 h2). Qed.
Lemma lem71110 (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term65 NUM_REP'.
Proof. exact (fun NUM_REP'' : ind -> Prop => @lem71020 NUM_REP'' NUM_REP' h2). Qed.
Lemma lem71111 (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term41 NUM_REP'.
Proof. exact (EQ_MP (@lem70995 NUM_REP') (@lem71108 NUM_REP' h1 h2)). Qed.
Lemma lem71125 (NUM_REP' : ind -> Prop) : (term47 NUM_REP') = (term41 NUM_REP').
Proof. exact (SYM (@lem70994 NUM_REP')). Qed.
Lemma lem71126 (NUM_REP' : ind -> Prop) : (term47 NUM_REP') = (term41 NUM_REP').
Proof. exact (@lem71125 NUM_REP'). Qed.
Lemma lem71127 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem71128 (NUM_REP' : ind -> Prop) : (term110 NUM_REP') = (term111 NUM_REP').
Proof. exact (MK_COMB (@lem71127) (@lem71126 NUM_REP')). Qed.
Lemma lem71153 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) : (term63 NUM_REP' NUM_REP'') = (term63 NUM_REP' NUM_REP'').
Proof. exact (eq_refl (term63 NUM_REP' NUM_REP'')). Qed.
Lemma lem71154 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) : (term64 NUM_REP' NUM_REP'') = (term112 NUM_REP' NUM_REP'').
Proof. exact (MK_COMB (@lem71128 NUM_REP'') (@lem71153 NUM_REP' NUM_REP'')). Qed.
Lemma lem71155 (NUM_REP' : ind -> Prop) : (term113 NUM_REP') = (term114 NUM_REP').
Proof. exact (fun_ext (fun NUM_REP'' : ind -> Prop => @lem71154 NUM_REP' NUM_REP'')). Qed.
Lemma lem71156 : (@all (ind -> Prop)) = (@all (ind -> Prop)).
Proof. exact (eq_refl (@all (ind -> Prop))). Qed.
Lemma lem71157 (NUM_REP' : ind -> Prop) : (term65 NUM_REP') = (term115 NUM_REP').
Proof. exact (MK_COMB (@lem71156) (@lem71155 NUM_REP')). Qed.
Lemma lem71158 (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term115 NUM_REP'.
Proof. exact (EQ_MP (@lem71157 NUM_REP') (@lem71110 NUM_REP' h1 h2)). Qed.
Lemma lem71159 (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term116 NUM_REP'.
Proof. exact (conj (@lem71158 NUM_REP' h1 h2) (@lem71109 NUM_REP' h1 h2)). Qed.
Lemma lem71160 (NUM_REP' : ind -> Prop) (h1 : term66) (h2 : NUM_REP' = term53) : term117 NUM_REP'.
Proof. exact (conj (@lem71111 NUM_REP' h1 h2) (@lem71159 NUM_REP' h1 h2)). Qed.
Lemma lem71161 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : term63 NUM_REP' NUM_REP''.
Proof. exact (h1). Qed.
Lemma lem71163 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term118 A C B D.
Proof. exact (fun h0 : term119 A B C D => @lem7129 A B C D h0). Qed.
Lemma lem71165 (a : ind) : term120 a.
Proof. exact (@lem9120 (a = IND_0)). Qed.
Lemma lem71166 (a : ind) : (term120 a) = (term121 a).
Proof. exact (eq_refl (term120 a)). Qed.
Lemma lem71167 (a : ind) : term121 a.
Proof. exact (EQ_MP (@lem71166 a) (@lem71165 a)). Qed.
Lemma lem71169 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term122 A P Q.
Proof. exact (fun h0 : term123 A P Q => @lem7400 A P Q h0). Qed.
Lemma lem71170 (P : ind -> Prop) (Q : ind -> Prop) : term124 P Q.
Proof. exact (@lem71169 ind P Q). Qed.
Lemma lem71171 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) : term125 NUM_REP' a NUM_REP''.
Proof. exact (@lem71170 (term30 a NUM_REP') (term30 a NUM_REP'')). Qed.
Lemma lem71172 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) : (term126 a NUM_REP' i) = (term11 a NUM_REP' i).
Proof. exact (eq_refl (term126 a NUM_REP' i)). Qed.
Lemma lem71173 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem71174 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) : (term127 a NUM_REP' i) = (term128 a NUM_REP' i).
Proof. exact (MK_COMB (@lem71173) (@lem71172 a NUM_REP' i)). Qed.
Lemma lem71175 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) : (term126 a NUM_REP' i) = (term11 a NUM_REP' i).
Proof. exact (eq_refl (term126 a NUM_REP' i)). Qed.
Lemma lem71176 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) (i : ind) : (term129 NUM_REP' a NUM_REP'' i) = (term130 NUM_REP' a NUM_REP'' i).
Proof. exact (MK_COMB (@lem71174 a NUM_REP' i) (@lem71175 a NUM_REP'' i)). Qed.
Lemma lem71177 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) : (term131 NUM_REP' a NUM_REP'') = (term132 NUM_REP' a NUM_REP'').
Proof. exact (fun_ext (fun i : ind => @lem71176 NUM_REP' a NUM_REP'' i)). Qed.
Lemma lem71178 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem71179 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) : (term133 NUM_REP' a NUM_REP'') = (term134 NUM_REP' a NUM_REP'').
Proof. exact (MK_COMB (@lem71178) (@lem71177 NUM_REP' a NUM_REP'')). Qed.
Lemma lem71180 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem71181 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) : (term135 NUM_REP' a NUM_REP'') = (term136 NUM_REP' a NUM_REP'').
Proof. exact (MK_COMB (@lem71180) (@lem71179 NUM_REP' a NUM_REP'')). Qed.
Lemma lem71182 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) : (term126 a NUM_REP' i) = (term11 a NUM_REP' i).
Proof. exact (eq_refl (term126 a NUM_REP' i)). Qed.
Lemma lem71183 (a : ind) (NUM_REP' : ind -> Prop) : (term137 a NUM_REP') = (term30 a NUM_REP').
Proof. exact (fun_ext (fun i : ind => @lem71182 a NUM_REP' i)). Qed.
Lemma lem71184 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem71185 (a : ind) (NUM_REP' : ind -> Prop) : (term138 a NUM_REP') = (term29 a NUM_REP').
Proof. exact (MK_COMB (@lem71184) (@lem71183 a NUM_REP')). Qed.
Lemma lem71186 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem71187 (a : ind) (NUM_REP' : ind -> Prop) : (term139 a NUM_REP') = (term140 a NUM_REP').
Proof. exact (MK_COMB (@lem71186) (@lem71185 a NUM_REP')). Qed.
Lemma lem71188 (a : ind) (NUM_REP' : ind -> Prop) (i : ind) : (term126 a NUM_REP' i) = (term11 a NUM_REP' i).
Proof. exact (eq_refl (term126 a NUM_REP' i)). Qed.
Lemma lem71189 (a : ind) (NUM_REP' : ind -> Prop) : (term137 a NUM_REP') = (term30 a NUM_REP').
Proof. exact (fun_ext (fun i : ind => @lem71188 a NUM_REP' i)). Qed.
Lemma lem71190 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem71191 (a : ind) (NUM_REP' : ind -> Prop) : (term138 a NUM_REP') = (term29 a NUM_REP').
Proof. exact (MK_COMB (@lem71190) (@lem71189 a NUM_REP')). Qed.
Lemma lem71192 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) : (term141 NUM_REP' a NUM_REP'') = (term142 NUM_REP' a NUM_REP'').
Proof. exact (MK_COMB (@lem71187 a NUM_REP') (@lem71191 a NUM_REP'')). Qed.
Lemma lem71193 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) : (term125 NUM_REP' a NUM_REP'') = (term143 NUM_REP' a NUM_REP'').
Proof. exact (MK_COMB (@lem71181 NUM_REP' a NUM_REP'') (@lem71192 NUM_REP' a NUM_REP'')). Qed.
Lemma lem71196 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term144 A C B D.
Proof. exact (fun h0 : term119 A B C D => @lem7058 A B C D h0). Qed.
Lemma lem71198 (a : ind) (i : ind) : term145 a i.
Proof. exact (@lem9120 (a = (IND_SUC i))). Qed.
Lemma lem71199 (a : ind) (i : ind) : (term145 a i) = (term146 a i).
Proof. exact (eq_refl (term145 a i)). Qed.
Lemma lem71200 (a : ind) (i : ind) : term146 a i.
Proof. exact (EQ_MP (@lem71199 a i) (@lem71198 a i)). Qed.
Lemma lem71201 (a : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : term147 NUM_REP' NUM_REP'' a.
Proof. exact (@lem71161 NUM_REP' NUM_REP'' h1 a). Qed.
Lemma lem71202 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (a : ind) : (term147 NUM_REP' NUM_REP'' a) = (term62 NUM_REP' NUM_REP'' a).
Proof. exact (eq_refl (term147 NUM_REP' NUM_REP'' a)). Qed.
Lemma lem71203 (a : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : term62 NUM_REP' NUM_REP'' a.
Proof. exact (EQ_MP (@lem71202 NUM_REP' NUM_REP'' a) (@lem71201 a NUM_REP' NUM_REP'' h1)). Qed.
Lemma lem71204 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (a : ind) : (term62 NUM_REP' NUM_REP'' a) = ((term62 NUM_REP' NUM_REP'' a) = True).
Proof. exact (@lem7 (term62 NUM_REP' NUM_REP'' a)). Qed.
Lemma lem71207 (a : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : (term62 NUM_REP' NUM_REP'' a) = True.
Proof. exact (EQ_MP (@lem71204 NUM_REP' NUM_REP'' a) (@lem71203 a NUM_REP' NUM_REP'' h1)). Qed.
Lemma lem71208 (i : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : (term62 NUM_REP' NUM_REP'' i) = True.
Proof. exact (@lem71207 i NUM_REP' NUM_REP'' h1). Qed.
Lemma lem71209 (i : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : True = (term62 NUM_REP' NUM_REP'' i).
Proof. exact (SYM (@lem71208 i NUM_REP' NUM_REP'' h1)). Qed.
Lemma lem71210 (i : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : term62 NUM_REP' NUM_REP'' i.
Proof. exact (EQ_MP (@lem71209 i NUM_REP' NUM_REP'' h1) (@lem0)). Qed.
Lemma lem71211 (a : ind) (i : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : term148 a NUM_REP' NUM_REP'' i.
Proof. exact (conj (@lem71200 a i) (@lem71210 i NUM_REP' NUM_REP'' h1)). Qed.
Lemma lem71213 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) (i : ind) : term149 NUM_REP' a NUM_REP'' i.
Proof. exact (@lem71196 (a = (IND_SUC i)) (NUM_REP' i) (a = (IND_SUC i)) (NUM_REP'' i)). Qed.
Lemma lem71214 (a : ind) (i : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : term130 NUM_REP' a NUM_REP'' i.
Proof. exact (@lem71213 NUM_REP' a NUM_REP'' i (@lem71211 a i NUM_REP' NUM_REP'' h1)). Qed.
Lemma lem71219 (a : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : term134 NUM_REP' a NUM_REP''.
Proof. exact (fun i : ind => @lem71214 a i NUM_REP' NUM_REP'' h1). Qed.
Lemma lem71221 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) : term143 NUM_REP' a NUM_REP''.
Proof. exact (EQ_MP (@lem71193 NUM_REP' a NUM_REP'') (@lem71171 NUM_REP' a NUM_REP'')). Qed.
Lemma lem71222 (a : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : term142 NUM_REP' a NUM_REP''.
Proof. exact (@lem71221 NUM_REP' a NUM_REP'' (@lem71219 a NUM_REP' NUM_REP'' h1)). Qed.
Lemma lem71223 (a : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : term150 NUM_REP' a NUM_REP''.
Proof. exact (conj (@lem71167 a) (@lem71222 a NUM_REP' NUM_REP'' h1)). Qed.
Lemma lem71225 (NUM_REP' : ind -> Prop) (a : ind) (NUM_REP'' : ind -> Prop) : term151 NUM_REP' a NUM_REP''.
Proof. exact (@lem71163 (a = IND_0) (term29 a NUM_REP') (a = IND_0) (term29 a NUM_REP'')). Qed.
Lemma lem71226 (a : ind) (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : term74 NUM_REP' a NUM_REP''.
Proof. exact (@lem71225 NUM_REP' a NUM_REP'' (@lem71223 a NUM_REP' NUM_REP'' h1)). Qed.
Lemma lem71231 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : term72 NUM_REP' NUM_REP''.
Proof. exact (fun a : ind => @lem71226 a NUM_REP' NUM_REP'' h1). Qed.
Lemma lem71232 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : (term63 NUM_REP' NUM_REP'') = (term72 NUM_REP' NUM_REP'').
Proof. exact (prop_ext (fun h2 : term63 NUM_REP' NUM_REP'' => @lem71231 NUM_REP' NUM_REP'' h1) (fun h2 : term72 NUM_REP' NUM_REP'' => @lem71161 NUM_REP' NUM_REP'' h1)). Qed.
Lemma lem71233 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) (h1 : term63 NUM_REP' NUM_REP'') : term72 NUM_REP' NUM_REP''.
Proof. exact (EQ_MP (@lem71232 NUM_REP' NUM_REP'' h1) (@lem71161 NUM_REP' NUM_REP'' h1)). Qed.
Lemma lem71234 (NUM_REP' : ind -> Prop) (NUM_REP'' : ind -> Prop) : term71 NUM_REP' NUM_REP''.
Proof. exact (fun h0 : term63 NUM_REP' NUM_REP'' => @lem71233 NUM_REP' NUM_REP'' h0). Qed.
Lemma lem71239 (NUM_REP' : ind -> Prop) : term69 NUM_REP'.
Proof. exact (fun NUM_REP'' : ind -> Prop => @lem71234 NUM_REP' NUM_REP''). Qed.
Lemma lem71244 : term66.
Proof. exact (fun NUM_REP' : ind -> Prop => @lem71239 NUM_REP'). Qed.
Lemma lem71245 (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : term66 = (term117 NUM_REP').
Proof. exact (prop_ext (fun h2 : term66 => @lem71160 NUM_REP' h2 h1) (fun h2 : term117 NUM_REP' => @lem71244)). Qed.
Lemma lem71246 (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : term117 NUM_REP'.
Proof. exact (EQ_MP (@lem71245 NUM_REP' h1) (@lem71244)). Qed.
Lemma lem71247 (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : NUM_REP' = term53.
Proof. exact (h1). Qed.
Lemma lem71248 (NUM_REP' : ind -> Prop) : term152 NUM_REP'.
Proof. exact (fun h0 : NUM_REP' = term53 => @lem71246 NUM_REP' h0). Qed.
Lemma lem71249 (NUM_REP' : ind -> Prop) : term152 NUM_REP'.
Proof. exact (@lem71248 NUM_REP'). Qed.
Lemma lem71250 (NUM_REP' : ind -> Prop) (h1 : NUM_REP' = term53) : term117 NUM_REP'.
Proof. exact (@lem71249 NUM_REP' (@lem71247 NUM_REP' h1)). Qed.
Lemma lem71251 : NUM_REP = term53.
Proof. exact (@NUM_REP_def). Qed.
Lemma lem71252 (NUM_REP' : ind -> Prop) : term152 NUM_REP'.
Proof. exact (fun h0 : NUM_REP' = term53 => @lem71250 NUM_REP' h0). Qed.
Lemma lem71253 : term153.
Proof. exact (@lem71252 NUM_REP). Qed.
Lemma lem71254 : term154.
Proof. exact (@lem71253 (@lem71251)). Qed.
