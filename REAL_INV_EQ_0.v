Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INV_EQ_0_term_abbrevs.
Require Import REAL_INV_INV_spec.
Require Import TREAL_INV_0_spec.
Require Import thm0_spec.
Require Import thm1340072_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Lemma lem1588852 (x : real) (h1 : (term0 x) = x) : (term0 x) = x.
Proof. exact (h1). Qed.
Lemma lem1588853 (x : real) (h1 : (term0 x) = x) : x = (term0 x).
Proof. exact (SYM (@lem1588852 x h1)). Qed.
Lemma lem1588854 (x : real) (h1 : x = (term0 x)) : x = (term0 x).
Proof. exact (h1). Qed.
Lemma lem1588855 (x : real) (h1 : x = (term0 x)) : (term0 x) = x.
Proof. exact (SYM (@lem1588854 x h1)). Qed.
Lemma lem1588856 (x : real) : ((term0 x) = x) = (x = (term0 x)).
Proof. exact (prop_ext (fun h1 : (term0 x) = x => @lem1588853 x h1) (fun h1 : x = (term0 x) => @lem1588855 x h1)). Qed.
Lemma lem1588857 : term1 = term2.
Proof. exact (fun_ext (fun x : real => @lem1588856 x)). Qed.
Lemma lem1588858 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1588859 : term3 = term4.
Proof. exact (MK_COMB (@lem1588858) (@lem1588857)). Qed.
Lemma lem1588860 : term4.
Proof. exact (EQ_MP (@lem1588859) (@lem1587920)). Qed.
Lemma lem1588861 (x : real) : term5 x.
Proof. exact (@lem1588860 x). Qed.
Lemma lem1588862 (x : real) : (term5 x) = (x = (term0 x)).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1588873 (x : real) (h1 : x = term6) : x = term6.
Proof. exact (h1). Qed.
Lemma lem1588874 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1588875 (x : real) (h1 : x = term6) : (real_inv x) = term7.
Proof. exact (MK_COMB (@lem1588874) (@lem1588873 x h1)). Qed.
Lemma lem1588877 : term7 = term6.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1588878 (x : real) (h1 : x = term6) : (real_inv x) = term6.
Proof. exact (TRANS (@lem1588875 x h1) (@lem1588877)). Qed.
Lemma lem1588879 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1588880 (x : real) (h1 : x = term6) : (term8 x) = term9.
Proof. exact (MK_COMB (@lem1588879) (@lem1588878 x h1)). Qed.
Lemma lem1588881 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1588882 (x : real) (h1 : x = term6) : ((real_inv x) = term6) = (term6 = term6).
Proof. exact (MK_COMB (@lem1588880 x h1) (@lem1588881)). Qed.
Lemma lem1588884 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1588885 (x : real) : (x = x) = True.
Proof. exact (@lem1588884 real x). Qed.
Lemma lem1588886 : (term6 = term6) = True.
Proof. exact (@lem1588885 term6). Qed.
Lemma lem1588887 (x : real) (h1 : x = term6) : ((real_inv x) = term6) = True.
Proof. exact (TRANS (@lem1588882 x h1) (@lem1588886)). Qed.
Lemma lem1588888 (x : real) (h1 : x = term6) : True = ((real_inv x) = term6).
Proof. exact (SYM (@lem1588887 x h1)). Qed.
Lemma lem1588889 (x : real) (h1 : x = term6) : (real_inv x) = term6.
Proof. exact (EQ_MP (@lem1588888 x h1) (@lem0)). Qed.
Lemma lem1588899 (x : real) : x = (term0 x).
Proof. exact (EQ_MP (@lem1588862 x) (@lem1588861 x)). Qed.
Lemma lem1588900 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1588901 (x : real) : (@eq real x) = (term10 x).
Proof. exact (MK_COMB (@lem1588900) (@lem1588899 x)). Qed.
Lemma lem1588903 (x : real) : x = (term0 x).
Proof. exact (EQ_MP (@lem1588862 x) (@lem1588861 x)). Qed.
Lemma lem1588904 : term6 = term11.
Proof. exact (@lem1588903 term6). Qed.
Lemma lem1588905 (x : real) : (x = term6) = ((term0 x) = term11).
Proof. exact (MK_COMB (@lem1588901 x) (@lem1588904)). Qed.
Lemma lem1588906 (x : real) : ((term0 x) = term11) = (x = term6).
Proof. exact (SYM (@lem1588905 x)). Qed.
Lemma lem1588910 (x : real) (h1 : (real_inv x) = term6) : (real_inv x) = term6.
Proof. exact (h1). Qed.
Lemma lem1588911 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1588912 (x : real) (h1 : (real_inv x) = term6) : (term0 x) = term7.
Proof. exact (MK_COMB (@lem1588911) (@lem1588910 x h1)). Qed.
Lemma lem1588914 : term7 = term6.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1588915 (x : real) (h1 : (real_inv x) = term6) : (term0 x) = term6.
Proof. exact (TRANS (@lem1588912 x h1) (@lem1588914)). Qed.
Lemma lem1588916 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1588917 (x : real) (h1 : (real_inv x) = term6) : (term10 x) = term9.
Proof. exact (MK_COMB (@lem1588916) (@lem1588915 x h1)). Qed.
Lemma lem1588919 : term7 = term6.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1588920 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1588921 : term11 = term7.
Proof. exact (MK_COMB (@lem1588920) (@lem1588919)). Qed.
Lemma lem1588923 : term7 = term6.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1588924 : term11 = term6.
Proof. exact (TRANS (@lem1588921) (@lem1588923)). Qed.
Lemma lem1588925 (x : real) (h1 : (real_inv x) = term6) : ((term0 x) = term11) = (term6 = term6).
Proof. exact (MK_COMB (@lem1588917 x h1) (@lem1588924)). Qed.
Lemma lem1588927 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1588928 (x : real) : (x = x) = True.
Proof. exact (@lem1588927 real x). Qed.
Lemma lem1588929 : (term6 = term6) = True.
Proof. exact (@lem1588928 term6). Qed.
Lemma lem1588930 (x : real) (h1 : (real_inv x) = term6) : ((term0 x) = term11) = True.
Proof. exact (TRANS (@lem1588925 x h1) (@lem1588929)). Qed.
Lemma lem1588931 (x : real) (h1 : (real_inv x) = term6) : True = ((term0 x) = term11).
Proof. exact (SYM (@lem1588930 x h1)). Qed.
Lemma lem1588932 (x : real) (h1 : (real_inv x) = term6) : (term0 x) = term11.
Proof. exact (EQ_MP (@lem1588931 x h1) (@lem0)). Qed.
Lemma lem1588934 (x : real) (h1 : (real_inv x) = term6) : x = term6.
Proof. exact (EQ_MP (@lem1588906 x) (@lem1588932 x h1)). Qed.
Lemma lem1588935 (x : real) : term12 x.
Proof. exact (fun h0 : x = term6 => @lem1588889 x h0). Qed.
Lemma lem1588936 (x : real) : term13 x.
Proof. exact (fun h0 : (real_inv x) = term6 => @lem1588934 x h0). Qed.
Lemma lem1588937 (x : real) : term14 x.
Proof. exact (conj (@lem1588936 x) (@lem1588935 x)). Qed.
Lemma lem1588938 (x : real) : (term14 x) = (((real_inv x) = term6) = (x = term6)).
Proof. exact (@lem32 ((real_inv x) = term6) (x = term6)). Qed.
Lemma lem1588939 (x : real) : ((real_inv x) = term6) = (x = term6).
Proof. exact (EQ_MP (@lem1588938 x) (@lem1588937 x)). Qed.
Lemma lem1588944 : term15.
Proof. exact (fun x : real => @lem1588939 x). Qed.
