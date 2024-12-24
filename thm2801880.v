Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2801880_term_abbrevs.
Require Import thm2801043_spec.
Require Import thm2801817_spec.
Lemma lem2801818 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem2801819 : term1.
Proof. exact (EQ_MP (@lem2801818) (@lem2801043)). Qed.
Lemma lem2801820 : term2.
Proof. exact (@lem2801819 term3). Qed.
Lemma lem2801821 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem2801822 : term4.
Proof. exact (EQ_MP (@lem2801821) (@lem2801820)). Qed.
Lemma lem2801823 (h1 : int_gcd = term5) : int_gcd = term5.
Proof. exact (h1). Qed.
Lemma lem2801824 (h1 : int_gcd = term5) : term5 = int_gcd.
Proof. exact (SYM (@lem2801823 h1)). Qed.
Lemma lem2801825 (h1 : term5 = int_gcd) : term5 = int_gcd.
Proof. exact (h1). Qed.
Lemma lem2801826 (h1 : term5 = int_gcd) : int_gcd = term5.
Proof. exact (SYM (@lem2801825 h1)). Qed.
Lemma lem2801827 : (int_gcd = term5) = (term5 = int_gcd).
Proof. exact (prop_ext (fun h1 : int_gcd = term5 => @lem2801824 h1) (fun h1 : term5 = int_gcd => @lem2801826 h1)). Qed.
Lemma lem2801830 : term5 = int_gcd.
Proof. exact (EQ_MP (@lem2801827) (@lem2801817)). Qed.
Lemma lem2801831 (a : int) (b : int) : (@pair int int a b) = (@pair int int a b).
Proof. exact (eq_refl (@pair int int a b)). Qed.
Lemma lem2801832 (a : int) (b : int) : (term6 a b) = (term7 a b).
Proof. exact (MK_COMB (@lem2801830) (@lem2801831 a b)). Qed.
Lemma lem2801833 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem2801834 (a : int) (b : int) : (term9 a b) = (term10 a b).
Proof. exact (MK_COMB (@lem2801833) (@lem2801832 a b)). Qed.
Lemma lem2801835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2801836 (a : int) (b : int) : (term11 a b) = (term12 a b).
Proof. exact (MK_COMB (@lem2801835) (@lem2801834 a b)). Qed.
Lemma lem2801838 : term5 = int_gcd.
Proof. exact (EQ_MP (@lem2801827) (@lem2801817)). Qed.
Lemma lem2801839 (a : int) (b : int) : (@pair int int a b) = (@pair int int a b).
Proof. exact (eq_refl (@pair int int a b)). Qed.
Lemma lem2801840 (a : int) (b : int) : (term6 a b) = (term7 a b).
Proof. exact (MK_COMB (@lem2801838) (@lem2801839 a b)). Qed.
Lemma lem2801841 : int_divides = int_divides.
Proof. exact (eq_refl int_divides). Qed.
Lemma lem2801842 (a : int) (b : int) : (term13 a b) = (term14 a b).
Proof. exact (MK_COMB (@lem2801841) (@lem2801840 a b)). Qed.
Lemma lem2801843 (a : int) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem2801844 (b : int) (a : int) : (term15 b a) = (term16 b a).
Proof. exact (MK_COMB (@lem2801842 a b) (@lem2801843 a)). Qed.
Lemma lem2801845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2801846 (b : int) (a : int) : (term17 b a) = (term18 b a).
Proof. exact (MK_COMB (@lem2801845) (@lem2801844 b a)). Qed.
Lemma lem2801848 : term5 = int_gcd.
Proof. exact (EQ_MP (@lem2801827) (@lem2801817)). Qed.
Lemma lem2801849 (a : int) (b : int) : (@pair int int a b) = (@pair int int a b).
Proof. exact (eq_refl (@pair int int a b)). Qed.
Lemma lem2801850 (a : int) (b : int) : (term6 a b) = (term7 a b).
Proof. exact (MK_COMB (@lem2801848) (@lem2801849 a b)). Qed.
Lemma lem2801851 : int_divides = int_divides.
Proof. exact (eq_refl int_divides). Qed.
Lemma lem2801852 (a : int) (b : int) : (term13 a b) = (term14 a b).
Proof. exact (MK_COMB (@lem2801851) (@lem2801850 a b)). Qed.
Lemma lem2801853 (b : int) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem2801854 (a : int) (b : int) : (term19 a b) = (term20 a b).
Proof. exact (MK_COMB (@lem2801852 a b) (@lem2801853 b)). Qed.
Lemma lem2801855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2801856 (a : int) (b : int) : (term21 a b) = (term22 a b).
Proof. exact (MK_COMB (@lem2801855) (@lem2801854 a b)). Qed.
Lemma lem2801858 : term5 = int_gcd.
Proof. exact (EQ_MP (@lem2801827) (@lem2801817)). Qed.
Lemma lem2801859 (a : int) (b : int) : (@pair int int a b) = (@pair int int a b).
Proof. exact (eq_refl (@pair int int a b)). Qed.
Lemma lem2801860 (a : int) (b : int) : (term6 a b) = (term7 a b).
Proof. exact (MK_COMB (@lem2801858) (@lem2801859 a b)). Qed.
Lemma lem2801861 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2801862 (a : int) (b : int) : (term23 a b) = (term24 a b).
Proof. exact (MK_COMB (@lem2801861) (@lem2801860 a b)). Qed.
Lemma lem2801863 (a : int) (x : int) (b : int) (y : int) : (term25 a x b y) = (term25 a x b y).
Proof. exact (eq_refl (term25 a x b y)). Qed.
Lemma lem2801864 (a : int) (x : int) (b : int) (y : int) : ((term6 a b) = (term25 a x b y)) = ((term7 a b) = (term25 a x b y)).
Proof. exact (MK_COMB (@lem2801862 a b) (@lem2801863 a x b y)). Qed.
Lemma lem2801865 (a : int) (x : int) (b : int) : (term26 a x b) = (term27 a x b).
Proof. exact (fun_ext (fun y : int => @lem2801864 a x b y)). Qed.
Lemma lem2801866 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2801867 (a : int) (x : int) (b : int) : (term28 a x b) = (term29 a x b).
Proof. exact (MK_COMB (@lem2801866) (@lem2801865 a x b)). Qed.
Lemma lem2801868 (a : int) (b : int) : (term30 a b) = (term31 a b).
Proof. exact (fun_ext (fun x : int => @lem2801867 a x b)). Qed.
Lemma lem2801869 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2801870 (a : int) (b : int) : (term32 a b) = (term33 a b).
Proof. exact (MK_COMB (@lem2801869) (@lem2801868 a b)). Qed.
Lemma lem2801871 (a : int) (b : int) : (term34 a b) = (term35 a b).
Proof. exact (MK_COMB (@lem2801856 a b) (@lem2801870 a b)). Qed.
Lemma lem2801872 (a : int) (b : int) : (term36 a b) = (term37 a b).
Proof. exact (MK_COMB (@lem2801846 b a) (@lem2801871 a b)). Qed.
Lemma lem2801873 (a : int) (b : int) : (term38 a b) = (term39 a b).
Proof. exact (MK_COMB (@lem2801836 a b) (@lem2801872 a b)). Qed.
Lemma lem2801874 (a : int) : (term40 a) = (term41 a).
Proof. exact (fun_ext (fun b : int => @lem2801873 a b)). Qed.
Lemma lem2801875 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2801876 (a : int) : (term42 a) = (term43 a).
Proof. exact (MK_COMB (@lem2801875) (@lem2801874 a)). Qed.
Lemma lem2801877 : term44 = term45.
Proof. exact (fun_ext (fun a : int => @lem2801876 a)). Qed.
Lemma lem2801878 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2801879 : term4 = term46.
Proof. exact (MK_COMB (@lem2801878) (@lem2801877)). Qed.
Lemma lem2801880 : term46.
Proof. exact (EQ_MP (@lem2801879) (@lem2801822)). Qed.
