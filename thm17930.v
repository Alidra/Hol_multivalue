Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17930_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem17797 (p : Prop) : term0 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem17798 (p : Prop) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem17799 (p : Prop) : term1 p.
Proof. exact (EQ_MP (@lem17798 p) (@lem17797 p)). Qed.
Lemma lem17800 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem17801 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem17814 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem17815 (q : Prop) (p : Prop) (h1 : p = True) : (term3 q p) = (term4 q).
Proof. exact (MK_COMB (@lem17814 q) (@lem17800 p h1)). Qed.
Lemma lem17816 (q : Prop) : (term4 q) = ((term5 q) = (term6 q)).
Proof. exact (eq_refl (term4 q)). Qed.
Lemma lem17817 (q : Prop) (p : Prop) : (term7 q p) = (term7 q p).
Proof. exact (eq_refl (term7 q p)). Qed.
Lemma lem17818 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = ((term3 q p) = ((term5 q) = (term6 q))).
Proof. exact (MK_COMB (@lem17817 q p) (@lem17816 q)). Qed.
Lemma lem17819 (p : Prop) (q : Prop) : (term3 q p) = ((term8 p q) = (term9 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem17820 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17821 (p : Prop) (q : Prop) : (term7 q p) = (term10 p q).
Proof. exact (MK_COMB (@lem17820) (@lem17819 p q)). Qed.
Lemma lem17822 (q : Prop) : ((term5 q) = (term6 q)) = ((term5 q) = (term6 q)).
Proof. exact (eq_refl ((term5 q) = (term6 q))). Qed.
Lemma lem17823 (p : Prop) (q : Prop) : ((term3 q p) = ((term5 q) = (term6 q))) = (((term8 p q) = (term9 p q)) = ((term5 q) = (term6 q))).
Proof. exact (MK_COMB (@lem17821 p q) (@lem17822 q)). Qed.
Lemma lem17824 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = (((term8 p q) = (term9 p q)) = ((term5 q) = (term6 q))).
Proof. exact (TRANS (@lem17818 p q) (@lem17823 p q)). Qed.
Lemma lem17825 (q : Prop) (p : Prop) (h1 : p = True) : ((term8 p q) = (term9 p q)) = ((term5 q) = (term6 q)).
Proof. exact (EQ_MP (@lem17824 p q) (@lem17815 q p h1)). Qed.
Lemma lem17826 (q : Prop) (p : Prop) (h1 : p = True) : ((term5 q) = (term6 q)) = ((term8 p q) = (term9 p q)).
Proof. exact (SYM (@lem17825 q p h1)). Qed.
Lemma lem17827 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem17828 (q : Prop) (p : Prop) (h1 : p = False) : (term3 q p) = (term11 q).
Proof. exact (MK_COMB (@lem17827 q) (@lem17801 p h1)). Qed.
Lemma lem17829 (q : Prop) : (term11 q) = ((term12 q) = (term13 q)).
Proof. exact (eq_refl (term11 q)). Qed.
Lemma lem17830 (q : Prop) (p : Prop) : (term7 q p) = (term7 q p).
Proof. exact (eq_refl (term7 q p)). Qed.
Lemma lem17831 (p : Prop) (q : Prop) : ((term3 q p) = (term11 q)) = ((term3 q p) = ((term12 q) = (term13 q))).
Proof. exact (MK_COMB (@lem17830 q p) (@lem17829 q)). Qed.
Lemma lem17832 (p : Prop) (q : Prop) : (term3 q p) = ((term8 p q) = (term9 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem17833 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17834 (p : Prop) (q : Prop) : (term7 q p) = (term10 p q).
Proof. exact (MK_COMB (@lem17833) (@lem17832 p q)). Qed.
Lemma lem17835 (q : Prop) : ((term12 q) = (term13 q)) = ((term12 q) = (term13 q)).
Proof. exact (eq_refl ((term12 q) = (term13 q))). Qed.
Lemma lem17836 (p : Prop) (q : Prop) : ((term3 q p) = ((term12 q) = (term13 q))) = (((term8 p q) = (term9 p q)) = ((term12 q) = (term13 q))).
Proof. exact (MK_COMB (@lem17834 p q) (@lem17835 q)). Qed.
Lemma lem17837 (p : Prop) (q : Prop) : ((term3 q p) = (term11 q)) = (((term8 p q) = (term9 p q)) = ((term12 q) = (term13 q))).
Proof. exact (TRANS (@lem17831 p q) (@lem17836 p q)). Qed.
Lemma lem17838 (q : Prop) (p : Prop) (h1 : p = False) : ((term8 p q) = (term9 p q)) = ((term12 q) = (term13 q)).
Proof. exact (EQ_MP (@lem17837 p q) (@lem17828 q p h1)). Qed.
Lemma lem17839 (q : Prop) (p : Prop) (h1 : p = False) : ((term12 q) = (term13 q)) = ((term8 p q) = (term9 p q)).
Proof. exact (SYM (@lem17838 q p h1)). Qed.
Lemma lem17843 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem17844 (q : Prop) : (True = q) = q.
Proof. exact (@lem17843 q). Qed.
Lemma lem17845 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem17846 (q : Prop) : (term5 q) = (~ q).
Proof. exact (MK_COMB (@lem17845) (@lem17844 q)). Qed.
Lemma lem17847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17848 (q : Prop) : (term14 q) = (term15 q).
Proof. exact (MK_COMB (@lem17847) (@lem17846 q)). Qed.
Lemma lem17852 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem17853 (q : Prop) : (True \/ q) = True.
Proof. exact (@lem17852 q). Qed.
Lemma lem17854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem17855 (q : Prop) : (term16 q) = (and True).
Proof. exact (MK_COMB (@lem17854) (@lem17853 q)). Qed.
Lemma lem17859 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem17860 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem17861 : term17 = (or False).
Proof. exact (MK_COMB (@lem17860) (@lem17859)). Qed.
Lemma lem17862 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem17863 (q : Prop) : (term18 q) = (term19 q).
Proof. exact (MK_COMB (@lem17861) (@lem17862 q)). Qed.
Lemma lem17865 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem17866 (q : Prop) : (term19 q) = (~ q).
Proof. exact (@lem17865 (~ q)). Qed.
Lemma lem17867 (q : Prop) : (term18 q) = (~ q).
Proof. exact (TRANS (@lem17863 q) (@lem17866 q)). Qed.
Lemma lem17868 (q : Prop) : (term6 q) = (term20 q).
Proof. exact (MK_COMB (@lem17855 q) (@lem17867 q)). Qed.
Lemma lem17870 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem17871 (q : Prop) : (term20 q) = (~ q).
Proof. exact (@lem17870 (~ q)). Qed.
Lemma lem17872 (q : Prop) : (term6 q) = (~ q).
Proof. exact (TRANS (@lem17868 q) (@lem17871 q)). Qed.
Lemma lem17873 (q : Prop) : ((term5 q) = (term6 q)) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem17848 q) (@lem17872 q)). Qed.
Lemma lem17875 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem17876 (x : Prop) : (x = x) = True.
Proof. exact (@lem17875 Prop x). Qed.
Lemma lem17877 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem17876 (~ q)). Qed.
Lemma lem17878 (q : Prop) : ((term5 q) = (term6 q)) = True.
Proof. exact (TRANS (@lem17873 q) (@lem17877 q)). Qed.
Lemma lem17879 (q : Prop) : True = ((term5 q) = (term6 q)).
Proof. exact (SYM (@lem17878 q)). Qed.
Lemma lem17880 (q : Prop) : (term5 q) = (term6 q).
Proof. exact (EQ_MP (@lem17879 q) (@lem0)). Qed.
Lemma lem17884 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem17885 (q : Prop) : (False = q) = (~ q).
Proof. exact (@lem17884 q). Qed.
Lemma lem17886 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem17887 (q : Prop) : (term12 q) = (term21 q).
Proof. exact (MK_COMB (@lem17886) (@lem17885 q)). Qed.
Lemma lem17889 (t : Prop) : (term21 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem17890 (q : Prop) : (term21 q) = q.
Proof. exact (@lem17889 q). Qed.
Lemma lem17891 (q : Prop) : (term12 q) = q.
Proof. exact (TRANS (@lem17887 q) (@lem17890 q)). Qed.
Lemma lem17892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17893 (q : Prop) : (term22 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem17892) (@lem17891 q)). Qed.
Lemma lem17897 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem17898 (q : Prop) : (False \/ q) = q.
Proof. exact (@lem17897 q). Qed.
Lemma lem17899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem17900 (q : Prop) : (term23 q) = (and q).
Proof. exact (MK_COMB (@lem17899) (@lem17898 q)). Qed.
Lemma lem17904 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem17905 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem17906 : term24 = (or True).
Proof. exact (MK_COMB (@lem17905) (@lem17904)). Qed.
Lemma lem17907 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem17908 (q : Prop) : (term25 q) = (term26 q).
Proof. exact (MK_COMB (@lem17906) (@lem17907 q)). Qed.
Lemma lem17910 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem17911 (q : Prop) : (term26 q) = True.
Proof. exact (@lem17910 (~ q)). Qed.
Lemma lem17912 (q : Prop) : (term25 q) = True.
Proof. exact (TRANS (@lem17908 q) (@lem17911 q)). Qed.
Lemma lem17913 (q : Prop) : (term13 q) = (q /\ True).
Proof. exact (MK_COMB (@lem17900 q) (@lem17912 q)). Qed.
Lemma lem17915 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem17916 (q : Prop) : (q /\ True) = q.
Proof. exact (@lem17915 q). Qed.
Lemma lem17917 (q : Prop) : (term13 q) = q.
Proof. exact (TRANS (@lem17913 q) (@lem17916 q)). Qed.
Lemma lem17918 (q : Prop) : ((term12 q) = (term13 q)) = (q = q).
Proof. exact (MK_COMB (@lem17893 q) (@lem17917 q)). Qed.
Lemma lem17920 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem17921 (x : Prop) : (x = x) = True.
Proof. exact (@lem17920 Prop x). Qed.
Lemma lem17922 (q : Prop) : (q = q) = True.
Proof. exact (@lem17921 q). Qed.
Lemma lem17923 (q : Prop) : ((term12 q) = (term13 q)) = True.
Proof. exact (TRANS (@lem17918 q) (@lem17922 q)). Qed.
Lemma lem17924 (q : Prop) : True = ((term12 q) = (term13 q)).
Proof. exact (SYM (@lem17923 q)). Qed.
Lemma lem17925 (q : Prop) : (term12 q) = (term13 q).
Proof. exact (EQ_MP (@lem17924 q) (@lem0)). Qed.
Lemma lem17926 (q : Prop) (p : Prop) (h1 : p = False) : (term8 p q) = (term9 p q).
Proof. exact (EQ_MP (@lem17839 q p h1) (@lem17925 q)). Qed.
Lemma lem17927 (q : Prop) (p : Prop) (h1 : p = True) : (term8 p q) = (term9 p q).
Proof. exact (EQ_MP (@lem17826 q p h1) (@lem17880 q)). Qed.
Lemma lem17930 (p : Prop) (q : Prop) : (term8 p q) = (term9 p q).
Proof. exact (or_elim (@lem17799 p) (fun h0 : p = True => @lem17927 q p h0) (fun h0 : p = False => @lem17926 q p h0)). Qed.
