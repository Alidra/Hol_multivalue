Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL_MEM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1855_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem1135813 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1135814 {_26777 : Type'} (P : type1143 _26777) : term0 _26777 P.
Proof. exact (@lem1135813 _26777 P). Qed.
Lemma lem1135815 {_26777 : Type'} (P : _26777 -> Prop) : term1 _26777 P.
Proof. exact (@lem1135814 _26777 (term2 _26777 P)). Qed.
Lemma lem1135816 {_26777 : Type'} (P : _26777 -> Prop) : (term3 _26777 P) = ((term4 _26777 P) = (@List.Forall _26777 P (@nil _26777))).
Proof. exact (eq_refl (term3 _26777 P)). Qed.
Lemma lem1135817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1135818 {_26777 : Type'} (P : _26777 -> Prop) : (term5 _26777 P) = (term6 _26777 P).
Proof. exact (MK_COMB (@lem1135817) (@lem1135816 _26777 P)). Qed.
Lemma lem1135819 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term7 _26777 P t) = ((term8 _26777 t P) = (@List.Forall _26777 P t)).
Proof. exact (eq_refl (term7 _26777 P t)). Qed.
Lemma lem1135820 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1135821 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term9 _26777 P t) = (term10 _26777 P t).
Proof. exact (MK_COMB (@lem1135820) (@lem1135819 _26777 P t)). Qed.
Lemma lem1135822 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) (t : list _26777) : (term11 _26777 P h t) = ((term12 _26777 h t P) = (term13 _26777 P h t)).
Proof. exact (eq_refl (term11 _26777 P h t)). Qed.
Lemma lem1135823 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) (t : list _26777) : (term14 _26777 P h t) = (term15 _26777 P h t).
Proof. exact (MK_COMB (@lem1135821 _26777 P t) (@lem1135822 _26777 P h t)). Qed.
Lemma lem1135824 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term16 _26777 P h) = (term17 _26777 P h).
Proof. exact (fun_ext (fun t : list _26777 => @lem1135823 _26777 P h t)). Qed.
Lemma lem1135825 {_26777 : Type'} : (@all (list _26777)) = (@all (list _26777)).
Proof. exact (eq_refl (@all (list _26777))). Qed.
Lemma lem1135826 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term18 _26777 P h) = (term19 _26777 P h).
Proof. exact (MK_COMB (@lem1135825 _26777) (@lem1135824 _26777 P h)). Qed.
Lemma lem1135827 {_26777 : Type'} (P : _26777 -> Prop) : (term20 _26777 P) = (term21 _26777 P).
Proof. exact (fun_ext (fun h : _26777 => @lem1135826 _26777 P h)). Qed.
Lemma lem1135828 {_26777 : Type'} : (@all _26777) = (@all _26777).
Proof. exact (eq_refl (@all _26777)). Qed.
Lemma lem1135829 {_26777 : Type'} (P : _26777 -> Prop) : (term22 _26777 P) = (term23 _26777 P).
Proof. exact (MK_COMB (@lem1135828 _26777) (@lem1135827 _26777 P)). Qed.
Lemma lem1135830 {_26777 : Type'} (P : _26777 -> Prop) : (term24 _26777 P) = (term25 _26777 P).
Proof. exact (MK_COMB (@lem1135818 _26777 P) (@lem1135829 _26777 P)). Qed.
Lemma lem1135831 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1135832 {_26777 : Type'} (P : _26777 -> Prop) : (term26 _26777 P) = (term27 _26777 P).
Proof. exact (MK_COMB (@lem1135831) (@lem1135830 _26777 P)). Qed.
Lemma lem1135833 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) : (term7 _26777 P l) = ((term8 _26777 l P) = (@List.Forall _26777 P l)).
Proof. exact (eq_refl (term7 _26777 P l)). Qed.
Lemma lem1135834 {_26777 : Type'} (P : _26777 -> Prop) : (term28 _26777 P) = (term2 _26777 P).
Proof. exact (fun_ext (fun l : list _26777 => @lem1135833 _26777 P l)). Qed.
Lemma lem1135835 {_26777 : Type'} : (@all (list _26777)) = (@all (list _26777)).
Proof. exact (eq_refl (@all (list _26777))). Qed.
Lemma lem1135836 {_26777 : Type'} (P : _26777 -> Prop) : (term29 _26777 P) = (term30 _26777 P).
Proof. exact (MK_COMB (@lem1135835 _26777) (@lem1135834 _26777 P)). Qed.
Lemma lem1135837 {_26777 : Type'} (P : _26777 -> Prop) : (term1 _26777 P) = (term31 _26777 P).
Proof. exact (MK_COMB (@lem1135832 _26777 P) (@lem1135836 _26777 P)). Qed.
Lemma lem1135838 {_26777 : Type'} (P : _26777 -> Prop) : term31 _26777 P.
Proof. exact (EQ_MP (@lem1135837 _26777 P) (@lem1135815 _26777 P)). Qed.
Lemma lem1135839 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : (term8 _26777 t P) = (@List.Forall _26777 P t)) : (term8 _26777 t P) = (@List.Forall _26777 P t).
Proof. exact (h1). Qed.
Lemma lem1135849 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1135850 {_26777 : Type'} (x : _26777) : (@List.In _26777 x (@nil _26777)) = False.
Proof. exact (@lem1135849 _26777 x). Qed.
Lemma lem1135851 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1135852 {_26777 : Type'} (x : _26777) : (term32 _26777 x) = (imp False).
Proof. exact (MK_COMB (@lem1135851) (@lem1135850 _26777 x)). Qed.
Lemma lem1135853 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1135854 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (term33 _26777 P x) = (term34 _26777 P x).
Proof. exact (MK_COMB (@lem1135852 _26777 x) (@lem1135853 _26777 P x)). Qed.
Lemma lem1135856 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1135857 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (term34 _26777 P x) = True.
Proof. exact (@lem1135856 (P x)). Qed.
Lemma lem1135858 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (term33 _26777 P x) = True.
Proof. exact (TRANS (@lem1135854 _26777 P x) (@lem1135857 _26777 P x)). Qed.
Lemma lem1135859 {_26777 : Type'} (P : _26777 -> Prop) : (term35 _26777 P) = (term36 _26777).
Proof. exact (fun_ext (fun x : _26777 => @lem1135858 _26777 P x)). Qed.
Lemma lem1135860 {_26777 : Type'} : (@all _26777) = (@all _26777).
Proof. exact (eq_refl (@all _26777)). Qed.
Lemma lem1135861 {_26777 : Type'} (P : _26777 -> Prop) : (term4 _26777 P) = (term37 _26777).
Proof. exact (MK_COMB (@lem1135860 _26777) (@lem1135859 _26777 P)). Qed.
Lemma lem1135863 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1135864 {_26777 : Type'} (t : Prop) : (term38 _26777 t) = t.
Proof. exact (@lem1135863 _26777 t). Qed.
Lemma lem1135865 {_26777 : Type'} : (term37 _26777) = True.
Proof. exact (@lem1135864 _26777 True). Qed.
Lemma lem1135866 {_26777 : Type'} (P : _26777 -> Prop) : (term4 _26777 P) = True.
Proof. exact (TRANS (@lem1135861 _26777 P) (@lem1135865 _26777)). Qed.
Lemma lem1135867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1135868 {_26777 : Type'} (P : _26777 -> Prop) : (term39 _26777 P) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1135867) (@lem1135866 _26777 P)). Qed.
Lemma lem1135870 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1135871 {_26777 : Type'} (P : _26777 -> Prop) : (@List.Forall _26777 P (@nil _26777)) = True.
Proof. exact (@lem1135870 _26777 P). Qed.
Lemma lem1135872 {_26777 : Type'} (P : _26777 -> Prop) : ((term4 _26777 P) = (@List.Forall _26777 P (@nil _26777))) = (True = True).
Proof. exact (MK_COMB (@lem1135868 _26777 P) (@lem1135871 _26777 P)). Qed.
Lemma lem1135874 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1135875 : (True = True) = True.
Proof. exact (@lem1135874 True). Qed.
Lemma lem1135876 {_26777 : Type'} (P : _26777 -> Prop) : ((term4 _26777 P) = (@List.Forall _26777 P (@nil _26777))) = True.
Proof. exact (TRANS (@lem1135872 _26777 P) (@lem1135875)). Qed.
Lemma lem1135877 {_26777 : Type'} (P : _26777 -> Prop) : True = ((term4 _26777 P) = (@List.Forall _26777 P (@nil _26777))).
Proof. exact (SYM (@lem1135876 _26777 P)). Qed.
Lemma lem1135878 {_26777 : Type'} (P : _26777 -> Prop) : (term4 _26777 P) = (@List.Forall _26777 P (@nil _26777)).
Proof. exact (EQ_MP (@lem1135877 _26777 P) (@lem0)). Qed.
Lemma lem1135888 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term40 _25376 x h t) = (term41 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1135889 {_26777 : Type'} (h : _26777) (x : _26777) (t : list _26777) : (term40 _26777 x h t) = (term41 _26777 h x t).
Proof. exact (@lem1135888 _26777 h x t). Qed.
Lemma lem1135894 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1135895 {_26777 : Type'} (h : _26777) (x : _26777) (t : list _26777) : (term42 _26777 x h t) = (term43 _26777 h x t).
Proof. exact (MK_COMB (@lem1135894) (@lem1135889 _26777 h x t)). Qed.
Lemma lem1135896 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1135897 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term44 _26777 h t P x) = (term45 _26777 h t P x).
Proof. exact (MK_COMB (@lem1135895 _26777 h x t) (@lem1135896 _26777 P x)). Qed.
Lemma lem1135900 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term46 _26777 h t P) = (term47 _26777 h t P).
Proof. exact (fun_ext (fun x : _26777 => @lem1135897 _26777 h t P x)). Qed.
Lemma lem1135901 {_26777 : Type'} : (@all _26777) = (@all _26777).
Proof. exact (eq_refl (@all _26777)). Qed.
Lemma lem1135902 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term12 _26777 h t P) = (term48 _26777 h t P).
Proof. exact (MK_COMB (@lem1135901 _26777) (@lem1135900 _26777 h t P)). Qed.
Lemma lem1135907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1135908 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term49 _26777 h t P) = (term50 _26777 h t P).
Proof. exact (MK_COMB (@lem1135907) (@lem1135902 _26777 h t P)). Qed.
Lemma lem1135910 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term13 _25307 P h t) = (term51 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1135911 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term13 _26777 P h t) = (term51 _26777 h P t).
Proof. exact (@lem1135910 _26777 h P t). Qed.
Lemma lem1135914 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : ((term12 _26777 h t P) = (term13 _26777 P h t)) = ((term48 _26777 h t P) = (term51 _26777 h P t)).
Proof. exact (MK_COMB (@lem1135908 _26777 h t P) (@lem1135911 _26777 h P t)). Qed.
Lemma lem1135917 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) (t : list _26777) : ((term48 _26777 h t P) = (term51 _26777 h P t)) = ((term12 _26777 h t P) = (term13 _26777 P h t)).
Proof. exact (SYM (@lem1135914 _26777 h P t)). Qed.
Lemma lem1135919 (p : Prop) : p = (term52 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1135920 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : ((term48 _26777 h t P) = (term51 _26777 h P t)) = (term53 _26777 h P t).
Proof. exact (@lem1135919 ((term48 _26777 h t P) = (term51 _26777 h P t))). Qed.
Lemma lem1135921 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term53 _26777 h P t) = ((term48 _26777 h t P) = (term51 _26777 h P t)).
Proof. exact (SYM (@lem1135920 _26777 h P t)). Qed.
Lemma lem1135922 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term54 _26777 h P t) : term54 _26777 h P t.
Proof. exact (h1). Qed.
Lemma lem1135925 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term55 _26777 h P t) : term55 _26777 h P t.
Proof. exact (h1). Qed.
Lemma lem1135926 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : term56 _26777 h P t.
Proof. exact (fun h0 : term55 _26777 h P t => @lem1135925 _26777 h P t h0). Qed.
Lemma lem1135927 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term56 _26777 h P t) : term56 _26777 h P t.
Proof. exact (h1). Qed.
Lemma lem1135928 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term55 _26777 h P t) : term55 _26777 h P t.
Proof. exact (h1). Qed.
Lemma lem1135929 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term55 _26777 h P t) (h2 : term56 _26777 h P t) : term55 _26777 h P t.
Proof. exact (@lem1135927 _26777 h P t h2 (@lem1135928 _26777 h P t h1)). Qed.
Lemma lem1135930 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term55 _26777 h P t) : term57 _26777 h P t.
Proof. exact (fun h0 : term56 _26777 h P t => @lem1135929 _26777 h P t h1 h0). Qed.
Lemma lem1135931 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term56 _26777 h P t) : term56 _26777 h P t.
Proof. exact (h1). Qed.
Lemma lem1135932 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term55 _26777 h P t) (h2 : term56 _26777 h P t) : term55 _26777 h P t.
Proof. exact (@lem1135930 _26777 h P t h1 (@lem1135931 _26777 h P t h2)). Qed.
Lemma lem1135933 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term56 _26777 h P t) : term56 _26777 h P t.
Proof. exact (fun h0 : term55 _26777 h P t => @lem1135932 _26777 h P t h0 h1). Qed.
Lemma lem1135934 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : term58 _26777 h P t.
Proof. exact (fun h0 : term56 _26777 h P t => @lem1135933 _26777 h P t h0). Qed.
Lemma lem1135937 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : term56 _26777 h P t.
Proof. exact (@lem1135934 _26777 h P t (@lem1135926 _26777 h P t)). Qed.
Lemma lem1135938 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : term56 _26777 h P t.
Proof. exact (@lem1135937 _26777 h P t). Qed.
Lemma lem1135960 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1135961 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term53 _26777 h P t) = (term59 _26777 h P t).
Proof. exact (@lem1135960 (term54 _26777 h P t)). Qed.
Lemma lem1135963 (t : Prop) : (term60 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1135964 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term59 _26777 h P t) = ((term48 _26777 h t P) = (term51 _26777 h P t)).
Proof. exact (@lem1135963 ((term48 _26777 h t P) = (term51 _26777 h P t))). Qed.
Lemma lem1135965 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term53 _26777 h P t) = ((term48 _26777 h t P) = (term51 _26777 h P t)).
Proof. exact (TRANS (@lem1135961 _26777 h P t) (@lem1135964 _26777 h P t)). Qed.
Lemma lem1135976 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term10 _26777 P t) = (term10 _26777 P t).
Proof. exact (eq_refl (term10 _26777 P t)). Qed.
Lemma lem1135977 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term55 _26777 h P t) = (term61 _26777 h P t).
Proof. exact (MK_COMB (@lem1135976 _26777 P t) (@lem1135965 _26777 h P t)). Qed.
Lemma lem1135980 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term62 _26777 P t) = (term63 _26777 P t).
Proof. exact (fun_ext (fun h : _26777 => @lem1135977 _26777 h P t)). Qed.
Lemma lem1135981 {_26777 : Type'} : (@all _26777) = (@all _26777).
Proof. exact (eq_refl (@all _26777)). Qed.
Lemma lem1135982 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term64 _26777 P t) = (term65 _26777 P t).
Proof. exact (MK_COMB (@lem1135981 _26777) (@lem1135980 _26777 P t)). Qed.
Lemma lem1135987 {_26777 : Type'} (t : list _26777) : (term66 _26777 t) = (term67 _26777 t).
Proof. exact (fun_ext (fun P : _26777 -> Prop => @lem1135982 _26777 P t)). Qed.
Lemma lem1135988 {_26777 : Type'} : (@all (_26777 -> Prop)) = (@all (_26777 -> Prop)).
Proof. exact (eq_refl (@all (_26777 -> Prop))). Qed.
Lemma lem1135989 {_26777 : Type'} (t : list _26777) : (term68 _26777 t) = (term69 _26777 t).
Proof. exact (MK_COMB (@lem1135988 _26777) (@lem1135987 _26777 t)). Qed.
Lemma lem1135994 {_26777 : Type'} : (term70 _26777) = (term71 _26777).
Proof. exact (fun_ext (fun t : list _26777 => @lem1135989 _26777 t)). Qed.
Lemma lem1135995 {_26777 : Type'} : (@all (list _26777)) = (@all (list _26777)).
Proof. exact (eq_refl (@all (list _26777))). Qed.
Lemma lem1136004 {_26777 : Type'} : (term72 _26777) = (term73 _26777).
Proof. exact (MK_COMB (@lem1135995 _26777) (@lem1135994 _26777)). Qed.
Lemma lem1136009 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term51 _26777 h P t) = (term51 _26777 h P t).
Proof. exact (eq_refl (term51 _26777 h P t)). Qed.
Lemma lem1136018 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term45 _26777 h t P x) = (term45 _26777 h t P x).
Proof. exact (eq_refl (term45 _26777 h t P x)). Qed.
Lemma lem1136019 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term47 _26777 h t P) = (term47 _26777 h t P).
Proof. exact (fun_ext (fun x : _26777 => @lem1136018 _26777 h t P x)). Qed.
Lemma lem1136020 {_26777 : Type'} : (@all _26777) = (@all _26777).
Proof. exact (eq_refl (@all _26777)). Qed.
Lemma lem1136021 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term48 _26777 h t P) = (term48 _26777 h t P).
Proof. exact (MK_COMB (@lem1136020 _26777) (@lem1136019 _26777 h t P)). Qed.
Lemma lem1136022 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1136023 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term50 _26777 h t P) = (term50 _26777 h t P).
Proof. exact (MK_COMB (@lem1136022) (@lem1136021 _26777 h t P)). Qed.
Lemma lem1136024 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : ((term48 _26777 h t P) = (term51 _26777 h P t)) = ((term48 _26777 h t P) = (term51 _26777 h P t)).
Proof. exact (MK_COMB (@lem1136023 _26777 h t P) (@lem1136009 _26777 h P t)). Qed.
Lemma lem1136025 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (@List.Forall _26777 P t) = (@List.Forall _26777 P t).
Proof. exact (eq_refl (@List.Forall _26777 P t)). Qed.
Lemma lem1136030 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term74 _26777 t P x) = (term74 _26777 t P x).
Proof. exact (eq_refl (term74 _26777 t P x)). Qed.
Lemma lem1136031 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term75 _26777 t P) = (term75 _26777 t P).
Proof. exact (fun_ext (fun x : _26777 => @lem1136030 _26777 t P x)). Qed.
Lemma lem1136032 {_26777 : Type'} : (@all _26777) = (@all _26777).
Proof. exact (eq_refl (@all _26777)). Qed.
Lemma lem1136033 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term8 _26777 t P) = (term8 _26777 t P).
Proof. exact (MK_COMB (@lem1136032 _26777) (@lem1136031 _26777 t P)). Qed.
Lemma lem1136034 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1136035 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term76 _26777 t P) = (term76 _26777 t P).
Proof. exact (MK_COMB (@lem1136034) (@lem1136033 _26777 t P)). Qed.
Lemma lem1136036 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : ((term8 _26777 t P) = (@List.Forall _26777 P t)) = ((term8 _26777 t P) = (@List.Forall _26777 P t)).
Proof. exact (MK_COMB (@lem1136035 _26777 t P) (@lem1136025 _26777 P t)). Qed.
Lemma lem1136037 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1136038 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term10 _26777 P t) = (term10 _26777 P t).
Proof. exact (MK_COMB (@lem1136037) (@lem1136036 _26777 P t)). Qed.
Lemma lem1136039 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term61 _26777 h P t) = (term61 _26777 h P t).
Proof. exact (MK_COMB (@lem1136038 _26777 P t) (@lem1136024 _26777 h P t)). Qed.
Lemma lem1136040 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term63 _26777 P t) = (term63 _26777 P t).
Proof. exact (fun_ext (fun h : _26777 => @lem1136039 _26777 h P t)). Qed.
Lemma lem1136041 {_26777 : Type'} : (@all _26777) = (@all _26777).
Proof. exact (eq_refl (@all _26777)). Qed.
Lemma lem1136042 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term65 _26777 P t) = (term65 _26777 P t).
Proof. exact (MK_COMB (@lem1136041 _26777) (@lem1136040 _26777 P t)). Qed.
Lemma lem1136043 {_26777 : Type'} (t : list _26777) : (term67 _26777 t) = (term67 _26777 t).
Proof. exact (fun_ext (fun P : _26777 -> Prop => @lem1136042 _26777 P t)). Qed.
Lemma lem1136044 {_26777 : Type'} : (@all (_26777 -> Prop)) = (@all (_26777 -> Prop)).
Proof. exact (eq_refl (@all (_26777 -> Prop))). Qed.
Lemma lem1136045 {_26777 : Type'} (t : list _26777) : (term69 _26777 t) = (term69 _26777 t).
Proof. exact (MK_COMB (@lem1136044 _26777) (@lem1136043 _26777 t)). Qed.
Lemma lem1136046 {_26777 : Type'} : (term71 _26777) = (term71 _26777).
Proof. exact (fun_ext (fun t : list _26777 => @lem1136045 _26777 t)). Qed.
Lemma lem1136047 {_26777 : Type'} : (@all (list _26777)) = (@all (list _26777)).
Proof. exact (eq_refl (@all (list _26777))). Qed.
Lemma lem1136048 {_26777 : Type'} : (term73 _26777) = (term73 _26777).
Proof. exact (MK_COMB (@lem1136047 _26777) (@lem1136046 _26777)). Qed.
Lemma lem1136091 {_26777 : Type'} : (term72 _26777) = (term73 _26777).
Proof. exact (TRANS (@lem1136004 _26777) (@lem1136048 _26777)). Qed.
Lemma lem1136092 {_26777 : Type'} : (term73 _26777) = (term72 _26777).
Proof. exact (SYM (@lem1136091 _26777)). Qed.
Lemma lem1136093 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : (term8 _26777 t P) = (@List.Forall _26777 P t)) : (term8 _26777 t P) = (@List.Forall _26777 P t).
Proof. exact (h1). Qed.
Lemma lem1136095 (p : Prop) : p = (term52 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1136096 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : ((term48 _26777 h t P) = (term51 _26777 h P t)) = (term53 _26777 h P t).
Proof. exact (@lem1136095 ((term48 _26777 h t P) = (term51 _26777 h P t))). Qed.
Lemma lem1136097 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term53 _26777 h P t) = ((term48 _26777 h t P) = (term51 _26777 h P t)).
Proof. exact (SYM (@lem1136096 _26777 h P t)). Qed.
Lemma lem1136098 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term54 _26777 h P t) : term54 _26777 h P t.
Proof. exact (h1). Qed.
Lemma lem1136107 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term77 _26777 t P x) = (term78 _26777 t P x).
Proof. exact (@lem17362 (@List.In _26777 x t) (P x)). Qed.
Lemma lem1136112 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term74 _26777 t P x) = (term79 _26777 t P x).
Proof. exact (@lem17265 (@List.In _26777 x t) (P x)). Qed.
Lemma lem1136113 {_26777 : Type'} (P : _26777 -> Prop) : (term80 _26777 P) = (term81 _26777 P).
Proof. exact (@lem18392 _26777 P). Qed.
Lemma lem1136114 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term82 _26777 t P) = (term83 _26777 t P).
Proof. exact (@lem1136113 _26777 (term75 _26777 t P)). Qed.
Lemma lem1136115 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term84 _26777 t P x) = (term74 _26777 t P x).
Proof. exact (eq_refl (term84 _26777 t P x)). Qed.
Lemma lem1136116 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1136117 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term85 _26777 t P x) = (term77 _26777 t P x).
Proof. exact (MK_COMB (@lem1136116) (@lem1136115 _26777 t P x)). Qed.
Lemma lem1136118 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term85 _26777 t P x) = (term78 _26777 t P x).
Proof. exact (TRANS (@lem1136117 _26777 t P x) (@lem1136107 _26777 t P x)). Qed.
Lemma lem1136119 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term86 _26777 t P) = (term87 _26777 t P).
Proof. exact (fun_ext (fun x : _26777 => @lem1136118 _26777 t P x)). Qed.
Lemma lem1136120 {_26777 : Type'} : (@ex _26777) = (@ex _26777).
Proof. exact (eq_refl (@ex _26777)). Qed.
Lemma lem1136121 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term83 _26777 t P) = (term88 _26777 t P).
Proof. exact (MK_COMB (@lem1136120 _26777) (@lem1136119 _26777 t P)). Qed.
Lemma lem1136122 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term82 _26777 t P) = (term88 _26777 t P).
Proof. exact (TRANS (@lem1136114 _26777 t P) (@lem1136121 _26777 t P)). Qed.
Lemma lem1136123 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term75 _26777 t P) = (term89 _26777 t P).
Proof. exact (fun_ext (fun x : _26777 => @lem1136112 _26777 t P x)). Qed.
Lemma lem1136124 {_26777 : Type'} : (@all _26777) = (@all _26777).
Proof. exact (eq_refl (@all _26777)). Qed.
Lemma lem1136125 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term8 _26777 t P) = (term90 _26777 t P).
Proof. exact (MK_COMB (@lem1136124 _26777) (@lem1136123 _26777 t P)). Qed.
Lemma lem1136126 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term91 _26777 P t) = (term91 _26777 P t).
Proof. exact (eq_refl (term91 _26777 P t)). Qed.
Lemma lem1136127 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (@List.Forall _26777 P t) = (@List.Forall _26777 P t).
Proof. exact (eq_refl (@List.Forall _26777 P t)). Qed.
Lemma lem1136128 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1136129 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term92 _26777 t P) = (term93 _26777 t P).
Proof. exact (MK_COMB (@lem1136128) (@lem1136122 _26777 t P)). Qed.
Lemma lem1136130 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term94 _26777 P t) = (term95 _26777 P t).
Proof. exact (MK_COMB (@lem1136129 _26777 t P) (@lem1136126 _26777 P t)). Qed.
Lemma lem1136131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1136132 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term96 _26777 t P) = (term97 _26777 t P).
Proof. exact (MK_COMB (@lem1136131) (@lem1136125 _26777 t P)). Qed.
Lemma lem1136133 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term98 _26777 P t) = (term99 _26777 P t).
Proof. exact (MK_COMB (@lem1136132 _26777 t P) (@lem1136127 _26777 P t)). Qed.
Lemma lem1136134 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1136135 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term100 _26777 P t) = (term101 _26777 P t).
Proof. exact (MK_COMB (@lem1136134) (@lem1136133 _26777 P t)). Qed.
Lemma lem1136136 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term102 _26777 P t) = (term103 _26777 P t).
Proof. exact (MK_COMB (@lem1136135 _26777 P t) (@lem1136130 _26777 P t)). Qed.
Lemma lem1136137 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : ((term8 _26777 t P) = (@List.Forall _26777 P t)) = (term102 _26777 P t).
Proof. exact (@lem17500 (term8 _26777 t P) (@List.Forall _26777 P t)). Qed.
Lemma lem1136138 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : ((term8 _26777 t P) = (@List.Forall _26777 P t)) = (term103 _26777 P t).
Proof. exact (TRANS (@lem1136137 _26777 P t) (@lem1136136 _26777 P t)). Qed.
Lemma lem1136221 {A : Type'} (P : A -> Prop) (Q : Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1136222 {_26777 : Type'} (P : _26777 -> Prop) (Q : Prop) : (term104 _26777 P Q) = (term105 _26777 P Q).
Proof. exact (@lem1136221 _26777 P Q). Qed.
Lemma lem1136223 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term106 _26777 P t) = (term107 _26777 P t).
Proof. exact (@lem1136222 _26777 (term87 _26777 t P) (term91 _26777 P t)). Qed.
Lemma lem1136224 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term108 _26777 t P x) = (term78 _26777 t P x).
Proof. exact (eq_refl (term108 _26777 t P x)). Qed.
Lemma lem1136225 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term109 _26777 t P) = (term87 _26777 t P).
Proof. exact (fun_ext (fun x : _26777 => @lem1136224 _26777 t P x)). Qed.
Lemma lem1136226 {_26777 : Type'} : (@ex _26777) = (@ex _26777).
Proof. exact (eq_refl (@ex _26777)). Qed.
Lemma lem1136227 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term110 _26777 t P) = (term88 _26777 t P).
Proof. exact (MK_COMB (@lem1136226 _26777) (@lem1136225 _26777 t P)). Qed.
Lemma lem1136228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1136229 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term111 _26777 t P) = (term93 _26777 t P).
Proof. exact (MK_COMB (@lem1136228) (@lem1136227 _26777 t P)). Qed.
Lemma lem1136230 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term91 _26777 P t) = (term91 _26777 P t).
Proof. exact (eq_refl (term91 _26777 P t)). Qed.
Lemma lem1136231 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term106 _26777 P t) = (term95 _26777 P t).
Proof. exact (MK_COMB (@lem1136229 _26777 t P) (@lem1136230 _26777 P t)). Qed.
Lemma lem1136232 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1136233 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term112 _26777 P t) = (term113 _26777 P t).
Proof. exact (MK_COMB (@lem1136232) (@lem1136231 _26777 P t)). Qed.
Lemma lem1136234 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term108 _26777 t P x) = (term78 _26777 t P x).
Proof. exact (eq_refl (term108 _26777 t P x)). Qed.
Lemma lem1136235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1136236 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term114 _26777 t P x) = (term115 _26777 t P x).
Proof. exact (MK_COMB (@lem1136235) (@lem1136234 _26777 t P x)). Qed.
Lemma lem1136237 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term91 _26777 P t) = (term91 _26777 P t).
Proof. exact (eq_refl (term91 _26777 P t)). Qed.
Lemma lem1136238 {_26777 : Type'} (x : _26777) (P : _26777 -> Prop) (t : list _26777) : (term116 _26777 x P t) = (term117 _26777 x P t).
Proof. exact (MK_COMB (@lem1136236 _26777 t P x) (@lem1136237 _26777 P t)). Qed.
Lemma lem1136239 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term118 _26777 P t) = (term119 _26777 P t).
Proof. exact (fun_ext (fun x : _26777 => @lem1136238 _26777 x P t)). Qed.
Lemma lem1136240 {_26777 : Type'} : (@ex _26777) = (@ex _26777).
Proof. exact (eq_refl (@ex _26777)). Qed.
Lemma lem1136241 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term107 _26777 P t) = (term120 _26777 P t).
Proof. exact (MK_COMB (@lem1136240 _26777) (@lem1136239 _26777 P t)). Qed.
Lemma lem1136242 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : ((term106 _26777 P t) = (term107 _26777 P t)) = ((term95 _26777 P t) = (term120 _26777 P t)).
Proof. exact (MK_COMB (@lem1136233 _26777 P t) (@lem1136241 _26777 P t)). Qed.
Lemma lem1136243 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term95 _26777 P t) = (term120 _26777 P t).
Proof. exact (EQ_MP (@lem1136242 _26777 P t) (@lem1136223 _26777 P t)). Qed.
Lemma lem1136244 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term101 _26777 P t) = (term101 _26777 P t).
Proof. exact (eq_refl (term101 _26777 P t)). Qed.
Lemma lem1136245 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term103 _26777 P t) = (term121 _26777 P t).
Proof. exact (MK_COMB (@lem1136244 _26777 P t) (@lem1136243 _26777 P t)). Qed.
Lemma lem1136247 {A : Type'} (P : Prop) (Q : A -> Prop) : (term122 A P Q) = (term123 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1136248 {_26777 : Type'} (P : Prop) (Q : _26777 -> Prop) : (term122 _26777 P Q) = (term123 _26777 P Q).
Proof. exact (@lem1136247 _26777 P Q). Qed.
Lemma lem1136249 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term124 _26777 P t) = (term125 _26777 P t).
Proof. exact (@lem1136248 _26777 (term99 _26777 P t) (term119 _26777 P t)). Qed.
Lemma lem1136250 {_26777 : Type'} (x : _26777) (P : _26777 -> Prop) (t : list _26777) : (term126 _26777 P t x) = (term117 _26777 x P t).
Proof. exact (eq_refl (term126 _26777 P t x)). Qed.
Lemma lem1136251 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term127 _26777 P t) = (term119 _26777 P t).
Proof. exact (fun_ext (fun x : _26777 => @lem1136250 _26777 x P t)). Qed.
Lemma lem1136252 {_26777 : Type'} : (@ex _26777) = (@ex _26777).
Proof. exact (eq_refl (@ex _26777)). Qed.
Lemma lem1136253 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term128 _26777 P t) = (term120 _26777 P t).
Proof. exact (MK_COMB (@lem1136252 _26777) (@lem1136251 _26777 P t)). Qed.
Lemma lem1136254 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term101 _26777 P t) = (term101 _26777 P t).
Proof. exact (eq_refl (term101 _26777 P t)). Qed.
Lemma lem1136255 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term124 _26777 P t) = (term121 _26777 P t).
Proof. exact (MK_COMB (@lem1136254 _26777 P t) (@lem1136253 _26777 P t)). Qed.
Lemma lem1136256 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1136257 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term129 _26777 P t) = (term130 _26777 P t).
Proof. exact (MK_COMB (@lem1136256) (@lem1136255 _26777 P t)). Qed.
Lemma lem1136258 {_26777 : Type'} (x : _26777) (P : _26777 -> Prop) (t : list _26777) : (term126 _26777 P t x) = (term117 _26777 x P t).
Proof. exact (eq_refl (term126 _26777 P t x)). Qed.
Lemma lem1136259 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term101 _26777 P t) = (term101 _26777 P t).
Proof. exact (eq_refl (term101 _26777 P t)). Qed.
Lemma lem1136260 {_26777 : Type'} (x : _26777) (P : _26777 -> Prop) (t : list _26777) : (term131 _26777 P t x) = (term132 _26777 x P t).
Proof. exact (MK_COMB (@lem1136259 _26777 P t) (@lem1136258 _26777 x P t)). Qed.
Lemma lem1136261 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term133 _26777 P t) = (term134 _26777 P t).
Proof. exact (fun_ext (fun x : _26777 => @lem1136260 _26777 x P t)). Qed.
Lemma lem1136262 {_26777 : Type'} : (@ex _26777) = (@ex _26777).
Proof. exact (eq_refl (@ex _26777)). Qed.
Lemma lem1136263 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term125 _26777 P t) = (term135 _26777 P t).
Proof. exact (MK_COMB (@lem1136262 _26777) (@lem1136261 _26777 P t)). Qed.
Lemma lem1136264 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : ((term124 _26777 P t) = (term125 _26777 P t)) = ((term121 _26777 P t) = (term135 _26777 P t)).
Proof. exact (MK_COMB (@lem1136257 _26777 P t) (@lem1136263 _26777 P t)). Qed.
Lemma lem1136265 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term121 _26777 P t) = (term135 _26777 P t).
Proof. exact (EQ_MP (@lem1136264 _26777 P t) (@lem1136249 _26777 P t)). Qed.
Lemma lem1136267 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term103 _26777 P t) = (term135 _26777 P t).
Proof. exact (TRANS (@lem1136245 _26777 P t) (@lem1136265 _26777 P t)). Qed.
Lemma lem1136268 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : ((term8 _26777 t P) = (@List.Forall _26777 P t)) = (term135 _26777 P t).
Proof. exact (TRANS (@lem1136138 _26777 P t) (@lem1136267 _26777 P t)). Qed.
Lemma lem1136269 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : (term8 _26777 t P) = (@List.Forall _26777 P t)) : term135 _26777 P t.
Proof. exact (EQ_MP (@lem1136268 _26777 P t) (@lem1136093 _26777 P t h1)). Qed.
Lemma lem1136278 {_26777 : Type'} (h : _26777) (x : _26777) (t : list _26777) : (term136 _26777 h x t) = (term137 _26777 h x t).
Proof. exact (@lem17160 (x = h) (@List.In _26777 x t)). Qed.
Lemma lem1136283 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1136288 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term138 _26777 h t P x) = (term139 _26777 h t P x).
Proof. exact (@lem17362 (term41 _26777 h x t) (P x)). Qed.
Lemma lem1136289 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1136290 {_26777 : Type'} (h : _26777) (x : _26777) (t : list _26777) : (term140 _26777 h x t) = (term141 _26777 h x t).
Proof. exact (MK_COMB (@lem1136289) (@lem1136278 _26777 h x t)). Qed.
Lemma lem1136291 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term142 _26777 h t P x) = (term143 _26777 h t P x).
Proof. exact (MK_COMB (@lem1136290 _26777 h x t) (@lem1136283 _26777 P x)). Qed.
Lemma lem1136292 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term45 _26777 h t P x) = (term142 _26777 h t P x).
Proof. exact (@lem17265 (term41 _26777 h x t) (P x)). Qed.
Lemma lem1136293 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term45 _26777 h t P x) = (term143 _26777 h t P x).
Proof. exact (TRANS (@lem1136292 _26777 h t P x) (@lem1136291 _26777 h t P x)). Qed.
Lemma lem1136294 {_26777 : Type'} (P : _26777 -> Prop) : (term80 _26777 P) = (term81 _26777 P).
Proof. exact (@lem18392 _26777 P). Qed.
Lemma lem1136295 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term144 _26777 h t P) = (term145 _26777 h t P).
Proof. exact (@lem1136294 _26777 (term47 _26777 h t P)). Qed.
Lemma lem1136296 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term146 _26777 h t P x) = (term45 _26777 h t P x).
Proof. exact (eq_refl (term146 _26777 h t P x)). Qed.
Lemma lem1136297 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1136298 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term147 _26777 h t P x) = (term138 _26777 h t P x).
Proof. exact (MK_COMB (@lem1136297) (@lem1136296 _26777 h t P x)). Qed.
Lemma lem1136299 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term147 _26777 h t P x) = (term139 _26777 h t P x).
Proof. exact (TRANS (@lem1136298 _26777 h t P x) (@lem1136288 _26777 h t P x)). Qed.
Lemma lem1136300 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term148 _26777 h t P) = (term149 _26777 h t P).
Proof. exact (fun_ext (fun x : _26777 => @lem1136299 _26777 h t P x)). Qed.
Lemma lem1136301 {_26777 : Type'} : (@ex _26777) = (@ex _26777).
Proof. exact (eq_refl (@ex _26777)). Qed.
Lemma lem1136302 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term145 _26777 h t P) = (term150 _26777 h t P).
Proof. exact (MK_COMB (@lem1136301 _26777) (@lem1136300 _26777 h t P)). Qed.
Lemma lem1136303 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term144 _26777 h t P) = (term150 _26777 h t P).
Proof. exact (TRANS (@lem1136295 _26777 h t P) (@lem1136302 _26777 h t P)). Qed.
Lemma lem1136304 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term47 _26777 h t P) = (term151 _26777 h t P).
Proof. exact (fun_ext (fun x : _26777 => @lem1136293 _26777 h t P x)). Qed.
Lemma lem1136305 {_26777 : Type'} : (@all _26777) = (@all _26777).
Proof. exact (eq_refl (@all _26777)). Qed.
Lemma lem1136306 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term48 _26777 h t P) = (term152 _26777 h t P).
Proof. exact (MK_COMB (@lem1136305 _26777) (@lem1136304 _26777 h t P)). Qed.
Lemma lem1136315 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term153 _26777 h P t) = (term154 _26777 h P t).
Proof. exact (@lem17045 (P h) (@List.Forall _26777 P t)). Qed.
Lemma lem1136318 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term51 _26777 h P t) = (term51 _26777 h P t).
Proof. exact (eq_refl (term51 _26777 h P t)). Qed.
Lemma lem1136319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1136320 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term155 _26777 h t P) = (term156 _26777 h t P).
Proof. exact (MK_COMB (@lem1136319) (@lem1136303 _26777 h t P)). Qed.
Lemma lem1136321 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term157 _26777 h P t) = (term158 _26777 h P t).
Proof. exact (MK_COMB (@lem1136320 _26777 h t P) (@lem1136318 _26777 h P t)). Qed.
Lemma lem1136322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1136323 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term159 _26777 h t P) = (term160 _26777 h t P).
Proof. exact (MK_COMB (@lem1136322) (@lem1136306 _26777 h t P)). Qed.
Lemma lem1136324 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term161 _26777 h P t) = (term162 _26777 h P t).
Proof. exact (MK_COMB (@lem1136323 _26777 h t P) (@lem1136315 _26777 h P t)). Qed.
Lemma lem1136325 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1136326 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term163 _26777 h P t) = (term164 _26777 h P t).
Proof. exact (MK_COMB (@lem1136325) (@lem1136324 _26777 h P t)). Qed.
Lemma lem1136327 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term165 _26777 h P t) = (term166 _26777 h P t).
Proof. exact (MK_COMB (@lem1136326 _26777 h P t) (@lem1136321 _26777 h P t)). Qed.
Lemma lem1136328 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term54 _26777 h P t) = (term165 _26777 h P t).
Proof. exact (@lem17646 (term48 _26777 h t P) (term51 _26777 h P t)). Qed.
Lemma lem1136329 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term54 _26777 h P t) = (term166 _26777 h P t).
Proof. exact (TRANS (@lem1136328 _26777 h P t) (@lem1136327 _26777 h P t)). Qed.
Lemma lem1136412 {A : Type'} (P : A -> Prop) (Q : Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1136413 {_26777 : Type'} (P : _26777 -> Prop) (Q : Prop) : (term104 _26777 P Q) = (term105 _26777 P Q).
Proof. exact (@lem1136412 _26777 P Q). Qed.
Lemma lem1136414 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term167 _26777 h P t) = (term168 _26777 h P t).
Proof. exact (@lem1136413 _26777 (term149 _26777 h t P) (term51 _26777 h P t)). Qed.
Lemma lem1136415 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term169 _26777 h t P x) = (term139 _26777 h t P x).
Proof. exact (eq_refl (term169 _26777 h t P x)). Qed.
Lemma lem1136416 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term170 _26777 h t P) = (term149 _26777 h t P).
Proof. exact (fun_ext (fun x : _26777 => @lem1136415 _26777 h t P x)). Qed.
Lemma lem1136417 {_26777 : Type'} : (@ex _26777) = (@ex _26777).
Proof. exact (eq_refl (@ex _26777)). Qed.
Lemma lem1136418 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term171 _26777 h t P) = (term150 _26777 h t P).
Proof. exact (MK_COMB (@lem1136417 _26777) (@lem1136416 _26777 h t P)). Qed.
Lemma lem1136419 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1136420 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term172 _26777 h t P) = (term156 _26777 h t P).
Proof. exact (MK_COMB (@lem1136419) (@lem1136418 _26777 h t P)). Qed.
Lemma lem1136421 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term51 _26777 h P t) = (term51 _26777 h P t).
Proof. exact (eq_refl (term51 _26777 h P t)). Qed.
Lemma lem1136422 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term167 _26777 h P t) = (term158 _26777 h P t).
Proof. exact (MK_COMB (@lem1136420 _26777 h t P) (@lem1136421 _26777 h P t)). Qed.
Lemma lem1136423 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1136424 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term173 _26777 h P t) = (term174 _26777 h P t).
Proof. exact (MK_COMB (@lem1136423) (@lem1136422 _26777 h P t)). Qed.
Lemma lem1136425 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term169 _26777 h t P x) = (term139 _26777 h t P x).
Proof. exact (eq_refl (term169 _26777 h t P x)). Qed.
Lemma lem1136426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1136427 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term175 _26777 h t P x) = (term176 _26777 h t P x).
Proof. exact (MK_COMB (@lem1136426) (@lem1136425 _26777 h t P x)). Qed.
Lemma lem1136428 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term51 _26777 h P t) = (term51 _26777 h P t).
Proof. exact (eq_refl (term51 _26777 h P t)). Qed.
Lemma lem1136429 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term177 _26777 x h P t) = (term178 _26777 x h P t).
Proof. exact (MK_COMB (@lem1136427 _26777 h t P x) (@lem1136428 _26777 h P t)). Qed.
Lemma lem1136430 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term179 _26777 h P t) = (term180 _26777 h P t).
Proof. exact (fun_ext (fun x : _26777 => @lem1136429 _26777 x h P t)). Qed.
Lemma lem1136431 {_26777 : Type'} : (@ex _26777) = (@ex _26777).
Proof. exact (eq_refl (@ex _26777)). Qed.
Lemma lem1136432 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term168 _26777 h P t) = (term181 _26777 h P t).
Proof. exact (MK_COMB (@lem1136431 _26777) (@lem1136430 _26777 h P t)). Qed.
Lemma lem1136433 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : ((term167 _26777 h P t) = (term168 _26777 h P t)) = ((term158 _26777 h P t) = (term181 _26777 h P t)).
Proof. exact (MK_COMB (@lem1136424 _26777 h P t) (@lem1136432 _26777 h P t)). Qed.
Lemma lem1136434 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term158 _26777 h P t) = (term181 _26777 h P t).
Proof. exact (EQ_MP (@lem1136433 _26777 h P t) (@lem1136414 _26777 h P t)). Qed.
Lemma lem1136435 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term164 _26777 h P t) = (term164 _26777 h P t).
Proof. exact (eq_refl (term164 _26777 h P t)). Qed.
Lemma lem1136436 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term166 _26777 h P t) = (term182 _26777 h P t).
Proof. exact (MK_COMB (@lem1136435 _26777 h P t) (@lem1136434 _26777 h P t)). Qed.
Lemma lem1136438 {A : Type'} (P : Prop) (Q : A -> Prop) : (term122 A P Q) = (term123 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1136439 {_26777 : Type'} (P : Prop) (Q : _26777 -> Prop) : (term122 _26777 P Q) = (term123 _26777 P Q).
Proof. exact (@lem1136438 _26777 P Q). Qed.
Lemma lem1136440 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term183 _26777 h P t) = (term184 _26777 h P t).
Proof. exact (@lem1136439 _26777 (term162 _26777 h P t) (term180 _26777 h P t)). Qed.
Lemma lem1136441 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term185 _26777 h P t x) = (term178 _26777 x h P t).
Proof. exact (eq_refl (term185 _26777 h P t x)). Qed.
Lemma lem1136442 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term186 _26777 h P t) = (term180 _26777 h P t).
Proof. exact (fun_ext (fun x : _26777 => @lem1136441 _26777 x h P t)). Qed.
Lemma lem1136443 {_26777 : Type'} : (@ex _26777) = (@ex _26777).
Proof. exact (eq_refl (@ex _26777)). Qed.
Lemma lem1136444 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term187 _26777 h P t) = (term181 _26777 h P t).
Proof. exact (MK_COMB (@lem1136443 _26777) (@lem1136442 _26777 h P t)). Qed.
Lemma lem1136445 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term164 _26777 h P t) = (term164 _26777 h P t).
Proof. exact (eq_refl (term164 _26777 h P t)). Qed.
Lemma lem1136446 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term183 _26777 h P t) = (term182 _26777 h P t).
Proof. exact (MK_COMB (@lem1136445 _26777 h P t) (@lem1136444 _26777 h P t)). Qed.
Lemma lem1136447 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1136448 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term188 _26777 h P t) = (term189 _26777 h P t).
Proof. exact (MK_COMB (@lem1136447) (@lem1136446 _26777 h P t)). Qed.
Lemma lem1136449 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term185 _26777 h P t x) = (term178 _26777 x h P t).
Proof. exact (eq_refl (term185 _26777 h P t x)). Qed.
Lemma lem1136450 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term164 _26777 h P t) = (term164 _26777 h P t).
Proof. exact (eq_refl (term164 _26777 h P t)). Qed.
Lemma lem1136451 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term190 _26777 h P t x) = (term191 _26777 x h P t).
Proof. exact (MK_COMB (@lem1136450 _26777 h P t) (@lem1136449 _26777 x h P t)). Qed.
Lemma lem1136452 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term192 _26777 h P t) = (term193 _26777 h P t).
Proof. exact (fun_ext (fun x : _26777 => @lem1136451 _26777 x h P t)). Qed.
Lemma lem1136453 {_26777 : Type'} : (@ex _26777) = (@ex _26777).
Proof. exact (eq_refl (@ex _26777)). Qed.
Lemma lem1136454 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term184 _26777 h P t) = (term194 _26777 h P t).
Proof. exact (MK_COMB (@lem1136453 _26777) (@lem1136452 _26777 h P t)). Qed.
Lemma lem1136455 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : ((term183 _26777 h P t) = (term184 _26777 h P t)) = ((term182 _26777 h P t) = (term194 _26777 h P t)).
Proof. exact (MK_COMB (@lem1136448 _26777 h P t) (@lem1136454 _26777 h P t)). Qed.
Lemma lem1136456 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term182 _26777 h P t) = (term194 _26777 h P t).
Proof. exact (EQ_MP (@lem1136455 _26777 h P t) (@lem1136440 _26777 h P t)). Qed.
Lemma lem1136458 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term166 _26777 h P t) = (term194 _26777 h P t).
Proof. exact (TRANS (@lem1136436 _26777 h P t) (@lem1136456 _26777 h P t)). Qed.
Lemma lem1136459 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term54 _26777 h P t) = (term194 _26777 h P t).
Proof. exact (TRANS (@lem1136329 _26777 h P t) (@lem1136458 _26777 h P t)). Qed.
Lemma lem1136460 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term54 _26777 h P t) : term194 _26777 h P t.
Proof. exact (EQ_MP (@lem1136459 _26777 h P t) (@lem1136098 _26777 h P t h1)). Qed.
Lemma lem1136461 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term191 _26777 x h P t) : term191 _26777 x h P t.
Proof. exact (h1). Qed.
Lemma lem1136462 {_26777 : Type'} (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term132 _26777 x' P t) : term132 _26777 x' P t.
Proof. exact (h1). Qed.
Lemma lem1136467 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (@List.Forall _26777 P t) = (@List.Forall _26777 P t).
Proof. exact (eq_refl (@List.Forall _26777 P t)). Qed.
Lemma lem1136472 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1136473 {_26777 : Type'} (f : _26777 -> Prop) (x : _26777) : (f x) = (@I (_26777 -> Prop) f x).
Proof. exact (@lem1136472 _26777 Prop f x). Qed.
Lemma lem1136475 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (P h) = (@I (_26777 -> Prop) P h).
Proof. exact (@lem1136473 _26777 P h). Qed.
Lemma lem1136476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1136477 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term195 _26777 P h) = (term196 _26777 P h).
Proof. exact (MK_COMB (@lem1136476) (@lem1136475 _26777 P h)). Qed.
Lemma lem1136478 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term51 _26777 h P t) = (term197 _26777 h P t).
Proof. exact (MK_COMB (@lem1136477 _26777 P h) (@lem1136467 _26777 P t)). Qed.
Lemma lem1136479 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1136484 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1136485 {_26777 : Type'} (f : _26777 -> Prop) (x : _26777) : (f x) = (@I (_26777 -> Prop) f x).
Proof. exact (@lem1136484 _26777 Prop f x). Qed.
Lemma lem1136487 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (P x) = (@I (_26777 -> Prop) P x).
Proof. exact (@lem1136485 _26777 P x). Qed.
Lemma lem1136488 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (term198 _26777 P x) = (term199 _26777 P x).
Proof. exact (MK_COMB (@lem1136479) (@lem1136487 _26777 P x)). Qed.
Lemma lem1136503 {_26777 : Type'} (h : _26777) (x : _26777) (t : list _26777) : (term200 _26777 h x t) = (term200 _26777 h x t).
Proof. exact (eq_refl (term200 _26777 h x t)). Qed.
Lemma lem1136504 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term139 _26777 h t P x) = (term201 _26777 h t P x).
Proof. exact (MK_COMB (@lem1136503 _26777 h x t) (@lem1136488 _26777 P x)). Qed.
Lemma lem1136505 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1136506 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term176 _26777 h t P x) = (term202 _26777 h t P x).
Proof. exact (MK_COMB (@lem1136505) (@lem1136504 _26777 h t P x)). Qed.
Lemma lem1136507 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term178 _26777 x h P t) = (term203 _26777 x h P t).
Proof. exact (MK_COMB (@lem1136506 _26777 h t P x) (@lem1136478 _26777 h P t)). Qed.
Lemma lem1136514 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term91 _26777 P t) = (term91 _26777 P t).
Proof. exact (eq_refl (term91 _26777 P t)). Qed.
Lemma lem1136515 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1136520 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1136521 {_26777 : Type'} (f : _26777 -> Prop) (x : _26777) : (f x) = (@I (_26777 -> Prop) f x).
Proof. exact (@lem1136520 _26777 Prop f x). Qed.
Lemma lem1136523 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (P h) = (@I (_26777 -> Prop) P h).
Proof. exact (@lem1136521 _26777 P h). Qed.
Lemma lem1136524 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term198 _26777 P h) = (term199 _26777 P h).
Proof. exact (MK_COMB (@lem1136515) (@lem1136523 _26777 P h)). Qed.
Lemma lem1136525 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1136526 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term204 _26777 P h) = (term205 _26777 P h).
Proof. exact (MK_COMB (@lem1136525) (@lem1136524 _26777 P h)). Qed.
Lemma lem1136527 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term154 _26777 h P t) = (term206 _26777 h P t).
Proof. exact (MK_COMB (@lem1136526 _26777 P h) (@lem1136514 _26777 P t)). Qed.
Lemma lem1136532 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1136533 {_26777 : Type'} (f : _26777 -> Prop) (x : _26777) : (f x) = (@I (_26777 -> Prop) f x).
Proof. exact (@lem1136532 _26777 Prop f x). Qed.
Lemma lem1136535 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (P x) = (@I (_26777 -> Prop) P x).
Proof. exact (@lem1136533 _26777 P x). Qed.
Lemma lem1136554 {_26777 : Type'} (h : _26777) (x : _26777) (t : list _26777) : (term141 _26777 h x t) = (term141 _26777 h x t).
Proof. exact (eq_refl (term141 _26777 h x t)). Qed.
Lemma lem1136555 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term143 _26777 h t P x) = (term207 _26777 h t P x).
Proof. exact (MK_COMB (@lem1136554 _26777 h x t) (@lem1136535 _26777 P x)). Qed.
Lemma lem1136556 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term151 _26777 h t P) = (term208 _26777 h t P).
Proof. exact (fun_ext (fun x : _26777 => @lem1136555 _26777 h t P x)). Qed.
Lemma lem1136557 {_26777 : Type'} : (@all _26777) = (@all _26777).
Proof. exact (eq_refl (@all _26777)). Qed.
Lemma lem1136558 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term152 _26777 h t P) = (term209 _26777 h t P).
Proof. exact (MK_COMB (@lem1136557 _26777) (@lem1136556 _26777 h t P)). Qed.
Lemma lem1136559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1136560 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term160 _26777 h t P) = (term210 _26777 h t P).
Proof. exact (MK_COMB (@lem1136559) (@lem1136558 _26777 h t P)). Qed.
Lemma lem1136561 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term162 _26777 h P t) = (term211 _26777 h P t).
Proof. exact (MK_COMB (@lem1136560 _26777 h t P) (@lem1136527 _26777 h P t)). Qed.
Lemma lem1136562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1136563 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term164 _26777 h P t) = (term212 _26777 h P t).
Proof. exact (MK_COMB (@lem1136562) (@lem1136561 _26777 h P t)). Qed.
Lemma lem1136564 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term191 _26777 x h P t) = (term213 _26777 x h P t).
Proof. exact (MK_COMB (@lem1136563 _26777 h P t) (@lem1136507 _26777 x h P t)). Qed.
Lemma lem1136565 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term191 _26777 x h P t) : term213 _26777 x h P t.
Proof. exact (EQ_MP (@lem1136564 _26777 x h P t) (@lem1136461 _26777 x h P t h1)). Qed.
Lemma lem1136572 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term91 _26777 P t) = (term91 _26777 P t).
Proof. exact (eq_refl (term91 _26777 P t)). Qed.
Lemma lem1136573 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1136578 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1136579 {_26777 : Type'} (f : _26777 -> Prop) (x : _26777) : (f x) = (@I (_26777 -> Prop) f x).
Proof. exact (@lem1136578 _26777 Prop f x). Qed.
Lemma lem1136581 {_26777 : Type'} (P : _26777 -> Prop) (x' : _26777) : (P x') = (@I (_26777 -> Prop) P x').
Proof. exact (@lem1136579 _26777 P x'). Qed.
Lemma lem1136582 {_26777 : Type'} (P : _26777 -> Prop) (x' : _26777) : (term198 _26777 P x') = (term199 _26777 P x').
Proof. exact (MK_COMB (@lem1136573) (@lem1136581 _26777 P x')). Qed.
Lemma lem1136589 {_26777 : Type'} (x' : _26777) (t : list _26777) : (term214 _26777 x' t) = (term214 _26777 x' t).
Proof. exact (eq_refl (term214 _26777 x' t)). Qed.
Lemma lem1136590 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (x' : _26777) : (term78 _26777 t P x') = (term215 _26777 t P x').
Proof. exact (MK_COMB (@lem1136589 _26777 x' t) (@lem1136582 _26777 P x')). Qed.
Lemma lem1136591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1136592 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (x' : _26777) : (term115 _26777 t P x') = (term216 _26777 t P x').
Proof. exact (MK_COMB (@lem1136591) (@lem1136590 _26777 t P x')). Qed.
Lemma lem1136593 {_26777 : Type'} (x' : _26777) (P : _26777 -> Prop) (t : list _26777) : (term117 _26777 x' P t) = (term217 _26777 x' P t).
Proof. exact (MK_COMB (@lem1136592 _26777 t P x') (@lem1136572 _26777 P t)). Qed.
Lemma lem1136598 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (@List.Forall _26777 P t) = (@List.Forall _26777 P t).
Proof. exact (eq_refl (@List.Forall _26777 P t)). Qed.
Lemma lem1136603 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1136604 {_26777 : Type'} (f : _26777 -> Prop) (x : _26777) : (f x) = (@I (_26777 -> Prop) f x).
Proof. exact (@lem1136603 _26777 Prop f x). Qed.
Lemma lem1136606 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (P x) = (@I (_26777 -> Prop) P x).
Proof. exact (@lem1136604 _26777 P x). Qed.
Lemma lem1136615 {_26777 : Type'} (x : _26777) (t : list _26777) : (term218 _26777 x t) = (term218 _26777 x t).
Proof. exact (eq_refl (term218 _26777 x t)). Qed.
Lemma lem1136616 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term79 _26777 t P x) = (term219 _26777 t P x).
Proof. exact (MK_COMB (@lem1136615 _26777 x t) (@lem1136606 _26777 P x)). Qed.
Lemma lem1136617 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term89 _26777 t P) = (term220 _26777 t P).
Proof. exact (fun_ext (fun x : _26777 => @lem1136616 _26777 t P x)). Qed.
Lemma lem1136618 {_26777 : Type'} : (@all _26777) = (@all _26777).
Proof. exact (eq_refl (@all _26777)). Qed.
Lemma lem1136619 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term90 _26777 t P) = (term221 _26777 t P).
Proof. exact (MK_COMB (@lem1136618 _26777) (@lem1136617 _26777 t P)). Qed.
Lemma lem1136620 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1136621 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term97 _26777 t P) = (term222 _26777 t P).
Proof. exact (MK_COMB (@lem1136620) (@lem1136619 _26777 t P)). Qed.
Lemma lem1136622 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term99 _26777 P t) = (term223 _26777 P t).
Proof. exact (MK_COMB (@lem1136621 _26777 t P) (@lem1136598 _26777 P t)). Qed.
Lemma lem1136623 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1136624 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term101 _26777 P t) = (term224 _26777 P t).
Proof. exact (MK_COMB (@lem1136623) (@lem1136622 _26777 P t)). Qed.
Lemma lem1136625 {_26777 : Type'} (x' : _26777) (P : _26777 -> Prop) (t : list _26777) : (term132 _26777 x' P t) = (term225 _26777 x' P t).
Proof. exact (MK_COMB (@lem1136624 _26777 P t) (@lem1136593 _26777 x' P t)). Qed.
Lemma lem1136626 {_26777 : Type'} (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term132 _26777 x' P t) : term225 _26777 x' P t.
Proof. exact (EQ_MP (@lem1136625 _26777 x' P t) (@lem1136462 _26777 x' P t h1)). Qed.
Lemma lem1136627 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term223 _26777 P t) : term223 _26777 P t.
Proof. exact (h1). Qed.
Lemma lem1136628 {_26777 : Type'} (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term217 _26777 x' P t) : term217 _26777 x' P t.
Proof. exact (h1). Qed.
Lemma lem1136630 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term223 _26777 P t) : term221 _26777 t P.
Proof. exact (proj1 (@lem1136627 _26777 P t h1)). Qed.
Lemma lem1136631 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term211 _26777 h P t.
Proof. exact (h1). Qed.
Lemma lem1136632 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : term203 _26777 x h P t.
Proof. exact (h1). Qed.
Lemma lem1136633 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term206 _26777 h P t.
Proof. exact (proj2 (@lem1136631 _26777 h P t h1)). Qed.
Lemma lem1136634 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term209 _26777 h t P.
Proof. exact (proj1 (@lem1136631 _26777 h P t h1)). Qed.
Lemma lem1136637 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : term197 _26777 h P t.
Proof. exact (proj2 (@lem1136632 _26777 x h P t h1)). Qed.
Lemma lem1136638 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : term201 _26777 h t P x.
Proof. exact (proj1 (@lem1136632 _26777 x h P t h1)). Qed.
Lemma lem1136642 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : term41 _26777 h x t.
Proof. exact (proj1 (@lem1136638 _26777 x h P t h1)). Qed.
Lemma lem1136646 {_26777 : Type'} (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term217 _26777 x' P t) : term215 _26777 t P x'.
Proof. exact (proj1 (@lem1136628 _26777 x' P t h1)). Qed.
Lemma lem1136649 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term211 _26777 h P t.
Proof. exact (h1). Qed.
Lemma lem1136650 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : term203 _26777 x h P t.
Proof. exact (h1). Qed.
Lemma lem1136651 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term206 _26777 h P t.
Proof. exact (proj2 (@lem1136649 _26777 h P t h1)). Qed.
Lemma lem1136652 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term209 _26777 h t P.
Proof. exact (proj1 (@lem1136649 _26777 h P t h1)). Qed.
Lemma lem1136655 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : term197 _26777 h P t.
Proof. exact (proj2 (@lem1136650 _26777 x h P t h1)). Qed.
Lemma lem1136656 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : term201 _26777 h t P x.
Proof. exact (proj1 (@lem1136650 _26777 x h P t h1)). Qed.
Lemma lem1136660 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : term41 _26777 h x t.
Proof. exact (proj1 (@lem1136656 _26777 x h P t h1)). Qed.
Lemma lem1136697 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term207 _26777 h t P x) = (term226 _26777 h t P x).
Proof. exact (@lem19699 (term227 _26777 x h) (term228 _26777 x t) (@I (_26777 -> Prop) P x)). Qed.
Lemma lem1136698 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term208 _26777 h t P) = (term229 _26777 h t P).
Proof. exact (fun_ext (fun x : _26777 => @lem1136697 _26777 h t P x)). Qed.
Lemma lem1136699 {_26777 : Type'} : (@all _26777) = (@all _26777).
Proof. exact (eq_refl (@all _26777)). Qed.
Lemma lem1136701 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term209 _26777 h t P) = (term230 _26777 h t P).
Proof. exact (MK_COMB (@lem1136699 _26777) (@lem1136698 _26777 h t P)). Qed.
Lemma lem1136702 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term230 _26777 h t P.
Proof. exact (EQ_MP (@lem1136701 _26777 h t P) (@lem1136634 _26777 h P t h1)). Qed.
Lemma lem1136706 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) (h1 : term199 _26777 P h) : term199 _26777 P h.
Proof. exact (h1). Qed.
Lemma lem1136750 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term91 _26777 P t) : term91 _26777 P t.
Proof. exact (h1). Qed.
Lemma lem1136783 {_26777 : Type'} (x : _26777) (h : _26777) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1136791 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term219 _26777 t P x) = (term219 _26777 t P x).
Proof. exact (eq_refl (term219 _26777 t P x)). Qed.
Lemma lem1136792 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term220 _26777 t P) = (term220 _26777 t P).
Proof. exact (fun_ext (fun x : _26777 => @lem1136791 _26777 t P x)). Qed.
Lemma lem1136793 {_26777 : Type'} : (@all _26777) = (@all _26777).
Proof. exact (eq_refl (@all _26777)). Qed.
Lemma lem1136795 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : (term221 _26777 t P) = (term221 _26777 t P).
Proof. exact (MK_COMB (@lem1136793 _26777) (@lem1136792 _26777 t P)). Qed.
Lemma lem1136796 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term223 _26777 P t) : term221 _26777 t P.
Proof. exact (EQ_MP (@lem1136795 _26777 t P) (@lem1136630 _26777 P t h1)). Qed.
Lemma lem1136816 {_26777 : Type'} (x : _26777) (t : list _26777) (h1 : @List.In _26777 x t) : @List.In _26777 x t.
Proof. exact (h1). Qed.
Lemma lem1136846 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term207 _26777 h t P x) = (term226 _26777 h t P x).
Proof. exact (@lem19699 (term227 _26777 x h) (term228 _26777 x t) (@I (_26777 -> Prop) P x)). Qed.
Lemma lem1136847 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term208 _26777 h t P) = (term229 _26777 h t P).
Proof. exact (fun_ext (fun x : _26777 => @lem1136846 _26777 h t P x)). Qed.
Lemma lem1136848 {_26777 : Type'} : (@all _26777) = (@all _26777).
Proof. exact (eq_refl (@all _26777)). Qed.
Lemma lem1136850 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term209 _26777 h t P) = (term230 _26777 h t P).
Proof. exact (MK_COMB (@lem1136848 _26777) (@lem1136847 _26777 h t P)). Qed.
Lemma lem1136851 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term230 _26777 h t P.
Proof. exact (EQ_MP (@lem1136850 _26777 h t P) (@lem1136652 _26777 h P t h1)). Qed.
Lemma lem1136855 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) (h1 : term199 _26777 P h) : term199 _26777 P h.
Proof. exact (h1). Qed.
Lemma lem1136885 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (x : _26777) : (term207 _26777 h t P x) = (term226 _26777 h t P x).
Proof. exact (@lem19699 (term227 _26777 x h) (term228 _26777 x t) (@I (_26777 -> Prop) P x)). Qed.
Lemma lem1136886 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term208 _26777 h t P) = (term229 _26777 h t P).
Proof. exact (fun_ext (fun x : _26777 => @lem1136885 _26777 h t P x)). Qed.
Lemma lem1136887 {_26777 : Type'} : (@all _26777) = (@all _26777).
Proof. exact (eq_refl (@all _26777)). Qed.
Lemma lem1136889 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) : (term209 _26777 h t P) = (term230 _26777 h t P).
Proof. exact (MK_COMB (@lem1136887 _26777) (@lem1136886 _26777 h t P)). Qed.
Lemma lem1136890 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term230 _26777 h t P.
Proof. exact (EQ_MP (@lem1136889 _26777 h t P) (@lem1136652 _26777 h P t h1)). Qed.
Lemma lem1136922 {_26777 : Type'} (x : _26777) (h : _26777) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1136954 {_26777 : Type'} (_18740 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term231 _26777 h t P _18740.
Proof. exact (@lem1136702 _26777 h P t h1 _18740). Qed.
Lemma lem1136955 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (_18740 : _26777) : (term231 _26777 h t P _18740) = (term226 _26777 h t P _18740).
Proof. exact (eq_refl (term231 _26777 h t P _18740)). Qed.
Lemma lem1136956 {_26777 : Type'} (_18740 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term226 _26777 h t P _18740.
Proof. exact (EQ_MP (@lem1136955 _26777 h t P _18740) (@lem1136954 _26777 _18740 h P t h1)). Qed.
Lemma lem1136966 {_26777 : Type'} (_18744 : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term223 _26777 P t) : term232 _26777 t P _18744.
Proof. exact (@lem1136796 _26777 P t h1 _18744). Qed.
Lemma lem1136967 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (_18744 : _26777) : (term232 _26777 t P _18744) = (term219 _26777 t P _18744).
Proof. exact (eq_refl (term232 _26777 t P _18744)). Qed.
Lemma lem1136969 {_26777 : Type'} (_18745 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term231 _26777 h t P _18745.
Proof. exact (@lem1136851 _26777 h P t h1 _18745). Qed.
Lemma lem1136970 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (_18745 : _26777) : (term231 _26777 h t P _18745) = (term226 _26777 h t P _18745).
Proof. exact (eq_refl (term231 _26777 h t P _18745)). Qed.
Lemma lem1136971 {_26777 : Type'} (_18745 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term226 _26777 h t P _18745.
Proof. exact (EQ_MP (@lem1136970 _26777 h t P _18745) (@lem1136969 _26777 _18745 h P t h1)). Qed.
Lemma lem1136972 {_26777 : Type'} (_18746 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term231 _26777 h t P _18746.
Proof. exact (@lem1136890 _26777 h P t h1 _18746). Qed.
Lemma lem1136973 {_26777 : Type'} (h : _26777) (t : list _26777) (P : _26777 -> Prop) (_18746 : _26777) : (term231 _26777 h t P _18746) = (term226 _26777 h t P _18746).
Proof. exact (eq_refl (term231 _26777 h t P _18746)). Qed.
Lemma lem1136974 {_26777 : Type'} (_18746 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term226 _26777 h t P _18746.
Proof. exact (EQ_MP (@lem1136973 _26777 h t P _18746) (@lem1136972 _26777 _18746 h P t h1)). Qed.
Lemma lem1136992 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) (h1 : term199 _26777 P h) : term199 _26777 P h.
Proof. exact (h1). Qed.
Lemma lem1136998 {_26777 : Type'} (_18740 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term233 _26777 h P _18740.
Proof. exact (proj1 (@lem1136956 _26777 _18740 h P t h1)). Qed.
Lemma lem1137014 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term91 _26777 P t) : term91 _26777 P t.
Proof. exact (h1). Qed.
Lemma lem1137040 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : term199 _26777 P x.
Proof. exact (proj2 (@lem1136638 _26777 x h P t h1)). Qed.
Lemma lem1137042 {_26777 : Type'} (x : _26777) (h : _26777) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1137048 {_26777 : Type'} (_18744 : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term223 _26777 P t) : term219 _26777 t P _18744.
Proof. exact (EQ_MP (@lem1136967 _26777 t P _18744) (@lem1136966 _26777 _18744 P t h1)). Qed.
Lemma lem1137056 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : term199 _26777 P x.
Proof. exact (proj2 (@lem1136638 _26777 x h P t h1)). Qed.
Lemma lem1137058 {_26777 : Type'} (x : _26777) (t : list _26777) (h1 : @List.In _26777 x t) : @List.In _26777 x t.
Proof. exact (h1). Qed.
Lemma lem1137066 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) (h1 : term199 _26777 P h) : term199 _26777 P h.
Proof. exact (h1). Qed.
Lemma lem1137072 {_26777 : Type'} (_18745 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term233 _26777 h P _18745.
Proof. exact (proj1 (@lem1136971 _26777 _18745 h P t h1)). Qed.
Lemma lem1137084 {_26777 : Type'} (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term217 _26777 x' P t) : term199 _26777 P x'.
Proof. exact (proj2 (@lem1136646 _26777 x' P t h1)). Qed.
Lemma lem1137098 {_26777 : Type'} (_18746 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term219 _26777 t P _18746.
Proof. exact (proj2 (@lem1136974 _26777 _18746 h P t h1)). Qed.
Lemma lem1137110 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : term199 _26777 P x.
Proof. exact (proj2 (@lem1136656 _26777 x h P t h1)). Qed.
Lemma lem1137112 {_26777 : Type'} (x : _26777) (h : _26777) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1137114 {_26777 : Type'} (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term217 _26777 x' P t) : term91 _26777 P t.
Proof. exact (proj2 (@lem1136628 _26777 x' P t h1)). Qed.
Lemma lem1137197 {_26777 : Type'} (P : _26777 -> Prop) : (term234 _26777 P) = (term234 _26777 P).
Proof. exact (eq_refl (term234 _26777 P)). Qed.
Lemma lem1137198 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) (h : _26777) (h1 : x = h) : (term235 _26777 P x) = (term235 _26777 P h).
Proof. exact (MK_COMB (@lem1137197 _26777 P) (@lem1137042 _26777 x h h1)). Qed.
Lemma lem1137199 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term235 _26777 P h) = (term199 _26777 P h).
Proof. exact (eq_refl (term235 _26777 P h)). Qed.
Lemma lem1137200 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (term236 _26777 P x) = (term236 _26777 P x).
Proof. exact (eq_refl (term236 _26777 P x)). Qed.
Lemma lem1137201 {_26777 : Type'} (x : _26777) (P : _26777 -> Prop) (h : _26777) : ((term235 _26777 P x) = (term235 _26777 P h)) = ((term235 _26777 P x) = (term199 _26777 P h)).
Proof. exact (MK_COMB (@lem1137200 _26777 P x) (@lem1137199 _26777 P h)). Qed.
Lemma lem1137202 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (term235 _26777 P x) = (term199 _26777 P x).
Proof. exact (eq_refl (term235 _26777 P x)). Qed.
Lemma lem1137203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1137204 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (term236 _26777 P x) = (term237 _26777 P x).
Proof. exact (MK_COMB (@lem1137203) (@lem1137202 _26777 P x)). Qed.
Lemma lem1137205 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term199 _26777 P h) = (term199 _26777 P h).
Proof. exact (eq_refl (term199 _26777 P h)). Qed.
Lemma lem1137206 {_26777 : Type'} (x : _26777) (P : _26777 -> Prop) (h : _26777) : ((term235 _26777 P x) = (term199 _26777 P h)) = ((term199 _26777 P x) = (term199 _26777 P h)).
Proof. exact (MK_COMB (@lem1137204 _26777 P x) (@lem1137205 _26777 P h)). Qed.
Lemma lem1137207 {_26777 : Type'} (x : _26777) (P : _26777 -> Prop) (h : _26777) : ((term235 _26777 P x) = (term235 _26777 P h)) = ((term199 _26777 P x) = (term199 _26777 P h)).
Proof. exact (TRANS (@lem1137201 _26777 x P h) (@lem1137206 _26777 x P h)). Qed.
Lemma lem1137208 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) (h : _26777) (h1 : x = h) : (term199 _26777 P x) = (term199 _26777 P h).
Proof. exact (EQ_MP (@lem1137207 _26777 x P h) (@lem1137198 _26777 P x h h1)). Qed.
Lemma lem1137209 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : term199 _26777 P h.
Proof. exact (EQ_MP (@lem1137208 _26777 P x h h2) (@lem1137040 _26777 x h P t h1)). Qed.
Lemma lem1137294 {_26777 : Type'} (P : _26777 -> Prop) : (term234 _26777 P) = (term234 _26777 P).
Proof. exact (eq_refl (term234 _26777 P)). Qed.
Lemma lem1137295 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) (h : _26777) (h1 : x = h) : (term235 _26777 P x) = (term235 _26777 P h).
Proof. exact (MK_COMB (@lem1137294 _26777 P) (@lem1137112 _26777 x h h1)). Qed.
Lemma lem1137296 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term235 _26777 P h) = (term199 _26777 P h).
Proof. exact (eq_refl (term235 _26777 P h)). Qed.
Lemma lem1137297 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (term236 _26777 P x) = (term236 _26777 P x).
Proof. exact (eq_refl (term236 _26777 P x)). Qed.
Lemma lem1137298 {_26777 : Type'} (x : _26777) (P : _26777 -> Prop) (h : _26777) : ((term235 _26777 P x) = (term235 _26777 P h)) = ((term235 _26777 P x) = (term199 _26777 P h)).
Proof. exact (MK_COMB (@lem1137297 _26777 P x) (@lem1137296 _26777 P h)). Qed.
Lemma lem1137299 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (term235 _26777 P x) = (term199 _26777 P x).
Proof. exact (eq_refl (term235 _26777 P x)). Qed.
Lemma lem1137300 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1137301 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (term236 _26777 P x) = (term237 _26777 P x).
Proof. exact (MK_COMB (@lem1137300) (@lem1137299 _26777 P x)). Qed.
Lemma lem1137302 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term199 _26777 P h) = (term199 _26777 P h).
Proof. exact (eq_refl (term199 _26777 P h)). Qed.
Lemma lem1137303 {_26777 : Type'} (x : _26777) (P : _26777 -> Prop) (h : _26777) : ((term235 _26777 P x) = (term199 _26777 P h)) = ((term199 _26777 P x) = (term199 _26777 P h)).
Proof. exact (MK_COMB (@lem1137301 _26777 P x) (@lem1137302 _26777 P h)). Qed.
Lemma lem1137304 {_26777 : Type'} (x : _26777) (P : _26777 -> Prop) (h : _26777) : ((term235 _26777 P x) = (term235 _26777 P h)) = ((term199 _26777 P x) = (term199 _26777 P h)).
Proof. exact (TRANS (@lem1137298 _26777 x P h) (@lem1137303 _26777 x P h)). Qed.
Lemma lem1137305 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) (h : _26777) (h1 : x = h) : (term199 _26777 P x) = (term199 _26777 P h).
Proof. exact (EQ_MP (@lem1137304 _26777 x P h) (@lem1137295 _26777 P x h h1)). Qed.
Lemma lem1137306 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : term199 _26777 P h.
Proof. exact (EQ_MP (@lem1137305 _26777 P x h h2) (@lem1137110 _26777 x h P t h1)). Qed.
Lemma lem1137371 {_26777 : Type'} (x : _26777) : x = x.
Proof. exact (@lem21386 _26777 x). Qed.
Lemma lem1137372 {_26777 : Type'} (x : _26777) : x = x.
Proof. exact (@lem1137371 _26777 x). Qed.
Lemma lem1137373 {_26777 : Type'} (h : _26777) : h = h.
Proof. exact (@lem1137372 _26777 h). Qed.
Lemma lem1137374 {_26777 : Type'} (h : _26777) : term238 _26777 h.
Proof. exact (fun h0 : term239 _26777 h => @lem1137373 _26777 h). Qed.
Lemma lem1137376 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137377 {_26777 : Type'} (h : _26777) : (term238 _26777 h) = (h = h).
Proof. exact (@lem1137376 (h = h)). Qed.
Lemma lem1137378 {_26777 : Type'} (h : _26777) : h = h.
Proof. exact (EQ_MP (@lem1137377 _26777 h) (@lem1137374 _26777 h)). Qed.
Lemma lem1137384 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1137385 {_26777 : Type'} (P : _26777 -> Prop) (_18740 : _26777) (h : _26777) : (term233 _26777 h P _18740) = (term241 _26777 P _18740 h).
Proof. exact (@lem1137384 (@I (_26777 -> Prop) P _18740) (term227 _26777 _18740 h)). Qed.
Lemma lem1137393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1137394 {_26777 : Type'} (P : _26777 -> Prop) (_18740 : _26777) (h : _26777) : (term242 _26777 h P _18740) = (term243 _26777 P _18740 h).
Proof. exact (MK_COMB (@lem1137393) (@lem1137385 _26777 P _18740 h)). Qed.
Lemma lem1137402 {_26777 : Type'} (P : _26777 -> Prop) (_18740 : _26777) (h : _26777) : (term241 _26777 P _18740 h) = (term241 _26777 P _18740 h).
Proof. exact (eq_refl (term241 _26777 P _18740 h)). Qed.
Lemma lem1137403 {_26777 : Type'} (P : _26777 -> Prop) (_18740 : _26777) (h : _26777) : ((term233 _26777 h P _18740) = (term241 _26777 P _18740 h)) = ((term241 _26777 P _18740 h) = (term241 _26777 P _18740 h)).
Proof. exact (MK_COMB (@lem1137394 _26777 P _18740 h) (@lem1137402 _26777 P _18740 h)). Qed.
Lemma lem1137405 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1137406 (x : Prop) : (x = x) = True.
Proof. exact (@lem1137405 Prop x). Qed.
Lemma lem1137407 {_26777 : Type'} (P : _26777 -> Prop) (_18740 : _26777) (h : _26777) : ((term241 _26777 P _18740 h) = (term241 _26777 P _18740 h)) = True.
Proof. exact (@lem1137406 (term241 _26777 P _18740 h)). Qed.
Lemma lem1137408 {_26777 : Type'} (P : _26777 -> Prop) (_18740 : _26777) (h : _26777) : ((term233 _26777 h P _18740) = (term241 _26777 P _18740 h)) = True.
Proof. exact (TRANS (@lem1137403 _26777 P _18740 h) (@lem1137407 _26777 P _18740 h)). Qed.
Lemma lem1137409 {_26777 : Type'} (P : _26777 -> Prop) (_18740 : _26777) (h : _26777) : True = ((term233 _26777 h P _18740) = (term241 _26777 P _18740 h)).
Proof. exact (SYM (@lem1137408 _26777 P _18740 h)). Qed.
Lemma lem1137410 {_26777 : Type'} (P : _26777 -> Prop) (_18740 : _26777) (h : _26777) : (term233 _26777 h P _18740) = (term241 _26777 P _18740 h).
Proof. exact (EQ_MP (@lem1137409 _26777 P _18740 h) (@lem0)). Qed.
Lemma lem1137411 {_26777 : Type'} (_18740 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term241 _26777 P _18740 h.
Proof. exact (EQ_MP (@lem1137410 _26777 P _18740 h) (@lem1136998 _26777 _18740 h P t h1)). Qed.
Lemma lem1137413 (b : Prop) (a : Prop) : (a \/ b) = (term244 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1137414 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (_18740 : _26777) : (term241 _26777 P _18740 h) = (term245 _26777 h P _18740).
Proof. exact (@lem1137413 (term227 _26777 _18740 h) (@I (_26777 -> Prop) P _18740)). Qed.
Lemma lem1137416 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1137417 {_26777 : Type'} (_18740 : _26777) (h : _26777) : (term246 _26777 _18740 h) = (_18740 = h).
Proof. exact (@lem1137416 (_18740 = h)). Qed.
Lemma lem1137418 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1137419 {_26777 : Type'} (_18740 : _26777) (h : _26777) : (term247 _26777 _18740 h) = (term248 _26777 _18740 h).
Proof. exact (MK_COMB (@lem1137418) (@lem1137417 _26777 _18740 h)). Qed.
Lemma lem1137420 {_26777 : Type'} (P : _26777 -> Prop) (_18740 : _26777) : (@I (_26777 -> Prop) P _18740) = (@I (_26777 -> Prop) P _18740).
Proof. exact (eq_refl (@I (_26777 -> Prop) P _18740)). Qed.
Lemma lem1137421 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (_18740 : _26777) : (term245 _26777 h P _18740) = (term249 _26777 h P _18740).
Proof. exact (MK_COMB (@lem1137419 _26777 _18740 h) (@lem1137420 _26777 P _18740)). Qed.
Lemma lem1137422 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (_18740 : _26777) : (term241 _26777 P _18740 h) = (term249 _26777 h P _18740).
Proof. exact (TRANS (@lem1137414 _26777 h P _18740) (@lem1137421 _26777 h P _18740)). Qed.
Lemma lem1137425 {_26777 : Type'} (_18740 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term249 _26777 h P _18740.
Proof. exact (EQ_MP (@lem1137422 _26777 h P _18740) (@lem1137411 _26777 _18740 h P t h1)). Qed.
Lemma lem1137426 {_26777 : Type'} (_18740 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term249 _26777 h P _18740.
Proof. exact (@lem1137425 _26777 _18740 h P t h1). Qed.
Lemma lem1137427 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term250 _26777 P h.
Proof. exact (@lem1137426 _26777 h h P t h1). Qed.
Lemma lem1137430 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : @I (_26777 -> Prop) P h.
Proof. exact (@lem1137427 _26777 h P t h1 (@lem1137378 _26777 h)). Qed.
Lemma lem1137431 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term251 _26777 P h.
Proof. exact (fun h0 : term199 _26777 P h => @lem1137430 _26777 h P t h1). Qed.
Lemma lem1137433 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137434 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term251 _26777 P h) = (@I (_26777 -> Prop) P h).
Proof. exact (@lem1137433 (@I (_26777 -> Prop) P h)). Qed.
Lemma lem1137435 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : @I (_26777 -> Prop) P h.
Proof. exact (EQ_MP (@lem1137434 _26777 P h) (@lem1137431 _26777 h P t h1)). Qed.
Lemma lem1137438 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1137440 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term199 _26777 P h) = (term252 _26777 P h).
Proof. exact (@lem1137438 (@I (_26777 -> Prop) P h)). Qed.
Lemma lem1137443 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) (h1 : term199 _26777 P h) : term252 _26777 P h.
Proof. exact (EQ_MP (@lem1137440 _26777 P h) (@lem1136992 _26777 P h h1)). Qed.
Lemma lem1137446 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : False.
Proof. exact (@lem1137443 _26777 P h h1 (@lem1137435 _26777 h P t h2)). Qed.
Lemma lem1137447 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : term253.
Proof. exact (fun h0 : ~ False => @lem1137446 _26777 h P t h1 h2). Qed.
Lemma lem1137449 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137450 : term253 = False.
Proof. exact (@lem1137449 False). Qed.
Lemma lem1137451 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : False.
Proof. exact (EQ_MP (@lem1137450) (@lem1137447 _26777 h P t h1 h2)). Qed.
Lemma lem1137516 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term223 _26777 P t) : @List.Forall _26777 P t.
Proof. exact (proj2 (@lem1136627 _26777 P t h1)). Qed.
Lemma lem1137517 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term223 _26777 P t) : term254 _26777 P t.
Proof. exact (fun h0 : term91 _26777 P t => @lem1137516 _26777 P t h1). Qed.
Lemma lem1137519 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137520 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term254 _26777 P t) = (@List.Forall _26777 P t).
Proof. exact (@lem1137519 (@List.Forall _26777 P t)). Qed.
Lemma lem1137521 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term223 _26777 P t) : @List.Forall _26777 P t.
Proof. exact (EQ_MP (@lem1137520 _26777 P t) (@lem1137517 _26777 P t h1)). Qed.
Lemma lem1137524 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1137526 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term91 _26777 P t) = (term255 _26777 P t).
Proof. exact (@lem1137524 (@List.Forall _26777 P t)). Qed.
Lemma lem1137529 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term91 _26777 P t) : term255 _26777 P t.
Proof. exact (EQ_MP (@lem1137526 _26777 P t) (@lem1137014 _26777 P t h1)). Qed.
Lemma lem1137532 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term91 _26777 P t) (h2 : term223 _26777 P t) : False.
Proof. exact (@lem1137529 _26777 P t h1 (@lem1137521 _26777 P t h2)). Qed.
Lemma lem1137533 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term91 _26777 P t) (h2 : term223 _26777 P t) : term253.
Proof. exact (fun h0 : ~ False => @lem1137532 _26777 P t h1 h2). Qed.
Lemma lem1137535 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137536 : term253 = False.
Proof. exact (@lem1137535 False). Qed.
Lemma lem1137537 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term91 _26777 P t) (h2 : term223 _26777 P t) : False.
Proof. exact (EQ_MP (@lem1137536) (@lem1137533 _26777 P t h1 h2)). Qed.
Lemma lem1137539 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : @I (_26777 -> Prop) P h.
Proof. exact (proj1 (@lem1136637 _26777 x h P t h1)). Qed.
Lemma lem1137540 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : term251 _26777 P h.
Proof. exact (fun h0 : term199 _26777 P h => @lem1137539 _26777 x h P t h1). Qed.
Lemma lem1137542 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137543 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term251 _26777 P h) = (@I (_26777 -> Prop) P h).
Proof. exact (@lem1137542 (@I (_26777 -> Prop) P h)). Qed.
Lemma lem1137544 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : @I (_26777 -> Prop) P h.
Proof. exact (EQ_MP (@lem1137543 _26777 P h) (@lem1137540 _26777 x h P t h1)). Qed.
Lemma lem1137547 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1137549 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term199 _26777 P h) = (term252 _26777 P h).
Proof. exact (@lem1137547 (@I (_26777 -> Prop) P h)). Qed.
Lemma lem1137552 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : term252 _26777 P h.
Proof. exact (EQ_MP (@lem1137549 _26777 P h) (@lem1137209 _26777 P t x h h1 h2)). Qed.
Lemma lem1137555 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : False.
Proof. exact (@lem1137552 _26777 P t x h h1 h2 (@lem1137544 _26777 x h P t h1)). Qed.
Lemma lem1137556 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : term253.
Proof. exact (fun h0 : ~ False => @lem1137555 _26777 P t x h h1 h2). Qed.
Lemma lem1137558 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137559 : term253 = False.
Proof. exact (@lem1137558 False). Qed.
Lemma lem1137562 {_26777 : Type'} (x : _26777) (t : list _26777) (h1 : @List.In _26777 x t) : @List.In _26777 x t.
Proof. exact (h1). Qed.
Lemma lem1137563 {_26777 : Type'} (x : _26777) (t : list _26777) (h1 : @List.In _26777 x t) : term256 _26777 x t.
Proof. exact (fun h0 : term228 _26777 x t => @lem1137562 _26777 x t h1). Qed.
Lemma lem1137565 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137566 {_26777 : Type'} (x : _26777) (t : list _26777) : (term256 _26777 x t) = (@List.In _26777 x t).
Proof. exact (@lem1137565 (@List.In _26777 x t)). Qed.
Lemma lem1137567 {_26777 : Type'} (x : _26777) (t : list _26777) (h1 : @List.In _26777 x t) : @List.In _26777 x t.
Proof. exact (EQ_MP (@lem1137566 _26777 x t) (@lem1137563 _26777 x t h1)). Qed.
Lemma lem1137573 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1137574 {_26777 : Type'} (P : _26777 -> Prop) (_18744 : _26777) (t : list _26777) : (term219 _26777 t P _18744) = (term257 _26777 P _18744 t).
Proof. exact (@lem1137573 (@I (_26777 -> Prop) P _18744) (term228 _26777 _18744 t)). Qed.
Lemma lem1137580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1137581 {_26777 : Type'} (P : _26777 -> Prop) (_18744 : _26777) (t : list _26777) : (term258 _26777 t P _18744) = (term259 _26777 P _18744 t).
Proof. exact (MK_COMB (@lem1137580) (@lem1137574 _26777 P _18744 t)). Qed.
Lemma lem1137587 {_26777 : Type'} (P : _26777 -> Prop) (_18744 : _26777) (t : list _26777) : (term257 _26777 P _18744 t) = (term257 _26777 P _18744 t).
Proof. exact (eq_refl (term257 _26777 P _18744 t)). Qed.
Lemma lem1137588 {_26777 : Type'} (P : _26777 -> Prop) (_18744 : _26777) (t : list _26777) : ((term219 _26777 t P _18744) = (term257 _26777 P _18744 t)) = ((term257 _26777 P _18744 t) = (term257 _26777 P _18744 t)).
Proof. exact (MK_COMB (@lem1137581 _26777 P _18744 t) (@lem1137587 _26777 P _18744 t)). Qed.
Lemma lem1137590 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1137591 (x : Prop) : (x = x) = True.
Proof. exact (@lem1137590 Prop x). Qed.
Lemma lem1137592 {_26777 : Type'} (P : _26777 -> Prop) (_18744 : _26777) (t : list _26777) : ((term257 _26777 P _18744 t) = (term257 _26777 P _18744 t)) = True.
Proof. exact (@lem1137591 (term257 _26777 P _18744 t)). Qed.
Lemma lem1137593 {_26777 : Type'} (P : _26777 -> Prop) (_18744 : _26777) (t : list _26777) : ((term219 _26777 t P _18744) = (term257 _26777 P _18744 t)) = True.
Proof. exact (TRANS (@lem1137588 _26777 P _18744 t) (@lem1137592 _26777 P _18744 t)). Qed.
Lemma lem1137594 {_26777 : Type'} (P : _26777 -> Prop) (_18744 : _26777) (t : list _26777) : True = ((term219 _26777 t P _18744) = (term257 _26777 P _18744 t)).
Proof. exact (SYM (@lem1137593 _26777 P _18744 t)). Qed.
Lemma lem1137595 {_26777 : Type'} (P : _26777 -> Prop) (_18744 : _26777) (t : list _26777) : (term219 _26777 t P _18744) = (term257 _26777 P _18744 t).
Proof. exact (EQ_MP (@lem1137594 _26777 P _18744 t) (@lem0)). Qed.
Lemma lem1137596 {_26777 : Type'} (_18744 : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term223 _26777 P t) : term257 _26777 P _18744 t.
Proof. exact (EQ_MP (@lem1137595 _26777 P _18744 t) (@lem1137048 _26777 _18744 P t h1)). Qed.
Lemma lem1137598 (b : Prop) (a : Prop) : (a \/ b) = (term244 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1137599 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (_18744 : _26777) : (term257 _26777 P _18744 t) = (term260 _26777 t P _18744).
Proof. exact (@lem1137598 (term228 _26777 _18744 t) (@I (_26777 -> Prop) P _18744)). Qed.
Lemma lem1137601 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1137602 {_26777 : Type'} (_18744 : _26777) (t : list _26777) : (term261 _26777 _18744 t) = (@List.In _26777 _18744 t).
Proof. exact (@lem1137601 (@List.In _26777 _18744 t)). Qed.
Lemma lem1137603 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1137604 {_26777 : Type'} (_18744 : _26777) (t : list _26777) : (term262 _26777 _18744 t) = (term263 _26777 _18744 t).
Proof. exact (MK_COMB (@lem1137603) (@lem1137602 _26777 _18744 t)). Qed.
Lemma lem1137605 {_26777 : Type'} (P : _26777 -> Prop) (_18744 : _26777) : (@I (_26777 -> Prop) P _18744) = (@I (_26777 -> Prop) P _18744).
Proof. exact (eq_refl (@I (_26777 -> Prop) P _18744)). Qed.
Lemma lem1137606 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (_18744 : _26777) : (term260 _26777 t P _18744) = (term264 _26777 t P _18744).
Proof. exact (MK_COMB (@lem1137604 _26777 _18744 t) (@lem1137605 _26777 P _18744)). Qed.
Lemma lem1137607 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (_18744 : _26777) : (term257 _26777 P _18744 t) = (term264 _26777 t P _18744).
Proof. exact (TRANS (@lem1137599 _26777 t P _18744) (@lem1137606 _26777 t P _18744)). Qed.
Lemma lem1137610 {_26777 : Type'} (_18744 : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term223 _26777 P t) : term264 _26777 t P _18744.
Proof. exact (EQ_MP (@lem1137607 _26777 t P _18744) (@lem1137596 _26777 _18744 P t h1)). Qed.
Lemma lem1137611 {_26777 : Type'} (_18744 : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term223 _26777 P t) : term264 _26777 t P _18744.
Proof. exact (@lem1137610 _26777 _18744 P t h1). Qed.
Lemma lem1137612 {_26777 : Type'} (x : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term223 _26777 P t) : term264 _26777 t P x.
Proof. exact (@lem1137611 _26777 x P t h1). Qed.
Lemma lem1137615 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) (t : list _26777) (h1 : term223 _26777 P t) (h2 : @List.In _26777 x t) : @I (_26777 -> Prop) P x.
Proof. exact (@lem1137612 _26777 x P t h1 (@lem1137567 _26777 x t h2)). Qed.
Lemma lem1137616 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) (t : list _26777) (h1 : term223 _26777 P t) (h2 : @List.In _26777 x t) : term251 _26777 P x.
Proof. exact (fun h0 : term199 _26777 P x => @lem1137615 _26777 P x t h1 h2). Qed.
Lemma lem1137618 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137619 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (term251 _26777 P x) = (@I (_26777 -> Prop) P x).
Proof. exact (@lem1137618 (@I (_26777 -> Prop) P x)). Qed.
Lemma lem1137620 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) (t : list _26777) (h1 : term223 _26777 P t) (h2 : @List.In _26777 x t) : @I (_26777 -> Prop) P x.
Proof. exact (EQ_MP (@lem1137619 _26777 P x) (@lem1137616 _26777 P x t h1 h2)). Qed.
Lemma lem1137623 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1137625 {_26777 : Type'} (P : _26777 -> Prop) (x : _26777) : (term199 _26777 P x) = (term252 _26777 P x).
Proof. exact (@lem1137623 (@I (_26777 -> Prop) P x)). Qed.
Lemma lem1137628 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : term252 _26777 P x.
Proof. exact (EQ_MP (@lem1137625 _26777 P x) (@lem1137056 _26777 x h P t h1)). Qed.
Lemma lem1137631 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (x : _26777) (t : list _26777) (h1 : term223 _26777 P t) (h2 : term203 _26777 x h P t) (h3 : @List.In _26777 x t) : False.
Proof. exact (@lem1137628 _26777 x h P t h2 (@lem1137620 _26777 P x t h1 h3)). Qed.
Lemma lem1137632 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (x : _26777) (t : list _26777) (h1 : term223 _26777 P t) (h2 : term203 _26777 x h P t) (h3 : @List.In _26777 x t) : term253.
Proof. exact (fun h0 : ~ False => @lem1137631 _26777 h P x t h1 h2 h3). Qed.
Lemma lem1137634 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137635 : term253 = False.
Proof. exact (@lem1137634 False). Qed.
Lemma lem1137636 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (x : _26777) (t : list _26777) (h1 : term223 _26777 P t) (h2 : term203 _26777 x h P t) (h3 : @List.In _26777 x t) : False.
Proof. exact (EQ_MP (@lem1137635) (@lem1137632 _26777 h P x t h1 h2 h3)). Qed.
Lemma lem1137701 {_26777 : Type'} (x : _26777) : x = x.
Proof. exact (@lem21386 _26777 x). Qed.
Lemma lem1137702 {_26777 : Type'} (x : _26777) : x = x.
Proof. exact (@lem1137701 _26777 x). Qed.
Lemma lem1137703 {_26777 : Type'} (h : _26777) : h = h.
Proof. exact (@lem1137702 _26777 h). Qed.
Lemma lem1137704 {_26777 : Type'} (h : _26777) : term238 _26777 h.
Proof. exact (fun h0 : term239 _26777 h => @lem1137703 _26777 h). Qed.
Lemma lem1137706 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137707 {_26777 : Type'} (h : _26777) : (term238 _26777 h) = (h = h).
Proof. exact (@lem1137706 (h = h)). Qed.
Lemma lem1137708 {_26777 : Type'} (h : _26777) : h = h.
Proof. exact (EQ_MP (@lem1137707 _26777 h) (@lem1137704 _26777 h)). Qed.
Lemma lem1137714 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1137715 {_26777 : Type'} (P : _26777 -> Prop) (_18745 : _26777) (h : _26777) : (term233 _26777 h P _18745) = (term241 _26777 P _18745 h).
Proof. exact (@lem1137714 (@I (_26777 -> Prop) P _18745) (term227 _26777 _18745 h)). Qed.
Lemma lem1137723 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1137724 {_26777 : Type'} (P : _26777 -> Prop) (_18745 : _26777) (h : _26777) : (term242 _26777 h P _18745) = (term243 _26777 P _18745 h).
Proof. exact (MK_COMB (@lem1137723) (@lem1137715 _26777 P _18745 h)). Qed.
Lemma lem1137732 {_26777 : Type'} (P : _26777 -> Prop) (_18745 : _26777) (h : _26777) : (term241 _26777 P _18745 h) = (term241 _26777 P _18745 h).
Proof. exact (eq_refl (term241 _26777 P _18745 h)). Qed.
Lemma lem1137733 {_26777 : Type'} (P : _26777 -> Prop) (_18745 : _26777) (h : _26777) : ((term233 _26777 h P _18745) = (term241 _26777 P _18745 h)) = ((term241 _26777 P _18745 h) = (term241 _26777 P _18745 h)).
Proof. exact (MK_COMB (@lem1137724 _26777 P _18745 h) (@lem1137732 _26777 P _18745 h)). Qed.
Lemma lem1137735 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1137736 (x : Prop) : (x = x) = True.
Proof. exact (@lem1137735 Prop x). Qed.
Lemma lem1137737 {_26777 : Type'} (P : _26777 -> Prop) (_18745 : _26777) (h : _26777) : ((term241 _26777 P _18745 h) = (term241 _26777 P _18745 h)) = True.
Proof. exact (@lem1137736 (term241 _26777 P _18745 h)). Qed.
Lemma lem1137738 {_26777 : Type'} (P : _26777 -> Prop) (_18745 : _26777) (h : _26777) : ((term233 _26777 h P _18745) = (term241 _26777 P _18745 h)) = True.
Proof. exact (TRANS (@lem1137733 _26777 P _18745 h) (@lem1137737 _26777 P _18745 h)). Qed.
Lemma lem1137739 {_26777 : Type'} (P : _26777 -> Prop) (_18745 : _26777) (h : _26777) : True = ((term233 _26777 h P _18745) = (term241 _26777 P _18745 h)).
Proof. exact (SYM (@lem1137738 _26777 P _18745 h)). Qed.
Lemma lem1137740 {_26777 : Type'} (P : _26777 -> Prop) (_18745 : _26777) (h : _26777) : (term233 _26777 h P _18745) = (term241 _26777 P _18745 h).
Proof. exact (EQ_MP (@lem1137739 _26777 P _18745 h) (@lem0)). Qed.
Lemma lem1137741 {_26777 : Type'} (_18745 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term241 _26777 P _18745 h.
Proof. exact (EQ_MP (@lem1137740 _26777 P _18745 h) (@lem1137072 _26777 _18745 h P t h1)). Qed.
Lemma lem1137743 (b : Prop) (a : Prop) : (a \/ b) = (term244 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1137744 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (_18745 : _26777) : (term241 _26777 P _18745 h) = (term245 _26777 h P _18745).
Proof. exact (@lem1137743 (term227 _26777 _18745 h) (@I (_26777 -> Prop) P _18745)). Qed.
Lemma lem1137746 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1137747 {_26777 : Type'} (_18745 : _26777) (h : _26777) : (term246 _26777 _18745 h) = (_18745 = h).
Proof. exact (@lem1137746 (_18745 = h)). Qed.
Lemma lem1137748 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1137749 {_26777 : Type'} (_18745 : _26777) (h : _26777) : (term247 _26777 _18745 h) = (term248 _26777 _18745 h).
Proof. exact (MK_COMB (@lem1137748) (@lem1137747 _26777 _18745 h)). Qed.
Lemma lem1137750 {_26777 : Type'} (P : _26777 -> Prop) (_18745 : _26777) : (@I (_26777 -> Prop) P _18745) = (@I (_26777 -> Prop) P _18745).
Proof. exact (eq_refl (@I (_26777 -> Prop) P _18745)). Qed.
Lemma lem1137751 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (_18745 : _26777) : (term245 _26777 h P _18745) = (term249 _26777 h P _18745).
Proof. exact (MK_COMB (@lem1137749 _26777 _18745 h) (@lem1137750 _26777 P _18745)). Qed.
Lemma lem1137752 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (_18745 : _26777) : (term241 _26777 P _18745 h) = (term249 _26777 h P _18745).
Proof. exact (TRANS (@lem1137744 _26777 h P _18745) (@lem1137751 _26777 h P _18745)). Qed.
Lemma lem1137755 {_26777 : Type'} (_18745 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term249 _26777 h P _18745.
Proof. exact (EQ_MP (@lem1137752 _26777 h P _18745) (@lem1137741 _26777 _18745 h P t h1)). Qed.
Lemma lem1137756 {_26777 : Type'} (_18745 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term249 _26777 h P _18745.
Proof. exact (@lem1137755 _26777 _18745 h P t h1). Qed.
Lemma lem1137757 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term250 _26777 P h.
Proof. exact (@lem1137756 _26777 h h P t h1). Qed.
Lemma lem1137760 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : @I (_26777 -> Prop) P h.
Proof. exact (@lem1137757 _26777 h P t h1 (@lem1137708 _26777 h)). Qed.
Lemma lem1137761 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term251 _26777 P h.
Proof. exact (fun h0 : term199 _26777 P h => @lem1137760 _26777 h P t h1). Qed.
Lemma lem1137763 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137764 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term251 _26777 P h) = (@I (_26777 -> Prop) P h).
Proof. exact (@lem1137763 (@I (_26777 -> Prop) P h)). Qed.
Lemma lem1137765 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : @I (_26777 -> Prop) P h.
Proof. exact (EQ_MP (@lem1137764 _26777 P h) (@lem1137761 _26777 h P t h1)). Qed.
Lemma lem1137768 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1137770 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term199 _26777 P h) = (term252 _26777 P h).
Proof. exact (@lem1137768 (@I (_26777 -> Prop) P h)). Qed.
Lemma lem1137773 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) (h1 : term199 _26777 P h) : term252 _26777 P h.
Proof. exact (EQ_MP (@lem1137770 _26777 P h) (@lem1137066 _26777 P h h1)). Qed.
Lemma lem1137776 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : False.
Proof. exact (@lem1137773 _26777 P h h1 (@lem1137765 _26777 h P t h2)). Qed.
Lemma lem1137777 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : term253.
Proof. exact (fun h0 : ~ False => @lem1137776 _26777 h P t h1 h2). Qed.
Lemma lem1137779 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137780 : term253 = False.
Proof. exact (@lem1137779 False). Qed.
Lemma lem1137781 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : False.
Proof. exact (EQ_MP (@lem1137780) (@lem1137777 _26777 h P t h1 h2)). Qed.
Lemma lem1137846 {_26777 : Type'} (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term217 _26777 x' P t) : @List.In _26777 x' t.
Proof. exact (proj1 (@lem1136646 _26777 x' P t h1)). Qed.
Lemma lem1137847 {_26777 : Type'} (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term217 _26777 x' P t) : term256 _26777 x' t.
Proof. exact (fun h0 : term228 _26777 x' t => @lem1137846 _26777 x' P t h1). Qed.
Lemma lem1137849 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137850 {_26777 : Type'} (x' : _26777) (t : list _26777) : (term256 _26777 x' t) = (@List.In _26777 x' t).
Proof. exact (@lem1137849 (@List.In _26777 x' t)). Qed.
Lemma lem1137851 {_26777 : Type'} (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term217 _26777 x' P t) : @List.In _26777 x' t.
Proof. exact (EQ_MP (@lem1137850 _26777 x' t) (@lem1137847 _26777 x' P t h1)). Qed.
Lemma lem1137857 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1137858 {_26777 : Type'} (P : _26777 -> Prop) (_18746 : _26777) (t : list _26777) : (term219 _26777 t P _18746) = (term257 _26777 P _18746 t).
Proof. exact (@lem1137857 (@I (_26777 -> Prop) P _18746) (term228 _26777 _18746 t)). Qed.
Lemma lem1137864 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1137865 {_26777 : Type'} (P : _26777 -> Prop) (_18746 : _26777) (t : list _26777) : (term258 _26777 t P _18746) = (term259 _26777 P _18746 t).
Proof. exact (MK_COMB (@lem1137864) (@lem1137858 _26777 P _18746 t)). Qed.
Lemma lem1137871 {_26777 : Type'} (P : _26777 -> Prop) (_18746 : _26777) (t : list _26777) : (term257 _26777 P _18746 t) = (term257 _26777 P _18746 t).
Proof. exact (eq_refl (term257 _26777 P _18746 t)). Qed.
Lemma lem1137872 {_26777 : Type'} (P : _26777 -> Prop) (_18746 : _26777) (t : list _26777) : ((term219 _26777 t P _18746) = (term257 _26777 P _18746 t)) = ((term257 _26777 P _18746 t) = (term257 _26777 P _18746 t)).
Proof. exact (MK_COMB (@lem1137865 _26777 P _18746 t) (@lem1137871 _26777 P _18746 t)). Qed.
Lemma lem1137874 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1137875 (x : Prop) : (x = x) = True.
Proof. exact (@lem1137874 Prop x). Qed.
Lemma lem1137876 {_26777 : Type'} (P : _26777 -> Prop) (_18746 : _26777) (t : list _26777) : ((term257 _26777 P _18746 t) = (term257 _26777 P _18746 t)) = True.
Proof. exact (@lem1137875 (term257 _26777 P _18746 t)). Qed.
Lemma lem1137877 {_26777 : Type'} (P : _26777 -> Prop) (_18746 : _26777) (t : list _26777) : ((term219 _26777 t P _18746) = (term257 _26777 P _18746 t)) = True.
Proof. exact (TRANS (@lem1137872 _26777 P _18746 t) (@lem1137876 _26777 P _18746 t)). Qed.
Lemma lem1137878 {_26777 : Type'} (P : _26777 -> Prop) (_18746 : _26777) (t : list _26777) : True = ((term219 _26777 t P _18746) = (term257 _26777 P _18746 t)).
Proof. exact (SYM (@lem1137877 _26777 P _18746 t)). Qed.
Lemma lem1137879 {_26777 : Type'} (P : _26777 -> Prop) (_18746 : _26777) (t : list _26777) : (term219 _26777 t P _18746) = (term257 _26777 P _18746 t).
Proof. exact (EQ_MP (@lem1137878 _26777 P _18746 t) (@lem0)). Qed.
Lemma lem1137880 {_26777 : Type'} (_18746 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term257 _26777 P _18746 t.
Proof. exact (EQ_MP (@lem1137879 _26777 P _18746 t) (@lem1137098 _26777 _18746 h P t h1)). Qed.
Lemma lem1137882 (b : Prop) (a : Prop) : (a \/ b) = (term244 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1137883 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (_18746 : _26777) : (term257 _26777 P _18746 t) = (term260 _26777 t P _18746).
Proof. exact (@lem1137882 (term228 _26777 _18746 t) (@I (_26777 -> Prop) P _18746)). Qed.
Lemma lem1137885 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1137886 {_26777 : Type'} (_18746 : _26777) (t : list _26777) : (term261 _26777 _18746 t) = (@List.In _26777 _18746 t).
Proof. exact (@lem1137885 (@List.In _26777 _18746 t)). Qed.
Lemma lem1137887 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1137888 {_26777 : Type'} (_18746 : _26777) (t : list _26777) : (term262 _26777 _18746 t) = (term263 _26777 _18746 t).
Proof. exact (MK_COMB (@lem1137887) (@lem1137886 _26777 _18746 t)). Qed.
Lemma lem1137889 {_26777 : Type'} (P : _26777 -> Prop) (_18746 : _26777) : (@I (_26777 -> Prop) P _18746) = (@I (_26777 -> Prop) P _18746).
Proof. exact (eq_refl (@I (_26777 -> Prop) P _18746)). Qed.
Lemma lem1137890 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (_18746 : _26777) : (term260 _26777 t P _18746) = (term264 _26777 t P _18746).
Proof. exact (MK_COMB (@lem1137888 _26777 _18746 t) (@lem1137889 _26777 P _18746)). Qed.
Lemma lem1137891 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) (_18746 : _26777) : (term257 _26777 P _18746 t) = (term264 _26777 t P _18746).
Proof. exact (TRANS (@lem1137883 _26777 t P _18746) (@lem1137890 _26777 t P _18746)). Qed.
Lemma lem1137894 {_26777 : Type'} (_18746 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term264 _26777 t P _18746.
Proof. exact (EQ_MP (@lem1137891 _26777 t P _18746) (@lem1137880 _26777 _18746 h P t h1)). Qed.
Lemma lem1137895 {_26777 : Type'} (_18746 : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term264 _26777 t P _18746.
Proof. exact (@lem1137894 _26777 _18746 h P t h1). Qed.
Lemma lem1137896 {_26777 : Type'} (x' : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) : term264 _26777 t P x'.
Proof. exact (@lem1137895 _26777 x' h P t h1). Qed.
Lemma lem1137899 {_26777 : Type'} (h : _26777) (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) (h2 : term217 _26777 x' P t) : @I (_26777 -> Prop) P x'.
Proof. exact (@lem1137896 _26777 x' h P t h1 (@lem1137851 _26777 x' P t h2)). Qed.
Lemma lem1137900 {_26777 : Type'} (h : _26777) (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) (h2 : term217 _26777 x' P t) : term251 _26777 P x'.
Proof. exact (fun h0 : term199 _26777 P x' => @lem1137899 _26777 h x' P t h1 h2). Qed.
Lemma lem1137902 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137903 {_26777 : Type'} (P : _26777 -> Prop) (x' : _26777) : (term251 _26777 P x') = (@I (_26777 -> Prop) P x').
Proof. exact (@lem1137902 (@I (_26777 -> Prop) P x')). Qed.
Lemma lem1137904 {_26777 : Type'} (h : _26777) (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) (h2 : term217 _26777 x' P t) : @I (_26777 -> Prop) P x'.
Proof. exact (EQ_MP (@lem1137903 _26777 P x') (@lem1137900 _26777 h x' P t h1 h2)). Qed.
Lemma lem1137907 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1137909 {_26777 : Type'} (P : _26777 -> Prop) (x' : _26777) : (term199 _26777 P x') = (term252 _26777 P x').
Proof. exact (@lem1137907 (@I (_26777 -> Prop) P x')). Qed.
Lemma lem1137912 {_26777 : Type'} (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term217 _26777 x' P t) : term252 _26777 P x'.
Proof. exact (EQ_MP (@lem1137909 _26777 P x') (@lem1137084 _26777 x' P t h1)). Qed.
Lemma lem1137915 {_26777 : Type'} (h : _26777) (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) (h2 : term217 _26777 x' P t) : False.
Proof. exact (@lem1137912 _26777 x' P t h2 (@lem1137904 _26777 h x' P t h1 h2)). Qed.
Lemma lem1137916 {_26777 : Type'} (h : _26777) (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) (h2 : term217 _26777 x' P t) : term253.
Proof. exact (fun h0 : ~ False => @lem1137915 _26777 h x' P t h1 h2). Qed.
Lemma lem1137918 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137919 : term253 = False.
Proof. exact (@lem1137918 False). Qed.
Lemma lem1137920 {_26777 : Type'} (h : _26777) (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) (h2 : term217 _26777 x' P t) : False.
Proof. exact (EQ_MP (@lem1137919) (@lem1137916 _26777 h x' P t h1 h2)). Qed.
Lemma lem1137922 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : @I (_26777 -> Prop) P h.
Proof. exact (proj1 (@lem1136655 _26777 x h P t h1)). Qed.
Lemma lem1137923 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : term251 _26777 P h.
Proof. exact (fun h0 : term199 _26777 P h => @lem1137922 _26777 x h P t h1). Qed.
Lemma lem1137925 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137926 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term251 _26777 P h) = (@I (_26777 -> Prop) P h).
Proof. exact (@lem1137925 (@I (_26777 -> Prop) P h)). Qed.
Lemma lem1137927 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : @I (_26777 -> Prop) P h.
Proof. exact (EQ_MP (@lem1137926 _26777 P h) (@lem1137923 _26777 x h P t h1)). Qed.
Lemma lem1137930 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1137932 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : (term199 _26777 P h) = (term252 _26777 P h).
Proof. exact (@lem1137930 (@I (_26777 -> Prop) P h)). Qed.
Lemma lem1137935 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : term252 _26777 P h.
Proof. exact (EQ_MP (@lem1137932 _26777 P h) (@lem1137306 _26777 P t x h h1 h2)). Qed.
Lemma lem1137938 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : False.
Proof. exact (@lem1137935 _26777 P t x h h1 h2 (@lem1137927 _26777 x h P t h1)). Qed.
Lemma lem1137939 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : term253.
Proof. exact (fun h0 : ~ False => @lem1137938 _26777 P t x h h1 h2). Qed.
Lemma lem1137941 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137942 : term253 = False.
Proof. exact (@lem1137941 False). Qed.
Lemma lem1137945 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : @List.Forall _26777 P t.
Proof. exact (proj2 (@lem1136655 _26777 x h P t h1)). Qed.
Lemma lem1137946 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : term254 _26777 P t.
Proof. exact (fun h0 : term91 _26777 P t => @lem1137945 _26777 x h P t h1). Qed.
Lemma lem1137948 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137949 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term254 _26777 P t) = (@List.Forall _26777 P t).
Proof. exact (@lem1137948 (@List.Forall _26777 P t)). Qed.
Lemma lem1137950 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term203 _26777 x h P t) : @List.Forall _26777 P t.
Proof. exact (EQ_MP (@lem1137949 _26777 P t) (@lem1137946 _26777 x h P t h1)). Qed.
Lemma lem1137953 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1137955 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term91 _26777 P t) = (term255 _26777 P t).
Proof. exact (@lem1137953 (@List.Forall _26777 P t)). Qed.
Lemma lem1137958 {_26777 : Type'} (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term217 _26777 x' P t) : term255 _26777 P t.
Proof. exact (EQ_MP (@lem1137955 _26777 P t) (@lem1137114 _26777 x' P t h1)). Qed.
Lemma lem1137961 {_26777 : Type'} (x' : _26777) (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term217 _26777 x' P t) (h2 : term203 _26777 x h P t) : False.
Proof. exact (@lem1137958 _26777 x' P t h1 (@lem1137950 _26777 x h P t h2)). Qed.
Lemma lem1137962 {_26777 : Type'} (x' : _26777) (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term217 _26777 x' P t) (h2 : term203 _26777 x h P t) : term253.
Proof. exact (fun h0 : ~ False => @lem1137961 _26777 x' x h P t h1 h2). Qed.
Lemma lem1137964 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1137965 : term253 = False.
Proof. exact (@lem1137964 False). Qed.
Lemma lem1137966 {_26777 : Type'} (x' : _26777) (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term217 _26777 x' P t) (h2 : term203 _26777 x h P t) : False.
Proof. exact (EQ_MP (@lem1137965) (@lem1137962 _26777 x' x h P t h1 h2)). Qed.
Lemma lem1137967 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1137942) (@lem1137939 _26777 P t x h h1 h2)). Qed.
Lemma lem1137968 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1137559) (@lem1137556 _26777 P t x h h1 h2)). Qed.
Lemma lem1137969 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1137967 _26777 P t x h h1 h2) (fun h3 : False => @lem1137112 _26777 x h h2)). Qed.
Lemma lem1137970 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1137969 _26777 P t x h h1 h2) (@lem1137112 _26777 x h h2)). Qed.
Lemma lem1137971 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : (term199 _26777 P h) = False.
Proof. exact (prop_ext (fun h3 : term199 _26777 P h => @lem1137781 _26777 h P t h1 h2) (fun h3 : False => @lem1137066 _26777 P h h1)). Qed.
Lemma lem1137972 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : False.
Proof. exact (EQ_MP (@lem1137971 _26777 h P t h1 h2) (@lem1137066 _26777 P h h1)). Qed.
Lemma lem1137973 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (x : _26777) (t : list _26777) (h1 : term223 _26777 P t) (h2 : term203 _26777 x h P t) (h3 : @List.In _26777 x t) : (@List.In _26777 x t) = False.
Proof. exact (prop_ext (fun h4 : @List.In _26777 x t => @lem1137636 _26777 h P x t h1 h2 h3) (fun h4 : False => @lem1137058 _26777 x t h3)). Qed.
Lemma lem1137974 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (x : _26777) (t : list _26777) (h1 : term223 _26777 P t) (h2 : term203 _26777 x h P t) (h3 : @List.In _26777 x t) : False.
Proof. exact (EQ_MP (@lem1137973 _26777 h P x t h1 h2 h3) (@lem1137058 _26777 x t h3)). Qed.
Lemma lem1137975 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1137968 _26777 P t x h h1 h2) (fun h3 : False => @lem1137042 _26777 x h h2)). Qed.
Lemma lem1137976 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1137975 _26777 P t x h h1 h2) (@lem1137042 _26777 x h h2)). Qed.
Lemma lem1137977 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term91 _26777 P t) (h2 : term223 _26777 P t) : (term91 _26777 P t) = False.
Proof. exact (prop_ext (fun h3 : term91 _26777 P t => @lem1137537 _26777 P t h1 h2) (fun h3 : False => @lem1137014 _26777 P t h1)). Qed.
Lemma lem1137978 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term91 _26777 P t) (h2 : term223 _26777 P t) : False.
Proof. exact (EQ_MP (@lem1137977 _26777 P t h1 h2) (@lem1137014 _26777 P t h1)). Qed.
Lemma lem1137979 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : (term199 _26777 P h) = False.
Proof. exact (prop_ext (fun h3 : term199 _26777 P h => @lem1137451 _26777 h P t h1 h2) (fun h3 : False => @lem1136992 _26777 P h h1)). Qed.
Lemma lem1137980 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : False.
Proof. exact (EQ_MP (@lem1137979 _26777 h P t h1 h2) (@lem1136992 _26777 P h h1)). Qed.
Lemma lem1137981 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1137970 _26777 P t x h h1 h2) (fun h3 : False => @lem1136922 _26777 x h h2)). Qed.
Lemma lem1137982 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1137981 _26777 P t x h h1 h2) (@lem1136922 _26777 x h h2)). Qed.
Lemma lem1137983 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : (term199 _26777 P h) = False.
Proof. exact (prop_ext (fun h3 : term199 _26777 P h => @lem1137972 _26777 h P t h1 h2) (fun h3 : False => @lem1136855 _26777 P h h1)). Qed.
Lemma lem1137984 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : False.
Proof. exact (EQ_MP (@lem1137983 _26777 h P t h1 h2) (@lem1136855 _26777 P h h1)). Qed.
Lemma lem1137985 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (x : _26777) (t : list _26777) (h1 : term223 _26777 P t) (h2 : term203 _26777 x h P t) (h3 : @List.In _26777 x t) : (@List.In _26777 x t) = False.
Proof. exact (prop_ext (fun h4 : @List.In _26777 x t => @lem1137974 _26777 h P x t h1 h2 h3) (fun h4 : False => @lem1136816 _26777 x t h3)). Qed.
Lemma lem1137986 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (x : _26777) (t : list _26777) (h1 : term223 _26777 P t) (h2 : term203 _26777 x h P t) (h3 : @List.In _26777 x t) : False.
Proof. exact (EQ_MP (@lem1137985 _26777 h P x t h1 h2 h3) (@lem1136816 _26777 x t h3)). Qed.
Lemma lem1137987 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1137976 _26777 P t x h h1 h2) (fun h3 : False => @lem1136783 _26777 x h h2)). Qed.
Lemma lem1137988 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1137987 _26777 P t x h h1 h2) (@lem1136783 _26777 x h h2)). Qed.
Lemma lem1137989 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term91 _26777 P t) (h2 : term223 _26777 P t) : (term91 _26777 P t) = False.
Proof. exact (prop_ext (fun h3 : term91 _26777 P t => @lem1137978 _26777 P t h1 h2) (fun h3 : False => @lem1136750 _26777 P t h1)). Qed.
Lemma lem1137990 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term91 _26777 P t) (h2 : term223 _26777 P t) : False.
Proof. exact (EQ_MP (@lem1137989 _26777 P t h1 h2) (@lem1136750 _26777 P t h1)). Qed.
Lemma lem1137991 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : (term199 _26777 P h) = False.
Proof. exact (prop_ext (fun h3 : term199 _26777 P h => @lem1137980 _26777 h P t h1 h2) (fun h3 : False => @lem1136706 _26777 P h h1)). Qed.
Lemma lem1137992 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : False.
Proof. exact (EQ_MP (@lem1137991 _26777 h P t h1 h2) (@lem1136706 _26777 P h h1)). Qed.
Lemma lem1137993 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1137982 _26777 P t x h h1 h2) (fun h3 : False => @lem1136922 _26777 x h h2)). Qed.
Lemma lem1137994 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1137993 _26777 P t x h h1 h2) (@lem1136922 _26777 x h h2)). Qed.
Lemma lem1137995 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : (term199 _26777 P h) = False.
Proof. exact (prop_ext (fun h3 : term199 _26777 P h => @lem1137984 _26777 h P t h1 h2) (fun h3 : False => @lem1136855 _26777 P h h1)). Qed.
Lemma lem1137996 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : False.
Proof. exact (EQ_MP (@lem1137995 _26777 h P t h1 h2) (@lem1136855 _26777 P h h1)). Qed.
Lemma lem1137997 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (x : _26777) (t : list _26777) (h1 : term223 _26777 P t) (h2 : term203 _26777 x h P t) (h3 : @List.In _26777 x t) : (@List.In _26777 x t) = False.
Proof. exact (prop_ext (fun h4 : @List.In _26777 x t => @lem1137986 _26777 h P x t h1 h2 h3) (fun h4 : False => @lem1136816 _26777 x t h3)). Qed.
Lemma lem1137998 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (x : _26777) (t : list _26777) (h1 : term223 _26777 P t) (h2 : term203 _26777 x h P t) (h3 : @List.In _26777 x t) : False.
Proof. exact (EQ_MP (@lem1137997 _26777 h P x t h1 h2 h3) (@lem1136816 _26777 x t h3)). Qed.
Lemma lem1137999 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1137988 _26777 P t x h h1 h2) (fun h3 : False => @lem1136783 _26777 x h h2)). Qed.
Lemma lem1138000 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (x : _26777) (h : _26777) (h1 : term203 _26777 x h P t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1137999 _26777 P t x h h1 h2) (@lem1136783 _26777 x h h2)). Qed.
Lemma lem1138001 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term91 _26777 P t) (h2 : term223 _26777 P t) : (term91 _26777 P t) = False.
Proof. exact (prop_ext (fun h3 : term91 _26777 P t => @lem1137990 _26777 P t h1 h2) (fun h3 : False => @lem1136750 _26777 P t h1)). Qed.
Lemma lem1138002 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h1 : term91 _26777 P t) (h2 : term223 _26777 P t) : False.
Proof. exact (EQ_MP (@lem1138001 _26777 P t h1 h2) (@lem1136750 _26777 P t h1)). Qed.
Lemma lem1138003 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : (term199 _26777 P h) = False.
Proof. exact (prop_ext (fun h3 : term199 _26777 P h => @lem1137992 _26777 h P t h1 h2) (fun h3 : False => @lem1136706 _26777 P h h1)). Qed.
Lemma lem1138004 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term199 _26777 P h) (h2 : term211 _26777 h P t) : False.
Proof. exact (EQ_MP (@lem1138003 _26777 h P t h1 h2) (@lem1136706 _26777 P h h1)). Qed.
Lemma lem1138005 {_26777 : Type'} (x' : _26777) (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term217 _26777 x' P t) (h2 : term203 _26777 x h P t) : False.
Proof. exact (or_elim (@lem1136660 _26777 x h P t h2) (fun h0 : x = h => @lem1137994 _26777 P t x h h2 h0) (fun h0 : @List.In _26777 x t => @lem1137966 _26777 x' x h P t h1 h2)). Qed.
Lemma lem1138006 {_26777 : Type'} (h : _26777) (x' : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term211 _26777 h P t) (h2 : term217 _26777 x' P t) : False.
Proof. exact (or_elim (@lem1136651 _26777 h P t h1) (fun h0 : term199 _26777 P h => @lem1137996 _26777 h P t h0 h1) (fun h0 : term91 _26777 P t => @lem1137920 _26777 h x' P t h1 h2)). Qed.
Lemma lem1138007 {_26777 : Type'} (x' : _26777) (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term217 _26777 x' P t) (h2 : term191 _26777 x h P t) : False.
Proof. exact (or_elim (@lem1136565 _26777 x h P t h2) (fun h0 : term211 _26777 h P t => @lem1138006 _26777 h x' P t h0 h1) (fun h0 : term203 _26777 x h P t => @lem1138005 _26777 x' x h P t h1 h0)). Qed.
Lemma lem1138008 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term223 _26777 P t) (h2 : term203 _26777 x h P t) : False.
Proof. exact (or_elim (@lem1136642 _26777 x h P t h2) (fun h0 : x = h => @lem1138000 _26777 P t x h h2 h0) (fun h0 : @List.In _26777 x t => @lem1137998 _26777 h P x t h1 h2 h0)). Qed.
Lemma lem1138009 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term223 _26777 P t) (h2 : term211 _26777 h P t) : False.
Proof. exact (or_elim (@lem1136633 _26777 h P t h2) (fun h0 : term199 _26777 P h => @lem1138004 _26777 h P t h0 h2) (fun h0 : term91 _26777 P t => @lem1138002 _26777 P t h0 h1)). Qed.
Lemma lem1138010 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term223 _26777 P t) (h2 : term191 _26777 x h P t) : False.
Proof. exact (or_elim (@lem1136565 _26777 x h P t h2) (fun h0 : term211 _26777 h P t => @lem1138009 _26777 h P t h1 h0) (fun h0 : term203 _26777 x h P t => @lem1138008 _26777 x h P t h1 h0)). Qed.
Lemma lem1138011 {_26777 : Type'} (x' : _26777) (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term132 _26777 x' P t) (h2 : term191 _26777 x h P t) : False.
Proof. exact (or_elim (@lem1136626 _26777 x' P t h1) (fun h0 : term223 _26777 P t => @lem1138010 _26777 x h P t h0 h2) (fun h0 : term217 _26777 x' P t => @lem1138007 _26777 x' x h P t h0 h2)). Qed.
Lemma lem1138012 {_26777 : Type'} (x : _26777) (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : (term8 _26777 t P) = (@List.Forall _26777 P t)) (h2 : term191 _26777 x h P t) : False.
Proof. exact (ex_elim (@lem1136269 _26777 P t h1) (fun x' : _26777 => fun h0 : term134 _26777 P t x' => @lem1138011 _26777 x' x h P t h0 h2)). Qed.
Lemma lem1138013 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term54 _26777 h P t) (h2 : (term8 _26777 t P) = (@List.Forall _26777 P t)) : False.
Proof. exact (ex_elim (@lem1136460 _26777 h P t h1) (fun x : _26777 => fun h0 : term193 _26777 h P t x => @lem1138012 _26777 x h P t h2 h0)). Qed.
Lemma lem1138014 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term54 _26777 h P t) (h2 : (term8 _26777 t P) = (@List.Forall _26777 P t)) : (term54 _26777 h P t) = False.
Proof. exact (prop_ext (fun h3 : term54 _26777 h P t => @lem1138013 _26777 h P t h1 h2) (fun h3 : False => @lem1136098 _26777 h P t h1)). Qed.
Lemma lem1138015 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term54 _26777 h P t) (h2 : (term8 _26777 t P) = (@List.Forall _26777 P t)) : False.
Proof. exact (EQ_MP (@lem1138014 _26777 h P t h1 h2) (@lem1136098 _26777 h P t h1)). Qed.
Lemma lem1138016 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : (term8 _26777 t P) = (@List.Forall _26777 P t)) : term53 _26777 h P t.
Proof. exact (fun h0 : term54 _26777 h P t => @lem1138015 _26777 h P t h0 h1). Qed.
Lemma lem1138017 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : (term8 _26777 t P) = (@List.Forall _26777 P t)) : (term48 _26777 h t P) = (term51 _26777 h P t).
Proof. exact (EQ_MP (@lem1136097 _26777 h P t) (@lem1138016 _26777 h P t h1)). Qed.
Lemma lem1138018 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : term61 _26777 h P t.
Proof. exact (fun h0 : (term8 _26777 t P) = (@List.Forall _26777 P t) => @lem1138017 _26777 h P t h0). Qed.
Lemma lem1138023 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : term65 _26777 P t.
Proof. exact (fun h : _26777 => @lem1138018 _26777 h P t). Qed.
Lemma lem1138028 {_26777 : Type'} (t : list _26777) : term69 _26777 t.
Proof. exact (fun P : _26777 -> Prop => @lem1138023 _26777 P t). Qed.
Lemma lem1138033 {_26777 : Type'} : term73 _26777.
Proof. exact (fun t : list _26777 => @lem1138028 _26777 t). Qed.
Lemma lem1138034 {_26777 : Type'} : term72 _26777.
Proof. exact (EQ_MP (@lem1136092 _26777) (@lem1138033 _26777)). Qed.
Lemma lem1138035 {_26777 : Type'} (t : list _26777) : term265 _26777 t.
Proof. exact (@lem1138034 _26777 t). Qed.
Lemma lem1138036 {_26777 : Type'} (t : list _26777) : (term265 _26777 t) = (term68 _26777 t).
Proof. exact (eq_refl (term265 _26777 t)). Qed.
Lemma lem1138037 {_26777 : Type'} (t : list _26777) : term68 _26777 t.
Proof. exact (EQ_MP (@lem1138036 _26777 t) (@lem1138035 _26777 t)). Qed.
Lemma lem1138038 {_26777 : Type'} (t : list _26777) (P : _26777 -> Prop) : term266 _26777 t P.
Proof. exact (@lem1138037 _26777 t P). Qed.
Lemma lem1138039 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : (term266 _26777 t P) = (term64 _26777 P t).
Proof. exact (eq_refl (term266 _26777 t P)). Qed.
Lemma lem1138040 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) : term64 _26777 P t.
Proof. exact (EQ_MP (@lem1138039 _26777 P t) (@lem1138038 _26777 t P)). Qed.
Lemma lem1138041 {_26777 : Type'} (P : _26777 -> Prop) (t : list _26777) (h : _26777) : term267 _26777 P t h.
Proof. exact (@lem1138040 _26777 P t h). Qed.
Lemma lem1138042 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : (term267 _26777 P t h) = (term55 _26777 h P t).
Proof. exact (eq_refl (term267 _26777 P t h)). Qed.
Lemma lem1138043 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : term55 _26777 h P t.
Proof. exact (EQ_MP (@lem1138042 _26777 h P t) (@lem1138041 _26777 P t h)). Qed.
Lemma lem1138045 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) : term55 _26777 h P t.
Proof. exact (@lem1135938 _26777 h P t (@lem1138043 _26777 h P t)). Qed.
Lemma lem1138046 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : (term8 _26777 t P) = (@List.Forall _26777 P t)) : term53 _26777 h P t.
Proof. exact (@lem1138045 _26777 h P t (@lem1135839 _26777 P t h1)). Qed.
Lemma lem1138047 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term54 _26777 h P t) (h2 : (term8 _26777 t P) = (@List.Forall _26777 P t)) : False.
Proof. exact (@lem1138046 _26777 h P t h2 (@lem1135922 _26777 h P t h1)). Qed.
Lemma lem1138048 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term54 _26777 h P t) (h2 : (term8 _26777 t P) = (@List.Forall _26777 P t)) : (term54 _26777 h P t) = False.
Proof. exact (prop_ext (fun h3 : term54 _26777 h P t => @lem1138047 _26777 h P t h1 h2) (fun h3 : False => @lem1135922 _26777 h P t h1)). Qed.
Lemma lem1138049 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : term54 _26777 h P t) (h2 : (term8 _26777 t P) = (@List.Forall _26777 P t)) : False.
Proof. exact (EQ_MP (@lem1138048 _26777 h P t h1 h2) (@lem1135922 _26777 h P t h1)). Qed.
Lemma lem1138050 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : (term8 _26777 t P) = (@List.Forall _26777 P t)) : term53 _26777 h P t.
Proof. exact (fun h0 : term54 _26777 h P t => @lem1138049 _26777 h P t h0 h1). Qed.
Lemma lem1138051 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : (term8 _26777 t P) = (@List.Forall _26777 P t)) : (term48 _26777 h t P) = (term51 _26777 h P t).
Proof. exact (EQ_MP (@lem1135921 _26777 h P t) (@lem1138050 _26777 h P t h1)). Qed.
Lemma lem1138052 {_26777 : Type'} (h : _26777) (P : _26777 -> Prop) (t : list _26777) (h1 : (term8 _26777 t P) = (@List.Forall _26777 P t)) : (term12 _26777 h t P) = (term13 _26777 P h t).
Proof. exact (EQ_MP (@lem1135917 _26777 P h t) (@lem1138051 _26777 h P t h1)). Qed.
Lemma lem1138053 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) (t : list _26777) : term15 _26777 P h t.
Proof. exact (fun h0 : (term8 _26777 t P) = (@List.Forall _26777 P t) => @lem1138052 _26777 h P t h0). Qed.
Lemma lem1138058 {_26777 : Type'} (P : _26777 -> Prop) (h : _26777) : term19 _26777 P h.
Proof. exact (fun t : list _26777 => @lem1138053 _26777 P h t). Qed.
Lemma lem1138063 {_26777 : Type'} (P : _26777 -> Prop) : term23 _26777 P.
Proof. exact (fun h : _26777 => @lem1138058 _26777 P h). Qed.
Lemma lem1138064 {_26777 : Type'} (P : _26777 -> Prop) : term25 _26777 P.
Proof. exact (conj (@lem1135878 _26777 P) (@lem1138063 _26777 P)). Qed.
Lemma lem1138065 {_26777 : Type'} (P : _26777 -> Prop) : term30 _26777 P.
Proof. exact (@lem1135838 _26777 P (@lem1138064 _26777 P)). Qed.
Lemma lem1138070 {_26777 : Type'} : term268 _26777.
Proof. exact (fun P : _26777 -> Prop => @lem1138065 _26777 P). Qed.
