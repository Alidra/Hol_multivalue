Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_RESTRICT_SET_term_abbrevs.
Require Import CONJ_ASSOC_spec.
Require Import ITERATE_EQ_spec.
Require Import ITERATE_SUPPORT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm21735_spec.
Require Import thm21736_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem5985803 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5985804 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem5985803 _83095 p). Qed.
Lemma lem5985805 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem5985806 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem5985805 _83095 p) (@lem5985804 _83095 p)). Qed.
Lemma lem5985807 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem5985806 _83095 p x). Qed.
Lemma lem5985808 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem5985817 {A B : Type'} (op : type1400 B) : term5 A B op.
Proof. exact (@lem5985778 A B op). Qed.
Lemma lem5985818 {A B : Type'} (op : type1400 B) : (term5 A B op) = (term6 A B op).
Proof. exact (eq_refl (term5 A B op)). Qed.
Lemma lem5985823 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term7 t1 t2 t3) = (term8 t1 t2 t3)) : (term7 t1 t2 t3) = (term8 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem5985824 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term7 t1 t2 t3) = (term8 t1 t2 t3)) : (term8 t1 t2 t3) = (term7 t1 t2 t3).
Proof. exact (SYM (@lem5985823 t1 t2 t3 h1)). Qed.
Lemma lem5985825 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term8 t1 t2 t3) = (term7 t1 t2 t3)) : (term8 t1 t2 t3) = (term7 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem5985826 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term8 t1 t2 t3) = (term7 t1 t2 t3)) : (term7 t1 t2 t3) = (term8 t1 t2 t3).
Proof. exact (SYM (@lem5985825 t1 t2 t3 h1)). Qed.
Lemma lem5985827 (t1 : Prop) (t2 : Prop) (t3 : Prop) : ((term7 t1 t2 t3) = (term8 t1 t2 t3)) = ((term8 t1 t2 t3) = (term7 t1 t2 t3)).
Proof. exact (prop_ext (fun h1 : (term7 t1 t2 t3) = (term8 t1 t2 t3) => @lem5985824 t1 t2 t3 h1) (fun h1 : (term8 t1 t2 t3) = (term7 t1 t2 t3) => @lem5985826 t1 t2 t3 h1)). Qed.
Lemma lem5985828 (t1 : Prop) (t2 : Prop) : (term9 t1 t2) = (term10 t1 t2).
Proof. exact (fun_ext (fun t3 : Prop => @lem5985827 t1 t2 t3)). Qed.
Lemma lem5985829 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem5985830 (t1 : Prop) (t2 : Prop) : (term11 t1 t2) = (term12 t1 t2).
Proof. exact (MK_COMB (@lem5985829) (@lem5985828 t1 t2)). Qed.
Lemma lem5985831 (t1 : Prop) : (term13 t1) = (term14 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem5985830 t1 t2)). Qed.
Lemma lem5985832 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem5985833 (t1 : Prop) : (term15 t1) = (term16 t1).
Proof. exact (MK_COMB (@lem5985832) (@lem5985831 t1)). Qed.
Lemma lem5985834 : term17 = term18.
Proof. exact (fun_ext (fun t1 : Prop => @lem5985833 t1)). Qed.
Lemma lem5985835 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem5985836 : term19 = term20.
Proof. exact (MK_COMB (@lem5985835) (@lem5985834)). Qed.
Lemma lem5985837 : term20.
Proof. exact (EQ_MP (@lem5985836) (@lem512)). Qed.
Lemma lem5985849 (p : Prop) : p = (term21 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5985850 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : ((term22 _122099 _122102 P f x a) = (term23 _122099 _122102 P f x a)) = (term24 _122099 _122102 P f x a).
Proof. exact (@lem5985849 ((term22 _122099 _122102 P f x a) = (term23 _122099 _122102 P f x a))). Qed.
Lemma lem5985851 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term24 _122099 _122102 P f x a) = ((term22 _122099 _122102 P f x a) = (term23 _122099 _122102 P f x a)).
Proof. exact (SYM (@lem5985850 _122099 _122102 P f x a)). Qed.
Lemma lem5985852 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) (h1 : term25 _122099 _122102 P f x a) : term25 _122099 _122102 P f x a.
Proof. exact (h1). Qed.
Lemma lem5985855 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) (h1 : term24 _122099 _122102 P f x a) : term24 _122099 _122102 P f x a.
Proof. exact (h1). Qed.
Lemma lem5985856 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : term26 _122099 _122102 P f x a.
Proof. exact (fun h0 : term24 _122099 _122102 P f x a => @lem5985855 _122099 _122102 P f x a h0). Qed.
Lemma lem5985857 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) (h1 : term26 _122099 _122102 P f x a) : term26 _122099 _122102 P f x a.
Proof. exact (h1). Qed.
Lemma lem5985858 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) (h1 : term24 _122099 _122102 P f x a) : term24 _122099 _122102 P f x a.
Proof. exact (h1). Qed.
Lemma lem5985859 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) (h1 : term24 _122099 _122102 P f x a) (h2 : term26 _122099 _122102 P f x a) : term24 _122099 _122102 P f x a.
Proof. exact (@lem5985857 _122099 _122102 P f x a h2 (@lem5985858 _122099 _122102 P f x a h1)). Qed.
Lemma lem5985860 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) (h1 : term24 _122099 _122102 P f x a) : term27 _122099 _122102 P f x a.
Proof. exact (fun h0 : term26 _122099 _122102 P f x a => @lem5985859 _122099 _122102 P f x a h1 h0). Qed.
Lemma lem5985861 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) (h1 : term26 _122099 _122102 P f x a) : term26 _122099 _122102 P f x a.
Proof. exact (h1). Qed.
Lemma lem5985862 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) (h1 : term24 _122099 _122102 P f x a) (h2 : term26 _122099 _122102 P f x a) : term24 _122099 _122102 P f x a.
Proof. exact (@lem5985860 _122099 _122102 P f x a h1 (@lem5985861 _122099 _122102 P f x a h2)). Qed.
Lemma lem5985863 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) (h1 : term26 _122099 _122102 P f x a) : term26 _122099 _122102 P f x a.
Proof. exact (fun h0 : term24 _122099 _122102 P f x a => @lem5985862 _122099 _122102 P f x a h0 h1). Qed.
Lemma lem5985864 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : term28 _122099 _122102 P f x a.
Proof. exact (fun h0 : term26 _122099 _122102 P f x a => @lem5985863 _122099 _122102 P f x a h0). Qed.
Lemma lem5985867 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : term26 _122099 _122102 P f x a.
Proof. exact (@lem5985864 _122099 _122102 P f x a (@lem5985856 _122099 _122102 P f x a)). Qed.
Lemma lem5985868 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : term26 _122099 _122102 P f x a.
Proof. exact (@lem5985867 _122099 _122102 P f x a). Qed.
Lemma lem5985886 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5985887 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term24 _122099 _122102 P f x a) = (term29 _122099 _122102 P f x a).
Proof. exact (@lem5985886 (term25 _122099 _122102 P f x a)). Qed.
Lemma lem5985889 (t : Prop) : (term30 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5985890 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term29 _122099 _122102 P f x a) = ((term22 _122099 _122102 P f x a) = (term23 _122099 _122102 P f x a)).
Proof. exact (@lem5985889 ((term22 _122099 _122102 P f x a) = (term23 _122099 _122102 P f x a))). Qed.
Lemma lem5985891 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term24 _122099 _122102 P f x a) = ((term22 _122099 _122102 P f x a) = (term23 _122099 _122102 P f x a)).
Proof. exact (TRANS (@lem5985887 _122099 _122102 P f x a) (@lem5985890 _122099 _122102 P f x a)). Qed.
Lemma lem5985894 {_122099 _122102 : Type'} (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term31 _122099 _122102 f x a) = (term32 _122099 _122102 f x a).
Proof. exact (fun_ext (fun P : _122102 -> Prop => @lem5985891 _122099 _122102 P f x a)). Qed.
Lemma lem5985895 {_122102 : Type'} : (@all (_122102 -> Prop)) = (@all (_122102 -> Prop)).
Proof. exact (eq_refl (@all (_122102 -> Prop))). Qed.
Lemma lem5985896 {_122099 _122102 : Type'} (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term33 _122099 _122102 f x a) = (term34 _122099 _122102 f x a).
Proof. exact (MK_COMB (@lem5985895 _122102) (@lem5985894 _122099 _122102 f x a)). Qed.
Lemma lem5985901 {_122099 _122102 : Type'} (x : _122102) (a : _122099) : (term35 _122099 _122102 x a) = (term36 _122099 _122102 x a).
Proof. exact (fun_ext (fun f : _122102 -> _122099 => @lem5985896 _122099 _122102 f x a)). Qed.
Lemma lem5985902 {_122099 _122102 : Type'} : (@all (_122102 -> _122099)) = (@all (_122102 -> _122099)).
Proof. exact (eq_refl (@all (_122102 -> _122099))). Qed.
Lemma lem5985903 {_122099 _122102 : Type'} (x : _122102) (a : _122099) : (term37 _122099 _122102 x a) = (term38 _122099 _122102 x a).
Proof. exact (MK_COMB (@lem5985902 _122099 _122102) (@lem5985901 _122099 _122102 x a)). Qed.
Lemma lem5985908 {_122099 _122102 : Type'} (a : _122099) : (term39 _122099 _122102 a) = (term40 _122099 _122102 a).
Proof. exact (fun_ext (fun x : _122102 => @lem5985903 _122099 _122102 x a)). Qed.
Lemma lem5985909 {_122102 : Type'} : (@all _122102) = (@all _122102).
Proof. exact (eq_refl (@all _122102)). Qed.
Lemma lem5985910 {_122099 _122102 : Type'} (a : _122099) : (term41 _122099 _122102 a) = (term42 _122099 _122102 a).
Proof. exact (MK_COMB (@lem5985909 _122102) (@lem5985908 _122099 _122102 a)). Qed.
Lemma lem5985915 {_122099 _122102 : Type'} : (term43 _122099 _122102) = (term44 _122099 _122102).
Proof. exact (fun_ext (fun a : _122099 => @lem5985910 _122099 _122102 a)). Qed.
Lemma lem5985916 {_122099 : Type'} : (@all _122099) = (@all _122099).
Proof. exact (eq_refl (@all _122099)). Qed.
Lemma lem5985925 {_122099 _122102 : Type'} : (term45 _122099 _122102) = (term46 _122099 _122102).
Proof. exact (MK_COMB (@lem5985916 _122099) (@lem5985915 _122099 _122102)). Qed.
Lemma lem5985929 {_122102 : Type'} (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : (P x) = False.
Proof. exact (h1). Qed.
Lemma lem5985930 {_122099 : Type'} : (@COND _122099) = (@COND _122099).
Proof. exact (eq_refl (@COND _122099)). Qed.
Lemma lem5985931 {_122099 _122102 : Type'} (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : (term47 _122099 _122102 P x) = (@COND _122099 False).
Proof. exact (MK_COMB (@lem5985930 _122099) (@lem5985929 _122102 P x h1)). Qed.
Lemma lem5985932 {_122099 _122102 : Type'} (f : _122102 -> _122099) (x : _122102) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem5985933 {_122099 _122102 : Type'} (f : _122102 -> _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : (term48 _122099 _122102 P f x) = (term49 _122099 _122102 f x).
Proof. exact (MK_COMB (@lem5985931 _122099 _122102 P x h1) (@lem5985932 _122099 _122102 f x)). Qed.
Lemma lem5985934 {_122099 : Type'} (a : _122099) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5985935 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : (term50 _122099 _122102 P f x a) = (term51 _122099 _122102 f x a).
Proof. exact (MK_COMB (@lem5985933 _122099 _122102 f P x h1) (@lem5985934 _122099 a)). Qed.
Lemma lem5985937 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5985938 {_122099 : Type'} (t1 : _122099) (t2 : _122099) : (@COND _122099 False t1 t2) = t2.
Proof. exact (@lem5985937 _122099 t1 t2). Qed.
Lemma lem5985939 {_122099 _122102 : Type'} (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term51 _122099 _122102 f x a) = a.
Proof. exact (@lem5985938 _122099 (f x) a). Qed.
Lemma lem5985940 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : (term50 _122099 _122102 P f x a) = a.
Proof. exact (TRANS (@lem5985935 _122099 _122102 f a P x h1) (@lem5985939 _122099 _122102 f x a)). Qed.
Lemma lem5985941 {_122099 : Type'} : (@eq _122099) = (@eq _122099).
Proof. exact (eq_refl (@eq _122099)). Qed.
Lemma lem5985942 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : (term52 _122099 _122102 P f x a) = (@eq _122099 a).
Proof. exact (MK_COMB (@lem5985941 _122099) (@lem5985940 _122099 _122102 f a P x h1)). Qed.
Lemma lem5985943 {_122099 : Type'} (a : _122099) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5985944 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : ((term50 _122099 _122102 P f x a) = a) = (a = a).
Proof. exact (MK_COMB (@lem5985942 _122099 _122102 f a P x h1) (@lem5985943 _122099 a)). Qed.
Lemma lem5985946 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5985947 {_122099 : Type'} (x : _122099) : (x = x) = True.
Proof. exact (@lem5985946 _122099 x). Qed.
Lemma lem5985948 {_122099 : Type'} (a : _122099) : (a = a) = True.
Proof. exact (@lem5985947 _122099 a). Qed.
Lemma lem5985949 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : ((term50 _122099 _122102 P f x a) = a) = True.
Proof. exact (TRANS (@lem5985944 _122099 _122102 f a P x h1) (@lem5985948 _122099 a)). Qed.
Lemma lem5985950 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5985951 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : (term22 _122099 _122102 P f x a) = (~ True).
Proof. exact (MK_COMB (@lem5985950) (@lem5985949 _122099 _122102 f a P x h1)). Qed.
Lemma lem5985953 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem5985954 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : (term22 _122099 _122102 P f x a) = False.
Proof. exact (TRANS (@lem5985951 _122099 _122102 f a P x h1) (@lem5985953)). Qed.
Lemma lem5985955 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5985956 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : (term53 _122099 _122102 P f x a) = (@eq Prop False).
Proof. exact (MK_COMB (@lem5985955) (@lem5985954 _122099 _122102 f a P x h1)). Qed.
Lemma lem5985958 {_122102 : Type'} (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : (P x) = False.
Proof. exact (h1). Qed.
Lemma lem5985959 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5985960 {_122102 : Type'} (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : (term54 _122102 P x) = (and False).
Proof. exact (MK_COMB (@lem5985959) (@lem5985958 _122102 P x h1)). Qed.
Lemma lem5985963 {_122099 _122102 : Type'} (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term55 _122099 _122102 f x a) = (term55 _122099 _122102 f x a).
Proof. exact (eq_refl (term55 _122099 _122102 f x a)). Qed.
Lemma lem5985964 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : (term23 _122099 _122102 P f x a) = (term56 _122099 _122102 f x a).
Proof. exact (MK_COMB (@lem5985960 _122102 P x h1) (@lem5985963 _122099 _122102 f x a)). Qed.
Lemma lem5985966 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem5985967 {_122099 _122102 : Type'} (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term56 _122099 _122102 f x a) = False.
Proof. exact (@lem5985966 (term55 _122099 _122102 f x a)). Qed.
Lemma lem5985968 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : (term23 _122099 _122102 P f x a) = False.
Proof. exact (TRANS (@lem5985964 _122099 _122102 f a P x h1) (@lem5985967 _122099 _122102 f x a)). Qed.
Lemma lem5985969 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : ((term22 _122099 _122102 P f x a) = (term23 _122099 _122102 P f x a)) = (False = False).
Proof. exact (MK_COMB (@lem5985956 _122099 _122102 f a P x h1) (@lem5985968 _122099 _122102 f a P x h1)). Qed.
Lemma lem5985971 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem5985972 : (False = False) = (~ False).
Proof. exact (@lem5985971 False). Qed.
Lemma lem5985974 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5985975 : (False = False) = True.
Proof. exact (TRANS (@lem5985972) (@lem5985974)). Qed.
Lemma lem5985976 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = False) : ((term22 _122099 _122102 P f x a) = (term23 _122099 _122102 P f x a)) = True.
Proof. exact (TRANS (@lem5985969 _122099 _122102 f a P x h1) (@lem5985975)). Qed.
Lemma lem5985977 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : term57 _122099 _122102 P f x a.
Proof. exact (fun h0 : (P x) = False => @lem5985976 _122099 _122102 f a P x h0). Qed.
Lemma lem5985979 {_122102 : Type'} (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = True) : (P x) = True.
Proof. exact (h1). Qed.
Lemma lem5985980 {_122099 : Type'} : (@COND _122099) = (@COND _122099).
Proof. exact (eq_refl (@COND _122099)). Qed.
Lemma lem5985981 {_122099 _122102 : Type'} (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = True) : (term47 _122099 _122102 P x) = (@COND _122099 True).
Proof. exact (MK_COMB (@lem5985980 _122099) (@lem5985979 _122102 P x h1)). Qed.
Lemma lem5985982 {_122099 _122102 : Type'} (f : _122102 -> _122099) (x : _122102) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem5985983 {_122099 _122102 : Type'} (f : _122102 -> _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = True) : (term48 _122099 _122102 P f x) = (term58 _122099 _122102 f x).
Proof. exact (MK_COMB (@lem5985981 _122099 _122102 P x h1) (@lem5985982 _122099 _122102 f x)). Qed.
Lemma lem5985984 {_122099 : Type'} (a : _122099) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5985985 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = True) : (term50 _122099 _122102 P f x a) = (term59 _122099 _122102 f x a).
Proof. exact (MK_COMB (@lem5985983 _122099 _122102 f P x h1) (@lem5985984 _122099 a)). Qed.
Lemma lem5985987 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5985988 {_122099 : Type'} (t2 : _122099) (t1 : _122099) : (@COND _122099 True t1 t2) = t1.
Proof. exact (@lem5985987 _122099 t2 t1). Qed.
Lemma lem5985989 {_122099 _122102 : Type'} (a : _122099) (f : _122102 -> _122099) (x : _122102) : (term59 _122099 _122102 f x a) = (f x).
Proof. exact (@lem5985988 _122099 a (f x)). Qed.
Lemma lem5985990 {_122099 _122102 : Type'} (a : _122099) (f : _122102 -> _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = True) : (term50 _122099 _122102 P f x a) = (f x).
Proof. exact (TRANS (@lem5985985 _122099 _122102 f a P x h1) (@lem5985989 _122099 _122102 a f x)). Qed.
Lemma lem5985991 {_122099 : Type'} : (@eq _122099) = (@eq _122099).
Proof. exact (eq_refl (@eq _122099)). Qed.
Lemma lem5985992 {_122099 _122102 : Type'} (a : _122099) (f : _122102 -> _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = True) : (term52 _122099 _122102 P f x a) = (term60 _122099 _122102 f x).
Proof. exact (MK_COMB (@lem5985991 _122099) (@lem5985990 _122099 _122102 a f P x h1)). Qed.
Lemma lem5985993 {_122099 : Type'} (a : _122099) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5985994 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = True) : ((term50 _122099 _122102 P f x a) = a) = ((f x) = a).
Proof. exact (MK_COMB (@lem5985992 _122099 _122102 a f P x h1) (@lem5985993 _122099 a)). Qed.
Lemma lem5985997 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5985998 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = True) : (term22 _122099 _122102 P f x a) = (term55 _122099 _122102 f x a).
Proof. exact (MK_COMB (@lem5985997) (@lem5985994 _122099 _122102 f a P x h1)). Qed.
Lemma lem5985999 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5986000 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = True) : (term53 _122099 _122102 P f x a) = (term61 _122099 _122102 f x a).
Proof. exact (MK_COMB (@lem5985999) (@lem5985998 _122099 _122102 f a P x h1)). Qed.
Lemma lem5986002 {_122102 : Type'} (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = True) : (P x) = True.
Proof. exact (h1). Qed.
Lemma lem5986003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5986004 {_122102 : Type'} (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = True) : (term54 _122102 P x) = (and True).
Proof. exact (MK_COMB (@lem5986003) (@lem5986002 _122102 P x h1)). Qed.
Lemma lem5986007 {_122099 _122102 : Type'} (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term55 _122099 _122102 f x a) = (term55 _122099 _122102 f x a).
Proof. exact (eq_refl (term55 _122099 _122102 f x a)). Qed.
Lemma lem5986008 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = True) : (term23 _122099 _122102 P f x a) = (term62 _122099 _122102 f x a).
Proof. exact (MK_COMB (@lem5986004 _122102 P x h1) (@lem5986007 _122099 _122102 f x a)). Qed.
Lemma lem5986010 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5986011 {_122099 _122102 : Type'} (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term62 _122099 _122102 f x a) = (term55 _122099 _122102 f x a).
Proof. exact (@lem5986010 (term55 _122099 _122102 f x a)). Qed.
Lemma lem5986012 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = True) : (term23 _122099 _122102 P f x a) = (term55 _122099 _122102 f x a).
Proof. exact (TRANS (@lem5986008 _122099 _122102 f a P x h1) (@lem5986011 _122099 _122102 f x a)). Qed.
Lemma lem5986013 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = True) : ((term22 _122099 _122102 P f x a) = (term23 _122099 _122102 P f x a)) = ((term55 _122099 _122102 f x a) = (term55 _122099 _122102 f x a)).
Proof. exact (MK_COMB (@lem5986000 _122099 _122102 f a P x h1) (@lem5986012 _122099 _122102 f a P x h1)). Qed.
Lemma lem5986015 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5986016 (x : Prop) : (x = x) = True.
Proof. exact (@lem5986015 Prop x). Qed.
Lemma lem5986017 {_122099 _122102 : Type'} (f : _122102 -> _122099) (x : _122102) (a : _122099) : ((term55 _122099 _122102 f x a) = (term55 _122099 _122102 f x a)) = True.
Proof. exact (@lem5986016 (term55 _122099 _122102 f x a)). Qed.
Lemma lem5986018 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) (h1 : (P x) = True) : ((term22 _122099 _122102 P f x a) = (term23 _122099 _122102 P f x a)) = True.
Proof. exact (TRANS (@lem5986013 _122099 _122102 f a P x h1) (@lem5986017 _122099 _122102 f x a)). Qed.
Lemma lem5986019 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : term63 _122099 _122102 P f x a.
Proof. exact (fun h0 : (P x) = True => @lem5986018 _122099 _122102 f a P x h0). Qed.
Lemma lem5986020 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : term64 _122099 _122102 P f x a.
Proof. exact (conj (@lem5985977 _122099 _122102 P f x a) (@lem5986019 _122099 _122102 P f x a)). Qed.
Lemma lem5986022 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term65 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5986023 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) : term66 _122099 _122102 f a P x.
Proof. exact (@lem5986022 ((term22 _122099 _122102 P f x a) = (term23 _122099 _122102 P f x a)) True (P x) True). Qed.
Lemma lem5986024 {_122099 _122102 : Type'} (f : _122102 -> _122099) (a : _122099) (P : _122102 -> Prop) (x : _122102) : ((term22 _122099 _122102 P f x a) = (term23 _122099 _122102 P f x a)) = (term67 _122102 P x).
Proof. exact (@lem5986023 _122099 _122102 f a P x (@lem5986020 _122099 _122102 P f x a)). Qed.
Lemma lem5986026 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem5986027 {_122102 : Type'} (P : _122102 -> Prop) (x : _122102) : (term68 _122102 P x) = True.
Proof. exact (@lem5986026 (P x)). Qed.
Lemma lem5986029 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem5986030 {_122102 : Type'} (P : _122102 -> Prop) (x : _122102) : (term69 _122102 P x) = True.
Proof. exact (@lem5986029 (term70 _122102 P x)). Qed.
Lemma lem5986031 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5986032 {_122102 : Type'} (P : _122102 -> Prop) (x : _122102) : (term71 _122102 P x) = (and True).
Proof. exact (MK_COMB (@lem5986031) (@lem5986030 _122102 P x)). Qed.
Lemma lem5986033 {_122102 : Type'} (P : _122102 -> Prop) (x : _122102) : (term67 _122102 P x) = (True /\ True).
Proof. exact (MK_COMB (@lem5986032 _122102 P x) (@lem5986027 _122102 P x)). Qed.
Lemma lem5986035 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5986036 : (True /\ True) = True.
Proof. exact (@lem5986035 True). Qed.
Lemma lem5986037 {_122102 : Type'} (P : _122102 -> Prop) (x : _122102) : (term67 _122102 P x) = True.
Proof. exact (TRANS (@lem5986033 _122102 P x) (@lem5986036)). Qed.
Lemma lem5986042 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : ((term22 _122099 _122102 P f x a) = (term23 _122099 _122102 P f x a)) = True.
Proof. exact (TRANS (@lem5986024 _122099 _122102 f a P x) (@lem5986037 _122102 P x)). Qed.
Lemma lem5986043 {_122099 _122102 : Type'} (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term32 _122099 _122102 f x a) = (term72 _122102).
Proof. exact (fun_ext (fun P : _122102 -> Prop => @lem5986042 _122099 _122102 P f x a)). Qed.
Lemma lem5986044 {_122102 : Type'} : (@all (_122102 -> Prop)) = (@all (_122102 -> Prop)).
Proof. exact (eq_refl (@all (_122102 -> Prop))). Qed.
Lemma lem5986045 {_122099 _122102 : Type'} (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term34 _122099 _122102 f x a) = (term73 _122102).
Proof. exact (MK_COMB (@lem5986044 _122102) (@lem5986043 _122099 _122102 f x a)). Qed.
Lemma lem5986046 {_122099 _122102 : Type'} (x : _122102) (a : _122099) : (term36 _122099 _122102 x a) = (term74 _122099 _122102).
Proof. exact (fun_ext (fun f : _122102 -> _122099 => @lem5986045 _122099 _122102 f x a)). Qed.
Lemma lem5986047 {_122099 _122102 : Type'} : (@all (_122102 -> _122099)) = (@all (_122102 -> _122099)).
Proof. exact (eq_refl (@all (_122102 -> _122099))). Qed.
Lemma lem5986048 {_122099 _122102 : Type'} (x : _122102) (a : _122099) : (term38 _122099 _122102 x a) = (term75 _122099 _122102).
Proof. exact (MK_COMB (@lem5986047 _122099 _122102) (@lem5986046 _122099 _122102 x a)). Qed.
Lemma lem5986049 {_122099 _122102 : Type'} (a : _122099) : (term40 _122099 _122102 a) = (term76 _122099 _122102).
Proof. exact (fun_ext (fun x : _122102 => @lem5986048 _122099 _122102 x a)). Qed.
Lemma lem5986050 {_122102 : Type'} : (@all _122102) = (@all _122102).
Proof. exact (eq_refl (@all _122102)). Qed.
Lemma lem5986051 {_122099 _122102 : Type'} (a : _122099) : (term42 _122099 _122102 a) = (term77 _122099 _122102).
Proof. exact (MK_COMB (@lem5986050 _122102) (@lem5986049 _122099 _122102 a)). Qed.
Lemma lem5986052 {_122099 _122102 : Type'} : (term44 _122099 _122102) = (term78 _122099 _122102).
Proof. exact (fun_ext (fun a : _122099 => @lem5986051 _122099 _122102 a)). Qed.
Lemma lem5986053 {_122099 : Type'} : (@all _122099) = (@all _122099).
Proof. exact (eq_refl (@all _122099)). Qed.
Lemma lem5986054 {_122099 _122102 : Type'} : (term46 _122099 _122102) = (term79 _122099 _122102).
Proof. exact (MK_COMB (@lem5986053 _122099) (@lem5986052 _122099 _122102)). Qed.
Lemma lem5986055 {_122099 _122102 : Type'} : (term45 _122099 _122102) = (term79 _122099 _122102).
Proof. exact (TRANS (@lem5985925 _122099 _122102) (@lem5986054 _122099 _122102)). Qed.
Lemma lem5986057 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem5986058 {_122099 : Type'} (t : Prop) : (term80 _122099 t) = t.
Proof. exact (@lem5986057 _122099 t). Qed.
Lemma lem5986059 {_122099 _122102 : Type'} : (term79 _122099 _122102) = (term77 _122099 _122102).
Proof. exact (@lem5986058 _122099 (term77 _122099 _122102)). Qed.
Lemma lem5986061 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem5986062 {_122102 : Type'} (t : Prop) : (term80 _122102 t) = t.
Proof. exact (@lem5986061 _122102 t). Qed.
Lemma lem5986063 {_122099 _122102 : Type'} : (term77 _122099 _122102) = (term75 _122099 _122102).
Proof. exact (@lem5986062 _122102 (term75 _122099 _122102)). Qed.
Lemma lem5986065 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem5986066 {_122099 _122102 : Type'} (t : Prop) : (term81 _122099 _122102 t) = t.
Proof. exact (@lem5986065 (_122102 -> _122099) t). Qed.
Lemma lem5986067 {_122099 _122102 : Type'} : (term75 _122099 _122102) = (term73 _122102).
Proof. exact (@lem5986066 _122099 _122102 (term73 _122102)). Qed.
Lemma lem5986069 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem5986070 {_122102 : Type'} (t : Prop) : (term82 _122102 t) = t.
Proof. exact (@lem5986069 (_122102 -> Prop) t). Qed.
Lemma lem5986071 {_122102 : Type'} : (term73 _122102) = True.
Proof. exact (@lem5986070 _122102 True). Qed.
Lemma lem5986072 {_122099 _122102 : Type'} : (term75 _122099 _122102) = True.
Proof. exact (TRANS (@lem5986067 _122099 _122102) (@lem5986071 _122102)). Qed.
Lemma lem5986073 {_122099 _122102 : Type'} : (term77 _122099 _122102) = True.
Proof. exact (TRANS (@lem5986063 _122099 _122102) (@lem5986072 _122099 _122102)). Qed.
Lemma lem5986074 {_122099 _122102 : Type'} : (term79 _122099 _122102) = True.
Proof. exact (TRANS (@lem5986059 _122099 _122102) (@lem5986073 _122099 _122102)). Qed.
Lemma lem5986075 {_122099 _122102 : Type'} : (term45 _122099 _122102) = True.
Proof. exact (TRANS (@lem5986055 _122099 _122102) (@lem5986074 _122099 _122102)). Qed.
Lemma lem5986076 {_122099 _122102 : Type'} : True = (term45 _122099 _122102).
Proof. exact (SYM (@lem5986075 _122099 _122102)). Qed.
Lemma lem5986077 {_122099 _122102 : Type'} : term45 _122099 _122102.
Proof. exact (EQ_MP (@lem5986076 _122099 _122102) (@lem0)). Qed.
Lemma lem5986078 {_122099 _122102 : Type'} (a : _122099) : term83 _122099 _122102 a.
Proof. exact (@lem5986077 _122099 _122102 a). Qed.
Lemma lem5986079 {_122099 _122102 : Type'} (a : _122099) : (term83 _122099 _122102 a) = (term41 _122099 _122102 a).
Proof. exact (eq_refl (term83 _122099 _122102 a)). Qed.
Lemma lem5986080 {_122099 _122102 : Type'} (a : _122099) : term41 _122099 _122102 a.
Proof. exact (EQ_MP (@lem5986079 _122099 _122102 a) (@lem5986078 _122099 _122102 a)). Qed.
Lemma lem5986081 {_122099 _122102 : Type'} (a : _122099) (x : _122102) : term84 _122099 _122102 a x.
Proof. exact (@lem5986080 _122099 _122102 a x). Qed.
Lemma lem5986082 {_122099 _122102 : Type'} (x : _122102) (a : _122099) : (term84 _122099 _122102 a x) = (term37 _122099 _122102 x a).
Proof. exact (eq_refl (term84 _122099 _122102 a x)). Qed.
Lemma lem5986083 {_122099 _122102 : Type'} (x : _122102) (a : _122099) : term37 _122099 _122102 x a.
Proof. exact (EQ_MP (@lem5986082 _122099 _122102 x a) (@lem5986081 _122099 _122102 a x)). Qed.
Lemma lem5986084 {_122099 _122102 : Type'} (x : _122102) (a : _122099) (f : _122102 -> _122099) : term85 _122099 _122102 x a f.
Proof. exact (@lem5986083 _122099 _122102 x a f). Qed.
Lemma lem5986085 {_122099 _122102 : Type'} (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term85 _122099 _122102 x a f) = (term33 _122099 _122102 f x a).
Proof. exact (eq_refl (term85 _122099 _122102 x a f)). Qed.
Lemma lem5986086 {_122099 _122102 : Type'} (f : _122102 -> _122099) (x : _122102) (a : _122099) : term33 _122099 _122102 f x a.
Proof. exact (EQ_MP (@lem5986085 _122099 _122102 f x a) (@lem5986084 _122099 _122102 x a f)). Qed.
Lemma lem5986087 {_122099 _122102 : Type'} (f : _122102 -> _122099) (x : _122102) (a : _122099) (P : _122102 -> Prop) : term86 _122099 _122102 f x a P.
Proof. exact (@lem5986086 _122099 _122102 f x a P). Qed.
Lemma lem5986088 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term86 _122099 _122102 f x a P) = (term24 _122099 _122102 P f x a).
Proof. exact (eq_refl (term86 _122099 _122102 f x a P)). Qed.
Lemma lem5986089 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : term24 _122099 _122102 P f x a.
Proof. exact (EQ_MP (@lem5986088 _122099 _122102 P f x a) (@lem5986087 _122099 _122102 f x a P)). Qed.
Lemma lem5986091 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : term24 _122099 _122102 P f x a.
Proof. exact (@lem5985868 _122099 _122102 P f x a (@lem5986089 _122099 _122102 P f x a)). Qed.
Lemma lem5986092 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) (h1 : term25 _122099 _122102 P f x a) : False.
Proof. exact (@lem5986091 _122099 _122102 P f x a (@lem5985852 _122099 _122102 P f x a h1)). Qed.
Lemma lem5986093 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) (h1 : term25 _122099 _122102 P f x a) : (term25 _122099 _122102 P f x a) = False.
Proof. exact (prop_ext (fun h2 : term25 _122099 _122102 P f x a => @lem5986092 _122099 _122102 P f x a h1) (fun h2 : False => @lem5985852 _122099 _122102 P f x a h1)). Qed.
Lemma lem5986094 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) (h1 : term25 _122099 _122102 P f x a) : False.
Proof. exact (EQ_MP (@lem5986093 _122099 _122102 P f x a h1) (@lem5985852 _122099 _122102 P f x a h1)). Qed.
Lemma lem5986095 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : term24 _122099 _122102 P f x a.
Proof. exact (fun h0 : term25 _122099 _122102 P f x a => @lem5986094 _122099 _122102 P f x a h0). Qed.
Lemma lem5986097 (t1 : Prop) : term87 t1.
Proof. exact (@lem5985837 t1). Qed.
Lemma lem5986098 (t1 : Prop) : (term87 t1) = (term16 t1).
Proof. exact (eq_refl (term87 t1)). Qed.
Lemma lem5986099 (t1 : Prop) : term16 t1.
Proof. exact (EQ_MP (@lem5986098 t1) (@lem5986097 t1)). Qed.
Lemma lem5986100 (t1 : Prop) (t2 : Prop) : term88 t1 t2.
Proof. exact (@lem5986099 t1 t2). Qed.
Lemma lem5986101 (t1 : Prop) (t2 : Prop) : (term88 t1 t2) = (term12 t1 t2).
Proof. exact (eq_refl (term88 t1 t2)). Qed.
Lemma lem5986102 (t1 : Prop) (t2 : Prop) : term12 t1 t2.
Proof. exact (EQ_MP (@lem5986101 t1 t2) (@lem5986100 t1 t2)). Qed.
Lemma lem5986103 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term89 t1 t2 t3.
Proof. exact (@lem5986102 t1 t2 t3). Qed.
Lemma lem5986104 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term89 t1 t2 t3) = ((term8 t1 t2 t3) = (term7 t1 t2 t3)).
Proof. exact (eq_refl (term89 t1 t2 t3)). Qed.
Lemma lem5986130 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5986131 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem5986130 _83095 p). Qed.
Lemma lem5986132 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem5986133 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem5986132 _83095 p) (@lem5986131 _83095 p)). Qed.
Lemma lem5986134 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem5986133 _83095 p x). Qed.
Lemma lem5986135 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem5986144 {A B : Type'} (s : A -> Prop) : term90 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem5986145 {A B : Type'} (s : A -> Prop) : (term90 A B s) = (term91 A B s).
Proof. exact (eq_refl (term90 A B s)). Qed.
Lemma lem5986146 {A B : Type'} (s : A -> Prop) : term91 A B s.
Proof. exact (EQ_MP (@lem5986145 A B s) (@lem5986144 A B s)). Qed.
Lemma lem5986147 {A B : Type'} (s : A -> Prop) (f : A -> B) : term92 A B s f.
Proof. exact (@lem5986146 A B s f). Qed.
Lemma lem5986148 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term92 A B s f) = (term93 A B s f).
Proof. exact (eq_refl (term92 A B s f)). Qed.
Lemma lem5986149 {A B : Type'} (s : A -> Prop) (f : A -> B) : term93 A B s f.
Proof. exact (EQ_MP (@lem5986148 A B s f) (@lem5986147 A B s f)). Qed.
Lemma lem5986150 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term94 A B s f op.
Proof. exact (@lem5986149 A B s f op). Qed.
Lemma lem5986151 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term94 A B s f op) = ((@support A B op f s) = (term95 A B s f op)).
Proof. exact (eq_refl (term94 A B s f op)). Qed.
Lemma lem5986156 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term96 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (term96 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem5986157 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term96 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term96 _120296 _120308 op s f).
Proof. exact (SYM (@lem5986156 _120296 _120308 op s f h1)). Qed.
Lemma lem5986158 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term96 _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term96 _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem5986159 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term96 _120296 _120308 op s f)) : (term96 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (SYM (@lem5986158 _120296 _120308 op s f h1)). Qed.
Lemma lem5986160 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : ((term96 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) = ((@iterate _120296 _120308 op s f) = (term96 _120296 _120308 op s f)).
Proof. exact (prop_ext (fun h1 : (term96 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f) => @lem5986157 _120296 _120308 op s f h1) (fun h1 : (@iterate _120296 _120308 op s f) = (term96 _120296 _120308 op s f) => @lem5986159 _120296 _120308 op s f h1)). Qed.
Lemma lem5986161 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term97 _120296 _120308 op f) = (term98 _120296 _120308 op f).
Proof. exact (fun_ext (fun s : _120308 -> Prop => @lem5986160 _120296 _120308 op s f)). Qed.
Lemma lem5986162 {_120308 : Type'} : (@all (_120308 -> Prop)) = (@all (_120308 -> Prop)).
Proof. exact (eq_refl (@all (_120308 -> Prop))). Qed.
Lemma lem5986163 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term99 _120296 _120308 op f) = (term100 _120296 _120308 op f).
Proof. exact (MK_COMB (@lem5986162 _120308) (@lem5986161 _120296 _120308 op f)). Qed.
Lemma lem5986164 {_120296 _120308 : Type'} (op : type1400 _120296) : (term101 _120296 _120308 op) = (term102 _120296 _120308 op).
Proof. exact (fun_ext (fun f : _120308 -> _120296 => @lem5986163 _120296 _120308 op f)). Qed.
Lemma lem5986165 {_120296 _120308 : Type'} : (@all (_120308 -> _120296)) = (@all (_120308 -> _120296)).
Proof. exact (eq_refl (@all (_120308 -> _120296))). Qed.
Lemma lem5986166 {_120296 _120308 : Type'} (op : type1400 _120296) : (term103 _120296 _120308 op) = (term104 _120296 _120308 op).
Proof. exact (MK_COMB (@lem5986165 _120296 _120308) (@lem5986164 _120296 _120308 op)). Qed.
Lemma lem5986167 {_120296 _120308 : Type'} : (term105 _120296 _120308) = (term106 _120296 _120308).
Proof. exact (fun_ext (fun op : type1400 _120296 => @lem5986166 _120296 _120308 op)). Qed.
Lemma lem5986168 {_120296 : Type'} : (@all (_120296 -> _120296 -> _120296)) = (@all (_120296 -> _120296 -> _120296)).
Proof. exact (eq_refl (@all (_120296 -> _120296 -> _120296))). Qed.
Lemma lem5986169 {_120296 _120308 : Type'} : (term107 _120296 _120308) = (term108 _120296 _120308).
Proof. exact (MK_COMB (@lem5986168 _120296) (@lem5986167 _120296 _120308)). Qed.
Lemma lem5986170 {_120296 _120308 : Type'} : term108 _120296 _120308.
Proof. exact (EQ_MP (@lem5986169 _120296 _120308) (@lem5737860 _120296 _120308)). Qed.
Lemma lem5986171 {_120296 _120308 : Type'} (op : type1400 _120296) : term109 _120296 _120308 op.
Proof. exact (@lem5986170 _120296 _120308 op). Qed.
Lemma lem5986172 {_120296 _120308 : Type'} (op : type1400 _120296) : (term109 _120296 _120308 op) = (term104 _120296 _120308 op).
Proof. exact (eq_refl (term109 _120296 _120308 op)). Qed.
Lemma lem5986173 {_120296 _120308 : Type'} (op : type1400 _120296) : term104 _120296 _120308 op.
Proof. exact (EQ_MP (@lem5986172 _120296 _120308 op) (@lem5986171 _120296 _120308 op)). Qed.
Lemma lem5986174 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term110 _120296 _120308 op f.
Proof. exact (@lem5986173 _120296 _120308 op f). Qed.
Lemma lem5986175 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term110 _120296 _120308 op f) = (term100 _120296 _120308 op f).
Proof. exact (eq_refl (term110 _120296 _120308 op f)). Qed.
Lemma lem5986176 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term100 _120296 _120308 op f.
Proof. exact (EQ_MP (@lem5986175 _120296 _120308 op f) (@lem5986174 _120296 _120308 op f)). Qed.
Lemma lem5986177 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) (s : _120308 -> Prop) : term111 _120296 _120308 op f s.
Proof. exact (@lem5986176 _120296 _120308 op f s). Qed.
Lemma lem5986178 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (term111 _120296 _120308 op f s) = ((@iterate _120296 _120308 op s f) = (term96 _120296 _120308 op s f)).
Proof. exact (eq_refl (term111 _120296 _120308 op f s)). Qed.
Lemma lem5986180 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5986184 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term96 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem5986178 _120296 _120308 op s f) (@lem5986177 _120296 _120308 op f s)). Qed.
Lemma lem5986185 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term112 A B op s f).
Proof. exact (@lem5986184 B A op s f). Qed.
Lemma lem5986186 {A B : Type'} (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) : (term113 A B op s P f) = (term114 A B op s P f).
Proof. exact (@lem5986185 A B op (term115 A s P) f). Qed.
Lemma lem5986187 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5986188 {A B : Type'} (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) : (term116 A B op s P f) = (term117 A B op s P f).
Proof. exact (MK_COMB (@lem5986187 B) (@lem5986186 A B op s P f)). Qed.
Lemma lem5986190 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term96 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem5986178 _120296 _120308 op s f) (@lem5986177 _120296 _120308 op f s)). Qed.
Lemma lem5986191 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term112 A B op s f).
Proof. exact (@lem5986190 B A op s f). Qed.
Lemma lem5986192 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term118 A B s P f op) = (term119 A B s P f op).
Proof. exact (@lem5986191 A B op s (term120 A B P f op)). Qed.
Lemma lem5986193 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : ((term113 A B op s P f) = (term118 A B s P f op)) = ((term114 A B op s P f) = (term119 A B s P f op)).
Proof. exact (MK_COMB (@lem5986188 A B op s P f) (@lem5986192 A B s P f op)). Qed.
Lemma lem5986194 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : ((term114 A B op s P f) = (term119 A B s P f op)) = ((term113 A B op s P f) = (term118 A B s P f op)).
Proof. exact (SYM (@lem5986193 A B s P f op)). Qed.
Lemma lem5986198 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term95 A B s f op).
Proof. exact (EQ_MP (@lem5986151 A B s f op) (@lem5986150 A B s f op)). Qed.
Lemma lem5986199 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term95 A B s f op).
Proof. exact (@lem5986198 A B s f op). Qed.
Lemma lem5986200 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term121 A B op f s P) = (term122 A B s P f op).
Proof. exact (@lem5986199 A B (term115 A s P) f op). Qed.
Lemma lem5986208 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5986135 _83095 p x) (@lem5986134 _83095 p x)). Qed.
Lemma lem5986209 {A : Type'} (p : A -> Prop) (x : A) : (term4 A x p) = (p x).
Proof. exact (@lem5986208 A p x). Qed.
Lemma lem5986210 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term123 A x s P) = (term124 A s P x).
Proof. exact (@lem5986209 A (term125 A s P) x). Qed.
Lemma lem5986211 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term124 A s P x) = (term126 A s P x).
Proof. exact (eq_refl (term124 A s P x)). Qed.
Lemma lem5986212 {A : Type'} (GEN_PVAR_242 : A) : (@SETSPEC A GEN_PVAR_242) = (@SETSPEC A GEN_PVAR_242).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_242)). Qed.
Lemma lem5986213 {A : Type'} (GEN_PVAR_242 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term127 A GEN_PVAR_242 s P x) = (term128 A GEN_PVAR_242 s P x).
Proof. exact (MK_COMB (@lem5986212 A GEN_PVAR_242) (@lem5986211 A s P x)). Qed.
Lemma lem5986214 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5986215 {A : Type'} (GEN_PVAR_242 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term129 A GEN_PVAR_242 s P x) = (term130 A GEN_PVAR_242 s P x).
Proof. exact (MK_COMB (@lem5986213 A GEN_PVAR_242 s P x) (@lem5986214 A x)). Qed.
Lemma lem5986216 {A : Type'} (GEN_PVAR_242 : A) (s : A -> Prop) (P : A -> Prop) : (term131 A GEN_PVAR_242 s P) = (term132 A GEN_PVAR_242 s P).
Proof. exact (fun_ext (fun x : A => @lem5986215 A GEN_PVAR_242 s P x)). Qed.
Lemma lem5986217 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5986218 {A : Type'} (GEN_PVAR_242 : A) (s : A -> Prop) (P : A -> Prop) : (term133 A GEN_PVAR_242 s P) = (term134 A GEN_PVAR_242 s P).
Proof. exact (MK_COMB (@lem5986217 A) (@lem5986216 A GEN_PVAR_242 s P)). Qed.
Lemma lem5986219 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term135 A s P) = (term136 A s P).
Proof. exact (fun_ext (fun GEN_PVAR_242 : A => @lem5986218 A GEN_PVAR_242 s P)). Qed.
Lemma lem5986220 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5986221 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term137 A s P) = (term115 A s P).
Proof. exact (MK_COMB (@lem5986220 A) (@lem5986219 A s P)). Qed.
Lemma lem5986222 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5986223 {A : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) : (term123 A x s P) = (term138 A x s P).
Proof. exact (MK_COMB (@lem5986222 A x) (@lem5986221 A s P)). Qed.
Lemma lem5986224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5986225 {A : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) : (term139 A x s P) = (term140 A x s P).
Proof. exact (MK_COMB (@lem5986224) (@lem5986223 A x s P)). Qed.
Lemma lem5986226 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term124 A s P x) = (term126 A s P x).
Proof. exact (eq_refl (term124 A s P x)). Qed.
Lemma lem5986227 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : ((term123 A x s P) = (term124 A s P x)) = ((term138 A x s P) = (term126 A s P x)).
Proof. exact (MK_COMB (@lem5986225 A x s P) (@lem5986226 A s P x)). Qed.
Lemma lem5986228 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term138 A x s P) = (term126 A s P x).
Proof. exact (EQ_MP (@lem5986227 A s P x) (@lem5986210 A s P x)). Qed.
Lemma lem5986231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5986232 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term141 A x s P) = (term142 A s P x).
Proof. exact (MK_COMB (@lem5986231) (@lem5986228 A s P x)). Qed.
Lemma lem5986235 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term143 A B f x op) = (term143 A B f x op).
Proof. exact (eq_refl (term143 A B f x op)). Qed.
Lemma lem5986236 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term144 A B s P f x op) = (term145 A B s P f x op).
Proof. exact (MK_COMB (@lem5986232 A s P x) (@lem5986235 A B f x op)). Qed.
Lemma lem5986239 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem5986240 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term146 A B GEN_PVAR_237 s P f x op) = (term147 A B GEN_PVAR_237 s P f x op).
Proof. exact (MK_COMB (@lem5986239 A GEN_PVAR_237) (@lem5986236 A B s P f x op)). Qed.
Lemma lem5986241 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5986242 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term148 A B GEN_PVAR_237 s P f op x) = (term149 A B GEN_PVAR_237 s P f op x).
Proof. exact (MK_COMB (@lem5986240 A B GEN_PVAR_237 s P f x op) (@lem5986241 A x)). Qed.
Lemma lem5986243 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term150 A B GEN_PVAR_237 s P f op) = (term151 A B GEN_PVAR_237 s P f op).
Proof. exact (fun_ext (fun x : A => @lem5986242 A B GEN_PVAR_237 s P f op x)). Qed.
Lemma lem5986244 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5986245 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term152 A B GEN_PVAR_237 s P f op) = (term153 A B GEN_PVAR_237 s P f op).
Proof. exact (MK_COMB (@lem5986244 A) (@lem5986243 A B GEN_PVAR_237 s P f op)). Qed.
Lemma lem5986250 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term154 A B s P f op) = (term155 A B s P f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem5986245 A B GEN_PVAR_237 s P f op)). Qed.
Lemma lem5986251 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5986252 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term122 A B s P f op) = (term156 A B s P f op).
Proof. exact (MK_COMB (@lem5986251 A) (@lem5986250 A B s P f op)). Qed.
Lemma lem5986253 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term121 A B op f s P) = (term156 A B s P f op).
Proof. exact (TRANS (@lem5986200 A B s P f op) (@lem5986252 A B s P f op)). Qed.
Lemma lem5986254 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5986255 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term157 A B op f s P) = (term158 A B s P f op).
Proof. exact (MK_COMB (@lem5986254 A B op) (@lem5986253 A B s P f op)). Qed.
Lemma lem5986256 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5986257 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (op : type1400 B) (f : A -> B) : (term114 A B op s P f) = (term159 A B s P op f).
Proof. exact (MK_COMB (@lem5986255 A B s P f op) (@lem5986256 A B f)). Qed.
Lemma lem5986258 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5986259 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (op : type1400 B) (f : A -> B) : (term117 A B op s P f) = (term160 A B s P op f).
Proof. exact (MK_COMB (@lem5986258 B) (@lem5986257 A B s P op f)). Qed.
Lemma lem5986261 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term95 A B s f op).
Proof. exact (EQ_MP (@lem5986151 A B s f op) (@lem5986150 A B s f op)). Qed.
Lemma lem5986262 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term95 A B s f op).
Proof. exact (@lem5986261 A B s f op). Qed.
Lemma lem5986263 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term161 A B P f op s) = (term162 A B s P f op).
Proof. exact (@lem5986262 A B s (term120 A B P f op) op). Qed.
Lemma lem5986273 {A B : Type'} (f : A -> B) (y : A) : (term163 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5986274 {A B : Type'} (f : A -> B) (y : A) : (term163 A B f y) = (f y).
Proof. exact (@lem5986273 A B f y). Qed.
Lemma lem5986275 {A B : Type'} (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term164 A B P f op x) = (term165 A B P f op x).
Proof. exact (@lem5986274 A B (term120 A B P f op) x). Qed.
Lemma lem5986276 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term165 A B P f op x) = (term166 A B P f x op).
Proof. exact (eq_refl (term165 A B P f op x)). Qed.
Lemma lem5986277 {A B : Type'} (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term167 A B P f op) = (term120 A B P f op).
Proof. exact (fun_ext (fun x : A => @lem5986276 A B P f x op)). Qed.
Lemma lem5986278 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5986279 {A B : Type'} (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term164 A B P f op x) = (term165 A B P f op x).
Proof. exact (MK_COMB (@lem5986277 A B P f op) (@lem5986278 A x)). Qed.
Lemma lem5986280 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5986281 {A B : Type'} (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term168 A B P f op x) = (term169 A B P f op x).
Proof. exact (MK_COMB (@lem5986280 B) (@lem5986279 A B P f op x)). Qed.
Lemma lem5986282 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term165 A B P f op x) = (term166 A B P f x op).
Proof. exact (eq_refl (term165 A B P f op x)). Qed.
Lemma lem5986283 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term164 A B P f op x) = (term165 A B P f op x)) = ((term165 A B P f op x) = (term166 A B P f x op)).
Proof. exact (MK_COMB (@lem5986281 A B P f op x) (@lem5986282 A B P f x op)). Qed.
Lemma lem5986284 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term165 A B P f op x) = (term166 A B P f x op).
Proof. exact (EQ_MP (@lem5986283 A B P f x op) (@lem5986275 A B P f op x)). Qed.
Lemma lem5986285 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5986286 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term169 A B P f op x) = (term170 A B P f x op).
Proof. exact (MK_COMB (@lem5986285 B) (@lem5986284 A B P f x op)). Qed.
Lemma lem5986287 {B : Type'} (op : type1400 B) : (@neutral B op) = (@neutral B op).
Proof. exact (eq_refl (@neutral B op)). Qed.
Lemma lem5986288 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term165 A B P f op x) = (@neutral B op)) = ((term166 A B P f x op) = (@neutral B op)).
Proof. exact (MK_COMB (@lem5986286 A B P f x op) (@lem5986287 B op)). Qed.
Lemma lem5986291 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5986292 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term171 A B P f x op) = (term172 A B P f x op).
Proof. exact (MK_COMB (@lem5986291) (@lem5986288 A B P f x op)). Qed.
Lemma lem5986293 {A : Type'} (x : A) (s : A -> Prop) : (term173 A x s) = (term173 A x s).
Proof. exact (eq_refl (term173 A x s)). Qed.
Lemma lem5986294 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term174 A B s P f x op) = (term175 A B s P f x op).
Proof. exact (MK_COMB (@lem5986293 A x s) (@lem5986292 A B P f x op)). Qed.
Lemma lem5986297 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem5986298 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term176 A B GEN_PVAR_237 s P f x op) = (term177 A B GEN_PVAR_237 s P f x op).
Proof. exact (MK_COMB (@lem5986297 A GEN_PVAR_237) (@lem5986294 A B s P f x op)). Qed.
Lemma lem5986299 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5986300 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term178 A B GEN_PVAR_237 s P f op x) = (term179 A B GEN_PVAR_237 s P f op x).
Proof. exact (MK_COMB (@lem5986298 A B GEN_PVAR_237 s P f x op) (@lem5986299 A x)). Qed.
Lemma lem5986301 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term180 A B GEN_PVAR_237 s P f op) = (term181 A B GEN_PVAR_237 s P f op).
Proof. exact (fun_ext (fun x : A => @lem5986300 A B GEN_PVAR_237 s P f op x)). Qed.
Lemma lem5986302 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5986303 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term182 A B GEN_PVAR_237 s P f op) = (term183 A B GEN_PVAR_237 s P f op).
Proof. exact (MK_COMB (@lem5986302 A) (@lem5986301 A B GEN_PVAR_237 s P f op)). Qed.
Lemma lem5986308 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term184 A B s P f op) = (term185 A B s P f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem5986303 A B GEN_PVAR_237 s P f op)). Qed.
Lemma lem5986309 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5986310 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term162 A B s P f op) = (term186 A B s P f op).
Proof. exact (MK_COMB (@lem5986309 A) (@lem5986308 A B s P f op)). Qed.
Lemma lem5986311 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term161 A B P f op s) = (term186 A B s P f op).
Proof. exact (TRANS (@lem5986263 A B s P f op) (@lem5986310 A B s P f op)). Qed.
Lemma lem5986312 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5986313 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term187 A B P f op s) = (term188 A B s P f op).
Proof. exact (MK_COMB (@lem5986312 A B op) (@lem5986311 A B s P f op)). Qed.
Lemma lem5986314 {A B : Type'} (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term120 A B P f op) = (term120 A B P f op).
Proof. exact (eq_refl (term120 A B P f op)). Qed.
Lemma lem5986315 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term119 A B s P f op) = (term189 A B s P f op).
Proof. exact (MK_COMB (@lem5986313 A B s P f op) (@lem5986314 A B P f op)). Qed.
Lemma lem5986316 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : ((term114 A B op s P f) = (term119 A B s P f op)) = ((term159 A B s P op f) = (term189 A B s P f op)).
Proof. exact (MK_COMB (@lem5986259 A B s P op f) (@lem5986315 A B s P f op)). Qed.
Lemma lem5986319 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : ((term159 A B s P op f) = (term189 A B s P f op)) = ((term114 A B op s P f) = (term119 A B s P f op)).
Proof. exact (SYM (@lem5986316 A B s P f op)). Qed.
Lemma lem5986327 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term8 t1 t2 t3) = (term7 t1 t2 t3).
Proof. exact (EQ_MP (@lem5986104 t1 t2 t3) (@lem5986103 t1 t2 t3)). Qed.
Lemma lem5986328 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term145 A B s P f x op) = (term190 A B s P f x op).
Proof. exact (@lem5986327 (@IN A x s) (P x) (term143 A B f x op)). Qed.
Lemma lem5986335 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem5986336 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term147 A B GEN_PVAR_237 s P f x op) = (term191 A B GEN_PVAR_237 s P f x op).
Proof. exact (MK_COMB (@lem5986335 A GEN_PVAR_237) (@lem5986328 A B s P f x op)). Qed.
Lemma lem5986337 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5986338 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term149 A B GEN_PVAR_237 s P f op x) = (term192 A B GEN_PVAR_237 s P f op x).
Proof. exact (MK_COMB (@lem5986336 A B GEN_PVAR_237 s P f x op) (@lem5986337 A x)). Qed.
Lemma lem5986339 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term151 A B GEN_PVAR_237 s P f op) = (term193 A B GEN_PVAR_237 s P f op).
Proof. exact (fun_ext (fun x : A => @lem5986338 A B GEN_PVAR_237 s P f op x)). Qed.
Lemma lem5986340 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5986341 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term153 A B GEN_PVAR_237 s P f op) = (term194 A B GEN_PVAR_237 s P f op).
Proof. exact (MK_COMB (@lem5986340 A) (@lem5986339 A B GEN_PVAR_237 s P f op)). Qed.
Lemma lem5986346 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term155 A B s P f op) = (term195 A B s P f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem5986341 A B GEN_PVAR_237 s P f op)). Qed.
Lemma lem5986347 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5986348 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term156 A B s P f op) = (term196 A B s P f op).
Proof. exact (MK_COMB (@lem5986347 A) (@lem5986346 A B s P f op)). Qed.
Lemma lem5986349 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5986350 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term158 A B s P f op) = (term197 A B s P f op).
Proof. exact (MK_COMB (@lem5986349 A B op) (@lem5986348 A B s P f op)). Qed.
Lemma lem5986351 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5986352 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (op : type1400 B) (f : A -> B) : (term159 A B s P op f) = (term198 A B s P op f).
Proof. exact (MK_COMB (@lem5986350 A B s P f op) (@lem5986351 A B f)). Qed.
Lemma lem5986353 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5986354 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (op : type1400 B) (f : A -> B) : (term160 A B s P op f) = (term199 A B s P op f).
Proof. exact (MK_COMB (@lem5986353 B) (@lem5986352 A B s P op f)). Qed.
Lemma lem5986362 {_122099 _122102 : Type'} (P : _122102 -> Prop) (f : _122102 -> _122099) (x : _122102) (a : _122099) : (term22 _122099 _122102 P f x a) = (term23 _122099 _122102 P f x a).
Proof. exact (EQ_MP (@lem5985851 _122099 _122102 P f x a) (@lem5986095 _122099 _122102 P f x a)). Qed.
Lemma lem5986363 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (a : B) : (term200 A B P f x a) = (term201 A B P f x a).
Proof. exact (@lem5986362 B A P f x a). Qed.
Lemma lem5986364 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term172 A B P f x op) = (term202 A B P f x op).
Proof. exact (@lem5986363 A B P f x (@neutral B op)). Qed.
Lemma lem5986369 {A : Type'} (x : A) (s : A -> Prop) : (term173 A x s) = (term173 A x s).
Proof. exact (eq_refl (term173 A x s)). Qed.
Lemma lem5986370 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term175 A B s P f x op) = (term190 A B s P f x op).
Proof. exact (MK_COMB (@lem5986369 A x s) (@lem5986364 A B P f x op)). Qed.
Lemma lem5986373 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem5986374 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term177 A B GEN_PVAR_237 s P f x op) = (term191 A B GEN_PVAR_237 s P f x op).
Proof. exact (MK_COMB (@lem5986373 A GEN_PVAR_237) (@lem5986370 A B s P f x op)). Qed.
Lemma lem5986375 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5986376 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term179 A B GEN_PVAR_237 s P f op x) = (term192 A B GEN_PVAR_237 s P f op x).
Proof. exact (MK_COMB (@lem5986374 A B GEN_PVAR_237 s P f x op) (@lem5986375 A x)). Qed.
Lemma lem5986377 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term181 A B GEN_PVAR_237 s P f op) = (term193 A B GEN_PVAR_237 s P f op).
Proof. exact (fun_ext (fun x : A => @lem5986376 A B GEN_PVAR_237 s P f op x)). Qed.
Lemma lem5986378 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5986379 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term183 A B GEN_PVAR_237 s P f op) = (term194 A B GEN_PVAR_237 s P f op).
Proof. exact (MK_COMB (@lem5986378 A) (@lem5986377 A B GEN_PVAR_237 s P f op)). Qed.
Lemma lem5986384 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term185 A B s P f op) = (term195 A B s P f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem5986379 A B GEN_PVAR_237 s P f op)). Qed.
Lemma lem5986385 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5986386 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term186 A B s P f op) = (term196 A B s P f op).
Proof. exact (MK_COMB (@lem5986385 A) (@lem5986384 A B s P f op)). Qed.
Lemma lem5986387 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5986388 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term188 A B s P f op) = (term197 A B s P f op).
Proof. exact (MK_COMB (@lem5986387 A B op) (@lem5986386 A B s P f op)). Qed.
Lemma lem5986389 {A B : Type'} (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term120 A B P f op) = (term120 A B P f op).
Proof. exact (eq_refl (term120 A B P f op)). Qed.
Lemma lem5986390 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term189 A B s P f op) = (term203 A B s P f op).
Proof. exact (MK_COMB (@lem5986388 A B s P f op) (@lem5986389 A B P f op)). Qed.
Lemma lem5986391 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : ((term159 A B s P op f) = (term189 A B s P f op)) = ((term198 A B s P op f) = (term203 A B s P f op)).
Proof. exact (MK_COMB (@lem5986354 A B s P op f) (@lem5986390 A B s P f op)). Qed.
Lemma lem5986394 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : ((term198 A B s P op f) = (term203 A B s P f op)) = ((term159 A B s P op f) = (term189 A B s P f op)).
Proof. exact (SYM (@lem5986391 A B s P f op)). Qed.
Lemma lem5986396 {A B : Type'} (op : type1400 B) : term6 A B op.
Proof. exact (EQ_MP (@lem5985818 A B op) (@lem5985817 A B op)). Qed.
Lemma lem5986397 {A B : Type'} (op : type1400 B) : term6 A B op.
Proof. exact (@lem5986396 A B op). Qed.
Lemma lem5986398 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term204 A B op.
Proof. exact (@lem5986397 A B op (@lem5986180 B op h1)). Qed.
Lemma lem5986399 {A B : Type'} (op : type1400 B) (h1 : term204 A B op) : term204 A B op.
Proof. exact (h1). Qed.
Lemma lem5986400 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term204 A B op) : term205 A B op f.
Proof. exact (@lem5986399 A B op h1 f). Qed.
Lemma lem5986401 {A B : Type'} (f : A -> B) (op : type1400 B) : (term205 A B op f) = (term206 A B f op).
Proof. exact (eq_refl (term205 A B op f)). Qed.
Lemma lem5986402 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term204 A B op) : term206 A B f op.
Proof. exact (EQ_MP (@lem5986401 A B f op) (@lem5986400 A B f op h1)). Qed.
Lemma lem5986403 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term204 A B op) : term207 A B f op g.
Proof. exact (@lem5986402 A B f op h1 g). Qed.
Lemma lem5986404 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term207 A B f op g) = (term208 A B f op g).
Proof. exact (eq_refl (term207 A B f op g)). Qed.
Lemma lem5986405 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term204 A B op) : term208 A B f op g.
Proof. exact (EQ_MP (@lem5986404 A B f op g) (@lem5986403 A B f g op h1)). Qed.
Lemma lem5986406 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term204 A B op) : term209 A B f op g s.
Proof. exact (@lem5986405 A B f g op h1 s). Qed.
Lemma lem5986407 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term209 A B f op g s) = (term210 A B f op s g).
Proof. exact (eq_refl (term209 A B f op g s)). Qed.
Lemma lem5986408 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term204 A B op) : term210 A B f op s g.
Proof. exact (EQ_MP (@lem5986407 A B f op s g) (@lem5986406 A B f g s op h1)). Qed.
Lemma lem5986409 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term211 A B s f g) : term211 A B s f g.
Proof. exact (h1). Qed.
Lemma lem5986410 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term211 A B s f g) (h2 : term204 A B op) : (@iterate B A op s f) = (@iterate B A op s g).
Proof. exact (@lem5986408 A B f s g op h2 (@lem5986409 A B s f g h1)). Qed.
Lemma lem5986411 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term211 A B s f g) : term212 A B f op s g.
Proof. exact (fun h0 : term204 A B op => @lem5986410 A B s f g op h1 h0). Qed.
Lemma lem5986412 {A B : Type'} (op : type1400 B) (h1 : term204 A B op) : term204 A B op.
Proof. exact (h1). Qed.
Lemma lem5986413 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term211 A B s f g) (h2 : term204 A B op) : (@iterate B A op s f) = (@iterate B A op s g).
Proof. exact (@lem5986411 A B op s f g h1 (@lem5986412 A B op h2)). Qed.
Lemma lem5986414 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term204 A B op) : term210 A B f op s g.
Proof. exact (fun h0 : term211 A B s f g => @lem5986413 A B s f g op h0 h1). Qed.
Lemma lem5986415 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term204 A B op) : term213 A B f op s.
Proof. exact (fun g : A -> B => @lem5986414 A B f s g op h1). Qed.
Lemma lem5986416 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term204 A B op) : term214 A B f op.
Proof. exact (fun s : A -> Prop => @lem5986415 A B f s op h1). Qed.
Lemma lem5986417 {A B : Type'} (op : type1400 B) (h1 : term204 A B op) : term215 A B op.
Proof. exact (fun f : A -> B => @lem5986416 A B f op h1). Qed.
Lemma lem5986418 {A B : Type'} (op : type1400 B) : term216 A B op.
Proof. exact (fun h0 : term204 A B op => @lem5986417 A B op h0). Qed.
Lemma lem5986419 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term215 A B op.
Proof. exact (@lem5986418 A B op (@lem5986398 A B op h1)). Qed.
Lemma lem5986420 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term217 A B op f.
Proof. exact (@lem5986419 A B op h1 f). Qed.
Lemma lem5986421 {A B : Type'} (f : A -> B) (op : type1400 B) : (term217 A B op f) = (term214 A B f op).
Proof. exact (eq_refl (term217 A B op f)). Qed.
Lemma lem5986422 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term214 A B f op.
Proof. exact (EQ_MP (@lem5986421 A B f op) (@lem5986420 A B f op h1)). Qed.
Lemma lem5986423 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term218 A B f op s.
Proof. exact (@lem5986422 A B f op h1 s). Qed.
Lemma lem5986424 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term218 A B f op s) = (term213 A B f op s).
Proof. exact (eq_refl (term218 A B f op s)). Qed.
Lemma lem5986425 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term213 A B f op s.
Proof. exact (EQ_MP (@lem5986424 A B f op s) (@lem5986423 A B f s op h1)). Qed.
Lemma lem5986426 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term219 A B f op s g.
Proof. exact (@lem5986425 A B f s op h1 g). Qed.
Lemma lem5986427 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term219 A B f op s g) = (term210 A B f op s g).
Proof. exact (eq_refl (term219 A B f op s g)). Qed.
Lemma lem5986430 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term210 A B f op s g.
Proof. exact (EQ_MP (@lem5986427 A B f op s g) (@lem5986426 A B f s g op h1)). Qed.
Lemma lem5986431 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term210 A B f op s g.
Proof. exact (@lem5986430 A B f s g op h1). Qed.
Lemma lem5986432 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term220 A B s P f op.
Proof. exact (@lem5986431 A B f (term196 A B s P f op) (term120 A B P f op) op h1). Qed.
Lemma lem5986440 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term221 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5986441 (p : Prop) (q : Prop) (p' : Prop) : term222 p q p'.
Proof. exact (fun q' : Prop => @lem5986440 p q p' q'). Qed.
Lemma lem5986442 (p : Prop) (q : Prop) : term223 p q.
Proof. exact (fun p' : Prop => @lem5986441 p q p'). Qed.
Lemma lem5986443 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : term224 A B s P f op x.
Proof. exact (@lem5986442 (term225 A B x s P f op) ((f x) = (term165 A B P f op x))). Qed.
Lemma lem5986444 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (p' : Prop) : term226 A B s P f op x p'.
Proof. exact (@lem5986443 A B s P f op x p'). Qed.
Lemma lem5986445 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (p' : Prop) : (term226 A B s P f op x p') = (term227 A B s P f op x p').
Proof. exact (eq_refl (term226 A B s P f op x p')). Qed.
Lemma lem5986446 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (p' : Prop) : term227 A B s P f op x p'.
Proof. exact (EQ_MP (@lem5986445 A B s P f op x p') (@lem5986444 A B s P f op x p')). Qed.
Lemma lem5986447 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (p' : Prop) (q' : Prop) : term228 A B s P f op x p' q'.
Proof. exact (@lem5986446 A B s P f op x p' q'). Qed.
Lemma lem5986448 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (p' : Prop) (q' : Prop) : (term228 A B s P f op x p' q') = (term229 A B s P f op x p' q').
Proof. exact (eq_refl (term228 A B s P f op x p' q')). Qed.
Lemma lem5986449 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (p' : Prop) (q' : Prop) : term229 A B s P f op x p' q'.
Proof. exact (EQ_MP (@lem5986448 A B s P f op x p' q') (@lem5986447 A B s P f op x p' q')). Qed.
Lemma lem5986451 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5985808 _83095 p x) (@lem5985807 _83095 p x)). Qed.
Lemma lem5986452 {A : Type'} (p : A -> Prop) (x : A) : (term4 A x p) = (p x).
Proof. exact (@lem5986451 A p x). Qed.
Lemma lem5986453 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term230 A B x s P f op) = (term231 A B s P f op x).
Proof. exact (@lem5986452 A (term232 A B s P f op) x). Qed.
Lemma lem5986454 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term231 A B s P f op x) = (term190 A B s P f x op).
Proof. exact (eq_refl (term231 A B s P f op x)). Qed.
Lemma lem5986455 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem5986456 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term233 A B GEN_PVAR_237 s P f op x) = (term191 A B GEN_PVAR_237 s P f x op).
Proof. exact (MK_COMB (@lem5986455 A GEN_PVAR_237) (@lem5986454 A B s P f x op)). Qed.
Lemma lem5986457 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5986458 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term234 A B GEN_PVAR_237 s P f op x) = (term192 A B GEN_PVAR_237 s P f op x).
Proof. exact (MK_COMB (@lem5986456 A B GEN_PVAR_237 s P f x op) (@lem5986457 A x)). Qed.
Lemma lem5986459 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term235 A B GEN_PVAR_237 s P f op) = (term193 A B GEN_PVAR_237 s P f op).
Proof. exact (fun_ext (fun x : A => @lem5986458 A B GEN_PVAR_237 s P f op x)). Qed.
Lemma lem5986460 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5986461 {A B : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term236 A B GEN_PVAR_237 s P f op) = (term194 A B GEN_PVAR_237 s P f op).
Proof. exact (MK_COMB (@lem5986460 A) (@lem5986459 A B GEN_PVAR_237 s P f op)). Qed.
Lemma lem5986462 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term237 A B s P f op) = (term195 A B s P f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem5986461 A B GEN_PVAR_237 s P f op)). Qed.
Lemma lem5986463 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5986464 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term238 A B s P f op) = (term196 A B s P f op).
Proof. exact (MK_COMB (@lem5986463 A) (@lem5986462 A B s P f op)). Qed.
Lemma lem5986465 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5986466 {A B : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term230 A B x s P f op) = (term225 A B x s P f op).
Proof. exact (MK_COMB (@lem5986465 A x) (@lem5986464 A B s P f op)). Qed.
Lemma lem5986467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5986468 {A B : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term239 A B x s P f op) = (term240 A B x s P f op).
Proof. exact (MK_COMB (@lem5986467) (@lem5986466 A B x s P f op)). Qed.
Lemma lem5986469 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term231 A B s P f op x) = (term190 A B s P f x op).
Proof. exact (eq_refl (term231 A B s P f op x)). Qed.
Lemma lem5986470 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term230 A B x s P f op) = (term231 A B s P f op x)) = ((term225 A B x s P f op) = (term190 A B s P f x op)).
Proof. exact (MK_COMB (@lem5986468 A B x s P f op) (@lem5986469 A B s P f x op)). Qed.
Lemma lem5986471 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term225 A B x s P f op) = (term190 A B s P f x op).
Proof. exact (EQ_MP (@lem5986470 A B s P f x op) (@lem5986453 A B s P f op x)). Qed.
Lemma lem5986478 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (q' : Prop) : term241 A B s P f x op q'.
Proof. exact (@lem5986449 A B s P f op x (term190 A B s P f x op) q'). Qed.
Lemma lem5986479 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (q' : Prop) : term242 A B s P f x op q'.
Proof. exact (@lem5986478 A B s P f x op q' (@lem5986471 A B s P f x op)). Qed.
Lemma lem5986480 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term190 A B s P f x op) : term190 A B s P f x op.
Proof. exact (h1). Qed.
Lemma lem5986481 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term190 A B s P f x op) : term202 A B P f x op.
Proof. exact (proj2 (@lem5986480 A B s P f x op h1)). Qed.
Lemma lem5986496 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term190 A B s P f x op) : P x.
Proof. exact (proj1 (@lem5986481 A B s P f x op h1)). Qed.
Lemma lem5986497 {A : Type'} (P : A -> Prop) (x : A) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem5986505 {A B : Type'} (f : A -> B) (y : A) : (term163 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5986506 {A B : Type'} (f : A -> B) (y : A) : (term163 A B f y) = (f y).
Proof. exact (@lem5986505 A B f y). Qed.
Lemma lem5986507 {A B : Type'} (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term164 A B P f op x) = (term165 A B P f op x).
Proof. exact (@lem5986506 A B (term120 A B P f op) x). Qed.
Lemma lem5986508 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term165 A B P f op x) = (term166 A B P f x op).
Proof. exact (eq_refl (term165 A B P f op x)). Qed.
Lemma lem5986509 {A B : Type'} (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term167 A B P f op) = (term120 A B P f op).
Proof. exact (fun_ext (fun x : A => @lem5986508 A B P f x op)). Qed.
Lemma lem5986510 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5986511 {A B : Type'} (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term164 A B P f op x) = (term165 A B P f op x).
Proof. exact (MK_COMB (@lem5986509 A B P f op) (@lem5986510 A x)). Qed.
Lemma lem5986512 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5986513 {A B : Type'} (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term168 A B P f op x) = (term169 A B P f op x).
Proof. exact (MK_COMB (@lem5986512 B) (@lem5986511 A B P f op x)). Qed.
Lemma lem5986514 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term165 A B P f op x) = (term166 A B P f x op).
Proof. exact (eq_refl (term165 A B P f op x)). Qed.
Lemma lem5986515 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term164 A B P f op x) = (term165 A B P f op x)) = ((term165 A B P f op x) = (term166 A B P f x op)).
Proof. exact (MK_COMB (@lem5986513 A B P f op x) (@lem5986514 A B P f x op)). Qed.
Lemma lem5986516 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term165 A B P f op x) = (term166 A B P f x op).
Proof. exact (EQ_MP (@lem5986515 A B P f x op) (@lem5986507 A B P f op x)). Qed.
Lemma lem5986518 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term243 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5986519 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term244 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5986518 _2963 g t e g' t' e'). Qed.
Lemma lem5986520 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term245 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5986519 _2963 g t e g' t'). Qed.
Lemma lem5986521 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term246 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5986520 _2963 g t e g'). Qed.
Lemma lem5986522 {B : Type'} (g : Prop) (t : B) (e : B) : term246 B g t e.
Proof. exact (@lem5986521 B g t e). Qed.
Lemma lem5986523 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : term247 A B P f x op.
Proof. exact (@lem5986522 B (P x) (f x) (@neutral B op)). Qed.
Lemma lem5986524 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (g' : Prop) : term248 A B P f x op g'.
Proof. exact (@lem5986523 A B P f x op g'). Qed.
Lemma lem5986525 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (g' : Prop) : (term248 A B P f x op g') = (term249 A B P f x op g').
Proof. exact (eq_refl (term248 A B P f x op g')). Qed.
Lemma lem5986526 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (g' : Prop) : term249 A B P f x op g'.
Proof. exact (EQ_MP (@lem5986525 A B P f x op g') (@lem5986524 A B P f x op g')). Qed.
Lemma lem5986527 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (g' : Prop) (t' : B) : term250 A B P f x op g' t'.
Proof. exact (@lem5986526 A B P f x op g' t'). Qed.
Lemma lem5986528 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (g' : Prop) (t' : B) : (term250 A B P f x op g' t') = (term251 A B P f x op g' t').
Proof. exact (eq_refl (term250 A B P f x op g' t')). Qed.
Lemma lem5986529 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (g' : Prop) (t' : B) : term251 A B P f x op g' t'.
Proof. exact (EQ_MP (@lem5986528 A B P f x op g' t') (@lem5986527 A B P f x op g' t')). Qed.
Lemma lem5986530 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (g' : Prop) (t' : B) (e' : B) : term252 A B P f x op g' t' e'.
Proof. exact (@lem5986529 A B P f x op g' t' e'). Qed.
Lemma lem5986531 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (g' : Prop) (t' : B) (e' : B) : (term252 A B P f x op g' t' e') = (term253 A B P f x op g' t' e').
Proof. exact (eq_refl (term252 A B P f x op g' t' e')). Qed.
Lemma lem5986532 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (g' : Prop) (t' : B) (e' : B) : term253 A B P f x op g' t' e'.
Proof. exact (EQ_MP (@lem5986531 A B P f x op g' t' e') (@lem5986530 A B P f x op g' t' e')). Qed.
Lemma lem5986534 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term190 A B s P f x op) : (P x) = True.
Proof. exact (EQ_MP (@lem5986497 A P x) (@lem5986496 A B s P f x op h1)). Qed.
Lemma lem5986535 {A B : Type'} (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (t' : B) (e' : B) : term254 A B P f x op t' e'.
Proof. exact (@lem5986532 A B P f x op True t' e'). Qed.
Lemma lem5986536 {A B : Type'} (t' : B) (e' : B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term190 A B s P f x op) : term255 A B P f x op t' e'.
Proof. exact (@lem5986535 A B P f x op t' e' (@lem5986534 A B s P f x op h1)). Qed.
Lemma lem5986542 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem5986543 {A B : Type'} (f : A -> B) (x : A) : term256 A B f x.
Proof. exact (fun h0 : True => @lem5986542 A B f x). Qed.
Lemma lem5986544 {A B : Type'} (e' : B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term190 A B s P f x op) : term257 A B P op f x e'.
Proof. exact (@lem5986536 A B (f x) e' s P f x op h1). Qed.
Lemma lem5986545 {A B : Type'} (e' : B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term190 A B s P f x op) : term258 A B P op f x e'.
Proof. exact (@lem5986544 A B e' s P f x op h1 (@lem5986543 A B f x)). Qed.
Lemma lem5986549 {B : Type'} (op : type1400 B) : (@neutral B op) = (@neutral B op).
Proof. exact (eq_refl (@neutral B op)). Qed.
Lemma lem5986550 {B : Type'} (op : type1400 B) : term259 B op.
Proof. exact (fun h0 : ~ True => @lem5986549 B op). Qed.
Lemma lem5986551 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term190 A B s P f x op) : term260 A B P f x op.
Proof. exact (@lem5986545 A B (@neutral B op) s P f x op h1). Qed.
Lemma lem5986552 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term190 A B s P f x op) : (term166 A B P f x op) = (term261 A B f x op).
Proof. exact (@lem5986551 A B s P f x op h1 (@lem5986550 B op)). Qed.
Lemma lem5986554 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5986555 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5986554 B t2 t1). Qed.
Lemma lem5986556 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term261 A B f x op) = (f x).
Proof. exact (@lem5986555 B (@neutral B op) (f x)). Qed.
Lemma lem5986557 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term190 A B s P f x op) : (term166 A B P f x op) = (f x).
Proof. exact (TRANS (@lem5986552 A B s P f x op h1) (@lem5986556 A B op f x)). Qed.
Lemma lem5986558 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term190 A B s P f x op) : (term165 A B P f op x) = (f x).
Proof. exact (TRANS (@lem5986516 A B P f x op) (@lem5986557 A B s P f x op h1)). Qed.
Lemma lem5986559 {A B : Type'} (f : A -> B) (x : A) : (term262 A B f x) = (term262 A B f x).
Proof. exact (eq_refl (term262 A B f x)). Qed.
Lemma lem5986560 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term190 A B s P f x op) : ((f x) = (term165 A B P f op x)) = ((f x) = (f x)).
Proof. exact (MK_COMB (@lem5986559 A B f x) (@lem5986558 A B s P f x op h1)). Qed.
Lemma lem5986562 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5986563 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem5986562 B x). Qed.
Lemma lem5986564 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (f x)) = True.
Proof. exact (@lem5986563 B (f x)). Qed.
Lemma lem5986565 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term190 A B s P f x op) : ((f x) = (term165 A B P f op x)) = True.
Proof. exact (TRANS (@lem5986560 A B s P f x op h1) (@lem5986564 A B f x)). Qed.
Lemma lem5986566 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : term263 A B s P f op x.
Proof. exact (fun h0 : term190 A B s P f x op => @lem5986565 A B s P f x op h0). Qed.
Lemma lem5986567 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : term264 A B s P f x op.
Proof. exact (@lem5986479 A B s P f x op True). Qed.
Lemma lem5986568 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term265 A B s P f op x) = (term266 A B s P f x op).
Proof. exact (@lem5986567 A B s P f x op (@lem5986566 A B s P f op x)). Qed.
Lemma lem5986570 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5986571 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term266 A B s P f x op) = True.
Proof. exact (@lem5986570 (term190 A B s P f x op)). Qed.
Lemma lem5986572 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term265 A B s P f op x) = True.
Proof. exact (TRANS (@lem5986568 A B s P f x op) (@lem5986571 A B s P f x op)). Qed.
Lemma lem5986573 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term267 A B s P f op) = (term268 A).
Proof. exact (fun_ext (fun x : A => @lem5986572 A B s P f op x)). Qed.
Lemma lem5986574 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5986575 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term269 A B s P f op) = (term270 A).
Proof. exact (MK_COMB (@lem5986574 A) (@lem5986573 A B s P f op)). Qed.
Lemma lem5986577 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5986578 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (@lem5986577 A t). Qed.
Lemma lem5986579 {A : Type'} : (term270 A) = True.
Proof. exact (@lem5986578 A True). Qed.
Lemma lem5986580 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term269 A B s P f op) = True.
Proof. exact (TRANS (@lem5986575 A B s P f op) (@lem5986579 A)). Qed.
Lemma lem5986581 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : True = (term269 A B s P f op).
Proof. exact (SYM (@lem5986580 A B s P f op)). Qed.
Lemma lem5986582 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : term269 A B s P f op.
Proof. exact (EQ_MP (@lem5986581 A B s P f op) (@lem0)). Qed.
Lemma lem5986583 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term198 A B s P op f) = (term203 A B s P f op).
Proof. exact (@lem5986432 A B s P f op h1 (@lem5986582 A B s P f op)). Qed.
Lemma lem5986584 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term159 A B s P op f) = (term189 A B s P f op).
Proof. exact (EQ_MP (@lem5986394 A B s P f op) (@lem5986583 A B s P f op h1)). Qed.
Lemma lem5986585 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term114 A B op s P f) = (term119 A B s P f op).
Proof. exact (EQ_MP (@lem5986319 A B s P f op) (@lem5986584 A B s P f op h1)). Qed.
Lemma lem5986586 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term113 A B op s P f) = (term118 A B s P f op).
Proof. exact (EQ_MP (@lem5986194 A B s P f op) (@lem5986585 A B s P f op h1)). Qed.
Lemma lem5986591 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term271 A B s P op.
Proof. exact (fun f : A -> B => @lem5986586 A B s P f op h1). Qed.
Lemma lem5986596 {A B : Type'} (P : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term272 A B P op.
Proof. exact (fun s : A -> Prop => @lem5986591 A B s P op h1). Qed.
Lemma lem5986601 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term273 A B op.
Proof. exact (fun P : A -> Prop => @lem5986596 A B P op h1). Qed.
Lemma lem5986602 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = (term273 A B op).
Proof. exact (prop_ext (fun h2 : @monoidal B op => @lem5986601 A B op h1) (fun h2 : term273 A B op => @lem5986180 B op h1)). Qed.
Lemma lem5986603 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term273 A B op.
Proof. exact (EQ_MP (@lem5986602 A B op h1) (@lem5986180 B op h1)). Qed.
Lemma lem5986604 {A B : Type'} (op : type1400 B) : term274 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem5986603 A B op h0). Qed.
Lemma lem5986609 {A B : Type'} : term275 A B.
Proof. exact (fun op : type1400 B => @lem5986604 A B op). Qed.
