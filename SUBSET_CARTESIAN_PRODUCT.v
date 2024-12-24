Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_CARTESIAN_PRODUCT_term_abbrevs.
Require Import CARTESIAN_PRODUCT_EQ_EMPTY_spec.
Require Import DISJ_ACI_spec.
Require Import EMPTY_SUBSET_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import EXTENSIONAL_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import SUBSET_spec.
Require Import cartesian_product_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18934_spec.
Require Import thm18935_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184714_spec.
Require Import thm3184717_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4417744 {_83152 : Type'} : term0 _83152.
Proof. exact (EQ_MP (@lem3184717 _83152) (@lem3184714 _83152)). Qed.
Lemma lem4417745 {_83152 : Type'} (p : _83152 -> Prop) : term1 _83152 p.
Proof. exact (@lem4417744 _83152 p). Qed.
Lemma lem4417746 {_83152 : Type'} (p : _83152 -> Prop) : (term1 _83152 p) = (term2 _83152 p).
Proof. exact (eq_refl (term1 _83152 p)). Qed.
Lemma lem4417747 {_83152 : Type'} (p : _83152 -> Prop) : term2 _83152 p.
Proof. exact (EQ_MP (@lem4417746 _83152 p) (@lem4417745 _83152 p)). Qed.
Lemma lem4417748 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term3 _83152 p x.
Proof. exact (@lem4417747 _83152 p x). Qed.
Lemma lem4417749 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term3 _83152 p x) = ((term4 _83152 p x) = (p x)).
Proof. exact (eq_refl (term3 _83152 p x)). Qed.
Lemma lem4417772 {A B : Type'} (s : A -> Prop) : term5 A B s.
Proof. exact (@lem4382798 A B s). Qed.
Lemma lem4417773 {A B : Type'} (s : A -> Prop) : (term5 A B s) = ((@EXTENSIONAL A B s) = (term6 A B s)).
Proof. exact (eq_refl (term5 A B s)). Qed.
Lemma lem4417775 {A : Type'} (P : A -> Prop) : term7 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem4417776 {A : Type'} (P : A -> Prop) : (term7 A P) = (term8 A P).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem4417777 {A : Type'} (P : A -> Prop) : term8 A P.
Proof. exact (EQ_MP (@lem4417776 A P) (@lem4417775 A P)). Qed.
Lemma lem4417778 {A : Type'} (P : A -> Prop) (Q : Prop) : term9 A P Q.
Proof. exact (@lem4417777 A P Q). Qed.
Lemma lem4417779 {A : Type'} (P : A -> Prop) (Q : Prop) : (term9 A P Q) = ((term10 A P Q) = (term11 A P Q)).
Proof. exact (eq_refl (term9 A P Q)). Qed.
Lemma lem4417781 {A B : Type'} (P : type1413 A B) : term12 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem4417782 {A B : Type'} (P : type1413 A B) : (term12 A B P) = ((term13 A B P) = (term14 A B P)).
Proof. exact (eq_refl (term12 A B P)). Qed.
Lemma lem4417807 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term15 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4417808 {_106233 : Type'} (s : _106233 -> Prop) (t : _106233 -> Prop) : (s = t) = (term15 _106233 s t).
Proof. exact (@lem4417807 _106233 s t). Qed.
Lemma lem4417809 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : ((s i) = (@EMPTY _106233)) = (term16 _106233 _106250 s i).
Proof. exact (@lem4417808 _106233 (s i) (@EMPTY _106233)). Qed.
Lemma lem4417818 {_106250 : Type'} (i : _106250) (k : _106250 -> Prop) : (term17 _106250 i k) = (term17 _106250 i k).
Proof. exact (eq_refl (term17 _106250 i k)). Qed.
Lemma lem4417819 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term18 _106233 _106250 k s i) = (term19 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4417818 _106250 i k) (@lem4417809 _106233 _106250 s i)). Qed.
Lemma lem4417822 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term20 _106233 _106250 k s) = (term21 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4417819 _106233 _106250 k s i)). Qed.
Lemma lem4417823 {_106250 : Type'} : (@ex _106250) = (@ex _106250).
Proof. exact (eq_refl (@ex _106250)). Qed.
Lemma lem4417824 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term22 _106233 _106250 k s) = (term23 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4417823 _106250) (@lem4417822 _106233 _106250 k s)). Qed.
Lemma lem4417829 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4417830 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term24 _106233 _106250 k s) = (term25 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4417829) (@lem4417824 _106233 _106250 k s)). Qed.
Lemma lem4417831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4417832 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term26 _106233 _106250 k s) = (term27 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4417831) (@lem4417830 _106233 _106250 k s)). Qed.
Lemma lem4417843 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term28 _106233 _106250 k s) = (term28 _106233 _106250 k s).
Proof. exact (eq_refl (term28 _106233 _106250 k s)). Qed.
Lemma lem4417844 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term24 _106233 _106250 k s) = (term28 _106233 _106250 k s)) = ((term25 _106233 _106250 k s) = (term28 _106233 _106250 k s)).
Proof. exact (MK_COMB (@lem4417832 _106233 _106250 k s) (@lem4417843 _106233 _106250 k s)). Qed.
Lemma lem4417849 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term25 _106233 _106250 k s) = (term28 _106233 _106250 k s)) = ((term24 _106233 _106250 k s) = (term28 _106233 _106250 k s)).
Proof. exact (SYM (@lem4417844 _106233 _106250 k s)). Qed.
Lemma lem4417859 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4417860 {_106250 : Type'} (P : _106250 -> Prop) (x : _106250) : (@IN _106250 x P) = (P x).
Proof. exact (@lem4417859 _106250 P x). Qed.
Lemma lem4417861 {_106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (@IN _106250 i k) = (k i).
Proof. exact (@lem4417860 _106250 k i). Qed.
Lemma lem4417862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4417863 {_106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term17 _106250 i k) = (term29 _106250 k i).
Proof. exact (MK_COMB (@lem4417862) (@lem4417861 _106250 k i)). Qed.
Lemma lem4417871 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4417872 {_106233 : Type'} (P : _106233 -> Prop) (x : _106233) : (@IN _106233 x P) = (P x).
Proof. exact (@lem4417871 _106233 P x). Qed.
Lemma lem4417873 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term30 _106233 _106250 x s i) = (s i x).
Proof. exact (@lem4417872 _106233 (s i) x). Qed.
Lemma lem4417874 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4417875 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term31 _106233 _106250 x s i) = (term32 _106233 _106250 s i x).
Proof. exact (MK_COMB (@lem4417874) (@lem4417873 _106233 _106250 s i x)). Qed.
Lemma lem4417877 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4417878 {_106233 : Type'} (x : _106233) : (@IN _106233 x (@EMPTY _106233)) = False.
Proof. exact (@lem4417877 _106233 x). Qed.
Lemma lem4417879 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : ((term30 _106233 _106250 x s i) = (@IN _106233 x (@EMPTY _106233))) = ((s i x) = False).
Proof. exact (MK_COMB (@lem4417875 _106233 _106250 s i x) (@lem4417878 _106233 x)). Qed.
Lemma lem4417881 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4417882 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : ((s i x) = False) = (term33 _106233 _106250 s i x).
Proof. exact (@lem4417881 (s i x)). Qed.
Lemma lem4417883 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : ((term30 _106233 _106250 x s i) = (@IN _106233 x (@EMPTY _106233))) = (term33 _106233 _106250 s i x).
Proof. exact (TRANS (@lem4417879 _106233 _106250 s i x) (@lem4417882 _106233 _106250 s i x)). Qed.
Lemma lem4417884 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term34 _106233 _106250 s i) = (term35 _106233 _106250 s i).
Proof. exact (fun_ext (fun x : _106233 => @lem4417883 _106233 _106250 s i x)). Qed.
Lemma lem4417885 {_106233 : Type'} : (@all _106233) = (@all _106233).
Proof. exact (eq_refl (@all _106233)). Qed.
Lemma lem4417886 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term16 _106233 _106250 s i) = (term36 _106233 _106250 s i).
Proof. exact (MK_COMB (@lem4417885 _106233) (@lem4417884 _106233 _106250 s i)). Qed.
Lemma lem4417891 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term19 _106233 _106250 k s i) = (term37 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4417863 _106250 k i) (@lem4417886 _106233 _106250 s i)). Qed.
Lemma lem4417894 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term21 _106233 _106250 k s) = (term38 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4417891 _106233 _106250 k s i)). Qed.
Lemma lem4417895 {_106250 : Type'} : (@ex _106250) = (@ex _106250).
Proof. exact (eq_refl (@ex _106250)). Qed.
Lemma lem4417896 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term23 _106233 _106250 k s) = (term39 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4417895 _106250) (@lem4417894 _106233 _106250 k s)). Qed.
Lemma lem4417901 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4417902 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term25 _106233 _106250 k s) = (term40 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4417901) (@lem4417896 _106233 _106250 k s)). Qed.
Lemma lem4417903 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4417904 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term27 _106233 _106250 k s) = (term41 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4417903) (@lem4417902 _106233 _106250 k s)). Qed.
Lemma lem4417916 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4417917 {_106250 : Type'} (P : _106250 -> Prop) (x : _106250) : (@IN _106250 x P) = (P x).
Proof. exact (@lem4417916 _106250 P x). Qed.
Lemma lem4417918 {_106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (@IN _106250 i k) = (k i).
Proof. exact (@lem4417917 _106250 k i). Qed.
Lemma lem4417919 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4417920 {_106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term42 _106250 i k) = (term43 _106250 k i).
Proof. exact (MK_COMB (@lem4417919) (@lem4417918 _106250 k i)). Qed.
Lemma lem4417922 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4417923 {_106233 : Type'} (P : _106233 -> Prop) (x : _106233) : (@IN _106233 x P) = (P x).
Proof. exact (@lem4417922 _106233 P x). Qed.
Lemma lem4417924 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term30 _106233 _106250 a s i) = (s i a).
Proof. exact (@lem4417923 _106233 (s i) a). Qed.
Lemma lem4417925 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term44 _106233 _106250 k a s i) = (term45 _106233 _106250 k s i a).
Proof. exact (MK_COMB (@lem4417920 _106250 k i) (@lem4417924 _106233 _106250 s i a)). Qed.
Lemma lem4417928 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term46 _106233 _106250 k s i) = (term47 _106233 _106250 k s i).
Proof. exact (fun_ext (fun a : _106233 => @lem4417925 _106233 _106250 k s i a)). Qed.
Lemma lem4417929 {_106233 : Type'} : (@ex _106233) = (@ex _106233).
Proof. exact (eq_refl (@ex _106233)). Qed.
Lemma lem4417930 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term48 _106233 _106250 k s i) = (term49 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4417929 _106233) (@lem4417928 _106233 _106250 k s i)). Qed.
Lemma lem4417935 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term50 _106233 _106250 k s) = (term51 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4417930 _106233 _106250 k s i)). Qed.
Lemma lem4417936 {_106250 : Type'} : (@all _106250) = (@all _106250).
Proof. exact (eq_refl (@all _106250)). Qed.
Lemma lem4417937 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term28 _106233 _106250 k s) = (term52 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4417936 _106250) (@lem4417935 _106233 _106250 k s)). Qed.
Lemma lem4417942 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term25 _106233 _106250 k s) = (term28 _106233 _106250 k s)) = ((term40 _106233 _106250 k s) = (term52 _106233 _106250 k s)).
Proof. exact (MK_COMB (@lem4417904 _106233 _106250 k s) (@lem4417937 _106233 _106250 k s)). Qed.
Lemma lem4417945 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term40 _106233 _106250 k s) = (term52 _106233 _106250 k s)) = ((term25 _106233 _106250 k s) = (term28 _106233 _106250 k s)).
Proof. exact (SYM (@lem4417942 _106233 _106250 k s)). Qed.
Lemma lem4417947 (p : Prop) : p = (term53 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4417948 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term40 _106233 _106250 k s) = (term52 _106233 _106250 k s)) = (term54 _106233 _106250 k s).
Proof. exact (@lem4417947 ((term40 _106233 _106250 k s) = (term52 _106233 _106250 k s))). Qed.
Lemma lem4417949 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term54 _106233 _106250 k s) = ((term40 _106233 _106250 k s) = (term52 _106233 _106250 k s)).
Proof. exact (SYM (@lem4417948 _106233 _106250 k s)). Qed.
Lemma lem4417950 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term55 _106233 _106250 k s) : term55 _106233 _106250 k s.
Proof. exact (h1). Qed.
Lemma lem4417953 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term54 _106233 _106250 k s) : term54 _106233 _106250 k s.
Proof. exact (h1). Qed.
Lemma lem4417954 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : term56 _106233 _106250 k s.
Proof. exact (fun h0 : term54 _106233 _106250 k s => @lem4417953 _106233 _106250 k s h0). Qed.
Lemma lem4417955 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term56 _106233 _106250 k s) : term56 _106233 _106250 k s.
Proof. exact (h1). Qed.
Lemma lem4417956 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term54 _106233 _106250 k s) : term54 _106233 _106250 k s.
Proof. exact (h1). Qed.
Lemma lem4417957 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term54 _106233 _106250 k s) (h2 : term56 _106233 _106250 k s) : term54 _106233 _106250 k s.
Proof. exact (@lem4417955 _106233 _106250 k s h2 (@lem4417956 _106233 _106250 k s h1)). Qed.
Lemma lem4417958 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term54 _106233 _106250 k s) : term57 _106233 _106250 k s.
Proof. exact (fun h0 : term56 _106233 _106250 k s => @lem4417957 _106233 _106250 k s h1 h0). Qed.
Lemma lem4417959 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term56 _106233 _106250 k s) : term56 _106233 _106250 k s.
Proof. exact (h1). Qed.
Lemma lem4417960 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term54 _106233 _106250 k s) (h2 : term56 _106233 _106250 k s) : term54 _106233 _106250 k s.
Proof. exact (@lem4417958 _106233 _106250 k s h1 (@lem4417959 _106233 _106250 k s h2)). Qed.
Lemma lem4417961 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term56 _106233 _106250 k s) : term56 _106233 _106250 k s.
Proof. exact (fun h0 : term54 _106233 _106250 k s => @lem4417960 _106233 _106250 k s h0 h1). Qed.
Lemma lem4417962 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : term58 _106233 _106250 k s.
Proof. exact (fun h0 : term56 _106233 _106250 k s => @lem4417961 _106233 _106250 k s h0). Qed.
Lemma lem4417965 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : term56 _106233 _106250 k s.
Proof. exact (@lem4417962 _106233 _106250 k s (@lem4417954 _106233 _106250 k s)). Qed.
Lemma lem4417966 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : term56 _106233 _106250 k s.
Proof. exact (@lem4417965 _106233 _106250 k s). Qed.
Lemma lem4417976 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4417977 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term54 _106233 _106250 k s) = (term59 _106233 _106250 k s).
Proof. exact (@lem4417976 (term55 _106233 _106250 k s)). Qed.
Lemma lem4417979 (t : Prop) : (term60 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4417980 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term59 _106233 _106250 k s) = ((term40 _106233 _106250 k s) = (term52 _106233 _106250 k s)).
Proof. exact (@lem4417979 ((term40 _106233 _106250 k s) = (term52 _106233 _106250 k s))). Qed.
Lemma lem4417981 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term54 _106233 _106250 k s) = ((term40 _106233 _106250 k s) = (term52 _106233 _106250 k s)).
Proof. exact (TRANS (@lem4417977 _106233 _106250 k s) (@lem4417980 _106233 _106250 k s)). Qed.
Lemma lem4418026 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) : (term61 _106233 _106250 s) = (term62 _106233 _106250 s).
Proof. exact (fun_ext (fun k : _106250 -> Prop => @lem4417981 _106233 _106250 k s)). Qed.
Lemma lem4418027 {_106250 : Type'} : (@all (_106250 -> Prop)) = (@all (_106250 -> Prop)).
Proof. exact (eq_refl (@all (_106250 -> Prop))). Qed.
Lemma lem4418028 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) : (term63 _106233 _106250 s) = (term64 _106233 _106250 s).
Proof. exact (MK_COMB (@lem4418027 _106250) (@lem4418026 _106233 _106250 s)). Qed.
Lemma lem4418033 {_106233 _106250 : Type'} : (term65 _106233 _106250) = (term66 _106233 _106250).
Proof. exact (fun_ext (fun s : type1470 _106233 _106250 => @lem4418028 _106233 _106250 s)). Qed.
Lemma lem4418034 {_106233 _106250 : Type'} : (@all (_106250 -> _106233 -> Prop)) = (@all (_106250 -> _106233 -> Prop)).
Proof. exact (eq_refl (@all (_106250 -> _106233 -> Prop))). Qed.
Lemma lem4418043 {_106233 _106250 : Type'} : (term67 _106233 _106250) = (term68 _106233 _106250).
Proof. exact (MK_COMB (@lem4418034 _106233 _106250) (@lem4418033 _106233 _106250)). Qed.
Lemma lem4418048 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term45 _106233 _106250 k s i a) = (term45 _106233 _106250 k s i a).
Proof. exact (eq_refl (term45 _106233 _106250 k s i a)). Qed.
Lemma lem4418049 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term47 _106233 _106250 k s i) = (term47 _106233 _106250 k s i).
Proof. exact (fun_ext (fun a : _106233 => @lem4418048 _106233 _106250 k s i a)). Qed.
Lemma lem4418050 {_106233 : Type'} : (@ex _106233) = (@ex _106233).
Proof. exact (eq_refl (@ex _106233)). Qed.
Lemma lem4418051 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term49 _106233 _106250 k s i) = (term49 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418050 _106233) (@lem4418049 _106233 _106250 k s i)). Qed.
Lemma lem4418052 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term51 _106233 _106250 k s) = (term51 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418051 _106233 _106250 k s i)). Qed.
Lemma lem4418053 {_106250 : Type'} : (@all _106250) = (@all _106250).
Proof. exact (eq_refl (@all _106250)). Qed.
Lemma lem4418054 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term52 _106233 _106250 k s) = (term52 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418053 _106250) (@lem4418052 _106233 _106250 k s)). Qed.
Lemma lem4418057 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term33 _106233 _106250 s i x) = (term33 _106233 _106250 s i x).
Proof. exact (eq_refl (term33 _106233 _106250 s i x)). Qed.
Lemma lem4418058 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term35 _106233 _106250 s i) = (term35 _106233 _106250 s i).
Proof. exact (fun_ext (fun x : _106233 => @lem4418057 _106233 _106250 s i x)). Qed.
Lemma lem4418059 {_106233 : Type'} : (@all _106233) = (@all _106233).
Proof. exact (eq_refl (@all _106233)). Qed.
Lemma lem4418060 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term36 _106233 _106250 s i) = (term36 _106233 _106250 s i).
Proof. exact (MK_COMB (@lem4418059 _106233) (@lem4418058 _106233 _106250 s i)). Qed.
Lemma lem4418063 {_106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term29 _106250 k i) = (term29 _106250 k i).
Proof. exact (eq_refl (term29 _106250 k i)). Qed.
Lemma lem4418064 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term37 _106233 _106250 k s i) = (term37 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418063 _106250 k i) (@lem4418060 _106233 _106250 s i)). Qed.
Lemma lem4418065 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term38 _106233 _106250 k s) = (term38 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418064 _106233 _106250 k s i)). Qed.
Lemma lem4418066 {_106250 : Type'} : (@ex _106250) = (@ex _106250).
Proof. exact (eq_refl (@ex _106250)). Qed.
Lemma lem4418067 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term39 _106233 _106250 k s) = (term39 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418066 _106250) (@lem4418065 _106233 _106250 k s)). Qed.
Lemma lem4418068 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4418069 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term40 _106233 _106250 k s) = (term40 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418068) (@lem4418067 _106233 _106250 k s)). Qed.
Lemma lem4418070 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4418071 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term41 _106233 _106250 k s) = (term41 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418070) (@lem4418069 _106233 _106250 k s)). Qed.
Lemma lem4418072 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term40 _106233 _106250 k s) = (term52 _106233 _106250 k s)) = ((term40 _106233 _106250 k s) = (term52 _106233 _106250 k s)).
Proof. exact (MK_COMB (@lem4418071 _106233 _106250 k s) (@lem4418054 _106233 _106250 k s)). Qed.
Lemma lem4418073 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) : (term62 _106233 _106250 s) = (term62 _106233 _106250 s).
Proof. exact (fun_ext (fun k : _106250 -> Prop => @lem4418072 _106233 _106250 k s)). Qed.
Lemma lem4418074 {_106250 : Type'} : (@all (_106250 -> Prop)) = (@all (_106250 -> Prop)).
Proof. exact (eq_refl (@all (_106250 -> Prop))). Qed.
Lemma lem4418075 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) : (term64 _106233 _106250 s) = (term64 _106233 _106250 s).
Proof. exact (MK_COMB (@lem4418074 _106250) (@lem4418073 _106233 _106250 s)). Qed.
Lemma lem4418076 {_106233 _106250 : Type'} : (term66 _106233 _106250) = (term66 _106233 _106250).
Proof. exact (fun_ext (fun s : type1470 _106233 _106250 => @lem4418075 _106233 _106250 s)). Qed.
Lemma lem4418077 {_106233 _106250 : Type'} : (@all (_106250 -> _106233 -> Prop)) = (@all (_106250 -> _106233 -> Prop)).
Proof. exact (eq_refl (@all (_106250 -> _106233 -> Prop))). Qed.
Lemma lem4418078 {_106233 _106250 : Type'} : (term68 _106233 _106250) = (term68 _106233 _106250).
Proof. exact (MK_COMB (@lem4418077 _106233 _106250) (@lem4418076 _106233 _106250)). Qed.
Lemma lem4418121 {_106233 _106250 : Type'} : (term67 _106233 _106250) = (term68 _106233 _106250).
Proof. exact (TRANS (@lem4418043 _106233 _106250) (@lem4418078 _106233 _106250)). Qed.
Lemma lem4418122 {_106233 _106250 : Type'} : (term68 _106233 _106250) = (term67 _106233 _106250).
Proof. exact (SYM (@lem4418121 _106233 _106250)). Qed.
Lemma lem4418124 (p : Prop) : p = (term53 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4418125 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term40 _106233 _106250 k s) = (term52 _106233 _106250 k s)) = (term54 _106233 _106250 k s).
Proof. exact (@lem4418124 ((term40 _106233 _106250 k s) = (term52 _106233 _106250 k s))). Qed.
Lemma lem4418126 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term54 _106233 _106250 k s) = ((term40 _106233 _106250 k s) = (term52 _106233 _106250 k s)).
Proof. exact (SYM (@lem4418125 _106233 _106250 k s)). Qed.
Lemma lem4418127 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term55 _106233 _106250 k s) : term55 _106233 _106250 k s.
Proof. exact (h1). Qed.
Lemma lem4418130 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term33 _106233 _106250 s i x) = (term33 _106233 _106250 s i x).
Proof. exact (eq_refl (term33 _106233 _106250 s i x)). Qed.
Lemma lem4418133 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term69 _106233 _106250 s i x) = (s i x).
Proof. exact (@lem16933 (s i x)). Qed.
Lemma lem4418134 {_106233 : Type'} (P : _106233 -> Prop) : (term70 _106233 P) = (term71 _106233 P).
Proof. exact (@lem18392 _106233 P). Qed.
Lemma lem4418135 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term72 _106233 _106250 s i) = (term73 _106233 _106250 s i).
Proof. exact (@lem4418134 _106233 (term35 _106233 _106250 s i)). Qed.
Lemma lem4418136 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term74 _106233 _106250 s i x) = (term33 _106233 _106250 s i x).
Proof. exact (eq_refl (term74 _106233 _106250 s i x)). Qed.
Lemma lem4418137 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4418138 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term75 _106233 _106250 s i x) = (term69 _106233 _106250 s i x).
Proof. exact (MK_COMB (@lem4418137) (@lem4418136 _106233 _106250 s i x)). Qed.
Lemma lem4418139 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term75 _106233 _106250 s i x) = (s i x).
Proof. exact (TRANS (@lem4418138 _106233 _106250 s i x) (@lem4418133 _106233 _106250 s i x)). Qed.
Lemma lem4418140 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term76 _106233 _106250 s i) = (term77 _106233 _106250 s i).
Proof. exact (fun_ext (fun x : _106233 => @lem4418139 _106233 _106250 s i x)). Qed.
Lemma lem4418141 {_106233 : Type'} : (@ex _106233) = (@ex _106233).
Proof. exact (eq_refl (@ex _106233)). Qed.
Lemma lem4418142 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term73 _106233 _106250 s i) = (term78 _106233 _106250 s i).
Proof. exact (MK_COMB (@lem4418141 _106233) (@lem4418140 _106233 _106250 s i)). Qed.
Lemma lem4418143 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term72 _106233 _106250 s i) = (term78 _106233 _106250 s i).
Proof. exact (TRANS (@lem4418135 _106233 _106250 s i) (@lem4418142 _106233 _106250 s i)). Qed.
Lemma lem4418144 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term35 _106233 _106250 s i) = (term35 _106233 _106250 s i).
Proof. exact (fun_ext (fun x : _106233 => @lem4418130 _106233 _106250 s i x)). Qed.
Lemma lem4418145 {_106233 : Type'} : (@all _106233) = (@all _106233).
Proof. exact (eq_refl (@all _106233)). Qed.
Lemma lem4418146 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term36 _106233 _106250 s i) = (term36 _106233 _106250 s i).
Proof. exact (MK_COMB (@lem4418145 _106233) (@lem4418144 _106233 _106250 s i)). Qed.
Lemma lem4418148 {_106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term79 _106250 k i) = (term79 _106250 k i).
Proof. exact (eq_refl (term79 _106250 k i)). Qed.
Lemma lem4418149 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term80 _106233 _106250 k s i) = (term81 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418148 _106250 k i) (@lem4418143 _106233 _106250 s i)). Qed.
Lemma lem4418150 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term82 _106233 _106250 k s i) = (term80 _106233 _106250 k s i).
Proof. exact (@lem17045 (k i) (term36 _106233 _106250 s i)). Qed.
Lemma lem4418151 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term82 _106233 _106250 k s i) = (term81 _106233 _106250 k s i).
Proof. exact (TRANS (@lem4418150 _106233 _106250 k s i) (@lem4418149 _106233 _106250 k s i)). Qed.
Lemma lem4418153 {_106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term29 _106250 k i) = (term29 _106250 k i).
Proof. exact (eq_refl (term29 _106250 k i)). Qed.
Lemma lem4418154 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term37 _106233 _106250 k s i) = (term37 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418153 _106250 k i) (@lem4418146 _106233 _106250 s i)). Qed.
Lemma lem4418155 {_106250 : Type'} (P : _106250 -> Prop) : (term83 _106250 P) = (term84 _106250 P).
Proof. exact (@lem18394 _106250 P). Qed.
Lemma lem4418156 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term40 _106233 _106250 k s) = (term85 _106233 _106250 k s).
Proof. exact (@lem4418155 _106250 (term38 _106233 _106250 k s)). Qed.
Lemma lem4418157 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term86 _106233 _106250 k s i) = (term37 _106233 _106250 k s i).
Proof. exact (eq_refl (term86 _106233 _106250 k s i)). Qed.
Lemma lem4418158 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4418159 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term87 _106233 _106250 k s i) = (term82 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418158) (@lem4418157 _106233 _106250 k s i)). Qed.
Lemma lem4418160 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term87 _106233 _106250 k s i) = (term81 _106233 _106250 k s i).
Proof. exact (TRANS (@lem4418159 _106233 _106250 k s i) (@lem4418151 _106233 _106250 k s i)). Qed.
Lemma lem4418161 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term88 _106233 _106250 k s) = (term89 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418160 _106233 _106250 k s i)). Qed.
Lemma lem4418162 {_106250 : Type'} : (@all _106250) = (@all _106250).
Proof. exact (eq_refl (@all _106250)). Qed.
Lemma lem4418163 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term85 _106233 _106250 k s) = (term90 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418162 _106250) (@lem4418161 _106233 _106250 k s)). Qed.
Lemma lem4418164 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term40 _106233 _106250 k s) = (term90 _106233 _106250 k s).
Proof. exact (TRANS (@lem4418156 _106233 _106250 k s) (@lem4418163 _106233 _106250 k s)). Qed.
Lemma lem4418165 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term38 _106233 _106250 k s) = (term38 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418154 _106233 _106250 k s i)). Qed.
Lemma lem4418166 {_106250 : Type'} : (@ex _106250) = (@ex _106250).
Proof. exact (eq_refl (@ex _106250)). Qed.
Lemma lem4418167 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term39 _106233 _106250 k s) = (term39 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418166 _106250) (@lem4418165 _106233 _106250 k s)). Qed.
Lemma lem4418168 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term91 _106233 _106250 k s) = (term39 _106233 _106250 k s).
Proof. exact (@lem16933 (term39 _106233 _106250 k s)). Qed.
Lemma lem4418169 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term91 _106233 _106250 k s) = (term39 _106233 _106250 k s).
Proof. exact (TRANS (@lem4418168 _106233 _106250 k s) (@lem4418167 _106233 _106250 k s)). Qed.
Lemma lem4418178 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term92 _106233 _106250 k s i a) = (term93 _106233 _106250 k s i a).
Proof. exact (@lem17362 (k i) (s i a)). Qed.
Lemma lem4418183 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term45 _106233 _106250 k s i a) = (term94 _106233 _106250 k s i a).
Proof. exact (@lem17265 (k i) (s i a)). Qed.
Lemma lem4418184 {_106233 : Type'} (P : _106233 -> Prop) : (term83 _106233 P) = (term84 _106233 P).
Proof. exact (@lem18394 _106233 P). Qed.
Lemma lem4418185 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term95 _106233 _106250 k s i) = (term96 _106233 _106250 k s i).
Proof. exact (@lem4418184 _106233 (term47 _106233 _106250 k s i)). Qed.
Lemma lem4418186 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term97 _106233 _106250 k s i a) = (term45 _106233 _106250 k s i a).
Proof. exact (eq_refl (term97 _106233 _106250 k s i a)). Qed.
Lemma lem4418187 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4418188 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term98 _106233 _106250 k s i a) = (term92 _106233 _106250 k s i a).
Proof. exact (MK_COMB (@lem4418187) (@lem4418186 _106233 _106250 k s i a)). Qed.
Lemma lem4418189 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term98 _106233 _106250 k s i a) = (term93 _106233 _106250 k s i a).
Proof. exact (TRANS (@lem4418188 _106233 _106250 k s i a) (@lem4418178 _106233 _106250 k s i a)). Qed.
Lemma lem4418190 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term99 _106233 _106250 k s i) = (term100 _106233 _106250 k s i).
Proof. exact (fun_ext (fun a : _106233 => @lem4418189 _106233 _106250 k s i a)). Qed.
Lemma lem4418191 {_106233 : Type'} : (@all _106233) = (@all _106233).
Proof. exact (eq_refl (@all _106233)). Qed.
Lemma lem4418192 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term96 _106233 _106250 k s i) = (term101 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418191 _106233) (@lem4418190 _106233 _106250 k s i)). Qed.
Lemma lem4418193 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term95 _106233 _106250 k s i) = (term101 _106233 _106250 k s i).
Proof. exact (TRANS (@lem4418185 _106233 _106250 k s i) (@lem4418192 _106233 _106250 k s i)). Qed.
Lemma lem4418194 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term47 _106233 _106250 k s i) = (term102 _106233 _106250 k s i).
Proof. exact (fun_ext (fun a : _106233 => @lem4418183 _106233 _106250 k s i a)). Qed.
Lemma lem4418195 {_106233 : Type'} : (@ex _106233) = (@ex _106233).
Proof. exact (eq_refl (@ex _106233)). Qed.
Lemma lem4418196 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term49 _106233 _106250 k s i) = (term103 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418195 _106233) (@lem4418194 _106233 _106250 k s i)). Qed.
Lemma lem4418197 {_106250 : Type'} (P : _106250 -> Prop) : (term70 _106250 P) = (term71 _106250 P).
Proof. exact (@lem18392 _106250 P). Qed.
Lemma lem4418198 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term104 _106233 _106250 k s) = (term105 _106233 _106250 k s).
Proof. exact (@lem4418197 _106250 (term51 _106233 _106250 k s)). Qed.
Lemma lem4418199 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term106 _106233 _106250 k s i) = (term49 _106233 _106250 k s i).
Proof. exact (eq_refl (term106 _106233 _106250 k s i)). Qed.
Lemma lem4418200 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4418201 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term107 _106233 _106250 k s i) = (term95 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418200) (@lem4418199 _106233 _106250 k s i)). Qed.
Lemma lem4418202 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term107 _106233 _106250 k s i) = (term101 _106233 _106250 k s i).
Proof. exact (TRANS (@lem4418201 _106233 _106250 k s i) (@lem4418193 _106233 _106250 k s i)). Qed.
Lemma lem4418203 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term108 _106233 _106250 k s) = (term109 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418202 _106233 _106250 k s i)). Qed.
Lemma lem4418204 {_106250 : Type'} : (@ex _106250) = (@ex _106250).
Proof. exact (eq_refl (@ex _106250)). Qed.
Lemma lem4418205 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term105 _106233 _106250 k s) = (term110 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418204 _106250) (@lem4418203 _106233 _106250 k s)). Qed.
Lemma lem4418206 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term104 _106233 _106250 k s) = (term110 _106233 _106250 k s).
Proof. exact (TRANS (@lem4418198 _106233 _106250 k s) (@lem4418205 _106233 _106250 k s)). Qed.
Lemma lem4418207 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term51 _106233 _106250 k s) = (term111 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418196 _106233 _106250 k s i)). Qed.
Lemma lem4418208 {_106250 : Type'} : (@all _106250) = (@all _106250).
Proof. exact (eq_refl (@all _106250)). Qed.
Lemma lem4418209 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term52 _106233 _106250 k s) = (term112 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418208 _106250) (@lem4418207 _106233 _106250 k s)). Qed.
Lemma lem4418210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4418211 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term113 _106233 _106250 k s) = (term114 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418210) (@lem4418169 _106233 _106250 k s)). Qed.
Lemma lem4418212 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term115 _106233 _106250 k s) = (term116 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418211 _106233 _106250 k s) (@lem4418209 _106233 _106250 k s)). Qed.
Lemma lem4418213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4418214 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term117 _106233 _106250 k s) = (term118 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418213) (@lem4418164 _106233 _106250 k s)). Qed.
Lemma lem4418215 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term119 _106233 _106250 k s) = (term120 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418214 _106233 _106250 k s) (@lem4418206 _106233 _106250 k s)). Qed.
Lemma lem4418216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4418217 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term121 _106233 _106250 k s) = (term122 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418216) (@lem4418215 _106233 _106250 k s)). Qed.
Lemma lem4418218 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term123 _106233 _106250 k s) = (term124 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418217 _106233 _106250 k s) (@lem4418212 _106233 _106250 k s)). Qed.
Lemma lem4418219 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term55 _106233 _106250 k s) = (term123 _106233 _106250 k s).
Proof. exact (@lem17646 (term40 _106233 _106250 k s) (term52 _106233 _106250 k s)). Qed.
Lemma lem4418220 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term55 _106233 _106250 k s) = (term124 _106233 _106250 k s).
Proof. exact (TRANS (@lem4418219 _106233 _106250 k s) (@lem4418218 _106233 _106250 k s)). Qed.
Lemma lem4418278 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term125 A P Q) = (term126 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4418279 {_106233 : Type'} (P : _106233 -> Prop) (Q : _106233 -> Prop) : (term125 _106233 P Q) = (term126 _106233 P Q).
Proof. exact (@lem4418278 _106233 P Q). Qed.
Lemma lem4418280 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term127 _106233 _106250 k s i) = (term128 _106233 _106250 k s i).
Proof. exact (@lem4418279 _106233 (term129 _106233 _106250 k i) (term35 _106233 _106250 s i)). Qed.
Lemma lem4418281 {_106233 _106250 : Type'} (a : _106233) (k : _106250 -> Prop) (i : _106250) : (term130 _106233 _106250 k i a) = (k i).
Proof. exact (eq_refl (term130 _106233 _106250 k i a)). Qed.
Lemma lem4418282 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4418283 {_106233 _106250 : Type'} (a : _106233) (k : _106250 -> Prop) (i : _106250) : (term131 _106233 _106250 k i a) = (term29 _106250 k i).
Proof. exact (MK_COMB (@lem4418282) (@lem4418281 _106233 _106250 a k i)). Qed.
Lemma lem4418284 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term74 _106233 _106250 s i a) = (term33 _106233 _106250 s i a).
Proof. exact (eq_refl (term74 _106233 _106250 s i a)). Qed.
Lemma lem4418285 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term132 _106233 _106250 k s i a) = (term93 _106233 _106250 k s i a).
Proof. exact (MK_COMB (@lem4418283 _106233 _106250 a k i) (@lem4418284 _106233 _106250 s i a)). Qed.
Lemma lem4418286 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term133 _106233 _106250 k s i) = (term100 _106233 _106250 k s i).
Proof. exact (fun_ext (fun a : _106233 => @lem4418285 _106233 _106250 k s i a)). Qed.
Lemma lem4418287 {_106233 : Type'} : (@all _106233) = (@all _106233).
Proof. exact (eq_refl (@all _106233)). Qed.
Lemma lem4418288 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term127 _106233 _106250 k s i) = (term101 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418287 _106233) (@lem4418286 _106233 _106250 k s i)). Qed.
Lemma lem4418289 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4418290 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term134 _106233 _106250 k s i) = (term135 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418289) (@lem4418288 _106233 _106250 k s i)). Qed.
Lemma lem4418291 {_106233 _106250 : Type'} (a : _106233) (k : _106250 -> Prop) (i : _106250) : (term130 _106233 _106250 k i a) = (k i).
Proof. exact (eq_refl (term130 _106233 _106250 k i a)). Qed.
Lemma lem4418292 {_106233 _106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term136 _106233 _106250 k i) = (term129 _106233 _106250 k i).
Proof. exact (fun_ext (fun a : _106233 => @lem4418291 _106233 _106250 a k i)). Qed.
Lemma lem4418293 {_106233 : Type'} : (@all _106233) = (@all _106233).
Proof. exact (eq_refl (@all _106233)). Qed.
Lemma lem4418294 {_106233 _106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term137 _106233 _106250 k i) = (term138 _106233 _106250 k i).
Proof. exact (MK_COMB (@lem4418293 _106233) (@lem4418292 _106233 _106250 k i)). Qed.
Lemma lem4418295 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4418296 {_106233 _106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term139 _106233 _106250 k i) = (term140 _106233 _106250 k i).
Proof. exact (MK_COMB (@lem4418295) (@lem4418294 _106233 _106250 k i)). Qed.
Lemma lem4418297 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term74 _106233 _106250 s i a) = (term33 _106233 _106250 s i a).
Proof. exact (eq_refl (term74 _106233 _106250 s i a)). Qed.
Lemma lem4418298 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term141 _106233 _106250 s i) = (term35 _106233 _106250 s i).
Proof. exact (fun_ext (fun a : _106233 => @lem4418297 _106233 _106250 s i a)). Qed.
Lemma lem4418299 {_106233 : Type'} : (@all _106233) = (@all _106233).
Proof. exact (eq_refl (@all _106233)). Qed.
Lemma lem4418300 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term142 _106233 _106250 s i) = (term36 _106233 _106250 s i).
Proof. exact (MK_COMB (@lem4418299 _106233) (@lem4418298 _106233 _106250 s i)). Qed.
Lemma lem4418301 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term128 _106233 _106250 k s i) = (term143 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418296 _106233 _106250 k i) (@lem4418300 _106233 _106250 s i)). Qed.
Lemma lem4418302 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : ((term127 _106233 _106250 k s i) = (term128 _106233 _106250 k s i)) = ((term101 _106233 _106250 k s i) = (term143 _106233 _106250 k s i)).
Proof. exact (MK_COMB (@lem4418290 _106233 _106250 k s i) (@lem4418301 _106233 _106250 k s i)). Qed.
Lemma lem4418303 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term101 _106233 _106250 k s i) = (term143 _106233 _106250 k s i).
Proof. exact (EQ_MP (@lem4418302 _106233 _106250 k s i) (@lem4418280 _106233 _106250 k s i)). Qed.
Lemma lem4418305 {A : Type'} (t : Prop) : (term144 A t) = t.
Proof. exact (EQ_MP (@lem18935 A t) (@lem18934 A t)). Qed.
Lemma lem4418306 {_106233 : Type'} (t : Prop) : (term144 _106233 t) = t.
Proof. exact (@lem4418305 _106233 t). Qed.
Lemma lem4418307 {_106233 _106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term138 _106233 _106250 k i) = (k i).
Proof. exact (@lem4418306 _106233 (k i)). Qed.
Lemma lem4418308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4418309 {_106233 _106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term140 _106233 _106250 k i) = (term29 _106250 k i).
Proof. exact (MK_COMB (@lem4418308) (@lem4418307 _106233 _106250 k i)). Qed.
Lemma lem4418314 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term36 _106233 _106250 s i) = (term36 _106233 _106250 s i).
Proof. exact (eq_refl (term36 _106233 _106250 s i)). Qed.
Lemma lem4418315 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term143 _106233 _106250 k s i) = (term37 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418309 _106233 _106250 k i) (@lem4418314 _106233 _106250 s i)). Qed.
Lemma lem4418316 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term101 _106233 _106250 k s i) = (term37 _106233 _106250 k s i).
Proof. exact (TRANS (@lem4418303 _106233 _106250 k s i) (@lem4418315 _106233 _106250 k s i)). Qed.
Lemma lem4418317 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term109 _106233 _106250 k s) = (term38 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418316 _106233 _106250 k s i)). Qed.
Lemma lem4418318 {_106250 : Type'} : (@ex _106250) = (@ex _106250).
Proof. exact (eq_refl (@ex _106250)). Qed.
Lemma lem4418319 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term110 _106233 _106250 k s) = (term39 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418318 _106250) (@lem4418317 _106233 _106250 k s)). Qed.
Lemma lem4418348 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term118 _106233 _106250 k s) = (term118 _106233 _106250 k s).
Proof. exact (eq_refl (term118 _106233 _106250 k s)). Qed.
Lemma lem4418349 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term120 _106233 _106250 k s) = (term145 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418348 _106233 _106250 k s) (@lem4418319 _106233 _106250 k s)). Qed.
Lemma lem4418350 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4418351 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term122 _106233 _106250 k s) = (term146 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418350) (@lem4418349 _106233 _106250 k s)). Qed.
Lemma lem4418389 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4418390 {_106233 : Type'} (P : _106233 -> Prop) (Q : _106233 -> Prop) : (term147 _106233 P Q) = (term148 _106233 P Q).
Proof. exact (@lem4418389 _106233 P Q). Qed.
Lemma lem4418391 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term149 _106233 _106250 k s i) = (term150 _106233 _106250 k s i).
Proof. exact (@lem4418390 _106233 (term151 _106233 _106250 k i) (term77 _106233 _106250 s i)). Qed.
Lemma lem4418392 {_106233 _106250 : Type'} (a : _106233) (k : _106250 -> Prop) (i : _106250) : (term152 _106233 _106250 k i a) = (term153 _106250 k i).
Proof. exact (eq_refl (term152 _106233 _106250 k i a)). Qed.
Lemma lem4418393 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4418394 {_106233 _106250 : Type'} (a : _106233) (k : _106250 -> Prop) (i : _106250) : (term154 _106233 _106250 k i a) = (term79 _106250 k i).
Proof. exact (MK_COMB (@lem4418393) (@lem4418392 _106233 _106250 a k i)). Qed.
Lemma lem4418395 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term155 _106233 _106250 s i a) = (s i a).
Proof. exact (eq_refl (term155 _106233 _106250 s i a)). Qed.
Lemma lem4418396 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term156 _106233 _106250 k s i a) = (term94 _106233 _106250 k s i a).
Proof. exact (MK_COMB (@lem4418394 _106233 _106250 a k i) (@lem4418395 _106233 _106250 s i a)). Qed.
Lemma lem4418397 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term157 _106233 _106250 k s i) = (term102 _106233 _106250 k s i).
Proof. exact (fun_ext (fun a : _106233 => @lem4418396 _106233 _106250 k s i a)). Qed.
Lemma lem4418398 {_106233 : Type'} : (@ex _106233) = (@ex _106233).
Proof. exact (eq_refl (@ex _106233)). Qed.
Lemma lem4418399 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term149 _106233 _106250 k s i) = (term103 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418398 _106233) (@lem4418397 _106233 _106250 k s i)). Qed.
Lemma lem4418400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4418401 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term158 _106233 _106250 k s i) = (term159 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418400) (@lem4418399 _106233 _106250 k s i)). Qed.
Lemma lem4418402 {_106233 _106250 : Type'} (a : _106233) (k : _106250 -> Prop) (i : _106250) : (term152 _106233 _106250 k i a) = (term153 _106250 k i).
Proof. exact (eq_refl (term152 _106233 _106250 k i a)). Qed.
Lemma lem4418403 {_106233 _106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term160 _106233 _106250 k i) = (term151 _106233 _106250 k i).
Proof. exact (fun_ext (fun a : _106233 => @lem4418402 _106233 _106250 a k i)). Qed.
Lemma lem4418404 {_106233 : Type'} : (@ex _106233) = (@ex _106233).
Proof. exact (eq_refl (@ex _106233)). Qed.
Lemma lem4418405 {_106233 _106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term161 _106233 _106250 k i) = (term162 _106233 _106250 k i).
Proof. exact (MK_COMB (@lem4418404 _106233) (@lem4418403 _106233 _106250 k i)). Qed.
Lemma lem4418406 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4418407 {_106233 _106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term163 _106233 _106250 k i) = (term164 _106233 _106250 k i).
Proof. exact (MK_COMB (@lem4418406) (@lem4418405 _106233 _106250 k i)). Qed.
Lemma lem4418408 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term155 _106233 _106250 s i a) = (s i a).
Proof. exact (eq_refl (term155 _106233 _106250 s i a)). Qed.
Lemma lem4418409 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term165 _106233 _106250 s i) = (term77 _106233 _106250 s i).
Proof. exact (fun_ext (fun a : _106233 => @lem4418408 _106233 _106250 s i a)). Qed.
Lemma lem4418410 {_106233 : Type'} : (@ex _106233) = (@ex _106233).
Proof. exact (eq_refl (@ex _106233)). Qed.
Lemma lem4418411 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term166 _106233 _106250 s i) = (term78 _106233 _106250 s i).
Proof. exact (MK_COMB (@lem4418410 _106233) (@lem4418409 _106233 _106250 s i)). Qed.
Lemma lem4418412 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term150 _106233 _106250 k s i) = (term167 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418407 _106233 _106250 k i) (@lem4418411 _106233 _106250 s i)). Qed.
Lemma lem4418413 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : ((term149 _106233 _106250 k s i) = (term150 _106233 _106250 k s i)) = ((term103 _106233 _106250 k s i) = (term167 _106233 _106250 k s i)).
Proof. exact (MK_COMB (@lem4418401 _106233 _106250 k s i) (@lem4418412 _106233 _106250 k s i)). Qed.
Lemma lem4418414 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term103 _106233 _106250 k s i) = (term167 _106233 _106250 k s i).
Proof. exact (EQ_MP (@lem4418413 _106233 _106250 k s i) (@lem4418391 _106233 _106250 k s i)). Qed.
Lemma lem4418416 {A : Type'} (t : Prop) : (term168 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem4418417 {_106233 : Type'} (t : Prop) : (term168 _106233 t) = t.
Proof. exact (@lem4418416 _106233 t). Qed.
Lemma lem4418418 {_106233 _106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term162 _106233 _106250 k i) = (term153 _106250 k i).
Proof. exact (@lem4418417 _106233 (term153 _106250 k i)). Qed.
Lemma lem4418419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4418420 {_106233 _106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term164 _106233 _106250 k i) = (term79 _106250 k i).
Proof. exact (MK_COMB (@lem4418419) (@lem4418418 _106233 _106250 k i)). Qed.
Lemma lem4418425 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term78 _106233 _106250 s i) = (term78 _106233 _106250 s i).
Proof. exact (eq_refl (term78 _106233 _106250 s i)). Qed.
Lemma lem4418426 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term167 _106233 _106250 k s i) = (term81 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418420 _106233 _106250 k i) (@lem4418425 _106233 _106250 s i)). Qed.
Lemma lem4418427 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term103 _106233 _106250 k s i) = (term81 _106233 _106250 k s i).
Proof. exact (TRANS (@lem4418414 _106233 _106250 k s i) (@lem4418426 _106233 _106250 k s i)). Qed.
Lemma lem4418428 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term111 _106233 _106250 k s) = (term89 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418427 _106233 _106250 k s i)). Qed.
Lemma lem4418429 {_106250 : Type'} : (@all _106250) = (@all _106250).
Proof. exact (eq_refl (@all _106250)). Qed.
Lemma lem4418430 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term112 _106233 _106250 k s) = (term90 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418429 _106250) (@lem4418428 _106233 _106250 k s)). Qed.
Lemma lem4418479 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term114 _106233 _106250 k s) = (term114 _106233 _106250 k s).
Proof. exact (eq_refl (term114 _106233 _106250 k s)). Qed.
Lemma lem4418480 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term116 _106233 _106250 k s) = (term169 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418479 _106233 _106250 k s) (@lem4418430 _106233 _106250 k s)). Qed.
Lemma lem4418481 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term124 _106233 _106250 k s) = (term170 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418351 _106233 _106250 k s) (@lem4418480 _106233 _106250 k s)). Qed.
Lemma lem4418483 {A : Type'} (P : Prop) (Q : A -> Prop) : (term171 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4418484 {_106233 : Type'} (P : Prop) (Q : _106233 -> Prop) : (term171 _106233 P Q) = (term172 _106233 P Q).
Proof. exact (@lem4418483 _106233 P Q). Qed.
Lemma lem4418485 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term173 _106233 _106250 k s i) = (term174 _106233 _106250 k s i).
Proof. exact (@lem4418484 _106233 (term153 _106250 k i) (term77 _106233 _106250 s i)). Qed.
Lemma lem4418486 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term155 _106233 _106250 s i x) = (s i x).
Proof. exact (eq_refl (term155 _106233 _106250 s i x)). Qed.
Lemma lem4418487 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term165 _106233 _106250 s i) = (term77 _106233 _106250 s i).
Proof. exact (fun_ext (fun x : _106233 => @lem4418486 _106233 _106250 s i x)). Qed.
Lemma lem4418488 {_106233 : Type'} : (@ex _106233) = (@ex _106233).
Proof. exact (eq_refl (@ex _106233)). Qed.
Lemma lem4418489 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term166 _106233 _106250 s i) = (term78 _106233 _106250 s i).
Proof. exact (MK_COMB (@lem4418488 _106233) (@lem4418487 _106233 _106250 s i)). Qed.
Lemma lem4418490 {_106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term79 _106250 k i) = (term79 _106250 k i).
Proof. exact (eq_refl (term79 _106250 k i)). Qed.
Lemma lem4418491 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term173 _106233 _106250 k s i) = (term81 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418490 _106250 k i) (@lem4418489 _106233 _106250 s i)). Qed.
Lemma lem4418492 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4418493 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term175 _106233 _106250 k s i) = (term176 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418492) (@lem4418491 _106233 _106250 k s i)). Qed.
Lemma lem4418494 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term155 _106233 _106250 s i x) = (s i x).
Proof. exact (eq_refl (term155 _106233 _106250 s i x)). Qed.
Lemma lem4418495 {_106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term79 _106250 k i) = (term79 _106250 k i).
Proof. exact (eq_refl (term79 _106250 k i)). Qed.
Lemma lem4418496 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term177 _106233 _106250 k s i x) = (term94 _106233 _106250 k s i x).
Proof. exact (MK_COMB (@lem4418495 _106250 k i) (@lem4418494 _106233 _106250 s i x)). Qed.
Lemma lem4418497 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term178 _106233 _106250 k s i) = (term102 _106233 _106250 k s i).
Proof. exact (fun_ext (fun x : _106233 => @lem4418496 _106233 _106250 k s i x)). Qed.
Lemma lem4418498 {_106233 : Type'} : (@ex _106233) = (@ex _106233).
Proof. exact (eq_refl (@ex _106233)). Qed.
Lemma lem4418499 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term174 _106233 _106250 k s i) = (term103 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418498 _106233) (@lem4418497 _106233 _106250 k s i)). Qed.
Lemma lem4418500 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : ((term173 _106233 _106250 k s i) = (term174 _106233 _106250 k s i)) = ((term81 _106233 _106250 k s i) = (term103 _106233 _106250 k s i)).
Proof. exact (MK_COMB (@lem4418493 _106233 _106250 k s i) (@lem4418499 _106233 _106250 k s i)). Qed.
Lemma lem4418501 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term81 _106233 _106250 k s i) = (term103 _106233 _106250 k s i).
Proof. exact (EQ_MP (@lem4418500 _106233 _106250 k s i) (@lem4418485 _106233 _106250 k s i)). Qed.
Lemma lem4418502 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term89 _106233 _106250 k s) = (term111 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418501 _106233 _106250 k s i)). Qed.
Lemma lem4418503 {_106250 : Type'} : (@all _106250) = (@all _106250).
Proof. exact (eq_refl (@all _106250)). Qed.
Lemma lem4418504 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term90 _106233 _106250 k s) = (term112 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418503 _106250) (@lem4418502 _106233 _106250 k s)). Qed.
Lemma lem4418506 {A B : Type'} (P : type1413 A B) : (term13 A B P) = (term14 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4418507 {_106233 _106250 : Type'} (P : type1470 _106233 _106250) : (term179 _106233 _106250 P) = (term180 _106233 _106250 P).
Proof. exact (@lem4418506 _106250 _106233 P). Qed.
Lemma lem4418508 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term181 _106233 _106250 k s) = (term182 _106233 _106250 k s).
Proof. exact (@lem4418507 _106233 _106250 (term183 _106233 _106250 k s)). Qed.
Lemma lem4418509 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term184 _106233 _106250 k s i) = (term102 _106233 _106250 k s i).
Proof. exact (eq_refl (term184 _106233 _106250 k s i)). Qed.
Lemma lem4418510 {_106233 : Type'} (x : _106233) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4418511 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term185 _106233 _106250 k s i x) = (term186 _106233 _106250 k s i x).
Proof. exact (MK_COMB (@lem4418509 _106233 _106250 k s i) (@lem4418510 _106233 x)). Qed.
Lemma lem4418512 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term186 _106233 _106250 k s i x) = (term94 _106233 _106250 k s i x).
Proof. exact (eq_refl (term186 _106233 _106250 k s i x)). Qed.
Lemma lem4418513 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term185 _106233 _106250 k s i x) = (term94 _106233 _106250 k s i x).
Proof. exact (TRANS (@lem4418511 _106233 _106250 k s i x) (@lem4418512 _106233 _106250 k s i x)). Qed.
Lemma lem4418514 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term187 _106233 _106250 k s i) = (term102 _106233 _106250 k s i).
Proof. exact (fun_ext (fun x : _106233 => @lem4418513 _106233 _106250 k s i x)). Qed.
Lemma lem4418515 {_106233 : Type'} : (@ex _106233) = (@ex _106233).
Proof. exact (eq_refl (@ex _106233)). Qed.
Lemma lem4418516 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term188 _106233 _106250 k s i) = (term103 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418515 _106233) (@lem4418514 _106233 _106250 k s i)). Qed.
Lemma lem4418517 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term189 _106233 _106250 k s) = (term111 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418516 _106233 _106250 k s i)). Qed.
Lemma lem4418518 {_106250 : Type'} : (@all _106250) = (@all _106250).
Proof. exact (eq_refl (@all _106250)). Qed.
Lemma lem4418519 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term181 _106233 _106250 k s) = (term112 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418518 _106250) (@lem4418517 _106233 _106250 k s)). Qed.
Lemma lem4418520 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4418521 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term190 _106233 _106250 k s) = (term191 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418520) (@lem4418519 _106233 _106250 k s)). Qed.
Lemma lem4418522 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term184 _106233 _106250 k s i) = (term102 _106233 _106250 k s i).
Proof. exact (eq_refl (term184 _106233 _106250 k s i)). Qed.
Lemma lem4418523 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) : (x i) = (x i).
Proof. exact (eq_refl (x i)). Qed.
Lemma lem4418524 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) (i : _106250) : (term192 _106233 _106250 k s x i) = (term193 _106233 _106250 k s x i).
Proof. exact (MK_COMB (@lem4418522 _106233 _106250 k s i) (@lem4418523 _106233 _106250 x i)). Qed.
Lemma lem4418525 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) (i : _106250) : (term193 _106233 _106250 k s x i) = (term194 _106233 _106250 k s x i).
Proof. exact (eq_refl (term193 _106233 _106250 k s x i)). Qed.
Lemma lem4418526 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) (i : _106250) : (term192 _106233 _106250 k s x i) = (term194 _106233 _106250 k s x i).
Proof. exact (TRANS (@lem4418524 _106233 _106250 k s x i) (@lem4418525 _106233 _106250 k s x i)). Qed.
Lemma lem4418527 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) : (term195 _106233 _106250 k s x) = (term196 _106233 _106250 k s x).
Proof. exact (fun_ext (fun i : _106250 => @lem4418526 _106233 _106250 k s x i)). Qed.
Lemma lem4418528 {_106250 : Type'} : (@all _106250) = (@all _106250).
Proof. exact (eq_refl (@all _106250)). Qed.
Lemma lem4418529 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) : (term197 _106233 _106250 k s x) = (term198 _106233 _106250 k s x).
Proof. exact (MK_COMB (@lem4418528 _106250) (@lem4418527 _106233 _106250 k s x)). Qed.
Lemma lem4418530 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term199 _106233 _106250 k s) = (term200 _106233 _106250 k s).
Proof. exact (fun_ext (fun x : _106250 -> _106233 => @lem4418529 _106233 _106250 k s x)). Qed.
Lemma lem4418531 {_106233 _106250 : Type'} : (@ex (_106250 -> _106233)) = (@ex (_106250 -> _106233)).
Proof. exact (eq_refl (@ex (_106250 -> _106233))). Qed.
Lemma lem4418532 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term182 _106233 _106250 k s) = (term201 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418531 _106233 _106250) (@lem4418530 _106233 _106250 k s)). Qed.
Lemma lem4418533 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term181 _106233 _106250 k s) = (term182 _106233 _106250 k s)) = ((term112 _106233 _106250 k s) = (term201 _106233 _106250 k s)).
Proof. exact (MK_COMB (@lem4418521 _106233 _106250 k s) (@lem4418532 _106233 _106250 k s)). Qed.
Lemma lem4418534 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term112 _106233 _106250 k s) = (term201 _106233 _106250 k s).
Proof. exact (EQ_MP (@lem4418533 _106233 _106250 k s) (@lem4418508 _106233 _106250 k s)). Qed.
Lemma lem4418535 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term90 _106233 _106250 k s) = (term201 _106233 _106250 k s).
Proof. exact (TRANS (@lem4418504 _106233 _106250 k s) (@lem4418534 _106233 _106250 k s)). Qed.
Lemma lem4418536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4418537 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term118 _106233 _106250 k s) = (term202 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418536) (@lem4418535 _106233 _106250 k s)). Qed.
Lemma lem4418538 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term39 _106233 _106250 k s) = (term39 _106233 _106250 k s).
Proof. exact (eq_refl (term39 _106233 _106250 k s)). Qed.
Lemma lem4418539 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term145 _106233 _106250 k s) = (term203 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418537 _106233 _106250 k s) (@lem4418538 _106233 _106250 k s)). Qed.
Lemma lem4418541 {A : Type'} (P : A -> Prop) (Q : Prop) : (term204 A P Q) = (term205 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4418542 {_106233 _106250 : Type'} (P : type805 _106233 _106250) (Q : Prop) : (term206 _106233 _106250 P Q) = (term207 _106233 _106250 P Q).
Proof. exact (@lem4418541 (_106250 -> _106233) P Q). Qed.
Lemma lem4418543 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term208 _106233 _106250 k s) = (term209 _106233 _106250 k s).
Proof. exact (@lem4418542 _106233 _106250 (term200 _106233 _106250 k s) (term39 _106233 _106250 k s)). Qed.
Lemma lem4418544 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) : (term210 _106233 _106250 k s x) = (term198 _106233 _106250 k s x).
Proof. exact (eq_refl (term210 _106233 _106250 k s x)). Qed.
Lemma lem4418545 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term211 _106233 _106250 k s) = (term200 _106233 _106250 k s).
Proof. exact (fun_ext (fun x : _106250 -> _106233 => @lem4418544 _106233 _106250 k s x)). Qed.
Lemma lem4418546 {_106233 _106250 : Type'} : (@ex (_106250 -> _106233)) = (@ex (_106250 -> _106233)).
Proof. exact (eq_refl (@ex (_106250 -> _106233))). Qed.
Lemma lem4418547 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term212 _106233 _106250 k s) = (term201 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418546 _106233 _106250) (@lem4418545 _106233 _106250 k s)). Qed.
Lemma lem4418548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4418549 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term213 _106233 _106250 k s) = (term202 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418548) (@lem4418547 _106233 _106250 k s)). Qed.
Lemma lem4418550 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term39 _106233 _106250 k s) = (term39 _106233 _106250 k s).
Proof. exact (eq_refl (term39 _106233 _106250 k s)). Qed.
Lemma lem4418551 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term208 _106233 _106250 k s) = (term203 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418549 _106233 _106250 k s) (@lem4418550 _106233 _106250 k s)). Qed.
Lemma lem4418552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4418553 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term214 _106233 _106250 k s) = (term215 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418552) (@lem4418551 _106233 _106250 k s)). Qed.
Lemma lem4418554 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) : (term210 _106233 _106250 k s x) = (term198 _106233 _106250 k s x).
Proof. exact (eq_refl (term210 _106233 _106250 k s x)). Qed.
Lemma lem4418555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4418556 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) : (term216 _106233 _106250 k s x) = (term217 _106233 _106250 k s x).
Proof. exact (MK_COMB (@lem4418555) (@lem4418554 _106233 _106250 k s x)). Qed.
Lemma lem4418557 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term39 _106233 _106250 k s) = (term39 _106233 _106250 k s).
Proof. exact (eq_refl (term39 _106233 _106250 k s)). Qed.
Lemma lem4418558 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term218 _106233 _106250 x k s) = (term219 _106233 _106250 x k s).
Proof. exact (MK_COMB (@lem4418556 _106233 _106250 k s x) (@lem4418557 _106233 _106250 k s)). Qed.
Lemma lem4418559 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term220 _106233 _106250 k s) = (term221 _106233 _106250 k s).
Proof. exact (fun_ext (fun x : _106250 -> _106233 => @lem4418558 _106233 _106250 x k s)). Qed.
Lemma lem4418560 {_106233 _106250 : Type'} : (@ex (_106250 -> _106233)) = (@ex (_106250 -> _106233)).
Proof. exact (eq_refl (@ex (_106250 -> _106233))). Qed.
Lemma lem4418561 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term209 _106233 _106250 k s) = (term222 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418560 _106233 _106250) (@lem4418559 _106233 _106250 k s)). Qed.
Lemma lem4418562 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term208 _106233 _106250 k s) = (term209 _106233 _106250 k s)) = ((term203 _106233 _106250 k s) = (term222 _106233 _106250 k s)).
Proof. exact (MK_COMB (@lem4418553 _106233 _106250 k s) (@lem4418561 _106233 _106250 k s)). Qed.
Lemma lem4418563 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term203 _106233 _106250 k s) = (term222 _106233 _106250 k s).
Proof. exact (EQ_MP (@lem4418562 _106233 _106250 k s) (@lem4418543 _106233 _106250 k s)). Qed.
Lemma lem4418565 {A : Type'} (P : Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4418566 {_106250 : Type'} (P : Prop) (Q : _106250 -> Prop) : (term223 _106250 P Q) = (term224 _106250 P Q).
Proof. exact (@lem4418565 _106250 P Q). Qed.
Lemma lem4418567 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term225 _106233 _106250 x k s) = (term226 _106233 _106250 x k s).
Proof. exact (@lem4418566 _106250 (term198 _106233 _106250 k s x) (term38 _106233 _106250 k s)). Qed.
Lemma lem4418568 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term86 _106233 _106250 k s i) = (term37 _106233 _106250 k s i).
Proof. exact (eq_refl (term86 _106233 _106250 k s i)). Qed.
Lemma lem4418569 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term227 _106233 _106250 k s) = (term38 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418568 _106233 _106250 k s i)). Qed.
Lemma lem4418570 {_106250 : Type'} : (@ex _106250) = (@ex _106250).
Proof. exact (eq_refl (@ex _106250)). Qed.
Lemma lem4418571 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term228 _106233 _106250 k s) = (term39 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418570 _106250) (@lem4418569 _106233 _106250 k s)). Qed.
Lemma lem4418572 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) : (term217 _106233 _106250 k s x) = (term217 _106233 _106250 k s x).
Proof. exact (eq_refl (term217 _106233 _106250 k s x)). Qed.
Lemma lem4418573 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term225 _106233 _106250 x k s) = (term219 _106233 _106250 x k s).
Proof. exact (MK_COMB (@lem4418572 _106233 _106250 k s x) (@lem4418571 _106233 _106250 k s)). Qed.
Lemma lem4418574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4418575 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term229 _106233 _106250 x k s) = (term230 _106233 _106250 x k s).
Proof. exact (MK_COMB (@lem4418574) (@lem4418573 _106233 _106250 x k s)). Qed.
Lemma lem4418576 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term86 _106233 _106250 k s i) = (term37 _106233 _106250 k s i).
Proof. exact (eq_refl (term86 _106233 _106250 k s i)). Qed.
Lemma lem4418577 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) : (term217 _106233 _106250 k s x) = (term217 _106233 _106250 k s x).
Proof. exact (eq_refl (term217 _106233 _106250 k s x)). Qed.
Lemma lem4418578 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term231 _106233 _106250 x k s i) = (term232 _106233 _106250 x k s i).
Proof. exact (MK_COMB (@lem4418577 _106233 _106250 k s x) (@lem4418576 _106233 _106250 k s i)). Qed.
Lemma lem4418579 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term233 _106233 _106250 x k s) = (term234 _106233 _106250 x k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418578 _106233 _106250 x k s i)). Qed.
Lemma lem4418580 {_106250 : Type'} : (@ex _106250) = (@ex _106250).
Proof. exact (eq_refl (@ex _106250)). Qed.
Lemma lem4418581 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term226 _106233 _106250 x k s) = (term235 _106233 _106250 x k s).
Proof. exact (MK_COMB (@lem4418580 _106250) (@lem4418579 _106233 _106250 x k s)). Qed.
Lemma lem4418582 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term225 _106233 _106250 x k s) = (term226 _106233 _106250 x k s)) = ((term219 _106233 _106250 x k s) = (term235 _106233 _106250 x k s)).
Proof. exact (MK_COMB (@lem4418575 _106233 _106250 x k s) (@lem4418581 _106233 _106250 x k s)). Qed.
Lemma lem4418583 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term219 _106233 _106250 x k s) = (term235 _106233 _106250 x k s).
Proof. exact (EQ_MP (@lem4418582 _106233 _106250 x k s) (@lem4418567 _106233 _106250 x k s)). Qed.
Lemma lem4418584 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term221 _106233 _106250 k s) = (term236 _106233 _106250 k s).
Proof. exact (fun_ext (fun x : _106250 -> _106233 => @lem4418583 _106233 _106250 x k s)). Qed.
Lemma lem4418585 {_106233 _106250 : Type'} : (@ex (_106250 -> _106233)) = (@ex (_106250 -> _106233)).
Proof. exact (eq_refl (@ex (_106250 -> _106233))). Qed.
Lemma lem4418586 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term222 _106233 _106250 k s) = (term237 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418585 _106233 _106250) (@lem4418584 _106233 _106250 k s)). Qed.
Lemma lem4418587 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term203 _106233 _106250 k s) = (term237 _106233 _106250 k s).
Proof. exact (TRANS (@lem4418563 _106233 _106250 k s) (@lem4418586 _106233 _106250 k s)). Qed.
Lemma lem4418588 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term145 _106233 _106250 k s) = (term237 _106233 _106250 k s).
Proof. exact (TRANS (@lem4418539 _106233 _106250 k s) (@lem4418587 _106233 _106250 k s)). Qed.
Lemma lem4418589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4418590 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term146 _106233 _106250 k s) = (term238 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418589) (@lem4418588 _106233 _106250 k s)). Qed.
Lemma lem4418592 {A : Type'} (P : Prop) (Q : A -> Prop) : (term171 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4418593 {_106233 : Type'} (P : Prop) (Q : _106233 -> Prop) : (term171 _106233 P Q) = (term172 _106233 P Q).
Proof. exact (@lem4418592 _106233 P Q). Qed.
Lemma lem4418594 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term173 _106233 _106250 k s i) = (term174 _106233 _106250 k s i).
Proof. exact (@lem4418593 _106233 (term153 _106250 k i) (term77 _106233 _106250 s i)). Qed.
Lemma lem4418595 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term155 _106233 _106250 s i a) = (s i a).
Proof. exact (eq_refl (term155 _106233 _106250 s i a)). Qed.
Lemma lem4418596 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term165 _106233 _106250 s i) = (term77 _106233 _106250 s i).
Proof. exact (fun_ext (fun a : _106233 => @lem4418595 _106233 _106250 s i a)). Qed.
Lemma lem4418597 {_106233 : Type'} : (@ex _106233) = (@ex _106233).
Proof. exact (eq_refl (@ex _106233)). Qed.
Lemma lem4418598 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term166 _106233 _106250 s i) = (term78 _106233 _106250 s i).
Proof. exact (MK_COMB (@lem4418597 _106233) (@lem4418596 _106233 _106250 s i)). Qed.
Lemma lem4418599 {_106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term79 _106250 k i) = (term79 _106250 k i).
Proof. exact (eq_refl (term79 _106250 k i)). Qed.
Lemma lem4418600 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term173 _106233 _106250 k s i) = (term81 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418599 _106250 k i) (@lem4418598 _106233 _106250 s i)). Qed.
Lemma lem4418601 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4418602 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term175 _106233 _106250 k s i) = (term176 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418601) (@lem4418600 _106233 _106250 k s i)). Qed.
Lemma lem4418603 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term155 _106233 _106250 s i a) = (s i a).
Proof. exact (eq_refl (term155 _106233 _106250 s i a)). Qed.
Lemma lem4418604 {_106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term79 _106250 k i) = (term79 _106250 k i).
Proof. exact (eq_refl (term79 _106250 k i)). Qed.
Lemma lem4418605 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term177 _106233 _106250 k s i a) = (term94 _106233 _106250 k s i a).
Proof. exact (MK_COMB (@lem4418604 _106250 k i) (@lem4418603 _106233 _106250 s i a)). Qed.
Lemma lem4418606 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term178 _106233 _106250 k s i) = (term102 _106233 _106250 k s i).
Proof. exact (fun_ext (fun a : _106233 => @lem4418605 _106233 _106250 k s i a)). Qed.
Lemma lem4418607 {_106233 : Type'} : (@ex _106233) = (@ex _106233).
Proof. exact (eq_refl (@ex _106233)). Qed.
Lemma lem4418608 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term174 _106233 _106250 k s i) = (term103 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418607 _106233) (@lem4418606 _106233 _106250 k s i)). Qed.
Lemma lem4418609 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : ((term173 _106233 _106250 k s i) = (term174 _106233 _106250 k s i)) = ((term81 _106233 _106250 k s i) = (term103 _106233 _106250 k s i)).
Proof. exact (MK_COMB (@lem4418602 _106233 _106250 k s i) (@lem4418608 _106233 _106250 k s i)). Qed.
Lemma lem4418610 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term81 _106233 _106250 k s i) = (term103 _106233 _106250 k s i).
Proof. exact (EQ_MP (@lem4418609 _106233 _106250 k s i) (@lem4418594 _106233 _106250 k s i)). Qed.
Lemma lem4418611 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term89 _106233 _106250 k s) = (term111 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418610 _106233 _106250 k s i)). Qed.
Lemma lem4418612 {_106250 : Type'} : (@all _106250) = (@all _106250).
Proof. exact (eq_refl (@all _106250)). Qed.
Lemma lem4418613 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term90 _106233 _106250 k s) = (term112 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418612 _106250) (@lem4418611 _106233 _106250 k s)). Qed.
Lemma lem4418615 {A B : Type'} (P : type1413 A B) : (term13 A B P) = (term14 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4418616 {_106233 _106250 : Type'} (P : type1470 _106233 _106250) : (term179 _106233 _106250 P) = (term180 _106233 _106250 P).
Proof. exact (@lem4418615 _106250 _106233 P). Qed.
Lemma lem4418617 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term181 _106233 _106250 k s) = (term182 _106233 _106250 k s).
Proof. exact (@lem4418616 _106233 _106250 (term183 _106233 _106250 k s)). Qed.
Lemma lem4418618 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term184 _106233 _106250 k s i) = (term102 _106233 _106250 k s i).
Proof. exact (eq_refl (term184 _106233 _106250 k s i)). Qed.
Lemma lem4418619 {_106233 : Type'} (a : _106233) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4418620 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term185 _106233 _106250 k s i a) = (term186 _106233 _106250 k s i a).
Proof. exact (MK_COMB (@lem4418618 _106233 _106250 k s i) (@lem4418619 _106233 a)). Qed.
Lemma lem4418621 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term186 _106233 _106250 k s i a) = (term94 _106233 _106250 k s i a).
Proof. exact (eq_refl (term186 _106233 _106250 k s i a)). Qed.
Lemma lem4418622 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term185 _106233 _106250 k s i a) = (term94 _106233 _106250 k s i a).
Proof. exact (TRANS (@lem4418620 _106233 _106250 k s i a) (@lem4418621 _106233 _106250 k s i a)). Qed.
Lemma lem4418623 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term187 _106233 _106250 k s i) = (term102 _106233 _106250 k s i).
Proof. exact (fun_ext (fun a : _106233 => @lem4418622 _106233 _106250 k s i a)). Qed.
Lemma lem4418624 {_106233 : Type'} : (@ex _106233) = (@ex _106233).
Proof. exact (eq_refl (@ex _106233)). Qed.
Lemma lem4418625 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term188 _106233 _106250 k s i) = (term103 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418624 _106233) (@lem4418623 _106233 _106250 k s i)). Qed.
Lemma lem4418626 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term189 _106233 _106250 k s) = (term111 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418625 _106233 _106250 k s i)). Qed.
Lemma lem4418627 {_106250 : Type'} : (@all _106250) = (@all _106250).
Proof. exact (eq_refl (@all _106250)). Qed.
Lemma lem4418628 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term181 _106233 _106250 k s) = (term112 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418627 _106250) (@lem4418626 _106233 _106250 k s)). Qed.
Lemma lem4418629 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4418630 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term190 _106233 _106250 k s) = (term191 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418629) (@lem4418628 _106233 _106250 k s)). Qed.
Lemma lem4418631 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term184 _106233 _106250 k s i) = (term102 _106233 _106250 k s i).
Proof. exact (eq_refl (term184 _106233 _106250 k s i)). Qed.
Lemma lem4418632 {_106233 _106250 : Type'} (a : _106250 -> _106233) (i : _106250) : (a i) = (a i).
Proof. exact (eq_refl (a i)). Qed.
Lemma lem4418633 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (i : _106250) : (term192 _106233 _106250 k s a i) = (term193 _106233 _106250 k s a i).
Proof. exact (MK_COMB (@lem4418631 _106233 _106250 k s i) (@lem4418632 _106233 _106250 a i)). Qed.
Lemma lem4418634 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (i : _106250) : (term193 _106233 _106250 k s a i) = (term194 _106233 _106250 k s a i).
Proof. exact (eq_refl (term193 _106233 _106250 k s a i)). Qed.
Lemma lem4418635 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (i : _106250) : (term192 _106233 _106250 k s a i) = (term194 _106233 _106250 k s a i).
Proof. exact (TRANS (@lem4418633 _106233 _106250 k s a i) (@lem4418634 _106233 _106250 k s a i)). Qed.
Lemma lem4418636 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) : (term195 _106233 _106250 k s a) = (term196 _106233 _106250 k s a).
Proof. exact (fun_ext (fun i : _106250 => @lem4418635 _106233 _106250 k s a i)). Qed.
Lemma lem4418637 {_106250 : Type'} : (@all _106250) = (@all _106250).
Proof. exact (eq_refl (@all _106250)). Qed.
Lemma lem4418638 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) : (term197 _106233 _106250 k s a) = (term198 _106233 _106250 k s a).
Proof. exact (MK_COMB (@lem4418637 _106250) (@lem4418636 _106233 _106250 k s a)). Qed.
Lemma lem4418639 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term199 _106233 _106250 k s) = (term200 _106233 _106250 k s).
Proof. exact (fun_ext (fun a : _106250 -> _106233 => @lem4418638 _106233 _106250 k s a)). Qed.
Lemma lem4418640 {_106233 _106250 : Type'} : (@ex (_106250 -> _106233)) = (@ex (_106250 -> _106233)).
Proof. exact (eq_refl (@ex (_106250 -> _106233))). Qed.
Lemma lem4418641 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term182 _106233 _106250 k s) = (term201 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418640 _106233 _106250) (@lem4418639 _106233 _106250 k s)). Qed.
Lemma lem4418642 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term181 _106233 _106250 k s) = (term182 _106233 _106250 k s)) = ((term112 _106233 _106250 k s) = (term201 _106233 _106250 k s)).
Proof. exact (MK_COMB (@lem4418630 _106233 _106250 k s) (@lem4418641 _106233 _106250 k s)). Qed.
Lemma lem4418643 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term112 _106233 _106250 k s) = (term201 _106233 _106250 k s).
Proof. exact (EQ_MP (@lem4418642 _106233 _106250 k s) (@lem4418617 _106233 _106250 k s)). Qed.
Lemma lem4418644 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term90 _106233 _106250 k s) = (term201 _106233 _106250 k s).
Proof. exact (TRANS (@lem4418613 _106233 _106250 k s) (@lem4418643 _106233 _106250 k s)). Qed.
Lemma lem4418645 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term114 _106233 _106250 k s) = (term114 _106233 _106250 k s).
Proof. exact (eq_refl (term114 _106233 _106250 k s)). Qed.
Lemma lem4418646 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term169 _106233 _106250 k s) = (term239 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418645 _106233 _106250 k s) (@lem4418644 _106233 _106250 k s)). Qed.
Lemma lem4418648 {A : Type'} (P : A -> Prop) (Q : Prop) : (term204 A P Q) = (term205 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4418649 {_106250 : Type'} (P : _106250 -> Prop) (Q : Prop) : (term204 _106250 P Q) = (term205 _106250 P Q).
Proof. exact (@lem4418648 _106250 P Q). Qed.
Lemma lem4418650 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term240 _106233 _106250 k s) = (term241 _106233 _106250 k s).
Proof. exact (@lem4418649 _106250 (term38 _106233 _106250 k s) (term201 _106233 _106250 k s)). Qed.
Lemma lem4418651 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term86 _106233 _106250 k s i) = (term37 _106233 _106250 k s i).
Proof. exact (eq_refl (term86 _106233 _106250 k s i)). Qed.
Lemma lem4418652 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term227 _106233 _106250 k s) = (term38 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418651 _106233 _106250 k s i)). Qed.
Lemma lem4418653 {_106250 : Type'} : (@ex _106250) = (@ex _106250).
Proof. exact (eq_refl (@ex _106250)). Qed.
Lemma lem4418654 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term228 _106233 _106250 k s) = (term39 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418653 _106250) (@lem4418652 _106233 _106250 k s)). Qed.
Lemma lem4418655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4418656 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term242 _106233 _106250 k s) = (term114 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418655) (@lem4418654 _106233 _106250 k s)). Qed.
Lemma lem4418657 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term201 _106233 _106250 k s) = (term201 _106233 _106250 k s).
Proof. exact (eq_refl (term201 _106233 _106250 k s)). Qed.
Lemma lem4418658 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term240 _106233 _106250 k s) = (term239 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418656 _106233 _106250 k s) (@lem4418657 _106233 _106250 k s)). Qed.
Lemma lem4418659 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4418660 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term243 _106233 _106250 k s) = (term244 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418659) (@lem4418658 _106233 _106250 k s)). Qed.
Lemma lem4418661 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term86 _106233 _106250 k s i) = (term37 _106233 _106250 k s i).
Proof. exact (eq_refl (term86 _106233 _106250 k s i)). Qed.
Lemma lem4418662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4418663 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term245 _106233 _106250 k s i) = (term246 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418662) (@lem4418661 _106233 _106250 k s i)). Qed.
Lemma lem4418664 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term201 _106233 _106250 k s) = (term201 _106233 _106250 k s).
Proof. exact (eq_refl (term201 _106233 _106250 k s)). Qed.
Lemma lem4418665 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term247 _106233 _106250 i k s) = (term248 _106233 _106250 i k s).
Proof. exact (MK_COMB (@lem4418663 _106233 _106250 k s i) (@lem4418664 _106233 _106250 k s)). Qed.
Lemma lem4418666 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term249 _106233 _106250 k s) = (term250 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418665 _106233 _106250 i k s)). Qed.
Lemma lem4418667 {_106250 : Type'} : (@ex _106250) = (@ex _106250).
Proof. exact (eq_refl (@ex _106250)). Qed.
Lemma lem4418668 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term241 _106233 _106250 k s) = (term251 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418667 _106250) (@lem4418666 _106233 _106250 k s)). Qed.
Lemma lem4418669 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term240 _106233 _106250 k s) = (term241 _106233 _106250 k s)) = ((term239 _106233 _106250 k s) = (term251 _106233 _106250 k s)).
Proof. exact (MK_COMB (@lem4418660 _106233 _106250 k s) (@lem4418668 _106233 _106250 k s)). Qed.
Lemma lem4418670 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term239 _106233 _106250 k s) = (term251 _106233 _106250 k s).
Proof. exact (EQ_MP (@lem4418669 _106233 _106250 k s) (@lem4418650 _106233 _106250 k s)). Qed.
Lemma lem4418672 {A : Type'} (P : Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4418673 {_106233 _106250 : Type'} (P : Prop) (Q : type805 _106233 _106250) : (term252 _106233 _106250 P Q) = (term253 _106233 _106250 P Q).
Proof. exact (@lem4418672 (_106250 -> _106233) P Q). Qed.
Lemma lem4418674 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term254 _106233 _106250 i k s) = (term255 _106233 _106250 i k s).
Proof. exact (@lem4418673 _106233 _106250 (term37 _106233 _106250 k s i) (term200 _106233 _106250 k s)). Qed.
Lemma lem4418675 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) : (term210 _106233 _106250 k s a) = (term198 _106233 _106250 k s a).
Proof. exact (eq_refl (term210 _106233 _106250 k s a)). Qed.
Lemma lem4418676 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term211 _106233 _106250 k s) = (term200 _106233 _106250 k s).
Proof. exact (fun_ext (fun a : _106250 -> _106233 => @lem4418675 _106233 _106250 k s a)). Qed.
Lemma lem4418677 {_106233 _106250 : Type'} : (@ex (_106250 -> _106233)) = (@ex (_106250 -> _106233)).
Proof. exact (eq_refl (@ex (_106250 -> _106233))). Qed.
Lemma lem4418678 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term212 _106233 _106250 k s) = (term201 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418677 _106233 _106250) (@lem4418676 _106233 _106250 k s)). Qed.
Lemma lem4418679 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term246 _106233 _106250 k s i) = (term246 _106233 _106250 k s i).
Proof. exact (eq_refl (term246 _106233 _106250 k s i)). Qed.
Lemma lem4418680 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term254 _106233 _106250 i k s) = (term248 _106233 _106250 i k s).
Proof. exact (MK_COMB (@lem4418679 _106233 _106250 k s i) (@lem4418678 _106233 _106250 k s)). Qed.
Lemma lem4418681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4418682 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term256 _106233 _106250 i k s) = (term257 _106233 _106250 i k s).
Proof. exact (MK_COMB (@lem4418681) (@lem4418680 _106233 _106250 i k s)). Qed.
Lemma lem4418683 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) : (term210 _106233 _106250 k s a) = (term198 _106233 _106250 k s a).
Proof. exact (eq_refl (term210 _106233 _106250 k s a)). Qed.
Lemma lem4418684 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term246 _106233 _106250 k s i) = (term246 _106233 _106250 k s i).
Proof. exact (eq_refl (term246 _106233 _106250 k s i)). Qed.
Lemma lem4418685 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) : (term258 _106233 _106250 i k s a) = (term259 _106233 _106250 i k s a).
Proof. exact (MK_COMB (@lem4418684 _106233 _106250 k s i) (@lem4418683 _106233 _106250 k s a)). Qed.
Lemma lem4418686 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term260 _106233 _106250 i k s) = (term261 _106233 _106250 i k s).
Proof. exact (fun_ext (fun a : _106250 -> _106233 => @lem4418685 _106233 _106250 i k s a)). Qed.
Lemma lem4418687 {_106233 _106250 : Type'} : (@ex (_106250 -> _106233)) = (@ex (_106250 -> _106233)).
Proof. exact (eq_refl (@ex (_106250 -> _106233))). Qed.
Lemma lem4418688 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term255 _106233 _106250 i k s) = (term262 _106233 _106250 i k s).
Proof. exact (MK_COMB (@lem4418687 _106233 _106250) (@lem4418686 _106233 _106250 i k s)). Qed.
Lemma lem4418689 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term254 _106233 _106250 i k s) = (term255 _106233 _106250 i k s)) = ((term248 _106233 _106250 i k s) = (term262 _106233 _106250 i k s)).
Proof. exact (MK_COMB (@lem4418682 _106233 _106250 i k s) (@lem4418688 _106233 _106250 i k s)). Qed.
Lemma lem4418690 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term248 _106233 _106250 i k s) = (term262 _106233 _106250 i k s).
Proof. exact (EQ_MP (@lem4418689 _106233 _106250 i k s) (@lem4418674 _106233 _106250 i k s)). Qed.
Lemma lem4418691 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term250 _106233 _106250 k s) = (term263 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418690 _106233 _106250 i k s)). Qed.
Lemma lem4418692 {_106250 : Type'} : (@ex _106250) = (@ex _106250).
Proof. exact (eq_refl (@ex _106250)). Qed.
Lemma lem4418693 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term251 _106233 _106250 k s) = (term264 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418692 _106250) (@lem4418691 _106233 _106250 k s)). Qed.
Lemma lem4418694 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term239 _106233 _106250 k s) = (term264 _106233 _106250 k s).
Proof. exact (TRANS (@lem4418670 _106233 _106250 k s) (@lem4418693 _106233 _106250 k s)). Qed.
Lemma lem4418695 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term169 _106233 _106250 k s) = (term264 _106233 _106250 k s).
Proof. exact (TRANS (@lem4418646 _106233 _106250 k s) (@lem4418694 _106233 _106250 k s)). Qed.
Lemma lem4418696 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term170 _106233 _106250 k s) = (term265 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418590 _106233 _106250 k s) (@lem4418695 _106233 _106250 k s)). Qed.
Lemma lem4418700 {A : Type'} (P : A -> Prop) (Q : Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4418701 {_106233 _106250 : Type'} (P : type805 _106233 _106250) (Q : Prop) : (term268 _106233 _106250 P Q) = (term269 _106233 _106250 P Q).
Proof. exact (@lem4418700 (_106250 -> _106233) P Q). Qed.
Lemma lem4418702 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term270 _106233 _106250 k s) = (term271 _106233 _106250 k s).
Proof. exact (@lem4418701 _106233 _106250 (term236 _106233 _106250 k s) (term264 _106233 _106250 k s)). Qed.
Lemma lem4418703 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term272 _106233 _106250 k s x) = (term235 _106233 _106250 x k s).
Proof. exact (eq_refl (term272 _106233 _106250 k s x)). Qed.
Lemma lem4418704 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term273 _106233 _106250 k s) = (term236 _106233 _106250 k s).
Proof. exact (fun_ext (fun x : _106250 -> _106233 => @lem4418703 _106233 _106250 x k s)). Qed.
Lemma lem4418705 {_106233 _106250 : Type'} : (@ex (_106250 -> _106233)) = (@ex (_106250 -> _106233)).
Proof. exact (eq_refl (@ex (_106250 -> _106233))). Qed.
Lemma lem4418706 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term274 _106233 _106250 k s) = (term237 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418705 _106233 _106250) (@lem4418704 _106233 _106250 k s)). Qed.
Lemma lem4418707 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4418708 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term275 _106233 _106250 k s) = (term238 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418707) (@lem4418706 _106233 _106250 k s)). Qed.
Lemma lem4418709 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term264 _106233 _106250 k s) = (term264 _106233 _106250 k s).
Proof. exact (eq_refl (term264 _106233 _106250 k s)). Qed.
Lemma lem4418710 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term270 _106233 _106250 k s) = (term265 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418708 _106233 _106250 k s) (@lem4418709 _106233 _106250 k s)). Qed.
Lemma lem4418711 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4418712 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term276 _106233 _106250 k s) = (term277 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418711) (@lem4418710 _106233 _106250 k s)). Qed.
Lemma lem4418713 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term272 _106233 _106250 k s x) = (term235 _106233 _106250 x k s).
Proof. exact (eq_refl (term272 _106233 _106250 k s x)). Qed.
Lemma lem4418714 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4418715 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term278 _106233 _106250 k s x) = (term279 _106233 _106250 x k s).
Proof. exact (MK_COMB (@lem4418714) (@lem4418713 _106233 _106250 x k s)). Qed.
Lemma lem4418716 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term264 _106233 _106250 k s) = (term264 _106233 _106250 k s).
Proof. exact (eq_refl (term264 _106233 _106250 k s)). Qed.
Lemma lem4418717 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term280 _106233 _106250 x k s) = (term281 _106233 _106250 x k s).
Proof. exact (MK_COMB (@lem4418715 _106233 _106250 x k s) (@lem4418716 _106233 _106250 k s)). Qed.
Lemma lem4418718 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term282 _106233 _106250 k s) = (term283 _106233 _106250 k s).
Proof. exact (fun_ext (fun x : _106250 -> _106233 => @lem4418717 _106233 _106250 x k s)). Qed.
Lemma lem4418719 {_106233 _106250 : Type'} : (@ex (_106250 -> _106233)) = (@ex (_106250 -> _106233)).
Proof. exact (eq_refl (@ex (_106250 -> _106233))). Qed.
Lemma lem4418720 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term271 _106233 _106250 k s) = (term284 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418719 _106233 _106250) (@lem4418718 _106233 _106250 k s)). Qed.
Lemma lem4418721 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term270 _106233 _106250 k s) = (term271 _106233 _106250 k s)) = ((term265 _106233 _106250 k s) = (term284 _106233 _106250 k s)).
Proof. exact (MK_COMB (@lem4418712 _106233 _106250 k s) (@lem4418720 _106233 _106250 k s)). Qed.
Lemma lem4418722 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term265 _106233 _106250 k s) = (term284 _106233 _106250 k s).
Proof. exact (EQ_MP (@lem4418721 _106233 _106250 k s) (@lem4418702 _106233 _106250 k s)). Qed.
Lemma lem4418724 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term148 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4418725 {_106250 : Type'} (P : _106250 -> Prop) (Q : _106250 -> Prop) : (term148 _106250 P Q) = (term147 _106250 P Q).
Proof. exact (@lem4418724 _106250 P Q). Qed.
Lemma lem4418726 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term285 _106233 _106250 x k s) = (term286 _106233 _106250 x k s).
Proof. exact (@lem4418725 _106250 (term234 _106233 _106250 x k s) (term263 _106233 _106250 k s)). Qed.
Lemma lem4418727 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term287 _106233 _106250 x k s i) = (term232 _106233 _106250 x k s i).
Proof. exact (eq_refl (term287 _106233 _106250 x k s i)). Qed.
Lemma lem4418728 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term288 _106233 _106250 x k s) = (term234 _106233 _106250 x k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418727 _106233 _106250 x k s i)). Qed.
Lemma lem4418729 {_106250 : Type'} : (@ex _106250) = (@ex _106250).
Proof. exact (eq_refl (@ex _106250)). Qed.
Lemma lem4418730 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term289 _106233 _106250 x k s) = (term235 _106233 _106250 x k s).
Proof. exact (MK_COMB (@lem4418729 _106250) (@lem4418728 _106233 _106250 x k s)). Qed.
Lemma lem4418731 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4418732 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term290 _106233 _106250 x k s) = (term279 _106233 _106250 x k s).
Proof. exact (MK_COMB (@lem4418731) (@lem4418730 _106233 _106250 x k s)). Qed.
Lemma lem4418733 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term291 _106233 _106250 k s i) = (term262 _106233 _106250 i k s).
Proof. exact (eq_refl (term291 _106233 _106250 k s i)). Qed.
Lemma lem4418734 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term292 _106233 _106250 k s) = (term263 _106233 _106250 k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418733 _106233 _106250 i k s)). Qed.
Lemma lem4418735 {_106250 : Type'} : (@ex _106250) = (@ex _106250).
Proof. exact (eq_refl (@ex _106250)). Qed.
Lemma lem4418736 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term293 _106233 _106250 k s) = (term264 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418735 _106250) (@lem4418734 _106233 _106250 k s)). Qed.
Lemma lem4418737 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term285 _106233 _106250 x k s) = (term281 _106233 _106250 x k s).
Proof. exact (MK_COMB (@lem4418732 _106233 _106250 x k s) (@lem4418736 _106233 _106250 k s)). Qed.
Lemma lem4418738 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4418739 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term294 _106233 _106250 x k s) = (term295 _106233 _106250 x k s).
Proof. exact (MK_COMB (@lem4418738) (@lem4418737 _106233 _106250 x k s)). Qed.
Lemma lem4418740 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term287 _106233 _106250 x k s i) = (term232 _106233 _106250 x k s i).
Proof. exact (eq_refl (term287 _106233 _106250 x k s i)). Qed.
Lemma lem4418741 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4418742 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term296 _106233 _106250 x k s i) = (term297 _106233 _106250 x k s i).
Proof. exact (MK_COMB (@lem4418741) (@lem4418740 _106233 _106250 x k s i)). Qed.
Lemma lem4418743 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term291 _106233 _106250 k s i) = (term262 _106233 _106250 i k s).
Proof. exact (eq_refl (term291 _106233 _106250 k s i)). Qed.
Lemma lem4418744 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term298 _106233 _106250 x k s i) = (term299 _106233 _106250 x i k s).
Proof. exact (MK_COMB (@lem4418742 _106233 _106250 x k s i) (@lem4418743 _106233 _106250 i k s)). Qed.
Lemma lem4418745 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term300 _106233 _106250 x k s) = (term301 _106233 _106250 x k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418744 _106233 _106250 x i k s)). Qed.
Lemma lem4418746 {_106250 : Type'} : (@ex _106250) = (@ex _106250).
Proof. exact (eq_refl (@ex _106250)). Qed.
Lemma lem4418747 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term286 _106233 _106250 x k s) = (term302 _106233 _106250 x k s).
Proof. exact (MK_COMB (@lem4418746 _106250) (@lem4418745 _106233 _106250 x k s)). Qed.
Lemma lem4418748 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term285 _106233 _106250 x k s) = (term286 _106233 _106250 x k s)) = ((term281 _106233 _106250 x k s) = (term302 _106233 _106250 x k s)).
Proof. exact (MK_COMB (@lem4418739 _106233 _106250 x k s) (@lem4418747 _106233 _106250 x k s)). Qed.
Lemma lem4418749 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term281 _106233 _106250 x k s) = (term302 _106233 _106250 x k s).
Proof. exact (EQ_MP (@lem4418748 _106233 _106250 x k s) (@lem4418726 _106233 _106250 x k s)). Qed.
Lemma lem4418751 {A : Type'} (P : Prop) (Q : A -> Prop) : (term171 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4418752 {_106233 _106250 : Type'} (P : Prop) (Q : type805 _106233 _106250) : (term303 _106233 _106250 P Q) = (term304 _106233 _106250 P Q).
Proof. exact (@lem4418751 (_106250 -> _106233) P Q). Qed.
Lemma lem4418753 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term305 _106233 _106250 x i k s) = (term306 _106233 _106250 x i k s).
Proof. exact (@lem4418752 _106233 _106250 (term232 _106233 _106250 x k s i) (term261 _106233 _106250 i k s)). Qed.
Lemma lem4418754 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) : (term307 _106233 _106250 i k s a) = (term259 _106233 _106250 i k s a).
Proof. exact (eq_refl (term307 _106233 _106250 i k s a)). Qed.
Lemma lem4418755 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term308 _106233 _106250 i k s) = (term261 _106233 _106250 i k s).
Proof. exact (fun_ext (fun a : _106250 -> _106233 => @lem4418754 _106233 _106250 i k s a)). Qed.
Lemma lem4418756 {_106233 _106250 : Type'} : (@ex (_106250 -> _106233)) = (@ex (_106250 -> _106233)).
Proof. exact (eq_refl (@ex (_106250 -> _106233))). Qed.
Lemma lem4418757 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term309 _106233 _106250 i k s) = (term262 _106233 _106250 i k s).
Proof. exact (MK_COMB (@lem4418756 _106233 _106250) (@lem4418755 _106233 _106250 i k s)). Qed.
Lemma lem4418758 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term297 _106233 _106250 x k s i) = (term297 _106233 _106250 x k s i).
Proof. exact (eq_refl (term297 _106233 _106250 x k s i)). Qed.
Lemma lem4418759 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term305 _106233 _106250 x i k s) = (term299 _106233 _106250 x i k s).
Proof. exact (MK_COMB (@lem4418758 _106233 _106250 x k s i) (@lem4418757 _106233 _106250 i k s)). Qed.
Lemma lem4418760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4418761 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term310 _106233 _106250 x i k s) = (term311 _106233 _106250 x i k s).
Proof. exact (MK_COMB (@lem4418760) (@lem4418759 _106233 _106250 x i k s)). Qed.
Lemma lem4418762 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) : (term307 _106233 _106250 i k s a) = (term259 _106233 _106250 i k s a).
Proof. exact (eq_refl (term307 _106233 _106250 i k s a)). Qed.
Lemma lem4418763 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term297 _106233 _106250 x k s i) = (term297 _106233 _106250 x k s i).
Proof. exact (eq_refl (term297 _106233 _106250 x k s i)). Qed.
Lemma lem4418764 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) : (term312 _106233 _106250 x i k s a) = (term313 _106233 _106250 x i k s a).
Proof. exact (MK_COMB (@lem4418763 _106233 _106250 x k s i) (@lem4418762 _106233 _106250 i k s a)). Qed.
Lemma lem4418765 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term314 _106233 _106250 x i k s) = (term315 _106233 _106250 x i k s).
Proof. exact (fun_ext (fun a : _106250 -> _106233 => @lem4418764 _106233 _106250 x i k s a)). Qed.
Lemma lem4418766 {_106233 _106250 : Type'} : (@ex (_106250 -> _106233)) = (@ex (_106250 -> _106233)).
Proof. exact (eq_refl (@ex (_106250 -> _106233))). Qed.
Lemma lem4418767 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term306 _106233 _106250 x i k s) = (term316 _106233 _106250 x i k s).
Proof. exact (MK_COMB (@lem4418766 _106233 _106250) (@lem4418765 _106233 _106250 x i k s)). Qed.
Lemma lem4418768 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : ((term305 _106233 _106250 x i k s) = (term306 _106233 _106250 x i k s)) = ((term299 _106233 _106250 x i k s) = (term316 _106233 _106250 x i k s)).
Proof. exact (MK_COMB (@lem4418761 _106233 _106250 x i k s) (@lem4418767 _106233 _106250 x i k s)). Qed.
Lemma lem4418769 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term299 _106233 _106250 x i k s) = (term316 _106233 _106250 x i k s).
Proof. exact (EQ_MP (@lem4418768 _106233 _106250 x i k s) (@lem4418753 _106233 _106250 x i k s)). Qed.
Lemma lem4418770 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term301 _106233 _106250 x k s) = (term317 _106233 _106250 x k s).
Proof. exact (fun_ext (fun i : _106250 => @lem4418769 _106233 _106250 x i k s)). Qed.
Lemma lem4418771 {_106250 : Type'} : (@ex _106250) = (@ex _106250).
Proof. exact (eq_refl (@ex _106250)). Qed.
Lemma lem4418772 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term302 _106233 _106250 x k s) = (term318 _106233 _106250 x k s).
Proof. exact (MK_COMB (@lem4418771 _106250) (@lem4418770 _106233 _106250 x k s)). Qed.
Lemma lem4418773 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term281 _106233 _106250 x k s) = (term318 _106233 _106250 x k s).
Proof. exact (TRANS (@lem4418749 _106233 _106250 x k s) (@lem4418772 _106233 _106250 x k s)). Qed.
Lemma lem4418774 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term283 _106233 _106250 k s) = (term319 _106233 _106250 k s).
Proof. exact (fun_ext (fun x : _106250 -> _106233 => @lem4418773 _106233 _106250 x k s)). Qed.
Lemma lem4418775 {_106233 _106250 : Type'} : (@ex (_106250 -> _106233)) = (@ex (_106250 -> _106233)).
Proof. exact (eq_refl (@ex (_106250 -> _106233))). Qed.
Lemma lem4418776 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term284 _106233 _106250 k s) = (term320 _106233 _106250 k s).
Proof. exact (MK_COMB (@lem4418775 _106233 _106250) (@lem4418774 _106233 _106250 k s)). Qed.
Lemma lem4418777 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term265 _106233 _106250 k s) = (term320 _106233 _106250 k s).
Proof. exact (TRANS (@lem4418722 _106233 _106250 k s) (@lem4418776 _106233 _106250 k s)). Qed.
Lemma lem4418778 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term170 _106233 _106250 k s) = (term320 _106233 _106250 k s).
Proof. exact (TRANS (@lem4418696 _106233 _106250 k s) (@lem4418777 _106233 _106250 k s)). Qed.
Lemma lem4418779 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term124 _106233 _106250 k s) = (term320 _106233 _106250 k s).
Proof. exact (TRANS (@lem4418481 _106233 _106250 k s) (@lem4418778 _106233 _106250 k s)). Qed.
Lemma lem4418780 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term55 _106233 _106250 k s) = (term320 _106233 _106250 k s).
Proof. exact (TRANS (@lem4418220 _106233 _106250 k s) (@lem4418779 _106233 _106250 k s)). Qed.
Lemma lem4418781 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term55 _106233 _106250 k s) : term320 _106233 _106250 k s.
Proof. exact (EQ_MP (@lem4418780 _106233 _106250 k s) (@lem4418127 _106233 _106250 k s h1)). Qed.
Lemma lem4418782 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term318 _106233 _106250 x k s) : term318 _106233 _106250 x k s.
Proof. exact (h1). Qed.
Lemma lem4418783 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term316 _106233 _106250 x i k s) : term316 _106233 _106250 x i k s.
Proof. exact (h1). Qed.
Lemma lem4418784 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term313 _106233 _106250 x i k s a) : term313 _106233 _106250 x i k s a.
Proof. exact (h1). Qed.
Lemma lem4418799 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (i : _106250) : (term194 _106233 _106250 k s a i) = (term194 _106233 _106250 k s a i).
Proof. exact (eq_refl (term194 _106233 _106250 k s a i)). Qed.
Lemma lem4418800 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) : (term196 _106233 _106250 k s a) = (term196 _106233 _106250 k s a).
Proof. exact (fun_ext (fun i : _106250 => @lem4418799 _106233 _106250 k s a i)). Qed.
Lemma lem4418801 {_106250 : Type'} : (@all _106250) = (@all _106250).
Proof. exact (eq_refl (@all _106250)). Qed.
Lemma lem4418802 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) : (term198 _106233 _106250 k s a) = (term198 _106233 _106250 k s a).
Proof. exact (MK_COMB (@lem4418801 _106250) (@lem4418800 _106233 _106250 k s a)). Qed.
Lemma lem4418809 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term33 _106233 _106250 s i x) = (term33 _106233 _106250 s i x).
Proof. exact (eq_refl (term33 _106233 _106250 s i x)). Qed.
Lemma lem4418810 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term35 _106233 _106250 s i) = (term35 _106233 _106250 s i).
Proof. exact (fun_ext (fun x : _106233 => @lem4418809 _106233 _106250 s i x)). Qed.
Lemma lem4418811 {_106233 : Type'} : (@all _106233) = (@all _106233).
Proof. exact (eq_refl (@all _106233)). Qed.
Lemma lem4418812 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term36 _106233 _106250 s i) = (term36 _106233 _106250 s i).
Proof. exact (MK_COMB (@lem4418811 _106233) (@lem4418810 _106233 _106250 s i)). Qed.
Lemma lem4418817 {_106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term29 _106250 k i) = (term29 _106250 k i).
Proof. exact (eq_refl (term29 _106250 k i)). Qed.
Lemma lem4418818 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term37 _106233 _106250 k s i) = (term37 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418817 _106250 k i) (@lem4418812 _106233 _106250 s i)). Qed.
Lemma lem4418819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4418820 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term246 _106233 _106250 k s i) = (term246 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418819) (@lem4418818 _106233 _106250 k s i)). Qed.
Lemma lem4418821 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) : (term259 _106233 _106250 i k s a) = (term259 _106233 _106250 i k s a).
Proof. exact (MK_COMB (@lem4418820 _106233 _106250 k s i) (@lem4418802 _106233 _106250 k s a)). Qed.
Lemma lem4418828 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term33 _106233 _106250 s i a) = (term33 _106233 _106250 s i a).
Proof. exact (eq_refl (term33 _106233 _106250 s i a)). Qed.
Lemma lem4418829 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term35 _106233 _106250 s i) = (term35 _106233 _106250 s i).
Proof. exact (fun_ext (fun a : _106233 => @lem4418828 _106233 _106250 s i a)). Qed.
Lemma lem4418830 {_106233 : Type'} : (@all _106233) = (@all _106233).
Proof. exact (eq_refl (@all _106233)). Qed.
Lemma lem4418831 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term36 _106233 _106250 s i) = (term36 _106233 _106250 s i).
Proof. exact (MK_COMB (@lem4418830 _106233) (@lem4418829 _106233 _106250 s i)). Qed.
Lemma lem4418836 {_106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term29 _106250 k i) = (term29 _106250 k i).
Proof. exact (eq_refl (term29 _106250 k i)). Qed.
Lemma lem4418837 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term37 _106233 _106250 k s i) = (term37 _106233 _106250 k s i).
Proof. exact (MK_COMB (@lem4418836 _106250 k i) (@lem4418831 _106233 _106250 s i)). Qed.
Lemma lem4418852 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) (i : _106250) : (term194 _106233 _106250 k s x i) = (term194 _106233 _106250 k s x i).
Proof. exact (eq_refl (term194 _106233 _106250 k s x i)). Qed.
Lemma lem4418853 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) : (term196 _106233 _106250 k s x) = (term196 _106233 _106250 k s x).
Proof. exact (fun_ext (fun i : _106250 => @lem4418852 _106233 _106250 k s x i)). Qed.
Lemma lem4418854 {_106250 : Type'} : (@all _106250) = (@all _106250).
Proof. exact (eq_refl (@all _106250)). Qed.
Lemma lem4418855 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) : (term198 _106233 _106250 k s x) = (term198 _106233 _106250 k s x).
Proof. exact (MK_COMB (@lem4418854 _106250) (@lem4418853 _106233 _106250 k s x)). Qed.
Lemma lem4418856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4418857 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) : (term217 _106233 _106250 k s x) = (term217 _106233 _106250 k s x).
Proof. exact (MK_COMB (@lem4418856) (@lem4418855 _106233 _106250 k s x)). Qed.
Lemma lem4418858 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term232 _106233 _106250 x k s i) = (term232 _106233 _106250 x k s i).
Proof. exact (MK_COMB (@lem4418857 _106233 _106250 k s x) (@lem4418837 _106233 _106250 k s i)). Qed.
Lemma lem4418859 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4418860 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) : (term297 _106233 _106250 x k s i) = (term297 _106233 _106250 x k s i).
Proof. exact (MK_COMB (@lem4418859) (@lem4418858 _106233 _106250 x k s i)). Qed.
Lemma lem4418861 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) : (term313 _106233 _106250 x i k s a) = (term313 _106233 _106250 x i k s a).
Proof. exact (MK_COMB (@lem4418860 _106233 _106250 x k s i) (@lem4418821 _106233 _106250 i k s a)). Qed.
Lemma lem4418862 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term313 _106233 _106250 x i k s a) : term313 _106233 _106250 x i k s a.
Proof. exact (EQ_MP (@lem4418861 _106233 _106250 x i k s a) (@lem4418784 _106233 _106250 x i k s a h1)). Qed.
Lemma lem4418863 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term232 _106233 _106250 x k s i.
Proof. exact (h1). Qed.
Lemma lem4418864 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term259 _106233 _106250 i k s a.
Proof. exact (h1). Qed.
Lemma lem4418865 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term37 _106233 _106250 k s i.
Proof. exact (proj2 (@lem4418863 _106233 _106250 x k s i h1)). Qed.
Lemma lem4418866 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term198 _106233 _106250 k s x.
Proof. exact (proj1 (@lem4418863 _106233 _106250 x k s i h1)). Qed.
Lemma lem4418867 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term36 _106233 _106250 s i.
Proof. exact (proj2 (@lem4418865 _106233 _106250 x k s i h1)). Qed.
Lemma lem4418869 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term198 _106233 _106250 k s a.
Proof. exact (proj2 (@lem4418864 _106233 _106250 i k s a h1)). Qed.
Lemma lem4418870 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term37 _106233 _106250 k s i.
Proof. exact (proj1 (@lem4418864 _106233 _106250 i k s a h1)). Qed.
Lemma lem4418871 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term36 _106233 _106250 s i.
Proof. exact (proj2 (@lem4418870 _106233 _106250 i k s a h1)). Qed.
Lemma lem4418880 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) (i : _106250) : (term194 _106233 _106250 k s x i) = (term194 _106233 _106250 k s x i).
Proof. exact (eq_refl (term194 _106233 _106250 k s x i)). Qed.
Lemma lem4418881 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) : (term196 _106233 _106250 k s x) = (term196 _106233 _106250 k s x).
Proof. exact (fun_ext (fun i : _106250 => @lem4418880 _106233 _106250 k s x i)). Qed.
Lemma lem4418882 {_106250 : Type'} : (@all _106250) = (@all _106250).
Proof. exact (eq_refl (@all _106250)). Qed.
Lemma lem4418884 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) : (term198 _106233 _106250 k s x) = (term198 _106233 _106250 k s x).
Proof. exact (MK_COMB (@lem4418882 _106250) (@lem4418881 _106233 _106250 k s x)). Qed.
Lemma lem4418885 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term198 _106233 _106250 k s x.
Proof. exact (EQ_MP (@lem4418884 _106233 _106250 k s x) (@lem4418866 _106233 _106250 x k s i h1)). Qed.
Lemma lem4418891 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (a : _106233) : (term33 _106233 _106250 s i a) = (term33 _106233 _106250 s i a).
Proof. exact (eq_refl (term33 _106233 _106250 s i a)). Qed.
Lemma lem4418892 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term35 _106233 _106250 s i) = (term35 _106233 _106250 s i).
Proof. exact (fun_ext (fun a : _106233 => @lem4418891 _106233 _106250 s i a)). Qed.
Lemma lem4418893 {_106233 : Type'} : (@all _106233) = (@all _106233).
Proof. exact (eq_refl (@all _106233)). Qed.
Lemma lem4418895 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term36 _106233 _106250 s i) = (term36 _106233 _106250 s i).
Proof. exact (MK_COMB (@lem4418893 _106233) (@lem4418892 _106233 _106250 s i)). Qed.
Lemma lem4418896 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term36 _106233 _106250 s i.
Proof. exact (EQ_MP (@lem4418895 _106233 _106250 s i) (@lem4418867 _106233 _106250 x k s i h1)). Qed.
Lemma lem4418904 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (i : _106250) : (term194 _106233 _106250 k s a i) = (term194 _106233 _106250 k s a i).
Proof. exact (eq_refl (term194 _106233 _106250 k s a i)). Qed.
Lemma lem4418905 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) : (term196 _106233 _106250 k s a) = (term196 _106233 _106250 k s a).
Proof. exact (fun_ext (fun i : _106250 => @lem4418904 _106233 _106250 k s a i)). Qed.
Lemma lem4418906 {_106250 : Type'} : (@all _106250) = (@all _106250).
Proof. exact (eq_refl (@all _106250)). Qed.
Lemma lem4418908 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) : (term198 _106233 _106250 k s a) = (term198 _106233 _106250 k s a).
Proof. exact (MK_COMB (@lem4418906 _106250) (@lem4418905 _106233 _106250 k s a)). Qed.
Lemma lem4418909 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term198 _106233 _106250 k s a.
Proof. exact (EQ_MP (@lem4418908 _106233 _106250 k s a) (@lem4418869 _106233 _106250 i k s a h1)). Qed.
Lemma lem4418915 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (x : _106233) : (term33 _106233 _106250 s i x) = (term33 _106233 _106250 s i x).
Proof. exact (eq_refl (term33 _106233 _106250 s i x)). Qed.
Lemma lem4418916 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term35 _106233 _106250 s i) = (term35 _106233 _106250 s i).
Proof. exact (fun_ext (fun x : _106233 => @lem4418915 _106233 _106250 s i x)). Qed.
Lemma lem4418917 {_106233 : Type'} : (@all _106233) = (@all _106233).
Proof. exact (eq_refl (@all _106233)). Qed.
Lemma lem4418919 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) : (term36 _106233 _106250 s i) = (term36 _106233 _106250 s i).
Proof. exact (MK_COMB (@lem4418917 _106233) (@lem4418916 _106233 _106250 s i)). Qed.
Lemma lem4418920 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term36 _106233 _106250 s i.
Proof. exact (EQ_MP (@lem4418919 _106233 _106250 s i) (@lem4418871 _106233 _106250 i k s a h1)). Qed.
Lemma lem4418921 {_106233 _106250 : Type'} (_50916 : _106250) (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term321 _106233 _106250 k s x _50916.
Proof. exact (@lem4418885 _106233 _106250 x k s i h1 _50916). Qed.
Lemma lem4418922 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) (_50916 : _106250) : (term321 _106233 _106250 k s x _50916) = (term194 _106233 _106250 k s x _50916).
Proof. exact (eq_refl (term321 _106233 _106250 k s x _50916)). Qed.
Lemma lem4418924 {_106233 _106250 : Type'} (_50917 : _106233) (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term74 _106233 _106250 s i _50917.
Proof. exact (@lem4418896 _106233 _106250 x k s i h1 _50917). Qed.
Lemma lem4418925 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (_50917 : _106233) : (term74 _106233 _106250 s i _50917) = (term33 _106233 _106250 s i _50917).
Proof. exact (eq_refl (term74 _106233 _106250 s i _50917)). Qed.
Lemma lem4418927 {_106233 _106250 : Type'} (_50918 : _106250) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term321 _106233 _106250 k s a _50918.
Proof. exact (@lem4418909 _106233 _106250 i k s a h1 _50918). Qed.
Lemma lem4418928 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (_50918 : _106250) : (term321 _106233 _106250 k s a _50918) = (term194 _106233 _106250 k s a _50918).
Proof. exact (eq_refl (term321 _106233 _106250 k s a _50918)). Qed.
Lemma lem4418930 {_106233 _106250 : Type'} (_50919 : _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term74 _106233 _106250 s i _50919.
Proof. exact (@lem4418920 _106233 _106250 i k s a h1 _50919). Qed.
Lemma lem4418931 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (_50919 : _106233) : (term74 _106233 _106250 s i _50919) = (term33 _106233 _106250 s i _50919).
Proof. exact (eq_refl (term74 _106233 _106250 s i _50919)). Qed.
Lemma lem4418938 {_106233 _106250 : Type'} (_50916 : _106250) (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term194 _106233 _106250 k s x _50916.
Proof. exact (EQ_MP (@lem4418922 _106233 _106250 k s x _50916) (@lem4418921 _106233 _106250 _50916 x k s i h1)). Qed.
Lemma lem4418942 {_106233 _106250 : Type'} (_50917 : _106233) (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term33 _106233 _106250 s i _50917.
Proof. exact (EQ_MP (@lem4418925 _106233 _106250 s i _50917) (@lem4418924 _106233 _106250 _50917 x k s i h1)). Qed.
Lemma lem4418948 {_106233 _106250 : Type'} (_50918 : _106250) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term194 _106233 _106250 k s a _50918.
Proof. exact (EQ_MP (@lem4418928 _106233 _106250 k s a _50918) (@lem4418927 _106233 _106250 _50918 i k s a h1)). Qed.
Lemma lem4418952 {_106233 _106250 : Type'} (_50919 : _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term33 _106233 _106250 s i _50919.
Proof. exact (EQ_MP (@lem4418931 _106233 _106250 s i _50919) (@lem4418930 _106233 _106250 _50919 i k s a h1)). Qed.
Lemma lem4418954 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : k i.
Proof. exact (proj1 (@lem4418865 _106233 _106250 x k s i h1)). Qed.
Lemma lem4418955 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term322 _106250 k i.
Proof. exact (fun h0 : term153 _106250 k i => @lem4418954 _106233 _106250 x k s i h1). Qed.
Lemma lem4418957 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4418958 {_106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term322 _106250 k i) = (k i).
Proof. exact (@lem4418957 (k i)). Qed.
Lemma lem4418959 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : k i.
Proof. exact (EQ_MP (@lem4418958 _106250 k i) (@lem4418955 _106233 _106250 x k s i h1)). Qed.
Lemma lem4418965 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4418966 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (x : _106250 -> _106233) (k : _106250 -> Prop) (_50916 : _106250) : (term194 _106233 _106250 k s x _50916) = (term324 _106233 _106250 s x k _50916).
Proof. exact (@lem4418965 (term325 _106233 _106250 s x _50916) (term153 _106250 k _50916)). Qed.
Lemma lem4418972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4418973 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (x : _106250 -> _106233) (k : _106250 -> Prop) (_50916 : _106250) : (term326 _106233 _106250 k s x _50916) = (term327 _106233 _106250 s x k _50916).
Proof. exact (MK_COMB (@lem4418972) (@lem4418966 _106233 _106250 s x k _50916)). Qed.
Lemma lem4418979 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (x : _106250 -> _106233) (k : _106250 -> Prop) (_50916 : _106250) : (term324 _106233 _106250 s x k _50916) = (term324 _106233 _106250 s x k _50916).
Proof. exact (eq_refl (term324 _106233 _106250 s x k _50916)). Qed.
Lemma lem4418980 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (x : _106250 -> _106233) (k : _106250 -> Prop) (_50916 : _106250) : ((term194 _106233 _106250 k s x _50916) = (term324 _106233 _106250 s x k _50916)) = ((term324 _106233 _106250 s x k _50916) = (term324 _106233 _106250 s x k _50916)).
Proof. exact (MK_COMB (@lem4418973 _106233 _106250 s x k _50916) (@lem4418979 _106233 _106250 s x k _50916)). Qed.
Lemma lem4418982 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4418983 (x : Prop) : (x = x) = True.
Proof. exact (@lem4418982 Prop x). Qed.
Lemma lem4418984 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (x : _106250 -> _106233) (k : _106250 -> Prop) (_50916 : _106250) : ((term324 _106233 _106250 s x k _50916) = (term324 _106233 _106250 s x k _50916)) = True.
Proof. exact (@lem4418983 (term324 _106233 _106250 s x k _50916)). Qed.
Lemma lem4418985 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (x : _106250 -> _106233) (k : _106250 -> Prop) (_50916 : _106250) : ((term194 _106233 _106250 k s x _50916) = (term324 _106233 _106250 s x k _50916)) = True.
Proof. exact (TRANS (@lem4418980 _106233 _106250 s x k _50916) (@lem4418984 _106233 _106250 s x k _50916)). Qed.
Lemma lem4418986 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (x : _106250 -> _106233) (k : _106250 -> Prop) (_50916 : _106250) : True = ((term194 _106233 _106250 k s x _50916) = (term324 _106233 _106250 s x k _50916)).
Proof. exact (SYM (@lem4418985 _106233 _106250 s x k _50916)). Qed.
Lemma lem4418987 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (x : _106250 -> _106233) (k : _106250 -> Prop) (_50916 : _106250) : (term194 _106233 _106250 k s x _50916) = (term324 _106233 _106250 s x k _50916).
Proof. exact (EQ_MP (@lem4418986 _106233 _106250 s x k _50916) (@lem0)). Qed.
Lemma lem4418988 {_106233 _106250 : Type'} (_50916 : _106250) (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term324 _106233 _106250 s x k _50916.
Proof. exact (EQ_MP (@lem4418987 _106233 _106250 s x k _50916) (@lem4418938 _106233 _106250 _50916 x k s i h1)). Qed.
Lemma lem4418990 (b : Prop) (a : Prop) : (a \/ b) = (term328 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4418991 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) (_50916 : _106250) : (term324 _106233 _106250 s x k _50916) = (term329 _106233 _106250 k s x _50916).
Proof. exact (@lem4418990 (term153 _106250 k _50916) (term325 _106233 _106250 s x _50916)). Qed.
Lemma lem4418993 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4418994 {_106250 : Type'} (k : _106250 -> Prop) (_50916 : _106250) : (term330 _106250 k _50916) = (k _50916).
Proof. exact (@lem4418993 (k _50916)). Qed.
Lemma lem4418995 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4418996 {_106250 : Type'} (k : _106250 -> Prop) (_50916 : _106250) : (term331 _106250 k _50916) = (term43 _106250 k _50916).
Proof. exact (MK_COMB (@lem4418995) (@lem4418994 _106250 k _50916)). Qed.
Lemma lem4418997 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (x : _106250 -> _106233) (_50916 : _106250) : (term325 _106233 _106250 s x _50916) = (term325 _106233 _106250 s x _50916).
Proof. exact (eq_refl (term325 _106233 _106250 s x _50916)). Qed.
Lemma lem4418998 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) (_50916 : _106250) : (term329 _106233 _106250 k s x _50916) = (term332 _106233 _106250 k s x _50916).
Proof. exact (MK_COMB (@lem4418996 _106250 k _50916) (@lem4418997 _106233 _106250 s x _50916)). Qed.
Lemma lem4418999 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (x : _106250 -> _106233) (_50916 : _106250) : (term324 _106233 _106250 s x k _50916) = (term332 _106233 _106250 k s x _50916).
Proof. exact (TRANS (@lem4418991 _106233 _106250 k s x _50916) (@lem4418998 _106233 _106250 k s x _50916)). Qed.
Lemma lem4419002 {_106233 _106250 : Type'} (_50916 : _106250) (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term332 _106233 _106250 k s x _50916.
Proof. exact (EQ_MP (@lem4418999 _106233 _106250 k s x _50916) (@lem4418988 _106233 _106250 _50916 x k s i h1)). Qed.
Lemma lem4419003 {_106233 _106250 : Type'} (_50916 : _106250) (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term332 _106233 _106250 k s x _50916.
Proof. exact (@lem4419002 _106233 _106250 _50916 x k s i h1). Qed.
Lemma lem4419004 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term332 _106233 _106250 k s x i.
Proof. exact (@lem4419003 _106233 _106250 i x k s i h1). Qed.
Lemma lem4419007 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term325 _106233 _106250 s x i.
Proof. exact (@lem4419004 _106233 _106250 x k s i h1 (@lem4418959 _106233 _106250 x k s i h1)). Qed.
Lemma lem4419008 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term333 _106233 _106250 s x i.
Proof. exact (fun h0 : term334 _106233 _106250 s x i => @lem4419007 _106233 _106250 x k s i h1). Qed.
Lemma lem4419010 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4419011 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (x : _106250 -> _106233) (i : _106250) : (term333 _106233 _106250 s x i) = (term325 _106233 _106250 s x i).
Proof. exact (@lem4419010 (term325 _106233 _106250 s x i)). Qed.
Lemma lem4419012 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term325 _106233 _106250 s x i.
Proof. exact (EQ_MP (@lem4419011 _106233 _106250 s x i) (@lem4419008 _106233 _106250 x k s i h1)). Qed.
Lemma lem4419015 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4419017 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (_50917 : _106233) : (term33 _106233 _106250 s i _50917) = (term335 _106233 _106250 s i _50917).
Proof. exact (@lem4419015 (s i _50917)). Qed.
Lemma lem4419020 {_106233 _106250 : Type'} (_50917 : _106233) (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term335 _106233 _106250 s i _50917.
Proof. exact (EQ_MP (@lem4419017 _106233 _106250 s i _50917) (@lem4418942 _106233 _106250 _50917 x k s i h1)). Qed.
Lemma lem4419021 {_106233 _106250 : Type'} (_50917 : _106233) (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term335 _106233 _106250 s i _50917.
Proof. exact (@lem4419020 _106233 _106250 _50917 x k s i h1). Qed.
Lemma lem4419022 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term336 _106233 _106250 s x i.
Proof. exact (@lem4419021 _106233 _106250 (x i) x k s i h1). Qed.
Lemma lem4419025 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : False.
Proof. exact (@lem4419022 _106233 _106250 x k s i h1 (@lem4419012 _106233 _106250 x k s i h1)). Qed.
Lemma lem4419026 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : term337.
Proof. exact (fun h0 : ~ False => @lem4419025 _106233 _106250 x k s i h1). Qed.
Lemma lem4419028 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4419029 : term337 = False.
Proof. exact (@lem4419028 False). Qed.
Lemma lem4419030 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (i : _106250) (h1 : term232 _106233 _106250 x k s i) : False.
Proof. exact (EQ_MP (@lem4419029) (@lem4419026 _106233 _106250 x k s i h1)). Qed.
Lemma lem4419032 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : k i.
Proof. exact (proj1 (@lem4418870 _106233 _106250 i k s a h1)). Qed.
Lemma lem4419033 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term322 _106250 k i.
Proof. exact (fun h0 : term153 _106250 k i => @lem4419032 _106233 _106250 i k s a h1). Qed.
Lemma lem4419035 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4419036 {_106250 : Type'} (k : _106250 -> Prop) (i : _106250) : (term322 _106250 k i) = (k i).
Proof. exact (@lem4419035 (k i)). Qed.
Lemma lem4419037 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : k i.
Proof. exact (EQ_MP (@lem4419036 _106250 k i) (@lem4419033 _106233 _106250 i k s a h1)). Qed.
Lemma lem4419043 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4419044 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (a : _106250 -> _106233) (k : _106250 -> Prop) (_50918 : _106250) : (term194 _106233 _106250 k s a _50918) = (term324 _106233 _106250 s a k _50918).
Proof. exact (@lem4419043 (term325 _106233 _106250 s a _50918) (term153 _106250 k _50918)). Qed.
Lemma lem4419050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4419051 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (a : _106250 -> _106233) (k : _106250 -> Prop) (_50918 : _106250) : (term326 _106233 _106250 k s a _50918) = (term327 _106233 _106250 s a k _50918).
Proof. exact (MK_COMB (@lem4419050) (@lem4419044 _106233 _106250 s a k _50918)). Qed.
Lemma lem4419057 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (a : _106250 -> _106233) (k : _106250 -> Prop) (_50918 : _106250) : (term324 _106233 _106250 s a k _50918) = (term324 _106233 _106250 s a k _50918).
Proof. exact (eq_refl (term324 _106233 _106250 s a k _50918)). Qed.
Lemma lem4419058 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (a : _106250 -> _106233) (k : _106250 -> Prop) (_50918 : _106250) : ((term194 _106233 _106250 k s a _50918) = (term324 _106233 _106250 s a k _50918)) = ((term324 _106233 _106250 s a k _50918) = (term324 _106233 _106250 s a k _50918)).
Proof. exact (MK_COMB (@lem4419051 _106233 _106250 s a k _50918) (@lem4419057 _106233 _106250 s a k _50918)). Qed.
Lemma lem4419060 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4419061 (x : Prop) : (x = x) = True.
Proof. exact (@lem4419060 Prop x). Qed.
Lemma lem4419062 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (a : _106250 -> _106233) (k : _106250 -> Prop) (_50918 : _106250) : ((term324 _106233 _106250 s a k _50918) = (term324 _106233 _106250 s a k _50918)) = True.
Proof. exact (@lem4419061 (term324 _106233 _106250 s a k _50918)). Qed.
Lemma lem4419063 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (a : _106250 -> _106233) (k : _106250 -> Prop) (_50918 : _106250) : ((term194 _106233 _106250 k s a _50918) = (term324 _106233 _106250 s a k _50918)) = True.
Proof. exact (TRANS (@lem4419058 _106233 _106250 s a k _50918) (@lem4419062 _106233 _106250 s a k _50918)). Qed.
Lemma lem4419064 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (a : _106250 -> _106233) (k : _106250 -> Prop) (_50918 : _106250) : True = ((term194 _106233 _106250 k s a _50918) = (term324 _106233 _106250 s a k _50918)).
Proof. exact (SYM (@lem4419063 _106233 _106250 s a k _50918)). Qed.
Lemma lem4419065 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (a : _106250 -> _106233) (k : _106250 -> Prop) (_50918 : _106250) : (term194 _106233 _106250 k s a _50918) = (term324 _106233 _106250 s a k _50918).
Proof. exact (EQ_MP (@lem4419064 _106233 _106250 s a k _50918) (@lem0)). Qed.
Lemma lem4419066 {_106233 _106250 : Type'} (_50918 : _106250) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term324 _106233 _106250 s a k _50918.
Proof. exact (EQ_MP (@lem4419065 _106233 _106250 s a k _50918) (@lem4418948 _106233 _106250 _50918 i k s a h1)). Qed.
Lemma lem4419068 (b : Prop) (a : Prop) : (a \/ b) = (term328 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4419069 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (_50918 : _106250) : (term324 _106233 _106250 s a k _50918) = (term329 _106233 _106250 k s a _50918).
Proof. exact (@lem4419068 (term153 _106250 k _50918) (term325 _106233 _106250 s a _50918)). Qed.
Lemma lem4419071 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4419072 {_106250 : Type'} (k : _106250 -> Prop) (_50918 : _106250) : (term330 _106250 k _50918) = (k _50918).
Proof. exact (@lem4419071 (k _50918)). Qed.
Lemma lem4419073 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4419074 {_106250 : Type'} (k : _106250 -> Prop) (_50918 : _106250) : (term331 _106250 k _50918) = (term43 _106250 k _50918).
Proof. exact (MK_COMB (@lem4419073) (@lem4419072 _106250 k _50918)). Qed.
Lemma lem4419075 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (a : _106250 -> _106233) (_50918 : _106250) : (term325 _106233 _106250 s a _50918) = (term325 _106233 _106250 s a _50918).
Proof. exact (eq_refl (term325 _106233 _106250 s a _50918)). Qed.
Lemma lem4419076 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (_50918 : _106250) : (term329 _106233 _106250 k s a _50918) = (term332 _106233 _106250 k s a _50918).
Proof. exact (MK_COMB (@lem4419074 _106250 k _50918) (@lem4419075 _106233 _106250 s a _50918)). Qed.
Lemma lem4419077 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (_50918 : _106250) : (term324 _106233 _106250 s a k _50918) = (term332 _106233 _106250 k s a _50918).
Proof. exact (TRANS (@lem4419069 _106233 _106250 k s a _50918) (@lem4419076 _106233 _106250 k s a _50918)). Qed.
Lemma lem4419080 {_106233 _106250 : Type'} (_50918 : _106250) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term332 _106233 _106250 k s a _50918.
Proof. exact (EQ_MP (@lem4419077 _106233 _106250 k s a _50918) (@lem4419066 _106233 _106250 _50918 i k s a h1)). Qed.
Lemma lem4419081 {_106233 _106250 : Type'} (_50918 : _106250) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term332 _106233 _106250 k s a _50918.
Proof. exact (@lem4419080 _106233 _106250 _50918 i k s a h1). Qed.
Lemma lem4419082 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term332 _106233 _106250 k s a i.
Proof. exact (@lem4419081 _106233 _106250 i i k s a h1). Qed.
Lemma lem4419085 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term325 _106233 _106250 s a i.
Proof. exact (@lem4419082 _106233 _106250 i k s a h1 (@lem4419037 _106233 _106250 i k s a h1)). Qed.
Lemma lem4419086 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term333 _106233 _106250 s a i.
Proof. exact (fun h0 : term334 _106233 _106250 s a i => @lem4419085 _106233 _106250 i k s a h1). Qed.
Lemma lem4419088 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4419089 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (a : _106250 -> _106233) (i : _106250) : (term333 _106233 _106250 s a i) = (term325 _106233 _106250 s a i).
Proof. exact (@lem4419088 (term325 _106233 _106250 s a i)). Qed.
Lemma lem4419090 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term325 _106233 _106250 s a i.
Proof. exact (EQ_MP (@lem4419089 _106233 _106250 s a i) (@lem4419086 _106233 _106250 i k s a h1)). Qed.
Lemma lem4419093 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4419095 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (i : _106250) (_50919 : _106233) : (term33 _106233 _106250 s i _50919) = (term335 _106233 _106250 s i _50919).
Proof. exact (@lem4419093 (s i _50919)). Qed.
Lemma lem4419098 {_106233 _106250 : Type'} (_50919 : _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term335 _106233 _106250 s i _50919.
Proof. exact (EQ_MP (@lem4419095 _106233 _106250 s i _50919) (@lem4418952 _106233 _106250 _50919 i k s a h1)). Qed.
Lemma lem4419099 {_106233 _106250 : Type'} (_50919 : _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term335 _106233 _106250 s i _50919.
Proof. exact (@lem4419098 _106233 _106250 _50919 i k s a h1). Qed.
Lemma lem4419100 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term336 _106233 _106250 s a i.
Proof. exact (@lem4419099 _106233 _106250 (a i) i k s a h1). Qed.
Lemma lem4419103 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : False.
Proof. exact (@lem4419100 _106233 _106250 i k s a h1 (@lem4419090 _106233 _106250 i k s a h1)). Qed.
Lemma lem4419104 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : term337.
Proof. exact (fun h0 : ~ False => @lem4419103 _106233 _106250 i k s a h1). Qed.
Lemma lem4419106 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4419107 : term337 = False.
Proof. exact (@lem4419106 False). Qed.
Lemma lem4419108 {_106233 _106250 : Type'} (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term259 _106233 _106250 i k s a) : False.
Proof. exact (EQ_MP (@lem4419107) (@lem4419104 _106233 _106250 i k s a h1)). Qed.
Lemma lem4419109 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term313 _106233 _106250 x i k s a) : False.
Proof. exact (or_elim (@lem4418862 _106233 _106250 x i k s a h1) (fun h0 : term232 _106233 _106250 x k s i => @lem4419030 _106233 _106250 x k s i h0) (fun h0 : term259 _106233 _106250 i k s a => @lem4419108 _106233 _106250 i k s a h0)). Qed.
Lemma lem4419110 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term313 _106233 _106250 x i k s a) : (term313 _106233 _106250 x i k s a) = False.
Proof. exact (prop_ext (fun h2 : term313 _106233 _106250 x i k s a => @lem4419109 _106233 _106250 x i k s a h1) (fun h2 : False => @lem4418862 _106233 _106250 x i k s a h1)). Qed.
Lemma lem4419111 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (a : _106250 -> _106233) (h1 : term313 _106233 _106250 x i k s a) : False.
Proof. exact (EQ_MP (@lem4419110 _106233 _106250 x i k s a h1) (@lem4418862 _106233 _106250 x i k s a h1)). Qed.
Lemma lem4419112 {_106233 _106250 : Type'} (x : _106250 -> _106233) (i : _106250) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term316 _106233 _106250 x i k s) : False.
Proof. exact (ex_elim (@lem4418783 _106233 _106250 x i k s h1) (fun a : _106250 -> _106233 => fun h0 : term315 _106233 _106250 x i k s a => @lem4419111 _106233 _106250 x i k s a h0)). Qed.
Lemma lem4419113 {_106233 _106250 : Type'} (x : _106250 -> _106233) (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term318 _106233 _106250 x k s) : False.
Proof. exact (ex_elim (@lem4418782 _106233 _106250 x k s h1) (fun i : _106250 => fun h0 : term317 _106233 _106250 x k s i => @lem4419112 _106233 _106250 x i k s h0)). Qed.
Lemma lem4419114 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term55 _106233 _106250 k s) : False.
Proof. exact (ex_elim (@lem4418781 _106233 _106250 k s h1) (fun x : _106250 -> _106233 => fun h0 : term319 _106233 _106250 k s x => @lem4419113 _106233 _106250 x k s h0)). Qed.
Lemma lem4419115 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term55 _106233 _106250 k s) : (term55 _106233 _106250 k s) = False.
Proof. exact (prop_ext (fun h2 : term55 _106233 _106250 k s => @lem4419114 _106233 _106250 k s h1) (fun h2 : False => @lem4418127 _106233 _106250 k s h1)). Qed.
Lemma lem4419116 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term55 _106233 _106250 k s) : False.
Proof. exact (EQ_MP (@lem4419115 _106233 _106250 k s h1) (@lem4418127 _106233 _106250 k s h1)). Qed.
Lemma lem4419117 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : term54 _106233 _106250 k s.
Proof. exact (fun h0 : term55 _106233 _106250 k s => @lem4419116 _106233 _106250 k s h0). Qed.
Lemma lem4419118 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term40 _106233 _106250 k s) = (term52 _106233 _106250 k s).
Proof. exact (EQ_MP (@lem4418126 _106233 _106250 k s) (@lem4419117 _106233 _106250 k s)). Qed.
Lemma lem4419123 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) : term64 _106233 _106250 s.
Proof. exact (fun k : _106250 -> Prop => @lem4419118 _106233 _106250 k s). Qed.
Lemma lem4419128 {_106233 _106250 : Type'} : term68 _106233 _106250.
Proof. exact (fun s : type1470 _106233 _106250 => @lem4419123 _106233 _106250 s). Qed.
Lemma lem4419129 {_106233 _106250 : Type'} : term67 _106233 _106250.
Proof. exact (EQ_MP (@lem4418122 _106233 _106250) (@lem4419128 _106233 _106250)). Qed.
Lemma lem4419130 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) : term338 _106233 _106250 s.
Proof. exact (@lem4419129 _106233 _106250 s). Qed.
Lemma lem4419131 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) : (term338 _106233 _106250 s) = (term63 _106233 _106250 s).
Proof. exact (eq_refl (term338 _106233 _106250 s)). Qed.
Lemma lem4419132 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) : term63 _106233 _106250 s.
Proof. exact (EQ_MP (@lem4419131 _106233 _106250 s) (@lem4419130 _106233 _106250 s)). Qed.
Lemma lem4419133 {_106233 _106250 : Type'} (s : type1470 _106233 _106250) (k : _106250 -> Prop) : term339 _106233 _106250 s k.
Proof. exact (@lem4419132 _106233 _106250 s k). Qed.
Lemma lem4419134 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term339 _106233 _106250 s k) = (term54 _106233 _106250 k s).
Proof. exact (eq_refl (term339 _106233 _106250 s k)). Qed.
Lemma lem4419135 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : term54 _106233 _106250 k s.
Proof. exact (EQ_MP (@lem4419134 _106233 _106250 k s) (@lem4419133 _106233 _106250 s k)). Qed.
Lemma lem4419137 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : term54 _106233 _106250 k s.
Proof. exact (@lem4417966 _106233 _106250 k s (@lem4419135 _106233 _106250 k s)). Qed.
Lemma lem4419138 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term55 _106233 _106250 k s) : False.
Proof. exact (@lem4419137 _106233 _106250 k s (@lem4417950 _106233 _106250 k s h1)). Qed.
Lemma lem4419139 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term55 _106233 _106250 k s) : (term55 _106233 _106250 k s) = False.
Proof. exact (prop_ext (fun h2 : term55 _106233 _106250 k s => @lem4419138 _106233 _106250 k s h1) (fun h2 : False => @lem4417950 _106233 _106250 k s h1)). Qed.
Lemma lem4419140 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) (h1 : term55 _106233 _106250 k s) : False.
Proof. exact (EQ_MP (@lem4419139 _106233 _106250 k s h1) (@lem4417950 _106233 _106250 k s h1)). Qed.
Lemma lem4419141 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : term54 _106233 _106250 k s.
Proof. exact (fun h0 : term55 _106233 _106250 k s => @lem4419140 _106233 _106250 k s h0). Qed.
Lemma lem4419142 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term40 _106233 _106250 k s) = (term52 _106233 _106250 k s).
Proof. exact (EQ_MP (@lem4417949 _106233 _106250 k s) (@lem4419141 _106233 _106250 k s)). Qed.
Lemma lem4419143 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term25 _106233 _106250 k s) = (term28 _106233 _106250 k s).
Proof. exact (EQ_MP (@lem4417945 _106233 _106250 k s) (@lem4419142 _106233 _106250 k s)). Qed.
Lemma lem4419145 {A K : Type'} (k : K -> Prop) : term340 A K k.
Proof. exact (@lem4408929 A K k). Qed.
Lemma lem4419146 {A K : Type'} (k : K -> Prop) : (term340 A K k) = (term341 A K k).
Proof. exact (eq_refl (term340 A K k)). Qed.
Lemma lem4419147 {A K : Type'} (k : K -> Prop) : term341 A K k.
Proof. exact (EQ_MP (@lem4419146 A K k) (@lem4419145 A K k)). Qed.
Lemma lem4419148 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term342 A K k s.
Proof. exact (@lem4419147 A K k s). Qed.
Lemma lem4419149 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term342 A K k s) = (((@cartesian_product A K k s) = (@EMPTY (K -> A))) = (term22 A K k s)).
Proof. exact (eq_refl (term342 A K k s)). Qed.
Lemma lem4419185 {_83095 : Type'} : term343 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4419186 {_83095 : Type'} (p : _83095 -> Prop) : term344 _83095 p.
Proof. exact (@lem4419185 _83095 p). Qed.
Lemma lem4419187 {_83095 : Type'} (p : _83095 -> Prop) : (term344 _83095 p) = (term345 _83095 p).
Proof. exact (eq_refl (term344 _83095 p)). Qed.
Lemma lem4419188 {_83095 : Type'} (p : _83095 -> Prop) : term345 _83095 p.
Proof. exact (EQ_MP (@lem4419187 _83095 p) (@lem4419186 _83095 p)). Qed.
Lemma lem4419189 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term346 _83095 p x.
Proof. exact (@lem4419188 _83095 p x). Qed.
Lemma lem4419190 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term346 _83095 p x) = ((term347 _83095 x p) = (p x)).
Proof. exact (eq_refl (term346 _83095 p x)). Qed.
Lemma lem4419199 {A K : Type'} (k : K -> Prop) : term348 A K k.
Proof. exact (@lem4399444 A K k). Qed.
Lemma lem4419200 {A K : Type'} (k : K -> Prop) : (term348 A K k) = (term349 A K k).
Proof. exact (eq_refl (term348 A K k)). Qed.
Lemma lem4419201 {A K : Type'} (k : K -> Prop) : term349 A K k.
Proof. exact (EQ_MP (@lem4419200 A K k) (@lem4419199 A K k)). Qed.
Lemma lem4419202 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term350 A K k s.
Proof. exact (@lem4419201 A K k s). Qed.
Lemma lem4419203 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term350 A K k s) = ((@cartesian_product A K k s) = (term351 A K k s)).
Proof. exact (eq_refl (term350 A K k s)). Qed.
Lemma lem4419205 {A : Type'} (s : A -> Prop) : term352 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4419206 {A : Type'} (s : A -> Prop) : (term352 A s) = (term353 A s).
Proof. exact (eq_refl (term352 A s)). Qed.
Lemma lem4419207 {A : Type'} (s : A -> Prop) : term353 A s.
Proof. exact (EQ_MP (@lem4419206 A s) (@lem4419205 A s)). Qed.
Lemma lem4419208 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term354 A s t.
Proof. exact (@lem4419207 A s t). Qed.
Lemma lem4419209 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term354 A s t) = ((@SUBSET A s t) = (term355 A s t)).
Proof. exact (eq_refl (term354 A s t)). Qed.
Lemma lem4419211 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term356 A K k s.
Proof. exact (@lem9784 ((@cartesian_product A K k s) = (@EMPTY (K -> A)))). Qed.
Lemma lem4419212 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term356 A K k s) = (term357 A K k s).
Proof. exact (eq_refl (term356 A K k s)). Qed.
Lemma lem4419213 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term357 A K k s.
Proof. exact (EQ_MP (@lem4419212 A K k s) (@lem4419211 A K k s)). Qed.
Lemma lem4419215 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term358 A K k s) : term358 A K k s.
Proof. exact (h1). Qed.
Lemma lem4419216 {A : Type'} (s : A -> Prop) : term359 A s.
Proof. exact (@lem3219985 A s). Qed.
Lemma lem4419217 {A : Type'} (s : A -> Prop) : (term359 A s) = (@SUBSET A (@EMPTY A) s).
Proof. exact (eq_refl (term359 A s)). Qed.
Lemma lem4419218 {A : Type'} (s : A -> Prop) : @SUBSET A (@EMPTY A) s.
Proof. exact (EQ_MP (@lem4419217 A s) (@lem4419216 A s)). Qed.
Lemma lem4419219 {A : Type'} (s : A -> Prop) : (@SUBSET A (@EMPTY A) s) = ((@SUBSET A (@EMPTY A) s) = True).
Proof. exact (@lem7 (@SUBSET A (@EMPTY A) s)). Qed.
Lemma lem4419224 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (@cartesian_product A K k s) = (@EMPTY (K -> A)).
Proof. exact (h1). Qed.
Lemma lem4419225 {A K : Type'} : (@SUBSET (K -> A)) = (@SUBSET (K -> A)).
Proof. exact (eq_refl (@SUBSET (K -> A))). Qed.
Lemma lem4419226 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term360 A K k s) = (@SUBSET (K -> A) (@EMPTY (K -> A))).
Proof. exact (MK_COMB (@lem4419225 A K) (@lem4419224 A K k s h1)). Qed.
Lemma lem4419227 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@cartesian_product A K k t) = (@cartesian_product A K k t).
Proof. exact (eq_refl (@cartesian_product A K k t)). Qed.
Lemma lem4419228 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term361 A K s k t) = (term362 A K k t).
Proof. exact (MK_COMB (@lem4419226 A K k s h1) (@lem4419227 A K k t)). Qed.
Lemma lem4419230 {A : Type'} (s : A -> Prop) : (@SUBSET A (@EMPTY A) s) = True.
Proof. exact (EQ_MP (@lem4419219 A s) (@lem4419218 A s)). Qed.
Lemma lem4419231 {A K : Type'} (s : type805 A K) : (@SUBSET (K -> A) (@EMPTY (K -> A)) s) = True.
Proof. exact (@lem4419230 (K -> A) s). Qed.
Lemma lem4419232 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term362 A K k t) = True.
Proof. exact (@lem4419231 A K (@cartesian_product A K k t)). Qed.
Lemma lem4419233 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term361 A K s k t) = True.
Proof. exact (TRANS (@lem4419228 A K t k s h1) (@lem4419232 A K k t)). Qed.
Lemma lem4419234 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4419235 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term363 A K s k t) = (@eq Prop True).
Proof. exact (MK_COMB (@lem4419234) (@lem4419233 A K t k s h1)). Qed.
Lemma lem4419241 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (@cartesian_product A K k s) = (@EMPTY (K -> A)).
Proof. exact (h1). Qed.
Lemma lem4419242 {A K : Type'} : (@eq ((K -> A) -> Prop)) = (@eq ((K -> A) -> Prop)).
Proof. exact (eq_refl (@eq ((K -> A) -> Prop))). Qed.
Lemma lem4419243 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term364 A K k s) = (@eq ((K -> A) -> Prop) (@EMPTY (K -> A))).
Proof. exact (MK_COMB (@lem4419242 A K) (@lem4419241 A K k s h1)). Qed.
Lemma lem4419244 {A K : Type'} : (@EMPTY (K -> A)) = (@EMPTY (K -> A)).
Proof. exact (eq_refl (@EMPTY (K -> A))). Qed.
Lemma lem4419245 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = ((@EMPTY (K -> A)) = (@EMPTY (K -> A))).
Proof. exact (MK_COMB (@lem4419243 A K k s h1) (@lem4419244 A K)). Qed.
Lemma lem4419247 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4419248 {A K : Type'} (x : type805 A K) : (x = x) = True.
Proof. exact (@lem4419247 (type805 A K) x). Qed.
Lemma lem4419249 {A K : Type'} : ((@EMPTY (K -> A)) = (@EMPTY (K -> A))) = True.
Proof. exact (@lem4419248 A K (@EMPTY (K -> A))). Qed.
Lemma lem4419250 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = True.
Proof. exact (TRANS (@lem4419245 A K k s h1) (@lem4419249 A K)). Qed.
Lemma lem4419251 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4419252 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term365 A K k s) = (or True).
Proof. exact (MK_COMB (@lem4419251) (@lem4419250 A K k s h1)). Qed.
Lemma lem4419259 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term366 A K k s t) = (term366 A K k s t).
Proof. exact (eq_refl (term366 A K k s t)). Qed.
Lemma lem4419260 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term367 A K k s t) = (term368 A K k s t).
Proof. exact (MK_COMB (@lem4419252 A K k s h1) (@lem4419259 A K k s t)). Qed.
Lemma lem4419262 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem4419263 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term368 A K k s t) = True.
Proof. exact (@lem4419262 (term366 A K k s t)). Qed.
Lemma lem4419264 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term367 A K k s t) = True.
Proof. exact (TRANS (@lem4419260 A K t k s h1) (@lem4419263 A K k s t)). Qed.
Lemma lem4419265 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : ((term361 A K s k t) = (term367 A K k s t)) = (True = True).
Proof. exact (MK_COMB (@lem4419235 A K t k s h1) (@lem4419264 A K t k s h1)). Qed.
Lemma lem4419267 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4419268 : (True = True) = True.
Proof. exact (@lem4419267 True). Qed.
Lemma lem4419269 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : ((term361 A K s k t) = (term367 A K k s t)) = True.
Proof. exact (TRANS (@lem4419265 A K t k s h1) (@lem4419268)). Qed.
Lemma lem4419270 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : True = ((term361 A K s k t) = (term367 A K k s t)).
Proof. exact (SYM (@lem4419269 A K t k s h1)). Qed.
Lemma lem4419271 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term361 A K s k t) = (term367 A K k s t).
Proof. exact (EQ_MP (@lem4419270 A K t k s h1) (@lem0)). Qed.
Lemma lem4419277 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term369 A K k s.
Proof. exact (@lem82 ((@cartesian_product A K k s) = (@EMPTY (K -> A)))). Qed.
Lemma lem4419295 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term358 A K k s) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = False.
Proof. exact (@lem4419277 A K k s (@lem4419215 A K k s h1)). Qed.
Lemma lem4419296 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4419297 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term358 A K k s) : (term365 A K k s) = (or False).
Proof. exact (MK_COMB (@lem4419296) (@lem4419295 A K k s h1)). Qed.
Lemma lem4419304 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term366 A K k s t) = (term366 A K k s t).
Proof. exact (eq_refl (term366 A K k s t)). Qed.
Lemma lem4419305 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term358 A K k s) : (term367 A K k s t) = (term370 A K k s t).
Proof. exact (MK_COMB (@lem4419297 A K k s h1) (@lem4419304 A K k s t)). Qed.
Lemma lem4419307 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4419308 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term370 A K k s t) = (term366 A K k s t).
Proof. exact (@lem4419307 (term366 A K k s t)). Qed.
Lemma lem4419315 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term358 A K k s) : (term367 A K k s t) = (term366 A K k s t).
Proof. exact (TRANS (@lem4419305 A K t k s h1) (@lem4419308 A K k s t)). Qed.
Lemma lem4419316 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term363 A K s k t) = (term363 A K s k t).
Proof. exact (eq_refl (term363 A K s k t)). Qed.
Lemma lem4419317 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term358 A K k s) : ((term361 A K s k t) = (term367 A K k s t)) = ((term361 A K s k t) = (term366 A K k s t)).
Proof. exact (MK_COMB (@lem4419316 A K s k t) (@lem4419315 A K t k s h1)). Qed.
Lemma lem4419320 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term358 A K k s) : ((term361 A K s k t) = (term366 A K k s t)) = ((term361 A K s k t) = (term367 A K k s t)).
Proof. exact (SYM (@lem4419317 A K t k s h1)). Qed.
Lemma lem4419324 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term355 A s t).
Proof. exact (EQ_MP (@lem4419209 A s t) (@lem4419208 A s t)). Qed.
Lemma lem4419325 {A K : Type'} (s : type805 A K) (t : type805 A K) : (@SUBSET (K -> A) s t) = (term371 A K s t).
Proof. exact (@lem4419324 (K -> A) s t). Qed.
Lemma lem4419326 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term361 A K s k t) = (term372 A K s k t).
Proof. exact (@lem4419325 A K (@cartesian_product A K k s) (@cartesian_product A K k t)). Qed.
Lemma lem4419334 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term351 A K k s).
Proof. exact (EQ_MP (@lem4419203 A K k s) (@lem4419202 A K k s)). Qed.
Lemma lem4419335 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term351 A K k s).
Proof. exact (@lem4419334 A K k s). Qed.
Lemma lem4419348 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4419349 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term373 A K x k s) = (term374 A K x k s).
Proof. exact (MK_COMB (@lem4419348 A K x) (@lem4419335 A K k s)). Qed.
Lemma lem4419351 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term347 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4419190 _83095 p x) (@lem4419189 _83095 p x)). Qed.
Lemma lem4419352 {A K : Type'} (p : type805 A K) (x : K -> A) : (term375 A K x p) = (p x).
Proof. exact (@lem4419351 (K -> A) p x). Qed.
Lemma lem4419353 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term376 A K x k s) = (term377 A K k s x).
Proof. exact (@lem4419352 A K (term378 A K k s) x). Qed.
Lemma lem4419354 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term377 A K k s f) = (term379 A K k f s).
Proof. exact (eq_refl (term377 A K k s f)). Qed.
Lemma lem4419355 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4419356 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term380 A K GEN_PVAR_140 k s f) = (term381 A K GEN_PVAR_140 k f s).
Proof. exact (MK_COMB (@lem4419355 A K GEN_PVAR_140) (@lem4419354 A K k f s)). Qed.
Lemma lem4419357 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4419358 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term382 A K GEN_PVAR_140 k s f) = (term383 A K GEN_PVAR_140 k s f).
Proof. exact (MK_COMB (@lem4419356 A K GEN_PVAR_140 k f s) (@lem4419357 A K f)). Qed.
Lemma lem4419359 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term384 A K GEN_PVAR_140 k s) = (term385 A K GEN_PVAR_140 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4419358 A K GEN_PVAR_140 k s f)). Qed.
Lemma lem4419360 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4419361 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term386 A K GEN_PVAR_140 k s) = (term387 A K GEN_PVAR_140 k s).
Proof. exact (MK_COMB (@lem4419360 A K) (@lem4419359 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4419362 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term388 A K k s) = (term389 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4419361 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4419363 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4419364 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term390 A K k s) = (term351 A K k s).
Proof. exact (MK_COMB (@lem4419363 A K) (@lem4419362 A K k s)). Qed.
Lemma lem4419365 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4419366 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term376 A K x k s) = (term374 A K x k s).
Proof. exact (MK_COMB (@lem4419365 A K x) (@lem4419364 A K k s)). Qed.
Lemma lem4419367 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4419368 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term391 A K x k s) = (term392 A K x k s).
Proof. exact (MK_COMB (@lem4419367) (@lem4419366 A K x k s)). Qed.
Lemma lem4419369 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term377 A K k s x) = (term379 A K k x s).
Proof. exact (eq_refl (term377 A K k s x)). Qed.
Lemma lem4419370 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term376 A K x k s) = (term377 A K k s x)) = ((term374 A K x k s) = (term379 A K k x s)).
Proof. exact (MK_COMB (@lem4419368 A K x k s) (@lem4419369 A K k x s)). Qed.
Lemma lem4419371 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term374 A K x k s) = (term379 A K k x s).
Proof. exact (EQ_MP (@lem4419370 A K k x s) (@lem4419353 A K k s x)). Qed.
Lemma lem4419380 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term373 A K x k s) = (term379 A K k x s).
Proof. exact (TRANS (@lem4419349 A K x k s) (@lem4419371 A K k x s)). Qed.
Lemma lem4419381 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4419382 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term393 A K x k s) = (term394 A K k x s).
Proof. exact (MK_COMB (@lem4419381) (@lem4419380 A K k x s)). Qed.
Lemma lem4419384 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term351 A K k s).
Proof. exact (EQ_MP (@lem4419203 A K k s) (@lem4419202 A K k s)). Qed.
Lemma lem4419385 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term351 A K k s).
Proof. exact (@lem4419384 A K k s). Qed.
Lemma lem4419386 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@cartesian_product A K k t) = (term351 A K k t).
Proof. exact (@lem4419385 A K k t). Qed.
Lemma lem4419399 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4419400 {A K : Type'} (x : K -> A) (k : K -> Prop) (t : type1470 A K) : (term373 A K x k t) = (term374 A K x k t).
Proof. exact (MK_COMB (@lem4419399 A K x) (@lem4419386 A K k t)). Qed.
Lemma lem4419402 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term347 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4419190 _83095 p x) (@lem4419189 _83095 p x)). Qed.
Lemma lem4419403 {A K : Type'} (p : type805 A K) (x : K -> A) : (term375 A K x p) = (p x).
Proof. exact (@lem4419402 (K -> A) p x). Qed.
Lemma lem4419404 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term376 A K x k t) = (term377 A K k t x).
Proof. exact (@lem4419403 A K (term378 A K k t) x). Qed.
Lemma lem4419405 {A K : Type'} (k : K -> Prop) (f : K -> A) (t : type1470 A K) : (term377 A K k t f) = (term379 A K k f t).
Proof. exact (eq_refl (term377 A K k t f)). Qed.
Lemma lem4419406 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4419407 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (t : type1470 A K) : (term380 A K GEN_PVAR_140 k t f) = (term381 A K GEN_PVAR_140 k f t).
Proof. exact (MK_COMB (@lem4419406 A K GEN_PVAR_140) (@lem4419405 A K k f t)). Qed.
Lemma lem4419408 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4419409 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (t : type1470 A K) (f : K -> A) : (term382 A K GEN_PVAR_140 k t f) = (term383 A K GEN_PVAR_140 k t f).
Proof. exact (MK_COMB (@lem4419407 A K GEN_PVAR_140 k f t) (@lem4419408 A K f)). Qed.
Lemma lem4419410 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (t : type1470 A K) : (term384 A K GEN_PVAR_140 k t) = (term385 A K GEN_PVAR_140 k t).
Proof. exact (fun_ext (fun f : K -> A => @lem4419409 A K GEN_PVAR_140 k t f)). Qed.
Lemma lem4419411 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4419412 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (t : type1470 A K) : (term386 A K GEN_PVAR_140 k t) = (term387 A K GEN_PVAR_140 k t).
Proof. exact (MK_COMB (@lem4419411 A K) (@lem4419410 A K GEN_PVAR_140 k t)). Qed.
Lemma lem4419413 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term388 A K k t) = (term389 A K k t).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4419412 A K GEN_PVAR_140 k t)). Qed.
Lemma lem4419414 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4419415 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term390 A K k t) = (term351 A K k t).
Proof. exact (MK_COMB (@lem4419414 A K) (@lem4419413 A K k t)). Qed.
Lemma lem4419416 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4419417 {A K : Type'} (x : K -> A) (k : K -> Prop) (t : type1470 A K) : (term376 A K x k t) = (term374 A K x k t).
Proof. exact (MK_COMB (@lem4419416 A K x) (@lem4419415 A K k t)). Qed.
Lemma lem4419418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4419419 {A K : Type'} (x : K -> A) (k : K -> Prop) (t : type1470 A K) : (term391 A K x k t) = (term392 A K x k t).
Proof. exact (MK_COMB (@lem4419418) (@lem4419417 A K x k t)). Qed.
Lemma lem4419420 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term377 A K k t x) = (term379 A K k x t).
Proof. exact (eq_refl (term377 A K k t x)). Qed.
Lemma lem4419421 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : ((term376 A K x k t) = (term377 A K k t x)) = ((term374 A K x k t) = (term379 A K k x t)).
Proof. exact (MK_COMB (@lem4419419 A K x k t) (@lem4419420 A K k x t)). Qed.
Lemma lem4419422 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term374 A K x k t) = (term379 A K k x t).
Proof. exact (EQ_MP (@lem4419421 A K k x t) (@lem4419404 A K k t x)). Qed.
Lemma lem4419431 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term373 A K x k t) = (term379 A K k x t).
Proof. exact (TRANS (@lem4419400 A K x k t) (@lem4419422 A K k x t)). Qed.
Lemma lem4419432 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term395 A K s x k t) = (term396 A K s k x t).
Proof. exact (MK_COMB (@lem4419382 A K k x s) (@lem4419431 A K k x t)). Qed.
Lemma lem4419435 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term397 A K s k t) = (term398 A K s k t).
Proof. exact (fun_ext (fun x : K -> A => @lem4419432 A K s k x t)). Qed.
Lemma lem4419436 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4419437 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term372 A K s k t) = (term399 A K s k t).
Proof. exact (MK_COMB (@lem4419436 A K) (@lem4419435 A K s k t)). Qed.
Lemma lem4419442 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term361 A K s k t) = (term399 A K s k t).
Proof. exact (TRANS (@lem4419326 A K s k t) (@lem4419437 A K s k t)). Qed.
Lemma lem4419443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4419444 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term363 A K s k t) = (term400 A K s k t).
Proof. exact (MK_COMB (@lem4419443) (@lem4419442 A K s k t)). Qed.
Lemma lem4419452 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term355 A s t).
Proof. exact (EQ_MP (@lem4419209 A s t) (@lem4419208 A s t)). Qed.
Lemma lem4419453 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term355 A s t).
Proof. exact (@lem4419452 A s t). Qed.
Lemma lem4419454 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term401 A K s t i) = (term402 A K s t i).
Proof. exact (@lem4419453 A (s i) (t i)). Qed.
Lemma lem4419461 {K : Type'} (i : K) (k : K -> Prop) : (term42 K i k) = (term42 K i k).
Proof. exact (eq_refl (term42 K i k)). Qed.
Lemma lem4419462 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term403 A K k s t i) = (term404 A K k s t i).
Proof. exact (MK_COMB (@lem4419461 K i k) (@lem4419454 A K s t i)). Qed.
Lemma lem4419465 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term405 A K k s t) = (term406 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4419462 A K k s t i)). Qed.
Lemma lem4419466 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4419467 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term366 A K k s t) = (term407 A K k s t).
Proof. exact (MK_COMB (@lem4419466 K) (@lem4419465 A K k s t)). Qed.
Lemma lem4419472 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term361 A K s k t) = (term366 A K k s t)) = ((term399 A K s k t) = (term407 A K k s t)).
Proof. exact (MK_COMB (@lem4419444 A K s k t) (@lem4419467 A K k s t)). Qed.
Lemma lem4419475 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term399 A K s k t) = (term407 A K k s t)) = ((term361 A K s k t) = (term366 A K k s t)).
Proof. exact (SYM (@lem4419472 A K k s t)). Qed.
Lemma lem4419477 (p : Prop) : p = (term53 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4419478 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term408 A K s k t) = (term409 A K s k t).
Proof. exact (@lem4419477 (term408 A K s k t)). Qed.
Lemma lem4419479 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term409 A K s k t) = (term408 A K s k t).
Proof. exact (SYM (@lem4419478 A K s k t)). Qed.
Lemma lem4419480 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term410 A K s k t) : term410 A K s k t.
Proof. exact (h1). Qed.
Lemma lem4419483 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term409 A K s k t) : term409 A K s k t.
Proof. exact (h1). Qed.
Lemma lem4419484 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : term411 A K s k t.
Proof. exact (fun h0 : term409 A K s k t => @lem4419483 A K s k t h0). Qed.
Lemma lem4419485 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term411 A K s k t) : term411 A K s k t.
Proof. exact (h1). Qed.
Lemma lem4419486 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term409 A K s k t) : term409 A K s k t.
Proof. exact (h1). Qed.
Lemma lem4419487 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term409 A K s k t) (h2 : term411 A K s k t) : term409 A K s k t.
Proof. exact (@lem4419485 A K s k t h2 (@lem4419486 A K s k t h1)). Qed.
Lemma lem4419488 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term409 A K s k t) : term412 A K s k t.
Proof. exact (fun h0 : term411 A K s k t => @lem4419487 A K s k t h1 h0). Qed.
Lemma lem4419489 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term411 A K s k t) : term411 A K s k t.
Proof. exact (h1). Qed.
Lemma lem4419490 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term409 A K s k t) (h2 : term411 A K s k t) : term409 A K s k t.
Proof. exact (@lem4419488 A K s k t h1 (@lem4419489 A K s k t h2)). Qed.
Lemma lem4419491 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term411 A K s k t) : term411 A K s k t.
Proof. exact (fun h0 : term409 A K s k t => @lem4419490 A K s k t h0 h1). Qed.
Lemma lem4419492 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : term413 A K s k t.
Proof. exact (fun h0 : term411 A K s k t => @lem4419491 A K s k t h0). Qed.
Lemma lem4419495 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : term411 A K s k t.
Proof. exact (@lem4419492 A K s k t (@lem4419484 A K s k t)). Qed.
Lemma lem4419496 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : term411 A K s k t.
Proof. exact (@lem4419495 A K s k t). Qed.
Lemma lem4419510 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4419511 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term409 A K s k t) = (term414 A K s k t).
Proof. exact (@lem4419510 (term410 A K s k t)). Qed.
Lemma lem4419513 (t : Prop) : (term60 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4419514 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term414 A K s k t) = (term408 A K s k t).
Proof. exact (@lem4419513 (term408 A K s k t)). Qed.
Lemma lem4419517 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term409 A K s k t) = (term408 A K s k t).
Proof. exact (TRANS (@lem4419511 A K s k t) (@lem4419514 A K s k t)). Qed.
Lemma lem4419552 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term415 A K k t) = (term416 A K k t).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4419517 A K s k t)). Qed.
Lemma lem4419553 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4419554 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term417 A K k t) = (term418 A K k t).
Proof. exact (MK_COMB (@lem4419553 A K) (@lem4419552 A K k t)). Qed.
Lemma lem4419559 {A K : Type'} (t : type1470 A K) : (term419 A K t) = (term420 A K t).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4419554 A K k t)). Qed.
Lemma lem4419560 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4419561 {A K : Type'} (t : type1470 A K) : (term421 A K t) = (term422 A K t).
Proof. exact (MK_COMB (@lem4419560 K) (@lem4419559 A K t)). Qed.
Lemma lem4419566 {A K : Type'} : (term423 A K) = (term424 A K).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4419561 A K t)). Qed.
Lemma lem4419567 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4419576 {A K : Type'} : (term425 A K) = (term426 A K).
Proof. exact (MK_COMB (@lem4419567 A K) (@lem4419566 A K)). Qed.
Lemma lem4419581 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) : (term427 A K k x t i) = (term427 A K k x t i).
Proof. exact (eq_refl (term427 A K k x t i)). Qed.
Lemma lem4419582 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term428 A K k x t) = (term428 A K k x t).
Proof. exact (fun_ext (fun i : K => @lem4419581 A K k x t i)). Qed.
Lemma lem4419583 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4419584 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term429 A K k x t) = (term429 A K k x t).
Proof. exact (MK_COMB (@lem4419583 K) (@lem4419582 A K k x t)). Qed.
Lemma lem4419587 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term430 A K k x) = (term430 A K k x).
Proof. exact (eq_refl (term430 A K k x)). Qed.
Lemma lem4419588 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term379 A K k x t) = (term379 A K k x t).
Proof. exact (MK_COMB (@lem4419587 A K k x) (@lem4419584 A K k x t)). Qed.
Lemma lem4419593 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term427 A K k x s i) = (term427 A K k x s i).
Proof. exact (eq_refl (term427 A K k x s i)). Qed.
Lemma lem4419594 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term428 A K k x s) = (term428 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4419593 A K k x s i)). Qed.
Lemma lem4419595 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4419596 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term429 A K k x s) = (term429 A K k x s).
Proof. exact (MK_COMB (@lem4419595 K) (@lem4419594 A K k x s)). Qed.
Lemma lem4419599 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term430 A K k x) = (term430 A K k x).
Proof. exact (eq_refl (term430 A K k x)). Qed.
Lemma lem4419600 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term379 A K k x s) = (term379 A K k x s).
Proof. exact (MK_COMB (@lem4419599 A K k x) (@lem4419596 A K k x s)). Qed.
Lemma lem4419601 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4419602 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term394 A K k x s) = (term394 A K k x s).
Proof. exact (MK_COMB (@lem4419601) (@lem4419600 A K k x s)). Qed.
Lemma lem4419603 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term396 A K s k x t) = (term396 A K s k x t).
Proof. exact (MK_COMB (@lem4419602 A K k x s) (@lem4419588 A K k x t)). Qed.
Lemma lem4419604 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term398 A K s k t) = (term398 A K s k t).
Proof. exact (fun_ext (fun x : K -> A => @lem4419603 A K s k x t)). Qed.
Lemma lem4419605 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4419606 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term399 A K s k t) = (term399 A K s k t).
Proof. exact (MK_COMB (@lem4419605 A K) (@lem4419604 A K s k t)). Qed.
Lemma lem4419611 {A K : Type'} (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term431 A K s x t i) = (term431 A K s x t i).
Proof. exact (eq_refl (term431 A K s x t i)). Qed.
Lemma lem4419612 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term432 A K s t i) = (term432 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4419611 A K s x t i)). Qed.
Lemma lem4419613 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4419614 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term402 A K s t i) = (term402 A K s t i).
Proof. exact (MK_COMB (@lem4419613 A) (@lem4419612 A K s t i)). Qed.
Lemma lem4419617 {K : Type'} (i : K) (k : K -> Prop) : (term42 K i k) = (term42 K i k).
Proof. exact (eq_refl (term42 K i k)). Qed.
Lemma lem4419618 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term404 A K k s t i) = (term404 A K k s t i).
Proof. exact (MK_COMB (@lem4419617 K i k) (@lem4419614 A K s t i)). Qed.
Lemma lem4419619 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term406 A K k s t) = (term406 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4419618 A K k s t i)). Qed.
Lemma lem4419620 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4419621 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term407 A K k s t) = (term407 A K k s t).
Proof. exact (MK_COMB (@lem4419620 K) (@lem4419619 A K k s t)). Qed.
Lemma lem4419622 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4419623 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term433 A K k s t) = (term433 A K k s t).
Proof. exact (MK_COMB (@lem4419622) (@lem4419621 A K k s t)). Qed.
Lemma lem4419624 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term408 A K s k t) = (term408 A K s k t).
Proof. exact (MK_COMB (@lem4419623 A K k s t) (@lem4419606 A K s k t)). Qed.
Lemma lem4419625 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term416 A K k t) = (term416 A K k t).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4419624 A K s k t)). Qed.
Lemma lem4419626 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4419627 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term418 A K k t) = (term418 A K k t).
Proof. exact (MK_COMB (@lem4419626 A K) (@lem4419625 A K k t)). Qed.
Lemma lem4419628 {A K : Type'} (t : type1470 A K) : (term420 A K t) = (term420 A K t).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4419627 A K k t)). Qed.
Lemma lem4419629 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4419630 {A K : Type'} (t : type1470 A K) : (term422 A K t) = (term422 A K t).
Proof. exact (MK_COMB (@lem4419629 K) (@lem4419628 A K t)). Qed.
Lemma lem4419631 {A K : Type'} : (term424 A K) = (term424 A K).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4419630 A K t)). Qed.
Lemma lem4419632 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4419633 {A K : Type'} : (term426 A K) = (term426 A K).
Proof. exact (MK_COMB (@lem4419632 A K) (@lem4419631 A K)). Qed.
Lemma lem4419700 {A K : Type'} : (term425 A K) = (term426 A K).
Proof. exact (TRANS (@lem4419576 A K) (@lem4419633 A K)). Qed.
Lemma lem4419701 {A K : Type'} : (term426 A K) = (term425 A K).
Proof. exact (SYM (@lem4419700 A K)). Qed.
Lemma lem4419702 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term407 A K k s t) : term407 A K k s t.
Proof. exact (h1). Qed.
Lemma lem4419703 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term379 A K k x s) : term379 A K k x s.
Proof. exact (h1). Qed.
Lemma lem4419705 (p : Prop) : p = (term53 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4419706 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term379 A K k x t) = (term434 A K k x t).
Proof. exact (@lem4419705 (term379 A K k x t)). Qed.
Lemma lem4419707 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term434 A K k x t) = (term379 A K k x t).
Proof. exact (SYM (@lem4419706 A K k x t)). Qed.
Lemma lem4419708 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (h1 : term435 A K k x t) : term435 A K k x t.
Proof. exact (h1). Qed.
Lemma lem4419716 {A K : Type'} (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term431 A K s x t i) = (term436 A K s x t i).
Proof. exact (@lem17265 (term30 A K x s i) (term30 A K x t i)). Qed.
Lemma lem4419717 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term432 A K s t i) = (term437 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4419716 A K s x t i)). Qed.
Lemma lem4419718 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4419719 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term402 A K s t i) = (term438 A K s t i).
Proof. exact (MK_COMB (@lem4419718 A) (@lem4419717 A K s t i)). Qed.
Lemma lem4419721 {K : Type'} (i : K) (k : K -> Prop) : (term439 K i k) = (term439 K i k).
Proof. exact (eq_refl (term439 K i k)). Qed.
Lemma lem4419722 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term440 A K k s t i) = (term441 A K k s t i).
Proof. exact (MK_COMB (@lem4419721 K i k) (@lem4419719 A K s t i)). Qed.
Lemma lem4419723 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term404 A K k s t i) = (term440 A K k s t i).
Proof. exact (@lem17265 (@IN K i k) (term402 A K s t i)). Qed.
Lemma lem4419724 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term404 A K k s t i) = (term441 A K k s t i).
Proof. exact (TRANS (@lem4419723 A K k s t i) (@lem4419722 A K k s t i)). Qed.
Lemma lem4419725 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term406 A K k s t) = (term442 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4419724 A K k s t i)). Qed.
Lemma lem4419726 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4419827 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term407 A K k s t) = (term443 A K k s t).
Proof. exact (MK_COMB (@lem4419726 K) (@lem4419725 A K k s t)). Qed.
Lemma lem4419828 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term407 A K k s t) : term443 A K k s t.
Proof. exact (EQ_MP (@lem4419827 A K k s t) (@lem4419702 A K k s t h1)). Qed.
Lemma lem4419836 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term427 A K k x s i) = (term444 A K k x s i).
Proof. exact (@lem17265 (@IN K i k) (term445 A K x s i)). Qed.
Lemma lem4419837 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term428 A K k x s) = (term446 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4419836 A K k x s i)). Qed.
Lemma lem4419838 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4419839 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term429 A K k x s) = (term447 A K k x s).
Proof. exact (MK_COMB (@lem4419838 K) (@lem4419837 A K k x s)). Qed.
Lemma lem4419841 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term430 A K k x) = (term430 A K k x).
Proof. exact (eq_refl (term430 A K k x)). Qed.
Lemma lem4419894 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term379 A K k x s) = (term448 A K k x s).
Proof. exact (MK_COMB (@lem4419841 A K k x) (@lem4419839 A K k x s)). Qed.
Lemma lem4419895 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term379 A K k x s) : term448 A K k x s.
Proof. exact (EQ_MP (@lem4419894 A K k x s) (@lem4419703 A K k x s h1)). Qed.
Lemma lem4419903 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) : (term449 A K k x t i) = (term450 A K k x t i).
Proof. exact (@lem17362 (@IN K i k) (term445 A K x t i)). Qed.
Lemma lem4419904 {K : Type'} (P : K -> Prop) : (term70 K P) = (term71 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4419905 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term451 A K k x t) = (term452 A K k x t).
Proof. exact (@lem4419904 K (term428 A K k x t)). Qed.
Lemma lem4419906 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) : (term453 A K k x t i) = (term427 A K k x t i).
Proof. exact (eq_refl (term453 A K k x t i)). Qed.
Lemma lem4419907 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4419908 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) : (term454 A K k x t i) = (term449 A K k x t i).
Proof. exact (MK_COMB (@lem4419907) (@lem4419906 A K k x t i)). Qed.
Lemma lem4419909 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) : (term454 A K k x t i) = (term450 A K k x t i).
Proof. exact (TRANS (@lem4419908 A K k x t i) (@lem4419903 A K k x t i)). Qed.
Lemma lem4419910 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term455 A K k x t) = (term456 A K k x t).
Proof. exact (fun_ext (fun i : K => @lem4419909 A K k x t i)). Qed.
Lemma lem4419911 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4419912 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term452 A K k x t) = (term457 A K k x t).
Proof. exact (MK_COMB (@lem4419911 K) (@lem4419910 A K k x t)). Qed.
Lemma lem4419913 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term451 A K k x t) = (term457 A K k x t).
Proof. exact (TRANS (@lem4419905 A K k x t) (@lem4419912 A K k x t)). Qed.
Lemma lem4419915 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term458 A K k x) = (term458 A K k x).
Proof. exact (eq_refl (term458 A K k x)). Qed.
Lemma lem4419916 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term459 A K k x t) = (term460 A K k x t).
Proof. exact (MK_COMB (@lem4419915 A K k x) (@lem4419913 A K k x t)). Qed.
Lemma lem4419917 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term435 A K k x t) = (term459 A K k x t).
Proof. exact (@lem17045 (@EXTENSIONAL K A k x) (term429 A K k x t)). Qed.
Lemma lem4419918 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term435 A K k x t) = (term460 A K k x t).
Proof. exact (TRANS (@lem4419917 A K k x t) (@lem4419916 A K k x t)). Qed.
Lemma lem4419969 {A : Type'} (P : Prop) (Q : A -> Prop) : (term171 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4419970 {K : Type'} (P : Prop) (Q : K -> Prop) : (term171 K P Q) = (term172 K P Q).
Proof. exact (@lem4419969 K P Q). Qed.
Lemma lem4419971 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term461 A K k x t) = (term462 A K k x t).
Proof. exact (@lem4419970 K (term463 A K k x) (term456 A K k x t)). Qed.
Lemma lem4419972 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) : (term464 A K k x t i) = (term450 A K k x t i).
Proof. exact (eq_refl (term464 A K k x t i)). Qed.
Lemma lem4419973 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term465 A K k x t) = (term456 A K k x t).
Proof. exact (fun_ext (fun i : K => @lem4419972 A K k x t i)). Qed.
Lemma lem4419974 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4419975 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term466 A K k x t) = (term457 A K k x t).
Proof. exact (MK_COMB (@lem4419974 K) (@lem4419973 A K k x t)). Qed.
Lemma lem4419976 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term458 A K k x) = (term458 A K k x).
Proof. exact (eq_refl (term458 A K k x)). Qed.
Lemma lem4419977 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term461 A K k x t) = (term460 A K k x t).
Proof. exact (MK_COMB (@lem4419976 A K k x) (@lem4419975 A K k x t)). Qed.
Lemma lem4419978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4419979 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term467 A K k x t) = (term468 A K k x t).
Proof. exact (MK_COMB (@lem4419978) (@lem4419977 A K k x t)). Qed.
Lemma lem4419980 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) : (term464 A K k x t i) = (term450 A K k x t i).
Proof. exact (eq_refl (term464 A K k x t i)). Qed.
Lemma lem4419981 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term458 A K k x) = (term458 A K k x).
Proof. exact (eq_refl (term458 A K k x)). Qed.
Lemma lem4419982 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) : (term469 A K k x t i) = (term470 A K k x t i).
Proof. exact (MK_COMB (@lem4419981 A K k x) (@lem4419980 A K k x t i)). Qed.
Lemma lem4419983 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term471 A K k x t) = (term472 A K k x t).
Proof. exact (fun_ext (fun i : K => @lem4419982 A K k x t i)). Qed.
Lemma lem4419984 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4419985 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term462 A K k x t) = (term473 A K k x t).
Proof. exact (MK_COMB (@lem4419984 K) (@lem4419983 A K k x t)). Qed.
Lemma lem4419986 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : ((term461 A K k x t) = (term462 A K k x t)) = ((term460 A K k x t) = (term473 A K k x t)).
Proof. exact (MK_COMB (@lem4419979 A K k x t) (@lem4419985 A K k x t)). Qed.
Lemma lem4419988 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term460 A K k x t) = (term473 A K k x t).
Proof. exact (EQ_MP (@lem4419986 A K k x t) (@lem4419971 A K k x t)). Qed.
Lemma lem4419989 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term435 A K k x t) = (term473 A K k x t).
Proof. exact (TRANS (@lem4419918 A K k x t) (@lem4419988 A K k x t)). Qed.
Lemma lem4419990 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (h1 : term435 A K k x t) : term473 A K k x t.
Proof. exact (EQ_MP (@lem4419989 A K k x t) (@lem4419708 A K k x t h1)). Qed.
Lemma lem4419991 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term470 A K k x t i) : term470 A K k x t i.
Proof. exact (h1). Qed.
Lemma lem4420010 {A K : Type'} (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term436 A K s x t i) = (term436 A K s x t i).
Proof. exact (eq_refl (term436 A K s x t i)). Qed.
Lemma lem4420011 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term437 A K s t i) = (term437 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4420010 A K s x t i)). Qed.
Lemma lem4420012 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4420013 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term438 A K s t i) = (term438 A K s t i).
Proof. exact (MK_COMB (@lem4420012 A) (@lem4420011 A K s t i)). Qed.
Lemma lem4420022 {K : Type'} (i : K) (k : K -> Prop) : (term439 K i k) = (term439 K i k).
Proof. exact (eq_refl (term439 K i k)). Qed.
Lemma lem4420023 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term441 A K k s t i) = (term441 A K k s t i).
Proof. exact (MK_COMB (@lem4420022 K i k) (@lem4420013 A K s t i)). Qed.
Lemma lem4420024 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term442 A K k s t) = (term442 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4420023 A K k s t i)). Qed.
Lemma lem4420025 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4420026 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term443 A K k s t) = (term443 A K k s t).
Proof. exact (MK_COMB (@lem4420025 K) (@lem4420024 A K k s t)). Qed.
Lemma lem4420027 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term407 A K k s t) : term443 A K k s t.
Proof. exact (EQ_MP (@lem4420026 A K k s t) (@lem4419828 A K k s t h1)). Qed.
Lemma lem4420028 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4420033 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4420034 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4420033 K A f x). Qed.
Lemma lem4420036 {A K : Type'} (x : K -> A) (i : K) : (x i) = (@I (K -> A) x i).
Proof. exact (@lem4420034 A K x i). Qed.
Lemma lem4420039 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4420040 {A K : Type'} (x : K -> A) (i : K) : (term474 A K x i) = (term475 A K x i).
Proof. exact (MK_COMB (@lem4420028 A) (@lem4420036 A K x i)). Qed.
Lemma lem4420041 {A K : Type'} (x : K -> A) (s : type1470 A K) (i : K) : (term445 A K x s i) = (term476 A K x s i).
Proof. exact (MK_COMB (@lem4420040 A K x i) (@lem4420039 A K s i)). Qed.
Lemma lem4420050 {K : Type'} (i : K) (k : K -> Prop) : (term439 K i k) = (term439 K i k).
Proof. exact (eq_refl (term439 K i k)). Qed.
Lemma lem4420051 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term444 A K k x s i) = (term477 A K k x s i).
Proof. exact (MK_COMB (@lem4420050 K i k) (@lem4420041 A K x s i)). Qed.
Lemma lem4420052 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term446 A K k x s) = (term478 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4420051 A K k x s i)). Qed.
Lemma lem4420053 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4420054 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term447 A K k x s) = (term479 A K k x s).
Proof. exact (MK_COMB (@lem4420053 K) (@lem4420052 A K k x s)). Qed.
Lemma lem4420061 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term430 A K k x) = (term430 A K k x).
Proof. exact (eq_refl (term430 A K k x)). Qed.
Lemma lem4420062 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term448 A K k x s) = (term480 A K k x s).
Proof. exact (MK_COMB (@lem4420061 A K k x) (@lem4420054 A K k x s)). Qed.
Lemma lem4420063 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term379 A K k x s) : term480 A K k x s.
Proof. exact (EQ_MP (@lem4420062 A K k x s) (@lem4419895 A K k x s h1)). Qed.
Lemma lem4420064 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4420065 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4420070 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4420071 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4420070 K A f x). Qed.
Lemma lem4420073 {A K : Type'} (x : K -> A) (i : K) : (x i) = (@I (K -> A) x i).
Proof. exact (@lem4420071 A K x i). Qed.
Lemma lem4420076 {A K : Type'} (t : type1470 A K) (i : K) : (t i) = (t i).
Proof. exact (eq_refl (t i)). Qed.
Lemma lem4420077 {A K : Type'} (x : K -> A) (i : K) : (term474 A K x i) = (term475 A K x i).
Proof. exact (MK_COMB (@lem4420065 A) (@lem4420073 A K x i)). Qed.
Lemma lem4420078 {A K : Type'} (x : K -> A) (t : type1470 A K) (i : K) : (term445 A K x t i) = (term476 A K x t i).
Proof. exact (MK_COMB (@lem4420077 A K x i) (@lem4420076 A K t i)). Qed.
Lemma lem4420079 {A K : Type'} (x : K -> A) (t : type1470 A K) (i : K) : (term481 A K x t i) = (term482 A K x t i).
Proof. exact (MK_COMB (@lem4420064) (@lem4420078 A K x t i)). Qed.
Lemma lem4420086 {K : Type'} (i : K) (k : K -> Prop) : (term17 K i k) = (term17 K i k).
Proof. exact (eq_refl (term17 K i k)). Qed.
Lemma lem4420087 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) : (term450 A K k x t i) = (term483 A K k x t i).
Proof. exact (MK_COMB (@lem4420086 K i k) (@lem4420079 A K x t i)). Qed.
Lemma lem4420096 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term458 A K k x) = (term458 A K k x).
Proof. exact (eq_refl (term458 A K k x)). Qed.
Lemma lem4420097 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) : (term470 A K k x t i) = (term484 A K k x t i).
Proof. exact (MK_COMB (@lem4420096 A K k x) (@lem4420087 A K k x t i)). Qed.
Lemma lem4420098 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term470 A K k x t i) : term484 A K k x t i.
Proof. exact (EQ_MP (@lem4420097 A K k x t i) (@lem4419991 A K k x t i h1)). Qed.
Lemma lem4420099 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term379 A K k x s) : term479 A K k x s.
Proof. exact (proj2 (@lem4420063 A K k x s h1)). Qed.
Lemma lem4420102 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term483 A K k x t i) : term483 A K k x t i.
Proof. exact (h1). Qed.
Lemma lem4420169 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term463 A K k x) : term463 A K k x.
Proof. exact (h1). Qed.
Lemma lem4420171 {A : Type'} (P : Prop) (Q : A -> Prop) : (term485 A P Q) = (term486 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4420172 {A : Type'} (P : Prop) (Q : A -> Prop) : (term485 A P Q) = (term486 A P Q).
Proof. exact (@lem4420171 A P Q). Qed.
Lemma lem4420173 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term487 A K k s t i) = (term488 A K k s t i).
Proof. exact (@lem4420172 A (term489 K i k) (term437 A K s t i)). Qed.
Lemma lem4420174 {A K : Type'} (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term490 A K s t i x) = (term436 A K s x t i).
Proof. exact (eq_refl (term490 A K s t i x)). Qed.
Lemma lem4420175 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term491 A K s t i) = (term437 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4420174 A K s x t i)). Qed.
Lemma lem4420176 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4420177 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term492 A K s t i) = (term438 A K s t i).
Proof. exact (MK_COMB (@lem4420176 A) (@lem4420175 A K s t i)). Qed.
Lemma lem4420178 {K : Type'} (i : K) (k : K -> Prop) : (term439 K i k) = (term439 K i k).
Proof. exact (eq_refl (term439 K i k)). Qed.
Lemma lem4420179 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term487 A K k s t i) = (term441 A K k s t i).
Proof. exact (MK_COMB (@lem4420178 K i k) (@lem4420177 A K s t i)). Qed.
Lemma lem4420180 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4420181 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term493 A K k s t i) = (term494 A K k s t i).
Proof. exact (MK_COMB (@lem4420180) (@lem4420179 A K k s t i)). Qed.
Lemma lem4420182 {A K : Type'} (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term490 A K s t i x) = (term436 A K s x t i).
Proof. exact (eq_refl (term490 A K s t i x)). Qed.
Lemma lem4420183 {K : Type'} (i : K) (k : K -> Prop) : (term439 K i k) = (term439 K i k).
Proof. exact (eq_refl (term439 K i k)). Qed.
Lemma lem4420184 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term495 A K k s t i x) = (term496 A K k s x t i).
Proof. exact (MK_COMB (@lem4420183 K i k) (@lem4420182 A K s x t i)). Qed.
Lemma lem4420185 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term497 A K k s t i) = (term498 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4420184 A K k s x t i)). Qed.
Lemma lem4420186 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4420187 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term488 A K k s t i) = (term499 A K k s t i).
Proof. exact (MK_COMB (@lem4420186 A) (@lem4420185 A K k s t i)). Qed.
Lemma lem4420188 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : ((term487 A K k s t i) = (term488 A K k s t i)) = ((term441 A K k s t i) = (term499 A K k s t i)).
Proof. exact (MK_COMB (@lem4420181 A K k s t i) (@lem4420187 A K k s t i)). Qed.
Lemma lem4420189 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term441 A K k s t i) = (term499 A K k s t i).
Proof. exact (EQ_MP (@lem4420188 A K k s t i) (@lem4420173 A K k s t i)). Qed.
Lemma lem4420190 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term442 A K k s t) = (term500 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4420189 A K k s t i)). Qed.
Lemma lem4420191 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4420192 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term443 A K k s t) = (term501 A K k s t).
Proof. exact (MK_COMB (@lem4420191 K) (@lem4420190 A K k s t)). Qed.
Lemma lem4420205 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term496 A K k s x t i) = (term496 A K k s x t i).
Proof. exact (eq_refl (term496 A K k s x t i)). Qed.
Lemma lem4420206 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term498 A K k s t i) = (term498 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4420205 A K k s x t i)). Qed.
Lemma lem4420207 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4420208 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term499 A K k s t i) = (term499 A K k s t i).
Proof. exact (MK_COMB (@lem4420207 A) (@lem4420206 A K k s t i)). Qed.
Lemma lem4420209 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term500 A K k s t) = (term500 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4420208 A K k s t i)). Qed.
Lemma lem4420210 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4420211 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term501 A K k s t) = (term501 A K k s t).
Proof. exact (MK_COMB (@lem4420210 K) (@lem4420209 A K k s t)). Qed.
Lemma lem4420212 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term443 A K k s t) = (term501 A K k s t).
Proof. exact (TRANS (@lem4420192 A K k s t) (@lem4420211 A K k s t)). Qed.
Lemma lem4420213 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term407 A K k s t) : term501 A K k s t.
Proof. exact (EQ_MP (@lem4420212 A K k s t) (@lem4420027 A K k s t h1)). Qed.
Lemma lem4420225 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term477 A K k x s i) = (term477 A K k x s i).
Proof. exact (eq_refl (term477 A K k x s i)). Qed.
Lemma lem4420226 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term478 A K k x s) = (term478 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4420225 A K k x s i)). Qed.
Lemma lem4420227 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4420229 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term479 A K k x s) = (term479 A K k x s).
Proof. exact (MK_COMB (@lem4420227 K) (@lem4420226 A K k x s)). Qed.
Lemma lem4420230 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term379 A K k x s) : term479 A K k x s.
Proof. exact (EQ_MP (@lem4420229 A K k x s) (@lem4420099 A K k x s h1)). Qed.
Lemma lem4420248 {A K : Type'} (_50923 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term407 A K k s t) : term502 A K k s t _50923.
Proof. exact (@lem4420213 A K k s t h1 _50923). Qed.
Lemma lem4420249 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_50923 : K) : (term502 A K k s t _50923) = (term499 A K k s t _50923).
Proof. exact (eq_refl (term502 A K k s t _50923)). Qed.
Lemma lem4420250 {A K : Type'} (_50923 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term407 A K k s t) : term499 A K k s t _50923.
Proof. exact (EQ_MP (@lem4420249 A K k s t _50923) (@lem4420248 A K _50923 k s t h1)). Qed.
Lemma lem4420251 {A K : Type'} (_50923 : K) (_50924 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term407 A K k s t) : term503 A K k s t _50923 _50924.
Proof. exact (@lem4420250 A K _50923 k s t h1 _50924). Qed.
Lemma lem4420252 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_50924 : A) (t : type1470 A K) (_50923 : K) : (term503 A K k s t _50923 _50924) = (term496 A K k s _50924 t _50923).
Proof. exact (eq_refl (term503 A K k s t _50923 _50924)). Qed.
Lemma lem4420254 {A K : Type'} (_50925 : K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term379 A K k x s) : term504 A K k x s _50925.
Proof. exact (@lem4420230 A K k x s h1 _50925). Qed.
Lemma lem4420255 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (_50925 : K) : (term504 A K k x s _50925) = (term477 A K k x s _50925).
Proof. exact (eq_refl (term504 A K k x s _50925)). Qed.
Lemma lem4420276 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term463 A K k x) : term463 A K k x.
Proof. exact (h1). Qed.
Lemma lem4420286 {A K : Type'} (_50924 : A) (_50923 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term407 A K k s t) : term496 A K k s _50924 t _50923.
Proof. exact (EQ_MP (@lem4420252 A K k s _50924 t _50923) (@lem4420251 A K _50923 _50924 k s t h1)). Qed.
Lemma lem4420294 {A K : Type'} (_50925 : K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term379 A K k x s) : term477 A K k x s _50925.
Proof. exact (EQ_MP (@lem4420255 A K k x s _50925) (@lem4420254 A K _50925 k x s h1)). Qed.
Lemma lem4420298 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term483 A K k x t i) : term482 A K x t i.
Proof. exact (proj2 (@lem4420102 A K k x t i h1)). Qed.
Lemma lem4420300 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term379 A K k x s) : @EXTENSIONAL K A k x.
Proof. exact (proj1 (@lem4420063 A K k x s h1)). Qed.
Lemma lem4420301 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term379 A K k x s) : term505 A K k x.
Proof. exact (fun h0 : term463 A K k x => @lem4420300 A K k x s h1). Qed.
Lemma lem4420303 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4420304 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term505 A K k x) = (@EXTENSIONAL K A k x).
Proof. exact (@lem4420303 (@EXTENSIONAL K A k x)). Qed.
Lemma lem4420305 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term379 A K k x s) : @EXTENSIONAL K A k x.
Proof. exact (EQ_MP (@lem4420304 A K k x) (@lem4420301 A K k x s h1)). Qed.
Lemma lem4420308 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4420310 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term463 A K k x) = (term506 A K k x).
Proof. exact (@lem4420308 (@EXTENSIONAL K A k x)). Qed.
Lemma lem4420313 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term463 A K k x) : term506 A K k x.
Proof. exact (EQ_MP (@lem4420310 A K k x) (@lem4420276 A K k x h1)). Qed.
Lemma lem4420316 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term463 A K k x) (h2 : term379 A K k x s) : False.
Proof. exact (@lem4420313 A K k x h1 (@lem4420305 A K k x s h2)). Qed.
Lemma lem4420317 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term463 A K k x) (h2 : term379 A K k x s) : term337.
Proof. exact (fun h0 : ~ False => @lem4420316 A K k x s h1 h2). Qed.
Lemma lem4420319 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4420320 : term337 = False.
Proof. exact (@lem4420319 False). Qed.
Lemma lem4420321 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term463 A K k x) (h2 : term379 A K k x s) : False.
Proof. exact (EQ_MP (@lem4420320) (@lem4420317 A K k x s h1 h2)). Qed.
Lemma lem4420323 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term483 A K k x t i) : @IN K i k.
Proof. exact (proj1 (@lem4420102 A K k x t i h1)). Qed.
Lemma lem4420324 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term483 A K k x t i) : term507 K i k.
Proof. exact (fun h0 : term489 K i k => @lem4420323 A K k x t i h1). Qed.
Lemma lem4420326 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4420327 {K : Type'} (i : K) (k : K -> Prop) : (term507 K i k) = (@IN K i k).
Proof. exact (@lem4420326 (@IN K i k)). Qed.
Lemma lem4420328 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term483 A K k x t i) : @IN K i k.
Proof. exact (EQ_MP (@lem4420327 K i k) (@lem4420324 A K k x t i h1)). Qed.
Lemma lem4420330 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term483 A K k x t i) : @IN K i k.
Proof. exact (proj1 (@lem4420102 A K k x t i h1)). Qed.
Lemma lem4420331 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term483 A K k x t i) : term507 K i k.
Proof. exact (fun h0 : term489 K i k => @lem4420330 A K k x t i h1). Qed.
Lemma lem4420333 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4420334 {K : Type'} (i : K) (k : K -> Prop) : (term507 K i k) = (@IN K i k).
Proof. exact (@lem4420333 (@IN K i k)). Qed.
Lemma lem4420335 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term483 A K k x t i) : @IN K i k.
Proof. exact (EQ_MP (@lem4420334 K i k) (@lem4420331 A K k x t i h1)). Qed.
Lemma lem4420341 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4420342 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50925 : K) (k : K -> Prop) : (term477 A K k x s _50925) = (term508 A K x s _50925 k).
Proof. exact (@lem4420341 (term476 A K x s _50925) (term489 K _50925 k)). Qed.
Lemma lem4420348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4420349 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50925 : K) (k : K -> Prop) : (term509 A K k x s _50925) = (term510 A K x s _50925 k).
Proof. exact (MK_COMB (@lem4420348) (@lem4420342 A K x s _50925 k)). Qed.
Lemma lem4420355 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50925 : K) (k : K -> Prop) : (term508 A K x s _50925 k) = (term508 A K x s _50925 k).
Proof. exact (eq_refl (term508 A K x s _50925 k)). Qed.
Lemma lem4420356 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50925 : K) (k : K -> Prop) : ((term477 A K k x s _50925) = (term508 A K x s _50925 k)) = ((term508 A K x s _50925 k) = (term508 A K x s _50925 k)).
Proof. exact (MK_COMB (@lem4420349 A K x s _50925 k) (@lem4420355 A K x s _50925 k)). Qed.
Lemma lem4420358 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4420359 (x : Prop) : (x = x) = True.
Proof. exact (@lem4420358 Prop x). Qed.
Lemma lem4420360 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50925 : K) (k : K -> Prop) : ((term508 A K x s _50925 k) = (term508 A K x s _50925 k)) = True.
Proof. exact (@lem4420359 (term508 A K x s _50925 k)). Qed.
Lemma lem4420361 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50925 : K) (k : K -> Prop) : ((term477 A K k x s _50925) = (term508 A K x s _50925 k)) = True.
Proof. exact (TRANS (@lem4420356 A K x s _50925 k) (@lem4420360 A K x s _50925 k)). Qed.
Lemma lem4420362 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50925 : K) (k : K -> Prop) : True = ((term477 A K k x s _50925) = (term508 A K x s _50925 k)).
Proof. exact (SYM (@lem4420361 A K x s _50925 k)). Qed.
Lemma lem4420363 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50925 : K) (k : K -> Prop) : (term477 A K k x s _50925) = (term508 A K x s _50925 k).
Proof. exact (EQ_MP (@lem4420362 A K x s _50925 k) (@lem0)). Qed.
Lemma lem4420364 {A K : Type'} (_50925 : K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term379 A K k x s) : term508 A K x s _50925 k.
Proof. exact (EQ_MP (@lem4420363 A K x s _50925 k) (@lem4420294 A K _50925 k x s h1)). Qed.
Lemma lem4420366 (b : Prop) (a : Prop) : (a \/ b) = (term328 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4420367 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (_50925 : K) : (term508 A K x s _50925 k) = (term511 A K k x s _50925).
Proof. exact (@lem4420366 (term489 K _50925 k) (term476 A K x s _50925)). Qed.
Lemma lem4420369 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4420370 {K : Type'} (_50925 : K) (k : K -> Prop) : (term512 K _50925 k) = (@IN K _50925 k).
Proof. exact (@lem4420369 (@IN K _50925 k)). Qed.
Lemma lem4420371 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4420372 {K : Type'} (_50925 : K) (k : K -> Prop) : (term513 K _50925 k) = (term42 K _50925 k).
Proof. exact (MK_COMB (@lem4420371) (@lem4420370 K _50925 k)). Qed.
Lemma lem4420373 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50925 : K) : (term476 A K x s _50925) = (term476 A K x s _50925).
Proof. exact (eq_refl (term476 A K x s _50925)). Qed.
Lemma lem4420374 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (_50925 : K) : (term511 A K k x s _50925) = (term514 A K k x s _50925).
Proof. exact (MK_COMB (@lem4420372 K _50925 k) (@lem4420373 A K x s _50925)). Qed.
Lemma lem4420375 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (_50925 : K) : (term508 A K x s _50925 k) = (term514 A K k x s _50925).
Proof. exact (TRANS (@lem4420367 A K k x s _50925) (@lem4420374 A K k x s _50925)). Qed.
Lemma lem4420378 {A K : Type'} (_50925 : K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term379 A K k x s) : term514 A K k x s _50925.
Proof. exact (EQ_MP (@lem4420375 A K k x s _50925) (@lem4420364 A K _50925 k x s h1)). Qed.
Lemma lem4420379 {A K : Type'} (_50925 : K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term379 A K k x s) : term514 A K k x s _50925.
Proof. exact (@lem4420378 A K _50925 k x s h1). Qed.
Lemma lem4420380 {A K : Type'} (i : K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term379 A K k x s) : term514 A K k x s i.
Proof. exact (@lem4420379 A K i k x s h1). Qed.
Lemma lem4420383 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term379 A K k x s) (h2 : term483 A K k x t i) : term476 A K x s i.
Proof. exact (@lem4420380 A K i k x s h1 (@lem4420335 A K k x t i h2)). Qed.
Lemma lem4420384 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term379 A K k x s) (h2 : term483 A K k x t i) : term515 A K x s i.
Proof. exact (fun h0 : term482 A K x s i => @lem4420383 A K s k x t i h1 h2). Qed.
Lemma lem4420386 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4420387 {A K : Type'} (x : K -> A) (s : type1470 A K) (i : K) : (term515 A K x s i) = (term476 A K x s i).
Proof. exact (@lem4420386 (term476 A K x s i)). Qed.
Lemma lem4420388 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term379 A K k x s) (h2 : term483 A K k x t i) : term476 A K x s i.
Proof. exact (EQ_MP (@lem4420387 A K x s i) (@lem4420384 A K s k x t i h1 h2)). Qed.
Lemma lem4420394 (q : Prop) (p : Prop) (r : Prop) : (term516 p q r) = (term516 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4420395 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (_50924 : A) (t : type1470 A K) (_50923 : K) : (term496 A K k s _50924 t _50923) = (term517 A K s k _50924 t _50923).
Proof. exact (@lem4420394 (term518 A K _50924 s _50923) (term489 K _50923 k) (term30 A K _50924 t _50923)). Qed.
Lemma lem4420409 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4420410 {A K : Type'} (_50924 : A) (t : type1470 A K) (_50923 : K) (k : K -> Prop) : (term519 A K k _50924 t _50923) = (term520 A K _50924 t _50923 k).
Proof. exact (@lem4420409 (term30 A K _50924 t _50923) (term489 K _50923 k)). Qed.
Lemma lem4420416 {A K : Type'} (_50924 : A) (s : type1470 A K) (_50923 : K) : (term521 A K _50924 s _50923) = (term521 A K _50924 s _50923).
Proof. exact (eq_refl (term521 A K _50924 s _50923)). Qed.
Lemma lem4420417 {A K : Type'} (s : type1470 A K) (_50924 : A) (t : type1470 A K) (_50923 : K) (k : K -> Prop) : (term517 A K s k _50924 t _50923) = (term522 A K s _50924 t _50923 k).
Proof. exact (MK_COMB (@lem4420416 A K _50924 s _50923) (@lem4420410 A K _50924 t _50923 k)). Qed.
Lemma lem4420421 (q : Prop) (p : Prop) (r : Prop) : (term516 p q r) = (term516 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4420422 {A K : Type'} (t : type1470 A K) (_50924 : A) (s : type1470 A K) (_50923 : K) (k : K -> Prop) : (term522 A K s _50924 t _50923 k) = (term523 A K t _50924 s _50923 k).
Proof. exact (@lem4420421 (term30 A K _50924 t _50923) (term518 A K _50924 s _50923) (term489 K _50923 k)). Qed.
Lemma lem4420438 {A K : Type'} (t : type1470 A K) (_50924 : A) (s : type1470 A K) (_50923 : K) (k : K -> Prop) : (term517 A K s k _50924 t _50923) = (term523 A K t _50924 s _50923 k).
Proof. exact (TRANS (@lem4420417 A K s _50924 t _50923 k) (@lem4420422 A K t _50924 s _50923 k)). Qed.
Lemma lem4420439 {A K : Type'} (t : type1470 A K) (_50924 : A) (s : type1470 A K) (_50923 : K) (k : K -> Prop) : (term496 A K k s _50924 t _50923) = (term523 A K t _50924 s _50923 k).
Proof. exact (TRANS (@lem4420395 A K s k _50924 t _50923) (@lem4420438 A K t _50924 s _50923 k)). Qed.
Lemma lem4420440 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4420441 {A K : Type'} (t : type1470 A K) (_50924 : A) (s : type1470 A K) (_50923 : K) (k : K -> Prop) : (term524 A K k s _50924 t _50923) = (term525 A K t _50924 s _50923 k).
Proof. exact (MK_COMB (@lem4420440) (@lem4420439 A K t _50924 s _50923 k)). Qed.
Lemma lem4420455 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4420456 {A K : Type'} (_50924 : A) (s : type1470 A K) (_50923 : K) (k : K -> Prop) : (term526 A K k _50924 s _50923) = (term527 A K _50924 s _50923 k).
Proof. exact (@lem4420455 (term518 A K _50924 s _50923) (term489 K _50923 k)). Qed.
Lemma lem4420462 {A K : Type'} (_50924 : A) (t : type1470 A K) (_50923 : K) : (term528 A K _50924 t _50923) = (term528 A K _50924 t _50923).
Proof. exact (eq_refl (term528 A K _50924 t _50923)). Qed.
Lemma lem4420463 {A K : Type'} (t : type1470 A K) (_50924 : A) (s : type1470 A K) (_50923 : K) (k : K -> Prop) : (term529 A K t k _50924 s _50923) = (term523 A K t _50924 s _50923 k).
Proof. exact (MK_COMB (@lem4420462 A K _50924 t _50923) (@lem4420456 A K _50924 s _50923 k)). Qed.
Lemma lem4420474 {A K : Type'} (t : type1470 A K) (_50924 : A) (s : type1470 A K) (_50923 : K) (k : K -> Prop) : ((term496 A K k s _50924 t _50923) = (term529 A K t k _50924 s _50923)) = ((term523 A K t _50924 s _50923 k) = (term523 A K t _50924 s _50923 k)).
Proof. exact (MK_COMB (@lem4420441 A K t _50924 s _50923 k) (@lem4420463 A K t _50924 s _50923 k)). Qed.
Lemma lem4420476 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4420477 (x : Prop) : (x = x) = True.
Proof. exact (@lem4420476 Prop x). Qed.
Lemma lem4420478 {A K : Type'} (t : type1470 A K) (_50924 : A) (s : type1470 A K) (_50923 : K) (k : K -> Prop) : ((term523 A K t _50924 s _50923 k) = (term523 A K t _50924 s _50923 k)) = True.
Proof. exact (@lem4420477 (term523 A K t _50924 s _50923 k)). Qed.
Lemma lem4420479 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (_50924 : A) (s : type1470 A K) (_50923 : K) : ((term496 A K k s _50924 t _50923) = (term529 A K t k _50924 s _50923)) = True.
Proof. exact (TRANS (@lem4420474 A K t _50924 s _50923 k) (@lem4420478 A K t _50924 s _50923 k)). Qed.
Lemma lem4420480 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (_50924 : A) (s : type1470 A K) (_50923 : K) : True = ((term496 A K k s _50924 t _50923) = (term529 A K t k _50924 s _50923)).
Proof. exact (SYM (@lem4420479 A K t k _50924 s _50923)). Qed.
Lemma lem4420481 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (_50924 : A) (s : type1470 A K) (_50923 : K) : (term496 A K k s _50924 t _50923) = (term529 A K t k _50924 s _50923).
Proof. exact (EQ_MP (@lem4420480 A K t k _50924 s _50923) (@lem0)). Qed.
Lemma lem4420482 {A K : Type'} (_50924 : A) (_50923 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term407 A K k s t) : term529 A K t k _50924 s _50923.
Proof. exact (EQ_MP (@lem4420481 A K t k _50924 s _50923) (@lem4420286 A K _50924 _50923 k s t h1)). Qed.
Lemma lem4420484 (b : Prop) (a : Prop) : (a \/ b) = (term328 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4420485 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_50924 : A) (t : type1470 A K) (_50923 : K) : (term529 A K t k _50924 s _50923) = (term530 A K k s _50924 t _50923).
Proof. exact (@lem4420484 (term526 A K k _50924 s _50923) (term30 A K _50924 t _50923)). Qed.
Lemma lem4420487 (a : Prop) (b : Prop) : (term531 a b) = (term532 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4420488 {A K : Type'} (k : K -> Prop) (_50924 : A) (s : type1470 A K) (_50923 : K) : (term533 A K k _50924 s _50923) = (term534 A K k _50924 s _50923).
Proof. exact (@lem4420487 (term489 K _50923 k) (term518 A K _50924 s _50923)). Qed.
Lemma lem4420490 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4420491 {K : Type'} (_50923 : K) (k : K -> Prop) : (term512 K _50923 k) = (@IN K _50923 k).
Proof. exact (@lem4420490 (@IN K _50923 k)). Qed.
Lemma lem4420492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4420493 {K : Type'} (_50923 : K) (k : K -> Prop) : (term535 K _50923 k) = (term17 K _50923 k).
Proof. exact (MK_COMB (@lem4420492) (@lem4420491 K _50923 k)). Qed.
Lemma lem4420495 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4420496 {A K : Type'} (_50924 : A) (s : type1470 A K) (_50923 : K) : (term536 A K _50924 s _50923) = (term30 A K _50924 s _50923).
Proof. exact (@lem4420495 (term30 A K _50924 s _50923)). Qed.
Lemma lem4420497 {A K : Type'} (k : K -> Prop) (_50924 : A) (s : type1470 A K) (_50923 : K) : (term534 A K k _50924 s _50923) = (term537 A K k _50924 s _50923).
Proof. exact (MK_COMB (@lem4420493 K _50923 k) (@lem4420496 A K _50924 s _50923)). Qed.
Lemma lem4420498 {A K : Type'} (k : K -> Prop) (_50924 : A) (s : type1470 A K) (_50923 : K) : (term533 A K k _50924 s _50923) = (term537 A K k _50924 s _50923).
Proof. exact (TRANS (@lem4420488 A K k _50924 s _50923) (@lem4420497 A K k _50924 s _50923)). Qed.
Lemma lem4420499 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4420500 {A K : Type'} (k : K -> Prop) (_50924 : A) (s : type1470 A K) (_50923 : K) : (term538 A K k _50924 s _50923) = (term539 A K k _50924 s _50923).
Proof. exact (MK_COMB (@lem4420499) (@lem4420498 A K k _50924 s _50923)). Qed.
Lemma lem4420501 {A K : Type'} (_50924 : A) (t : type1470 A K) (_50923 : K) : (term30 A K _50924 t _50923) = (term30 A K _50924 t _50923).
Proof. exact (eq_refl (term30 A K _50924 t _50923)). Qed.
Lemma lem4420502 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_50924 : A) (t : type1470 A K) (_50923 : K) : (term530 A K k s _50924 t _50923) = (term540 A K k s _50924 t _50923).
Proof. exact (MK_COMB (@lem4420500 A K k _50924 s _50923) (@lem4420501 A K _50924 t _50923)). Qed.
Lemma lem4420503 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_50924 : A) (t : type1470 A K) (_50923 : K) : (term529 A K t k _50924 s _50923) = (term540 A K k s _50924 t _50923).
Proof. exact (TRANS (@lem4420485 A K k s _50924 t _50923) (@lem4420502 A K k s _50924 t _50923)). Qed.
Lemma lem4420505 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term379 A K k x s) (h2 : term483 A K k x t i) : term541 A K k x s i.
Proof. exact (conj (@lem4420328 A K k x t i h2) (@lem4420388 A K s k x t i h1 h2)). Qed.
Lemma lem4420507 {A K : Type'} (_50924 : A) (_50923 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term407 A K k s t) : term540 A K k s _50924 t _50923.
Proof. exact (EQ_MP (@lem4420503 A K k s _50924 t _50923) (@lem4420482 A K _50924 _50923 k s t h1)). Qed.
Lemma lem4420508 {A K : Type'} (_50924 : A) (_50923 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term407 A K k s t) : term540 A K k s _50924 t _50923.
Proof. exact (@lem4420507 A K _50924 _50923 k s t h1). Qed.
Lemma lem4420509 {A K : Type'} (x : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term407 A K k s t) : term542 A K k s x t i.
Proof. exact (@lem4420508 A K (@I (K -> A) x i) i k s t h1). Qed.
Lemma lem4420512 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term407 A K k s t) (h2 : term379 A K k x s) (h3 : term483 A K k x t i) : term476 A K x t i.
Proof. exact (@lem4420509 A K x i k s t h1 (@lem4420505 A K s k x t i h2 h3)). Qed.
Lemma lem4420513 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term407 A K k s t) (h2 : term379 A K k x s) (h3 : term483 A K k x t i) : term515 A K x t i.
Proof. exact (fun h0 : term482 A K x t i => @lem4420512 A K s k x t i h1 h2 h3). Qed.
Lemma lem4420515 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4420516 {A K : Type'} (x : K -> A) (t : type1470 A K) (i : K) : (term515 A K x t i) = (term476 A K x t i).
Proof. exact (@lem4420515 (term476 A K x t i)). Qed.
Lemma lem4420517 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term407 A K k s t) (h2 : term379 A K k x s) (h3 : term483 A K k x t i) : term476 A K x t i.
Proof. exact (EQ_MP (@lem4420516 A K x t i) (@lem4420513 A K s k x t i h1 h2 h3)). Qed.
Lemma lem4420520 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4420522 {A K : Type'} (x : K -> A) (t : type1470 A K) (i : K) : (term482 A K x t i) = (term543 A K x t i).
Proof. exact (@lem4420520 (term476 A K x t i)). Qed.
Lemma lem4420525 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term483 A K k x t i) : term543 A K x t i.
Proof. exact (EQ_MP (@lem4420522 A K x t i) (@lem4420298 A K k x t i h1)). Qed.
Lemma lem4420528 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term407 A K k s t) (h2 : term379 A K k x s) (h3 : term483 A K k x t i) : False.
Proof. exact (@lem4420525 A K k x t i h3 (@lem4420517 A K s k x t i h1 h2 h3)). Qed.
Lemma lem4420529 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term407 A K k s t) (h2 : term379 A K k x s) (h3 : term483 A K k x t i) : term337.
Proof. exact (fun h0 : ~ False => @lem4420528 A K s k x t i h1 h2 h3). Qed.
Lemma lem4420531 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4420532 : term337 = False.
Proof. exact (@lem4420531 False). Qed.
Lemma lem4420533 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term407 A K k s t) (h2 : term379 A K k x s) (h3 : term483 A K k x t i) : False.
Proof. exact (EQ_MP (@lem4420532) (@lem4420529 A K s k x t i h1 h2 h3)). Qed.
Lemma lem4420534 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term463 A K k x) (h2 : term379 A K k x s) : (term463 A K k x) = False.
Proof. exact (prop_ext (fun h3 : term463 A K k x => @lem4420321 A K k x s h1 h2) (fun h3 : False => @lem4420276 A K k x h1)). Qed.
Lemma lem4420535 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term463 A K k x) (h2 : term379 A K k x s) : False.
Proof. exact (EQ_MP (@lem4420534 A K k x s h1 h2) (@lem4420276 A K k x h1)). Qed.
Lemma lem4420536 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term463 A K k x) (h2 : term379 A K k x s) : (term463 A K k x) = False.
Proof. exact (prop_ext (fun h3 : term463 A K k x => @lem4420535 A K k x s h1 h2) (fun h3 : False => @lem4420169 A K k x h1)). Qed.
Lemma lem4420537 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term463 A K k x) (h2 : term379 A K k x s) : False.
Proof. exact (EQ_MP (@lem4420536 A K k x s h1 h2) (@lem4420169 A K k x h1)). Qed.
Lemma lem4420538 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term463 A K k x) (h2 : term379 A K k x s) : (term463 A K k x) = False.
Proof. exact (prop_ext (fun h3 : term463 A K k x => @lem4420537 A K k x s h1 h2) (fun h3 : False => @lem4420169 A K k x h1)). Qed.
Lemma lem4420539 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term463 A K k x) (h2 : term379 A K k x s) : False.
Proof. exact (EQ_MP (@lem4420538 A K k x s h1 h2) (@lem4420169 A K k x h1)). Qed.
Lemma lem4420540 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) (i : K) (h1 : term407 A K k s t) (h2 : term379 A K k x s) (h3 : term470 A K k x t i) : False.
Proof. exact (or_elim (@lem4420098 A K k x t i h3) (fun h0 : term463 A K k x => @lem4420539 A K k x s h0 h2) (fun h0 : term483 A K k x t i => @lem4420533 A K s k x t i h1 h2 h0)). Qed.
Lemma lem4420541 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term407 A K k s t) (h2 : term435 A K k x t) (h3 : term379 A K k x s) : False.
Proof. exact (ex_elim (@lem4419990 A K k x t h2) (fun i : K => fun h0 : term472 A K k x t i => @lem4420540 A K s k x t i h1 h3 h0)). Qed.
Lemma lem4420542 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term407 A K k s t) (h2 : term435 A K k x t) (h3 : term379 A K k x s) : (term435 A K k x t) = False.
Proof. exact (prop_ext (fun h4 : term435 A K k x t => @lem4420541 A K t k x s h1 h2 h3) (fun h4 : False => @lem4419708 A K k x t h2)). Qed.
Lemma lem4420543 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term407 A K k s t) (h2 : term435 A K k x t) (h3 : term379 A K k x s) : False.
Proof. exact (EQ_MP (@lem4420542 A K t k x s h1 h2 h3) (@lem4419708 A K k x t h2)). Qed.
Lemma lem4420544 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term407 A K k s t) (h2 : term379 A K k x s) : term434 A K k x t.
Proof. exact (fun h0 : term435 A K k x t => @lem4420543 A K t k x s h1 h0 h2). Qed.
Lemma lem4420545 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term407 A K k s t) (h2 : term379 A K k x s) : term379 A K k x t.
Proof. exact (EQ_MP (@lem4419707 A K k x t) (@lem4420544 A K t k x s h1 h2)). Qed.
Lemma lem4420546 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term407 A K k s t) : term396 A K s k x t.
Proof. exact (fun h0 : term379 A K k x s => @lem4420545 A K t k x s h1 h0). Qed.
Lemma lem4420551 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term407 A K k s t) : term399 A K s k t.
Proof. exact (fun x : K -> A => @lem4420546 A K x k s t h1). Qed.
Lemma lem4420552 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : term408 A K s k t.
Proof. exact (fun h0 : term407 A K k s t => @lem4420551 A K k s t h0). Qed.
Lemma lem4420557 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : term418 A K k t.
Proof. exact (fun s : type1470 A K => @lem4420552 A K s k t). Qed.
Lemma lem4420562 {A K : Type'} (t : type1470 A K) : term422 A K t.
Proof. exact (fun k : K -> Prop => @lem4420557 A K k t). Qed.
Lemma lem4420567 {A K : Type'} : term426 A K.
Proof. exact (fun t : type1470 A K => @lem4420562 A K t). Qed.
Lemma lem4420568 {A K : Type'} : term425 A K.
Proof. exact (EQ_MP (@lem4419701 A K) (@lem4420567 A K)). Qed.
Lemma lem4420569 {A K : Type'} (t : type1470 A K) : term544 A K t.
Proof. exact (@lem4420568 A K t). Qed.
Lemma lem4420570 {A K : Type'} (t : type1470 A K) : (term544 A K t) = (term421 A K t).
Proof. exact (eq_refl (term544 A K t)). Qed.
Lemma lem4420571 {A K : Type'} (t : type1470 A K) : term421 A K t.
Proof. exact (EQ_MP (@lem4420570 A K t) (@lem4420569 A K t)). Qed.
Lemma lem4420572 {A K : Type'} (t : type1470 A K) (k : K -> Prop) : term545 A K t k.
Proof. exact (@lem4420571 A K t k). Qed.
Lemma lem4420573 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term545 A K t k) = (term417 A K k t).
Proof. exact (eq_refl (term545 A K t k)). Qed.
Lemma lem4420574 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : term417 A K k t.
Proof. exact (EQ_MP (@lem4420573 A K k t) (@lem4420572 A K t k)). Qed.
Lemma lem4420575 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : term546 A K k t s.
Proof. exact (@lem4420574 A K k t s). Qed.
Lemma lem4420576 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term546 A K k t s) = (term409 A K s k t).
Proof. exact (eq_refl (term546 A K k t s)). Qed.
Lemma lem4420577 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : term409 A K s k t.
Proof. exact (EQ_MP (@lem4420576 A K s k t) (@lem4420575 A K k t s)). Qed.
Lemma lem4420579 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : term409 A K s k t.
Proof. exact (@lem4419496 A K s k t (@lem4420577 A K s k t)). Qed.
Lemma lem4420580 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term410 A K s k t) : False.
Proof. exact (@lem4420579 A K s k t (@lem4419480 A K s k t h1)). Qed.
Lemma lem4420581 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term410 A K s k t) : (term410 A K s k t) = False.
Proof. exact (prop_ext (fun h2 : term410 A K s k t => @lem4420580 A K s k t h1) (fun h2 : False => @lem4419480 A K s k t h1)). Qed.
Lemma lem4420582 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term410 A K s k t) : False.
Proof. exact (EQ_MP (@lem4420581 A K s k t h1) (@lem4419480 A K s k t h1)). Qed.
Lemma lem4420583 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : term409 A K s k t.
Proof. exact (fun h0 : term410 A K s k t => @lem4420582 A K s k t h0). Qed.
Lemma lem4420584 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : term408 A K s k t.
Proof. exact (EQ_MP (@lem4419479 A K s k t) (@lem4420583 A K s k t)). Qed.
Lemma lem4420586 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = (term22 A K k s).
Proof. exact (EQ_MP (@lem4419149 A K k s) (@lem4419148 A K k s)). Qed.
Lemma lem4420587 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = (term22 A K k s).
Proof. exact (@lem4420586 A K k s). Qed.
Lemma lem4420588 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4420589 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term358 A K k s) = (term24 A K k s).
Proof. exact (MK_COMB (@lem4420588) (@lem4420587 A K k s)). Qed.
Lemma lem4420590 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term358 A K k s) : term24 A K k s.
Proof. exact (EQ_MP (@lem4420589 A K k s) (@lem4419215 A K k s h1)). Qed.
Lemma lem4420594 {_106233 _106250 : Type'} (k : _106250 -> Prop) (s : type1470 _106233 _106250) : (term24 _106233 _106250 k s) = (term28 _106233 _106250 k s).
Proof. exact (EQ_MP (@lem4417849 _106233 _106250 k s) (@lem4419143 _106233 _106250 k s)). Qed.
Lemma lem4420595 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term24 A K k s) = (term28 A K k s).
Proof. exact (@lem4420594 A K k s). Qed.
Lemma lem4420606 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4420607 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term547 A K k s) = (term548 A K k s).
Proof. exact (MK_COMB (@lem4420606) (@lem4420595 A K k s)). Qed.
Lemma lem4420644 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term549 A K k s t) = (term549 A K k s t).
Proof. exact (eq_refl (term549 A K k s t)). Qed.
Lemma lem4420645 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term550 A K k s t) = (term551 A K k s t).
Proof. exact (MK_COMB (@lem4420607 A K k s) (@lem4420644 A K k s t)). Qed.
Lemma lem4420648 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term551 A K k s t) = (term550 A K k s t).
Proof. exact (SYM (@lem4420645 A K k s t)). Qed.
Lemma lem4420652 {A B : Type'} (P : type1413 A B) : (term13 A B P) = (term14 A B P).
Proof. exact (EQ_MP (@lem4417782 A B P) (@lem4417781 A B P)). Qed.
Lemma lem4420653 {A K : Type'} (P : type1470 A K) : (term179 A K P) = (term180 A K P).
Proof. exact (@lem4420652 K A P). Qed.
Lemma lem4420654 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term552 A K k s) = (term553 A K k s).
Proof. exact (@lem4420653 A K (term554 A K k s)). Qed.
Lemma lem4420655 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term555 A K k s i) = (term46 A K k s i).
Proof. exact (eq_refl (term555 A K k s i)). Qed.
Lemma lem4420656 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4420657 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (a : A) : (term556 A K k s i a) = (term557 A K k s i a).
Proof. exact (MK_COMB (@lem4420655 A K k s i) (@lem4420656 A a)). Qed.
Lemma lem4420658 {A K : Type'} (k : K -> Prop) (a : A) (s : type1470 A K) (i : K) : (term557 A K k s i a) = (term44 A K k a s i).
Proof. exact (eq_refl (term557 A K k s i a)). Qed.
Lemma lem4420659 {A K : Type'} (k : K -> Prop) (a : A) (s : type1470 A K) (i : K) : (term556 A K k s i a) = (term44 A K k a s i).
Proof. exact (TRANS (@lem4420657 A K k s i a) (@lem4420658 A K k a s i)). Qed.
Lemma lem4420660 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term558 A K k s i) = (term46 A K k s i).
Proof. exact (fun_ext (fun a : A => @lem4420659 A K k a s i)). Qed.
Lemma lem4420661 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4420662 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term559 A K k s i) = (term48 A K k s i).
Proof. exact (MK_COMB (@lem4420661 A) (@lem4420660 A K k s i)). Qed.
Lemma lem4420663 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term560 A K k s) = (term50 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4420662 A K k s i)). Qed.
Lemma lem4420664 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4420665 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term552 A K k s) = (term28 A K k s).
Proof. exact (MK_COMB (@lem4420664 K) (@lem4420663 A K k s)). Qed.
Lemma lem4420666 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4420667 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term561 A K k s) = (term562 A K k s).
Proof. exact (MK_COMB (@lem4420666) (@lem4420665 A K k s)). Qed.
Lemma lem4420668 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term555 A K k s i) = (term46 A K k s i).
Proof. exact (eq_refl (term555 A K k s i)). Qed.
Lemma lem4420669 {A K : Type'} (a : K -> A) (i : K) : (a i) = (a i).
Proof. exact (eq_refl (a i)). Qed.
Lemma lem4420670 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (a : K -> A) (i : K) : (term563 A K k s a i) = (term564 A K k s a i).
Proof. exact (MK_COMB (@lem4420668 A K k s i) (@lem4420669 A K a i)). Qed.
Lemma lem4420671 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) (i : K) : (term564 A K k s a i) = (term427 A K k a s i).
Proof. exact (eq_refl (term564 A K k s a i)). Qed.
Lemma lem4420672 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) (i : K) : (term563 A K k s a i) = (term427 A K k a s i).
Proof. exact (TRANS (@lem4420670 A K k s a i) (@lem4420671 A K k a s i)). Qed.
Lemma lem4420673 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) : (term565 A K k s a) = (term428 A K k a s).
Proof. exact (fun_ext (fun i : K => @lem4420672 A K k a s i)). Qed.
Lemma lem4420674 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4420675 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) : (term566 A K k s a) = (term429 A K k a s).
Proof. exact (MK_COMB (@lem4420674 K) (@lem4420673 A K k a s)). Qed.
Lemma lem4420676 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term567 A K k s) = (term568 A K k s).
Proof. exact (fun_ext (fun a : K -> A => @lem4420675 A K k a s)). Qed.
Lemma lem4420677 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4420678 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term553 A K k s) = (term569 A K k s).
Proof. exact (MK_COMB (@lem4420677 A K) (@lem4420676 A K k s)). Qed.
Lemma lem4420679 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term552 A K k s) = (term553 A K k s)) = ((term28 A K k s) = (term569 A K k s)).
Proof. exact (MK_COMB (@lem4420667 A K k s) (@lem4420678 A K k s)). Qed.
Lemma lem4420680 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term28 A K k s) = (term569 A K k s).
Proof. exact (EQ_MP (@lem4420679 A K k s) (@lem4420654 A K k s)). Qed.
Lemma lem4420691 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4420692 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term548 A K k s) = (term570 A K k s).
Proof. exact (MK_COMB (@lem4420691) (@lem4420680 A K k s)). Qed.
Lemma lem4420729 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term549 A K k s t) = (term549 A K k s t).
Proof. exact (eq_refl (term549 A K k s t)). Qed.
Lemma lem4420730 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term551 A K k s t) = (term571 A K k s t).
Proof. exact (MK_COMB (@lem4420692 A K k s) (@lem4420729 A K k s t)). Qed.
Lemma lem4420732 {A : Type'} (P : A -> Prop) (Q : Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem4417779 A P Q) (@lem4417778 A P Q)). Qed.
Lemma lem4420733 {A K : Type'} (P : type805 A K) (Q : Prop) : (term572 A K P Q) = (term573 A K P Q).
Proof. exact (@lem4420732 (K -> A) P Q). Qed.
Lemma lem4420734 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term574 A K k s t) = (term575 A K k s t).
Proof. exact (@lem4420733 A K (term568 A K k s) (term549 A K k s t)). Qed.
Lemma lem4420735 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) : (term576 A K k s a) = (term429 A K k a s).
Proof. exact (eq_refl (term576 A K k s a)). Qed.
Lemma lem4420736 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term577 A K k s) = (term568 A K k s).
Proof. exact (fun_ext (fun a : K -> A => @lem4420735 A K k a s)). Qed.
Lemma lem4420737 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4420738 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term578 A K k s) = (term569 A K k s).
Proof. exact (MK_COMB (@lem4420737 A K) (@lem4420736 A K k s)). Qed.
Lemma lem4420739 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4420740 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term579 A K k s) = (term570 A K k s).
Proof. exact (MK_COMB (@lem4420739) (@lem4420738 A K k s)). Qed.
Lemma lem4420741 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term549 A K k s t) = (term549 A K k s t).
Proof. exact (eq_refl (term549 A K k s t)). Qed.
Lemma lem4420742 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term574 A K k s t) = (term571 A K k s t).
Proof. exact (MK_COMB (@lem4420740 A K k s) (@lem4420741 A K k s t)). Qed.
Lemma lem4420743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4420744 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term580 A K k s t) = (term581 A K k s t).
Proof. exact (MK_COMB (@lem4420743) (@lem4420742 A K k s t)). Qed.
Lemma lem4420745 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) : (term576 A K k s a) = (term429 A K k a s).
Proof. exact (eq_refl (term576 A K k s a)). Qed.
Lemma lem4420746 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4420747 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) : (term582 A K k s a) = (term583 A K k a s).
Proof. exact (MK_COMB (@lem4420746) (@lem4420745 A K k a s)). Qed.
Lemma lem4420748 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term549 A K k s t) = (term549 A K k s t).
Proof. exact (eq_refl (term549 A K k s t)). Qed.
Lemma lem4420749 {A K : Type'} (a : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term584 A K a k s t) = (term585 A K a k s t).
Proof. exact (MK_COMB (@lem4420747 A K k a s) (@lem4420748 A K k s t)). Qed.
Lemma lem4420750 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term586 A K k s t) = (term587 A K k s t).
Proof. exact (fun_ext (fun a : K -> A => @lem4420749 A K a k s t)). Qed.
Lemma lem4420751 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4420752 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term575 A K k s t) = (term588 A K k s t).
Proof. exact (MK_COMB (@lem4420751 A K) (@lem4420750 A K k s t)). Qed.
Lemma lem4420753 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term574 A K k s t) = (term575 A K k s t)) = ((term571 A K k s t) = (term588 A K k s t)).
Proof. exact (MK_COMB (@lem4420744 A K k s t) (@lem4420752 A K k s t)). Qed.
Lemma lem4420754 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term571 A K k s t) = (term588 A K k s t).
Proof. exact (EQ_MP (@lem4420753 A K k s t) (@lem4420734 A K k s t)). Qed.
Lemma lem4420803 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term551 A K k s t) = (term588 A K k s t).
Proof. exact (TRANS (@lem4420730 A K k s t) (@lem4420754 A K k s t)). Qed.
Lemma lem4420804 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term588 A K k s t) = (term551 A K k s t).
Proof. exact (SYM (@lem4420803 A K k s t)). Qed.
Lemma lem4420805 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term429 A K k z s) : term429 A K k z s.
Proof. exact (h1). Qed.
Lemma lem4420806 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term399 A K s k t) : term399 A K s k t.
Proof. exact (h1). Qed.
Lemma lem4420807 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4420808 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (h1 : term30 A K x s i) : term30 A K x s i.
Proof. exact (h1). Qed.
Lemma lem4420809 {A K : Type'} (i : K) (x : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term399 A K s k t) : term589 A K s t k i x z.
Proof. exact (@lem4420806 A K s k t h1 (term590 A K k i x z)). Qed.
Lemma lem4420810 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) : (term589 A K s t k i x z) = (term591 A K s k i x z t).
Proof. exact (eq_refl (term589 A K s t k i x z)). Qed.
Lemma lem4420811 {A K : Type'} (i : K) (x : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term399 A K s k t) : term591 A K s k i x z t.
Proof. exact (EQ_MP (@lem4420810 A K s k i x z t) (@lem4420809 A K i x z s k t h1)). Qed.
Lemma lem4420819 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term6 A B s).
Proof. exact (EQ_MP (@lem4417773 A B s) (@lem4417772 A B s)). Qed.
Lemma lem4420820 {A K : Type'} (s : K -> Prop) : (@EXTENSIONAL K A s) = (term592 A K s).
Proof. exact (@lem4420819 K A s). Qed.
Lemma lem4420821 {A K : Type'} (k : K -> Prop) : (@EXTENSIONAL K A k) = (term592 A K k).
Proof. exact (@lem4420820 A K k). Qed.
Lemma lem4420838 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term590 A K k i x z) = (term590 A K k i x z).
Proof. exact (eq_refl (term590 A K k i x z)). Qed.
Lemma lem4420839 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term593 A K k i x z) = (term594 A K k i x z).
Proof. exact (MK_COMB (@lem4420821 A K k) (@lem4420838 A K k i x z)). Qed.
Lemma lem4420841 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term4 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem4417749 _83152 p x) (@lem4417748 _83152 p x)). Qed.
Lemma lem4420842 {A K : Type'} (p : type805 A K) (x : K -> A) : (term595 A K p x) = (p x).
Proof. exact (@lem4420841 (K -> A) p x). Qed.
Lemma lem4420843 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term596 A K k i x z) = (term597 A K k i x z).
Proof. exact (@lem4420842 A K (term598 A K k) (term590 A K k i x z)). Qed.
Lemma lem4420844 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term599 A K k f) = (term600 A K k f).
Proof. exact (eq_refl (term599 A K k f)). Qed.
Lemma lem4420845 {A K : Type'} (GEN_PVAR_139 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_139) = (@SETSPEC (K -> A) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_139)). Qed.
Lemma lem4420846 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term601 A K GEN_PVAR_139 k f) = (term602 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4420845 A K GEN_PVAR_139) (@lem4420844 A K k f)). Qed.
Lemma lem4420847 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4420848 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term603 A K GEN_PVAR_139 k f) = (term604 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4420846 A K GEN_PVAR_139 k f) (@lem4420847 A K f)). Qed.
Lemma lem4420849 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term605 A K GEN_PVAR_139 k) = (term606 A K GEN_PVAR_139 k).
Proof. exact (fun_ext (fun f : K -> A => @lem4420848 A K GEN_PVAR_139 k f)). Qed.
Lemma lem4420850 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4420851 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term607 A K GEN_PVAR_139 k) = (term608 A K GEN_PVAR_139 k).
Proof. exact (MK_COMB (@lem4420850 A K) (@lem4420849 A K GEN_PVAR_139 k)). Qed.
Lemma lem4420852 {A K : Type'} (k : K -> Prop) : (term609 A K k) = (term610 A K k).
Proof. exact (fun_ext (fun GEN_PVAR_139 : K -> A => @lem4420851 A K GEN_PVAR_139 k)). Qed.
Lemma lem4420853 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4420854 {A K : Type'} (k : K -> Prop) : (term611 A K k) = (term592 A K k).
Proof. exact (MK_COMB (@lem4420853 A K) (@lem4420852 A K k)). Qed.
Lemma lem4420855 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term590 A K k i x z) = (term590 A K k i x z).
Proof. exact (eq_refl (term590 A K k i x z)). Qed.
Lemma lem4420856 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term596 A K k i x z) = (term594 A K k i x z).
Proof. exact (MK_COMB (@lem4420854 A K k) (@lem4420855 A K k i x z)). Qed.
Lemma lem4420857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4420858 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term612 A K k i x z) = (term613 A K k i x z).
Proof. exact (MK_COMB (@lem4420857) (@lem4420856 A K k i x z)). Qed.
Lemma lem4420859 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term597 A K k i x z) = (term614 A K k i x z).
Proof. exact (eq_refl (term597 A K k i x z)). Qed.
Lemma lem4420860 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : ((term596 A K k i x z) = (term597 A K k i x z)) = ((term594 A K k i x z) = (term614 A K k i x z)).
Proof. exact (MK_COMB (@lem4420858 A K k i x z) (@lem4420859 A K k i x z)). Qed.
Lemma lem4420861 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term594 A K k i x z) = (term614 A K k i x z).
Proof. exact (EQ_MP (@lem4420860 A K k i x z) (@lem4420843 A K k i x z)). Qed.
Lemma lem4420871 {A B : Type'} (f : A -> B) (y : A) : (term615 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4420872 {A K : Type'} (f : K -> A) (y : K) : (term616 A K f y) = (f y).
Proof. exact (@lem4420871 K A f y). Qed.
Lemma lem4420873 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term617 A K k i x z x') = (term618 A K k i x z x').
Proof. exact (@lem4420872 A K (term590 A K k i x z) x'). Qed.
Lemma lem4420874 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (j : K) : (term618 A K k i x z j) = (term619 A K k i x z j).
Proof. exact (eq_refl (term618 A K k i x z j)). Qed.
Lemma lem4420875 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term620 A K k i x z) = (term590 A K k i x z).
Proof. exact (fun_ext (fun j : K => @lem4420874 A K k i x z j)). Qed.
Lemma lem4420876 {K : Type'} (x : K) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4420877 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term617 A K k i x z x') = (term618 A K k i x z x').
Proof. exact (MK_COMB (@lem4420875 A K k i x z) (@lem4420876 K x')). Qed.
Lemma lem4420878 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4420879 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term621 A K k i x z x') = (term622 A K k i x z x').
Proof. exact (MK_COMB (@lem4420878 A) (@lem4420877 A K k i x z x')). Qed.
Lemma lem4420880 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term618 A K k i x z x') = (term619 A K k i x z x').
Proof. exact (eq_refl (term618 A K k i x z x')). Qed.
Lemma lem4420881 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : ((term617 A K k i x z x') = (term618 A K k i x z x')) = ((term618 A K k i x z x') = (term619 A K k i x z x')).
Proof. exact (MK_COMB (@lem4420879 A K k i x z x') (@lem4420880 A K k i x z x')). Qed.
Lemma lem4420882 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term618 A K k i x z x') = (term619 A K k i x z x').
Proof. exact (EQ_MP (@lem4420881 A K k i x z x') (@lem4420873 A K k i x z x')). Qed.
Lemma lem4420887 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4420888 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term622 A K k i x z x') = (term623 A K k i x z x').
Proof. exact (MK_COMB (@lem4420887 A) (@lem4420882 A K k i x z x')). Qed.
Lemma lem4420889 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4420890 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : ((term618 A K k i x z x') = (@ARB A)) = ((term619 A K k i x z x') = (@ARB A)).
Proof. exact (MK_COMB (@lem4420888 A K k i x z x') (@lem4420889 A)). Qed.
Lemma lem4420893 {K : Type'} (x : K) (k : K -> Prop) : (term624 K x k) = (term624 K x k).
Proof. exact (eq_refl (term624 K x k)). Qed.
Lemma lem4420894 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term625 A K k i x z x') = (term626 A K k i x z x').
Proof. exact (MK_COMB (@lem4420893 K x' k) (@lem4420890 A K k i x z x')). Qed.
Lemma lem4420897 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term627 A K k i x z) = (term628 A K k i x z).
Proof. exact (fun_ext (fun x' : K => @lem4420894 A K k i x z x')). Qed.
Lemma lem4420898 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4420899 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term614 A K k i x z) = (term629 A K k i x z).
Proof. exact (MK_COMB (@lem4420898 K) (@lem4420897 A K k i x z)). Qed.
Lemma lem4420904 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term594 A K k i x z) = (term629 A K k i x z).
Proof. exact (TRANS (@lem4420861 A K k i x z) (@lem4420899 A K k i x z)). Qed.
Lemma lem4420905 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term593 A K k i x z) = (term629 A K k i x z).
Proof. exact (TRANS (@lem4420839 A K k i x z) (@lem4420904 A K k i x z)). Qed.
Lemma lem4420906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4420907 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term630 A K k i x z) = (term631 A K k i x z).
Proof. exact (MK_COMB (@lem4420906) (@lem4420905 A K k i x z)). Qed.
Lemma lem4420915 {A B : Type'} (f : A -> B) (y : A) : (term615 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4420916 {A K : Type'} (f : K -> A) (y : K) : (term616 A K f y) = (f y).
Proof. exact (@lem4420915 K A f y). Qed.
Lemma lem4420917 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : (term617 A K k i x z i') = (term618 A K k i x z i').
Proof. exact (@lem4420916 A K (term590 A K k i x z) i'). Qed.
Lemma lem4420918 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (j : K) : (term618 A K k i x z j) = (term619 A K k i x z j).
Proof. exact (eq_refl (term618 A K k i x z j)). Qed.
Lemma lem4420919 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term620 A K k i x z) = (term590 A K k i x z).
Proof. exact (fun_ext (fun j : K => @lem4420918 A K k i x z j)). Qed.
Lemma lem4420920 {K : Type'} (i' : K) : i' = i'.
Proof. exact (eq_refl i'). Qed.
Lemma lem4420921 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : (term617 A K k i x z i') = (term618 A K k i x z i').
Proof. exact (MK_COMB (@lem4420919 A K k i x z) (@lem4420920 K i')). Qed.
Lemma lem4420922 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4420923 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : (term621 A K k i x z i') = (term622 A K k i x z i').
Proof. exact (MK_COMB (@lem4420922 A) (@lem4420921 A K k i x z i')). Qed.
Lemma lem4420924 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : (term618 A K k i x z i') = (term619 A K k i x z i').
Proof. exact (eq_refl (term618 A K k i x z i')). Qed.
Lemma lem4420925 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : ((term617 A K k i x z i') = (term618 A K k i x z i')) = ((term618 A K k i x z i') = (term619 A K k i x z i')).
Proof. exact (MK_COMB (@lem4420923 A K k i x z i') (@lem4420924 A K k i x z i')). Qed.
Lemma lem4420926 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : (term618 A K k i x z i') = (term619 A K k i x z i').
Proof. exact (EQ_MP (@lem4420925 A K k i x z i') (@lem4420917 A K k i x z i')). Qed.
Lemma lem4420931 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4420932 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : (term632 A K k i x z i') = (term633 A K k i x z i').
Proof. exact (MK_COMB (@lem4420931 A) (@lem4420926 A K k i x z i')). Qed.
Lemma lem4420933 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4420934 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) (i' : K) : (term634 A K k i x z s i') = (term635 A K k i x z s i').
Proof. exact (MK_COMB (@lem4420932 A K k i x z i') (@lem4420933 A K s i')). Qed.
Lemma lem4420935 {K : Type'} (i' : K) (k : K -> Prop) : (term42 K i' k) = (term42 K i' k).
Proof. exact (eq_refl (term42 K i' k)). Qed.
Lemma lem4420936 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) (i' : K) : (term636 A K k i x z s i') = (term637 A K k i x z s i').
Proof. exact (MK_COMB (@lem4420935 K i' k) (@lem4420934 A K k i x z s i')). Qed.
Lemma lem4420939 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) : (term638 A K k i x z s) = (term639 A K k i x z s).
Proof. exact (fun_ext (fun i' : K => @lem4420936 A K k i x z s i')). Qed.
Lemma lem4420940 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4420941 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) : (term640 A K k i x z s) = (term641 A K k i x z s).
Proof. exact (MK_COMB (@lem4420940 K) (@lem4420939 A K k i x z s)). Qed.
Lemma lem4420946 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) : (term642 A K k i x z s) = (term643 A K k i x z s).
Proof. exact (MK_COMB (@lem4420907 A K k i x z) (@lem4420941 A K k i x z s)). Qed.
Lemma lem4420949 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4420950 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) : (term644 A K k i x z s) = (term645 A K k i x z s).
Proof. exact (MK_COMB (@lem4420949) (@lem4420946 A K k i x z s)). Qed.
Lemma lem4420954 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term6 A B s).
Proof. exact (EQ_MP (@lem4417773 A B s) (@lem4417772 A B s)). Qed.
Lemma lem4420955 {A K : Type'} (s : K -> Prop) : (@EXTENSIONAL K A s) = (term592 A K s).
Proof. exact (@lem4420954 K A s). Qed.
Lemma lem4420956 {A K : Type'} (k : K -> Prop) : (@EXTENSIONAL K A k) = (term592 A K k).
Proof. exact (@lem4420955 A K k). Qed.
Lemma lem4420973 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term590 A K k i x z) = (term590 A K k i x z).
Proof. exact (eq_refl (term590 A K k i x z)). Qed.
Lemma lem4420974 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term593 A K k i x z) = (term594 A K k i x z).
Proof. exact (MK_COMB (@lem4420956 A K k) (@lem4420973 A K k i x z)). Qed.
Lemma lem4420976 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term4 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem4417749 _83152 p x) (@lem4417748 _83152 p x)). Qed.
Lemma lem4420977 {A K : Type'} (p : type805 A K) (x : K -> A) : (term595 A K p x) = (p x).
Proof. exact (@lem4420976 (K -> A) p x). Qed.
Lemma lem4420978 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term596 A K k i x z) = (term597 A K k i x z).
Proof. exact (@lem4420977 A K (term598 A K k) (term590 A K k i x z)). Qed.
Lemma lem4420979 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term599 A K k f) = (term600 A K k f).
Proof. exact (eq_refl (term599 A K k f)). Qed.
Lemma lem4420980 {A K : Type'} (GEN_PVAR_139 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_139) = (@SETSPEC (K -> A) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_139)). Qed.
Lemma lem4420981 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term601 A K GEN_PVAR_139 k f) = (term602 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4420980 A K GEN_PVAR_139) (@lem4420979 A K k f)). Qed.
Lemma lem4420982 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4420983 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term603 A K GEN_PVAR_139 k f) = (term604 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4420981 A K GEN_PVAR_139 k f) (@lem4420982 A K f)). Qed.
Lemma lem4420984 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term605 A K GEN_PVAR_139 k) = (term606 A K GEN_PVAR_139 k).
Proof. exact (fun_ext (fun f : K -> A => @lem4420983 A K GEN_PVAR_139 k f)). Qed.
Lemma lem4420985 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4420986 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term607 A K GEN_PVAR_139 k) = (term608 A K GEN_PVAR_139 k).
Proof. exact (MK_COMB (@lem4420985 A K) (@lem4420984 A K GEN_PVAR_139 k)). Qed.
Lemma lem4420987 {A K : Type'} (k : K -> Prop) : (term609 A K k) = (term610 A K k).
Proof. exact (fun_ext (fun GEN_PVAR_139 : K -> A => @lem4420986 A K GEN_PVAR_139 k)). Qed.
Lemma lem4420988 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4420989 {A K : Type'} (k : K -> Prop) : (term611 A K k) = (term592 A K k).
Proof. exact (MK_COMB (@lem4420988 A K) (@lem4420987 A K k)). Qed.
Lemma lem4420990 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term590 A K k i x z) = (term590 A K k i x z).
Proof. exact (eq_refl (term590 A K k i x z)). Qed.
Lemma lem4420991 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term596 A K k i x z) = (term594 A K k i x z).
Proof. exact (MK_COMB (@lem4420989 A K k) (@lem4420990 A K k i x z)). Qed.
Lemma lem4420992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4420993 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term612 A K k i x z) = (term613 A K k i x z).
Proof. exact (MK_COMB (@lem4420992) (@lem4420991 A K k i x z)). Qed.
Lemma lem4420994 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term597 A K k i x z) = (term614 A K k i x z).
Proof. exact (eq_refl (term597 A K k i x z)). Qed.
Lemma lem4420995 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : ((term596 A K k i x z) = (term597 A K k i x z)) = ((term594 A K k i x z) = (term614 A K k i x z)).
Proof. exact (MK_COMB (@lem4420993 A K k i x z) (@lem4420994 A K k i x z)). Qed.
Lemma lem4420996 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term594 A K k i x z) = (term614 A K k i x z).
Proof. exact (EQ_MP (@lem4420995 A K k i x z) (@lem4420978 A K k i x z)). Qed.
Lemma lem4421006 {A B : Type'} (f : A -> B) (y : A) : (term615 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4421007 {A K : Type'} (f : K -> A) (y : K) : (term616 A K f y) = (f y).
Proof. exact (@lem4421006 K A f y). Qed.
Lemma lem4421008 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term617 A K k i x z x') = (term618 A K k i x z x').
Proof. exact (@lem4421007 A K (term590 A K k i x z) x'). Qed.
Lemma lem4421009 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (j : K) : (term618 A K k i x z j) = (term619 A K k i x z j).
Proof. exact (eq_refl (term618 A K k i x z j)). Qed.
Lemma lem4421010 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term620 A K k i x z) = (term590 A K k i x z).
Proof. exact (fun_ext (fun j : K => @lem4421009 A K k i x z j)). Qed.
Lemma lem4421011 {K : Type'} (x : K) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4421012 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term617 A K k i x z x') = (term618 A K k i x z x').
Proof. exact (MK_COMB (@lem4421010 A K k i x z) (@lem4421011 K x')). Qed.
Lemma lem4421013 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4421014 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term621 A K k i x z x') = (term622 A K k i x z x').
Proof. exact (MK_COMB (@lem4421013 A) (@lem4421012 A K k i x z x')). Qed.
Lemma lem4421015 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term618 A K k i x z x') = (term619 A K k i x z x').
Proof. exact (eq_refl (term618 A K k i x z x')). Qed.
Lemma lem4421016 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : ((term617 A K k i x z x') = (term618 A K k i x z x')) = ((term618 A K k i x z x') = (term619 A K k i x z x')).
Proof. exact (MK_COMB (@lem4421014 A K k i x z x') (@lem4421015 A K k i x z x')). Qed.
Lemma lem4421017 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term618 A K k i x z x') = (term619 A K k i x z x').
Proof. exact (EQ_MP (@lem4421016 A K k i x z x') (@lem4421008 A K k i x z x')). Qed.
Lemma lem4421022 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4421023 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term622 A K k i x z x') = (term623 A K k i x z x').
Proof. exact (MK_COMB (@lem4421022 A) (@lem4421017 A K k i x z x')). Qed.
Lemma lem4421024 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4421025 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : ((term618 A K k i x z x') = (@ARB A)) = ((term619 A K k i x z x') = (@ARB A)).
Proof. exact (MK_COMB (@lem4421023 A K k i x z x') (@lem4421024 A)). Qed.
Lemma lem4421028 {K : Type'} (x : K) (k : K -> Prop) : (term624 K x k) = (term624 K x k).
Proof. exact (eq_refl (term624 K x k)). Qed.
Lemma lem4421029 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term625 A K k i x z x') = (term626 A K k i x z x').
Proof. exact (MK_COMB (@lem4421028 K x' k) (@lem4421025 A K k i x z x')). Qed.
Lemma lem4421032 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term627 A K k i x z) = (term628 A K k i x z).
Proof. exact (fun_ext (fun x' : K => @lem4421029 A K k i x z x')). Qed.
Lemma lem4421033 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4421034 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term614 A K k i x z) = (term629 A K k i x z).
Proof. exact (MK_COMB (@lem4421033 K) (@lem4421032 A K k i x z)). Qed.
Lemma lem4421039 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term594 A K k i x z) = (term629 A K k i x z).
Proof. exact (TRANS (@lem4420996 A K k i x z) (@lem4421034 A K k i x z)). Qed.
Lemma lem4421040 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term593 A K k i x z) = (term629 A K k i x z).
Proof. exact (TRANS (@lem4420974 A K k i x z) (@lem4421039 A K k i x z)). Qed.
Lemma lem4421041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4421042 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term630 A K k i x z) = (term631 A K k i x z).
Proof. exact (MK_COMB (@lem4421041) (@lem4421040 A K k i x z)). Qed.
Lemma lem4421050 {A B : Type'} (f : A -> B) (y : A) : (term615 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4421051 {A K : Type'} (f : K -> A) (y : K) : (term616 A K f y) = (f y).
Proof. exact (@lem4421050 K A f y). Qed.
Lemma lem4421052 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : (term617 A K k i x z i') = (term618 A K k i x z i').
Proof. exact (@lem4421051 A K (term590 A K k i x z) i'). Qed.
Lemma lem4421053 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (j : K) : (term618 A K k i x z j) = (term619 A K k i x z j).
Proof. exact (eq_refl (term618 A K k i x z j)). Qed.
Lemma lem4421054 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term620 A K k i x z) = (term590 A K k i x z).
Proof. exact (fun_ext (fun j : K => @lem4421053 A K k i x z j)). Qed.
Lemma lem4421055 {K : Type'} (i' : K) : i' = i'.
Proof. exact (eq_refl i'). Qed.
Lemma lem4421056 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : (term617 A K k i x z i') = (term618 A K k i x z i').
Proof. exact (MK_COMB (@lem4421054 A K k i x z) (@lem4421055 K i')). Qed.
Lemma lem4421057 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4421058 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : (term621 A K k i x z i') = (term622 A K k i x z i').
Proof. exact (MK_COMB (@lem4421057 A) (@lem4421056 A K k i x z i')). Qed.
Lemma lem4421059 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : (term618 A K k i x z i') = (term619 A K k i x z i').
Proof. exact (eq_refl (term618 A K k i x z i')). Qed.
Lemma lem4421060 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : ((term617 A K k i x z i') = (term618 A K k i x z i')) = ((term618 A K k i x z i') = (term619 A K k i x z i')).
Proof. exact (MK_COMB (@lem4421058 A K k i x z i') (@lem4421059 A K k i x z i')). Qed.
Lemma lem4421061 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : (term618 A K k i x z i') = (term619 A K k i x z i').
Proof. exact (EQ_MP (@lem4421060 A K k i x z i') (@lem4421052 A K k i x z i')). Qed.
Lemma lem4421066 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4421067 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : (term632 A K k i x z i') = (term633 A K k i x z i').
Proof. exact (MK_COMB (@lem4421066 A) (@lem4421061 A K k i x z i')). Qed.
Lemma lem4421068 {A K : Type'} (t : type1470 A K) (i' : K) : (t i') = (t i').
Proof. exact (eq_refl (t i')). Qed.
Lemma lem4421069 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (i' : K) : (term634 A K k i x z t i') = (term635 A K k i x z t i').
Proof. exact (MK_COMB (@lem4421067 A K k i x z i') (@lem4421068 A K t i')). Qed.
Lemma lem4421070 {K : Type'} (i' : K) (k : K -> Prop) : (term42 K i' k) = (term42 K i' k).
Proof. exact (eq_refl (term42 K i' k)). Qed.
Lemma lem4421071 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (i' : K) : (term636 A K k i x z t i') = (term637 A K k i x z t i').
Proof. exact (MK_COMB (@lem4421070 K i' k) (@lem4421069 A K k i x z t i')). Qed.
Lemma lem4421074 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) : (term638 A K k i x z t) = (term639 A K k i x z t).
Proof. exact (fun_ext (fun i' : K => @lem4421071 A K k i x z t i')). Qed.
Lemma lem4421075 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4421076 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) : (term640 A K k i x z t) = (term641 A K k i x z t).
Proof. exact (MK_COMB (@lem4421075 K) (@lem4421074 A K k i x z t)). Qed.
Lemma lem4421081 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) : (term642 A K k i x z t) = (term643 A K k i x z t).
Proof. exact (MK_COMB (@lem4421042 A K k i x z) (@lem4421076 A K k i x z t)). Qed.
Lemma lem4421084 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) : (term591 A K s k i x z t) = (term646 A K s k i x z t).
Proof. exact (MK_COMB (@lem4420950 A K k i x z s) (@lem4421081 A K k i x z t)). Qed.
Lemma lem4421087 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4421088 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) : (term647 A K s k i x z t) = (term648 A K s k i x z t).
Proof. exact (MK_COMB (@lem4421087) (@lem4421084 A K s k i x z t)). Qed.
Lemma lem4421089 {A K : Type'} (x : A) (t : type1470 A K) (i : K) : (term30 A K x t i) = (term30 A K x t i).
Proof. exact (eq_refl (term30 A K x t i)). Qed.
Lemma lem4421090 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term649 A K s k z x t i) = (term650 A K s k z x t i).
Proof. exact (MK_COMB (@lem4421088 A K s k i x z t) (@lem4421089 A K x t i)). Qed.
Lemma lem4421093 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term650 A K s k z x t i) = (term649 A K s k z x t i).
Proof. exact (SYM (@lem4421090 A K s k z x t i)). Qed.
Lemma lem4421097 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term651 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4421098 (p : Prop) (q : Prop) (p' : Prop) : term652 p q p'.
Proof. exact (fun q' : Prop => @lem4421097 p q p' q'). Qed.
Lemma lem4421099 (p : Prop) (q : Prop) : term653 p q.
Proof. exact (fun p' : Prop => @lem4421098 p q p'). Qed.
Lemma lem4421100 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : term654 A K s k z x t i.
Proof. exact (@lem4421099 (term646 A K s k i x z t) (term30 A K x t i)). Qed.
Lemma lem4421101 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (p' : Prop) : term655 A K s k z x t i p'.
Proof. exact (@lem4421100 A K s k z x t i p'). Qed.
Lemma lem4421102 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (p' : Prop) : (term655 A K s k z x t i p') = (term656 A K s k z x t i p').
Proof. exact (eq_refl (term655 A K s k z x t i p')). Qed.
Lemma lem4421103 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (p' : Prop) : term656 A K s k z x t i p'.
Proof. exact (EQ_MP (@lem4421102 A K s k z x t i p') (@lem4421101 A K s k z x t i p')). Qed.
Lemma lem4421104 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (p' : Prop) (q' : Prop) : term657 A K s k z x t i p' q'.
Proof. exact (@lem4421103 A K s k z x t i p' q'). Qed.
Lemma lem4421105 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (p' : Prop) (q' : Prop) : (term657 A K s k z x t i p' q') = (term658 A K s k z x t i p' q').
Proof. exact (eq_refl (term657 A K s k z x t i p' q')). Qed.
Lemma lem4421106 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (p' : Prop) (q' : Prop) : term658 A K s k z x t i p' q'.
Proof. exact (EQ_MP (@lem4421105 A K s k z x t i p' q') (@lem4421104 A K s k z x t i p' q')). Qed.
Lemma lem4421110 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term651 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4421111 (p : Prop) (q : Prop) (p' : Prop) : term652 p q p'.
Proof. exact (fun q' : Prop => @lem4421110 p q p' q'). Qed.
Lemma lem4421112 (p : Prop) (q : Prop) : term653 p q.
Proof. exact (fun p' : Prop => @lem4421111 p q p'). Qed.
Lemma lem4421113 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) : term659 A K s k i x z t.
Proof. exact (@lem4421112 (term643 A K k i x z s) (term643 A K k i x z t)). Qed.
Lemma lem4421114 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (p' : Prop) : term660 A K s k i x z t p'.
Proof. exact (@lem4421113 A K s k i x z t p'). Qed.
Lemma lem4421115 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (p' : Prop) : (term660 A K s k i x z t p') = (term661 A K s k i x z t p').
Proof. exact (eq_refl (term660 A K s k i x z t p')). Qed.
Lemma lem4421116 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (p' : Prop) : term661 A K s k i x z t p'.
Proof. exact (EQ_MP (@lem4421115 A K s k i x z t p') (@lem4421114 A K s k i x z t p')). Qed.
Lemma lem4421117 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (p' : Prop) (q' : Prop) : term662 A K s k i x z t p' q'.
Proof. exact (@lem4421116 A K s k i x z t p' q'). Qed.
Lemma lem4421118 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (p' : Prop) (q' : Prop) : (term662 A K s k i x z t p' q') = (term663 A K s k i x z t p' q').
Proof. exact (eq_refl (term662 A K s k i x z t p' q')). Qed.
Lemma lem4421119 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (p' : Prop) (q' : Prop) : term663 A K s k i x z t p' q'.
Proof. exact (EQ_MP (@lem4421118 A K s k i x z t p' q') (@lem4421117 A K s k i x z t p' q')). Qed.
Lemma lem4421129 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term651 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4421130 (p : Prop) (q : Prop) (p' : Prop) : term652 p q p'.
Proof. exact (fun q' : Prop => @lem4421129 p q p' q'). Qed.
Lemma lem4421131 (p : Prop) (q : Prop) : term653 p q.
Proof. exact (fun p' : Prop => @lem4421130 p q p'). Qed.
Lemma lem4421132 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : term664 A K k i x z x'.
Proof. exact (@lem4421131 (term489 K x' k) ((term619 A K k i x z x') = (@ARB A))). Qed.
Lemma lem4421133 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (p' : Prop) : term665 A K k i x z x' p'.
Proof. exact (@lem4421132 A K k i x z x' p'). Qed.
Lemma lem4421134 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (p' : Prop) : (term665 A K k i x z x' p') = (term666 A K k i x z x' p').
Proof. exact (eq_refl (term665 A K k i x z x' p')). Qed.
Lemma lem4421135 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (p' : Prop) : term666 A K k i x z x' p'.
Proof. exact (EQ_MP (@lem4421134 A K k i x z x' p') (@lem4421133 A K k i x z x' p')). Qed.
Lemma lem4421136 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (p' : Prop) (q' : Prop) : term667 A K k i x z x' p' q'.
Proof. exact (@lem4421135 A K k i x z x' p' q'). Qed.
Lemma lem4421137 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (p' : Prop) (q' : Prop) : (term667 A K k i x z x' p' q') = (term668 A K k i x z x' p' q').
Proof. exact (eq_refl (term667 A K k i x z x' p' q')). Qed.
Lemma lem4421138 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (p' : Prop) (q' : Prop) : term668 A K k i x z x' p' q'.
Proof. exact (EQ_MP (@lem4421137 A K k i x z x' p' q') (@lem4421136 A K k i x z x' p' q')). Qed.
Lemma lem4421139 {K : Type'} (x : K) (k : K -> Prop) : (term489 K x k) = (term489 K x k).
Proof. exact (eq_refl (term489 K x k)). Qed.
Lemma lem4421140 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (q' : Prop) : term669 A K i x z x' k q'.
Proof. exact (@lem4421138 A K k i x z x' (term489 K x' k) q'). Qed.
Lemma lem4421141 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (q' : Prop) : term670 A K i x z x' k q'.
Proof. exact (@lem4421140 A K i x z x' k q' (@lem4421139 K x' k)). Qed.
Lemma lem4421142 {K : Type'} (x : K) (k : K -> Prop) (h1 : term489 K x k) : term489 K x k.
Proof. exact (h1). Qed.
Lemma lem4421143 {K : Type'} (x : K) (k : K -> Prop) : term671 K x k.
Proof. exact (@lem82 (@IN K x k)). Qed.
Lemma lem4421148 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term672 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4421149 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term673 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4421148 _2963 g t e g' t' e'). Qed.
Lemma lem4421150 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term674 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4421149 _2963 g t e g' t'). Qed.
Lemma lem4421151 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term675 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4421150 _2963 g t e g'). Qed.
Lemma lem4421152 {A : Type'} (g : Prop) (t : A) (e : A) : term675 A g t e.
Proof. exact (@lem4421151 A g t e). Qed.
Lemma lem4421153 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : term676 A K k i x z x'.
Proof. exact (@lem4421152 A (@IN K x' k) (term677 A K i x z x') (@ARB A)). Qed.
Lemma lem4421154 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) : term678 A K k i x z x' g'.
Proof. exact (@lem4421153 A K k i x z x' g'). Qed.
Lemma lem4421155 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) : (term678 A K k i x z x' g') = (term679 A K k i x z x' g').
Proof. exact (eq_refl (term678 A K k i x z x' g')). Qed.
Lemma lem4421156 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) : term679 A K k i x z x' g'.
Proof. exact (EQ_MP (@lem4421155 A K k i x z x' g') (@lem4421154 A K k i x z x' g')). Qed.
Lemma lem4421157 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) (t' : A) : term680 A K k i x z x' g' t'.
Proof. exact (@lem4421156 A K k i x z x' g' t'). Qed.
Lemma lem4421158 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) (t' : A) : (term680 A K k i x z x' g' t') = (term681 A K k i x z x' g' t').
Proof. exact (eq_refl (term680 A K k i x z x' g' t')). Qed.
Lemma lem4421159 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) (t' : A) : term681 A K k i x z x' g' t'.
Proof. exact (EQ_MP (@lem4421158 A K k i x z x' g' t') (@lem4421157 A K k i x z x' g' t')). Qed.
Lemma lem4421160 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) (t' : A) (e' : A) : term682 A K k i x z x' g' t' e'.
Proof. exact (@lem4421159 A K k i x z x' g' t' e'). Qed.
Lemma lem4421161 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) (t' : A) (e' : A) : (term682 A K k i x z x' g' t' e') = (term683 A K k i x z x' g' t' e').
Proof. exact (eq_refl (term682 A K k i x z x' g' t' e')). Qed.
Lemma lem4421162 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) (t' : A) (e' : A) : term683 A K k i x z x' g' t' e'.
Proof. exact (EQ_MP (@lem4421161 A K k i x z x' g' t' e') (@lem4421160 A K k i x z x' g' t' e')). Qed.
Lemma lem4421164 {K : Type'} (x : K) (k : K -> Prop) (h1 : term489 K x k) : (@IN K x k) = False.
Proof. exact (@lem4421143 K x k (@lem4421142 K x k h1)). Qed.
Lemma lem4421165 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (t' : A) (e' : A) : term684 A K k i x z x' t' e'.
Proof. exact (@lem4421162 A K k i x z x' False t' e'). Qed.
Lemma lem4421166 {A K : Type'} (i : K) (x : A) (z : K -> A) (t' : A) (e' : A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : term685 A K k i x z x' t' e'.
Proof. exact (@lem4421165 A K k i x z x' t' e' (@lem4421164 K x' k h1)). Qed.
Lemma lem4421220 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) : (term677 A K i x z x') = (term677 A K i x z x').
Proof. exact (eq_refl (term677 A K i x z x')). Qed.
Lemma lem4421221 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) : term686 A K i x z x'.
Proof. exact (fun h0 : False => @lem4421220 A K i x z x'). Qed.
Lemma lem4421222 {A K : Type'} (i : K) (x : A) (z : K -> A) (e' : A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : term687 A K k i x z x' e'.
Proof. exact (@lem4421166 A K i x z (term677 A K i x z x') e' x' k h1). Qed.
Lemma lem4421223 {A K : Type'} (i : K) (x : A) (z : K -> A) (e' : A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : term688 A K k i x z x' e'.
Proof. exact (@lem4421222 A K i x z e' x' k h1 (@lem4421221 A K i x z x')). Qed.
Lemma lem4421229 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4421230 {A : Type'} : term689 A.
Proof. exact (fun h0 : ~ False => @lem4421229 A). Qed.
Lemma lem4421231 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : term690 A K k i x z x'.
Proof. exact (@lem4421223 A K i x z (@ARB A) x' k h1). Qed.
Lemma lem4421232 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : (term619 A K k i x z x') = (term691 A K i x z x').
Proof. exact (@lem4421231 A K i x z x' k h1 (@lem4421230 A)). Qed.
Lemma lem4421234 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4421235 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4421234 A t1 t2). Qed.
Lemma lem4421236 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) : (term691 A K i x z x') = (@ARB A).
Proof. exact (@lem4421235 A (term677 A K i x z x') (@ARB A)). Qed.
Lemma lem4421237 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : (term619 A K k i x z x') = (@ARB A).
Proof. exact (TRANS (@lem4421232 A K i x z x' k h1) (@lem4421236 A K i x z x')). Qed.
Lemma lem4421238 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4421239 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : (term623 A K k i x z x') = (@eq A (@ARB A)).
Proof. exact (MK_COMB (@lem4421238 A) (@lem4421237 A K i x z x' k h1)). Qed.
Lemma lem4421240 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4421241 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : ((term619 A K k i x z x') = (@ARB A)) = ((@ARB A) = (@ARB A)).
Proof. exact (MK_COMB (@lem4421239 A K i x z x' k h1) (@lem4421240 A)). Qed.
Lemma lem4421243 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4421244 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem4421243 A x). Qed.
Lemma lem4421245 {A : Type'} : ((@ARB A) = (@ARB A)) = True.
Proof. exact (@lem4421244 A (@ARB A)). Qed.
Lemma lem4421246 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : ((term619 A K k i x z x') = (@ARB A)) = True.
Proof. exact (TRANS (@lem4421241 A K i x z x' k h1) (@lem4421245 A)). Qed.
Lemma lem4421247 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : term692 A K k i x z x'.
Proof. exact (fun h0 : term489 K x' k => @lem4421246 A K i x z x' k h0). Qed.
Lemma lem4421248 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) : term693 A K i x z x' k.
Proof. exact (@lem4421141 A K i x z x' k True). Qed.
Lemma lem4421249 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) : (term626 A K k i x z x') = (term694 K x' k).
Proof. exact (@lem4421248 A K i x z x' k (@lem4421247 A K k i x z x')). Qed.
Lemma lem4421251 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4421252 {K : Type'} (x : K) (k : K -> Prop) : (term694 K x k) = True.
Proof. exact (@lem4421251 (term489 K x k)). Qed.
Lemma lem4421253 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term626 A K k i x z x') = True.
Proof. exact (TRANS (@lem4421249 A K i x z x' k) (@lem4421252 K x' k)). Qed.
Lemma lem4421254 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term628 A K k i x z) = (term695 K).
Proof. exact (fun_ext (fun x' : K => @lem4421253 A K k i x z x')). Qed.
Lemma lem4421255 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4421256 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term629 A K k i x z) = (term696 K).
Proof. exact (MK_COMB (@lem4421255 K) (@lem4421254 A K k i x z)). Qed.
Lemma lem4421258 {A : Type'} (t : Prop) : (term144 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4421259 {K : Type'} (t : Prop) : (term144 K t) = t.
Proof. exact (@lem4421258 K t). Qed.
Lemma lem4421260 {K : Type'} : (term696 K) = True.
Proof. exact (@lem4421259 K True). Qed.
Lemma lem4421261 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term629 A K k i x z) = True.
Proof. exact (TRANS (@lem4421256 A K k i x z) (@lem4421260 K)). Qed.
Lemma lem4421262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4421263 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term631 A K k i x z) = (and True).
Proof. exact (MK_COMB (@lem4421262) (@lem4421261 A K k i x z)). Qed.
Lemma lem4421271 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term651 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4421272 (p : Prop) (q : Prop) (p' : Prop) : term652 p q p'.
Proof. exact (fun q' : Prop => @lem4421271 p q p' q'). Qed.
Lemma lem4421273 (p : Prop) (q : Prop) : term653 p q.
Proof. exact (fun p' : Prop => @lem4421272 p q p'). Qed.
Lemma lem4421274 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) (i' : K) : term697 A K k i x z s i'.
Proof. exact (@lem4421273 (@IN K i' k) (term635 A K k i x z s i')). Qed.
Lemma lem4421275 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) (i' : K) (p' : Prop) : term698 A K k i x z s i' p'.
Proof. exact (@lem4421274 A K k i x z s i' p'). Qed.
Lemma lem4421276 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) (i' : K) (p' : Prop) : (term698 A K k i x z s i' p') = (term699 A K k i x z s i' p').
Proof. exact (eq_refl (term698 A K k i x z s i' p')). Qed.
Lemma lem4421277 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) (i' : K) (p' : Prop) : term699 A K k i x z s i' p'.
Proof. exact (EQ_MP (@lem4421276 A K k i x z s i' p') (@lem4421275 A K k i x z s i' p')). Qed.
Lemma lem4421278 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) (i' : K) (p' : Prop) (q' : Prop) : term700 A K k i x z s i' p' q'.
Proof. exact (@lem4421277 A K k i x z s i' p' q'). Qed.
Lemma lem4421279 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) (i' : K) (p' : Prop) (q' : Prop) : (term700 A K k i x z s i' p' q') = (term701 A K k i x z s i' p' q').
Proof. exact (eq_refl (term700 A K k i x z s i' p' q')). Qed.
Lemma lem4421280 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) (i' : K) (p' : Prop) (q' : Prop) : term701 A K k i x z s i' p' q'.
Proof. exact (EQ_MP (@lem4421279 A K k i x z s i' p' q') (@lem4421278 A K k i x z s i' p' q')). Qed.
Lemma lem4421281 {K : Type'} (i' : K) (k : K -> Prop) : (@IN K i' k) = (@IN K i' k).
Proof. exact (eq_refl (@IN K i' k)). Qed.
Lemma lem4421282 {A K : Type'} (i : K) (x : A) (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (q' : Prop) : term702 A K i x z s i' k q'.
Proof. exact (@lem4421280 A K k i x z s i' (@IN K i' k) q'). Qed.
Lemma lem4421283 {A K : Type'} (i : K) (x : A) (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (q' : Prop) : term703 A K i x z s i' k q'.
Proof. exact (@lem4421282 A K i x z s i' k q' (@lem4421281 K i' k)). Qed.
Lemma lem4421284 {K : Type'} (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : @IN K i' k.
Proof. exact (h1). Qed.
Lemma lem4421285 {K : Type'} (i' : K) (k : K -> Prop) : (@IN K i' k) = ((@IN K i' k) = True).
Proof. exact (@lem7 (@IN K i' k)). Qed.
Lemma lem4421288 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term672 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4421289 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term673 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4421288 _2963 g t e g' t' e'). Qed.
Lemma lem4421290 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term674 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4421289 _2963 g t e g' t'). Qed.
Lemma lem4421291 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term675 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4421290 _2963 g t e g'). Qed.
Lemma lem4421292 {A : Type'} (g : Prop) (t : A) (e : A) : term675 A g t e.
Proof. exact (@lem4421291 A g t e). Qed.
Lemma lem4421293 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : term676 A K k i x z i'.
Proof. exact (@lem4421292 A (@IN K i' k) (term677 A K i x z i') (@ARB A)). Qed.
Lemma lem4421294 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) : term678 A K k i x z i' g'.
Proof. exact (@lem4421293 A K k i x z i' g'). Qed.
Lemma lem4421295 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) : (term678 A K k i x z i' g') = (term679 A K k i x z i' g').
Proof. exact (eq_refl (term678 A K k i x z i' g')). Qed.
Lemma lem4421296 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) : term679 A K k i x z i' g'.
Proof. exact (EQ_MP (@lem4421295 A K k i x z i' g') (@lem4421294 A K k i x z i' g')). Qed.
Lemma lem4421297 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) (t' : A) : term680 A K k i x z i' g' t'.
Proof. exact (@lem4421296 A K k i x z i' g' t'). Qed.
Lemma lem4421298 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) (t' : A) : (term680 A K k i x z i' g' t') = (term681 A K k i x z i' g' t').
Proof. exact (eq_refl (term680 A K k i x z i' g' t')). Qed.
Lemma lem4421299 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) (t' : A) : term681 A K k i x z i' g' t'.
Proof. exact (EQ_MP (@lem4421298 A K k i x z i' g' t') (@lem4421297 A K k i x z i' g' t')). Qed.
Lemma lem4421300 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) (t' : A) (e' : A) : term682 A K k i x z i' g' t' e'.
Proof. exact (@lem4421299 A K k i x z i' g' t' e'). Qed.
Lemma lem4421301 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) (t' : A) (e' : A) : (term682 A K k i x z i' g' t' e') = (term683 A K k i x z i' g' t' e').
Proof. exact (eq_refl (term682 A K k i x z i' g' t' e')). Qed.
Lemma lem4421302 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) (t' : A) (e' : A) : term683 A K k i x z i' g' t' e'.
Proof. exact (EQ_MP (@lem4421301 A K k i x z i' g' t' e') (@lem4421300 A K k i x z i' g' t' e')). Qed.
Lemma lem4421304 {K : Type'} (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : (@IN K i' k) = True.
Proof. exact (EQ_MP (@lem4421285 K i' k) (@lem4421284 K i' k h1)). Qed.
Lemma lem4421305 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (t' : A) (e' : A) : term704 A K k i x z i' t' e'.
Proof. exact (@lem4421302 A K k i x z i' True t' e'). Qed.
Lemma lem4421306 {A K : Type'} (i : K) (x : A) (z : K -> A) (t' : A) (e' : A) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : term705 A K k i x z i' t' e'.
Proof. exact (@lem4421305 A K k i x z i' t' e' (@lem4421304 K i' k h1)). Qed.
Lemma lem4421360 {A K : Type'} (i : K) (x : A) (z : K -> A) (i' : K) : (term677 A K i x z i') = (term677 A K i x z i').
Proof. exact (eq_refl (term677 A K i x z i')). Qed.
Lemma lem4421361 {A K : Type'} (i : K) (x : A) (z : K -> A) (i' : K) : term706 A K i x z i'.
Proof. exact (fun h0 : True => @lem4421360 A K i x z i'). Qed.
Lemma lem4421362 {A K : Type'} (i : K) (x : A) (z : K -> A) (e' : A) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : term707 A K k i x z i' e'.
Proof. exact (@lem4421306 A K i x z (term677 A K i x z i') e' i' k h1). Qed.
Lemma lem4421363 {A K : Type'} (i : K) (x : A) (z : K -> A) (e' : A) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : term708 A K k i x z i' e'.
Proof. exact (@lem4421362 A K i x z e' i' k h1 (@lem4421361 A K i x z i')). Qed.
Lemma lem4421367 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4421368 {A : Type'} : term709 A.
Proof. exact (fun h0 : ~ True => @lem4421367 A). Qed.
Lemma lem4421369 {A K : Type'} (i : K) (x : A) (z : K -> A) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : term710 A K k i x z i'.
Proof. exact (@lem4421363 A K i x z (@ARB A) i' k h1). Qed.
Lemma lem4421370 {A K : Type'} (i : K) (x : A) (z : K -> A) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : (term619 A K k i x z i') = (term711 A K i x z i').
Proof. exact (@lem4421369 A K i x z i' k h1 (@lem4421368 A)). Qed.
Lemma lem4421372 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4421373 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4421372 A t2 t1). Qed.
Lemma lem4421374 {A K : Type'} (i : K) (x : A) (z : K -> A) (i' : K) : (term711 A K i x z i') = (term677 A K i x z i').
Proof. exact (@lem4421373 A (@ARB A) (term677 A K i x z i')). Qed.
Lemma lem4421423 {A K : Type'} (i : K) (x : A) (z : K -> A) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : (term619 A K k i x z i') = (term677 A K i x z i').
Proof. exact (TRANS (@lem4421370 A K i x z i' k h1) (@lem4421374 A K i x z i')). Qed.
Lemma lem4421424 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4421425 {A K : Type'} (i : K) (x : A) (z : K -> A) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : (term633 A K k i x z i') = (term712 A K i x z i').
Proof. exact (MK_COMB (@lem4421424 A) (@lem4421423 A K i x z i' k h1)). Qed.
Lemma lem4421474 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4421475 {A K : Type'} (i : K) (x : A) (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : (term635 A K k i x z s i') = (term713 A K i x z s i').
Proof. exact (MK_COMB (@lem4421425 A K i x z i' k h1) (@lem4421474 A K s i')). Qed.
Lemma lem4421524 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) (i' : K) : term714 A K k i x z s i'.
Proof. exact (fun h0 : @IN K i' k => @lem4421475 A K i x z s i' k h0). Qed.
Lemma lem4421525 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) (i' : K) : term715 A K k i x z s i'.
Proof. exact (@lem4421283 A K i x z s i' k (term713 A K i x z s i')). Qed.
Lemma lem4421526 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) (i' : K) : (term637 A K k i x z s i') = (term716 A K k i x z s i').
Proof. exact (@lem4421525 A K k i x z s i' (@lem4421524 A K k i x z s i')). Qed.
Lemma lem4421646 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) : (term639 A K k i x z s) = (term717 A K k i x z s).
Proof. exact (fun_ext (fun i' : K => @lem4421526 A K k i x z s i')). Qed.
Lemma lem4421766 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4421767 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) : (term641 A K k i x z s) = (term718 A K k i x z s).
Proof. exact (MK_COMB (@lem4421766 K) (@lem4421646 A K k i x z s)). Qed.
Lemma lem4421891 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) : (term643 A K k i x z s) = (term719 A K k i x z s).
Proof. exact (MK_COMB (@lem4421263 A K k i x z) (@lem4421767 A K k i x z s)). Qed.
Lemma lem4421893 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4421894 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) : (term719 A K k i x z s) = (term718 A K k i x z s).
Proof. exact (@lem4421893 (term718 A K k i x z s)). Qed.
Lemma lem4422018 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) : (term643 A K k i x z s) = (term718 A K k i x z s).
Proof. exact (TRANS (@lem4421891 A K k i x z s) (@lem4421894 A K k i x z s)). Qed.
Lemma lem4422019 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) (q' : Prop) : term720 A K t k i x z s q'.
Proof. exact (@lem4421119 A K s k i x z t (term718 A K k i x z s) q'). Qed.
Lemma lem4422020 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (s : type1470 A K) (q' : Prop) : term721 A K t k i x z s q'.
Proof. exact (@lem4422019 A K t k i x z s q' (@lem4422018 A K k i x z s)). Qed.
Lemma lem4422043 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term651 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4422044 (p : Prop) (q : Prop) (p' : Prop) : term652 p q p'.
Proof. exact (fun q' : Prop => @lem4422043 p q p' q'). Qed.
Lemma lem4422045 (p : Prop) (q : Prop) : term653 p q.
Proof. exact (fun p' : Prop => @lem4422044 p q p'). Qed.
Lemma lem4422046 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : term664 A K k i x z x'.
Proof. exact (@lem4422045 (term489 K x' k) ((term619 A K k i x z x') = (@ARB A))). Qed.
Lemma lem4422047 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (p' : Prop) : term665 A K k i x z x' p'.
Proof. exact (@lem4422046 A K k i x z x' p'). Qed.
Lemma lem4422048 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (p' : Prop) : (term665 A K k i x z x' p') = (term666 A K k i x z x' p').
Proof. exact (eq_refl (term665 A K k i x z x' p')). Qed.
Lemma lem4422049 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (p' : Prop) : term666 A K k i x z x' p'.
Proof. exact (EQ_MP (@lem4422048 A K k i x z x' p') (@lem4422047 A K k i x z x' p')). Qed.
Lemma lem4422050 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (p' : Prop) (q' : Prop) : term667 A K k i x z x' p' q'.
Proof. exact (@lem4422049 A K k i x z x' p' q'). Qed.
Lemma lem4422051 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (p' : Prop) (q' : Prop) : (term667 A K k i x z x' p' q') = (term668 A K k i x z x' p' q').
Proof. exact (eq_refl (term667 A K k i x z x' p' q')). Qed.
Lemma lem4422052 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (p' : Prop) (q' : Prop) : term668 A K k i x z x' p' q'.
Proof. exact (EQ_MP (@lem4422051 A K k i x z x' p' q') (@lem4422050 A K k i x z x' p' q')). Qed.
Lemma lem4422053 {K : Type'} (x : K) (k : K -> Prop) : (term489 K x k) = (term489 K x k).
Proof. exact (eq_refl (term489 K x k)). Qed.
Lemma lem4422054 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (q' : Prop) : term669 A K i x z x' k q'.
Proof. exact (@lem4422052 A K k i x z x' (term489 K x' k) q'). Qed.
Lemma lem4422055 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (q' : Prop) : term670 A K i x z x' k q'.
Proof. exact (@lem4422054 A K i x z x' k q' (@lem4422053 K x' k)). Qed.
Lemma lem4422056 {K : Type'} (x : K) (k : K -> Prop) (h1 : term489 K x k) : term489 K x k.
Proof. exact (h1). Qed.
Lemma lem4422057 {K : Type'} (x : K) (k : K -> Prop) : term671 K x k.
Proof. exact (@lem82 (@IN K x k)). Qed.
Lemma lem4422062 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term672 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4422063 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term673 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4422062 _2963 g t e g' t' e'). Qed.
Lemma lem4422064 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term674 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4422063 _2963 g t e g' t'). Qed.
Lemma lem4422065 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term675 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4422064 _2963 g t e g'). Qed.
Lemma lem4422066 {A : Type'} (g : Prop) (t : A) (e : A) : term675 A g t e.
Proof. exact (@lem4422065 A g t e). Qed.
Lemma lem4422067 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : term676 A K k i x z x'.
Proof. exact (@lem4422066 A (@IN K x' k) (term677 A K i x z x') (@ARB A)). Qed.
Lemma lem4422068 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) : term678 A K k i x z x' g'.
Proof. exact (@lem4422067 A K k i x z x' g'). Qed.
Lemma lem4422069 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) : (term678 A K k i x z x' g') = (term679 A K k i x z x' g').
Proof. exact (eq_refl (term678 A K k i x z x' g')). Qed.
Lemma lem4422070 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) : term679 A K k i x z x' g'.
Proof. exact (EQ_MP (@lem4422069 A K k i x z x' g') (@lem4422068 A K k i x z x' g')). Qed.
Lemma lem4422071 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) (t' : A) : term680 A K k i x z x' g' t'.
Proof. exact (@lem4422070 A K k i x z x' g' t'). Qed.
Lemma lem4422072 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) (t' : A) : (term680 A K k i x z x' g' t') = (term681 A K k i x z x' g' t').
Proof. exact (eq_refl (term680 A K k i x z x' g' t')). Qed.
Lemma lem4422073 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) (t' : A) : term681 A K k i x z x' g' t'.
Proof. exact (EQ_MP (@lem4422072 A K k i x z x' g' t') (@lem4422071 A K k i x z x' g' t')). Qed.
Lemma lem4422074 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) (t' : A) (e' : A) : term682 A K k i x z x' g' t' e'.
Proof. exact (@lem4422073 A K k i x z x' g' t' e'). Qed.
Lemma lem4422075 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) (t' : A) (e' : A) : (term682 A K k i x z x' g' t' e') = (term683 A K k i x z x' g' t' e').
Proof. exact (eq_refl (term682 A K k i x z x' g' t' e')). Qed.
Lemma lem4422076 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (g' : Prop) (t' : A) (e' : A) : term683 A K k i x z x' g' t' e'.
Proof. exact (EQ_MP (@lem4422075 A K k i x z x' g' t' e') (@lem4422074 A K k i x z x' g' t' e')). Qed.
Lemma lem4422078 {K : Type'} (x : K) (k : K -> Prop) (h1 : term489 K x k) : (@IN K x k) = False.
Proof. exact (@lem4422057 K x k (@lem4422056 K x k h1)). Qed.
Lemma lem4422079 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) (t' : A) (e' : A) : term684 A K k i x z x' t' e'.
Proof. exact (@lem4422076 A K k i x z x' False t' e'). Qed.
Lemma lem4422080 {A K : Type'} (i : K) (x : A) (z : K -> A) (t' : A) (e' : A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : term685 A K k i x z x' t' e'.
Proof. exact (@lem4422079 A K k i x z x' t' e' (@lem4422078 K x' k h1)). Qed.
Lemma lem4422134 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) : (term677 A K i x z x') = (term677 A K i x z x').
Proof. exact (eq_refl (term677 A K i x z x')). Qed.
Lemma lem4422135 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) : term686 A K i x z x'.
Proof. exact (fun h0 : False => @lem4422134 A K i x z x'). Qed.
Lemma lem4422136 {A K : Type'} (i : K) (x : A) (z : K -> A) (e' : A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : term687 A K k i x z x' e'.
Proof. exact (@lem4422080 A K i x z (term677 A K i x z x') e' x' k h1). Qed.
Lemma lem4422137 {A K : Type'} (i : K) (x : A) (z : K -> A) (e' : A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : term688 A K k i x z x' e'.
Proof. exact (@lem4422136 A K i x z e' x' k h1 (@lem4422135 A K i x z x')). Qed.
Lemma lem4422143 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4422144 {A : Type'} : term689 A.
Proof. exact (fun h0 : ~ False => @lem4422143 A). Qed.
Lemma lem4422145 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : term690 A K k i x z x'.
Proof. exact (@lem4422137 A K i x z (@ARB A) x' k h1). Qed.
Lemma lem4422146 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : (term619 A K k i x z x') = (term691 A K i x z x').
Proof. exact (@lem4422145 A K i x z x' k h1 (@lem4422144 A)). Qed.
Lemma lem4422148 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4422149 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4422148 A t1 t2). Qed.
Lemma lem4422150 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) : (term691 A K i x z x') = (@ARB A).
Proof. exact (@lem4422149 A (term677 A K i x z x') (@ARB A)). Qed.
Lemma lem4422151 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : (term619 A K k i x z x') = (@ARB A).
Proof. exact (TRANS (@lem4422146 A K i x z x' k h1) (@lem4422150 A K i x z x')). Qed.
Lemma lem4422152 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4422153 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : (term623 A K k i x z x') = (@eq A (@ARB A)).
Proof. exact (MK_COMB (@lem4422152 A) (@lem4422151 A K i x z x' k h1)). Qed.
Lemma lem4422154 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4422155 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : ((term619 A K k i x z x') = (@ARB A)) = ((@ARB A) = (@ARB A)).
Proof. exact (MK_COMB (@lem4422153 A K i x z x' k h1) (@lem4422154 A)). Qed.
Lemma lem4422157 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4422158 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem4422157 A x). Qed.
Lemma lem4422159 {A : Type'} : ((@ARB A) = (@ARB A)) = True.
Proof. exact (@lem4422158 A (@ARB A)). Qed.
Lemma lem4422160 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) (h1 : term489 K x' k) : ((term619 A K k i x z x') = (@ARB A)) = True.
Proof. exact (TRANS (@lem4422155 A K i x z x' k h1) (@lem4422159 A)). Qed.
Lemma lem4422161 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : term692 A K k i x z x'.
Proof. exact (fun h0 : term489 K x' k => @lem4422160 A K i x z x' k h0). Qed.
Lemma lem4422162 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) : term693 A K i x z x' k.
Proof. exact (@lem4422055 A K i x z x' k True). Qed.
Lemma lem4422163 {A K : Type'} (i : K) (x : A) (z : K -> A) (x' : K) (k : K -> Prop) : (term626 A K k i x z x') = (term694 K x' k).
Proof. exact (@lem4422162 A K i x z x' k (@lem4422161 A K k i x z x')). Qed.
Lemma lem4422165 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4422166 {K : Type'} (x : K) (k : K -> Prop) : (term694 K x k) = True.
Proof. exact (@lem4422165 (term489 K x k)). Qed.
Lemma lem4422167 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (x' : K) : (term626 A K k i x z x') = True.
Proof. exact (TRANS (@lem4422163 A K i x z x' k) (@lem4422166 K x' k)). Qed.
Lemma lem4422168 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term628 A K k i x z) = (term695 K).
Proof. exact (fun_ext (fun x' : K => @lem4422167 A K k i x z x')). Qed.
Lemma lem4422169 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4422170 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term629 A K k i x z) = (term696 K).
Proof. exact (MK_COMB (@lem4422169 K) (@lem4422168 A K k i x z)). Qed.
Lemma lem4422172 {A : Type'} (t : Prop) : (term144 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4422173 {K : Type'} (t : Prop) : (term144 K t) = t.
Proof. exact (@lem4422172 K t). Qed.
Lemma lem4422174 {K : Type'} : (term696 K) = True.
Proof. exact (@lem4422173 K True). Qed.
Lemma lem4422175 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term629 A K k i x z) = True.
Proof. exact (TRANS (@lem4422170 A K k i x z) (@lem4422174 K)). Qed.
Lemma lem4422176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4422177 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) : (term631 A K k i x z) = (and True).
Proof. exact (MK_COMB (@lem4422176) (@lem4422175 A K k i x z)). Qed.
Lemma lem4422185 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term651 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4422186 (p : Prop) (q : Prop) (p' : Prop) : term652 p q p'.
Proof. exact (fun q' : Prop => @lem4422185 p q p' q'). Qed.
Lemma lem4422187 (p : Prop) (q : Prop) : term653 p q.
Proof. exact (fun p' : Prop => @lem4422186 p q p'). Qed.
Lemma lem4422188 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (i' : K) : term697 A K k i x z t i'.
Proof. exact (@lem4422187 (@IN K i' k) (term635 A K k i x z t i')). Qed.
Lemma lem4422189 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (i' : K) (p' : Prop) : term698 A K k i x z t i' p'.
Proof. exact (@lem4422188 A K k i x z t i' p'). Qed.
Lemma lem4422190 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (i' : K) (p' : Prop) : (term698 A K k i x z t i' p') = (term699 A K k i x z t i' p').
Proof. exact (eq_refl (term698 A K k i x z t i' p')). Qed.
Lemma lem4422191 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (i' : K) (p' : Prop) : term699 A K k i x z t i' p'.
Proof. exact (EQ_MP (@lem4422190 A K k i x z t i' p') (@lem4422189 A K k i x z t i' p')). Qed.
Lemma lem4422192 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (i' : K) (p' : Prop) (q' : Prop) : term700 A K k i x z t i' p' q'.
Proof. exact (@lem4422191 A K k i x z t i' p' q'). Qed.
Lemma lem4422193 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (i' : K) (p' : Prop) (q' : Prop) : (term700 A K k i x z t i' p' q') = (term701 A K k i x z t i' p' q').
Proof. exact (eq_refl (term700 A K k i x z t i' p' q')). Qed.
Lemma lem4422194 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (i' : K) (p' : Prop) (q' : Prop) : term701 A K k i x z t i' p' q'.
Proof. exact (EQ_MP (@lem4422193 A K k i x z t i' p' q') (@lem4422192 A K k i x z t i' p' q')). Qed.
Lemma lem4422195 {K : Type'} (i' : K) (k : K -> Prop) : (@IN K i' k) = (@IN K i' k).
Proof. exact (eq_refl (@IN K i' k)). Qed.
Lemma lem4422196 {A K : Type'} (i : K) (x : A) (z : K -> A) (t : type1470 A K) (i' : K) (k : K -> Prop) (q' : Prop) : term702 A K i x z t i' k q'.
Proof. exact (@lem4422194 A K k i x z t i' (@IN K i' k) q'). Qed.
Lemma lem4422197 {A K : Type'} (i : K) (x : A) (z : K -> A) (t : type1470 A K) (i' : K) (k : K -> Prop) (q' : Prop) : term703 A K i x z t i' k q'.
Proof. exact (@lem4422196 A K i x z t i' k q' (@lem4422195 K i' k)). Qed.
Lemma lem4422198 {K : Type'} (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : @IN K i' k.
Proof. exact (h1). Qed.
Lemma lem4422199 {K : Type'} (i' : K) (k : K -> Prop) : (@IN K i' k) = ((@IN K i' k) = True).
Proof. exact (@lem7 (@IN K i' k)). Qed.
Lemma lem4422202 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term672 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4422203 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term673 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4422202 _2963 g t e g' t' e'). Qed.
Lemma lem4422204 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term674 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4422203 _2963 g t e g' t'). Qed.
Lemma lem4422205 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term675 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4422204 _2963 g t e g'). Qed.
Lemma lem4422206 {A : Type'} (g : Prop) (t : A) (e : A) : term675 A g t e.
Proof. exact (@lem4422205 A g t e). Qed.
Lemma lem4422207 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) : term676 A K k i x z i'.
Proof. exact (@lem4422206 A (@IN K i' k) (term677 A K i x z i') (@ARB A)). Qed.
Lemma lem4422208 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) : term678 A K k i x z i' g'.
Proof. exact (@lem4422207 A K k i x z i' g'). Qed.
Lemma lem4422209 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) : (term678 A K k i x z i' g') = (term679 A K k i x z i' g').
Proof. exact (eq_refl (term678 A K k i x z i' g')). Qed.
Lemma lem4422210 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) : term679 A K k i x z i' g'.
Proof. exact (EQ_MP (@lem4422209 A K k i x z i' g') (@lem4422208 A K k i x z i' g')). Qed.
Lemma lem4422211 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) (t' : A) : term680 A K k i x z i' g' t'.
Proof. exact (@lem4422210 A K k i x z i' g' t'). Qed.
Lemma lem4422212 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) (t' : A) : (term680 A K k i x z i' g' t') = (term681 A K k i x z i' g' t').
Proof. exact (eq_refl (term680 A K k i x z i' g' t')). Qed.
Lemma lem4422213 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) (t' : A) : term681 A K k i x z i' g' t'.
Proof. exact (EQ_MP (@lem4422212 A K k i x z i' g' t') (@lem4422211 A K k i x z i' g' t')). Qed.
Lemma lem4422214 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) (t' : A) (e' : A) : term682 A K k i x z i' g' t' e'.
Proof. exact (@lem4422213 A K k i x z i' g' t' e'). Qed.
Lemma lem4422215 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) (t' : A) (e' : A) : (term682 A K k i x z i' g' t' e') = (term683 A K k i x z i' g' t' e').
Proof. exact (eq_refl (term682 A K k i x z i' g' t' e')). Qed.
Lemma lem4422216 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (g' : Prop) (t' : A) (e' : A) : term683 A K k i x z i' g' t' e'.
Proof. exact (EQ_MP (@lem4422215 A K k i x z i' g' t' e') (@lem4422214 A K k i x z i' g' t' e')). Qed.
Lemma lem4422218 {K : Type'} (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : (@IN K i' k) = True.
Proof. exact (EQ_MP (@lem4422199 K i' k) (@lem4422198 K i' k h1)). Qed.
Lemma lem4422219 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (i' : K) (t' : A) (e' : A) : term704 A K k i x z i' t' e'.
Proof. exact (@lem4422216 A K k i x z i' True t' e'). Qed.
Lemma lem4422220 {A K : Type'} (i : K) (x : A) (z : K -> A) (t' : A) (e' : A) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : term705 A K k i x z i' t' e'.
Proof. exact (@lem4422219 A K k i x z i' t' e' (@lem4422218 K i' k h1)). Qed.
Lemma lem4422274 {A K : Type'} (i : K) (x : A) (z : K -> A) (i' : K) : (term677 A K i x z i') = (term677 A K i x z i').
Proof. exact (eq_refl (term677 A K i x z i')). Qed.
Lemma lem4422275 {A K : Type'} (i : K) (x : A) (z : K -> A) (i' : K) : term706 A K i x z i'.
Proof. exact (fun h0 : True => @lem4422274 A K i x z i'). Qed.
Lemma lem4422276 {A K : Type'} (i : K) (x : A) (z : K -> A) (e' : A) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : term707 A K k i x z i' e'.
Proof. exact (@lem4422220 A K i x z (term677 A K i x z i') e' i' k h1). Qed.
Lemma lem4422277 {A K : Type'} (i : K) (x : A) (z : K -> A) (e' : A) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : term708 A K k i x z i' e'.
Proof. exact (@lem4422276 A K i x z e' i' k h1 (@lem4422275 A K i x z i')). Qed.
Lemma lem4422281 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4422282 {A : Type'} : term709 A.
Proof. exact (fun h0 : ~ True => @lem4422281 A). Qed.
Lemma lem4422283 {A K : Type'} (i : K) (x : A) (z : K -> A) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : term710 A K k i x z i'.
Proof. exact (@lem4422277 A K i x z (@ARB A) i' k h1). Qed.
Lemma lem4422284 {A K : Type'} (i : K) (x : A) (z : K -> A) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : (term619 A K k i x z i') = (term711 A K i x z i').
Proof. exact (@lem4422283 A K i x z i' k h1 (@lem4422282 A)). Qed.
Lemma lem4422286 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4422287 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4422286 A t2 t1). Qed.
Lemma lem4422288 {A K : Type'} (i : K) (x : A) (z : K -> A) (i' : K) : (term711 A K i x z i') = (term677 A K i x z i').
Proof. exact (@lem4422287 A (@ARB A) (term677 A K i x z i')). Qed.
Lemma lem4422337 {A K : Type'} (i : K) (x : A) (z : K -> A) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : (term619 A K k i x z i') = (term677 A K i x z i').
Proof. exact (TRANS (@lem4422284 A K i x z i' k h1) (@lem4422288 A K i x z i')). Qed.
Lemma lem4422338 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4422339 {A K : Type'} (i : K) (x : A) (z : K -> A) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : (term633 A K k i x z i') = (term712 A K i x z i').
Proof. exact (MK_COMB (@lem4422338 A) (@lem4422337 A K i x z i' k h1)). Qed.
Lemma lem4422388 {A K : Type'} (t : type1470 A K) (i' : K) : (t i') = (t i').
Proof. exact (eq_refl (t i')). Qed.
Lemma lem4422389 {A K : Type'} (i : K) (x : A) (z : K -> A) (t : type1470 A K) (i' : K) (k : K -> Prop) (h1 : @IN K i' k) : (term635 A K k i x z t i') = (term713 A K i x z t i').
Proof. exact (MK_COMB (@lem4422339 A K i x z i' k h1) (@lem4422388 A K t i')). Qed.
Lemma lem4422438 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (i' : K) : term714 A K k i x z t i'.
Proof. exact (fun h0 : @IN K i' k => @lem4422389 A K i x z t i' k h0). Qed.
Lemma lem4422439 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (i' : K) : term715 A K k i x z t i'.
Proof. exact (@lem4422197 A K i x z t i' k (term713 A K i x z t i')). Qed.
Lemma lem4422440 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (i' : K) : (term637 A K k i x z t i') = (term716 A K k i x z t i').
Proof. exact (@lem4422439 A K k i x z t i' (@lem4422438 A K k i x z t i')). Qed.
Lemma lem4422560 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) : (term639 A K k i x z t) = (term717 A K k i x z t).
Proof. exact (fun_ext (fun i' : K => @lem4422440 A K k i x z t i')). Qed.
Lemma lem4422680 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4422681 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) : (term641 A K k i x z t) = (term718 A K k i x z t).
Proof. exact (MK_COMB (@lem4422680 K) (@lem4422560 A K k i x z t)). Qed.
Lemma lem4422805 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) : (term643 A K k i x z t) = (term719 A K k i x z t).
Proof. exact (MK_COMB (@lem4422177 A K k i x z) (@lem4422681 A K k i x z t)). Qed.
Lemma lem4422807 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4422808 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) : (term719 A K k i x z t) = (term718 A K k i x z t).
Proof. exact (@lem4422807 (term718 A K k i x z t)). Qed.
Lemma lem4422932 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) : (term643 A K k i x z t) = (term718 A K k i x z t).
Proof. exact (TRANS (@lem4422805 A K k i x z t) (@lem4422808 A K k i x z t)). Qed.
Lemma lem4422933 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) : term722 A K s k i x z t.
Proof. exact (fun h0 : term718 A K k i x z s => @lem4422932 A K k i x z t). Qed.
Lemma lem4422934 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) : term723 A K s k i x z t.
Proof. exact (@lem4422020 A K t k i x z s (term718 A K k i x z t)). Qed.
Lemma lem4422935 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) : (term646 A K s k i x z t) = (term724 A K s k i x z t).
Proof. exact (@lem4422934 A K s k i x z t (@lem4422933 A K s k i x z t)). Qed.
Lemma lem4423461 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (q' : Prop) : term725 A K s k i x z t q'.
Proof. exact (@lem4421106 A K s k z x t i (term724 A K s k i x z t) q'). Qed.
Lemma lem4423462 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (i : K) (x : A) (z : K -> A) (t : type1470 A K) (q' : Prop) : term726 A K s k i x z t q'.
Proof. exact (@lem4423461 A K s k i x z t q' (@lem4422935 A K s k i x z t)). Qed.
Lemma lem4423483 {A K : Type'} (x : A) (t : type1470 A K) (i : K) : (term30 A K x t i) = (term30 A K x t i).
Proof. exact (eq_refl (term30 A K x t i)). Qed.
Lemma lem4423484 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : term727 A K s k z x t i.
Proof. exact (fun h0 : term724 A K s k i x z t => @lem4423483 A K x t i). Qed.
Lemma lem4423485 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : term728 A K s k z x t i.
Proof. exact (@lem4423462 A K s k i x z t (term30 A K x t i)). Qed.
Lemma lem4423486 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term650 A K s k z x t i) = (term729 A K s k z x t i).
Proof. exact (@lem4423485 A K s k z x t i (@lem4423484 A K s k z x t i)). Qed.
Lemma lem4424577 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term729 A K s k z x t i) = (term650 A K s k z x t i).
Proof. exact (SYM (@lem4423486 A K s k z x t i)). Qed.
Lemma lem4424579 (p : Prop) : p = (term53 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4424580 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term729 A K s k z x t i) = (term730 A K s k z x t i).
Proof. exact (@lem4424579 (term729 A K s k z x t i)). Qed.
Lemma lem4424581 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term730 A K s k z x t i) = (term729 A K s k z x t i).
Proof. exact (SYM (@lem4424580 A K s k z x t i)). Qed.
Lemma lem4424582 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (h1 : term731 A K s k z x t i) : term731 A K s k z x t i.
Proof. exact (h1). Qed.
Lemma lem4424585 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (h1 : term732 A K s k z x t i) : term732 A K s k z x t i.
Proof. exact (h1). Qed.
Lemma lem4424586 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : term733 A K s k z x t i.
Proof. exact (fun h0 : term732 A K s k z x t i => @lem4424585 A K s k z x t i h0). Qed.
Lemma lem4424587 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (h1 : term733 A K s k z x t i) : term733 A K s k z x t i.
Proof. exact (h1). Qed.
Lemma lem4424588 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (h1 : term732 A K s k z x t i) : term732 A K s k z x t i.
Proof. exact (h1). Qed.
Lemma lem4424589 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (h1 : term732 A K s k z x t i) (h2 : term733 A K s k z x t i) : term732 A K s k z x t i.
Proof. exact (@lem4424587 A K s k z x t i h2 (@lem4424588 A K s k z x t i h1)). Qed.
Lemma lem4424590 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (h1 : term732 A K s k z x t i) : term734 A K s k z x t i.
Proof. exact (fun h0 : term733 A K s k z x t i => @lem4424589 A K s k z x t i h1 h0). Qed.
Lemma lem4424591 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (h1 : term733 A K s k z x t i) : term733 A K s k z x t i.
Proof. exact (h1). Qed.
Lemma lem4424592 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (h1 : term732 A K s k z x t i) (h2 : term733 A K s k z x t i) : term732 A K s k z x t i.
Proof. exact (@lem4424590 A K s k z x t i h1 (@lem4424591 A K s k z x t i h2)). Qed.
Lemma lem4424593 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (h1 : term733 A K s k z x t i) : term733 A K s k z x t i.
Proof. exact (fun h0 : term732 A K s k z x t i => @lem4424592 A K s k z x t i h0 h1). Qed.
Lemma lem4424594 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : term735 A K s k z x t i.
Proof. exact (fun h0 : term733 A K s k z x t i => @lem4424593 A K s k z x t i h0). Qed.
Lemma lem4424597 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : term733 A K s k z x t i.
Proof. exact (@lem4424594 A K s k z x t i (@lem4424586 A K s k z x t i)). Qed.
Lemma lem4424598 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : term733 A K s k z x t i.
Proof. exact (@lem4424597 A K s k z x t i). Qed.
Lemma lem4424636 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4424637 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term730 A K s k z x t i) = (term736 A K s k z x t i).
Proof. exact (@lem4424636 (term731 A K s k z x t i)). Qed.
Lemma lem4424639 (t : Prop) : (term60 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4424640 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term736 A K s k z x t i) = (term729 A K s k z x t i).
Proof. exact (@lem4424639 (term729 A K s k z x t i)). Qed.
Lemma lem4424643 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term730 A K s k z x t i) = (term729 A K s k z x t i).
Proof. exact (TRANS (@lem4424637 A K s k z x t i) (@lem4424640 A K s k z x t i)). Qed.
Lemma lem4424658 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term737 A K x s i) = (term737 A K x s i).
Proof. exact (eq_refl (term737 A K x s i)). Qed.
Lemma lem4424659 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term738 A K s k z x t i) = (term739 A K s k z x t i).
Proof. exact (MK_COMB (@lem4424658 A K x s i) (@lem4424643 A K s k z x t i)). Qed.
Lemma lem4424662 {K : Type'} (i : K) (k : K -> Prop) : (term42 K i k) = (term42 K i k).
Proof. exact (eq_refl (term42 K i k)). Qed.
Lemma lem4424663 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term740 A K s k z x t i) = (term741 A K s k z x t i).
Proof. exact (MK_COMB (@lem4424662 K i k) (@lem4424659 A K s k z x t i)). Qed.
Lemma lem4424666 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term583 A K k z s) = (term583 A K k z s).
Proof. exact (eq_refl (term583 A K k z s)). Qed.
Lemma lem4424667 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term732 A K s k z x t i) = (term742 A K s k z x t i).
Proof. exact (MK_COMB (@lem4424666 A K k z s) (@lem4424663 A K s k z x t i)). Qed.
Lemma lem4424670 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term743 A K k z x t i) = (term744 A K k z x t i).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4424667 A K s k z x t i)). Qed.
Lemma lem4424671 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4424672 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term745 A K k z x t i) = (term746 A K k z x t i).
Proof. exact (MK_COMB (@lem4424671 A K) (@lem4424670 A K k z x t i)). Qed.
Lemma lem4424677 {A K : Type'} (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term747 A K z x t i) = (term748 A K z x t i).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4424672 A K k z x t i)). Qed.
Lemma lem4424678 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4424679 {A K : Type'} (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term749 A K z x t i) = (term750 A K z x t i).
Proof. exact (MK_COMB (@lem4424678 K) (@lem4424677 A K z x t i)). Qed.
Lemma lem4424684 {A K : Type'} (x : A) (t : type1470 A K) (i : K) : (term751 A K x t i) = (term752 A K x t i).
Proof. exact (fun_ext (fun z : K -> A => @lem4424679 A K z x t i)). Qed.
Lemma lem4424685 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4424686 {A K : Type'} (x : A) (t : type1470 A K) (i : K) : (term753 A K x t i) = (term754 A K x t i).
Proof. exact (MK_COMB (@lem4424685 A K) (@lem4424684 A K x t i)). Qed.
Lemma lem4424691 {A K : Type'} (t : type1470 A K) (i : K) : (term755 A K t i) = (term756 A K t i).
Proof. exact (fun_ext (fun x : A => @lem4424686 A K x t i)). Qed.
Lemma lem4424692 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4424693 {A K : Type'} (t : type1470 A K) (i : K) : (term757 A K t i) = (term758 A K t i).
Proof. exact (MK_COMB (@lem4424692 A) (@lem4424691 A K t i)). Qed.
Lemma lem4424698 {A K : Type'} (i : K) : (term759 A K i) = (term760 A K i).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4424693 A K t i)). Qed.
Lemma lem4424699 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4424700 {A K : Type'} (i : K) : (term761 A K i) = (term762 A K i).
Proof. exact (MK_COMB (@lem4424699 A K) (@lem4424698 A K i)). Qed.
Lemma lem4424705 {A K : Type'} : (term763 A K) = (term764 A K).
Proof. exact (fun_ext (fun i : K => @lem4424700 A K i)). Qed.
Lemma lem4424706 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4424715 {A K : Type'} : (term765 A K) = (term766 A K).
Proof. exact (MK_COMB (@lem4424706 K) (@lem4424705 A K)). Qed.
Lemma lem4424716 {A K : Type'} (x : A) (t : type1470 A K) (i : K) : (term30 A K x t i) = (term30 A K x t i).
Proof. exact (eq_refl (term30 A K x t i)). Qed.
Lemma lem4424720 {K : Type'} (i' : K) (i : K) (h1 : (i' = i) = False) : (i' = i) = False.
Proof. exact (h1). Qed.
Lemma lem4424721 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4424722 {A K : Type'} (i' : K) (i : K) (h1 : (i' = i) = False) : (term767 A K i' i) = (@COND A False).
Proof. exact (MK_COMB (@lem4424721 A) (@lem4424720 K i' i h1)). Qed.
Lemma lem4424723 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4424724 {A K : Type'} (x : A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term768 A K i' i x) = (@COND A False x).
Proof. exact (MK_COMB (@lem4424722 A K i' i h1) (@lem4424723 A x)). Qed.
Lemma lem4424725 {A K : Type'} (z : K -> A) (i' : K) : (z i') = (z i').
Proof. exact (eq_refl (z i')). Qed.
Lemma lem4424726 {A K : Type'} (x : A) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term677 A K i x z i') = (term769 A K x z i').
Proof. exact (MK_COMB (@lem4424724 A K x i' i h1) (@lem4424725 A K z i')). Qed.
Lemma lem4424728 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4424729 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4424728 A t1 t2). Qed.
Lemma lem4424730 {A K : Type'} (x : A) (z : K -> A) (i' : K) : (term769 A K x z i') = (z i').
Proof. exact (@lem4424729 A x (z i')). Qed.
Lemma lem4424731 {A K : Type'} (x : A) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term677 A K i x z i') = (z i').
Proof. exact (TRANS (@lem4424726 A K x z i' i h1) (@lem4424730 A K x z i')). Qed.
Lemma lem4424732 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4424733 {A K : Type'} (x : A) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term712 A K i x z i') = (term474 A K z i').
Proof. exact (MK_COMB (@lem4424732 A) (@lem4424731 A K x z i' i h1)). Qed.
Lemma lem4424734 {A K : Type'} (t : type1470 A K) (i' : K) : (t i') = (t i').
Proof. exact (eq_refl (t i')). Qed.
Lemma lem4424735 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = False) : (term713 A K i x z t i') = (term445 A K z t i').
Proof. exact (MK_COMB (@lem4424733 A K x z i' i h1) (@lem4424734 A K t i')). Qed.
Lemma lem4424736 {K : Type'} (i' : K) (k : K -> Prop) : (term42 K i' k) = (term42 K i' k).
Proof. exact (eq_refl (term42 K i' k)). Qed.
Lemma lem4424737 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = False) : (term716 A K k i x z t i') = (term427 A K k z t i').
Proof. exact (MK_COMB (@lem4424736 K i' k) (@lem4424735 A K x z t i' i h1)). Qed.
Lemma lem4424740 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (i' : K) : term770 A K i x k z t i'.
Proof. exact (fun h0 : (i' = i) = False => @lem4424737 A K x k z t i' i h0). Qed.
Lemma lem4424742 {K : Type'} (i' : K) (i : K) (h1 : (i' = i) = True) : (i' = i) = True.
Proof. exact (h1). Qed.
Lemma lem4424743 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4424744 {A K : Type'} (i' : K) (i : K) (h1 : (i' = i) = True) : (term767 A K i' i) = (@COND A True).
Proof. exact (MK_COMB (@lem4424743 A) (@lem4424742 K i' i h1)). Qed.
Lemma lem4424745 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4424746 {A K : Type'} (x : A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term768 A K i' i x) = (@COND A True x).
Proof. exact (MK_COMB (@lem4424744 A K i' i h1) (@lem4424745 A x)). Qed.
Lemma lem4424747 {A K : Type'} (z : K -> A) (i' : K) : (z i') = (z i').
Proof. exact (eq_refl (z i')). Qed.
Lemma lem4424748 {A K : Type'} (x : A) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term677 A K i x z i') = (term771 A K x z i').
Proof. exact (MK_COMB (@lem4424746 A K x i' i h1) (@lem4424747 A K z i')). Qed.
Lemma lem4424750 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4424751 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4424750 A t2 t1). Qed.
Lemma lem4424752 {A K : Type'} (z : K -> A) (i' : K) (x : A) : (term771 A K x z i') = x.
Proof. exact (@lem4424751 A (z i') x). Qed.
Lemma lem4424753 {A K : Type'} (z : K -> A) (x : A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term677 A K i x z i') = x.
Proof. exact (TRANS (@lem4424748 A K x z i' i h1) (@lem4424752 A K z i' x)). Qed.
Lemma lem4424754 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4424755 {A K : Type'} (z : K -> A) (x : A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term712 A K i x z i') = (@IN A x).
Proof. exact (MK_COMB (@lem4424754 A) (@lem4424753 A K z x i' i h1)). Qed.
Lemma lem4424756 {A K : Type'} (t : type1470 A K) (i' : K) : (t i') = (t i').
Proof. exact (eq_refl (t i')). Qed.
Lemma lem4424757 {A K : Type'} (z : K -> A) (x : A) (t : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = True) : (term713 A K i x z t i') = (term30 A K x t i').
Proof. exact (MK_COMB (@lem4424755 A K z x i' i h1) (@lem4424756 A K t i')). Qed.
Lemma lem4424758 {K : Type'} (i' : K) (k : K -> Prop) : (term42 K i' k) = (term42 K i' k).
Proof. exact (eq_refl (term42 K i' k)). Qed.
Lemma lem4424759 {A K : Type'} (z : K -> A) (k : K -> Prop) (x : A) (t : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = True) : (term716 A K k i x z t i') = (term44 A K k x t i').
Proof. exact (MK_COMB (@lem4424758 K i' k) (@lem4424757 A K z x t i' i h1)). Qed.
Lemma lem4424762 {A K : Type'} (i : K) (z : K -> A) (k : K -> Prop) (x : A) (t : type1470 A K) (i' : K) : term772 A K i z k x t i'.
Proof. exact (fun h0 : (i' = i) = True => @lem4424759 A K z k x t i' i h0). Qed.
Lemma lem4424763 {A K : Type'} (i : K) (z : K -> A) (k : K -> Prop) (x : A) (t : type1470 A K) (i' : K) : term773 A K i z k x t i'.
Proof. exact (conj (@lem4424740 A K i x k z t i') (@lem4424762 A K i z k x t i')). Qed.
Lemma lem4424765 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term774 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4424766 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (i' : K) : term775 A K x i k z t i'.
Proof. exact (@lem4424765 (term716 A K k i x z t i') (term44 A K k x t i') (i' = i) (term427 A K k z t i')). Qed.
Lemma lem4424807 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (i' : K) : (term716 A K k i x z t i') = (term776 A K x i k z t i').
Proof. exact (@lem4424766 A K x i k z t i' (@lem4424763 A K i z k x t i')). Qed.
Lemma lem4424808 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term717 A K k i x z t) = (term777 A K x i k z t).
Proof. exact (fun_ext (fun i' : K => @lem4424807 A K x i k z t i')). Qed.
Lemma lem4424809 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4424810 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term718 A K k i x z t) = (term778 A K x i k z t).
Proof. exact (MK_COMB (@lem4424809 K) (@lem4424808 A K x i k z t)). Qed.
Lemma lem4424814 {K : Type'} (i' : K) (i : K) (h1 : (i' = i) = False) : (i' = i) = False.
Proof. exact (h1). Qed.
Lemma lem4424815 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4424816 {A K : Type'} (i' : K) (i : K) (h1 : (i' = i) = False) : (term767 A K i' i) = (@COND A False).
Proof. exact (MK_COMB (@lem4424815 A) (@lem4424814 K i' i h1)). Qed.
Lemma lem4424817 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4424818 {A K : Type'} (x : A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term768 A K i' i x) = (@COND A False x).
Proof. exact (MK_COMB (@lem4424816 A K i' i h1) (@lem4424817 A x)). Qed.
Lemma lem4424819 {A K : Type'} (z : K -> A) (i' : K) : (z i') = (z i').
Proof. exact (eq_refl (z i')). Qed.
Lemma lem4424820 {A K : Type'} (x : A) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term677 A K i x z i') = (term769 A K x z i').
Proof. exact (MK_COMB (@lem4424818 A K x i' i h1) (@lem4424819 A K z i')). Qed.
Lemma lem4424822 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4424823 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4424822 A t1 t2). Qed.
Lemma lem4424824 {A K : Type'} (x : A) (z : K -> A) (i' : K) : (term769 A K x z i') = (z i').
Proof. exact (@lem4424823 A x (z i')). Qed.
Lemma lem4424825 {A K : Type'} (x : A) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term677 A K i x z i') = (z i').
Proof. exact (TRANS (@lem4424820 A K x z i' i h1) (@lem4424824 A K x z i')). Qed.
Lemma lem4424826 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4424827 {A K : Type'} (x : A) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term712 A K i x z i') = (term474 A K z i').
Proof. exact (MK_COMB (@lem4424826 A) (@lem4424825 A K x z i' i h1)). Qed.
Lemma lem4424828 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4424829 {A K : Type'} (x : A) (z : K -> A) (s : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = False) : (term713 A K i x z s i') = (term445 A K z s i').
Proof. exact (MK_COMB (@lem4424827 A K x z i' i h1) (@lem4424828 A K s i')). Qed.
Lemma lem4424830 {K : Type'} (i' : K) (k : K -> Prop) : (term42 K i' k) = (term42 K i' k).
Proof. exact (eq_refl (term42 K i' k)). Qed.
Lemma lem4424831 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = False) : (term716 A K k i x z s i') = (term427 A K k z s i').
Proof. exact (MK_COMB (@lem4424830 K i' k) (@lem4424829 A K x z s i' i h1)). Qed.
Lemma lem4424834 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : term770 A K i x k z s i'.
Proof. exact (fun h0 : (i' = i) = False => @lem4424831 A K x k z s i' i h0). Qed.
Lemma lem4424836 {K : Type'} (i' : K) (i : K) (h1 : (i' = i) = True) : (i' = i) = True.
Proof. exact (h1). Qed.
Lemma lem4424837 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4424838 {A K : Type'} (i' : K) (i : K) (h1 : (i' = i) = True) : (term767 A K i' i) = (@COND A True).
Proof. exact (MK_COMB (@lem4424837 A) (@lem4424836 K i' i h1)). Qed.
Lemma lem4424839 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4424840 {A K : Type'} (x : A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term768 A K i' i x) = (@COND A True x).
Proof. exact (MK_COMB (@lem4424838 A K i' i h1) (@lem4424839 A x)). Qed.
Lemma lem4424841 {A K : Type'} (z : K -> A) (i' : K) : (z i') = (z i').
Proof. exact (eq_refl (z i')). Qed.
Lemma lem4424842 {A K : Type'} (x : A) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term677 A K i x z i') = (term771 A K x z i').
Proof. exact (MK_COMB (@lem4424840 A K x i' i h1) (@lem4424841 A K z i')). Qed.
Lemma lem4424844 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4424845 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4424844 A t2 t1). Qed.
Lemma lem4424846 {A K : Type'} (z : K -> A) (i' : K) (x : A) : (term771 A K x z i') = x.
Proof. exact (@lem4424845 A (z i') x). Qed.
Lemma lem4424847 {A K : Type'} (z : K -> A) (x : A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term677 A K i x z i') = x.
Proof. exact (TRANS (@lem4424842 A K x z i' i h1) (@lem4424846 A K z i' x)). Qed.
Lemma lem4424848 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4424849 {A K : Type'} (z : K -> A) (x : A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term712 A K i x z i') = (@IN A x).
Proof. exact (MK_COMB (@lem4424848 A) (@lem4424847 A K z x i' i h1)). Qed.
Lemma lem4424850 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4424851 {A K : Type'} (z : K -> A) (x : A) (s : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = True) : (term713 A K i x z s i') = (term30 A K x s i').
Proof. exact (MK_COMB (@lem4424849 A K z x i' i h1) (@lem4424850 A K s i')). Qed.
Lemma lem4424852 {K : Type'} (i' : K) (k : K -> Prop) : (term42 K i' k) = (term42 K i' k).
Proof. exact (eq_refl (term42 K i' k)). Qed.
Lemma lem4424853 {A K : Type'} (z : K -> A) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = True) : (term716 A K k i x z s i') = (term44 A K k x s i').
Proof. exact (MK_COMB (@lem4424852 K i' k) (@lem4424851 A K z x s i' i h1)). Qed.
Lemma lem4424856 {A K : Type'} (i : K) (z : K -> A) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) : term772 A K i z k x s i'.
Proof. exact (fun h0 : (i' = i) = True => @lem4424853 A K z k x s i' i h0). Qed.
Lemma lem4424857 {A K : Type'} (i : K) (z : K -> A) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) : term773 A K i z k x s i'.
Proof. exact (conj (@lem4424834 A K i x k z s i') (@lem4424856 A K i z k x s i')). Qed.
Lemma lem4424859 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term774 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4424860 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : term775 A K x i k z s i'.
Proof. exact (@lem4424859 (term716 A K k i x z s i') (term44 A K k x s i') (i' = i) (term427 A K k z s i')). Qed.
Lemma lem4424901 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term716 A K k i x z s i') = (term776 A K x i k z s i').
Proof. exact (@lem4424860 A K x i k z s i' (@lem4424857 A K i z k x s i')). Qed.
Lemma lem4424902 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term717 A K k i x z s) = (term777 A K x i k z s).
Proof. exact (fun_ext (fun i' : K => @lem4424901 A K x i k z s i')). Qed.
Lemma lem4424903 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4424904 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term718 A K k i x z s) = (term778 A K x i k z s).
Proof. exact (MK_COMB (@lem4424903 K) (@lem4424902 A K x i k z s)). Qed.
Lemma lem4424905 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4424906 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term779 A K k i x z s) = (term780 A K x i k z s).
Proof. exact (MK_COMB (@lem4424905) (@lem4424904 A K x i k z s)). Qed.
Lemma lem4424907 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term724 A K s k i x z t) = (term781 A K s x i k z t).
Proof. exact (MK_COMB (@lem4424906 A K x i k z s) (@lem4424810 A K x i k z t)). Qed.
Lemma lem4424908 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4424909 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term782 A K s k i x z t) = (term783 A K s x i k z t).
Proof. exact (MK_COMB (@lem4424908) (@lem4424907 A K s x i k z t)). Qed.
Lemma lem4424910 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term729 A K s k z x t i) = (term784 A K s k z x t i).
Proof. exact (MK_COMB (@lem4424909 A K s x i k z t) (@lem4424716 A K x t i)). Qed.
Lemma lem4424913 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term737 A K x s i) = (term737 A K x s i).
Proof. exact (eq_refl (term737 A K x s i)). Qed.
Lemma lem4424914 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term739 A K s k z x t i) = (term785 A K s k z x t i).
Proof. exact (MK_COMB (@lem4424913 A K x s i) (@lem4424910 A K s k z x t i)). Qed.
Lemma lem4424917 {K : Type'} (i : K) (k : K -> Prop) : (term42 K i k) = (term42 K i k).
Proof. exact (eq_refl (term42 K i k)). Qed.
Lemma lem4424918 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term741 A K s k z x t i) = (term786 A K s k z x t i).
Proof. exact (MK_COMB (@lem4424917 K i k) (@lem4424914 A K s k z x t i)). Qed.
Lemma lem4424923 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term427 A K k z s i) = (term427 A K k z s i).
Proof. exact (eq_refl (term427 A K k z s i)). Qed.
Lemma lem4424924 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term428 A K k z s) = (term428 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4424923 A K k z s i)). Qed.
Lemma lem4424925 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4424926 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term429 A K k z s) = (term429 A K k z s).
Proof. exact (MK_COMB (@lem4424925 K) (@lem4424924 A K k z s)). Qed.
Lemma lem4424927 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4424928 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term583 A K k z s) = (term583 A K k z s).
Proof. exact (MK_COMB (@lem4424927) (@lem4424926 A K k z s)). Qed.
Lemma lem4424929 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term742 A K s k z x t i) = (term787 A K s k z x t i).
Proof. exact (MK_COMB (@lem4424928 A K k z s) (@lem4424918 A K s k z x t i)). Qed.
Lemma lem4424930 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term744 A K k z x t i) = (term788 A K k z x t i).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4424929 A K s k z x t i)). Qed.
Lemma lem4424931 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4424932 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term746 A K k z x t i) = (term789 A K k z x t i).
Proof. exact (MK_COMB (@lem4424931 A K) (@lem4424930 A K k z x t i)). Qed.
Lemma lem4424933 {A K : Type'} (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term748 A K z x t i) = (term790 A K z x t i).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4424932 A K k z x t i)). Qed.
Lemma lem4424934 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4424935 {A K : Type'} (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term750 A K z x t i) = (term791 A K z x t i).
Proof. exact (MK_COMB (@lem4424934 K) (@lem4424933 A K z x t i)). Qed.
Lemma lem4424936 {A K : Type'} (x : A) (t : type1470 A K) (i : K) : (term752 A K x t i) = (term792 A K x t i).
Proof. exact (fun_ext (fun z : K -> A => @lem4424935 A K z x t i)). Qed.
Lemma lem4424937 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4424938 {A K : Type'} (x : A) (t : type1470 A K) (i : K) : (term754 A K x t i) = (term793 A K x t i).
Proof. exact (MK_COMB (@lem4424937 A K) (@lem4424936 A K x t i)). Qed.
Lemma lem4424939 {A K : Type'} (t : type1470 A K) (i : K) : (term756 A K t i) = (term794 A K t i).
Proof. exact (fun_ext (fun x : A => @lem4424938 A K x t i)). Qed.
Lemma lem4424940 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4424941 {A K : Type'} (t : type1470 A K) (i : K) : (term758 A K t i) = (term795 A K t i).
Proof. exact (MK_COMB (@lem4424940 A) (@lem4424939 A K t i)). Qed.
Lemma lem4424942 {A K : Type'} (i : K) : (term760 A K i) = (term796 A K i).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4424941 A K t i)). Qed.
Lemma lem4424943 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4424944 {A K : Type'} (i : K) : (term762 A K i) = (term797 A K i).
Proof. exact (MK_COMB (@lem4424943 A K) (@lem4424942 A K i)). Qed.
Lemma lem4424945 {A K : Type'} : (term764 A K) = (term798 A K).
Proof. exact (fun_ext (fun i : K => @lem4424944 A K i)). Qed.
Lemma lem4424946 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4424947 {A K : Type'} : (term766 A K) = (term799 A K).
Proof. exact (MK_COMB (@lem4424946 K) (@lem4424945 A K)). Qed.
Lemma lem4425036 {A K : Type'} : (term765 A K) = (term799 A K).
Proof. exact (TRANS (@lem4424715 A K) (@lem4424947 A K)). Qed.
Lemma lem4425037 {A K : Type'} : (term799 A K) = (term765 A K).
Proof. exact (SYM (@lem4425036 A K)). Qed.
Lemma lem4425038 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term429 A K k z s) : term429 A K k z s.
Proof. exact (h1). Qed.
Lemma lem4425041 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term781 A K s x i k z t) : term781 A K s x i k z t.
Proof. exact (h1). Qed.
Lemma lem4425043 (p : Prop) : p = (term53 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4425044 {A K : Type'} (x : A) (t : type1470 A K) (i : K) : (term30 A K x t i) = (term800 A K x t i).
Proof. exact (@lem4425043 (term30 A K x t i)). Qed.
Lemma lem4425045 {A K : Type'} (x : A) (t : type1470 A K) (i : K) : (term800 A K x t i) = (term30 A K x t i).
Proof. exact (SYM (@lem4425044 A K x t i)). Qed.
Lemma lem4425046 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (h1 : term518 A K x t i) : term518 A K x t i.
Proof. exact (h1). Qed.
Lemma lem4425053 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term427 A K k z s i) = (term444 A K k z s i).
Proof. exact (@lem17265 (@IN K i k) (term445 A K z s i)). Qed.
Lemma lem4425054 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term428 A K k z s) = (term446 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4425053 A K k z s i)). Qed.
Lemma lem4425055 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4425108 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term429 A K k z s) = (term447 A K k z s).
Proof. exact (MK_COMB (@lem4425055 K) (@lem4425054 A K k z s)). Qed.
Lemma lem4425109 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term429 A K k z s) : term447 A K k z s.
Proof. exact (EQ_MP (@lem4425108 A K k z s) (@lem4425038 A K k z s h1)). Qed.
Lemma lem4425115 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4425121 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (h1 : term30 A K x s i) : term30 A K x s i.
Proof. exact (h1). Qed.
Lemma lem4425124 {K : Type'} (i' : K) (i : K) : (term801 K i' i) = (i' = i).
Proof. exact (@lem16933 (i' = i)). Qed.
Lemma lem4425131 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) : (term802 A K k x s i') = (term803 A K k x s i').
Proof. exact (@lem17362 (@IN K i' k) (term30 A K x s i')). Qed.
Lemma lem4425132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4425133 {K : Type'} (i' : K) (i : K) : (term804 K i' i) = (term805 K i' i).
Proof. exact (MK_COMB (@lem4425132) (@lem4425124 K i' i)). Qed.
Lemma lem4425134 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) : (term806 A K i k x s i') = (term807 A K i k x s i').
Proof. exact (MK_COMB (@lem4425133 K i' i) (@lem4425131 A K k x s i')). Qed.
Lemma lem4425135 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) : (term808 A K i k x s i') = (term806 A K i k x s i').
Proof. exact (@lem17160 (term809 K i' i) (term44 A K k x s i')). Qed.
Lemma lem4425136 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) : (term808 A K i k x s i') = (term807 A K i k x s i').
Proof. exact (TRANS (@lem4425135 A K i k x s i') (@lem4425134 A K i k x s i')). Qed.
Lemma lem4425144 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term449 A K k z s i') = (term450 A K k z s i').
Proof. exact (@lem17362 (@IN K i' k) (term445 A K z s i')). Qed.
Lemma lem4425146 {K : Type'} (i' : K) (i : K) : (term810 K i' i) = (term810 K i' i).
Proof. exact (eq_refl (term810 K i' i)). Qed.
Lemma lem4425147 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term811 A K i k z s i') = (term812 A K i k z s i').
Proof. exact (MK_COMB (@lem4425146 K i' i) (@lem4425144 A K k z s i')). Qed.
Lemma lem4425148 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term813 A K i k z s i') = (term811 A K i k z s i').
Proof. exact (@lem17160 (i' = i) (term427 A K k z s i')). Qed.
Lemma lem4425149 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term813 A K i k z s i') = (term812 A K i k z s i').
Proof. exact (TRANS (@lem4425148 A K i k z s i') (@lem4425147 A K i k z s i')). Qed.
Lemma lem4425150 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4425151 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) : (term814 A K i k x s i') = (term815 A K i k x s i').
Proof. exact (MK_COMB (@lem4425150) (@lem4425136 A K i k x s i')). Qed.
Lemma lem4425152 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term816 A K x i k z s i') = (term817 A K x i k z s i').
Proof. exact (MK_COMB (@lem4425151 A K i k x s i') (@lem4425149 A K i k z s i')). Qed.
Lemma lem4425153 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term818 A K x i k z s i') = (term816 A K x i k z s i').
Proof. exact (@lem17045 (term819 A K i k x s i') (term820 A K i k z s i')). Qed.
Lemma lem4425154 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term818 A K x i k z s i') = (term817 A K x i k z s i').
Proof. exact (TRANS (@lem4425153 A K x i k z s i') (@lem4425152 A K x i k z s i')). Qed.
Lemma lem4425155 {K : Type'} (P : K -> Prop) : (term70 K P) = (term71 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4425156 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term821 A K x i k z s) = (term822 A K x i k z s).
Proof. exact (@lem4425155 K (term777 A K x i k z s)). Qed.
Lemma lem4425157 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term823 A K x i k z s i') = (term776 A K x i k z s i').
Proof. exact (eq_refl (term823 A K x i k z s i')). Qed.
Lemma lem4425158 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4425159 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term824 A K x i k z s i') = (term818 A K x i k z s i').
Proof. exact (MK_COMB (@lem4425158) (@lem4425157 A K x i k z s i')). Qed.
Lemma lem4425160 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term824 A K x i k z s i') = (term817 A K x i k z s i').
Proof. exact (TRANS (@lem4425159 A K x i k z s i') (@lem4425154 A K x i k z s i')). Qed.
Lemma lem4425161 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term825 A K x i k z s) = (term826 A K x i k z s).
Proof. exact (fun_ext (fun i' : K => @lem4425160 A K x i k z s i')). Qed.
Lemma lem4425162 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4425163 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term822 A K x i k z s) = (term827 A K x i k z s).
Proof. exact (MK_COMB (@lem4425162 K) (@lem4425161 A K x i k z s)). Qed.
Lemma lem4425164 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term821 A K x i k z s) = (term827 A K x i k z s).
Proof. exact (TRANS (@lem4425156 A K x i k z s) (@lem4425163 A K x i k z s)). Qed.
Lemma lem4425172 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i' : K) : (term44 A K k x t i') = (term519 A K k x t i').
Proof. exact (@lem17265 (@IN K i' k) (term30 A K x t i')). Qed.
Lemma lem4425174 {K : Type'} (i' : K) (i : K) : (term828 K i' i) = (term828 K i' i).
Proof. exact (eq_refl (term828 K i' i)). Qed.
Lemma lem4425175 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) (i' : K) : (term819 A K i k x t i') = (term829 A K i k x t i').
Proof. exact (MK_COMB (@lem4425174 K i' i) (@lem4425172 A K k x t i')). Qed.
Lemma lem4425183 {A K : Type'} (k : K -> Prop) (z : K -> A) (t : type1470 A K) (i' : K) : (term427 A K k z t i') = (term444 A K k z t i').
Proof. exact (@lem17265 (@IN K i' k) (term445 A K z t i')). Qed.
Lemma lem4425185 {K : Type'} (i' : K) (i : K) : (term830 K i' i) = (term830 K i' i).
Proof. exact (eq_refl (term830 K i' i)). Qed.
Lemma lem4425186 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (i' : K) : (term820 A K i k z t i') = (term831 A K i k z t i').
Proof. exact (MK_COMB (@lem4425185 K i' i) (@lem4425183 A K k z t i')). Qed.
Lemma lem4425187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4425188 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) (i' : K) : (term832 A K i k x t i') = (term833 A K i k x t i').
Proof. exact (MK_COMB (@lem4425187) (@lem4425175 A K i k x t i')). Qed.
Lemma lem4425189 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (i' : K) : (term776 A K x i k z t i') = (term834 A K x i k z t i').
Proof. exact (MK_COMB (@lem4425188 A K i k x t i') (@lem4425186 A K i k z t i')). Qed.
Lemma lem4425190 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term777 A K x i k z t) = (term835 A K x i k z t).
Proof. exact (fun_ext (fun i' : K => @lem4425189 A K x i k z t i')). Qed.
Lemma lem4425191 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4425192 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term778 A K x i k z t) = (term836 A K x i k z t).
Proof. exact (MK_COMB (@lem4425191 K) (@lem4425190 A K x i k z t)). Qed.
Lemma lem4425193 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4425194 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term837 A K x i k z s) = (term838 A K x i k z s).
Proof. exact (MK_COMB (@lem4425193) (@lem4425164 A K x i k z s)). Qed.
Lemma lem4425195 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term839 A K s x i k z t) = (term840 A K s x i k z t).
Proof. exact (MK_COMB (@lem4425194 A K x i k z s) (@lem4425192 A K x i k z t)). Qed.
Lemma lem4425196 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term781 A K s x i k z t) = (term839 A K s x i k z t).
Proof. exact (@lem17265 (term778 A K x i k z s) (term778 A K x i k z t)). Qed.
Lemma lem4425197 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term781 A K s x i k z t) = (term840 A K s x i k z t).
Proof. exact (TRANS (@lem4425196 A K s x i k z t) (@lem4425195 A K s x i k z t)). Qed.
Lemma lem4425199 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4425200 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term147 K P Q) = (term148 K P Q).
Proof. exact (@lem4425199 K P Q). Qed.
Lemma lem4425201 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term841 A K x i k z s) = (term842 A K x i k z s).
Proof. exact (@lem4425200 K (term843 A K i k x s) (term844 A K i k z s)). Qed.
Lemma lem4425202 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) : (term845 A K i k x s i') = (term807 A K i k x s i').
Proof. exact (eq_refl (term845 A K i k x s i')). Qed.
Lemma lem4425203 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4425204 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) : (term846 A K i k x s i') = (term815 A K i k x s i').
Proof. exact (MK_COMB (@lem4425203) (@lem4425202 A K i k x s i')). Qed.
Lemma lem4425205 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term847 A K i k z s i') = (term812 A K i k z s i').
Proof. exact (eq_refl (term847 A K i k z s i')). Qed.
Lemma lem4425206 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term848 A K x i k z s i') = (term817 A K x i k z s i').
Proof. exact (MK_COMB (@lem4425204 A K i k x s i') (@lem4425205 A K i k z s i')). Qed.
Lemma lem4425207 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term849 A K x i k z s) = (term826 A K x i k z s).
Proof. exact (fun_ext (fun i' : K => @lem4425206 A K x i k z s i')). Qed.
Lemma lem4425208 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4425209 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term841 A K x i k z s) = (term827 A K x i k z s).
Proof. exact (MK_COMB (@lem4425208 K) (@lem4425207 A K x i k z s)). Qed.
Lemma lem4425210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4425211 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term850 A K x i k z s) = (term851 A K x i k z s).
Proof. exact (MK_COMB (@lem4425210) (@lem4425209 A K x i k z s)). Qed.
Lemma lem4425212 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) : (term845 A K i k x s i') = (term807 A K i k x s i').
Proof. exact (eq_refl (term845 A K i k x s i')). Qed.
Lemma lem4425213 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) : (term852 A K i k x s) = (term843 A K i k x s).
Proof. exact (fun_ext (fun i' : K => @lem4425212 A K i k x s i')). Qed.
Lemma lem4425214 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4425215 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) : (term853 A K i k x s) = (term854 A K i k x s).
Proof. exact (MK_COMB (@lem4425214 K) (@lem4425213 A K i k x s)). Qed.
Lemma lem4425216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4425217 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) : (term855 A K i k x s) = (term856 A K i k x s).
Proof. exact (MK_COMB (@lem4425216) (@lem4425215 A K i k x s)). Qed.
Lemma lem4425218 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term847 A K i k z s i') = (term812 A K i k z s i').
Proof. exact (eq_refl (term847 A K i k z s i')). Qed.
Lemma lem4425219 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term857 A K i k z s) = (term844 A K i k z s).
Proof. exact (fun_ext (fun i' : K => @lem4425218 A K i k z s i')). Qed.
Lemma lem4425220 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4425221 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term858 A K i k z s) = (term859 A K i k z s).
Proof. exact (MK_COMB (@lem4425220 K) (@lem4425219 A K i k z s)). Qed.
Lemma lem4425222 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term842 A K x i k z s) = (term860 A K x i k z s).
Proof. exact (MK_COMB (@lem4425217 A K i k x s) (@lem4425221 A K i k z s)). Qed.
Lemma lem4425223 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : ((term841 A K x i k z s) = (term842 A K x i k z s)) = ((term827 A K x i k z s) = (term860 A K x i k z s)).
Proof. exact (MK_COMB (@lem4425211 A K x i k z s) (@lem4425222 A K x i k z s)). Qed.
Lemma lem4425224 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term827 A K x i k z s) = (term860 A K x i k z s).
Proof. exact (EQ_MP (@lem4425223 A K x i k z s) (@lem4425201 A K x i k z s)). Qed.
Lemma lem4425321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4425322 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term838 A K x i k z s) = (term861 A K x i k z s).
Proof. exact (MK_COMB (@lem4425321) (@lem4425224 A K x i k z s)). Qed.
Lemma lem4425324 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term125 A P Q) = (term126 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4425325 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term125 K P Q) = (term126 K P Q).
Proof. exact (@lem4425324 K P Q). Qed.
Lemma lem4425326 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term862 A K x i k z t) = (term863 A K x i k z t).
Proof. exact (@lem4425325 K (term864 A K i k x t) (term865 A K i k z t)). Qed.
Lemma lem4425327 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) (i' : K) : (term866 A K i k x t i') = (term829 A K i k x t i').
Proof. exact (eq_refl (term866 A K i k x t i')). Qed.
Lemma lem4425328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4425329 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) (i' : K) : (term867 A K i k x t i') = (term833 A K i k x t i').
Proof. exact (MK_COMB (@lem4425328) (@lem4425327 A K i k x t i')). Qed.
Lemma lem4425330 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (i' : K) : (term868 A K i k z t i') = (term831 A K i k z t i').
Proof. exact (eq_refl (term868 A K i k z t i')). Qed.
Lemma lem4425331 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (i' : K) : (term869 A K x i k z t i') = (term834 A K x i k z t i').
Proof. exact (MK_COMB (@lem4425329 A K i k x t i') (@lem4425330 A K i k z t i')). Qed.
Lemma lem4425332 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term870 A K x i k z t) = (term835 A K x i k z t).
Proof. exact (fun_ext (fun i' : K => @lem4425331 A K x i k z t i')). Qed.
Lemma lem4425333 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4425334 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term862 A K x i k z t) = (term836 A K x i k z t).
Proof. exact (MK_COMB (@lem4425333 K) (@lem4425332 A K x i k z t)). Qed.
Lemma lem4425335 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4425336 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term871 A K x i k z t) = (term872 A K x i k z t).
Proof. exact (MK_COMB (@lem4425335) (@lem4425334 A K x i k z t)). Qed.
Lemma lem4425337 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) (i' : K) : (term866 A K i k x t i') = (term829 A K i k x t i').
Proof. exact (eq_refl (term866 A K i k x t i')). Qed.
Lemma lem4425338 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) : (term873 A K i k x t) = (term864 A K i k x t).
Proof. exact (fun_ext (fun i' : K => @lem4425337 A K i k x t i')). Qed.
Lemma lem4425339 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4425340 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) : (term874 A K i k x t) = (term875 A K i k x t).
Proof. exact (MK_COMB (@lem4425339 K) (@lem4425338 A K i k x t)). Qed.
Lemma lem4425341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4425342 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) : (term876 A K i k x t) = (term877 A K i k x t).
Proof. exact (MK_COMB (@lem4425341) (@lem4425340 A K i k x t)). Qed.
Lemma lem4425343 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (i' : K) : (term868 A K i k z t i') = (term831 A K i k z t i').
Proof. exact (eq_refl (term868 A K i k z t i')). Qed.
Lemma lem4425344 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term878 A K i k z t) = (term865 A K i k z t).
Proof. exact (fun_ext (fun i' : K => @lem4425343 A K i k z t i')). Qed.
Lemma lem4425345 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4425346 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term879 A K i k z t) = (term880 A K i k z t).
Proof. exact (MK_COMB (@lem4425345 K) (@lem4425344 A K i k z t)). Qed.
Lemma lem4425347 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term863 A K x i k z t) = (term881 A K x i k z t).
Proof. exact (MK_COMB (@lem4425342 A K i k x t) (@lem4425346 A K i k z t)). Qed.
Lemma lem4425348 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : ((term862 A K x i k z t) = (term863 A K x i k z t)) = ((term836 A K x i k z t) = (term881 A K x i k z t)).
Proof. exact (MK_COMB (@lem4425336 A K x i k z t) (@lem4425347 A K x i k z t)). Qed.
Lemma lem4425349 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term836 A K x i k z t) = (term881 A K x i k z t).
Proof. exact (EQ_MP (@lem4425348 A K x i k z t) (@lem4425326 A K x i k z t)). Qed.
Lemma lem4425446 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term840 A K s x i k z t) = (term882 A K s x i k z t).
Proof. exact (MK_COMB (@lem4425322 A K x i k z s) (@lem4425349 A K x i k z t)). Qed.
Lemma lem4425448 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term148 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4425449 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term148 K P Q) = (term147 K P Q).
Proof. exact (@lem4425448 K P Q). Qed.
Lemma lem4425450 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term842 A K x i k z s) = (term841 A K x i k z s).
Proof. exact (@lem4425449 K (term843 A K i k x s) (term844 A K i k z s)). Qed.
Lemma lem4425451 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) : (term845 A K i k x s i') = (term807 A K i k x s i').
Proof. exact (eq_refl (term845 A K i k x s i')). Qed.
Lemma lem4425452 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) : (term852 A K i k x s) = (term843 A K i k x s).
Proof. exact (fun_ext (fun i' : K => @lem4425451 A K i k x s i')). Qed.
Lemma lem4425453 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4425454 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) : (term853 A K i k x s) = (term854 A K i k x s).
Proof. exact (MK_COMB (@lem4425453 K) (@lem4425452 A K i k x s)). Qed.
Lemma lem4425455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4425456 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) : (term855 A K i k x s) = (term856 A K i k x s).
Proof. exact (MK_COMB (@lem4425455) (@lem4425454 A K i k x s)). Qed.
Lemma lem4425457 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term847 A K i k z s i') = (term812 A K i k z s i').
Proof. exact (eq_refl (term847 A K i k z s i')). Qed.
Lemma lem4425458 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term857 A K i k z s) = (term844 A K i k z s).
Proof. exact (fun_ext (fun i' : K => @lem4425457 A K i k z s i')). Qed.
Lemma lem4425459 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4425460 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term858 A K i k z s) = (term859 A K i k z s).
Proof. exact (MK_COMB (@lem4425459 K) (@lem4425458 A K i k z s)). Qed.
Lemma lem4425461 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term842 A K x i k z s) = (term860 A K x i k z s).
Proof. exact (MK_COMB (@lem4425456 A K i k x s) (@lem4425460 A K i k z s)). Qed.
Lemma lem4425462 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4425463 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term883 A K x i k z s) = (term884 A K x i k z s).
Proof. exact (MK_COMB (@lem4425462) (@lem4425461 A K x i k z s)). Qed.
Lemma lem4425464 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) : (term845 A K i k x s i') = (term807 A K i k x s i').
Proof. exact (eq_refl (term845 A K i k x s i')). Qed.
Lemma lem4425465 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4425466 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) : (term846 A K i k x s i') = (term815 A K i k x s i').
Proof. exact (MK_COMB (@lem4425465) (@lem4425464 A K i k x s i')). Qed.
Lemma lem4425467 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term847 A K i k z s i') = (term812 A K i k z s i').
Proof. exact (eq_refl (term847 A K i k z s i')). Qed.
Lemma lem4425468 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term848 A K x i k z s i') = (term817 A K x i k z s i').
Proof. exact (MK_COMB (@lem4425466 A K i k x s i') (@lem4425467 A K i k z s i')). Qed.
Lemma lem4425469 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term849 A K x i k z s) = (term826 A K x i k z s).
Proof. exact (fun_ext (fun i' : K => @lem4425468 A K x i k z s i')). Qed.
Lemma lem4425470 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4425471 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term841 A K x i k z s) = (term827 A K x i k z s).
Proof. exact (MK_COMB (@lem4425470 K) (@lem4425469 A K x i k z s)). Qed.
Lemma lem4425472 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : ((term842 A K x i k z s) = (term841 A K x i k z s)) = ((term860 A K x i k z s) = (term827 A K x i k z s)).
Proof. exact (MK_COMB (@lem4425463 A K x i k z s) (@lem4425471 A K x i k z s)). Qed.
Lemma lem4425473 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term860 A K x i k z s) = (term827 A K x i k z s).
Proof. exact (EQ_MP (@lem4425472 A K x i k z s) (@lem4425450 A K x i k z s)). Qed.
Lemma lem4425474 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4425475 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term861 A K x i k z s) = (term838 A K x i k z s).
Proof. exact (MK_COMB (@lem4425474) (@lem4425473 A K x i k z s)). Qed.
Lemma lem4425476 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term881 A K x i k z t) = (term881 A K x i k z t).
Proof. exact (eq_refl (term881 A K x i k z t)). Qed.
Lemma lem4425477 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term882 A K s x i k z t) = (term885 A K s x i k z t).
Proof. exact (MK_COMB (@lem4425475 A K x i k z s) (@lem4425476 A K x i k z t)). Qed.
Lemma lem4425479 {A : Type'} (P : A -> Prop) (Q : Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4425480 {K : Type'} (P : K -> Prop) (Q : Prop) : (term266 K P Q) = (term267 K P Q).
Proof. exact (@lem4425479 K P Q). Qed.
Lemma lem4425481 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term886 A K s x i k z t) = (term887 A K s x i k z t).
Proof. exact (@lem4425480 K (term826 A K x i k z s) (term881 A K x i k z t)). Qed.
Lemma lem4425482 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term888 A K x i k z s i') = (term817 A K x i k z s i').
Proof. exact (eq_refl (term888 A K x i k z s i')). Qed.
Lemma lem4425483 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term889 A K x i k z s) = (term826 A K x i k z s).
Proof. exact (fun_ext (fun i' : K => @lem4425482 A K x i k z s i')). Qed.
Lemma lem4425484 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4425485 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term890 A K x i k z s) = (term827 A K x i k z s).
Proof. exact (MK_COMB (@lem4425484 K) (@lem4425483 A K x i k z s)). Qed.
Lemma lem4425486 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4425487 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term891 A K x i k z s) = (term838 A K x i k z s).
Proof. exact (MK_COMB (@lem4425486) (@lem4425485 A K x i k z s)). Qed.
Lemma lem4425488 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term881 A K x i k z t) = (term881 A K x i k z t).
Proof. exact (eq_refl (term881 A K x i k z t)). Qed.
Lemma lem4425489 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term886 A K s x i k z t) = (term885 A K s x i k z t).
Proof. exact (MK_COMB (@lem4425487 A K x i k z s) (@lem4425488 A K x i k z t)). Qed.
Lemma lem4425490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4425491 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term892 A K s x i k z t) = (term893 A K s x i k z t).
Proof. exact (MK_COMB (@lem4425490) (@lem4425489 A K s x i k z t)). Qed.
Lemma lem4425492 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term888 A K x i k z s i') = (term817 A K x i k z s i').
Proof. exact (eq_refl (term888 A K x i k z s i')). Qed.
Lemma lem4425493 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4425494 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term894 A K x i k z s i') = (term895 A K x i k z s i').
Proof. exact (MK_COMB (@lem4425493) (@lem4425492 A K x i k z s i')). Qed.
Lemma lem4425495 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term881 A K x i k z t) = (term881 A K x i k z t).
Proof. exact (eq_refl (term881 A K x i k z t)). Qed.
Lemma lem4425496 {A K : Type'} (s : type1470 A K) (i' : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term896 A K s i' x i k z t) = (term897 A K s i' x i k z t).
Proof. exact (MK_COMB (@lem4425494 A K x i k z s i') (@lem4425495 A K x i k z t)). Qed.
Lemma lem4425497 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term898 A K s x i k z t) = (term899 A K s x i k z t).
Proof. exact (fun_ext (fun i' : K => @lem4425496 A K s i' x i k z t)). Qed.
Lemma lem4425498 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4425499 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term887 A K s x i k z t) = (term900 A K s x i k z t).
Proof. exact (MK_COMB (@lem4425498 K) (@lem4425497 A K s x i k z t)). Qed.
Lemma lem4425500 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : ((term886 A K s x i k z t) = (term887 A K s x i k z t)) = ((term885 A K s x i k z t) = (term900 A K s x i k z t)).
Proof. exact (MK_COMB (@lem4425491 A K s x i k z t) (@lem4425499 A K s x i k z t)). Qed.
Lemma lem4425501 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term885 A K s x i k z t) = (term900 A K s x i k z t).
Proof. exact (EQ_MP (@lem4425500 A K s x i k z t) (@lem4425481 A K s x i k z t)). Qed.
Lemma lem4425502 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term882 A K s x i k z t) = (term900 A K s x i k z t).
Proof. exact (TRANS (@lem4425477 A K s x i k z t) (@lem4425501 A K s x i k z t)). Qed.
Lemma lem4425503 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term840 A K s x i k z t) = (term900 A K s x i k z t).
Proof. exact (TRANS (@lem4425446 A K s x i k z t) (@lem4425502 A K s x i k z t)). Qed.
Lemma lem4425504 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term781 A K s x i k z t) = (term900 A K s x i k z t).
Proof. exact (TRANS (@lem4425197 A K s x i k z t) (@lem4425503 A K s x i k z t)). Qed.
Lemma lem4425505 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term781 A K s x i k z t) : term900 A K s x i k z t.
Proof. exact (EQ_MP (@lem4425504 A K s x i k z t) (@lem4425041 A K s x i k z t h1)). Qed.
Lemma lem4425511 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (h1 : term518 A K x t i) : term518 A K x t i.
Proof. exact (h1). Qed.
Lemma lem4425512 {A K : Type'} (s : type1470 A K) (i' : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term897 A K s i' x i k z t) : term897 A K s i' x i k z t.
Proof. exact (h1). Qed.
Lemma lem4425531 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term444 A K k z s i) = (term444 A K k z s i).
Proof. exact (eq_refl (term444 A K k z s i)). Qed.
Lemma lem4425532 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term446 A K k z s) = (term446 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4425531 A K k z s i)). Qed.
Lemma lem4425533 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4425534 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term447 A K k z s) = (term447 A K k z s).
Proof. exact (MK_COMB (@lem4425533 K) (@lem4425532 A K k z s)). Qed.
Lemma lem4425535 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term429 A K k z s) : term447 A K k z s.
Proof. exact (EQ_MP (@lem4425534 A K k z s) (@lem4425109 A K k z s h1)). Qed.
Lemma lem4425541 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4425549 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (h1 : term30 A K x s i) : term30 A K x s i.
Proof. exact (h1). Qed.
Lemma lem4425559 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (h1 : term518 A K x t i) : term518 A K x t i.
Proof. exact (h1). Qed.
Lemma lem4425586 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (i' : K) : (term831 A K i k z t i') = (term831 A K i k z t i').
Proof. exact (eq_refl (term831 A K i k z t i')). Qed.
Lemma lem4425587 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term865 A K i k z t) = (term865 A K i k z t).
Proof. exact (fun_ext (fun i' : K => @lem4425586 A K i k z t i')). Qed.
Lemma lem4425588 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4425589 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term880 A K i k z t) = (term880 A K i k z t).
Proof. exact (MK_COMB (@lem4425588 K) (@lem4425587 A K i k z t)). Qed.
Lemma lem4425616 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) (i' : K) : (term829 A K i k x t i') = (term829 A K i k x t i').
Proof. exact (eq_refl (term829 A K i k x t i')). Qed.
Lemma lem4425617 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) : (term864 A K i k x t) = (term864 A K i k x t).
Proof. exact (fun_ext (fun i' : K => @lem4425616 A K i k x t i')). Qed.
Lemma lem4425618 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4425619 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) : (term875 A K i k x t) = (term875 A K i k x t).
Proof. exact (MK_COMB (@lem4425618 K) (@lem4425617 A K i k x t)). Qed.
Lemma lem4425620 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4425621 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) : (term877 A K i k x t) = (term877 A K i k x t).
Proof. exact (MK_COMB (@lem4425620) (@lem4425619 A K i k x t)). Qed.
Lemma lem4425622 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term881 A K x i k z t) = (term881 A K x i k z t).
Proof. exact (MK_COMB (@lem4425621 A K i k x t) (@lem4425589 A K i k z t)). Qed.
Lemma lem4425681 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term895 A K x i k z s i') = (term895 A K x i k z s i').
Proof. exact (eq_refl (term895 A K x i k z s i')). Qed.
Lemma lem4425682 {A K : Type'} (s : type1470 A K) (i' : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) : (term897 A K s i' x i k z t) = (term897 A K s i' x i k z t).
Proof. exact (MK_COMB (@lem4425681 A K x i k z s i') (@lem4425622 A K x i k z t)). Qed.
Lemma lem4425683 {A K : Type'} (s : type1470 A K) (i' : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term897 A K s i' x i k z t) : term897 A K s i' x i k z t.
Proof. exact (EQ_MP (@lem4425682 A K s i' x i k z t) (@lem4425512 A K s i' x i k z t h1)). Qed.
Lemma lem4425684 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term817 A K x i k z s i') : term817 A K x i k z s i'.
Proof. exact (h1). Qed.
Lemma lem4425685 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term881 A K x i k z t) : term881 A K x i k z t.
Proof. exact (h1). Qed.
Lemma lem4425686 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) (h1 : term807 A K i k x s i') : term807 A K i k x s i'.
Proof. exact (h1). Qed.
Lemma lem4425687 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term812 A K i k z s i') : term812 A K i k z s i'.
Proof. exact (h1). Qed.
Lemma lem4425688 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) (h1 : term807 A K i k x s i') : term803 A K k x s i'.
Proof. exact (proj2 (@lem4425686 A K i k x s i' h1)). Qed.
Lemma lem4425692 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term812 A K i k z s i') : term450 A K k z s i'.
Proof. exact (proj2 (@lem4425687 A K i k z s i' h1)). Qed.
Lemma lem4425697 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term881 A K x i k z t) : term875 A K i k x t.
Proof. exact (proj1 (@lem4425685 A K x i k z t h1)). Qed.
Lemma lem4425718 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (h1 : term30 A K x s i) : term30 A K x s i.
Proof. exact (h1). Qed.
Lemma lem4425742 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term444 A K k z s i) = (term444 A K k z s i).
Proof. exact (eq_refl (term444 A K k z s i)). Qed.
Lemma lem4425743 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term446 A K k z s) = (term446 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4425742 A K k z s i)). Qed.
Lemma lem4425744 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4425746 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term447 A K k z s) = (term447 A K k z s).
Proof. exact (MK_COMB (@lem4425744 K) (@lem4425743 A K k z s)). Qed.
Lemma lem4425747 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term429 A K k z s) : term447 A K k z s.
Proof. exact (EQ_MP (@lem4425746 A K k z s) (@lem4425535 A K k z s h1)). Qed.
Lemma lem4425788 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4425796 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (h1 : term518 A K x t i) : term518 A K x t i.
Proof. exact (h1). Qed.
Lemma lem4425810 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) (i' : K) : (term829 A K i k x t i') = (term829 A K i k x t i').
Proof. exact (eq_refl (term829 A K i k x t i')). Qed.
Lemma lem4425811 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) : (term864 A K i k x t) = (term864 A K i k x t).
Proof. exact (fun_ext (fun i' : K => @lem4425810 A K i k x t i')). Qed.
Lemma lem4425812 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4425814 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) : (term875 A K i k x t) = (term875 A K i k x t).
Proof. exact (MK_COMB (@lem4425812 K) (@lem4425811 A K i k x t)). Qed.
Lemma lem4425815 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term881 A K x i k z t) : term875 A K i k x t.
Proof. exact (EQ_MP (@lem4425814 A K i k x t) (@lem4425697 A K x i k z t h1)). Qed.
Lemma lem4425838 {A K : Type'} (_50927 : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term429 A K k z s) : term901 A K k z s _50927.
Proof. exact (@lem4425747 A K k z s h1 _50927). Qed.
Lemma lem4425839 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_50927 : K) : (term901 A K k z s _50927) = (term444 A K k z s _50927).
Proof. exact (eq_refl (term901 A K k z s _50927)). Qed.
Lemma lem4425844 {A K : Type'} (_50929 : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term881 A K x i k z t) : term866 A K i k x t _50929.
Proof. exact (@lem4425815 A K x i k z t h1 _50929). Qed.
Lemma lem4425845 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) (_50929 : K) : (term866 A K i k x t _50929) = (term829 A K i k x t _50929).
Proof. exact (eq_refl (term866 A K i k x t _50929)). Qed.
Lemma lem4425859 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (h1 : term30 A K x s i) : term30 A K x s i.
Proof. exact (h1). Qed.
Lemma lem4425863 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) (h1 : term807 A K i k x s i') : i' = i.
Proof. exact (proj1 (@lem4425686 A K i k x s i' h1)). Qed.
Lemma lem4425867 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) (h1 : term807 A K i k x s i') : term518 A K x s i'.
Proof. exact (proj2 (@lem4425688 A K i k x s i' h1)). Qed.
Lemma lem4425873 {A K : Type'} (_50927 : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term429 A K k z s) : term444 A K k z s _50927.
Proof. exact (EQ_MP (@lem4425839 A K k z s _50927) (@lem4425838 A K _50927 k z s h1)). Qed.
Lemma lem4425885 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term812 A K i k z s i') : term481 A K z s i'.
Proof. exact (proj2 (@lem4425692 A K i k z s i' h1)). Qed.
Lemma lem4425893 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4425897 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (h1 : term518 A K x t i) : term518 A K x t i.
Proof. exact (h1). Qed.
Lemma lem4425907 {A K : Type'} (_50929 : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term881 A K x i k z t) : term829 A K i k x t _50929.
Proof. exact (EQ_MP (@lem4425845 A K i k x t _50929) (@lem4425844 A K _50929 x i k z t h1)). Qed.
Lemma lem4425973 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (h1 : term30 A K x s i) : term30 A K x s i.
Proof. exact (h1). Qed.
Lemma lem4426001 {A K : Type'} (x : A) (s : type1470 A K) : (term902 A K x s) = (term902 A K x s).
Proof. exact (eq_refl (term902 A K x s)). Qed.
Lemma lem4426002 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) (h1 : term807 A K i k x s i') : (term903 A K x s i') = (term903 A K x s i).
Proof. exact (MK_COMB (@lem4426001 A K x s) (@lem4425863 A K i k x s i' h1)). Qed.
Lemma lem4426003 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term903 A K x s i) = (term518 A K x s i).
Proof. exact (eq_refl (term903 A K x s i)). Qed.
Lemma lem4426004 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term904 A K x s i') = (term904 A K x s i').
Proof. exact (eq_refl (term904 A K x s i')). Qed.
Lemma lem4426005 {A K : Type'} (i' : K) (x : A) (s : type1470 A K) (i : K) : ((term903 A K x s i') = (term903 A K x s i)) = ((term903 A K x s i') = (term518 A K x s i)).
Proof. exact (MK_COMB (@lem4426004 A K x s i') (@lem4426003 A K x s i)). Qed.
Lemma lem4426006 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term903 A K x s i') = (term518 A K x s i').
Proof. exact (eq_refl (term903 A K x s i')). Qed.
Lemma lem4426007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4426008 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term904 A K x s i') = (term905 A K x s i').
Proof. exact (MK_COMB (@lem4426007) (@lem4426006 A K x s i')). Qed.
Lemma lem4426009 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term518 A K x s i) = (term518 A K x s i).
Proof. exact (eq_refl (term518 A K x s i)). Qed.
Lemma lem4426010 {A K : Type'} (i' : K) (x : A) (s : type1470 A K) (i : K) : ((term903 A K x s i') = (term518 A K x s i)) = ((term518 A K x s i') = (term518 A K x s i)).
Proof. exact (MK_COMB (@lem4426008 A K x s i') (@lem4426009 A K x s i)). Qed.
Lemma lem4426011 {A K : Type'} (i' : K) (x : A) (s : type1470 A K) (i : K) : ((term903 A K x s i') = (term903 A K x s i)) = ((term518 A K x s i') = (term518 A K x s i)).
Proof. exact (TRANS (@lem4426005 A K i' x s i) (@lem4426010 A K i' x s i)). Qed.
Lemma lem4426012 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) (h1 : term807 A K i k x s i') : (term518 A K x s i') = (term518 A K x s i).
Proof. exact (EQ_MP (@lem4426011 A K i' x s i) (@lem4426002 A K i k x s i' h1)). Qed.
Lemma lem4426013 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) (h1 : term807 A K i k x s i') : term518 A K x s i.
Proof. exact (EQ_MP (@lem4426012 A K i k x s i' h1) (@lem4425867 A K i k x s i' h1)). Qed.
Lemma lem4426015 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (h1 : term30 A K x s i) : term30 A K x s i.
Proof. exact (h1). Qed.
Lemma lem4426016 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (h1 : term30 A K x s i) : term906 A K x s i.
Proof. exact (fun h0 : term518 A K x s i => @lem4426015 A K x s i h1). Qed.
Lemma lem4426018 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4426019 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term906 A K x s i) = (term30 A K x s i).
Proof. exact (@lem4426018 (term30 A K x s i)). Qed.
Lemma lem4426020 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (h1 : term30 A K x s i) : term30 A K x s i.
Proof. exact (EQ_MP (@lem4426019 A K x s i) (@lem4426016 A K x s i h1)). Qed.
Lemma lem4426023 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4426025 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term518 A K x s i) = (term907 A K x s i).
Proof. exact (@lem4426023 (term30 A K x s i)). Qed.
Lemma lem4426028 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) (h1 : term807 A K i k x s i') : term907 A K x s i.
Proof. exact (EQ_MP (@lem4426025 A K x s i) (@lem4426013 A K i k x s i' h1)). Qed.
Lemma lem4426031 {A K : Type'} (k : K -> Prop) (i' : K) (x : A) (s : type1470 A K) (i : K) (h1 : term807 A K i k x s i') (h2 : term30 A K x s i) : False.
Proof. exact (@lem4426028 A K i k x s i' h1 (@lem4426020 A K x s i h2)). Qed.
Lemma lem4426032 {A K : Type'} (k : K -> Prop) (i' : K) (x : A) (s : type1470 A K) (i : K) (h1 : term807 A K i k x s i') (h2 : term30 A K x s i) : term337.
Proof. exact (fun h0 : ~ False => @lem4426031 A K k i' x s i h1 h2). Qed.
Lemma lem4426034 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4426035 : term337 = False.
Proof. exact (@lem4426034 False). Qed.
Lemma lem4426036 {A K : Type'} (k : K -> Prop) (i' : K) (x : A) (s : type1470 A K) (i : K) (h1 : term807 A K i k x s i') (h2 : term30 A K x s i) : False.
Proof. exact (EQ_MP (@lem4426035) (@lem4426032 A K k i' x s i h1 h2)). Qed.
Lemma lem4426108 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term812 A K i k z s i') : @IN K i' k.
Proof. exact (proj1 (@lem4425692 A K i k z s i' h1)). Qed.
Lemma lem4426109 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term812 A K i k z s i') : term507 K i' k.
Proof. exact (fun h0 : term489 K i' k => @lem4426108 A K i k z s i' h1). Qed.
Lemma lem4426111 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4426112 {K : Type'} (i' : K) (k : K -> Prop) : (term507 K i' k) = (@IN K i' k).
Proof. exact (@lem4426111 (@IN K i' k)). Qed.
Lemma lem4426113 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term812 A K i k z s i') : @IN K i' k.
Proof. exact (EQ_MP (@lem4426112 K i' k) (@lem4426109 A K i k z s i' h1)). Qed.
Lemma lem4426119 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4426120 {A K : Type'} (z : K -> A) (s : type1470 A K) (_50927 : K) (k : K -> Prop) : (term444 A K k z s _50927) = (term908 A K z s _50927 k).
Proof. exact (@lem4426119 (term445 A K z s _50927) (term489 K _50927 k)). Qed.
Lemma lem4426126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4426127 {A K : Type'} (z : K -> A) (s : type1470 A K) (_50927 : K) (k : K -> Prop) : (term909 A K k z s _50927) = (term910 A K z s _50927 k).
Proof. exact (MK_COMB (@lem4426126) (@lem4426120 A K z s _50927 k)). Qed.
Lemma lem4426133 {A K : Type'} (z : K -> A) (s : type1470 A K) (_50927 : K) (k : K -> Prop) : (term908 A K z s _50927 k) = (term908 A K z s _50927 k).
Proof. exact (eq_refl (term908 A K z s _50927 k)). Qed.
Lemma lem4426134 {A K : Type'} (z : K -> A) (s : type1470 A K) (_50927 : K) (k : K -> Prop) : ((term444 A K k z s _50927) = (term908 A K z s _50927 k)) = ((term908 A K z s _50927 k) = (term908 A K z s _50927 k)).
Proof. exact (MK_COMB (@lem4426127 A K z s _50927 k) (@lem4426133 A K z s _50927 k)). Qed.
Lemma lem4426136 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4426137 (x : Prop) : (x = x) = True.
Proof. exact (@lem4426136 Prop x). Qed.
Lemma lem4426138 {A K : Type'} (z : K -> A) (s : type1470 A K) (_50927 : K) (k : K -> Prop) : ((term908 A K z s _50927 k) = (term908 A K z s _50927 k)) = True.
Proof. exact (@lem4426137 (term908 A K z s _50927 k)). Qed.
Lemma lem4426139 {A K : Type'} (z : K -> A) (s : type1470 A K) (_50927 : K) (k : K -> Prop) : ((term444 A K k z s _50927) = (term908 A K z s _50927 k)) = True.
Proof. exact (TRANS (@lem4426134 A K z s _50927 k) (@lem4426138 A K z s _50927 k)). Qed.
Lemma lem4426140 {A K : Type'} (z : K -> A) (s : type1470 A K) (_50927 : K) (k : K -> Prop) : True = ((term444 A K k z s _50927) = (term908 A K z s _50927 k)).
Proof. exact (SYM (@lem4426139 A K z s _50927 k)). Qed.
Lemma lem4426141 {A K : Type'} (z : K -> A) (s : type1470 A K) (_50927 : K) (k : K -> Prop) : (term444 A K k z s _50927) = (term908 A K z s _50927 k).
Proof. exact (EQ_MP (@lem4426140 A K z s _50927 k) (@lem0)). Qed.
Lemma lem4426142 {A K : Type'} (_50927 : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term429 A K k z s) : term908 A K z s _50927 k.
Proof. exact (EQ_MP (@lem4426141 A K z s _50927 k) (@lem4425873 A K _50927 k z s h1)). Qed.
Lemma lem4426144 (b : Prop) (a : Prop) : (a \/ b) = (term328 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4426145 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_50927 : K) : (term908 A K z s _50927 k) = (term911 A K k z s _50927).
Proof. exact (@lem4426144 (term489 K _50927 k) (term445 A K z s _50927)). Qed.
Lemma lem4426147 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4426148 {K : Type'} (_50927 : K) (k : K -> Prop) : (term512 K _50927 k) = (@IN K _50927 k).
Proof. exact (@lem4426147 (@IN K _50927 k)). Qed.
Lemma lem4426149 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4426150 {K : Type'} (_50927 : K) (k : K -> Prop) : (term513 K _50927 k) = (term42 K _50927 k).
Proof. exact (MK_COMB (@lem4426149) (@lem4426148 K _50927 k)). Qed.
Lemma lem4426151 {A K : Type'} (z : K -> A) (s : type1470 A K) (_50927 : K) : (term445 A K z s _50927) = (term445 A K z s _50927).
Proof. exact (eq_refl (term445 A K z s _50927)). Qed.
Lemma lem4426152 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_50927 : K) : (term911 A K k z s _50927) = (term427 A K k z s _50927).
Proof. exact (MK_COMB (@lem4426150 K _50927 k) (@lem4426151 A K z s _50927)). Qed.
Lemma lem4426153 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_50927 : K) : (term908 A K z s _50927 k) = (term427 A K k z s _50927).
Proof. exact (TRANS (@lem4426145 A K k z s _50927) (@lem4426152 A K k z s _50927)). Qed.
Lemma lem4426156 {A K : Type'} (_50927 : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term429 A K k z s) : term427 A K k z s _50927.
Proof. exact (EQ_MP (@lem4426153 A K k z s _50927) (@lem4426142 A K _50927 k z s h1)). Qed.
Lemma lem4426157 {A K : Type'} (_50927 : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term429 A K k z s) : term427 A K k z s _50927.
Proof. exact (@lem4426156 A K _50927 k z s h1). Qed.
Lemma lem4426158 {A K : Type'} (i' : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term429 A K k z s) : term427 A K k z s i'.
Proof. exact (@lem4426157 A K i' k z s h1). Qed.
Lemma lem4426161 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term429 A K k z s) (h2 : term812 A K i k z s i') : term445 A K z s i'.
Proof. exact (@lem4426158 A K i' k z s h1 (@lem4426113 A K i k z s i' h2)). Qed.
Lemma lem4426162 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term429 A K k z s) (h2 : term812 A K i k z s i') : term912 A K z s i'.
Proof. exact (fun h0 : term481 A K z s i' => @lem4426161 A K i k z s i' h1 h2). Qed.
Lemma lem4426164 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4426165 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) : (term912 A K z s i') = (term445 A K z s i').
Proof. exact (@lem4426164 (term445 A K z s i')). Qed.
Lemma lem4426166 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term429 A K k z s) (h2 : term812 A K i k z s i') : term445 A K z s i'.
Proof. exact (EQ_MP (@lem4426165 A K z s i') (@lem4426162 A K i k z s i' h1 h2)). Qed.
Lemma lem4426169 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4426171 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) : (term481 A K z s i') = (term913 A K z s i').
Proof. exact (@lem4426169 (term445 A K z s i')). Qed.
Lemma lem4426174 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term812 A K i k z s i') : term913 A K z s i'.
Proof. exact (EQ_MP (@lem4426171 A K z s i') (@lem4425885 A K i k z s i' h1)). Qed.
Lemma lem4426177 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term429 A K k z s) (h2 : term812 A K i k z s i') : False.
Proof. exact (@lem4426174 A K i k z s i' h2 (@lem4426166 A K i k z s i' h1 h2)). Qed.
Lemma lem4426178 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term429 A K k z s) (h2 : term812 A K i k z s i') : term337.
Proof. exact (fun h0 : ~ False => @lem4426177 A K i k z s i' h1 h2). Qed.
Lemma lem4426180 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4426181 : term337 = False.
Proof. exact (@lem4426180 False). Qed.
Lemma lem4426182 {A K : Type'} (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term429 A K k z s) (h2 : term812 A K i k z s i') : False.
Proof. exact (EQ_MP (@lem4426181) (@lem4426178 A K i k z s i' h1 h2)). Qed.
Lemma lem4426254 {K : Type'} (x : K) : x = x.
Proof. exact (@lem21386 K x). Qed.
Lemma lem4426255 {K : Type'} (x : K) : x = x.
Proof. exact (@lem4426254 K x). Qed.
Lemma lem4426256 {K : Type'} (i : K) : i = i.
Proof. exact (@lem4426255 K i). Qed.
Lemma lem4426257 {K : Type'} (i : K) : term914 K i.
Proof. exact (fun h0 : term915 K i => @lem4426256 K i). Qed.
Lemma lem4426259 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4426260 {K : Type'} (i : K) : (term914 K i) = (i = i).
Proof. exact (@lem4426259 (i = i)). Qed.
Lemma lem4426261 {K : Type'} (i : K) : i = i.
Proof. exact (EQ_MP (@lem4426260 K i) (@lem4426257 K i)). Qed.
Lemma lem4426263 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4426264 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : term507 K i k.
Proof. exact (fun h0 : term489 K i k => @lem4426263 K i k h1). Qed.
Lemma lem4426266 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4426267 {K : Type'} (i : K) (k : K -> Prop) : (term507 K i k) = (@IN K i k).
Proof. exact (@lem4426266 (@IN K i k)). Qed.
Lemma lem4426268 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (EQ_MP (@lem4426267 K i k) (@lem4426264 K i k h1)). Qed.
Lemma lem4426286 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4426287 {A K : Type'} (x : A) (t : type1470 A K) (_50929 : K) (k : K -> Prop) : (term519 A K k x t _50929) = (term520 A K x t _50929 k).
Proof. exact (@lem4426286 (term30 A K x t _50929) (term489 K _50929 k)). Qed.
Lemma lem4426293 {K : Type'} (_50929 : K) (i : K) : (term828 K _50929 i) = (term828 K _50929 i).
Proof. exact (eq_refl (term828 K _50929 i)). Qed.
Lemma lem4426294 {A K : Type'} (i : K) (x : A) (t : type1470 A K) (_50929 : K) (k : K -> Prop) : (term829 A K i k x t _50929) = (term916 A K i x t _50929 k).
Proof. exact (MK_COMB (@lem4426293 K _50929 i) (@lem4426287 A K x t _50929 k)). Qed.
Lemma lem4426298 (q : Prop) (p : Prop) (r : Prop) : (term516 p q r) = (term516 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4426299 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (_50929 : K) (k : K -> Prop) : (term916 A K i x t _50929 k) = (term917 A K x t i _50929 k).
Proof. exact (@lem4426298 (term30 A K x t _50929) (term809 K _50929 i) (term489 K _50929 k)). Qed.
Lemma lem4426317 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (_50929 : K) (k : K -> Prop) : (term829 A K i k x t _50929) = (term917 A K x t i _50929 k).
Proof. exact (TRANS (@lem4426294 A K i x t _50929 k) (@lem4426299 A K x t i _50929 k)). Qed.
Lemma lem4426318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4426319 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (_50929 : K) (k : K -> Prop) : (term918 A K i k x t _50929) = (term919 A K x t i _50929 k).
Proof. exact (MK_COMB (@lem4426318) (@lem4426317 A K x t i _50929 k)). Qed.
Lemma lem4426337 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (_50929 : K) (k : K -> Prop) : (term917 A K x t i _50929 k) = (term917 A K x t i _50929 k).
Proof. exact (eq_refl (term917 A K x t i _50929 k)). Qed.
Lemma lem4426338 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (_50929 : K) (k : K -> Prop) : ((term829 A K i k x t _50929) = (term917 A K x t i _50929 k)) = ((term917 A K x t i _50929 k) = (term917 A K x t i _50929 k)).
Proof. exact (MK_COMB (@lem4426319 A K x t i _50929 k) (@lem4426337 A K x t i _50929 k)). Qed.
Lemma lem4426340 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4426341 (x : Prop) : (x = x) = True.
Proof. exact (@lem4426340 Prop x). Qed.
Lemma lem4426342 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (_50929 : K) (k : K -> Prop) : ((term917 A K x t i _50929 k) = (term917 A K x t i _50929 k)) = True.
Proof. exact (@lem4426341 (term917 A K x t i _50929 k)). Qed.
Lemma lem4426343 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (_50929 : K) (k : K -> Prop) : ((term829 A K i k x t _50929) = (term917 A K x t i _50929 k)) = True.
Proof. exact (TRANS (@lem4426338 A K x t i _50929 k) (@lem4426342 A K x t i _50929 k)). Qed.
Lemma lem4426344 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (_50929 : K) (k : K -> Prop) : True = ((term829 A K i k x t _50929) = (term917 A K x t i _50929 k)).
Proof. exact (SYM (@lem4426343 A K x t i _50929 k)). Qed.
Lemma lem4426345 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (_50929 : K) (k : K -> Prop) : (term829 A K i k x t _50929) = (term917 A K x t i _50929 k).
Proof. exact (EQ_MP (@lem4426344 A K x t i _50929 k) (@lem0)). Qed.
Lemma lem4426346 {A K : Type'} (_50929 : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term881 A K x i k z t) : term917 A K x t i _50929 k.
Proof. exact (EQ_MP (@lem4426345 A K x t i _50929 k) (@lem4425907 A K _50929 x i k z t h1)). Qed.
Lemma lem4426348 (b : Prop) (a : Prop) : (a \/ b) = (term328 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4426349 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) (_50929 : K) : (term917 A K x t i _50929 k) = (term920 A K i k x t _50929).
Proof. exact (@lem4426348 (term921 K i _50929 k) (term30 A K x t _50929)). Qed.
Lemma lem4426351 (a : Prop) (b : Prop) : (term531 a b) = (term532 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4426352 {K : Type'} (i : K) (_50929 : K) (k : K -> Prop) : (term922 K i _50929 k) = (term923 K i _50929 k).
Proof. exact (@lem4426351 (term809 K _50929 i) (term489 K _50929 k)). Qed.
Lemma lem4426354 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4426355 {K : Type'} (_50929 : K) (i : K) : (term801 K _50929 i) = (_50929 = i).
Proof. exact (@lem4426354 (_50929 = i)). Qed.
Lemma lem4426356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4426357 {K : Type'} (_50929 : K) (i : K) : (term804 K _50929 i) = (term805 K _50929 i).
Proof. exact (MK_COMB (@lem4426356) (@lem4426355 K _50929 i)). Qed.
Lemma lem4426359 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4426360 {K : Type'} (_50929 : K) (k : K -> Prop) : (term512 K _50929 k) = (@IN K _50929 k).
Proof. exact (@lem4426359 (@IN K _50929 k)). Qed.
Lemma lem4426361 {K : Type'} (i : K) (_50929 : K) (k : K -> Prop) : (term923 K i _50929 k) = (term924 K i _50929 k).
Proof. exact (MK_COMB (@lem4426357 K _50929 i) (@lem4426360 K _50929 k)). Qed.
Lemma lem4426362 {K : Type'} (i : K) (_50929 : K) (k : K -> Prop) : (term922 K i _50929 k) = (term924 K i _50929 k).
Proof. exact (TRANS (@lem4426352 K i _50929 k) (@lem4426361 K i _50929 k)). Qed.
Lemma lem4426363 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4426364 {K : Type'} (i : K) (_50929 : K) (k : K -> Prop) : (term925 K i _50929 k) = (term926 K i _50929 k).
Proof. exact (MK_COMB (@lem4426363) (@lem4426362 K i _50929 k)). Qed.
Lemma lem4426365 {A K : Type'} (x : A) (t : type1470 A K) (_50929 : K) : (term30 A K x t _50929) = (term30 A K x t _50929).
Proof. exact (eq_refl (term30 A K x t _50929)). Qed.
Lemma lem4426366 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) (_50929 : K) : (term920 A K i k x t _50929) = (term927 A K i k x t _50929).
Proof. exact (MK_COMB (@lem4426364 K i _50929 k) (@lem4426365 A K x t _50929)). Qed.
Lemma lem4426367 {A K : Type'} (i : K) (k : K -> Prop) (x : A) (t : type1470 A K) (_50929 : K) : (term917 A K x t i _50929 k) = (term927 A K i k x t _50929).
Proof. exact (TRANS (@lem4426349 A K i k x t _50929) (@lem4426366 A K i k x t _50929)). Qed.
Lemma lem4426369 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : term928 K i k.
Proof. exact (conj (@lem4426261 K i) (@lem4426268 K i k h1)). Qed.
Lemma lem4426371 {A K : Type'} (_50929 : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term881 A K x i k z t) : term927 A K i k x t _50929.
Proof. exact (EQ_MP (@lem4426367 A K i k x t _50929) (@lem4426346 A K _50929 x i k z t h1)). Qed.
Lemma lem4426372 {A K : Type'} (_50929 : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term881 A K x i k z t) : term927 A K i k x t _50929.
Proof. exact (@lem4426371 A K _50929 x i k z t h1). Qed.
Lemma lem4426373 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term881 A K x i k z t) : term929 A K k x t i.
Proof. exact (@lem4426372 A K i x i k z t h1). Qed.
Lemma lem4426376 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term881 A K x i k z t) (h2 : @IN K i k) : term30 A K x t i.
Proof. exact (@lem4426373 A K x i k z t h1 (@lem4426369 K i k h2)). Qed.
Lemma lem4426377 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term881 A K x i k z t) (h2 : @IN K i k) : term906 A K x t i.
Proof. exact (fun h0 : term518 A K x t i => @lem4426376 A K x z t i k h1 h2). Qed.
Lemma lem4426379 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4426380 {A K : Type'} (x : A) (t : type1470 A K) (i : K) : (term906 A K x t i) = (term30 A K x t i).
Proof. exact (@lem4426379 (term30 A K x t i)). Qed.
Lemma lem4426381 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term881 A K x i k z t) (h2 : @IN K i k) : term30 A K x t i.
Proof. exact (EQ_MP (@lem4426380 A K x t i) (@lem4426377 A K x z t i k h1 h2)). Qed.
Lemma lem4426384 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4426386 {A K : Type'} (x : A) (t : type1470 A K) (i : K) : (term518 A K x t i) = (term907 A K x t i).
Proof. exact (@lem4426384 (term30 A K x t i)). Qed.
Lemma lem4426389 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (h1 : term518 A K x t i) : term907 A K x t i.
Proof. exact (EQ_MP (@lem4426386 A K x t i) (@lem4425897 A K x t i h1)). Qed.
Lemma lem4426392 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term518 A K x t i) (h2 : term881 A K x i k z t) (h3 : @IN K i k) : False.
Proof. exact (@lem4426389 A K x t i h1 (@lem4426381 A K x z t i k h2 h3)). Qed.
Lemma lem4426393 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term518 A K x t i) (h2 : term881 A K x i k z t) (h3 : @IN K i k) : term337.
Proof. exact (fun h0 : ~ False => @lem4426392 A K x z t i k h1 h2 h3). Qed.
Lemma lem4426395 (p : Prop) : (term323 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4426396 : term337 = False.
Proof. exact (@lem4426395 False). Qed.
Lemma lem4426397 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term518 A K x t i) (h2 : term881 A K x i k z t) (h3 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4426396) (@lem4426393 A K x z t i k h1 h2 h3)). Qed.
Lemma lem4426398 {A K : Type'} (k : K -> Prop) (i' : K) (x : A) (s : type1470 A K) (i : K) (h1 : term807 A K i k x s i') (h2 : term30 A K x s i) : (term30 A K x s i) = False.
Proof. exact (prop_ext (fun h3 : term30 A K x s i => @lem4426036 A K k i' x s i h1 h2) (fun h3 : False => @lem4425973 A K x s i h2)). Qed.
Lemma lem4426400 {A K : Type'} (k : K -> Prop) (i' : K) (x : A) (s : type1470 A K) (i : K) (h1 : term807 A K i k x s i') (h2 : term30 A K x s i) : False.
Proof. exact (EQ_MP (@lem4426398 A K k i' x s i h1 h2) (@lem4425973 A K x s i h2)). Qed.
Lemma lem4426401 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term518 A K x t i) (h2 : term881 A K x i k z t) (h3 : @IN K i k) : (term518 A K x t i) = False.
Proof. exact (prop_ext (fun h4 : term518 A K x t i => @lem4426397 A K x z t i k h1 h2 h3) (fun h4 : False => @lem4425897 A K x t i h1)). Qed.
Lemma lem4426402 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term518 A K x t i) (h2 : term881 A K x i k z t) (h3 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4426401 A K x z t i k h1 h2 h3) (@lem4425897 A K x t i h1)). Qed.
Lemma lem4426403 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term518 A K x t i) (h2 : term881 A K x i k z t) (h3 : @IN K i k) : (@IN K i k) = False.
Proof. exact (prop_ext (fun h4 : @IN K i k => @lem4426402 A K x z t i k h1 h2 h3) (fun h4 : False => @lem4425893 K i k h3)). Qed.
Lemma lem4426404 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term518 A K x t i) (h2 : term881 A K x i k z t) (h3 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4426403 A K x z t i k h1 h2 h3) (@lem4425893 K i k h3)). Qed.
Lemma lem4426405 {A K : Type'} (k : K -> Prop) (i' : K) (x : A) (s : type1470 A K) (i : K) (h1 : term807 A K i k x s i') (h2 : term30 A K x s i) : (term30 A K x s i) = False.
Proof. exact (prop_ext (fun h3 : term30 A K x s i => @lem4426400 A K k i' x s i h1 h2) (fun h3 : False => @lem4425859 A K x s i h2)). Qed.
Lemma lem4426406 {A K : Type'} (k : K -> Prop) (i' : K) (x : A) (s : type1470 A K) (i : K) (h1 : term807 A K i k x s i') (h2 : term30 A K x s i) : False.
Proof. exact (EQ_MP (@lem4426405 A K k i' x s i h1 h2) (@lem4425859 A K x s i h2)). Qed.
Lemma lem4426407 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term518 A K x t i) (h2 : term881 A K x i k z t) (h3 : @IN K i k) : (term518 A K x t i) = False.
Proof. exact (prop_ext (fun h4 : term518 A K x t i => @lem4426404 A K x z t i k h1 h2 h3) (fun h4 : False => @lem4425796 A K x t i h1)). Qed.
Lemma lem4426408 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term518 A K x t i) (h2 : term881 A K x i k z t) (h3 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4426407 A K x z t i k h1 h2 h3) (@lem4425796 A K x t i h1)). Qed.
Lemma lem4426409 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term518 A K x t i) (h2 : term881 A K x i k z t) (h3 : @IN K i k) : (@IN K i k) = False.
Proof. exact (prop_ext (fun h4 : @IN K i k => @lem4426408 A K x z t i k h1 h2 h3) (fun h4 : False => @lem4425788 K i k h3)). Qed.
Lemma lem4426410 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term518 A K x t i) (h2 : term881 A K x i k z t) (h3 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4426409 A K x z t i k h1 h2 h3) (@lem4425788 K i k h3)). Qed.
Lemma lem4426411 {A K : Type'} (k : K -> Prop) (i' : K) (x : A) (s : type1470 A K) (i : K) (h1 : term807 A K i k x s i') (h2 : term30 A K x s i) : (term30 A K x s i) = False.
Proof. exact (prop_ext (fun h3 : term30 A K x s i => @lem4426406 A K k i' x s i h1 h2) (fun h3 : False => @lem4425718 A K x s i h2)). Qed.
Lemma lem4426412 {A K : Type'} (k : K -> Prop) (i' : K) (x : A) (s : type1470 A K) (i : K) (h1 : term807 A K i k x s i') (h2 : term30 A K x s i) : False.
Proof. exact (EQ_MP (@lem4426411 A K k i' x s i h1 h2) (@lem4425718 A K x s i h2)). Qed.
Lemma lem4426413 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term518 A K x t i) (h2 : term881 A K x i k z t) (h3 : @IN K i k) : (term518 A K x t i) = False.
Proof. exact (prop_ext (fun h4 : term518 A K x t i => @lem4426410 A K x z t i k h1 h2 h3) (fun h4 : False => @lem4425796 A K x t i h1)). Qed.
Lemma lem4426414 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term518 A K x t i) (h2 : term881 A K x i k z t) (h3 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4426413 A K x z t i k h1 h2 h3) (@lem4425796 A K x t i h1)). Qed.
Lemma lem4426415 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term518 A K x t i) (h2 : term881 A K x i k z t) (h3 : @IN K i k) : (@IN K i k) = False.
Proof. exact (prop_ext (fun h4 : @IN K i k => @lem4426414 A K x z t i k h1 h2 h3) (fun h4 : False => @lem4425788 K i k h3)). Qed.
Lemma lem4426416 {A K : Type'} (x : A) (z : K -> A) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term518 A K x t i) (h2 : term881 A K x i k z t) (h3 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4426415 A K x z t i k h1 h2 h3) (@lem4425788 K i k h3)). Qed.
Lemma lem4426417 {A K : Type'} (k : K -> Prop) (i' : K) (x : A) (s : type1470 A K) (i : K) (h1 : term807 A K i k x s i') (h2 : term30 A K x s i) : (term30 A K x s i) = False.
Proof. exact (prop_ext (fun h3 : term30 A K x s i => @lem4426412 A K k i' x s i h1 h2) (fun h3 : False => @lem4425718 A K x s i h2)). Qed.
Lemma lem4426418 {A K : Type'} (k : K -> Prop) (i' : K) (x : A) (s : type1470 A K) (i : K) (h1 : term807 A K i k x s i') (h2 : term30 A K x s i) : False.
Proof. exact (EQ_MP (@lem4426417 A K k i' x s i h1 h2) (@lem4425718 A K x s i h2)). Qed.
Lemma lem4426419 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term429 A K k z s) (h2 : term30 A K x s i) (h3 : term817 A K x i k z s i') : False.
Proof. exact (or_elim (@lem4425684 A K x i k z s i' h3) (fun h0 : term807 A K i k x s i' => @lem4426418 A K k i' x s i h0 h2) (fun h0 : term812 A K i k z s i' => @lem4426182 A K i k z s i' h1 h0)). Qed.
Lemma lem4426420 {A K : Type'} (s : type1470 A K) (i' : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term30 A K x s i) (h4 : @IN K i k) (h5 : term897 A K s i' x i k z t) : False.
Proof. exact (or_elim (@lem4425683 A K s i' x i k z t h5) (fun h0 : term817 A K x i k z s i' => @lem4426419 A K x i k z s i' h1 h3 h0) (fun h0 : term881 A K x i k z t => @lem4426416 A K x z t i k h2 h0 h4)). Qed.
Lemma lem4426421 {A K : Type'} (s : type1470 A K) (i' : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term30 A K x s i) (h4 : @IN K i k) (h5 : term897 A K s i' x i k z t) : (term897 A K s i' x i k z t) = False.
Proof. exact (prop_ext (fun h6 : term897 A K s i' x i k z t => @lem4426420 A K s i' x i k z t h1 h2 h3 h4 h5) (fun h6 : False => @lem4425683 A K s i' x i k z t h5)). Qed.
Lemma lem4426422 {A K : Type'} (s : type1470 A K) (i' : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term30 A K x s i) (h4 : @IN K i k) (h5 : term897 A K s i' x i k z t) : False.
Proof. exact (EQ_MP (@lem4426421 A K s i' x i k z t h1 h2 h3 h4 h5) (@lem4425683 A K s i' x i k z t h5)). Qed.
Lemma lem4426423 {A K : Type'} (s : type1470 A K) (i' : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term30 A K x s i) (h4 : @IN K i k) (h5 : term897 A K s i' x i k z t) : (term518 A K x t i) = False.
Proof. exact (prop_ext (fun h6 : term518 A K x t i => @lem4426422 A K s i' x i k z t h1 h2 h3 h4 h5) (fun h6 : False => @lem4425559 A K x t i h2)). Qed.
Lemma lem4426424 {A K : Type'} (s : type1470 A K) (i' : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term30 A K x s i) (h4 : @IN K i k) (h5 : term897 A K s i' x i k z t) : False.
Proof. exact (EQ_MP (@lem4426423 A K s i' x i k z t h1 h2 h3 h4 h5) (@lem4425559 A K x t i h2)). Qed.
Lemma lem4426425 {A K : Type'} (s : type1470 A K) (i' : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term30 A K x s i) (h4 : @IN K i k) (h5 : term897 A K s i' x i k z t) : (term30 A K x s i) = False.
Proof. exact (prop_ext (fun h6 : term30 A K x s i => @lem4426424 A K s i' x i k z t h1 h2 h3 h4 h5) (fun h6 : False => @lem4425549 A K x s i h3)). Qed.
Lemma lem4426426 {A K : Type'} (s : type1470 A K) (i' : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term30 A K x s i) (h4 : @IN K i k) (h5 : term897 A K s i' x i k z t) : False.
Proof. exact (EQ_MP (@lem4426425 A K s i' x i k z t h1 h2 h3 h4 h5) (@lem4425549 A K x s i h3)). Qed.
Lemma lem4426427 {A K : Type'} (s : type1470 A K) (i' : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term30 A K x s i) (h4 : @IN K i k) (h5 : term897 A K s i' x i k z t) : (@IN K i k) = False.
Proof. exact (prop_ext (fun h6 : @IN K i k => @lem4426426 A K s i' x i k z t h1 h2 h3 h4 h5) (fun h6 : False => @lem4425541 K i k h4)). Qed.
Lemma lem4426428 {A K : Type'} (s : type1470 A K) (i' : K) (x : A) (i : K) (k : K -> Prop) (z : K -> A) (t : type1470 A K) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term30 A K x s i) (h4 : @IN K i k) (h5 : term897 A K s i' x i k z t) : False.
Proof. exact (EQ_MP (@lem4426427 A K s i' x i k z t h1 h2 h3 h4 h5) (@lem4425541 K i k h4)). Qed.
Lemma lem4426429 {A K : Type'} (z : K -> A) (t : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term781 A K s x i k z t) (h4 : term30 A K x s i) (h5 : @IN K i k) : False.
Proof. exact (ex_elim (@lem4425505 A K s x i k z t h3) (fun i' : K => fun h0 : term899 A K s x i k z t i' => @lem4426428 A K s i' x i k z t h1 h2 h4 h5 h0)). Qed.
Lemma lem4426430 {A K : Type'} (z : K -> A) (t : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term781 A K s x i k z t) (h4 : term30 A K x s i) (h5 : @IN K i k) : (term518 A K x t i) = False.
Proof. exact (prop_ext (fun h6 : term518 A K x t i => @lem4426429 A K z t x s i k h1 h2 h3 h4 h5) (fun h6 : False => @lem4425511 A K x t i h2)). Qed.
Lemma lem4426431 {A K : Type'} (z : K -> A) (t : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term781 A K s x i k z t) (h4 : term30 A K x s i) (h5 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4426430 A K z t x s i k h1 h2 h3 h4 h5) (@lem4425511 A K x t i h2)). Qed.
Lemma lem4426432 {A K : Type'} (z : K -> A) (t : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term781 A K s x i k z t) (h4 : term30 A K x s i) (h5 : @IN K i k) : (term30 A K x s i) = False.
Proof. exact (prop_ext (fun h6 : term30 A K x s i => @lem4426431 A K z t x s i k h1 h2 h3 h4 h5) (fun h6 : False => @lem4425121 A K x s i h4)). Qed.
Lemma lem4426433 {A K : Type'} (z : K -> A) (t : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term781 A K s x i k z t) (h4 : term30 A K x s i) (h5 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4426432 A K z t x s i k h1 h2 h3 h4 h5) (@lem4425121 A K x s i h4)). Qed.
Lemma lem4426434 {A K : Type'} (z : K -> A) (t : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term781 A K s x i k z t) (h4 : term30 A K x s i) (h5 : @IN K i k) : (@IN K i k) = False.
Proof. exact (prop_ext (fun h6 : @IN K i k => @lem4426433 A K z t x s i k h1 h2 h3 h4 h5) (fun h6 : False => @lem4425115 K i k h5)). Qed.
Lemma lem4426435 {A K : Type'} (z : K -> A) (t : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term781 A K s x i k z t) (h4 : term30 A K x s i) (h5 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4426434 A K z t x s i k h1 h2 h3 h4 h5) (@lem4425115 K i k h5)). Qed.
Lemma lem4426436 {A K : Type'} (z : K -> A) (t : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term781 A K s x i k z t) (h4 : term30 A K x s i) (h5 : @IN K i k) : (term518 A K x t i) = False.
Proof. exact (prop_ext (fun h6 : term518 A K x t i => @lem4426435 A K z t x s i k h1 h2 h3 h4 h5) (fun h6 : False => @lem4425046 A K x t i h2)). Qed.
Lemma lem4426437 {A K : Type'} (z : K -> A) (t : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term518 A K x t i) (h3 : term781 A K s x i k z t) (h4 : term30 A K x s i) (h5 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4426436 A K z t x s i k h1 h2 h3 h4 h5) (@lem4425046 A K x t i h2)). Qed.
Lemma lem4426438 {A K : Type'} (z : K -> A) (t : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term781 A K s x i k z t) (h3 : term30 A K x s i) (h4 : @IN K i k) : term800 A K x t i.
Proof. exact (fun h0 : term518 A K x t i => @lem4426437 A K z t x s i k h1 h0 h2 h3 h4). Qed.
Lemma lem4426439 {A K : Type'} (z : K -> A) (t : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term781 A K s x i k z t) (h3 : term30 A K x s i) (h4 : @IN K i k) : term30 A K x t i.
Proof. exact (EQ_MP (@lem4425045 A K x t i) (@lem4426438 A K z t x s i k h1 h2 h3 h4)). Qed.
Lemma lem4426440 {A K : Type'} (t : type1470 A K) (z : K -> A) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term30 A K x s i) (h3 : @IN K i k) : term784 A K s k z x t i.
Proof. exact (fun h0 : term781 A K s x i k z t => @lem4426439 A K z t x s i k h1 h0 h2 h3). Qed.
Lemma lem4426441 {A K : Type'} (x : A) (t : type1470 A K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : @IN K i k) : term785 A K s k z x t i.
Proof. exact (fun h0 : term30 A K x s i => @lem4426440 A K t z x s i k h1 h0 h2). Qed.
Lemma lem4426442 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term429 A K k z s) : term786 A K s k z x t i.
Proof. exact (fun h0 : @IN K i k => @lem4426441 A K x t z s i k h1 h0). Qed.
Lemma lem4426443 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : term787 A K s k z x t i.
Proof. exact (fun h0 : term429 A K k z s => @lem4426442 A K x t i k z s h0). Qed.
Lemma lem4426448 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : term789 A K k z x t i.
Proof. exact (fun s : type1470 A K => @lem4426443 A K s k z x t i). Qed.
Lemma lem4426453 {A K : Type'} (z : K -> A) (x : A) (t : type1470 A K) (i : K) : term791 A K z x t i.
Proof. exact (fun k : K -> Prop => @lem4426448 A K k z x t i). Qed.
Lemma lem4426458 {A K : Type'} (x : A) (t : type1470 A K) (i : K) : term793 A K x t i.
Proof. exact (fun z : K -> A => @lem4426453 A K z x t i). Qed.
Lemma lem4426463 {A K : Type'} (t : type1470 A K) (i : K) : term795 A K t i.
Proof. exact (fun x : A => @lem4426458 A K x t i). Qed.
Lemma lem4426468 {A K : Type'} (i : K) : term797 A K i.
Proof. exact (fun t : type1470 A K => @lem4426463 A K t i). Qed.
Lemma lem4426473 {A K : Type'} : term799 A K.
Proof. exact (fun i : K => @lem4426468 A K i). Qed.
Lemma lem4426474 {A K : Type'} : term765 A K.
Proof. exact (EQ_MP (@lem4425037 A K) (@lem4426473 A K)). Qed.
Lemma lem4426475 {A K : Type'} (i : K) : term930 A K i.
Proof. exact (@lem4426474 A K i). Qed.
Lemma lem4426476 {A K : Type'} (i : K) : (term930 A K i) = (term761 A K i).
Proof. exact (eq_refl (term930 A K i)). Qed.
Lemma lem4426477 {A K : Type'} (i : K) : term761 A K i.
Proof. exact (EQ_MP (@lem4426476 A K i) (@lem4426475 A K i)). Qed.
Lemma lem4426478 {A K : Type'} (i : K) (t : type1470 A K) : term931 A K i t.
Proof. exact (@lem4426477 A K i t). Qed.
Lemma lem4426479 {A K : Type'} (t : type1470 A K) (i : K) : (term931 A K i t) = (term757 A K t i).
Proof. exact (eq_refl (term931 A K i t)). Qed.
Lemma lem4426480 {A K : Type'} (t : type1470 A K) (i : K) : term757 A K t i.
Proof. exact (EQ_MP (@lem4426479 A K t i) (@lem4426478 A K i t)). Qed.
Lemma lem4426481 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : term932 A K t i x.
Proof. exact (@lem4426480 A K t i x). Qed.
Lemma lem4426482 {A K : Type'} (x : A) (t : type1470 A K) (i : K) : (term932 A K t i x) = (term753 A K x t i).
Proof. exact (eq_refl (term932 A K t i x)). Qed.
Lemma lem4426483 {A K : Type'} (x : A) (t : type1470 A K) (i : K) : term753 A K x t i.
Proof. exact (EQ_MP (@lem4426482 A K x t i) (@lem4426481 A K t i x)). Qed.
Lemma lem4426484 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (z : K -> A) : term933 A K x t i z.
Proof. exact (@lem4426483 A K x t i z). Qed.
Lemma lem4426485 {A K : Type'} (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term933 A K x t i z) = (term749 A K z x t i).
Proof. exact (eq_refl (term933 A K x t i z)). Qed.
Lemma lem4426486 {A K : Type'} (z : K -> A) (x : A) (t : type1470 A K) (i : K) : term749 A K z x t i.
Proof. exact (EQ_MP (@lem4426485 A K z x t i) (@lem4426484 A K x t i z)). Qed.
Lemma lem4426487 {A K : Type'} (z : K -> A) (x : A) (t : type1470 A K) (i : K) (k : K -> Prop) : term934 A K z x t i k.
Proof. exact (@lem4426486 A K z x t i k). Qed.
Lemma lem4426488 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term934 A K z x t i k) = (term745 A K k z x t i).
Proof. exact (eq_refl (term934 A K z x t i k)). Qed.
Lemma lem4426489 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : term745 A K k z x t i.
Proof. exact (EQ_MP (@lem4426488 A K k z x t i) (@lem4426487 A K z x t i k)). Qed.
Lemma lem4426490 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) (s : type1470 A K) : term935 A K k z x t i s.
Proof. exact (@lem4426489 A K k z x t i s). Qed.
Lemma lem4426491 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : (term935 A K k z x t i s) = (term732 A K s k z x t i).
Proof. exact (eq_refl (term935 A K k z x t i s)). Qed.
Lemma lem4426492 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : term732 A K s k z x t i.
Proof. exact (EQ_MP (@lem4426491 A K s k z x t i) (@lem4426490 A K k z x t i s)). Qed.
Lemma lem4426494 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (z : K -> A) (x : A) (t : type1470 A K) (i : K) : term732 A K s k z x t i.
Proof. exact (@lem4424598 A K s k z x t i (@lem4426492 A K s k z x t i)). Qed.
Lemma lem4426495 {A K : Type'} (x : A) (t : type1470 A K) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term429 A K k z s) : term740 A K s k z x t i.
Proof. exact (@lem4426494 A K s k z x t i (@lem4420805 A K k z s h1)). Qed.
Lemma lem4426496 {A K : Type'} (x : A) (t : type1470 A K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : @IN K i k) : term738 A K s k z x t i.
Proof. exact (@lem4426495 A K x t i k z s h1 (@lem4420807 K i k h2)). Qed.
Lemma lem4426497 {A K : Type'} (t : type1470 A K) (z : K -> A) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term30 A K x s i) (h3 : @IN K i k) : term730 A K s k z x t i.
Proof. exact (@lem4426496 A K x t z s i k h1 h3 (@lem4420808 A K x s i h2)). Qed.
Lemma lem4426498 {A K : Type'} (z : K -> A) (t : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term731 A K s k z x t i) (h3 : term30 A K x s i) (h4 : @IN K i k) : False.
Proof. exact (@lem4426497 A K t z x s i k h1 h3 h4 (@lem4424582 A K s k z x t i h2)). Qed.
Lemma lem4426499 {A K : Type'} (z : K -> A) (t : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term731 A K s k z x t i) (h3 : term30 A K x s i) (h4 : @IN K i k) : (term731 A K s k z x t i) = False.
Proof. exact (prop_ext (fun h5 : term731 A K s k z x t i => @lem4426498 A K z t x s i k h1 h2 h3 h4) (fun h5 : False => @lem4424582 A K s k z x t i h2)). Qed.
Lemma lem4426500 {A K : Type'} (z : K -> A) (t : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term731 A K s k z x t i) (h3 : term30 A K x s i) (h4 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4426499 A K z t x s i k h1 h2 h3 h4) (@lem4424582 A K s k z x t i h2)). Qed.
Lemma lem4426501 {A K : Type'} (t : type1470 A K) (z : K -> A) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term30 A K x s i) (h3 : @IN K i k) : term730 A K s k z x t i.
Proof. exact (fun h0 : term731 A K s k z x t i => @lem4426500 A K z t x s i k h1 h0 h2 h3). Qed.
Lemma lem4426502 {A K : Type'} (t : type1470 A K) (z : K -> A) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term30 A K x s i) (h3 : @IN K i k) : term729 A K s k z x t i.
Proof. exact (EQ_MP (@lem4424581 A K s k z x t i) (@lem4426501 A K t z x s i k h1 h2 h3)). Qed.
Lemma lem4426503 {A K : Type'} (t : type1470 A K) (z : K -> A) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term30 A K x s i) (h3 : @IN K i k) : term650 A K s k z x t i.
Proof. exact (EQ_MP (@lem4424577 A K s k z x t i) (@lem4426502 A K t z x s i k h1 h2 h3)). Qed.
Lemma lem4426504 {A K : Type'} (t : type1470 A K) (z : K -> A) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term30 A K x s i) (h3 : @IN K i k) : term649 A K s k z x t i.
Proof. exact (EQ_MP (@lem4421093 A K s k z x t i) (@lem4426503 A K t z x s i k h1 h2 h3)). Qed.
Lemma lem4426505 {A K : Type'} (z : K -> A) (t : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term399 A K s k t) (h3 : term30 A K x s i) (h4 : @IN K i k) : term30 A K x t i.
Proof. exact (@lem4426504 A K t z x s i k h1 h3 h4 (@lem4420811 A K i x z s k t h2)). Qed.
Lemma lem4426506 {A K : Type'} (x : A) (z : K -> A) (s : type1470 A K) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term399 A K s k t) (h3 : @IN K i k) : term431 A K s x t i.
Proof. exact (fun h0 : term30 A K x s i => @lem4426505 A K z t x s i k h1 h2 h0 h3). Qed.
Lemma lem4426511 {A K : Type'} (z : K -> A) (s : type1470 A K) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term429 A K k z s) (h2 : term399 A K s k t) (h3 : @IN K i k) : term402 A K s t i.
Proof. exact (fun x : A => @lem4426506 A K x z s t i k h1 h2 h3). Qed.
Lemma lem4426512 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term429 A K k z s) (h2 : term399 A K s k t) : term404 A K k s t i.
Proof. exact (fun h0 : @IN K i k => @lem4426511 A K z s t i k h1 h2 h0). Qed.
Lemma lem4426517 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term429 A K k z s) (h2 : term399 A K s k t) : term407 A K k s t.
Proof. exact (fun i : K => @lem4426512 A K i z s k t h1 h2). Qed.
Lemma lem4426518 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term429 A K k z s) : term549 A K k s t.
Proof. exact (fun h0 : term399 A K s k t => @lem4426517 A K z s k t h1 h0). Qed.
Lemma lem4426519 {A K : Type'} (z : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term585 A K z k s t.
Proof. exact (fun h0 : term429 A K k z s => @lem4426518 A K t k z s h0). Qed.
Lemma lem4426524 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term588 A K k s t.
Proof. exact (fun z : K -> A => @lem4426519 A K z k s t). Qed.
Lemma lem4426525 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term551 A K k s t.
Proof. exact (EQ_MP (@lem4420804 A K k s t) (@lem4426524 A K k s t)). Qed.
Lemma lem4426526 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term550 A K k s t.
Proof. exact (EQ_MP (@lem4420648 A K k s t) (@lem4426525 A K k s t)). Qed.
Lemma lem4426527 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term358 A K k s) : term549 A K k s t.
Proof. exact (@lem4426526 A K k s t (@lem4420590 A K k s h1)). Qed.
Lemma lem4426528 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term358 A K k s) : term936 A K s k t.
Proof. exact (conj (@lem4426527 A K t k s h1) (@lem4420584 A K s k t)). Qed.
Lemma lem4426529 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term936 A K s k t) = ((term399 A K s k t) = (term407 A K k s t)).
Proof. exact (@lem32 (term399 A K s k t) (term407 A K k s t)). Qed.
Lemma lem4426530 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term358 A K k s) : (term399 A K s k t) = (term407 A K k s t).
Proof. exact (EQ_MP (@lem4426529 A K k s t) (@lem4426528 A K t k s h1)). Qed.
Lemma lem4426531 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term358 A K k s) : (term361 A K s k t) = (term366 A K k s t).
Proof. exact (EQ_MP (@lem4419475 A K k s t) (@lem4426530 A K t k s h1)). Qed.
Lemma lem4426532 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term358 A K k s) : (term361 A K s k t) = (term367 A K k s t).
Proof. exact (EQ_MP (@lem4419320 A K t k s h1) (@lem4426531 A K t k s h1)). Qed.
Lemma lem4426533 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term361 A K s k t) = (term367 A K k s t).
Proof. exact (or_elim (@lem4419213 A K k s) (fun h0 : (@cartesian_product A K k s) = (@EMPTY (K -> A)) => @lem4419271 A K t k s h0) (fun h0 : term358 A K k s => @lem4426532 A K t k s h0)). Qed.
Lemma lem4426538 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term937 A K k s.
Proof. exact (fun t : type1470 A K => @lem4426533 A K k s t). Qed.
Lemma lem4426543 {A K : Type'} (k : K -> Prop) : term938 A K k.
Proof. exact (fun s : type1470 A K => @lem4426538 A K k s). Qed.
Lemma lem4426548 {A K : Type'} : term939 A K.
Proof. exact (fun k : K -> Prop => @lem4426543 A K k). Qed.
