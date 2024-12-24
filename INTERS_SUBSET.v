Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERS_SUBSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3359698 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3359699 {A : Type'} (s : type686 A) (t : type686 A) : (s = t) = (term1 A s t).
Proof. exact (@lem3359698 (A -> Prop) s t). Qed.
Lemma lem3359700 {A : Type'} (u : type686 A) : (u = (@EMPTY (A -> Prop))) = (term2 A u).
Proof. exact (@lem3359699 A u (@EMPTY (A -> Prop))). Qed.
Lemma lem3359709 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3359710 {A : Type'} (u : type686 A) : (term3 A u) = (term4 A u).
Proof. exact (MK_COMB (@lem3359709) (@lem3359700 A u)). Qed.
Lemma lem3359711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3359712 {A : Type'} (u : type686 A) : (term5 A u) = (term6 A u).
Proof. exact (MK_COMB (@lem3359711) (@lem3359710 A u)). Qed.
Lemma lem3359720 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3359721 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (@lem3359720 A s t). Qed.
Lemma lem3359722 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term7 A t s).
Proof. exact (@lem3359721 A t s). Qed.
Lemma lem3359729 {A : Type'} (t : A -> Prop) (u : type686 A) : (term8 A t u) = (term8 A t u).
Proof. exact (eq_refl (term8 A t u)). Qed.
Lemma lem3359730 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term9 A u t s) = (term10 A u t s).
Proof. exact (MK_COMB (@lem3359729 A t u) (@lem3359722 A t s)). Qed.
Lemma lem3359733 {A : Type'} (u : type686 A) (s : A -> Prop) : (term11 A u s) = (term12 A u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3359730 A u t s)). Qed.
Lemma lem3359734 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3359735 {A : Type'} (u : type686 A) (s : A -> Prop) : (term13 A u s) = (term14 A u s).
Proof. exact (MK_COMB (@lem3359734 A) (@lem3359733 A u s)). Qed.
Lemma lem3359740 {A : Type'} (u : type686 A) (s : A -> Prop) : (term15 A u s) = (term16 A u s).
Proof. exact (MK_COMB (@lem3359712 A u) (@lem3359735 A u s)). Qed.
Lemma lem3359743 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3359744 {A : Type'} (u : type686 A) (s : A -> Prop) : (term17 A u s) = (term18 A u s).
Proof. exact (MK_COMB (@lem3359743) (@lem3359740 A u s)). Qed.
Lemma lem3359746 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3359747 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (@lem3359746 A s t). Qed.
Lemma lem3359748 {A : Type'} (u : type686 A) (s : A -> Prop) : (term19 A u s) = (term20 A u s).
Proof. exact (@lem3359747 A (@INTERS A u) s). Qed.
Lemma lem3359755 {A : Type'} (u : type686 A) (s : A -> Prop) : (term21 A u s) = (term22 A u s).
Proof. exact (MK_COMB (@lem3359744 A u s) (@lem3359748 A u s)). Qed.
Lemma lem3359758 {A : Type'} (u : type686 A) : (term23 A u) = (term24 A u).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3359755 A u s)). Qed.
Lemma lem3359759 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3359760 {A : Type'} (u : type686 A) : (term25 A u) = (term26 A u).
Proof. exact (MK_COMB (@lem3359759 A) (@lem3359758 A u)). Qed.
Lemma lem3359765 {A : Type'} : (term27 A) = (term28 A).
Proof. exact (fun_ext (fun u : type686 A => @lem3359760 A u)). Qed.
Lemma lem3359766 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3359767 {A : Type'} : (term29 A) = (term30 A).
Proof. exact (MK_COMB (@lem3359766 A) (@lem3359765 A)). Qed.
Lemma lem3359772 {A : Type'} : (term30 A) = (term29 A).
Proof. exact (SYM (@lem3359767 A)). Qed.
Lemma lem3359792 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3359793 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3359792 (A -> Prop) P x). Qed.
Lemma lem3359794 {A : Type'} (u : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x u) = (u x).
Proof. exact (@lem3359793 A u x). Qed.
Lemma lem3359795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3359796 {A : Type'} (u : type686 A) (x : A -> Prop) : (term31 A x u) = (term32 A u x).
Proof. exact (MK_COMB (@lem3359795) (@lem3359794 A u x)). Qed.
Lemma lem3359798 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3359799 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3359798 (A -> Prop) x). Qed.
Lemma lem3359800 {A : Type'} (u : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x u) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = ((u x) = False).
Proof. exact (MK_COMB (@lem3359796 A u x) (@lem3359799 A x)). Qed.
Lemma lem3359802 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3359803 {A : Type'} (u : type686 A) (x : A -> Prop) : ((u x) = False) = (term33 A u x).
Proof. exact (@lem3359802 (u x)). Qed.
Lemma lem3359804 {A : Type'} (u : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x u) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = (term33 A u x).
Proof. exact (TRANS (@lem3359800 A u x) (@lem3359803 A u x)). Qed.
Lemma lem3359805 {A : Type'} (u : type686 A) : (term34 A u) = (term35 A u).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3359804 A u x)). Qed.
Lemma lem3359806 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3359807 {A : Type'} (u : type686 A) : (term2 A u) = (term36 A u).
Proof. exact (MK_COMB (@lem3359806 A) (@lem3359805 A u)). Qed.
Lemma lem3359812 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3359813 {A : Type'} (u : type686 A) : (term4 A u) = (term37 A u).
Proof. exact (MK_COMB (@lem3359812) (@lem3359807 A u)). Qed.
Lemma lem3359814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3359815 {A : Type'} (u : type686 A) : (term6 A u) = (term38 A u).
Proof. exact (MK_COMB (@lem3359814) (@lem3359813 A u)). Qed.
Lemma lem3359823 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3359824 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3359823 (A -> Prop) P x). Qed.
Lemma lem3359825 {A : Type'} (u : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t u) = (u t).
Proof. exact (@lem3359824 A u t). Qed.
Lemma lem3359826 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3359827 {A : Type'} (u : type686 A) (t : A -> Prop) : (term8 A t u) = (term39 A u t).
Proof. exact (MK_COMB (@lem3359826) (@lem3359825 A u t)). Qed.
Lemma lem3359835 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3359836 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3359835 A P x). Qed.
Lemma lem3359837 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3359836 A t x). Qed.
Lemma lem3359838 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3359839 {A : Type'} (t : A -> Prop) (x : A) : (term40 A x t) = (term41 A t x).
Proof. exact (MK_COMB (@lem3359838) (@lem3359837 A t x)). Qed.
Lemma lem3359841 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3359842 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3359841 A P x). Qed.
Lemma lem3359843 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3359842 A s x). Qed.
Lemma lem3359844 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term42 A t x s) = (term43 A t s x).
Proof. exact (MK_COMB (@lem3359839 A t x) (@lem3359843 A s x)). Qed.
Lemma lem3359847 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term44 A t s) = (term45 A t s).
Proof. exact (fun_ext (fun x : A => @lem3359844 A t s x)). Qed.
Lemma lem3359848 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3359849 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term7 A t s) = (term46 A t s).
Proof. exact (MK_COMB (@lem3359848 A) (@lem3359847 A t s)). Qed.
Lemma lem3359854 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term10 A u t s) = (term47 A u t s).
Proof. exact (MK_COMB (@lem3359827 A u t) (@lem3359849 A t s)). Qed.
Lemma lem3359857 {A : Type'} (u : type686 A) (s : A -> Prop) : (term12 A u s) = (term48 A u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3359854 A u t s)). Qed.
Lemma lem3359858 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3359859 {A : Type'} (u : type686 A) (s : A -> Prop) : (term14 A u s) = (term49 A u s).
Proof. exact (MK_COMB (@lem3359858 A) (@lem3359857 A u s)). Qed.
Lemma lem3359864 {A : Type'} (u : type686 A) (s : A -> Prop) : (term16 A u s) = (term50 A u s).
Proof. exact (MK_COMB (@lem3359815 A u) (@lem3359859 A u s)). Qed.
Lemma lem3359867 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3359868 {A : Type'} (u : type686 A) (s : A -> Prop) : (term18 A u s) = (term51 A u s).
Proof. exact (MK_COMB (@lem3359867) (@lem3359864 A u s)). Qed.
Lemma lem3359876 {A : Type'} (s : type686 A) (x : A) : (term52 A x s) = (term53 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3359877 {A : Type'} (s : type686 A) (x : A) : (term52 A x s) = (term53 A s x).
Proof. exact (@lem3359876 A s x). Qed.
Lemma lem3359878 {A : Type'} (u : type686 A) (x : A) : (term52 A x u) = (term53 A u x).
Proof. exact (@lem3359877 A u x). Qed.
Lemma lem3359886 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3359887 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3359886 (A -> Prop) P x). Qed.
Lemma lem3359888 {A : Type'} (u : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t u) = (u t).
Proof. exact (@lem3359887 A u t). Qed.
Lemma lem3359889 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3359890 {A : Type'} (u : type686 A) (t : A -> Prop) : (term8 A t u) = (term39 A u t).
Proof. exact (MK_COMB (@lem3359889) (@lem3359888 A u t)). Qed.
Lemma lem3359892 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3359893 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3359892 A P x). Qed.
Lemma lem3359894 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3359893 A t x). Qed.
Lemma lem3359895 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term54 A u x t) = (term55 A u t x).
Proof. exact (MK_COMB (@lem3359890 A u t) (@lem3359894 A t x)). Qed.
Lemma lem3359898 {A : Type'} (u : type686 A) (x : A) : (term56 A u x) = (term57 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3359895 A u t x)). Qed.
Lemma lem3359899 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3359900 {A : Type'} (u : type686 A) (x : A) : (term53 A u x) = (term58 A u x).
Proof. exact (MK_COMB (@lem3359899 A) (@lem3359898 A u x)). Qed.
Lemma lem3359905 {A : Type'} (u : type686 A) (x : A) : (term52 A x u) = (term58 A u x).
Proof. exact (TRANS (@lem3359878 A u x) (@lem3359900 A u x)). Qed.
Lemma lem3359906 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3359907 {A : Type'} (u : type686 A) (x : A) : (term59 A x u) = (term60 A u x).
Proof. exact (MK_COMB (@lem3359906) (@lem3359905 A u x)). Qed.
Lemma lem3359909 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3359910 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3359909 A P x). Qed.
Lemma lem3359911 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3359910 A s x). Qed.
Lemma lem3359912 {A : Type'} (u : type686 A) (s : A -> Prop) (x : A) : (term61 A u x s) = (term62 A u s x).
Proof. exact (MK_COMB (@lem3359907 A u x) (@lem3359911 A s x)). Qed.
Lemma lem3359915 {A : Type'} (u : type686 A) (s : A -> Prop) : (term63 A u s) = (term64 A u s).
Proof. exact (fun_ext (fun x : A => @lem3359912 A u s x)). Qed.
Lemma lem3359916 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3359917 {A : Type'} (u : type686 A) (s : A -> Prop) : (term20 A u s) = (term65 A u s).
Proof. exact (MK_COMB (@lem3359916 A) (@lem3359915 A u s)). Qed.
Lemma lem3359922 {A : Type'} (u : type686 A) (s : A -> Prop) : (term22 A u s) = (term66 A u s).
Proof. exact (MK_COMB (@lem3359868 A u s) (@lem3359917 A u s)). Qed.
Lemma lem3359925 {A : Type'} (u : type686 A) : (term24 A u) = (term67 A u).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3359922 A u s)). Qed.
Lemma lem3359926 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3359927 {A : Type'} (u : type686 A) : (term26 A u) = (term68 A u).
Proof. exact (MK_COMB (@lem3359926 A) (@lem3359925 A u)). Qed.
Lemma lem3359932 {A : Type'} : (term28 A) = (term69 A).
Proof. exact (fun_ext (fun u : type686 A => @lem3359927 A u)). Qed.
Lemma lem3359933 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3359934 {A : Type'} : (term30 A) = (term70 A).
Proof. exact (MK_COMB (@lem3359933 A) (@lem3359932 A)). Qed.
Lemma lem3359939 {A : Type'} : (term70 A) = (term30 A).
Proof. exact (SYM (@lem3359934 A)). Qed.
Lemma lem3359941 (p : Prop) : p = (term71 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3359942 {A : Type'} : (term70 A) = (term72 A).
Proof. exact (@lem3359941 (term70 A)). Qed.
Lemma lem3359943 {A : Type'} : (term72 A) = (term70 A).
Proof. exact (SYM (@lem3359942 A)). Qed.
Lemma lem3359944 {A : Type'} (h1 : term73 A) : term73 A.
Proof. exact (h1). Qed.
Lemma lem3359947 {A : Type'} (h1 : term72 A) : term72 A.
Proof. exact (h1). Qed.
Lemma lem3359948 {A : Type'} : term74 A.
Proof. exact (fun h0 : term72 A => @lem3359947 A h0). Qed.
Lemma lem3359949 {A : Type'} (h1 : term74 A) : term74 A.
Proof. exact (h1). Qed.
Lemma lem3359950 {A : Type'} (h1 : term72 A) : term72 A.
Proof. exact (h1). Qed.
Lemma lem3359951 {A : Type'} (h1 : term72 A) (h2 : term74 A) : term72 A.
Proof. exact (@lem3359949 A h2 (@lem3359950 A h1)). Qed.
Lemma lem3359952 {A : Type'} (h1 : term72 A) : term75 A.
Proof. exact (fun h0 : term74 A => @lem3359951 A h1 h0). Qed.
Lemma lem3359953 {A : Type'} (h1 : term74 A) : term74 A.
Proof. exact (h1). Qed.
Lemma lem3359954 {A : Type'} (h1 : term72 A) (h2 : term74 A) : term72 A.
Proof. exact (@lem3359952 A h1 (@lem3359953 A h2)). Qed.
Lemma lem3359955 {A : Type'} (h1 : term74 A) : term74 A.
Proof. exact (fun h0 : term72 A => @lem3359954 A h0 h1). Qed.
Lemma lem3359956 {A : Type'} : term76 A.
Proof. exact (fun h0 : term74 A => @lem3359955 A h0). Qed.
Lemma lem3359959 {A : Type'} : term74 A.
Proof. exact (@lem3359956 A (@lem3359948 A)). Qed.
Lemma lem3359960 {A : Type'} : term74 A.
Proof. exact (@lem3359959 A). Qed.
Lemma lem3359962 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3359963 {A : Type'} : (term72 A) = (term77 A).
Proof. exact (@lem3359962 (term73 A)). Qed.
Lemma lem3359965 (t : Prop) : (term78 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3359966 {A : Type'} : (term77 A) = (term70 A).
Proof. exact (@lem3359965 (term70 A)). Qed.
Lemma lem3360011 {A : Type'} : (term72 A) = (term70 A).
Proof. exact (TRANS (@lem3359963 A) (@lem3359966 A)). Qed.
Lemma lem3360012 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3360017 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term55 A u t x) = (term55 A u t x).
Proof. exact (eq_refl (term55 A u t x)). Qed.
Lemma lem3360018 {A : Type'} (u : type686 A) (x : A) : (term57 A u x) = (term57 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3360017 A u t x)). Qed.
Lemma lem3360019 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3360020 {A : Type'} (u : type686 A) (x : A) : (term58 A u x) = (term58 A u x).
Proof. exact (MK_COMB (@lem3360019 A) (@lem3360018 A u x)). Qed.
Lemma lem3360021 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3360022 {A : Type'} (u : type686 A) (x : A) : (term60 A u x) = (term60 A u x).
Proof. exact (MK_COMB (@lem3360021) (@lem3360020 A u x)). Qed.
Lemma lem3360023 {A : Type'} (u : type686 A) (s : A -> Prop) (x : A) : (term62 A u s x) = (term62 A u s x).
Proof. exact (MK_COMB (@lem3360022 A u x) (@lem3360012 A s x)). Qed.
Lemma lem3360024 {A : Type'} (u : type686 A) (s : A -> Prop) : (term64 A u s) = (term64 A u s).
Proof. exact (fun_ext (fun x : A => @lem3360023 A u s x)). Qed.
Lemma lem3360025 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3360026 {A : Type'} (u : type686 A) (s : A -> Prop) : (term65 A u s) = (term65 A u s).
Proof. exact (MK_COMB (@lem3360025 A) (@lem3360024 A u s)). Qed.
Lemma lem3360031 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term43 A t s x) = (term43 A t s x).
Proof. exact (eq_refl (term43 A t s x)). Qed.
Lemma lem3360032 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term45 A t s) = (term45 A t s).
Proof. exact (fun_ext (fun x : A => @lem3360031 A t s x)). Qed.
Lemma lem3360033 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3360034 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term46 A t s) = (term46 A t s).
Proof. exact (MK_COMB (@lem3360033 A) (@lem3360032 A t s)). Qed.
Lemma lem3360037 {A : Type'} (u : type686 A) (t : A -> Prop) : (term39 A u t) = (term39 A u t).
Proof. exact (eq_refl (term39 A u t)). Qed.
Lemma lem3360038 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term47 A u t s) = (term47 A u t s).
Proof. exact (MK_COMB (@lem3360037 A u t) (@lem3360034 A t s)). Qed.
Lemma lem3360039 {A : Type'} (u : type686 A) (s : A -> Prop) : (term48 A u s) = (term48 A u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3360038 A u t s)). Qed.
Lemma lem3360040 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3360041 {A : Type'} (u : type686 A) (s : A -> Prop) : (term49 A u s) = (term49 A u s).
Proof. exact (MK_COMB (@lem3360040 A) (@lem3360039 A u s)). Qed.
Lemma lem3360044 {A : Type'} (u : type686 A) (x : A -> Prop) : (term33 A u x) = (term33 A u x).
Proof. exact (eq_refl (term33 A u x)). Qed.
Lemma lem3360045 {A : Type'} (u : type686 A) : (term35 A u) = (term35 A u).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3360044 A u x)). Qed.
Lemma lem3360046 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3360047 {A : Type'} (u : type686 A) : (term36 A u) = (term36 A u).
Proof. exact (MK_COMB (@lem3360046 A) (@lem3360045 A u)). Qed.
Lemma lem3360048 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3360049 {A : Type'} (u : type686 A) : (term37 A u) = (term37 A u).
Proof. exact (MK_COMB (@lem3360048) (@lem3360047 A u)). Qed.
Lemma lem3360050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3360051 {A : Type'} (u : type686 A) : (term38 A u) = (term38 A u).
Proof. exact (MK_COMB (@lem3360050) (@lem3360049 A u)). Qed.
Lemma lem3360052 {A : Type'} (u : type686 A) (s : A -> Prop) : (term50 A u s) = (term50 A u s).
Proof. exact (MK_COMB (@lem3360051 A u) (@lem3360041 A u s)). Qed.
Lemma lem3360053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3360054 {A : Type'} (u : type686 A) (s : A -> Prop) : (term51 A u s) = (term51 A u s).
Proof. exact (MK_COMB (@lem3360053) (@lem3360052 A u s)). Qed.
Lemma lem3360055 {A : Type'} (u : type686 A) (s : A -> Prop) : (term66 A u s) = (term66 A u s).
Proof. exact (MK_COMB (@lem3360054 A u s) (@lem3360026 A u s)). Qed.
Lemma lem3360056 {A : Type'} (u : type686 A) : (term67 A u) = (term67 A u).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3360055 A u s)). Qed.
Lemma lem3360057 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3360058 {A : Type'} (u : type686 A) : (term68 A u) = (term68 A u).
Proof. exact (MK_COMB (@lem3360057 A) (@lem3360056 A u)). Qed.
Lemma lem3360059 {A : Type'} : (term69 A) = (term69 A).
Proof. exact (fun_ext (fun u : type686 A => @lem3360058 A u)). Qed.
Lemma lem3360060 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3360061 {A : Type'} : (term70 A) = (term70 A).
Proof. exact (MK_COMB (@lem3360060 A) (@lem3360059 A)). Qed.
Lemma lem3360118 {A : Type'} : (term72 A) = (term70 A).
Proof. exact (TRANS (@lem3360011 A) (@lem3360061 A)). Qed.
Lemma lem3360119 {A : Type'} : (term70 A) = (term72 A).
Proof. exact (SYM (@lem3360118 A)). Qed.
Lemma lem3360120 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : term50 A u s) : term50 A u s.
Proof. exact (h1). Qed.
Lemma lem3360121 {A : Type'} (u : type686 A) (x : A) (h1 : term58 A u x) : term58 A u x.
Proof. exact (h1). Qed.
Lemma lem3360123 (p : Prop) : p = (term71 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3360124 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (term79 A s x).
Proof. exact (@lem3360123 (s x)). Qed.
Lemma lem3360125 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (s x).
Proof. exact (SYM (@lem3360124 A s x)). Qed.
Lemma lem3360126 {A : Type'} (s : A -> Prop) (x : A) (h1 : term80 A s x) : term80 A s x.
Proof. exact (h1). Qed.
Lemma lem3360129 {A : Type'} (u : type686 A) (x : A -> Prop) : (term81 A u x) = (u x).
Proof. exact (@lem16933 (u x)). Qed.
Lemma lem3360130 {A : Type'} (P : type686 A) : (term82 A P) = (term83 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3360131 {A : Type'} (u : type686 A) : (term37 A u) = (term84 A u).
Proof. exact (@lem3360130 A (term35 A u)). Qed.
Lemma lem3360132 {A : Type'} (u : type686 A) (x : A -> Prop) : (term85 A u x) = (term33 A u x).
Proof. exact (eq_refl (term85 A u x)). Qed.
Lemma lem3360133 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3360134 {A : Type'} (u : type686 A) (x : A -> Prop) : (term86 A u x) = (term81 A u x).
Proof. exact (MK_COMB (@lem3360133) (@lem3360132 A u x)). Qed.
Lemma lem3360135 {A : Type'} (u : type686 A) (x : A -> Prop) : (term86 A u x) = (u x).
Proof. exact (TRANS (@lem3360134 A u x) (@lem3360129 A u x)). Qed.
Lemma lem3360136 {A : Type'} (u : type686 A) : (term87 A u) = (term88 A u).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3360135 A u x)). Qed.
Lemma lem3360137 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3360138 {A : Type'} (u : type686 A) : (term84 A u) = (term89 A u).
Proof. exact (MK_COMB (@lem3360137 A) (@lem3360136 A u)). Qed.
Lemma lem3360139 {A : Type'} (u : type686 A) : (term37 A u) = (term89 A u).
Proof. exact (TRANS (@lem3360131 A u) (@lem3360138 A u)). Qed.
Lemma lem3360147 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term43 A t s x) = (term90 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem3360148 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term45 A t s) = (term91 A t s).
Proof. exact (fun_ext (fun x : A => @lem3360147 A t s x)). Qed.
Lemma lem3360149 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3360150 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term46 A t s) = (term92 A t s).
Proof. exact (MK_COMB (@lem3360149 A) (@lem3360148 A t s)). Qed.
Lemma lem3360152 {A : Type'} (u : type686 A) (t : A -> Prop) : (term93 A u t) = (term93 A u t).
Proof. exact (eq_refl (term93 A u t)). Qed.
Lemma lem3360153 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term94 A u t s) = (term95 A u t s).
Proof. exact (MK_COMB (@lem3360152 A u t) (@lem3360150 A t s)). Qed.
Lemma lem3360154 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term47 A u t s) = (term94 A u t s).
Proof. exact (@lem17265 (u t) (term46 A t s)). Qed.
Lemma lem3360155 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term47 A u t s) = (term95 A u t s).
Proof. exact (TRANS (@lem3360154 A u t s) (@lem3360153 A u t s)). Qed.
Lemma lem3360156 {A : Type'} (u : type686 A) (s : A -> Prop) : (term48 A u s) = (term96 A u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3360155 A u t s)). Qed.
Lemma lem3360157 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3360158 {A : Type'} (u : type686 A) (s : A -> Prop) : (term49 A u s) = (term97 A u s).
Proof. exact (MK_COMB (@lem3360157 A) (@lem3360156 A u s)). Qed.
Lemma lem3360159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3360160 {A : Type'} (u : type686 A) : (term38 A u) = (term98 A u).
Proof. exact (MK_COMB (@lem3360159) (@lem3360139 A u)). Qed.
Lemma lem3360161 {A : Type'} (u : type686 A) (s : A -> Prop) : (term50 A u s) = (term99 A u s).
Proof. exact (MK_COMB (@lem3360160 A u) (@lem3360158 A u s)). Qed.
Lemma lem3360248 {A : Type'} (P : A -> Prop) (Q : Prop) : (term100 A P Q) = (term101 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3360249 {A : Type'} (P : type686 A) (Q : Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (@lem3360248 (A -> Prop) P Q). Qed.
Lemma lem3360251 {A : Type'} (u : type686 A) (s : A -> Prop) : (term99 A u s) = (term104 A u s).
Proof. exact (@lem3360249 A u (term97 A u s)). Qed.
Lemma lem3360252 {A : Type'} (u : type686 A) (s : A -> Prop) : (term50 A u s) = (term104 A u s).
Proof. exact (TRANS (@lem3360161 A u s) (@lem3360251 A u s)). Qed.
Lemma lem3360253 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : term50 A u s) : term104 A u s.
Proof. exact (EQ_MP (@lem3360252 A u s) (@lem3360120 A u s h1)). Qed.
Lemma lem3360260 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term55 A u t x) = (term105 A u t x).
Proof. exact (@lem17265 (u t) (t x)). Qed.
Lemma lem3360261 {A : Type'} (u : type686 A) (x : A) : (term57 A u x) = (term106 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3360260 A u t x)). Qed.
Lemma lem3360262 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3360315 {A : Type'} (u : type686 A) (x : A) : (term58 A u x) = (term107 A u x).
Proof. exact (MK_COMB (@lem3360262 A) (@lem3360261 A u x)). Qed.
Lemma lem3360316 {A : Type'} (u : type686 A) (x : A) (h1 : term58 A u x) : term107 A u x.
Proof. exact (EQ_MP (@lem3360315 A u x) (@lem3360121 A u x h1)). Qed.
Lemma lem3360322 {A : Type'} (s : A -> Prop) (x : A) (h1 : term80 A s x) : term80 A s x.
Proof. exact (h1). Qed.
Lemma lem3360323 {A : Type'} (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : term108 A x' u s.
Proof. exact (h1). Qed.
Lemma lem3360328 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3360329 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3360328 A Prop f x). Qed.
Lemma lem3360331 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3360329 A t x). Qed.
Lemma lem3360332 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3360337 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3360338 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3360337 (A -> Prop) Prop f x). Qed.
Lemma lem3360340 {A : Type'} (u : type686 A) (t : A -> Prop) : (u t) = (@I ((A -> Prop) -> Prop) u t).
Proof. exact (@lem3360338 A u t). Qed.
Lemma lem3360341 {A : Type'} (u : type686 A) (t : A -> Prop) : (term33 A u t) = (term109 A u t).
Proof. exact (MK_COMB (@lem3360332) (@lem3360340 A u t)). Qed.
Lemma lem3360342 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3360343 {A : Type'} (u : type686 A) (t : A -> Prop) : (term93 A u t) = (term110 A u t).
Proof. exact (MK_COMB (@lem3360342) (@lem3360341 A u t)). Qed.
Lemma lem3360344 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term105 A u t x) = (term111 A u t x).
Proof. exact (MK_COMB (@lem3360343 A u t) (@lem3360331 A t x)). Qed.
Lemma lem3360345 {A : Type'} (u : type686 A) (x : A) : (term106 A u x) = (term112 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3360344 A u t x)). Qed.
Lemma lem3360346 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3360347 {A : Type'} (u : type686 A) (x : A) : (term107 A u x) = (term113 A u x).
Proof. exact (MK_COMB (@lem3360346 A) (@lem3360345 A u x)). Qed.
Lemma lem3360348 {A : Type'} (u : type686 A) (x : A) (h1 : term58 A u x) : term113 A u x.
Proof. exact (EQ_MP (@lem3360347 A u x) (@lem3360316 A u x h1)). Qed.
Lemma lem3360349 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3360354 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3360355 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3360354 A Prop f x). Qed.
Lemma lem3360357 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3360355 A s x). Qed.
Lemma lem3360358 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (term114 A s x).
Proof. exact (MK_COMB (@lem3360349) (@lem3360357 A s x)). Qed.
Lemma lem3360364 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3360365 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3360364 A Prop f x). Qed.
Lemma lem3360367 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3360365 A s x). Qed.
Lemma lem3360368 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3360373 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3360374 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3360373 A Prop f x). Qed.
Lemma lem3360376 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3360374 A t x). Qed.
Lemma lem3360377 {A : Type'} (t : A -> Prop) (x : A) : (term80 A t x) = (term114 A t x).
Proof. exact (MK_COMB (@lem3360368) (@lem3360376 A t x)). Qed.
Lemma lem3360378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3360379 {A : Type'} (t : A -> Prop) (x : A) : (term115 A t x) = (term116 A t x).
Proof. exact (MK_COMB (@lem3360378) (@lem3360377 A t x)). Qed.
Lemma lem3360380 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term90 A t s x) = (term117 A t s x).
Proof. exact (MK_COMB (@lem3360379 A t x) (@lem3360367 A s x)). Qed.
Lemma lem3360381 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term91 A t s) = (term118 A t s).
Proof. exact (fun_ext (fun x : A => @lem3360380 A t s x)). Qed.
Lemma lem3360382 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3360383 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term92 A t s) = (term119 A t s).
Proof. exact (MK_COMB (@lem3360382 A) (@lem3360381 A t s)). Qed.
Lemma lem3360384 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3360389 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3360390 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3360389 (A -> Prop) Prop f x). Qed.
Lemma lem3360392 {A : Type'} (u : type686 A) (t : A -> Prop) : (u t) = (@I ((A -> Prop) -> Prop) u t).
Proof. exact (@lem3360390 A u t). Qed.
Lemma lem3360393 {A : Type'} (u : type686 A) (t : A -> Prop) : (term33 A u t) = (term109 A u t).
Proof. exact (MK_COMB (@lem3360384) (@lem3360392 A u t)). Qed.
Lemma lem3360394 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3360395 {A : Type'} (u : type686 A) (t : A -> Prop) : (term93 A u t) = (term110 A u t).
Proof. exact (MK_COMB (@lem3360394) (@lem3360393 A u t)). Qed.
Lemma lem3360396 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term95 A u t s) = (term120 A u t s).
Proof. exact (MK_COMB (@lem3360395 A u t) (@lem3360383 A t s)). Qed.
Lemma lem3360397 {A : Type'} (u : type686 A) (s : A -> Prop) : (term96 A u s) = (term121 A u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3360396 A u t s)). Qed.
Lemma lem3360398 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3360399 {A : Type'} (u : type686 A) (s : A -> Prop) : (term97 A u s) = (term122 A u s).
Proof. exact (MK_COMB (@lem3360398 A) (@lem3360397 A u s)). Qed.
Lemma lem3360404 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3360405 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3360404 (A -> Prop) Prop f x). Qed.
Lemma lem3360407 {A : Type'} (u : type686 A) (x' : A -> Prop) : (u x') = (@I ((A -> Prop) -> Prop) u x').
Proof. exact (@lem3360405 A u x'). Qed.
Lemma lem3360408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3360409 {A : Type'} (u : type686 A) (x' : A -> Prop) : (term123 A u x') = (term124 A u x').
Proof. exact (MK_COMB (@lem3360408) (@lem3360407 A u x')). Qed.
Lemma lem3360410 {A : Type'} (x' : A -> Prop) (u : type686 A) (s : A -> Prop) : (term108 A x' u s) = (term125 A x' u s).
Proof. exact (MK_COMB (@lem3360409 A u x') (@lem3360399 A u s)). Qed.
Lemma lem3360411 {A : Type'} (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : term125 A x' u s.
Proof. exact (EQ_MP (@lem3360410 A x' u s) (@lem3360323 A x' u s h1)). Qed.
Lemma lem3360412 {A : Type'} (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : term122 A u s.
Proof. exact (proj2 (@lem3360411 A x' u s h1)). Qed.
Lemma lem3360421 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term111 A u t x) = (term111 A u t x).
Proof. exact (eq_refl (term111 A u t x)). Qed.
Lemma lem3360422 {A : Type'} (u : type686 A) (x : A) : (term112 A u x) = (term112 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3360421 A u t x)). Qed.
Lemma lem3360423 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3360425 {A : Type'} (u : type686 A) (x : A) : (term113 A u x) = (term113 A u x).
Proof. exact (MK_COMB (@lem3360423 A) (@lem3360422 A u x)). Qed.
Lemma lem3360426 {A : Type'} (u : type686 A) (x : A) (h1 : term58 A u x) : term113 A u x.
Proof. exact (EQ_MP (@lem3360425 A u x) (@lem3360348 A u x h1)). Qed.
Lemma lem3360436 {A : Type'} (P : Prop) (Q : A -> Prop) : (term126 A P Q) = (term127 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3360437 {A : Type'} (P : Prop) (Q : A -> Prop) : (term126 A P Q) = (term127 A P Q).
Proof. exact (@lem3360436 A P Q). Qed.
Lemma lem3360438 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term128 A u t s) = (term129 A u t s).
Proof. exact (@lem3360437 A (term109 A u t) (term118 A t s)). Qed.
Lemma lem3360439 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term130 A t s x) = (term117 A t s x).
Proof. exact (eq_refl (term130 A t s x)). Qed.
Lemma lem3360440 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term131 A t s) = (term118 A t s).
Proof. exact (fun_ext (fun x : A => @lem3360439 A t s x)). Qed.
Lemma lem3360441 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3360442 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term132 A t s) = (term119 A t s).
Proof. exact (MK_COMB (@lem3360441 A) (@lem3360440 A t s)). Qed.
Lemma lem3360443 {A : Type'} (u : type686 A) (t : A -> Prop) : (term110 A u t) = (term110 A u t).
Proof. exact (eq_refl (term110 A u t)). Qed.
Lemma lem3360444 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term128 A u t s) = (term120 A u t s).
Proof. exact (MK_COMB (@lem3360443 A u t) (@lem3360442 A t s)). Qed.
Lemma lem3360445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3360446 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term133 A u t s) = (term134 A u t s).
Proof. exact (MK_COMB (@lem3360445) (@lem3360444 A u t s)). Qed.
Lemma lem3360447 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term130 A t s x) = (term117 A t s x).
Proof. exact (eq_refl (term130 A t s x)). Qed.
Lemma lem3360448 {A : Type'} (u : type686 A) (t : A -> Prop) : (term110 A u t) = (term110 A u t).
Proof. exact (eq_refl (term110 A u t)). Qed.
Lemma lem3360449 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term135 A u t s x) = (term136 A u t s x).
Proof. exact (MK_COMB (@lem3360448 A u t) (@lem3360447 A t s x)). Qed.
Lemma lem3360450 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term137 A u t s) = (term138 A u t s).
Proof. exact (fun_ext (fun x : A => @lem3360449 A u t s x)). Qed.
Lemma lem3360451 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3360452 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term129 A u t s) = (term139 A u t s).
Proof. exact (MK_COMB (@lem3360451 A) (@lem3360450 A u t s)). Qed.
Lemma lem3360453 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : ((term128 A u t s) = (term129 A u t s)) = ((term120 A u t s) = (term139 A u t s)).
Proof. exact (MK_COMB (@lem3360446 A u t s) (@lem3360452 A u t s)). Qed.
Lemma lem3360454 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term120 A u t s) = (term139 A u t s).
Proof. exact (EQ_MP (@lem3360453 A u t s) (@lem3360438 A u t s)). Qed.
Lemma lem3360455 {A : Type'} (u : type686 A) (s : A -> Prop) : (term121 A u s) = (term140 A u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3360454 A u t s)). Qed.
Lemma lem3360456 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3360457 {A : Type'} (u : type686 A) (s : A -> Prop) : (term122 A u s) = (term141 A u s).
Proof. exact (MK_COMB (@lem3360456 A) (@lem3360455 A u s)). Qed.
Lemma lem3360470 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term136 A u t s x) = (term136 A u t s x).
Proof. exact (eq_refl (term136 A u t s x)). Qed.
Lemma lem3360471 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term138 A u t s) = (term138 A u t s).
Proof. exact (fun_ext (fun x : A => @lem3360470 A u t s x)). Qed.
Lemma lem3360472 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3360473 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term139 A u t s) = (term139 A u t s).
Proof. exact (MK_COMB (@lem3360472 A) (@lem3360471 A u t s)). Qed.
Lemma lem3360474 {A : Type'} (u : type686 A) (s : A -> Prop) : (term140 A u s) = (term140 A u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3360473 A u t s)). Qed.
Lemma lem3360475 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3360476 {A : Type'} (u : type686 A) (s : A -> Prop) : (term141 A u s) = (term141 A u s).
Proof. exact (MK_COMB (@lem3360475 A) (@lem3360474 A u s)). Qed.
Lemma lem3360477 {A : Type'} (u : type686 A) (s : A -> Prop) : (term122 A u s) = (term141 A u s).
Proof. exact (TRANS (@lem3360457 A u s) (@lem3360476 A u s)). Qed.
Lemma lem3360478 {A : Type'} (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : term141 A u s.
Proof. exact (EQ_MP (@lem3360477 A u s) (@lem3360412 A x' u s h1)). Qed.
Lemma lem3360479 {A : Type'} (_35065 : A -> Prop) (u : type686 A) (x : A) (h1 : term58 A u x) : term142 A u x _35065.
Proof. exact (@lem3360426 A u x h1 _35065). Qed.
Lemma lem3360480 {A : Type'} (u : type686 A) (_35065 : A -> Prop) (x : A) : (term142 A u x _35065) = (term111 A u _35065 x).
Proof. exact (eq_refl (term142 A u x _35065)). Qed.
Lemma lem3360482 {A : Type'} (_35066 : A -> Prop) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : term143 A u s _35066.
Proof. exact (@lem3360478 A x' u s h1 _35066). Qed.
Lemma lem3360483 {A : Type'} (u : type686 A) (_35066 : A -> Prop) (s : A -> Prop) : (term143 A u s _35066) = (term139 A u _35066 s).
Proof. exact (eq_refl (term143 A u s _35066)). Qed.
Lemma lem3360484 {A : Type'} (_35066 : A -> Prop) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : term139 A u _35066 s.
Proof. exact (EQ_MP (@lem3360483 A u _35066 s) (@lem3360482 A _35066 x' u s h1)). Qed.
Lemma lem3360485 {A : Type'} (_35066 : A -> Prop) (_35067 : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : term144 A u _35066 s _35067.
Proof. exact (@lem3360484 A _35066 x' u s h1 _35067). Qed.
Lemma lem3360486 {A : Type'} (u : type686 A) (_35066 : A -> Prop) (s : A -> Prop) (_35067 : A) : (term144 A u _35066 s _35067) = (term136 A u _35066 s _35067).
Proof. exact (eq_refl (term144 A u _35066 s _35067)). Qed.
Lemma lem3360493 {A : Type'} (_35065 : A -> Prop) (u : type686 A) (x : A) (h1 : term58 A u x) : term111 A u _35065 x.
Proof. exact (EQ_MP (@lem3360480 A u _35065 x) (@lem3360479 A _35065 u x h1)). Qed.
Lemma lem3360495 {A : Type'} (s : A -> Prop) (x : A) (h1 : term80 A s x) : term114 A s x.
Proof. exact (EQ_MP (@lem3360358 A s x) (@lem3360322 A s x h1)). Qed.
Lemma lem3360507 {A : Type'} (_35066 : A -> Prop) (_35067 : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : term136 A u _35066 s _35067.
Proof. exact (EQ_MP (@lem3360486 A u _35066 s _35067) (@lem3360485 A _35066 _35067 x' u s h1)). Qed.
Lemma lem3360509 {A : Type'} (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : @I ((A -> Prop) -> Prop) u x'.
Proof. exact (proj1 (@lem3360411 A x' u s h1)). Qed.
Lemma lem3360510 {A : Type'} (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : term145 A u x'.
Proof. exact (fun h0 : term109 A u x' => @lem3360509 A x' u s h1). Qed.
Lemma lem3360512 (p : Prop) : (term146 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3360513 {A : Type'} (u : type686 A) (x' : A -> Prop) : (term145 A u x') = (@I ((A -> Prop) -> Prop) u x').
Proof. exact (@lem3360512 (@I ((A -> Prop) -> Prop) u x')). Qed.
Lemma lem3360514 {A : Type'} (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : @I ((A -> Prop) -> Prop) u x'.
Proof. exact (EQ_MP (@lem3360513 A u x') (@lem3360510 A x' u s h1)). Qed.
Lemma lem3360516 {A : Type'} (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : @I ((A -> Prop) -> Prop) u x'.
Proof. exact (proj1 (@lem3360411 A x' u s h1)). Qed.
Lemma lem3360517 {A : Type'} (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : term145 A u x'.
Proof. exact (fun h0 : term109 A u x' => @lem3360516 A x' u s h1). Qed.
Lemma lem3360519 (p : Prop) : (term146 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3360520 {A : Type'} (u : type686 A) (x' : A -> Prop) : (term145 A u x') = (@I ((A -> Prop) -> Prop) u x').
Proof. exact (@lem3360519 (@I ((A -> Prop) -> Prop) u x')). Qed.
Lemma lem3360521 {A : Type'} (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : @I ((A -> Prop) -> Prop) u x'.
Proof. exact (EQ_MP (@lem3360520 A u x') (@lem3360517 A x' u s h1)). Qed.
Lemma lem3360527 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3360528 {A : Type'} (x : A) (u : type686 A) (_35065 : A -> Prop) : (term111 A u _35065 x) = (term147 A x u _35065).
Proof. exact (@lem3360527 (@I (A -> Prop) _35065 x) (term109 A u _35065)). Qed.
Lemma lem3360534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3360535 {A : Type'} (x : A) (u : type686 A) (_35065 : A -> Prop) : (term148 A u _35065 x) = (term149 A x u _35065).
Proof. exact (MK_COMB (@lem3360534) (@lem3360528 A x u _35065)). Qed.
Lemma lem3360541 {A : Type'} (x : A) (u : type686 A) (_35065 : A -> Prop) : (term147 A x u _35065) = (term147 A x u _35065).
Proof. exact (eq_refl (term147 A x u _35065)). Qed.
Lemma lem3360542 {A : Type'} (x : A) (u : type686 A) (_35065 : A -> Prop) : ((term111 A u _35065 x) = (term147 A x u _35065)) = ((term147 A x u _35065) = (term147 A x u _35065)).
Proof. exact (MK_COMB (@lem3360535 A x u _35065) (@lem3360541 A x u _35065)). Qed.
Lemma lem3360544 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3360545 (x : Prop) : (x = x) = True.
Proof. exact (@lem3360544 Prop x). Qed.
Lemma lem3360546 {A : Type'} (x : A) (u : type686 A) (_35065 : A -> Prop) : ((term147 A x u _35065) = (term147 A x u _35065)) = True.
Proof. exact (@lem3360545 (term147 A x u _35065)). Qed.
Lemma lem3360547 {A : Type'} (x : A) (u : type686 A) (_35065 : A -> Prop) : ((term111 A u _35065 x) = (term147 A x u _35065)) = True.
Proof. exact (TRANS (@lem3360542 A x u _35065) (@lem3360546 A x u _35065)). Qed.
Lemma lem3360548 {A : Type'} (x : A) (u : type686 A) (_35065 : A -> Prop) : True = ((term111 A u _35065 x) = (term147 A x u _35065)).
Proof. exact (SYM (@lem3360547 A x u _35065)). Qed.
Lemma lem3360549 {A : Type'} (x : A) (u : type686 A) (_35065 : A -> Prop) : (term111 A u _35065 x) = (term147 A x u _35065).
Proof. exact (EQ_MP (@lem3360548 A x u _35065) (@lem0)). Qed.
Lemma lem3360550 {A : Type'} (_35065 : A -> Prop) (u : type686 A) (x : A) (h1 : term58 A u x) : term147 A x u _35065.
Proof. exact (EQ_MP (@lem3360549 A x u _35065) (@lem3360493 A _35065 u x h1)). Qed.
Lemma lem3360552 (b : Prop) (a : Prop) : (a \/ b) = (term150 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3360553 {A : Type'} (u : type686 A) (_35065 : A -> Prop) (x : A) : (term147 A x u _35065) = (term151 A u _35065 x).
Proof. exact (@lem3360552 (term109 A u _35065) (@I (A -> Prop) _35065 x)). Qed.
Lemma lem3360555 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3360556 {A : Type'} (u : type686 A) (_35065 : A -> Prop) : (term152 A u _35065) = (@I ((A -> Prop) -> Prop) u _35065).
Proof. exact (@lem3360555 (@I ((A -> Prop) -> Prop) u _35065)). Qed.
Lemma lem3360557 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3360558 {A : Type'} (u : type686 A) (_35065 : A -> Prop) : (term153 A u _35065) = (term154 A u _35065).
Proof. exact (MK_COMB (@lem3360557) (@lem3360556 A u _35065)). Qed.
Lemma lem3360559 {A : Type'} (_35065 : A -> Prop) (x : A) : (@I (A -> Prop) _35065 x) = (@I (A -> Prop) _35065 x).
Proof. exact (eq_refl (@I (A -> Prop) _35065 x)). Qed.
Lemma lem3360560 {A : Type'} (u : type686 A) (_35065 : A -> Prop) (x : A) : (term151 A u _35065 x) = (term155 A u _35065 x).
Proof. exact (MK_COMB (@lem3360558 A u _35065) (@lem3360559 A _35065 x)). Qed.
Lemma lem3360561 {A : Type'} (u : type686 A) (_35065 : A -> Prop) (x : A) : (term147 A x u _35065) = (term155 A u _35065 x).
Proof. exact (TRANS (@lem3360553 A u _35065 x) (@lem3360560 A u _35065 x)). Qed.
Lemma lem3360564 {A : Type'} (_35065 : A -> Prop) (u : type686 A) (x : A) (h1 : term58 A u x) : term155 A u _35065 x.
Proof. exact (EQ_MP (@lem3360561 A u _35065 x) (@lem3360550 A _35065 u x h1)). Qed.
Lemma lem3360565 {A : Type'} (_35065 : A -> Prop) (u : type686 A) (x : A) (h1 : term58 A u x) : term155 A u _35065 x.
Proof. exact (@lem3360564 A _35065 u x h1). Qed.
Lemma lem3360566 {A : Type'} (x' : A -> Prop) (u : type686 A) (x : A) (h1 : term58 A u x) : term155 A u x' x.
Proof. exact (@lem3360565 A x' u x h1). Qed.
Lemma lem3360569 {A : Type'} (x : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term108 A x' u s) : @I (A -> Prop) x' x.
Proof. exact (@lem3360566 A x' u x h1 (@lem3360521 A x' u s h2)). Qed.
Lemma lem3360570 {A : Type'} (x : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term108 A x' u s) : term156 A x' x.
Proof. exact (fun h0 : term114 A x' x => @lem3360569 A x x' u s h1 h2). Qed.
Lemma lem3360572 (p : Prop) : (term146 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3360573 {A : Type'} (x' : A -> Prop) (x : A) : (term156 A x' x) = (@I (A -> Prop) x' x).
Proof. exact (@lem3360572 (@I (A -> Prop) x' x)). Qed.
Lemma lem3360574 {A : Type'} (x : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term108 A x' u s) : @I (A -> Prop) x' x.
Proof. exact (EQ_MP (@lem3360573 A x' x) (@lem3360570 A x x' u s h1 h2)). Qed.
Lemma lem3360580 (q : Prop) (p : Prop) (r : Prop) : (term157 p q r) = (term157 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3360581 {A : Type'} (u : type686 A) (_35066 : A -> Prop) (s : A -> Prop) (_35067 : A) : (term136 A u _35066 s _35067) = (term158 A u _35066 s _35067).
Proof. exact (@lem3360580 (term114 A _35066 _35067) (term109 A u _35066) (@I (A -> Prop) s _35067)). Qed.
Lemma lem3360595 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3360596 {A : Type'} (s : A -> Prop) (_35067 : A) (u : type686 A) (_35066 : A -> Prop) : (term159 A u _35066 s _35067) = (term160 A s _35067 u _35066).
Proof. exact (@lem3360595 (@I (A -> Prop) s _35067) (term109 A u _35066)). Qed.
Lemma lem3360602 {A : Type'} (_35066 : A -> Prop) (_35067 : A) : (term116 A _35066 _35067) = (term116 A _35066 _35067).
Proof. exact (eq_refl (term116 A _35066 _35067)). Qed.
Lemma lem3360603 {A : Type'} (s : A -> Prop) (_35067 : A) (u : type686 A) (_35066 : A -> Prop) : (term158 A u _35066 s _35067) = (term161 A s _35067 u _35066).
Proof. exact (MK_COMB (@lem3360602 A _35066 _35067) (@lem3360596 A s _35067 u _35066)). Qed.
Lemma lem3360607 (q : Prop) (p : Prop) (r : Prop) : (term157 p q r) = (term157 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3360608 {A : Type'} (s : A -> Prop) (_35067 : A) (u : type686 A) (_35066 : A -> Prop) : (term161 A s _35067 u _35066) = (term162 A s _35067 u _35066).
Proof. exact (@lem3360607 (@I (A -> Prop) s _35067) (term114 A _35066 _35067) (term109 A u _35066)). Qed.
Lemma lem3360624 {A : Type'} (s : A -> Prop) (_35067 : A) (u : type686 A) (_35066 : A -> Prop) : (term158 A u _35066 s _35067) = (term162 A s _35067 u _35066).
Proof. exact (TRANS (@lem3360603 A s _35067 u _35066) (@lem3360608 A s _35067 u _35066)). Qed.
Lemma lem3360625 {A : Type'} (s : A -> Prop) (_35067 : A) (u : type686 A) (_35066 : A -> Prop) : (term136 A u _35066 s _35067) = (term162 A s _35067 u _35066).
Proof. exact (TRANS (@lem3360581 A u _35066 s _35067) (@lem3360624 A s _35067 u _35066)). Qed.
Lemma lem3360626 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3360627 {A : Type'} (s : A -> Prop) (_35067 : A) (u : type686 A) (_35066 : A -> Prop) : (term163 A u _35066 s _35067) = (term164 A s _35067 u _35066).
Proof. exact (MK_COMB (@lem3360626) (@lem3360625 A s _35067 u _35066)). Qed.
Lemma lem3360641 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3360642 {A : Type'} (_35067 : A) (u : type686 A) (_35066 : A -> Prop) : (term165 A u _35066 _35067) = (term166 A _35067 u _35066).
Proof. exact (@lem3360641 (term114 A _35066 _35067) (term109 A u _35066)). Qed.
Lemma lem3360648 {A : Type'} (s : A -> Prop) (_35067 : A) : (term167 A s _35067) = (term167 A s _35067).
Proof. exact (eq_refl (term167 A s _35067)). Qed.
Lemma lem3360649 {A : Type'} (s : A -> Prop) (_35067 : A) (u : type686 A) (_35066 : A -> Prop) : (term168 A s u _35066 _35067) = (term162 A s _35067 u _35066).
Proof. exact (MK_COMB (@lem3360648 A s _35067) (@lem3360642 A _35067 u _35066)). Qed.
Lemma lem3360660 {A : Type'} (s : A -> Prop) (_35067 : A) (u : type686 A) (_35066 : A -> Prop) : ((term136 A u _35066 s _35067) = (term168 A s u _35066 _35067)) = ((term162 A s _35067 u _35066) = (term162 A s _35067 u _35066)).
Proof. exact (MK_COMB (@lem3360627 A s _35067 u _35066) (@lem3360649 A s _35067 u _35066)). Qed.
Lemma lem3360662 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3360663 (x : Prop) : (x = x) = True.
Proof. exact (@lem3360662 Prop x). Qed.
Lemma lem3360664 {A : Type'} (s : A -> Prop) (_35067 : A) (u : type686 A) (_35066 : A -> Prop) : ((term162 A s _35067 u _35066) = (term162 A s _35067 u _35066)) = True.
Proof. exact (@lem3360663 (term162 A s _35067 u _35066)). Qed.
Lemma lem3360665 {A : Type'} (s : A -> Prop) (u : type686 A) (_35066 : A -> Prop) (_35067 : A) : ((term136 A u _35066 s _35067) = (term168 A s u _35066 _35067)) = True.
Proof. exact (TRANS (@lem3360660 A s _35067 u _35066) (@lem3360664 A s _35067 u _35066)). Qed.
Lemma lem3360666 {A : Type'} (s : A -> Prop) (u : type686 A) (_35066 : A -> Prop) (_35067 : A) : True = ((term136 A u _35066 s _35067) = (term168 A s u _35066 _35067)).
Proof. exact (SYM (@lem3360665 A s u _35066 _35067)). Qed.
Lemma lem3360667 {A : Type'} (s : A -> Prop) (u : type686 A) (_35066 : A -> Prop) (_35067 : A) : (term136 A u _35066 s _35067) = (term168 A s u _35066 _35067).
Proof. exact (EQ_MP (@lem3360666 A s u _35066 _35067) (@lem0)). Qed.
Lemma lem3360668 {A : Type'} (_35066 : A -> Prop) (_35067 : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : term168 A s u _35066 _35067.
Proof. exact (EQ_MP (@lem3360667 A s u _35066 _35067) (@lem3360507 A _35066 _35067 x' u s h1)). Qed.
Lemma lem3360670 (b : Prop) (a : Prop) : (a \/ b) = (term150 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3360671 {A : Type'} (u : type686 A) (_35066 : A -> Prop) (s : A -> Prop) (_35067 : A) : (term168 A s u _35066 _35067) = (term169 A u _35066 s _35067).
Proof. exact (@lem3360670 (term165 A u _35066 _35067) (@I (A -> Prop) s _35067)). Qed.
Lemma lem3360673 (a : Prop) (b : Prop) : (term170 a b) = (term171 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3360674 {A : Type'} (u : type686 A) (_35066 : A -> Prop) (_35067 : A) : (term172 A u _35066 _35067) = (term173 A u _35066 _35067).
Proof. exact (@lem3360673 (term109 A u _35066) (term114 A _35066 _35067)). Qed.
Lemma lem3360676 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3360677 {A : Type'} (u : type686 A) (_35066 : A -> Prop) : (term152 A u _35066) = (@I ((A -> Prop) -> Prop) u _35066).
Proof. exact (@lem3360676 (@I ((A -> Prop) -> Prop) u _35066)). Qed.
Lemma lem3360678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3360679 {A : Type'} (u : type686 A) (_35066 : A -> Prop) : (term174 A u _35066) = (term124 A u _35066).
Proof. exact (MK_COMB (@lem3360678) (@lem3360677 A u _35066)). Qed.
Lemma lem3360681 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3360682 {A : Type'} (_35066 : A -> Prop) (_35067 : A) : (term175 A _35066 _35067) = (@I (A -> Prop) _35066 _35067).
Proof. exact (@lem3360681 (@I (A -> Prop) _35066 _35067)). Qed.
Lemma lem3360683 {A : Type'} (u : type686 A) (_35066 : A -> Prop) (_35067 : A) : (term173 A u _35066 _35067) = (term176 A u _35066 _35067).
Proof. exact (MK_COMB (@lem3360679 A u _35066) (@lem3360682 A _35066 _35067)). Qed.
Lemma lem3360684 {A : Type'} (u : type686 A) (_35066 : A -> Prop) (_35067 : A) : (term172 A u _35066 _35067) = (term176 A u _35066 _35067).
Proof. exact (TRANS (@lem3360674 A u _35066 _35067) (@lem3360683 A u _35066 _35067)). Qed.
Lemma lem3360685 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3360686 {A : Type'} (u : type686 A) (_35066 : A -> Prop) (_35067 : A) : (term177 A u _35066 _35067) = (term178 A u _35066 _35067).
Proof. exact (MK_COMB (@lem3360685) (@lem3360684 A u _35066 _35067)). Qed.
Lemma lem3360687 {A : Type'} (s : A -> Prop) (_35067 : A) : (@I (A -> Prop) s _35067) = (@I (A -> Prop) s _35067).
Proof. exact (eq_refl (@I (A -> Prop) s _35067)). Qed.
Lemma lem3360688 {A : Type'} (u : type686 A) (_35066 : A -> Prop) (s : A -> Prop) (_35067 : A) : (term169 A u _35066 s _35067) = (term179 A u _35066 s _35067).
Proof. exact (MK_COMB (@lem3360686 A u _35066 _35067) (@lem3360687 A s _35067)). Qed.
Lemma lem3360689 {A : Type'} (u : type686 A) (_35066 : A -> Prop) (s : A -> Prop) (_35067 : A) : (term168 A s u _35066 _35067) = (term179 A u _35066 s _35067).
Proof. exact (TRANS (@lem3360671 A u _35066 s _35067) (@lem3360688 A u _35066 s _35067)). Qed.
Lemma lem3360691 {A : Type'} (x : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term108 A x' u s) : term176 A u x' x.
Proof. exact (conj (@lem3360514 A x' u s h2) (@lem3360574 A x x' u s h1 h2)). Qed.
Lemma lem3360693 {A : Type'} (_35066 : A -> Prop) (_35067 : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : term179 A u _35066 s _35067.
Proof. exact (EQ_MP (@lem3360689 A u _35066 s _35067) (@lem3360668 A _35066 _35067 x' u s h1)). Qed.
Lemma lem3360694 {A : Type'} (_35066 : A -> Prop) (_35067 : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : term179 A u _35066 s _35067.
Proof. exact (@lem3360693 A _35066 _35067 x' u s h1). Qed.
Lemma lem3360695 {A : Type'} (x : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term108 A x' u s) : term179 A u x' s x.
Proof. exact (@lem3360694 A x' x x' u s h1). Qed.
Lemma lem3360698 {A : Type'} (x : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term108 A x' u s) : @I (A -> Prop) s x.
Proof. exact (@lem3360695 A x x' u s h2 (@lem3360691 A x x' u s h1 h2)). Qed.
Lemma lem3360699 {A : Type'} (x : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term108 A x' u s) : term156 A s x.
Proof. exact (fun h0 : term114 A s x => @lem3360698 A x x' u s h1 h2). Qed.
Lemma lem3360701 (p : Prop) : (term146 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3360702 {A : Type'} (s : A -> Prop) (x : A) : (term156 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3360701 (@I (A -> Prop) s x)). Qed.
Lemma lem3360703 {A : Type'} (x : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term108 A x' u s) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3360702 A s x) (@lem3360699 A x x' u s h1 h2)). Qed.
Lemma lem3360706 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3360708 {A : Type'} (s : A -> Prop) (x : A) : (term114 A s x) = (term180 A s x).
Proof. exact (@lem3360706 (@I (A -> Prop) s x)). Qed.
Lemma lem3360711 {A : Type'} (s : A -> Prop) (x : A) (h1 : term80 A s x) : term180 A s x.
Proof. exact (EQ_MP (@lem3360708 A s x) (@lem3360495 A s x h1)). Qed.
Lemma lem3360714 {A : Type'} (x : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term80 A s x) (h3 : term108 A x' u s) : False.
Proof. exact (@lem3360711 A s x h2 (@lem3360703 A x x' u s h1 h3)). Qed.
Lemma lem3360715 {A : Type'} (x : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term80 A s x) (h3 : term108 A x' u s) : term181.
Proof. exact (fun h0 : ~ False => @lem3360714 A x x' u s h1 h2 h3). Qed.
Lemma lem3360717 (p : Prop) : (term146 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3360718 : term181 = False.
Proof. exact (@lem3360717 False). Qed.
Lemma lem3360719 {A : Type'} (x : A) (x' : A -> Prop) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term80 A s x) (h3 : term108 A x' u s) : False.
Proof. exact (EQ_MP (@lem3360718) (@lem3360715 A x x' u s h1 h2 h3)). Qed.
Lemma lem3360720 {A : Type'} (x : A) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term80 A s x) (h3 : term50 A u s) : False.
Proof. exact (ex_elim (@lem3360253 A u s h3) (fun x' : A -> Prop => fun h0 : term182 A u s x' => @lem3360719 A x x' u s h1 h2 h0)). Qed.
Lemma lem3360721 {A : Type'} (x : A) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term80 A s x) (h3 : term50 A u s) : (term80 A s x) = False.
Proof. exact (prop_ext (fun h4 : term80 A s x => @lem3360720 A x u s h1 h2 h3) (fun h4 : False => @lem3360322 A s x h2)). Qed.
Lemma lem3360722 {A : Type'} (x : A) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term80 A s x) (h3 : term50 A u s) : False.
Proof. exact (EQ_MP (@lem3360721 A x u s h1 h2 h3) (@lem3360322 A s x h2)). Qed.
Lemma lem3360723 {A : Type'} (x : A) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term80 A s x) (h3 : term50 A u s) : (term80 A s x) = False.
Proof. exact (prop_ext (fun h4 : term80 A s x => @lem3360722 A x u s h1 h2 h3) (fun h4 : False => @lem3360126 A s x h2)). Qed.
Lemma lem3360724 {A : Type'} (x : A) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term80 A s x) (h3 : term50 A u s) : False.
Proof. exact (EQ_MP (@lem3360723 A x u s h1 h2 h3) (@lem3360126 A s x h2)). Qed.
Lemma lem3360725 {A : Type'} (x : A) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term50 A u s) : term79 A s x.
Proof. exact (fun h0 : term80 A s x => @lem3360724 A x u s h1 h0 h2). Qed.
Lemma lem3360726 {A : Type'} (x : A) (u : type686 A) (s : A -> Prop) (h1 : term58 A u x) (h2 : term50 A u s) : s x.
Proof. exact (EQ_MP (@lem3360125 A s x) (@lem3360725 A x u s h1 h2)). Qed.
Lemma lem3360727 {A : Type'} (x : A) (u : type686 A) (s : A -> Prop) (h1 : term50 A u s) : term62 A u s x.
Proof. exact (fun h0 : term58 A u x => @lem3360726 A x u s h0 h1). Qed.
Lemma lem3360732 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : term50 A u s) : term65 A u s.
Proof. exact (fun x : A => @lem3360727 A x u s h1). Qed.
Lemma lem3360733 {A : Type'} (u : type686 A) (s : A -> Prop) : term66 A u s.
Proof. exact (fun h0 : term50 A u s => @lem3360732 A u s h0). Qed.
Lemma lem3360738 {A : Type'} (u : type686 A) : term68 A u.
Proof. exact (fun s : A -> Prop => @lem3360733 A u s). Qed.
Lemma lem3360743 {A : Type'} : term70 A.
Proof. exact (fun u : type686 A => @lem3360738 A u). Qed.
Lemma lem3360744 {A : Type'} : term72 A.
Proof. exact (EQ_MP (@lem3360119 A) (@lem3360743 A)). Qed.
Lemma lem3360746 {A : Type'} : term72 A.
Proof. exact (@lem3359960 A (@lem3360744 A)). Qed.
Lemma lem3360747 {A : Type'} (h1 : term73 A) : False.
Proof. exact (@lem3360746 A (@lem3359944 A h1)). Qed.
Lemma lem3360748 {A : Type'} (h1 : term73 A) : (term73 A) = False.
Proof. exact (prop_ext (fun h2 : term73 A => @lem3360747 A h1) (fun h2 : False => @lem3359944 A h1)). Qed.
Lemma lem3360749 {A : Type'} (h1 : term73 A) : False.
Proof. exact (EQ_MP (@lem3360748 A h1) (@lem3359944 A h1)). Qed.
Lemma lem3360750 {A : Type'} : term72 A.
Proof. exact (fun h0 : term73 A => @lem3360749 A h0). Qed.
Lemma lem3360751 {A : Type'} : term70 A.
Proof. exact (EQ_MP (@lem3359943 A) (@lem3360750 A)). Qed.
Lemma lem3360752 {A : Type'} : term30 A.
Proof. exact (EQ_MP (@lem3359939 A) (@lem3360751 A)). Qed.
Lemma lem3360753 {A : Type'} : term29 A.
Proof. exact (EQ_MP (@lem3359772 A) (@lem3360752 A)). Qed.
