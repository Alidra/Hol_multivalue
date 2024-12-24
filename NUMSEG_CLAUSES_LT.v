Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMSEG_CLAUSES_LT_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm89994_spec.
Lemma lem4620685 : term0.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem4620686 (m : nat) : term1 m.
Proof. exact (@lem4620685 m). Qed.
Lemma lem4620687 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem4620688 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem4620687 m) (@lem4620686 m)). Qed.
Lemma lem4620689 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem4620688 m n). Qed.
Lemma lem4620690 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem4620692 : term6.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem4620693 (m : nat) : term7 m.
Proof. exact (@lem4620692 m). Qed.
Lemma lem4620694 (m : nat) : (term7 m) = ((term8 m) = False).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem4620705 (m : nat) : (term8 m) = False.
Proof. exact (EQ_MP (@lem4620694 m) (@lem4620693 m)). Qed.
Lemma lem4620706 (i : nat) : (term8 i) = False.
Proof. exact (@lem4620705 i). Qed.
Lemma lem4620707 (GEN_PVAR_179 : nat) : (@SETSPEC nat GEN_PVAR_179) = (@SETSPEC nat GEN_PVAR_179).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_179)). Qed.
Lemma lem4620708 (i : nat) (GEN_PVAR_179 : nat) : (term9 GEN_PVAR_179 i) = (@SETSPEC nat GEN_PVAR_179 False).
Proof. exact (MK_COMB (@lem4620707 GEN_PVAR_179) (@lem4620706 i)). Qed.
Lemma lem4620709 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4620710 (GEN_PVAR_179 : nat) (i : nat) : (term10 GEN_PVAR_179 i) = (@SETSPEC nat GEN_PVAR_179 False i).
Proof. exact (MK_COMB (@lem4620708 i GEN_PVAR_179) (@lem4620709 i)). Qed.
Lemma lem4620711 (GEN_PVAR_179 : nat) : (term11 GEN_PVAR_179) = (term12 GEN_PVAR_179).
Proof. exact (fun_ext (fun i : nat => @lem4620710 GEN_PVAR_179 i)). Qed.
Lemma lem4620712 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4620713 (GEN_PVAR_179 : nat) : (term13 GEN_PVAR_179) = (term14 GEN_PVAR_179).
Proof. exact (MK_COMB (@lem4620712) (@lem4620711 GEN_PVAR_179)). Qed.
Lemma lem4620718 : term15 = term16.
Proof. exact (fun_ext (fun GEN_PVAR_179 : nat => @lem4620713 GEN_PVAR_179)). Qed.
Lemma lem4620719 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem4620720 : term17 = term18.
Proof. exact (MK_COMB (@lem4620719) (@lem4620718)). Qed.
Lemma lem4620721 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem4620722 : term19 = term20.
Proof. exact (MK_COMB (@lem4620721) (@lem4620720)). Qed.
Lemma lem4620723 : (@EMPTY nat) = (@EMPTY nat).
Proof. exact (eq_refl (@EMPTY nat)). Qed.
Lemma lem4620724 : (term17 = (@EMPTY nat)) = (term18 = (@EMPTY nat)).
Proof. exact (MK_COMB (@lem4620722) (@lem4620723)). Qed.
Lemma lem4620727 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4620728 : term21 = term22.
Proof. exact (MK_COMB (@lem4620727) (@lem4620724)). Qed.
Lemma lem4620740 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem4620690 m n) (@lem4620689 m n)). Qed.
Lemma lem4620741 (i : nat) (k : nat) : (term4 i k) = (term5 i k).
Proof. exact (@lem4620740 i k). Qed.
Lemma lem4620746 (GEN_PVAR_180 : nat) : (@SETSPEC nat GEN_PVAR_180) = (@SETSPEC nat GEN_PVAR_180).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_180)). Qed.
Lemma lem4620747 (GEN_PVAR_180 : nat) (i : nat) (k : nat) : (term23 GEN_PVAR_180 i k) = (term24 GEN_PVAR_180 i k).
Proof. exact (MK_COMB (@lem4620746 GEN_PVAR_180) (@lem4620741 i k)). Qed.
Lemma lem4620748 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4620749 (GEN_PVAR_180 : nat) (k : nat) (i : nat) : (term25 GEN_PVAR_180 k i) = (term26 GEN_PVAR_180 k i).
Proof. exact (MK_COMB (@lem4620747 GEN_PVAR_180 i k) (@lem4620748 i)). Qed.
Lemma lem4620750 (GEN_PVAR_180 : nat) (k : nat) : (term27 GEN_PVAR_180 k) = (term28 GEN_PVAR_180 k).
Proof. exact (fun_ext (fun i : nat => @lem4620749 GEN_PVAR_180 k i)). Qed.
Lemma lem4620751 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4620752 (GEN_PVAR_180 : nat) (k : nat) : (term29 GEN_PVAR_180 k) = (term30 GEN_PVAR_180 k).
Proof. exact (MK_COMB (@lem4620751) (@lem4620750 GEN_PVAR_180 k)). Qed.
Lemma lem4620757 (k : nat) : (term31 k) = (term32 k).
Proof. exact (fun_ext (fun GEN_PVAR_180 : nat => @lem4620752 GEN_PVAR_180 k)). Qed.
Lemma lem4620758 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem4620759 (k : nat) : (term33 k) = (term34 k).
Proof. exact (MK_COMB (@lem4620758) (@lem4620757 k)). Qed.
Lemma lem4620760 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem4620761 (k : nat) : (term35 k) = (term36 k).
Proof. exact (MK_COMB (@lem4620760) (@lem4620759 k)). Qed.
Lemma lem4620766 (k : nat) : (term37 k) = (term37 k).
Proof. exact (eq_refl (term37 k)). Qed.
Lemma lem4620767 (k : nat) : ((term33 k) = (term37 k)) = ((term34 k) = (term37 k)).
Proof. exact (MK_COMB (@lem4620761 k) (@lem4620766 k)). Qed.
Lemma lem4620770 : term38 = term39.
Proof. exact (fun_ext (fun k : nat => @lem4620767 k)). Qed.
Lemma lem4620771 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4620772 : term40 = term41.
Proof. exact (MK_COMB (@lem4620771) (@lem4620770)). Qed.
Lemma lem4620777 : term42 = term43.
Proof. exact (MK_COMB (@lem4620728) (@lem4620772)). Qed.
Lemma lem4620780 : term43 = term42.
Proof. exact (SYM (@lem4620777)). Qed.
Lemma lem4620786 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term44 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4620787 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term45 s t).
Proof. exact (@lem4620786 nat s t). Qed.
Lemma lem4620788 : (term18 = (@EMPTY nat)) = term46.
Proof. exact (@lem4620787 term18 (@EMPTY nat)). Qed.
Lemma lem4620801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4620802 : term22 = term47.
Proof. exact (MK_COMB (@lem4620801) (@lem4620788)). Qed.
Lemma lem4620810 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term44 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4620811 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term45 s t).
Proof. exact (@lem4620810 nat s t). Qed.
Lemma lem4620812 (k : nat) : ((term34 k) = (term37 k)) = (term48 k).
Proof. exact (@lem4620811 (term34 k) (term37 k)). Qed.
Lemma lem4620835 : term39 = term49.
Proof. exact (fun_ext (fun k : nat => @lem4620812 k)). Qed.
Lemma lem4620836 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4620837 : term41 = term50.
Proof. exact (MK_COMB (@lem4620836) (@lem4620835)). Qed.
Lemma lem4620842 : term43 = term51.
Proof. exact (MK_COMB (@lem4620802) (@lem4620837)). Qed.
Lemma lem4620845 : term51 = term43.
Proof. exact (SYM (@lem4620842)). Qed.
Lemma lem4620855 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term52 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4620856 (p : nat -> Prop) (x : nat) : (term53 x p) = (p x).
Proof. exact (@lem4620855 nat p x). Qed.
Lemma lem4620857 (x : nat) : (term54 x) = (term55 x).
Proof. exact (@lem4620856 term56 x). Qed.
Lemma lem4620858 (i : nat) : (term55 i) = False.
Proof. exact (eq_refl (term55 i)). Qed.
Lemma lem4620859 (GEN_PVAR_179 : nat) : (@SETSPEC nat GEN_PVAR_179) = (@SETSPEC nat GEN_PVAR_179).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_179)). Qed.
Lemma lem4620860 (i : nat) (GEN_PVAR_179 : nat) : (term57 GEN_PVAR_179 i) = (@SETSPEC nat GEN_PVAR_179 False).
Proof. exact (MK_COMB (@lem4620859 GEN_PVAR_179) (@lem4620858 i)). Qed.
Lemma lem4620861 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4620862 (GEN_PVAR_179 : nat) (i : nat) : (term58 GEN_PVAR_179 i) = (@SETSPEC nat GEN_PVAR_179 False i).
Proof. exact (MK_COMB (@lem4620860 i GEN_PVAR_179) (@lem4620861 i)). Qed.
Lemma lem4620863 (GEN_PVAR_179 : nat) : (term59 GEN_PVAR_179) = (term12 GEN_PVAR_179).
Proof. exact (fun_ext (fun i : nat => @lem4620862 GEN_PVAR_179 i)). Qed.
Lemma lem4620864 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4620865 (GEN_PVAR_179 : nat) : (term60 GEN_PVAR_179) = (term14 GEN_PVAR_179).
Proof. exact (MK_COMB (@lem4620864) (@lem4620863 GEN_PVAR_179)). Qed.
Lemma lem4620866 : term61 = term16.
Proof. exact (fun_ext (fun GEN_PVAR_179 : nat => @lem4620865 GEN_PVAR_179)). Qed.
Lemma lem4620867 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem4620868 : term62 = term18.
Proof. exact (MK_COMB (@lem4620867) (@lem4620866)). Qed.
Lemma lem4620869 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem4620870 (x : nat) : (term54 x) = (term63 x).
Proof. exact (MK_COMB (@lem4620869 x) (@lem4620868)). Qed.
Lemma lem4620871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4620872 (x : nat) : (term64 x) = (term65 x).
Proof. exact (MK_COMB (@lem4620871) (@lem4620870 x)). Qed.
Lemma lem4620873 (x : nat) : (term55 x) = False.
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem4620874 (x : nat) : ((term54 x) = (term55 x)) = ((term63 x) = False).
Proof. exact (MK_COMB (@lem4620872 x) (@lem4620873 x)). Qed.
Lemma lem4620875 (x : nat) : (term63 x) = False.
Proof. exact (EQ_MP (@lem4620874 x) (@lem4620857 x)). Qed.
Lemma lem4620876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4620877 (x : nat) : (term65 x) = (@eq Prop False).
Proof. exact (MK_COMB (@lem4620876) (@lem4620875 x)). Qed.
Lemma lem4620879 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4620880 (x : nat) : (@IN nat x (@EMPTY nat)) = False.
Proof. exact (@lem4620879 nat x). Qed.
Lemma lem4620881 (x : nat) : ((term63 x) = (@IN nat x (@EMPTY nat))) = (False = False).
Proof. exact (MK_COMB (@lem4620877 x) (@lem4620880 x)). Qed.
Lemma lem4620883 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4620884 : (False = False) = (~ False).
Proof. exact (@lem4620883 False). Qed.
Lemma lem4620886 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4620887 : (False = False) = True.
Proof. exact (TRANS (@lem4620884) (@lem4620886)). Qed.
Lemma lem4620888 (x : nat) : ((term63 x) = (@IN nat x (@EMPTY nat))) = True.
Proof. exact (TRANS (@lem4620881 x) (@lem4620887)). Qed.
Lemma lem4620889 : term66 = term67.
Proof. exact (fun_ext (fun x : nat => @lem4620888 x)). Qed.
Lemma lem4620890 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4620891 : term46 = term68.
Proof. exact (MK_COMB (@lem4620890) (@lem4620889)). Qed.
Lemma lem4620893 {A : Type'} (t : Prop) : (term69 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4620894 (t : Prop) : (term70 t) = t.
Proof. exact (@lem4620893 nat t). Qed.
Lemma lem4620895 : term68 = True.
Proof. exact (@lem4620894 True). Qed.
Lemma lem4620896 : term46 = True.
Proof. exact (TRANS (@lem4620891) (@lem4620895)). Qed.
Lemma lem4620897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4620898 : term47 = (and True).
Proof. exact (MK_COMB (@lem4620897) (@lem4620896)). Qed.
Lemma lem4620910 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term52 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4620911 (p : nat -> Prop) (x : nat) : (term53 x p) = (p x).
Proof. exact (@lem4620910 nat p x). Qed.
Lemma lem4620912 (k : nat) (x : nat) : (term71 x k) = (term72 k x).
Proof. exact (@lem4620911 (term73 k) x). Qed.
Lemma lem4620913 (i : nat) (k : nat) : (term72 k i) = (term5 i k).
Proof. exact (eq_refl (term72 k i)). Qed.
Lemma lem4620914 (GEN_PVAR_180 : nat) : (@SETSPEC nat GEN_PVAR_180) = (@SETSPEC nat GEN_PVAR_180).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_180)). Qed.
Lemma lem4620915 (GEN_PVAR_180 : nat) (i : nat) (k : nat) : (term74 GEN_PVAR_180 k i) = (term24 GEN_PVAR_180 i k).
Proof. exact (MK_COMB (@lem4620914 GEN_PVAR_180) (@lem4620913 i k)). Qed.
Lemma lem4620916 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4620917 (GEN_PVAR_180 : nat) (k : nat) (i : nat) : (term75 GEN_PVAR_180 k i) = (term26 GEN_PVAR_180 k i).
Proof. exact (MK_COMB (@lem4620915 GEN_PVAR_180 i k) (@lem4620916 i)). Qed.
Lemma lem4620918 (GEN_PVAR_180 : nat) (k : nat) : (term76 GEN_PVAR_180 k) = (term28 GEN_PVAR_180 k).
Proof. exact (fun_ext (fun i : nat => @lem4620917 GEN_PVAR_180 k i)). Qed.
Lemma lem4620919 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4620920 (GEN_PVAR_180 : nat) (k : nat) : (term77 GEN_PVAR_180 k) = (term30 GEN_PVAR_180 k).
Proof. exact (MK_COMB (@lem4620919) (@lem4620918 GEN_PVAR_180 k)). Qed.
Lemma lem4620921 (k : nat) : (term78 k) = (term32 k).
Proof. exact (fun_ext (fun GEN_PVAR_180 : nat => @lem4620920 GEN_PVAR_180 k)). Qed.
Lemma lem4620922 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem4620923 (k : nat) : (term79 k) = (term34 k).
Proof. exact (MK_COMB (@lem4620922) (@lem4620921 k)). Qed.
Lemma lem4620924 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem4620925 (x : nat) (k : nat) : (term71 x k) = (term80 x k).
Proof. exact (MK_COMB (@lem4620924 x) (@lem4620923 k)). Qed.
Lemma lem4620926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4620927 (x : nat) (k : nat) : (term81 x k) = (term82 x k).
Proof. exact (MK_COMB (@lem4620926) (@lem4620925 x k)). Qed.
Lemma lem4620928 (x : nat) (k : nat) : (term72 k x) = (term5 x k).
Proof. exact (eq_refl (term72 k x)). Qed.
Lemma lem4620929 (x : nat) (k : nat) : ((term71 x k) = (term72 k x)) = ((term80 x k) = (term5 x k)).
Proof. exact (MK_COMB (@lem4620927 x k) (@lem4620928 x k)). Qed.
Lemma lem4620930 (x : nat) (k : nat) : (term80 x k) = (term5 x k).
Proof. exact (EQ_MP (@lem4620929 x k) (@lem4620912 k x)). Qed.
Lemma lem4620935 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4620936 (x : nat) (k : nat) : (term82 x k) = (term83 x k).
Proof. exact (MK_COMB (@lem4620935) (@lem4620930 x k)). Qed.
Lemma lem4620938 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term84 A x y s) = (term85 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4620939 (y : nat) (x : nat) (s : nat -> Prop) : (term86 x y s) = (term87 y x s).
Proof. exact (@lem4620938 nat y x s). Qed.
Lemma lem4620940 (x : nat) (k : nat) : (term88 x k) = (term89 x k).
Proof. exact (@lem4620939 k x (term90 k)). Qed.
Lemma lem4620946 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term52 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4620947 (p : nat -> Prop) (x : nat) : (term53 x p) = (p x).
Proof. exact (@lem4620946 nat p x). Qed.
Lemma lem4620948 (k : nat) (x : nat) : (term91 x k) = (term92 k x).
Proof. exact (@lem4620947 (term93 k) x). Qed.
Lemma lem4620949 (i : nat) (k : nat) : (term92 k i) = (Peano.lt i k).
Proof. exact (eq_refl (term92 k i)). Qed.
Lemma lem4620950 (GEN_PVAR_181 : nat) : (@SETSPEC nat GEN_PVAR_181) = (@SETSPEC nat GEN_PVAR_181).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_181)). Qed.
Lemma lem4620951 (GEN_PVAR_181 : nat) (i : nat) (k : nat) : (term94 GEN_PVAR_181 k i) = (term95 GEN_PVAR_181 i k).
Proof. exact (MK_COMB (@lem4620950 GEN_PVAR_181) (@lem4620949 i k)). Qed.
Lemma lem4620952 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4620953 (GEN_PVAR_181 : nat) (k : nat) (i : nat) : (term96 GEN_PVAR_181 k i) = (term97 GEN_PVAR_181 k i).
Proof. exact (MK_COMB (@lem4620951 GEN_PVAR_181 i k) (@lem4620952 i)). Qed.
Lemma lem4620954 (GEN_PVAR_181 : nat) (k : nat) : (term98 GEN_PVAR_181 k) = (term99 GEN_PVAR_181 k).
Proof. exact (fun_ext (fun i : nat => @lem4620953 GEN_PVAR_181 k i)). Qed.
Lemma lem4620955 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4620956 (GEN_PVAR_181 : nat) (k : nat) : (term100 GEN_PVAR_181 k) = (term101 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem4620955) (@lem4620954 GEN_PVAR_181 k)). Qed.
Lemma lem4620957 (k : nat) : (term102 k) = (term103 k).
Proof. exact (fun_ext (fun GEN_PVAR_181 : nat => @lem4620956 GEN_PVAR_181 k)). Qed.
Lemma lem4620958 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem4620959 (k : nat) : (term104 k) = (term90 k).
Proof. exact (MK_COMB (@lem4620958) (@lem4620957 k)). Qed.
Lemma lem4620960 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem4620961 (x : nat) (k : nat) : (term91 x k) = (term105 x k).
Proof. exact (MK_COMB (@lem4620960 x) (@lem4620959 k)). Qed.
Lemma lem4620962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4620963 (x : nat) (k : nat) : (term106 x k) = (term107 x k).
Proof. exact (MK_COMB (@lem4620962) (@lem4620961 x k)). Qed.
Lemma lem4620964 (x : nat) (k : nat) : (term92 k x) = (Peano.lt x k).
Proof. exact (eq_refl (term92 k x)). Qed.
Lemma lem4620965 (x : nat) (k : nat) : ((term91 x k) = (term92 k x)) = ((term105 x k) = (Peano.lt x k)).
Proof. exact (MK_COMB (@lem4620963 x k) (@lem4620964 x k)). Qed.
Lemma lem4620966 (x : nat) (k : nat) : (term105 x k) = (Peano.lt x k).
Proof. exact (EQ_MP (@lem4620965 x k) (@lem4620948 k x)). Qed.
Lemma lem4620967 (x : nat) (k : nat) : (term108 x k) = (term108 x k).
Proof. exact (eq_refl (term108 x k)). Qed.
Lemma lem4620968 (x : nat) (k : nat) : (term89 x k) = (term5 x k).
Proof. exact (MK_COMB (@lem4620967 x k) (@lem4620966 x k)). Qed.
Lemma lem4620971 (x : nat) (k : nat) : (term88 x k) = (term5 x k).
Proof. exact (TRANS (@lem4620940 x k) (@lem4620968 x k)). Qed.
Lemma lem4620972 (x : nat) (k : nat) : ((term80 x k) = (term88 x k)) = ((term5 x k) = (term5 x k)).
Proof. exact (MK_COMB (@lem4620936 x k) (@lem4620971 x k)). Qed.
Lemma lem4620974 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4620975 (x : Prop) : (x = x) = True.
Proof. exact (@lem4620974 Prop x). Qed.
Lemma lem4620976 (x : nat) (k : nat) : ((term5 x k) = (term5 x k)) = True.
Proof. exact (@lem4620975 (term5 x k)). Qed.
Lemma lem4620977 (x : nat) (k : nat) : ((term80 x k) = (term88 x k)) = True.
Proof. exact (TRANS (@lem4620972 x k) (@lem4620976 x k)). Qed.
Lemma lem4620978 (k : nat) : (term109 k) = term67.
Proof. exact (fun_ext (fun x : nat => @lem4620977 x k)). Qed.
Lemma lem4620979 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4620980 (k : nat) : (term48 k) = term68.
Proof. exact (MK_COMB (@lem4620979) (@lem4620978 k)). Qed.
Lemma lem4620982 {A : Type'} (t : Prop) : (term69 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4620983 (t : Prop) : (term70 t) = t.
Proof. exact (@lem4620982 nat t). Qed.
Lemma lem4620984 : term68 = True.
Proof. exact (@lem4620983 True). Qed.
Lemma lem4620985 (k : nat) : (term48 k) = True.
Proof. exact (TRANS (@lem4620980 k) (@lem4620984)). Qed.
Lemma lem4620986 : term49 = term67.
Proof. exact (fun_ext (fun k : nat => @lem4620985 k)). Qed.
Lemma lem4620987 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4620988 : term50 = term68.
Proof. exact (MK_COMB (@lem4620987) (@lem4620986)). Qed.
Lemma lem4620990 {A : Type'} (t : Prop) : (term69 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4620991 (t : Prop) : (term70 t) = t.
Proof. exact (@lem4620990 nat t). Qed.
Lemma lem4620992 : term68 = True.
Proof. exact (@lem4620991 True). Qed.
Lemma lem4620993 : term50 = True.
Proof. exact (TRANS (@lem4620988) (@lem4620992)). Qed.
Lemma lem4620994 : term51 = (True /\ True).
Proof. exact (MK_COMB (@lem4620898) (@lem4620993)). Qed.
Lemma lem4620996 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4620997 : (True /\ True) = True.
Proof. exact (@lem4620996 True). Qed.
Lemma lem4620998 : term51 = True.
Proof. exact (TRANS (@lem4620994) (@lem4620997)). Qed.
Lemma lem4620999 : True = term51.
Proof. exact (SYM (@lem4620998)). Qed.
Lemma lem4621000 : term51.
Proof. exact (EQ_MP (@lem4620999) (@lem0)). Qed.
Lemma lem4621001 : term43.
Proof. exact (EQ_MP (@lem4620845) (@lem4621000)). Qed.
Lemma lem4621002 : term42.
Proof. exact (EQ_MP (@lem4620780) (@lem4621001)). Qed.
