Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_BOUND_GEN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_0_spec.
Require Import REAL_DIV_LMUL_spec.
Require Import SUM_BOUND_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1340231_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem7132623 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7132624 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7132625 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7132624 t1) (@lem7132623 t1)). Qed.
Lemma lem7132626 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7132625 t1 t2). Qed.
Lemma lem7132627 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7132628 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7132627 t1 t2) (@lem7132626 t1 t2)). Qed.
Lemma lem7132629 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7132628 t1 t2 t3). Qed.
Lemma lem7132630 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7132631 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7132630 t1 t2 t3) (@lem7132629 t1 t2 t3)). Qed.
Lemma lem7132632 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7132631 t1 t2 t3)). Qed.
Lemma lem7132634 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7132635 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (@lem7132634 (term8 A)). Qed.
Lemma lem7132636 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem7132635 A)). Qed.
Lemma lem7132637 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem7132638 {A : Type'} : term11 A.
Proof. exact (@lem7132622 A). Qed.
Lemma lem7132644 {A : Type'} : term12 A.
Proof. exact (@lem3863773 A). Qed.
Lemma lem7132649 {_100044 A : Type'} (h1 : term13 _100044 A) : term13 _100044 A.
Proof. exact (h1). Qed.
Lemma lem7132650 {_100044 A : Type'} : term14 _100044 A.
Proof. exact (fun h0 : term13 _100044 A => @lem7132649 _100044 A h0). Qed.
Lemma lem7132651 {_100044 A : Type'} (h1 : term14 _100044 A) : term14 _100044 A.
Proof. exact (h1). Qed.
Lemma lem7132652 {_100044 A : Type'} (h1 : term13 _100044 A) : term13 _100044 A.
Proof. exact (h1). Qed.
Lemma lem7132653 {_100044 A : Type'} (h1 : term13 _100044 A) (h2 : term14 _100044 A) : term13 _100044 A.
Proof. exact (@lem7132651 _100044 A h2 (@lem7132652 _100044 A h1)). Qed.
Lemma lem7132654 {_100044 A : Type'} (h1 : term13 _100044 A) : term15 _100044 A.
Proof. exact (fun h0 : term14 _100044 A => @lem7132653 _100044 A h1 h0). Qed.
Lemma lem7132655 {_100044 A : Type'} (h1 : term14 _100044 A) : term14 _100044 A.
Proof. exact (h1). Qed.
Lemma lem7132656 {_100044 A : Type'} (h1 : term13 _100044 A) (h2 : term14 _100044 A) : term13 _100044 A.
Proof. exact (@lem7132654 _100044 A h1 (@lem7132655 _100044 A h2)). Qed.
Lemma lem7132657 {_100044 A : Type'} (h1 : term14 _100044 A) : term14 _100044 A.
Proof. exact (fun h0 : term13 _100044 A => @lem7132656 _100044 A h0 h1). Qed.
Lemma lem7132658 {_100044 A : Type'} : term16 _100044 A.
Proof. exact (fun h0 : term14 _100044 A => @lem7132657 _100044 A h0). Qed.
Lemma lem7132661 {_100044 A : Type'} : term14 _100044 A.
Proof. exact (@lem7132658 _100044 A (@lem7132650 _100044 A)). Qed.
Lemma lem7132662 {_100044 A : Type'} : term14 _100044 A.
Proof. exact (@lem7132661 _100044 A). Qed.
Lemma lem7132742 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7132743 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem7132742 (term11 A)). Qed.
Lemma lem7132766 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem7132767 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem7132766) (@lem7132743 A)). Qed.
Lemma lem7132770 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem7132771 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem7132770) (@lem7132767 A)). Qed.
Lemma lem7132774 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (eq_refl (term25 A)). Qed.
Lemma lem7132775 {A : Type'} : (term26 A) = (term27 A).
Proof. exact (MK_COMB (@lem7132774 A) (@lem7132771 A)). Qed.
Lemma lem7132778 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (eq_refl (term28 A)). Qed.
Lemma lem7132779 {A : Type'} : (term29 A) = (term30 A).
Proof. exact (MK_COMB (@lem7132778 A) (@lem7132775 A)). Qed.
Lemma lem7132782 {_100044 : Type'} : (term28 _100044) = (term28 _100044).
Proof. exact (eq_refl (term28 _100044)). Qed.
Lemma lem7132783 {_100044 A : Type'} : (term31 _100044 A) = (term32 _100044 A).
Proof. exact (MK_COMB (@lem7132782 _100044) (@lem7132779 A)). Qed.
Lemma lem7132786 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (eq_refl (term33 A)). Qed.
Lemma lem7132793 {_100044 A : Type'} : (term13 _100044 A) = (term34 _100044 A).
Proof. exact (MK_COMB (@lem7132786 A) (@lem7132783 _100044 A)). Qed.
Lemma lem7132794 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term35 A f s b) = (term35 A f s b).
Proof. exact (eq_refl (term35 A f s b)). Qed.
Lemma lem7132799 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term36 A s f x b) = (term36 A s f x b).
Proof. exact (eq_refl (term36 A s f x b)). Qed.
Lemma lem7132800 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term37 A s f b) = (term37 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7132799 A s f x b)). Qed.
Lemma lem7132801 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7132802 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term38 A s f b) = (term38 A s f b).
Proof. exact (MK_COMB (@lem7132801 A) (@lem7132800 A s f b)). Qed.
Lemma lem7132805 {A : Type'} (s : A -> Prop) : (term39 A s) = (term39 A s).
Proof. exact (eq_refl (term39 A s)). Qed.
Lemma lem7132806 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term40 A s f b) = (term40 A s f b).
Proof. exact (MK_COMB (@lem7132805 A s) (@lem7132802 A s f b)). Qed.
Lemma lem7132807 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7132808 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term41 A s f b) = (term41 A s f b).
Proof. exact (MK_COMB (@lem7132807) (@lem7132806 A s f b)). Qed.
Lemma lem7132809 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term42 A f s b) = (term42 A f s b).
Proof. exact (MK_COMB (@lem7132808 A s f b) (@lem7132794 A f s b)). Qed.
Lemma lem7132810 {A : Type'} (f : A -> real) (s : A -> Prop) : (term43 A f s) = (term43 A f s).
Proof. exact (fun_ext (fun b : real => @lem7132809 A f s b)). Qed.
Lemma lem7132811 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7132812 {A : Type'} (f : A -> real) (s : A -> Prop) : (term44 A f s) = (term44 A f s).
Proof. exact (MK_COMB (@lem7132811) (@lem7132810 A f s)). Qed.
Lemma lem7132813 {A : Type'} (s : A -> Prop) : (term45 A s) = (term45 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7132812 A f s)). Qed.
Lemma lem7132814 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7132815 {A : Type'} (s : A -> Prop) : (term46 A s) = (term46 A s).
Proof. exact (MK_COMB (@lem7132814 A) (@lem7132813 A s)). Qed.
Lemma lem7132816 {A : Type'} : (term47 A) = (term47 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7132815 A s)). Qed.
Lemma lem7132817 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7132818 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem7132817 A) (@lem7132816 A)). Qed.
Lemma lem7132819 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7132820 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem7132819) (@lem7132818 A)). Qed.
Lemma lem7132827 (y : real) (x : real) : (term48 y x) = (term48 y x).
Proof. exact (eq_refl (term48 y x)). Qed.
Lemma lem7132828 (x : real) : (term49 x) = (term49 x).
Proof. exact (fun_ext (fun y : real => @lem7132827 y x)). Qed.
Lemma lem7132829 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7132830 (x : real) : (term50 x) = (term50 x).
Proof. exact (MK_COMB (@lem7132829) (@lem7132828 x)). Qed.
Lemma lem7132831 : term51 = term51.
Proof. exact (fun_ext (fun x : real => @lem7132830 x)). Qed.
Lemma lem7132832 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7132833 : term52 = term52.
Proof. exact (MK_COMB (@lem7132832) (@lem7132831)). Qed.
Lemma lem7132834 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7132835 : term19 = term19.
Proof. exact (MK_COMB (@lem7132834) (@lem7132833)). Qed.
Lemma lem7132836 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (MK_COMB (@lem7132835) (@lem7132820 A)). Qed.
Lemma lem7132841 (m : nat) (n : nat) : (((real_of_num m) = (real_of_num n)) = (m = n)) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (((real_of_num m) = (real_of_num n)) = (m = n))). Qed.
Lemma lem7132842 (m : nat) : (term53 m) = (term53 m).
Proof. exact (fun_ext (fun n : nat => @lem7132841 m n)). Qed.
Lemma lem7132843 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7132844 (m : nat) : (term54 m) = (term54 m).
Proof. exact (MK_COMB (@lem7132843) (@lem7132842 m)). Qed.
Lemma lem7132845 : term55 = term55.
Proof. exact (fun_ext (fun m : nat => @lem7132844 m)). Qed.
Lemma lem7132846 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7132847 : term56 = term56.
Proof. exact (MK_COMB (@lem7132846) (@lem7132845)). Qed.
Lemma lem7132848 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7132849 : term22 = term22.
Proof. exact (MK_COMB (@lem7132848) (@lem7132847)). Qed.
Lemma lem7132850 {A : Type'} : (term24 A) = (term24 A).
Proof. exact (MK_COMB (@lem7132849) (@lem7132836 A)). Qed.
Lemma lem7132855 {A : Type'} (s : A -> Prop) : ((term57 A s) = (s = (@EMPTY A))) = ((term57 A s) = (s = (@EMPTY A))).
Proof. exact (eq_refl ((term57 A s) = (s = (@EMPTY A)))). Qed.
Lemma lem7132856 {A : Type'} : (term58 A) = (term58 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7132855 A s)). Qed.
Lemma lem7132857 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7132858 {A : Type'} : (term59 A) = (term59 A).
Proof. exact (MK_COMB (@lem7132857 A) (@lem7132856 A)). Qed.
Lemma lem7132859 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7132860 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (MK_COMB (@lem7132859) (@lem7132858 A)). Qed.
Lemma lem7132861 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (MK_COMB (@lem7132860 A) (@lem7132850 A)). Qed.
Lemma lem7132870 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term60 A s n)) = ((@HAS_SIZE A s n) = (term60 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE A s n) = (term60 A s n))). Qed.
Lemma lem7132871 {A : Type'} (s : A -> Prop) : (term61 A s) = (term61 A s).
Proof. exact (fun_ext (fun n : nat => @lem7132870 A s n)). Qed.
Lemma lem7132872 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7132873 {A : Type'} (s : A -> Prop) : (term62 A s) = (term62 A s).
Proof. exact (MK_COMB (@lem7132872) (@lem7132871 A s)). Qed.
Lemma lem7132874 {A : Type'} : (term63 A) = (term63 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7132873 A s)). Qed.
Lemma lem7132875 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7132876 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem7132875 A) (@lem7132874 A)). Qed.
Lemma lem7132877 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7132878 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem7132877) (@lem7132876 A)). Qed.
Lemma lem7132879 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (MK_COMB (@lem7132878 A) (@lem7132861 A)). Qed.
Lemma lem7132888 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term60 _100044 s n)) = ((@HAS_SIZE _100044 s n) = (term60 _100044 s n)).
Proof. exact (eq_refl ((@HAS_SIZE _100044 s n) = (term60 _100044 s n))). Qed.
Lemma lem7132889 {_100044 : Type'} (s : _100044 -> Prop) : (term61 _100044 s) = (term61 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7132888 _100044 s n)). Qed.
Lemma lem7132890 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7132891 {_100044 : Type'} (s : _100044 -> Prop) : (term62 _100044 s) = (term62 _100044 s).
Proof. exact (MK_COMB (@lem7132890) (@lem7132889 _100044 s)). Qed.
Lemma lem7132892 {_100044 : Type'} : (term63 _100044) = (term63 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7132891 _100044 s)). Qed.
Lemma lem7132893 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7132894 {_100044 : Type'} : (term12 _100044) = (term12 _100044).
Proof. exact (MK_COMB (@lem7132893 _100044) (@lem7132892 _100044)). Qed.
Lemma lem7132895 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7132896 {_100044 : Type'} : (term28 _100044) = (term28 _100044).
Proof. exact (MK_COMB (@lem7132895) (@lem7132894 _100044)). Qed.
Lemma lem7132897 {_100044 A : Type'} : (term32 _100044 A) = (term32 _100044 A).
Proof. exact (MK_COMB (@lem7132896 _100044) (@lem7132879 A)). Qed.
Lemma lem7132898 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term64 A s f b) = (term64 A s f b).
Proof. exact (eq_refl (term64 A s f b)). Qed.
Lemma lem7132903 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term65 A f x b s) = (term65 A f x b s).
Proof. exact (eq_refl (term65 A f x b s)). Qed.
Lemma lem7132904 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term66 A f b s) = (term66 A f b s).
Proof. exact (fun_ext (fun x : A => @lem7132903 A f x b s)). Qed.
Lemma lem7132905 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7132906 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term67 A f b s) = (term67 A f b s).
Proof. exact (MK_COMB (@lem7132905 A) (@lem7132904 A f b s)). Qed.
Lemma lem7132911 {A : Type'} (s : A -> Prop) : (term68 A s) = (term68 A s).
Proof. exact (eq_refl (term68 A s)). Qed.
Lemma lem7132912 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term69 A f b s) = (term69 A f b s).
Proof. exact (MK_COMB (@lem7132911 A s) (@lem7132906 A f b s)). Qed.
Lemma lem7132915 {A : Type'} (s : A -> Prop) : (term39 A s) = (term39 A s).
Proof. exact (eq_refl (term39 A s)). Qed.
Lemma lem7132916 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term70 A f b s) = (term70 A f b s).
Proof. exact (MK_COMB (@lem7132915 A s) (@lem7132912 A f b s)). Qed.
Lemma lem7132917 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7132918 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term71 A f b s) = (term71 A f b s).
Proof. exact (MK_COMB (@lem7132917) (@lem7132916 A f b s)). Qed.
Lemma lem7132919 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term72 A s f b) = (term72 A s f b).
Proof. exact (MK_COMB (@lem7132918 A f b s) (@lem7132898 A s f b)). Qed.
Lemma lem7132920 {A : Type'} (s : A -> Prop) (f : A -> real) : (term73 A s f) = (term73 A s f).
Proof. exact (fun_ext (fun b : real => @lem7132919 A s f b)). Qed.
Lemma lem7132921 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7132922 {A : Type'} (s : A -> Prop) (f : A -> real) : (term74 A s f) = (term74 A s f).
Proof. exact (MK_COMB (@lem7132921) (@lem7132920 A s f)). Qed.
Lemma lem7132923 {A : Type'} (s : A -> Prop) : (term75 A s) = (term75 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7132922 A s f)). Qed.
Lemma lem7132924 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7132925 {A : Type'} (s : A -> Prop) : (term76 A s) = (term76 A s).
Proof. exact (MK_COMB (@lem7132924 A) (@lem7132923 A s)). Qed.
Lemma lem7132926 {A : Type'} : (term77 A) = (term77 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7132925 A s)). Qed.
Lemma lem7132927 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7132928 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (MK_COMB (@lem7132927 A) (@lem7132926 A)). Qed.
Lemma lem7132929 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7132930 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem7132929) (@lem7132928 A)). Qed.
Lemma lem7132931 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7132932 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (MK_COMB (@lem7132931) (@lem7132930 A)). Qed.
Lemma lem7132933 {_100044 A : Type'} : (term34 _100044 A) = (term34 _100044 A).
Proof. exact (MK_COMB (@lem7132932 A) (@lem7132897 _100044 A)). Qed.
Lemma lem7133070 {_100044 A : Type'} : (term13 _100044 A) = (term34 _100044 A).
Proof. exact (TRANS (@lem7132793 _100044 A) (@lem7132933 _100044 A)). Qed.
Lemma lem7133071 {_100044 A : Type'} : (term34 _100044 A) = (term13 _100044 A).
Proof. exact (SYM (@lem7133070 _100044 A)). Qed.
Lemma lem7133072 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem7133074 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem7133075 {A : Type'} (h1 : term59 A) : term59 A.
Proof. exact (h1). Qed.
Lemma lem7133076 (h1 : term56) : term56.
Proof. exact (h1). Qed.
Lemma lem7133077 (h1 : term52) : term52.
Proof. exact (h1). Qed.
Lemma lem7133078 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem7133087 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term65 A f x b s) = (term78 A f x b s).
Proof. exact (@lem17265 (@IN A x s) (term79 A f x b s)). Qed.
Lemma lem7133088 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term66 A f b s) = (term80 A f b s).
Proof. exact (fun_ext (fun x : A => @lem7133087 A f x b s)). Qed.
Lemma lem7133089 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7133090 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term67 A f b s) = (term81 A f b s).
Proof. exact (MK_COMB (@lem7133089 A) (@lem7133088 A f b s)). Qed.
Lemma lem7133092 {A : Type'} (s : A -> Prop) : (term68 A s) = (term68 A s).
Proof. exact (eq_refl (term68 A s)). Qed.
Lemma lem7133093 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term69 A f b s) = (term82 A f b s).
Proof. exact (MK_COMB (@lem7133092 A s) (@lem7133090 A f b s)). Qed.
Lemma lem7133095 {A : Type'} (s : A -> Prop) : (term39 A s) = (term39 A s).
Proof. exact (eq_refl (term39 A s)). Qed.
Lemma lem7133096 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term70 A f b s) = (term83 A f b s).
Proof. exact (MK_COMB (@lem7133095 A s) (@lem7133093 A f b s)). Qed.
Lemma lem7133097 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term84 A s f b) = (term84 A s f b).
Proof. exact (eq_refl (term84 A s f b)). Qed.
Lemma lem7133098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7133099 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term85 A f b s) = (term86 A f b s).
Proof. exact (MK_COMB (@lem7133098) (@lem7133096 A f b s)). Qed.
Lemma lem7133100 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term87 A s f b) = (term88 A s f b).
Proof. exact (MK_COMB (@lem7133099 A f b s) (@lem7133097 A s f b)). Qed.
Lemma lem7133101 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term89 A s f b) = (term87 A s f b).
Proof. exact (@lem17362 (term70 A f b s) (term64 A s f b)). Qed.
Lemma lem7133102 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term89 A s f b) = (term88 A s f b).
Proof. exact (TRANS (@lem7133101 A s f b) (@lem7133100 A s f b)). Qed.
Lemma lem7133103 (P : real -> Prop) : (term90 P) = (term91 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7133104 {A : Type'} (s : A -> Prop) (f : A -> real) : (term92 A s f) = (term93 A s f).
Proof. exact (@lem7133103 (term73 A s f)). Qed.
Lemma lem7133105 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term94 A s f b) = (term72 A s f b).
Proof. exact (eq_refl (term94 A s f b)). Qed.
Lemma lem7133106 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7133107 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term95 A s f b) = (term89 A s f b).
Proof. exact (MK_COMB (@lem7133106) (@lem7133105 A s f b)). Qed.
Lemma lem7133108 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term95 A s f b) = (term88 A s f b).
Proof. exact (TRANS (@lem7133107 A s f b) (@lem7133102 A s f b)). Qed.
Lemma lem7133109 {A : Type'} (s : A -> Prop) (f : A -> real) : (term96 A s f) = (term97 A s f).
Proof. exact (fun_ext (fun b : real => @lem7133108 A s f b)). Qed.
Lemma lem7133110 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7133111 {A : Type'} (s : A -> Prop) (f : A -> real) : (term93 A s f) = (term98 A s f).
Proof. exact (MK_COMB (@lem7133110) (@lem7133109 A s f)). Qed.
Lemma lem7133112 {A : Type'} (s : A -> Prop) (f : A -> real) : (term92 A s f) = (term98 A s f).
Proof. exact (TRANS (@lem7133104 A s f) (@lem7133111 A s f)). Qed.
Lemma lem7133113 {A : Type'} (P : type716 A) : (term99 A P) = (term100 A P).
Proof. exact (@lem18392 (A -> real) P). Qed.
Lemma lem7133114 {A : Type'} (s : A -> Prop) : (term101 A s) = (term102 A s).
Proof. exact (@lem7133113 A (term75 A s)). Qed.
Lemma lem7133115 {A : Type'} (s : A -> Prop) (f : A -> real) : (term103 A s f) = (term74 A s f).
Proof. exact (eq_refl (term103 A s f)). Qed.
Lemma lem7133116 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7133117 {A : Type'} (s : A -> Prop) (f : A -> real) : (term104 A s f) = (term92 A s f).
Proof. exact (MK_COMB (@lem7133116) (@lem7133115 A s f)). Qed.
Lemma lem7133118 {A : Type'} (s : A -> Prop) (f : A -> real) : (term104 A s f) = (term98 A s f).
Proof. exact (TRANS (@lem7133117 A s f) (@lem7133112 A s f)). Qed.
Lemma lem7133119 {A : Type'} (s : A -> Prop) : (term105 A s) = (term106 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7133118 A s f)). Qed.
Lemma lem7133120 {A : Type'} : (@ex (A -> real)) = (@ex (A -> real)).
Proof. exact (eq_refl (@ex (A -> real))). Qed.
Lemma lem7133121 {A : Type'} (s : A -> Prop) : (term102 A s) = (term107 A s).
Proof. exact (MK_COMB (@lem7133120 A) (@lem7133119 A s)). Qed.
Lemma lem7133122 {A : Type'} (s : A -> Prop) : (term101 A s) = (term107 A s).
Proof. exact (TRANS (@lem7133114 A s) (@lem7133121 A s)). Qed.
Lemma lem7133123 {A : Type'} (P : type686 A) : (term108 A P) = (term109 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem7133124 {A : Type'} : (term10 A) = (term110 A).
Proof. exact (@lem7133123 A (term77 A)). Qed.
Lemma lem7133125 {A : Type'} (s : A -> Prop) : (term111 A s) = (term76 A s).
Proof. exact (eq_refl (term111 A s)). Qed.
Lemma lem7133126 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7133127 {A : Type'} (s : A -> Prop) : (term112 A s) = (term101 A s).
Proof. exact (MK_COMB (@lem7133126) (@lem7133125 A s)). Qed.
Lemma lem7133128 {A : Type'} (s : A -> Prop) : (term112 A s) = (term107 A s).
Proof. exact (TRANS (@lem7133127 A s) (@lem7133122 A s)). Qed.
Lemma lem7133129 {A : Type'} : (term113 A) = (term114 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7133128 A s)). Qed.
Lemma lem7133130 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7133131 {A : Type'} : (term110 A) = (term115 A).
Proof. exact (MK_COMB (@lem7133130 A) (@lem7133129 A)). Qed.
Lemma lem7133240 {A : Type'} : (term10 A) = (term115 A).
Proof. exact (TRANS (@lem7133124 A) (@lem7133131 A)). Qed.
Lemma lem7133241 {A : Type'} (h1 : term10 A) : term115 A.
Proof. exact (EQ_MP (@lem7133240 A) (@lem7133072 A h1)). Qed.
Lemma lem7133549 {A : Type'} (s : A -> Prop) (n : nat) : (term116 A s n) = (term117 A s n).
Proof. exact (@lem17045 (@FINITE A s) ((@CARD A s) = n)). Qed.
Lemma lem7133555 {A : Type'} (s : A -> Prop) (n : nat) : (term118 A s n) = (term118 A s n).
Proof. exact (eq_refl (term118 A s n)). Qed.
Lemma lem7133557 {A : Type'} (s : A -> Prop) (n : nat) : (term119 A s n) = (term119 A s n).
Proof. exact (eq_refl (term119 A s n)). Qed.
Lemma lem7133558 {A : Type'} (s : A -> Prop) (n : nat) : (term120 A s n) = (term121 A s n).
Proof. exact (MK_COMB (@lem7133557 A s n) (@lem7133549 A s n)). Qed.
Lemma lem7133559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7133560 {A : Type'} (s : A -> Prop) (n : nat) : (term122 A s n) = (term123 A s n).
Proof. exact (MK_COMB (@lem7133559) (@lem7133558 A s n)). Qed.
Lemma lem7133561 {A : Type'} (s : A -> Prop) (n : nat) : (term124 A s n) = (term125 A s n).
Proof. exact (MK_COMB (@lem7133560 A s n) (@lem7133555 A s n)). Qed.
Lemma lem7133562 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term60 A s n)) = (term124 A s n).
Proof. exact (@lem17784 (@HAS_SIZE A s n) (term60 A s n)). Qed.
Lemma lem7133563 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term60 A s n)) = (term125 A s n).
Proof. exact (TRANS (@lem7133562 A s n) (@lem7133561 A s n)). Qed.
Lemma lem7133564 {A : Type'} (s : A -> Prop) : (term61 A s) = (term126 A s).
Proof. exact (fun_ext (fun n : nat => @lem7133563 A s n)). Qed.
Lemma lem7133565 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7133566 {A : Type'} (s : A -> Prop) : (term62 A s) = (term127 A s).
Proof. exact (MK_COMB (@lem7133565) (@lem7133564 A s)). Qed.
Lemma lem7133567 {A : Type'} : (term63 A) = (term128 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7133566 A s)). Qed.
Lemma lem7133568 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7133569 {A : Type'} : (term12 A) = (term129 A).
Proof. exact (MK_COMB (@lem7133568 A) (@lem7133567 A)). Qed.
Lemma lem7133575 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7133576 (P : nat -> Prop) (Q : nat -> Prop) : (term132 P Q) = (term133 P Q).
Proof. exact (@lem7133575 nat P Q). Qed.
Lemma lem7133577 {A : Type'} (s : A -> Prop) : (term134 A s) = (term135 A s).
Proof. exact (@lem7133576 (term136 A s) (term137 A s)). Qed.
Lemma lem7133578 {A : Type'} (s : A -> Prop) (n : nat) : (term138 A s n) = (term121 A s n).
Proof. exact (eq_refl (term138 A s n)). Qed.
Lemma lem7133579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7133580 {A : Type'} (s : A -> Prop) (n : nat) : (term139 A s n) = (term123 A s n).
Proof. exact (MK_COMB (@lem7133579) (@lem7133578 A s n)). Qed.
Lemma lem7133581 {A : Type'} (s : A -> Prop) (n : nat) : (term140 A s n) = (term118 A s n).
Proof. exact (eq_refl (term140 A s n)). Qed.
Lemma lem7133582 {A : Type'} (s : A -> Prop) (n : nat) : (term141 A s n) = (term125 A s n).
Proof. exact (MK_COMB (@lem7133580 A s n) (@lem7133581 A s n)). Qed.
Lemma lem7133583 {A : Type'} (s : A -> Prop) : (term142 A s) = (term126 A s).
Proof. exact (fun_ext (fun n : nat => @lem7133582 A s n)). Qed.
Lemma lem7133584 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7133585 {A : Type'} (s : A -> Prop) : (term134 A s) = (term127 A s).
Proof. exact (MK_COMB (@lem7133584) (@lem7133583 A s)). Qed.
Lemma lem7133586 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7133587 {A : Type'} (s : A -> Prop) : (term143 A s) = (term144 A s).
Proof. exact (MK_COMB (@lem7133586) (@lem7133585 A s)). Qed.
Lemma lem7133588 {A : Type'} (s : A -> Prop) (n : nat) : (term138 A s n) = (term121 A s n).
Proof. exact (eq_refl (term138 A s n)). Qed.
Lemma lem7133589 {A : Type'} (s : A -> Prop) : (term145 A s) = (term136 A s).
Proof. exact (fun_ext (fun n : nat => @lem7133588 A s n)). Qed.
Lemma lem7133590 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7133591 {A : Type'} (s : A -> Prop) : (term146 A s) = (term147 A s).
Proof. exact (MK_COMB (@lem7133590) (@lem7133589 A s)). Qed.
Lemma lem7133592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7133593 {A : Type'} (s : A -> Prop) : (term148 A s) = (term149 A s).
Proof. exact (MK_COMB (@lem7133592) (@lem7133591 A s)). Qed.
Lemma lem7133594 {A : Type'} (s : A -> Prop) (n : nat) : (term140 A s n) = (term118 A s n).
Proof. exact (eq_refl (term140 A s n)). Qed.
Lemma lem7133595 {A : Type'} (s : A -> Prop) : (term150 A s) = (term137 A s).
Proof. exact (fun_ext (fun n : nat => @lem7133594 A s n)). Qed.
Lemma lem7133596 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7133597 {A : Type'} (s : A -> Prop) : (term151 A s) = (term152 A s).
Proof. exact (MK_COMB (@lem7133596) (@lem7133595 A s)). Qed.
Lemma lem7133598 {A : Type'} (s : A -> Prop) : (term135 A s) = (term153 A s).
Proof. exact (MK_COMB (@lem7133593 A s) (@lem7133597 A s)). Qed.
Lemma lem7133599 {A : Type'} (s : A -> Prop) : ((term134 A s) = (term135 A s)) = ((term127 A s) = (term153 A s)).
Proof. exact (MK_COMB (@lem7133587 A s) (@lem7133598 A s)). Qed.
Lemma lem7133600 {A : Type'} (s : A -> Prop) : (term127 A s) = (term153 A s).
Proof. exact (EQ_MP (@lem7133599 A s) (@lem7133577 A s)). Qed.
Lemma lem7133697 {A : Type'} : (term128 A) = (term154 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7133600 A s)). Qed.
Lemma lem7133698 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7133699 {A : Type'} : (term129 A) = (term155 A).
Proof. exact (MK_COMB (@lem7133698 A) (@lem7133697 A)). Qed.
Lemma lem7133701 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7133702 {A : Type'} (P : type686 A) (Q : type686 A) : (term156 A P Q) = (term157 A P Q).
Proof. exact (@lem7133701 (A -> Prop) P Q). Qed.
Lemma lem7133703 {A : Type'} : (term158 A) = (term159 A).
Proof. exact (@lem7133702 A (term160 A) (term161 A)). Qed.
Lemma lem7133704 {A : Type'} (s : A -> Prop) : (term162 A s) = (term147 A s).
Proof. exact (eq_refl (term162 A s)). Qed.
Lemma lem7133705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7133706 {A : Type'} (s : A -> Prop) : (term163 A s) = (term149 A s).
Proof. exact (MK_COMB (@lem7133705) (@lem7133704 A s)). Qed.
Lemma lem7133707 {A : Type'} (s : A -> Prop) : (term164 A s) = (term152 A s).
Proof. exact (eq_refl (term164 A s)). Qed.
Lemma lem7133708 {A : Type'} (s : A -> Prop) : (term165 A s) = (term153 A s).
Proof. exact (MK_COMB (@lem7133706 A s) (@lem7133707 A s)). Qed.
Lemma lem7133709 {A : Type'} : (term166 A) = (term154 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7133708 A s)). Qed.
Lemma lem7133710 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7133711 {A : Type'} : (term158 A) = (term155 A).
Proof. exact (MK_COMB (@lem7133710 A) (@lem7133709 A)). Qed.
Lemma lem7133712 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7133713 {A : Type'} : (term167 A) = (term168 A).
Proof. exact (MK_COMB (@lem7133712) (@lem7133711 A)). Qed.
Lemma lem7133714 {A : Type'} (s : A -> Prop) : (term162 A s) = (term147 A s).
Proof. exact (eq_refl (term162 A s)). Qed.
Lemma lem7133715 {A : Type'} : (term169 A) = (term160 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7133714 A s)). Qed.
Lemma lem7133716 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7133717 {A : Type'} : (term170 A) = (term171 A).
Proof. exact (MK_COMB (@lem7133716 A) (@lem7133715 A)). Qed.
Lemma lem7133718 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7133719 {A : Type'} : (term172 A) = (term173 A).
Proof. exact (MK_COMB (@lem7133718) (@lem7133717 A)). Qed.
Lemma lem7133720 {A : Type'} (s : A -> Prop) : (term164 A s) = (term152 A s).
Proof. exact (eq_refl (term164 A s)). Qed.
Lemma lem7133721 {A : Type'} : (term174 A) = (term161 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7133720 A s)). Qed.
Lemma lem7133722 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7133723 {A : Type'} : (term175 A) = (term176 A).
Proof. exact (MK_COMB (@lem7133722 A) (@lem7133721 A)). Qed.
Lemma lem7133724 {A : Type'} : (term159 A) = (term177 A).
Proof. exact (MK_COMB (@lem7133719 A) (@lem7133723 A)). Qed.
Lemma lem7133725 {A : Type'} : ((term158 A) = (term159 A)) = ((term155 A) = (term177 A)).
Proof. exact (MK_COMB (@lem7133713 A) (@lem7133724 A)). Qed.
Lemma lem7133726 {A : Type'} : (term155 A) = (term177 A).
Proof. exact (EQ_MP (@lem7133725 A) (@lem7133703 A)). Qed.
Lemma lem7133833 {A : Type'} : (term129 A) = (term177 A).
Proof. exact (TRANS (@lem7133699 A) (@lem7133726 A)). Qed.
Lemma lem7133834 {A : Type'} : (term12 A) = (term177 A).
Proof. exact (TRANS (@lem7133569 A) (@lem7133833 A)). Qed.
Lemma lem7133835 {A : Type'} (h1 : term12 A) : term177 A.
Proof. exact (EQ_MP (@lem7133834 A) (@lem7133074 A h1)). Qed.
Lemma lem7133850 {A : Type'} (s : A -> Prop) : ((term57 A s) = (s = (@EMPTY A))) = (term178 A s).
Proof. exact (@lem17784 (term57 A s) (s = (@EMPTY A))). Qed.
Lemma lem7133851 {A : Type'} : (term58 A) = (term179 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7133850 A s)). Qed.
Lemma lem7133852 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7133853 {A : Type'} : (term59 A) = (term180 A).
Proof. exact (MK_COMB (@lem7133852 A) (@lem7133851 A)). Qed.
Lemma lem7133855 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7133856 {A : Type'} (P : type686 A) (Q : type686 A) : (term156 A P Q) = (term157 A P Q).
Proof. exact (@lem7133855 (A -> Prop) P Q). Qed.
Lemma lem7133857 {A : Type'} : (term181 A) = (term182 A).
Proof. exact (@lem7133856 A (term183 A) (term184 A)). Qed.
Lemma lem7133858 {A : Type'} (s : A -> Prop) : (term185 A s) = (term186 A s).
Proof. exact (eq_refl (term185 A s)). Qed.
Lemma lem7133859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7133860 {A : Type'} (s : A -> Prop) : (term187 A s) = (term188 A s).
Proof. exact (MK_COMB (@lem7133859) (@lem7133858 A s)). Qed.
Lemma lem7133861 {A : Type'} (s : A -> Prop) : (term189 A s) = (term190 A s).
Proof. exact (eq_refl (term189 A s)). Qed.
Lemma lem7133862 {A : Type'} (s : A -> Prop) : (term191 A s) = (term178 A s).
Proof. exact (MK_COMB (@lem7133860 A s) (@lem7133861 A s)). Qed.
Lemma lem7133863 {A : Type'} : (term192 A) = (term179 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7133862 A s)). Qed.
Lemma lem7133864 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7133865 {A : Type'} : (term181 A) = (term180 A).
Proof. exact (MK_COMB (@lem7133864 A) (@lem7133863 A)). Qed.
Lemma lem7133866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7133867 {A : Type'} : (term193 A) = (term194 A).
Proof. exact (MK_COMB (@lem7133866) (@lem7133865 A)). Qed.
Lemma lem7133868 {A : Type'} (s : A -> Prop) : (term185 A s) = (term186 A s).
Proof. exact (eq_refl (term185 A s)). Qed.
Lemma lem7133869 {A : Type'} : (term195 A) = (term183 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7133868 A s)). Qed.
Lemma lem7133870 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7133871 {A : Type'} : (term196 A) = (term197 A).
Proof. exact (MK_COMB (@lem7133870 A) (@lem7133869 A)). Qed.
Lemma lem7133872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7133873 {A : Type'} : (term198 A) = (term199 A).
Proof. exact (MK_COMB (@lem7133872) (@lem7133871 A)). Qed.
Lemma lem7133874 {A : Type'} (s : A -> Prop) : (term189 A s) = (term190 A s).
Proof. exact (eq_refl (term189 A s)). Qed.
Lemma lem7133875 {A : Type'} : (term200 A) = (term184 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7133874 A s)). Qed.
Lemma lem7133876 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7133877 {A : Type'} : (term201 A) = (term202 A).
Proof. exact (MK_COMB (@lem7133876 A) (@lem7133875 A)). Qed.
Lemma lem7133878 {A : Type'} : (term182 A) = (term203 A).
Proof. exact (MK_COMB (@lem7133873 A) (@lem7133877 A)). Qed.
Lemma lem7133879 {A : Type'} : ((term181 A) = (term182 A)) = ((term180 A) = (term203 A)).
Proof. exact (MK_COMB (@lem7133867 A) (@lem7133878 A)). Qed.
Lemma lem7133978 {A : Type'} : (term180 A) = (term203 A).
Proof. exact (EQ_MP (@lem7133879 A) (@lem7133857 A)). Qed.
Lemma lem7133979 {A : Type'} : (term59 A) = (term203 A).
Proof. exact (TRANS (@lem7133853 A) (@lem7133978 A)). Qed.
Lemma lem7133980 {A : Type'} (h1 : term59 A) : term203 A.
Proof. exact (EQ_MP (@lem7133979 A) (@lem7133075 A h1)). Qed.
Lemma lem7133995 (m : nat) (n : nat) : (((real_of_num m) = (real_of_num n)) = (m = n)) = (term204 m n).
Proof. exact (@lem17784 ((real_of_num m) = (real_of_num n)) (m = n)). Qed.
Lemma lem7133996 (m : nat) : (term53 m) = (term205 m).
Proof. exact (fun_ext (fun n : nat => @lem7133995 m n)). Qed.
Lemma lem7133997 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7133998 (m : nat) : (term54 m) = (term206 m).
Proof. exact (MK_COMB (@lem7133997) (@lem7133996 m)). Qed.
Lemma lem7133999 : term55 = term207.
Proof. exact (fun_ext (fun m : nat => @lem7133998 m)). Qed.
Lemma lem7134000 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7134001 : term56 = term208.
Proof. exact (MK_COMB (@lem7134000) (@lem7133999)). Qed.
Lemma lem7134007 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7134008 (P : nat -> Prop) (Q : nat -> Prop) : (term132 P Q) = (term133 P Q).
Proof. exact (@lem7134007 nat P Q). Qed.
Lemma lem7134009 (m : nat) : (term209 m) = (term210 m).
Proof. exact (@lem7134008 (term211 m) (term212 m)). Qed.
Lemma lem7134010 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (eq_refl (term213 m n)). Qed.
Lemma lem7134011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7134012 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (MK_COMB (@lem7134011) (@lem7134010 m n)). Qed.
Lemma lem7134013 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (eq_refl (term217 m n)). Qed.
Lemma lem7134014 (m : nat) (n : nat) : (term219 m n) = (term204 m n).
Proof. exact (MK_COMB (@lem7134012 m n) (@lem7134013 m n)). Qed.
Lemma lem7134015 (m : nat) : (term220 m) = (term205 m).
Proof. exact (fun_ext (fun n : nat => @lem7134014 m n)). Qed.
Lemma lem7134016 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7134017 (m : nat) : (term209 m) = (term206 m).
Proof. exact (MK_COMB (@lem7134016) (@lem7134015 m)). Qed.
Lemma lem7134018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7134019 (m : nat) : (term221 m) = (term222 m).
Proof. exact (MK_COMB (@lem7134018) (@lem7134017 m)). Qed.
Lemma lem7134020 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (eq_refl (term213 m n)). Qed.
Lemma lem7134021 (m : nat) : (term223 m) = (term211 m).
Proof. exact (fun_ext (fun n : nat => @lem7134020 m n)). Qed.
Lemma lem7134022 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7134023 (m : nat) : (term224 m) = (term225 m).
Proof. exact (MK_COMB (@lem7134022) (@lem7134021 m)). Qed.
Lemma lem7134024 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7134025 (m : nat) : (term226 m) = (term227 m).
Proof. exact (MK_COMB (@lem7134024) (@lem7134023 m)). Qed.
Lemma lem7134026 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (eq_refl (term217 m n)). Qed.
Lemma lem7134027 (m : nat) : (term228 m) = (term212 m).
Proof. exact (fun_ext (fun n : nat => @lem7134026 m n)). Qed.
Lemma lem7134028 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7134029 (m : nat) : (term229 m) = (term230 m).
Proof. exact (MK_COMB (@lem7134028) (@lem7134027 m)). Qed.
Lemma lem7134030 (m : nat) : (term210 m) = (term231 m).
Proof. exact (MK_COMB (@lem7134025 m) (@lem7134029 m)). Qed.
Lemma lem7134031 (m : nat) : ((term209 m) = (term210 m)) = ((term206 m) = (term231 m)).
Proof. exact (MK_COMB (@lem7134019 m) (@lem7134030 m)). Qed.
Lemma lem7134032 (m : nat) : (term206 m) = (term231 m).
Proof. exact (EQ_MP (@lem7134031 m) (@lem7134009 m)). Qed.
Lemma lem7134129 : term207 = term232.
Proof. exact (fun_ext (fun m : nat => @lem7134032 m)). Qed.
Lemma lem7134130 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7134131 : term208 = term233.
Proof. exact (MK_COMB (@lem7134130) (@lem7134129)). Qed.
Lemma lem7134133 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7134134 (P : nat -> Prop) (Q : nat -> Prop) : (term132 P Q) = (term133 P Q).
Proof. exact (@lem7134133 nat P Q). Qed.
Lemma lem7134135 : term234 = term235.
Proof. exact (@lem7134134 term236 term237). Qed.
Lemma lem7134136 (m : nat) : (term238 m) = (term225 m).
Proof. exact (eq_refl (term238 m)). Qed.
Lemma lem7134137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7134138 (m : nat) : (term239 m) = (term227 m).
Proof. exact (MK_COMB (@lem7134137) (@lem7134136 m)). Qed.
Lemma lem7134139 (m : nat) : (term240 m) = (term230 m).
Proof. exact (eq_refl (term240 m)). Qed.
Lemma lem7134140 (m : nat) : (term241 m) = (term231 m).
Proof. exact (MK_COMB (@lem7134138 m) (@lem7134139 m)). Qed.
Lemma lem7134141 : term242 = term232.
Proof. exact (fun_ext (fun m : nat => @lem7134140 m)). Qed.
Lemma lem7134142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7134143 : term234 = term233.
Proof. exact (MK_COMB (@lem7134142) (@lem7134141)). Qed.
Lemma lem7134144 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7134145 : term243 = term244.
Proof. exact (MK_COMB (@lem7134144) (@lem7134143)). Qed.
Lemma lem7134146 (m : nat) : (term238 m) = (term225 m).
Proof. exact (eq_refl (term238 m)). Qed.
Lemma lem7134147 : term245 = term236.
Proof. exact (fun_ext (fun m : nat => @lem7134146 m)). Qed.
Lemma lem7134148 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7134149 : term246 = term247.
Proof. exact (MK_COMB (@lem7134148) (@lem7134147)). Qed.
Lemma lem7134150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7134151 : term248 = term249.
Proof. exact (MK_COMB (@lem7134150) (@lem7134149)). Qed.
Lemma lem7134152 (m : nat) : (term240 m) = (term230 m).
Proof. exact (eq_refl (term240 m)). Qed.
Lemma lem7134153 : term250 = term237.
Proof. exact (fun_ext (fun m : nat => @lem7134152 m)). Qed.
Lemma lem7134154 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7134155 : term251 = term252.
Proof. exact (MK_COMB (@lem7134154) (@lem7134153)). Qed.
Lemma lem7134156 : term235 = term253.
Proof. exact (MK_COMB (@lem7134151) (@lem7134155)). Qed.
Lemma lem7134157 : (term234 = term235) = (term233 = term253).
Proof. exact (MK_COMB (@lem7134145) (@lem7134156)). Qed.
Lemma lem7134158 : term233 = term253.
Proof. exact (EQ_MP (@lem7134157) (@lem7134135)). Qed.
Lemma lem7134265 : term208 = term253.
Proof. exact (TRANS (@lem7134131) (@lem7134158)). Qed.
Lemma lem7134266 : term56 = term253.
Proof. exact (TRANS (@lem7134001) (@lem7134265)). Qed.
Lemma lem7134267 (h1 : term56) : term253.
Proof. exact (EQ_MP (@lem7134266) (@lem7133076 h1)). Qed.
Lemma lem7134270 (y : real) : (term254 y) = (y = term255).
Proof. exact (@lem16933 (y = term255)). Qed.
Lemma lem7134271 (y : real) (x : real) : ((term256 x y) = x) = ((term256 x y) = x).
Proof. exact (eq_refl ((term256 x y) = x)). Qed.
Lemma lem7134272 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7134273 (y : real) : (term257 y) = (term258 y).
Proof. exact (MK_COMB (@lem7134272) (@lem7134270 y)). Qed.
Lemma lem7134274 (y : real) (x : real) : (term259 y x) = (term260 y x).
Proof. exact (MK_COMB (@lem7134273 y) (@lem7134271 y x)). Qed.
Lemma lem7134275 (y : real) (x : real) : (term48 y x) = (term259 y x).
Proof. exact (@lem17265 (term261 y) ((term256 x y) = x)). Qed.
Lemma lem7134276 (y : real) (x : real) : (term48 y x) = (term260 y x).
Proof. exact (TRANS (@lem7134275 y x) (@lem7134274 y x)). Qed.
Lemma lem7134277 (x : real) : (term49 x) = (term262 x).
Proof. exact (fun_ext (fun y : real => @lem7134276 y x)). Qed.
Lemma lem7134278 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7134279 (x : real) : (term50 x) = (term263 x).
Proof. exact (MK_COMB (@lem7134278) (@lem7134277 x)). Qed.
Lemma lem7134280 : term51 = term264.
Proof. exact (fun_ext (fun x : real => @lem7134279 x)). Qed.
Lemma lem7134281 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7134338 : term52 = term265.
Proof. exact (MK_COMB (@lem7134281) (@lem7134280)). Qed.
Lemma lem7134339 (h1 : term52) : term265.
Proof. exact (EQ_MP (@lem7134338) (@lem7133077 h1)). Qed.
Lemma lem7134347 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term266 A s f x b) = (term267 A s f x b).
Proof. exact (@lem17362 (@IN A x s) (term268 A f x b)). Qed.
Lemma lem7134348 {A : Type'} (P : A -> Prop) : (term269 A P) = (term270 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7134349 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term271 A s f b) = (term272 A s f b).
Proof. exact (@lem7134348 A (term37 A s f b)). Qed.
Lemma lem7134350 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term273 A s f b x) = (term36 A s f x b).
Proof. exact (eq_refl (term273 A s f b x)). Qed.
Lemma lem7134351 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7134352 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term274 A s f b x) = (term266 A s f x b).
Proof. exact (MK_COMB (@lem7134351) (@lem7134350 A s f x b)). Qed.
Lemma lem7134353 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term274 A s f b x) = (term267 A s f x b).
Proof. exact (TRANS (@lem7134352 A s f x b) (@lem7134347 A s f x b)). Qed.
Lemma lem7134354 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term275 A s f b) = (term276 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7134353 A s f x b)). Qed.
Lemma lem7134355 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7134356 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term272 A s f b) = (term277 A s f b).
Proof. exact (MK_COMB (@lem7134355 A) (@lem7134354 A s f b)). Qed.
Lemma lem7134357 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term271 A s f b) = (term277 A s f b).
Proof. exact (TRANS (@lem7134349 A s f b) (@lem7134356 A s f b)). Qed.
Lemma lem7134359 {A : Type'} (s : A -> Prop) : (term278 A s) = (term278 A s).
Proof. exact (eq_refl (term278 A s)). Qed.
Lemma lem7134360 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term279 A s f b) = (term280 A s f b).
Proof. exact (MK_COMB (@lem7134359 A s) (@lem7134357 A s f b)). Qed.
Lemma lem7134361 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term281 A s f b) = (term279 A s f b).
Proof. exact (@lem17045 (@FINITE A s) (term38 A s f b)). Qed.
Lemma lem7134362 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term281 A s f b) = (term280 A s f b).
Proof. exact (TRANS (@lem7134361 A s f b) (@lem7134360 A s f b)). Qed.
Lemma lem7134363 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term35 A f s b) = (term35 A f s b).
Proof. exact (eq_refl (term35 A f s b)). Qed.
Lemma lem7134364 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7134365 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term282 A s f b) = (term283 A s f b).
Proof. exact (MK_COMB (@lem7134364) (@lem7134362 A s f b)). Qed.
Lemma lem7134366 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term284 A f s b) = (term285 A f s b).
Proof. exact (MK_COMB (@lem7134365 A s f b) (@lem7134363 A f s b)). Qed.
Lemma lem7134367 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term42 A f s b) = (term284 A f s b).
Proof. exact (@lem17265 (term40 A s f b) (term35 A f s b)). Qed.
Lemma lem7134368 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term42 A f s b) = (term285 A f s b).
Proof. exact (TRANS (@lem7134367 A f s b) (@lem7134366 A f s b)). Qed.
Lemma lem7134369 {A : Type'} (f : A -> real) (s : A -> Prop) : (term43 A f s) = (term286 A f s).
Proof. exact (fun_ext (fun b : real => @lem7134368 A f s b)). Qed.
Lemma lem7134370 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7134371 {A : Type'} (f : A -> real) (s : A -> Prop) : (term44 A f s) = (term287 A f s).
Proof. exact (MK_COMB (@lem7134370) (@lem7134369 A f s)). Qed.
Lemma lem7134372 {A : Type'} (s : A -> Prop) : (term45 A s) = (term288 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7134371 A f s)). Qed.
Lemma lem7134373 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7134374 {A : Type'} (s : A -> Prop) : (term46 A s) = (term289 A s).
Proof. exact (MK_COMB (@lem7134373 A) (@lem7134372 A s)). Qed.
Lemma lem7134375 {A : Type'} : (term47 A) = (term290 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7134374 A s)). Qed.
Lemma lem7134376 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7134377 {A : Type'} : (term11 A) = (term291 A).
Proof. exact (MK_COMB (@lem7134376 A) (@lem7134375 A)). Qed.
Lemma lem7134484 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term293 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7134485 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term293 A P Q).
Proof. exact (@lem7134484 A P Q). Qed.
Lemma lem7134486 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term294 A s f b) = (term295 A s f b).
Proof. exact (@lem7134485 A (term296 A s) (term276 A s f b)). Qed.
Lemma lem7134487 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term297 A s f b x) = (term267 A s f x b).
Proof. exact (eq_refl (term297 A s f b x)). Qed.
Lemma lem7134488 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term298 A s f b) = (term276 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7134487 A s f x b)). Qed.
Lemma lem7134489 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7134490 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term299 A s f b) = (term277 A s f b).
Proof. exact (MK_COMB (@lem7134489 A) (@lem7134488 A s f b)). Qed.
Lemma lem7134491 {A : Type'} (s : A -> Prop) : (term278 A s) = (term278 A s).
Proof. exact (eq_refl (term278 A s)). Qed.
Lemma lem7134492 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term294 A s f b) = (term280 A s f b).
Proof. exact (MK_COMB (@lem7134491 A s) (@lem7134490 A s f b)). Qed.
Lemma lem7134493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7134494 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term300 A s f b) = (term301 A s f b).
Proof. exact (MK_COMB (@lem7134493) (@lem7134492 A s f b)). Qed.
Lemma lem7134495 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term297 A s f b x) = (term267 A s f x b).
Proof. exact (eq_refl (term297 A s f b x)). Qed.
Lemma lem7134496 {A : Type'} (s : A -> Prop) : (term278 A s) = (term278 A s).
Proof. exact (eq_refl (term278 A s)). Qed.
Lemma lem7134497 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term302 A s f b x) = (term303 A s f x b).
Proof. exact (MK_COMB (@lem7134496 A s) (@lem7134495 A s f x b)). Qed.
Lemma lem7134498 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term304 A s f b) = (term305 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7134497 A s f x b)). Qed.
Lemma lem7134499 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7134500 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term295 A s f b) = (term306 A s f b).
Proof. exact (MK_COMB (@lem7134499 A) (@lem7134498 A s f b)). Qed.
Lemma lem7134501 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : ((term294 A s f b) = (term295 A s f b)) = ((term280 A s f b) = (term306 A s f b)).
Proof. exact (MK_COMB (@lem7134494 A s f b) (@lem7134500 A s f b)). Qed.
Lemma lem7134502 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term280 A s f b) = (term306 A s f b).
Proof. exact (EQ_MP (@lem7134501 A s f b) (@lem7134486 A s f b)). Qed.
Lemma lem7134503 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7134504 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term283 A s f b) = (term307 A s f b).
Proof. exact (MK_COMB (@lem7134503) (@lem7134502 A s f b)). Qed.
Lemma lem7134505 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term35 A f s b) = (term35 A f s b).
Proof. exact (eq_refl (term35 A f s b)). Qed.
Lemma lem7134506 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term285 A f s b) = (term308 A f s b).
Proof. exact (MK_COMB (@lem7134504 A s f b) (@lem7134505 A f s b)). Qed.
Lemma lem7134508 {A : Type'} (P : A -> Prop) (Q : Prop) : (term309 A P Q) = (term310 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7134509 {A : Type'} (P : A -> Prop) (Q : Prop) : (term309 A P Q) = (term310 A P Q).
Proof. exact (@lem7134508 A P Q). Qed.
Lemma lem7134510 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term311 A f s b) = (term312 A f s b).
Proof. exact (@lem7134509 A (term305 A s f b) (term35 A f s b)). Qed.
Lemma lem7134511 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term313 A s f b x) = (term303 A s f x b).
Proof. exact (eq_refl (term313 A s f b x)). Qed.
Lemma lem7134512 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term314 A s f b) = (term305 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7134511 A s f x b)). Qed.
Lemma lem7134513 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7134514 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term315 A s f b) = (term306 A s f b).
Proof. exact (MK_COMB (@lem7134513 A) (@lem7134512 A s f b)). Qed.
Lemma lem7134515 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7134516 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term316 A s f b) = (term307 A s f b).
Proof. exact (MK_COMB (@lem7134515) (@lem7134514 A s f b)). Qed.
Lemma lem7134517 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term35 A f s b) = (term35 A f s b).
Proof. exact (eq_refl (term35 A f s b)). Qed.
Lemma lem7134518 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term311 A f s b) = (term308 A f s b).
Proof. exact (MK_COMB (@lem7134516 A s f b) (@lem7134517 A f s b)). Qed.
Lemma lem7134519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7134520 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term317 A f s b) = (term318 A f s b).
Proof. exact (MK_COMB (@lem7134519) (@lem7134518 A f s b)). Qed.
Lemma lem7134521 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term313 A s f b x) = (term303 A s f x b).
Proof. exact (eq_refl (term313 A s f b x)). Qed.
Lemma lem7134522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7134523 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term319 A s f b x) = (term320 A s f x b).
Proof. exact (MK_COMB (@lem7134522) (@lem7134521 A s f x b)). Qed.
Lemma lem7134524 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term35 A f s b) = (term35 A f s b).
Proof. exact (eq_refl (term35 A f s b)). Qed.
Lemma lem7134525 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (b : real) : (term321 A x f s b) = (term322 A x f s b).
Proof. exact (MK_COMB (@lem7134523 A s f x b) (@lem7134524 A f s b)). Qed.
Lemma lem7134526 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term323 A f s b) = (term324 A f s b).
Proof. exact (fun_ext (fun x : A => @lem7134525 A x f s b)). Qed.
Lemma lem7134527 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7134528 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term312 A f s b) = (term325 A f s b).
Proof. exact (MK_COMB (@lem7134527 A) (@lem7134526 A f s b)). Qed.
Lemma lem7134529 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : ((term311 A f s b) = (term312 A f s b)) = ((term308 A f s b) = (term325 A f s b)).
Proof. exact (MK_COMB (@lem7134520 A f s b) (@lem7134528 A f s b)). Qed.
Lemma lem7134530 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term308 A f s b) = (term325 A f s b).
Proof. exact (EQ_MP (@lem7134529 A f s b) (@lem7134510 A f s b)). Qed.
Lemma lem7134531 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term285 A f s b) = (term325 A f s b).
Proof. exact (TRANS (@lem7134506 A f s b) (@lem7134530 A f s b)). Qed.
Lemma lem7134532 {A : Type'} (f : A -> real) (s : A -> Prop) : (term286 A f s) = (term326 A f s).
Proof. exact (fun_ext (fun b : real => @lem7134531 A f s b)). Qed.
Lemma lem7134533 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7134534 {A : Type'} (f : A -> real) (s : A -> Prop) : (term287 A f s) = (term327 A f s).
Proof. exact (MK_COMB (@lem7134533) (@lem7134532 A f s)). Qed.
Lemma lem7134536 {A B : Type'} (P : type1413 A B) : (term328 A B P) = (term329 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7134537 {A : Type'} (P : type1620 A) : (term330 A P) = (term331 A P).
Proof. exact (@lem7134536 real A P). Qed.
Lemma lem7134538 {A : Type'} (f : A -> real) (s : A -> Prop) : (term332 A f s) = (term333 A f s).
Proof. exact (@lem7134537 A (term334 A f s)). Qed.
Lemma lem7134539 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term335 A f s b) = (term324 A f s b).
Proof. exact (eq_refl (term335 A f s b)). Qed.
Lemma lem7134540 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7134541 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) (x : A) : (term336 A f s b x) = (term337 A f s b x).
Proof. exact (MK_COMB (@lem7134539 A f s b) (@lem7134540 A x)). Qed.
Lemma lem7134542 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (b : real) : (term337 A f s b x) = (term322 A x f s b).
Proof. exact (eq_refl (term337 A f s b x)). Qed.
Lemma lem7134543 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (b : real) : (term336 A f s b x) = (term322 A x f s b).
Proof. exact (TRANS (@lem7134541 A f s b x) (@lem7134542 A x f s b)). Qed.
Lemma lem7134544 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term338 A f s b) = (term324 A f s b).
Proof. exact (fun_ext (fun x : A => @lem7134543 A x f s b)). Qed.
Lemma lem7134545 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7134546 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term339 A f s b) = (term325 A f s b).
Proof. exact (MK_COMB (@lem7134545 A) (@lem7134544 A f s b)). Qed.
Lemma lem7134547 {A : Type'} (f : A -> real) (s : A -> Prop) : (term340 A f s) = (term326 A f s).
Proof. exact (fun_ext (fun b : real => @lem7134546 A f s b)). Qed.
Lemma lem7134548 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7134549 {A : Type'} (f : A -> real) (s : A -> Prop) : (term332 A f s) = (term327 A f s).
Proof. exact (MK_COMB (@lem7134548) (@lem7134547 A f s)). Qed.
Lemma lem7134550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7134551 {A : Type'} (f : A -> real) (s : A -> Prop) : (term341 A f s) = (term342 A f s).
Proof. exact (MK_COMB (@lem7134550) (@lem7134549 A f s)). Qed.
Lemma lem7134552 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term335 A f s b) = (term324 A f s b).
Proof. exact (eq_refl (term335 A f s b)). Qed.
Lemma lem7134553 {A : Type'} (x : real -> A) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem7134554 {A : Type'} (f : A -> real) (s : A -> Prop) (x : real -> A) (b : real) : (term343 A f s x b) = (term344 A f s x b).
Proof. exact (MK_COMB (@lem7134552 A f s b) (@lem7134553 A x b)). Qed.
Lemma lem7134555 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) (b : real) : (term344 A f s x b) = (term345 A x f s b).
Proof. exact (eq_refl (term344 A f s x b)). Qed.
Lemma lem7134556 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) (b : real) : (term343 A f s x b) = (term345 A x f s b).
Proof. exact (TRANS (@lem7134554 A f s x b) (@lem7134555 A x f s b)). Qed.
Lemma lem7134557 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) : (term346 A f s x) = (term347 A x f s).
Proof. exact (fun_ext (fun b : real => @lem7134556 A x f s b)). Qed.
Lemma lem7134558 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7134559 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) : (term348 A f s x) = (term349 A x f s).
Proof. exact (MK_COMB (@lem7134558) (@lem7134557 A x f s)). Qed.
Lemma lem7134560 {A : Type'} (f : A -> real) (s : A -> Prop) : (term350 A f s) = (term351 A f s).
Proof. exact (fun_ext (fun x : real -> A => @lem7134559 A x f s)). Qed.
Lemma lem7134561 {A : Type'} : (@ex (real -> A)) = (@ex (real -> A)).
Proof. exact (eq_refl (@ex (real -> A))). Qed.
Lemma lem7134562 {A : Type'} (f : A -> real) (s : A -> Prop) : (term333 A f s) = (term352 A f s).
Proof. exact (MK_COMB (@lem7134561 A) (@lem7134560 A f s)). Qed.
Lemma lem7134563 {A : Type'} (f : A -> real) (s : A -> Prop) : ((term332 A f s) = (term333 A f s)) = ((term327 A f s) = (term352 A f s)).
Proof. exact (MK_COMB (@lem7134551 A f s) (@lem7134562 A f s)). Qed.
Lemma lem7134564 {A : Type'} (f : A -> real) (s : A -> Prop) : (term327 A f s) = (term352 A f s).
Proof. exact (EQ_MP (@lem7134563 A f s) (@lem7134538 A f s)). Qed.
Lemma lem7134565 {A : Type'} (f : A -> real) (s : A -> Prop) : (term287 A f s) = (term352 A f s).
Proof. exact (TRANS (@lem7134534 A f s) (@lem7134564 A f s)). Qed.
Lemma lem7134566 {A : Type'} (s : A -> Prop) : (term288 A s) = (term353 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7134565 A f s)). Qed.
Lemma lem7134567 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7134568 {A : Type'} (s : A -> Prop) : (term289 A s) = (term354 A s).
Proof. exact (MK_COMB (@lem7134567 A) (@lem7134566 A s)). Qed.
Lemma lem7134570 {A B : Type'} (P : type1413 A B) : (term328 A B P) = (term329 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7134571 {A : Type'} (P : type713 A) : (term355 A P) = (term356 A P).
Proof. exact (@lem7134570 (A -> real) (real -> A) P). Qed.
Lemma lem7134572 {A : Type'} (s : A -> Prop) : (term357 A s) = (term358 A s).
Proof. exact (@lem7134571 A (term359 A s)). Qed.
Lemma lem7134573 {A : Type'} (f : A -> real) (s : A -> Prop) : (term360 A s f) = (term351 A f s).
Proof. exact (eq_refl (term360 A s f)). Qed.
Lemma lem7134574 {A : Type'} (x : real -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7134575 {A : Type'} (f : A -> real) (s : A -> Prop) (x : real -> A) : (term361 A s f x) = (term362 A f s x).
Proof. exact (MK_COMB (@lem7134573 A f s) (@lem7134574 A x)). Qed.
Lemma lem7134576 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) : (term362 A f s x) = (term349 A x f s).
Proof. exact (eq_refl (term362 A f s x)). Qed.
Lemma lem7134577 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) : (term361 A s f x) = (term349 A x f s).
Proof. exact (TRANS (@lem7134575 A f s x) (@lem7134576 A x f s)). Qed.
Lemma lem7134578 {A : Type'} (f : A -> real) (s : A -> Prop) : (term363 A s f) = (term351 A f s).
Proof. exact (fun_ext (fun x : real -> A => @lem7134577 A x f s)). Qed.
Lemma lem7134579 {A : Type'} : (@ex (real -> A)) = (@ex (real -> A)).
Proof. exact (eq_refl (@ex (real -> A))). Qed.
Lemma lem7134580 {A : Type'} (f : A -> real) (s : A -> Prop) : (term364 A s f) = (term352 A f s).
Proof. exact (MK_COMB (@lem7134579 A) (@lem7134578 A f s)). Qed.
Lemma lem7134581 {A : Type'} (s : A -> Prop) : (term365 A s) = (term353 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7134580 A f s)). Qed.
Lemma lem7134582 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7134583 {A : Type'} (s : A -> Prop) : (term357 A s) = (term354 A s).
Proof. exact (MK_COMB (@lem7134582 A) (@lem7134581 A s)). Qed.
Lemma lem7134584 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7134585 {A : Type'} (s : A -> Prop) : (term366 A s) = (term367 A s).
Proof. exact (MK_COMB (@lem7134584) (@lem7134583 A s)). Qed.
Lemma lem7134586 {A : Type'} (f : A -> real) (s : A -> Prop) : (term360 A s f) = (term351 A f s).
Proof. exact (eq_refl (term360 A s f)). Qed.
Lemma lem7134587 {A : Type'} (x : type715 A) (f : A -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7134588 {A : Type'} (s : A -> Prop) (x : type715 A) (f : A -> real) : (term368 A s x f) = (term369 A s x f).
Proof. exact (MK_COMB (@lem7134586 A f s) (@lem7134587 A x f)). Qed.
Lemma lem7134589 {A : Type'} (x : type715 A) (f : A -> real) (s : A -> Prop) : (term369 A s x f) = (term370 A x f s).
Proof. exact (eq_refl (term369 A s x f)). Qed.
Lemma lem7134590 {A : Type'} (x : type715 A) (f : A -> real) (s : A -> Prop) : (term368 A s x f) = (term370 A x f s).
Proof. exact (TRANS (@lem7134588 A s x f) (@lem7134589 A x f s)). Qed.
Lemma lem7134591 {A : Type'} (x : type715 A) (s : A -> Prop) : (term371 A s x) = (term372 A x s).
Proof. exact (fun_ext (fun f : A -> real => @lem7134590 A x f s)). Qed.
Lemma lem7134592 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7134593 {A : Type'} (x : type715 A) (s : A -> Prop) : (term373 A s x) = (term374 A x s).
Proof. exact (MK_COMB (@lem7134592 A) (@lem7134591 A x s)). Qed.
Lemma lem7134594 {A : Type'} (s : A -> Prop) : (term375 A s) = (term376 A s).
Proof. exact (fun_ext (fun x : type715 A => @lem7134593 A x s)). Qed.
Lemma lem7134595 {A : Type'} : (@ex ((A -> real) -> real -> A)) = (@ex ((A -> real) -> real -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> real -> A))). Qed.
Lemma lem7134596 {A : Type'} (s : A -> Prop) : (term358 A s) = (term377 A s).
Proof. exact (MK_COMB (@lem7134595 A) (@lem7134594 A s)). Qed.
Lemma lem7134597 {A : Type'} (s : A -> Prop) : ((term357 A s) = (term358 A s)) = ((term354 A s) = (term377 A s)).
Proof. exact (MK_COMB (@lem7134585 A s) (@lem7134596 A s)). Qed.
Lemma lem7134598 {A : Type'} (s : A -> Prop) : (term354 A s) = (term377 A s).
Proof. exact (EQ_MP (@lem7134597 A s) (@lem7134572 A s)). Qed.
Lemma lem7134599 {A : Type'} (s : A -> Prop) : (term289 A s) = (term377 A s).
Proof. exact (TRANS (@lem7134568 A s) (@lem7134598 A s)). Qed.
Lemma lem7134600 {A : Type'} : (term290 A) = (term378 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7134599 A s)). Qed.
Lemma lem7134601 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7134602 {A : Type'} : (term291 A) = (term379 A).
Proof. exact (MK_COMB (@lem7134601 A) (@lem7134600 A)). Qed.
Lemma lem7134604 {A B : Type'} (P : type1413 A B) : (term328 A B P) = (term329 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7134605 {A : Type'} (P : type603 A) : (term380 A P) = (term381 A P).
Proof. exact (@lem7134604 (A -> Prop) (type715 A) P). Qed.
Lemma lem7134606 {A : Type'} : (term382 A) = (term383 A).
Proof. exact (@lem7134605 A (term384 A)). Qed.
Lemma lem7134607 {A : Type'} (s : A -> Prop) : (term385 A s) = (term376 A s).
Proof. exact (eq_refl (term385 A s)). Qed.
Lemma lem7134608 {A : Type'} (x : type715 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7134609 {A : Type'} (s : A -> Prop) (x : type715 A) : (term386 A s x) = (term387 A s x).
Proof. exact (MK_COMB (@lem7134607 A s) (@lem7134608 A x)). Qed.
Lemma lem7134610 {A : Type'} (x : type715 A) (s : A -> Prop) : (term387 A s x) = (term374 A x s).
Proof. exact (eq_refl (term387 A s x)). Qed.
Lemma lem7134611 {A : Type'} (x : type715 A) (s : A -> Prop) : (term386 A s x) = (term374 A x s).
Proof. exact (TRANS (@lem7134609 A s x) (@lem7134610 A x s)). Qed.
Lemma lem7134612 {A : Type'} (s : A -> Prop) : (term388 A s) = (term376 A s).
Proof. exact (fun_ext (fun x : type715 A => @lem7134611 A x s)). Qed.
Lemma lem7134613 {A : Type'} : (@ex ((A -> real) -> real -> A)) = (@ex ((A -> real) -> real -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> real -> A))). Qed.
Lemma lem7134614 {A : Type'} (s : A -> Prop) : (term389 A s) = (term377 A s).
Proof. exact (MK_COMB (@lem7134613 A) (@lem7134612 A s)). Qed.
Lemma lem7134615 {A : Type'} : (term390 A) = (term378 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7134614 A s)). Qed.
Lemma lem7134616 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7134617 {A : Type'} : (term382 A) = (term379 A).
Proof. exact (MK_COMB (@lem7134616 A) (@lem7134615 A)). Qed.
Lemma lem7134618 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7134619 {A : Type'} : (term391 A) = (term392 A).
Proof. exact (MK_COMB (@lem7134618) (@lem7134617 A)). Qed.
Lemma lem7134620 {A : Type'} (s : A -> Prop) : (term385 A s) = (term376 A s).
Proof. exact (eq_refl (term385 A s)). Qed.
Lemma lem7134621 {A : Type'} (x : type645 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7134622 {A : Type'} (x : type645 A) (s : A -> Prop) : (term393 A x s) = (term394 A x s).
Proof. exact (MK_COMB (@lem7134620 A s) (@lem7134621 A x s)). Qed.
Lemma lem7134623 {A : Type'} (x : type645 A) (s : A -> Prop) : (term394 A x s) = (term395 A x s).
Proof. exact (eq_refl (term394 A x s)). Qed.
Lemma lem7134624 {A : Type'} (x : type645 A) (s : A -> Prop) : (term393 A x s) = (term395 A x s).
Proof. exact (TRANS (@lem7134622 A x s) (@lem7134623 A x s)). Qed.
Lemma lem7134625 {A : Type'} (x : type645 A) : (term396 A x) = (term397 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7134624 A x s)). Qed.
Lemma lem7134626 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7134627 {A : Type'} (x : type645 A) : (term398 A x) = (term399 A x).
Proof. exact (MK_COMB (@lem7134626 A) (@lem7134625 A x)). Qed.
Lemma lem7134628 {A : Type'} : (term400 A) = (term401 A).
Proof. exact (fun_ext (fun x : type645 A => @lem7134627 A x)). Qed.
Lemma lem7134629 {A : Type'} : (@ex ((A -> Prop) -> (A -> real) -> real -> A)) = (@ex ((A -> Prop) -> (A -> real) -> real -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> real) -> real -> A))). Qed.
Lemma lem7134630 {A : Type'} : (term383 A) = (term402 A).
Proof. exact (MK_COMB (@lem7134629 A) (@lem7134628 A)). Qed.
Lemma lem7134631 {A : Type'} : ((term382 A) = (term383 A)) = ((term379 A) = (term402 A)).
Proof. exact (MK_COMB (@lem7134619 A) (@lem7134630 A)). Qed.
Lemma lem7134632 {A : Type'} : (term379 A) = (term402 A).
Proof. exact (EQ_MP (@lem7134631 A) (@lem7134606 A)). Qed.
Lemma lem7134634 {A : Type'} : (term291 A) = (term402 A).
Proof. exact (TRANS (@lem7134602 A) (@lem7134632 A)). Qed.
Lemma lem7134635 {A : Type'} : (term11 A) = (term402 A).
Proof. exact (TRANS (@lem7134377 A) (@lem7134634 A)). Qed.
Lemma lem7134636 {A : Type'} (h1 : term11 A) : term402 A.
Proof. exact (EQ_MP (@lem7134635 A) (@lem7133078 A h1)). Qed.
Lemma lem7134637 {A : Type'} (x : type645 A) (h1 : term399 A x) : term399 A x.
Proof. exact (h1). Qed.
Lemma lem7134638 {A : Type'} (s : A -> Prop) (h1 : term107 A s) : term107 A s.
Proof. exact (h1). Qed.
Lemma lem7134639 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term98 A s f) : term98 A s f.
Proof. exact (h1). Qed.
Lemma lem7134640 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term88 A s f b.
Proof. exact (h1). Qed.
Lemma lem7134749 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7134754 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134755 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem7134754 (A -> Prop) nat f x). Qed.
Lemma lem7134757 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem7134755 A (@CARD A) s). Qed.
Lemma lem7134758 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7134759 {A : Type'} (s : A -> Prop) : (term403 A s) = (term404 A s).
Proof. exact (MK_COMB (@lem7134749) (@lem7134757 A s)). Qed.
Lemma lem7134760 {A : Type'} (s : A -> Prop) (n : nat) : ((@CARD A s) = n) = ((@I ((A -> Prop) -> nat) (@CARD A) s) = n).
Proof. exact (MK_COMB (@lem7134759 A s) (@lem7134758 n)). Qed.
Lemma lem7134765 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134766 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7134765 (A -> Prop) Prop f x). Qed.
Lemma lem7134768 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7134766 A (@FINITE A) s). Qed.
Lemma lem7134769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7134770 {A : Type'} (s : A -> Prop) : (term39 A s) = (term405 A s).
Proof. exact (MK_COMB (@lem7134769) (@lem7134768 A s)). Qed.
Lemma lem7134771 {A : Type'} (s : A -> Prop) (n : nat) : (term60 A s n) = (term406 A s n).
Proof. exact (MK_COMB (@lem7134770 A s) (@lem7134760 A s n)). Qed.
Lemma lem7134772 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7134779 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134780 {A : Type'} (f : type682 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat -> Prop) f x).
Proof. exact (@lem7134779 (A -> Prop) (nat -> Prop) f x). Qed.
Lemma lem7134781 {A : Type'} (s : A -> Prop) : (@HAS_SIZE A s) = (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s).
Proof. exact (@lem7134780 A (@HAS_SIZE A) s). Qed.
Lemma lem7134782 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7134783 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s n).
Proof. exact (MK_COMB (@lem7134781 A s) (@lem7134782 n)). Qed.
Lemma lem7134785 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134786 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7134785 nat Prop f x). Qed.
Lemma lem7134787 {A : Type'} (s : A -> Prop) (n : nat) : (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s n) = (term407 A s n).
Proof. exact (@lem7134786 (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s) n). Qed.
Lemma lem7134789 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term407 A s n).
Proof. exact (TRANS (@lem7134783 A s n) (@lem7134787 A s n)). Qed.
Lemma lem7134790 {A : Type'} (s : A -> Prop) (n : nat) : (term408 A s n) = (term409 A s n).
Proof. exact (MK_COMB (@lem7134772) (@lem7134789 A s n)). Qed.
Lemma lem7134791 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7134792 {A : Type'} (s : A -> Prop) (n : nat) : (term410 A s n) = (term411 A s n).
Proof. exact (MK_COMB (@lem7134791) (@lem7134790 A s n)). Qed.
Lemma lem7134793 {A : Type'} (s : A -> Prop) (n : nat) : (term118 A s n) = (term412 A s n).
Proof. exact (MK_COMB (@lem7134792 A s n) (@lem7134771 A s n)). Qed.
Lemma lem7134794 {A : Type'} (s : A -> Prop) : (term137 A s) = (term413 A s).
Proof. exact (fun_ext (fun n : nat => @lem7134793 A s n)). Qed.
Lemma lem7134795 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7134796 {A : Type'} (s : A -> Prop) : (term152 A s) = (term414 A s).
Proof. exact (MK_COMB (@lem7134795) (@lem7134794 A s)). Qed.
Lemma lem7134797 {A : Type'} : (term161 A) = (term415 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7134796 A s)). Qed.
Lemma lem7134798 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7134799 {A : Type'} : (term176 A) = (term416 A).
Proof. exact (MK_COMB (@lem7134798 A) (@lem7134797 A)). Qed.
Lemma lem7134800 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7134801 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7134806 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134807 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem7134806 (A -> Prop) nat f x). Qed.
Lemma lem7134809 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem7134807 A (@CARD A) s). Qed.
Lemma lem7134810 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7134811 {A : Type'} (s : A -> Prop) : (term403 A s) = (term404 A s).
Proof. exact (MK_COMB (@lem7134801) (@lem7134809 A s)). Qed.
Lemma lem7134812 {A : Type'} (s : A -> Prop) (n : nat) : ((@CARD A s) = n) = ((@I ((A -> Prop) -> nat) (@CARD A) s) = n).
Proof. exact (MK_COMB (@lem7134811 A s) (@lem7134810 n)). Qed.
Lemma lem7134813 {A : Type'} (s : A -> Prop) (n : nat) : (term417 A s n) = (term418 A s n).
Proof. exact (MK_COMB (@lem7134800) (@lem7134812 A s n)). Qed.
Lemma lem7134814 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7134819 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134820 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7134819 (A -> Prop) Prop f x). Qed.
Lemma lem7134822 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7134820 A (@FINITE A) s). Qed.
Lemma lem7134823 {A : Type'} (s : A -> Prop) : (term296 A s) = (term419 A s).
Proof. exact (MK_COMB (@lem7134814) (@lem7134822 A s)). Qed.
Lemma lem7134824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7134825 {A : Type'} (s : A -> Prop) : (term278 A s) = (term420 A s).
Proof. exact (MK_COMB (@lem7134824) (@lem7134823 A s)). Qed.
Lemma lem7134826 {A : Type'} (s : A -> Prop) (n : nat) : (term117 A s n) = (term421 A s n).
Proof. exact (MK_COMB (@lem7134825 A s) (@lem7134813 A s n)). Qed.
Lemma lem7134833 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134834 {A : Type'} (f : type682 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat -> Prop) f x).
Proof. exact (@lem7134833 (A -> Prop) (nat -> Prop) f x). Qed.
Lemma lem7134835 {A : Type'} (s : A -> Prop) : (@HAS_SIZE A s) = (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s).
Proof. exact (@lem7134834 A (@HAS_SIZE A) s). Qed.
Lemma lem7134836 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7134837 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s n).
Proof. exact (MK_COMB (@lem7134835 A s) (@lem7134836 n)). Qed.
Lemma lem7134839 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134840 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7134839 nat Prop f x). Qed.
Lemma lem7134841 {A : Type'} (s : A -> Prop) (n : nat) : (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s n) = (term407 A s n).
Proof. exact (@lem7134840 (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s) n). Qed.
Lemma lem7134843 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term407 A s n).
Proof. exact (TRANS (@lem7134837 A s n) (@lem7134841 A s n)). Qed.
Lemma lem7134844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7134845 {A : Type'} (s : A -> Prop) (n : nat) : (term119 A s n) = (term422 A s n).
Proof. exact (MK_COMB (@lem7134844) (@lem7134843 A s n)). Qed.
Lemma lem7134846 {A : Type'} (s : A -> Prop) (n : nat) : (term121 A s n) = (term423 A s n).
Proof. exact (MK_COMB (@lem7134845 A s n) (@lem7134826 A s n)). Qed.
Lemma lem7134847 {A : Type'} (s : A -> Prop) : (term136 A s) = (term424 A s).
Proof. exact (fun_ext (fun n : nat => @lem7134846 A s n)). Qed.
Lemma lem7134848 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7134849 {A : Type'} (s : A -> Prop) : (term147 A s) = (term425 A s).
Proof. exact (MK_COMB (@lem7134848) (@lem7134847 A s)). Qed.
Lemma lem7134850 {A : Type'} : (term160 A) = (term426 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7134849 A s)). Qed.
Lemma lem7134851 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7134852 {A : Type'} : (term171 A) = (term427 A).
Proof. exact (MK_COMB (@lem7134851 A) (@lem7134850 A)). Qed.
Lemma lem7134853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7134854 {A : Type'} : (term173 A) = (term428 A).
Proof. exact (MK_COMB (@lem7134853) (@lem7134852 A)). Qed.
Lemma lem7134855 {A : Type'} : (term177 A) = (term429 A).
Proof. exact (MK_COMB (@lem7134854 A) (@lem7134799 A)). Qed.
Lemma lem7134856 {A : Type'} (h1 : term12 A) : term429 A.
Proof. exact (EQ_MP (@lem7134855 A) (@lem7133835 A h1)). Qed.
Lemma lem7134861 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (s = (@EMPTY A)).
Proof. exact (eq_refl (s = (@EMPTY A))). Qed.
Lemma lem7134862 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7134869 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134870 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7134869 nat nat f x). Qed.
Lemma lem7134872 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7134870 NUMERAL 0). Qed.
Lemma lem7134873 {A : Type'} (s : A -> Prop) : (@HAS_SIZE A s) = (@HAS_SIZE A s).
Proof. exact (eq_refl (@HAS_SIZE A s)). Qed.
Lemma lem7134874 {A : Type'} (s : A -> Prop) : (term57 A s) = (term430 A s).
Proof. exact (MK_COMB (@lem7134873 A s) (@lem7134872)). Qed.
Lemma lem7134876 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134877 {A : Type'} (f : type682 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat -> Prop) f x).
Proof. exact (@lem7134876 (A -> Prop) (nat -> Prop) f x). Qed.
Lemma lem7134878 {A : Type'} (s : A -> Prop) : (@HAS_SIZE A s) = (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s).
Proof. exact (@lem7134877 A (@HAS_SIZE A) s). Qed.
Lemma lem7134879 : (@I (nat -> nat) NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (eq_refl (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7134880 {A : Type'} (s : A -> Prop) : (term430 A s) = (term431 A s).
Proof. exact (MK_COMB (@lem7134878 A s) (@lem7134879)). Qed.
Lemma lem7134882 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134883 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7134882 nat Prop f x). Qed.
Lemma lem7134884 {A : Type'} (s : A -> Prop) : (term431 A s) = (term432 A s).
Proof. exact (@lem7134883 (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s) (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7134885 {A : Type'} (s : A -> Prop) : (term430 A s) = (term432 A s).
Proof. exact (TRANS (@lem7134880 A s) (@lem7134884 A s)). Qed.
Lemma lem7134886 {A : Type'} (s : A -> Prop) : (term57 A s) = (term432 A s).
Proof. exact (TRANS (@lem7134874 A s) (@lem7134885 A s)). Qed.
Lemma lem7134887 {A : Type'} (s : A -> Prop) : (term433 A s) = (term434 A s).
Proof. exact (MK_COMB (@lem7134862) (@lem7134886 A s)). Qed.
Lemma lem7134888 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7134889 {A : Type'} (s : A -> Prop) : (term435 A s) = (term436 A s).
Proof. exact (MK_COMB (@lem7134888) (@lem7134887 A s)). Qed.
Lemma lem7134890 {A : Type'} (s : A -> Prop) : (term190 A s) = (term437 A s).
Proof. exact (MK_COMB (@lem7134889 A s) (@lem7134861 A s)). Qed.
Lemma lem7134891 {A : Type'} : (term184 A) = (term438 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7134890 A s)). Qed.
Lemma lem7134892 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7134893 {A : Type'} : (term202 A) = (term439 A).
Proof. exact (MK_COMB (@lem7134892 A) (@lem7134891 A)). Qed.
Lemma lem7134900 {A : Type'} (s : A -> Prop) : (term440 A s) = (term440 A s).
Proof. exact (eq_refl (term440 A s)). Qed.
Lemma lem7134907 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134908 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7134907 nat nat f x). Qed.
Lemma lem7134910 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7134908 NUMERAL 0). Qed.
Lemma lem7134911 {A : Type'} (s : A -> Prop) : (@HAS_SIZE A s) = (@HAS_SIZE A s).
Proof. exact (eq_refl (@HAS_SIZE A s)). Qed.
Lemma lem7134912 {A : Type'} (s : A -> Prop) : (term57 A s) = (term430 A s).
Proof. exact (MK_COMB (@lem7134911 A s) (@lem7134910)). Qed.
Lemma lem7134914 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134915 {A : Type'} (f : type682 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat -> Prop) f x).
Proof. exact (@lem7134914 (A -> Prop) (nat -> Prop) f x). Qed.
Lemma lem7134916 {A : Type'} (s : A -> Prop) : (@HAS_SIZE A s) = (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s).
Proof. exact (@lem7134915 A (@HAS_SIZE A) s). Qed.
Lemma lem7134917 : (@I (nat -> nat) NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (eq_refl (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7134918 {A : Type'} (s : A -> Prop) : (term430 A s) = (term431 A s).
Proof. exact (MK_COMB (@lem7134916 A s) (@lem7134917)). Qed.
Lemma lem7134920 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134921 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7134920 nat Prop f x). Qed.
Lemma lem7134922 {A : Type'} (s : A -> Prop) : (term431 A s) = (term432 A s).
Proof. exact (@lem7134921 (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s) (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7134923 {A : Type'} (s : A -> Prop) : (term430 A s) = (term432 A s).
Proof. exact (TRANS (@lem7134918 A s) (@lem7134922 A s)). Qed.
Lemma lem7134924 {A : Type'} (s : A -> Prop) : (term57 A s) = (term432 A s).
Proof. exact (TRANS (@lem7134912 A s) (@lem7134923 A s)). Qed.
Lemma lem7134925 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7134926 {A : Type'} (s : A -> Prop) : (term441 A s) = (term442 A s).
Proof. exact (MK_COMB (@lem7134925) (@lem7134924 A s)). Qed.
Lemma lem7134927 {A : Type'} (s : A -> Prop) : (term186 A s) = (term443 A s).
Proof. exact (MK_COMB (@lem7134926 A s) (@lem7134900 A s)). Qed.
Lemma lem7134928 {A : Type'} : (term183 A) = (term444 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7134927 A s)). Qed.
Lemma lem7134929 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7134930 {A : Type'} : (term197 A) = (term445 A).
Proof. exact (MK_COMB (@lem7134929 A) (@lem7134928 A)). Qed.
Lemma lem7134931 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7134932 {A : Type'} : (term199 A) = (term446 A).
Proof. exact (MK_COMB (@lem7134931) (@lem7134930 A)). Qed.
Lemma lem7134933 {A : Type'} : (term203 A) = (term447 A).
Proof. exact (MK_COMB (@lem7134932 A) (@lem7134893 A)). Qed.
Lemma lem7134934 {A : Type'} (h1 : term59 A) : term447 A.
Proof. exact (EQ_MP (@lem7134933 A) (@lem7133980 A h1)). Qed.
Lemma lem7134939 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem7134940 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7134941 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7134946 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134947 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7134946 nat real f x). Qed.
Lemma lem7134949 (m : nat) : (real_of_num m) = (@I (nat -> real) real_of_num m).
Proof. exact (@lem7134947 real_of_num m). Qed.
Lemma lem7134954 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134955 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7134954 nat real f x). Qed.
Lemma lem7134957 (n : nat) : (real_of_num n) = (@I (nat -> real) real_of_num n).
Proof. exact (@lem7134955 real_of_num n). Qed.
Lemma lem7134958 (m : nat) : (term448 m) = (term449 m).
Proof. exact (MK_COMB (@lem7134941) (@lem7134949 m)). Qed.
Lemma lem7134959 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = ((@I (nat -> real) real_of_num m) = (@I (nat -> real) real_of_num n)).
Proof. exact (MK_COMB (@lem7134958 m) (@lem7134957 n)). Qed.
Lemma lem7134960 (m : nat) (n : nat) : (term450 m n) = (term451 m n).
Proof. exact (MK_COMB (@lem7134940) (@lem7134959 m n)). Qed.
Lemma lem7134961 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7134962 (m : nat) (n : nat) : (term452 m n) = (term453 m n).
Proof. exact (MK_COMB (@lem7134961) (@lem7134960 m n)). Qed.
Lemma lem7134963 (m : nat) (n : nat) : (term218 m n) = (term454 m n).
Proof. exact (MK_COMB (@lem7134962 m n) (@lem7134939 m n)). Qed.
Lemma lem7134964 (m : nat) : (term212 m) = (term455 m).
Proof. exact (fun_ext (fun n : nat => @lem7134963 m n)). Qed.
Lemma lem7134965 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7134966 (m : nat) : (term230 m) = (term456 m).
Proof. exact (MK_COMB (@lem7134965) (@lem7134964 m)). Qed.
Lemma lem7134967 : term237 = term457.
Proof. exact (fun_ext (fun m : nat => @lem7134966 m)). Qed.
Lemma lem7134968 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7134969 : term252 = term458.
Proof. exact (MK_COMB (@lem7134968) (@lem7134967)). Qed.
Lemma lem7134976 (m : nat) (n : nat) : (term459 m n) = (term459 m n).
Proof. exact (eq_refl (term459 m n)). Qed.
Lemma lem7134977 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7134982 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134983 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7134982 nat real f x). Qed.
Lemma lem7134985 (m : nat) : (real_of_num m) = (@I (nat -> real) real_of_num m).
Proof. exact (@lem7134983 real_of_num m). Qed.
Lemma lem7134990 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7134991 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7134990 nat real f x). Qed.
Lemma lem7134993 (n : nat) : (real_of_num n) = (@I (nat -> real) real_of_num n).
Proof. exact (@lem7134991 real_of_num n). Qed.
Lemma lem7134994 (m : nat) : (term448 m) = (term449 m).
Proof. exact (MK_COMB (@lem7134977) (@lem7134985 m)). Qed.
Lemma lem7134995 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = ((@I (nat -> real) real_of_num m) = (@I (nat -> real) real_of_num n)).
Proof. exact (MK_COMB (@lem7134994 m) (@lem7134993 n)). Qed.
Lemma lem7134996 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7134997 (m : nat) (n : nat) : (term460 m n) = (term461 m n).
Proof. exact (MK_COMB (@lem7134996) (@lem7134995 m n)). Qed.
Lemma lem7134998 (m : nat) (n : nat) : (term214 m n) = (term462 m n).
Proof. exact (MK_COMB (@lem7134997 m n) (@lem7134976 m n)). Qed.
Lemma lem7134999 (m : nat) : (term211 m) = (term463 m).
Proof. exact (fun_ext (fun n : nat => @lem7134998 m n)). Qed.
Lemma lem7135000 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7135001 (m : nat) : (term225 m) = (term464 m).
Proof. exact (MK_COMB (@lem7135000) (@lem7134999 m)). Qed.
Lemma lem7135002 : term236 = term465.
Proof. exact (fun_ext (fun m : nat => @lem7135001 m)). Qed.
Lemma lem7135003 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7135004 : term247 = term466.
Proof. exact (MK_COMB (@lem7135003) (@lem7135002)). Qed.
Lemma lem7135005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7135006 : term249 = term467.
Proof. exact (MK_COMB (@lem7135005) (@lem7135004)). Qed.
Lemma lem7135007 : term253 = term468.
Proof. exact (MK_COMB (@lem7135006) (@lem7134969)). Qed.
Lemma lem7135008 (h1 : term56) : term468.
Proof. exact (EQ_MP (@lem7135007) (@lem7134267 h1)). Qed.
Lemma lem7135009 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7135018 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135019 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7135018 real (real -> real) f x). Qed.
Lemma lem7135020 (x : real) : (real_div x) = (@I (real -> real -> real) real_div x).
Proof. exact (@lem7135019 real_div x). Qed.
Lemma lem7135021 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7135022 (x : real) (y : real) : (real_div x y) = (@I (real -> real -> real) real_div x y).
Proof. exact (MK_COMB (@lem7135020 x) (@lem7135021 y)). Qed.
Lemma lem7135024 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135025 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7135024 real real f x). Qed.
Lemma lem7135026 (x : real) (y : real) : (@I (real -> real -> real) real_div x y) = (term469 x y).
Proof. exact (@lem7135025 (@I (real -> real -> real) real_div x) y). Qed.
Lemma lem7135028 (x : real) (y : real) : (real_div x y) = (term469 x y).
Proof. exact (TRANS (@lem7135022 x y) (@lem7135026 x y)). Qed.
Lemma lem7135029 (y : real) : (real_mul y) = (real_mul y).
Proof. exact (eq_refl (real_mul y)). Qed.
Lemma lem7135030 (x : real) (y : real) : (term256 x y) = (term470 x y).
Proof. exact (MK_COMB (@lem7135029 y) (@lem7135028 x y)). Qed.
Lemma lem7135032 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135033 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7135032 real (real -> real) f x). Qed.
Lemma lem7135034 (y : real) : (real_mul y) = (@I (real -> real -> real) real_mul y).
Proof. exact (@lem7135033 real_mul y). Qed.
Lemma lem7135035 (x : real) (y : real) : (term469 x y) = (term469 x y).
Proof. exact (eq_refl (term469 x y)). Qed.
Lemma lem7135036 (x : real) (y : real) : (term470 x y) = (term471 x y).
Proof. exact (MK_COMB (@lem7135034 y) (@lem7135035 x y)). Qed.
Lemma lem7135038 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135039 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7135038 real real f x). Qed.
Lemma lem7135040 (x : real) (y : real) : (term471 x y) = (term472 x y).
Proof. exact (@lem7135039 (@I (real -> real -> real) real_mul y) (term469 x y)). Qed.
Lemma lem7135041 (x : real) (y : real) : (term470 x y) = (term472 x y).
Proof. exact (TRANS (@lem7135036 x y) (@lem7135040 x y)). Qed.
Lemma lem7135042 (x : real) (y : real) : (term256 x y) = (term472 x y).
Proof. exact (TRANS (@lem7135030 x y) (@lem7135041 x y)). Qed.
Lemma lem7135043 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7135044 (x : real) (y : real) : (term473 x y) = (term474 x y).
Proof. exact (MK_COMB (@lem7135009) (@lem7135042 x y)). Qed.
Lemma lem7135045 (y : real) (x : real) : ((term256 x y) = x) = ((term472 x y) = x).
Proof. exact (MK_COMB (@lem7135044 x y) (@lem7135043 x)). Qed.
Lemma lem7135048 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7135053 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135054 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7135053 nat nat f x). Qed.
Lemma lem7135056 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7135054 NUMERAL 0). Qed.
Lemma lem7135057 : term255 = term475.
Proof. exact (MK_COMB (@lem7135048) (@lem7135056)). Qed.
Lemma lem7135059 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135060 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7135059 nat real f x). Qed.
Lemma lem7135061 : term475 = term476.
Proof. exact (@lem7135060 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7135062 : term255 = term476.
Proof. exact (TRANS (@lem7135057) (@lem7135061)). Qed.
Lemma lem7135063 (y : real) : (@eq real y) = (@eq real y).
Proof. exact (eq_refl (@eq real y)). Qed.
Lemma lem7135064 (y : real) : (y = term255) = (y = term476).
Proof. exact (MK_COMB (@lem7135063 y) (@lem7135062)). Qed.
Lemma lem7135065 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7135066 (y : real) : (term258 y) = (term477 y).
Proof. exact (MK_COMB (@lem7135065) (@lem7135064 y)). Qed.
Lemma lem7135067 (y : real) (x : real) : (term260 y x) = (term478 y x).
Proof. exact (MK_COMB (@lem7135066 y) (@lem7135045 y x)). Qed.
Lemma lem7135068 (x : real) : (term262 x) = (term479 x).
Proof. exact (fun_ext (fun y : real => @lem7135067 y x)). Qed.
Lemma lem7135069 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7135070 (x : real) : (term263 x) = (term480 x).
Proof. exact (MK_COMB (@lem7135069) (@lem7135068 x)). Qed.
Lemma lem7135071 : term264 = term481.
Proof. exact (fun_ext (fun x : real => @lem7135070 x)). Qed.
Lemma lem7135072 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7135073 : term265 = term482.
Proof. exact (MK_COMB (@lem7135072) (@lem7135071)). Qed.
Lemma lem7135074 (h1 : term52) : term482.
Proof. exact (EQ_MP (@lem7135073) (@lem7134339 h1)). Qed.
Lemma lem7135075 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7135082 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135083 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7135082 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7135084 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7135083 A (@sum A) s). Qed.
Lemma lem7135085 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7135086 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f).
Proof. exact (MK_COMB (@lem7135084 A s) (@lem7135085 A f)). Qed.
Lemma lem7135088 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135089 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7135088 (A -> real) real f x). Qed.
Lemma lem7135090 {A : Type'} (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f) = (term483 A s f).
Proof. exact (@lem7135089 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) f). Qed.
Lemma lem7135092 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (term483 A s f).
Proof. exact (TRANS (@lem7135086 A s f) (@lem7135090 A s f)). Qed.
Lemma lem7135093 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7135094 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7135099 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135100 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem7135099 (A -> Prop) nat f x). Qed.
Lemma lem7135102 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem7135100 A (@CARD A) s). Qed.
Lemma lem7135103 {A : Type'} (s : A -> Prop) : (term484 A s) = (term485 A s).
Proof. exact (MK_COMB (@lem7135094) (@lem7135102 A s)). Qed.
Lemma lem7135105 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135106 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7135105 nat real f x). Qed.
Lemma lem7135107 {A : Type'} (s : A -> Prop) : (term485 A s) = (term486 A s).
Proof. exact (@lem7135106 real_of_num (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem7135108 {A : Type'} (s : A -> Prop) : (term484 A s) = (term486 A s).
Proof. exact (TRANS (@lem7135103 A s) (@lem7135107 A s)). Qed.
Lemma lem7135109 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7135110 {A : Type'} (s : A -> Prop) : (term487 A s) = (term488 A s).
Proof. exact (MK_COMB (@lem7135093) (@lem7135108 A s)). Qed.
Lemma lem7135111 {A : Type'} (s : A -> Prop) (b : real) : (term489 A s b) = (term490 A s b).
Proof. exact (MK_COMB (@lem7135110 A s) (@lem7135109 b)). Qed.
Lemma lem7135113 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135114 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7135113 real (real -> real) f x). Qed.
Lemma lem7135115 {A : Type'} (s : A -> Prop) : (term488 A s) = (term491 A s).
Proof. exact (@lem7135114 real_mul (term486 A s)). Qed.
Lemma lem7135116 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7135117 {A : Type'} (s : A -> Prop) (b : real) : (term490 A s b) = (term492 A s b).
Proof. exact (MK_COMB (@lem7135115 A s) (@lem7135116 b)). Qed.
Lemma lem7135119 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135120 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7135119 real real f x). Qed.
Lemma lem7135121 {A : Type'} (s : A -> Prop) (b : real) : (term492 A s b) = (term493 A s b).
Proof. exact (@lem7135120 (term491 A s) b). Qed.
Lemma lem7135122 {A : Type'} (s : A -> Prop) (b : real) : (term490 A s b) = (term493 A s b).
Proof. exact (TRANS (@lem7135117 A s b) (@lem7135121 A s b)). Qed.
Lemma lem7135123 {A : Type'} (s : A -> Prop) (b : real) : (term489 A s b) = (term493 A s b).
Proof. exact (TRANS (@lem7135111 A s b) (@lem7135122 A s b)). Qed.
Lemma lem7135124 {A : Type'} (s : A -> Prop) (f : A -> real) : (term494 A s f) = (term495 A s f).
Proof. exact (MK_COMB (@lem7135075) (@lem7135092 A s f)). Qed.
Lemma lem7135125 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term35 A f s b) = (term496 A f s b).
Proof. exact (MK_COMB (@lem7135124 A s f) (@lem7135123 A s b)). Qed.
Lemma lem7135127 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135128 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7135127 real (real -> Prop) f x). Qed.
Lemma lem7135129 {A : Type'} (s : A -> Prop) (f : A -> real) : (term495 A s f) = (term497 A s f).
Proof. exact (@lem7135128 real_le (term483 A s f)). Qed.
Lemma lem7135130 {A : Type'} (s : A -> Prop) (b : real) : (term493 A s b) = (term493 A s b).
Proof. exact (eq_refl (term493 A s b)). Qed.
Lemma lem7135131 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term496 A f s b) = (term498 A f s b).
Proof. exact (MK_COMB (@lem7135129 A s f) (@lem7135130 A s b)). Qed.
Lemma lem7135133 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135134 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7135133 real Prop f x). Qed.
Lemma lem7135135 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term498 A f s b) = (term499 A f s b).
Proof. exact (@lem7135134 (term497 A s f) (term493 A s b)). Qed.
Lemma lem7135136 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term496 A f s b) = (term499 A f s b).
Proof. exact (TRANS (@lem7135131 A f s b) (@lem7135135 A f s b)). Qed.
Lemma lem7135137 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term35 A f s b) = (term499 A f s b).
Proof. exact (TRANS (@lem7135125 A f s b) (@lem7135136 A f s b)). Qed.
Lemma lem7135138 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7135139 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7135140 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7135149 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135150 {A : Type'} (f : type645 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real -> A) f x).
Proof. exact (@lem7135149 (A -> Prop) (type715 A) f x). Qed.
Lemma lem7135151 {A : Type'} (x : type645 A) (s : A -> Prop) : (x s) = (@I ((A -> Prop) -> (A -> real) -> real -> A) x s).
Proof. exact (@lem7135150 A x s). Qed.
Lemma lem7135152 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7135153 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) : (x s f) = (@I ((A -> Prop) -> (A -> real) -> real -> A) x s f).
Proof. exact (MK_COMB (@lem7135151 A x s) (@lem7135152 A f)). Qed.
Lemma lem7135155 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135156 {A : Type'} (f : type715 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real -> A) f x).
Proof. exact (@lem7135155 (A -> real) (real -> A) f x). Qed.
Lemma lem7135157 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real -> A) x s f) = (term500 A x s f).
Proof. exact (@lem7135156 A (@I ((A -> Prop) -> (A -> real) -> real -> A) x s) f). Qed.
Lemma lem7135158 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) : (x s f) = (term500 A x s f).
Proof. exact (TRANS (@lem7135153 A x s f) (@lem7135157 A x s f)). Qed.
Lemma lem7135159 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7135160 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (x s f b) = (term501 A x s f b).
Proof. exact (MK_COMB (@lem7135158 A x s f) (@lem7135159 b)). Qed.
Lemma lem7135162 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135163 {A : Type'} (f : real -> A) (x : real) : (f x) = (@I (real -> A) f x).
Proof. exact (@lem7135162 real A f x). Qed.
Lemma lem7135164 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term501 A x s f b) = (term502 A x s f b).
Proof. exact (@lem7135163 A (term500 A x s f) b). Qed.
Lemma lem7135166 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (x s f b) = (term502 A x s f b).
Proof. exact (TRANS (@lem7135160 A x s f b) (@lem7135164 A x s f b)). Qed.
Lemma lem7135167 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term503 A x s f b) = (term504 A x s f b).
Proof. exact (MK_COMB (@lem7135140 A f) (@lem7135166 A x s f b)). Qed.
Lemma lem7135169 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135170 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7135169 A real f x). Qed.
Lemma lem7135171 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term504 A x s f b) = (term505 A x s f b).
Proof. exact (@lem7135170 A f (term502 A x s f b)). Qed.
Lemma lem7135172 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term503 A x s f b) = (term505 A x s f b).
Proof. exact (TRANS (@lem7135167 A x s f b) (@lem7135171 A x s f b)). Qed.
Lemma lem7135173 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7135174 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term506 A x s f b) = (term507 A x s f b).
Proof. exact (MK_COMB (@lem7135139) (@lem7135172 A x s f b)). Qed.
Lemma lem7135175 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term508 A x s f b) = (term509 A x s f b).
Proof. exact (MK_COMB (@lem7135174 A x s f b) (@lem7135173 b)). Qed.
Lemma lem7135177 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135178 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7135177 real (real -> Prop) f x). Qed.
Lemma lem7135179 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term507 A x s f b) = (term510 A x s f b).
Proof. exact (@lem7135178 real_le (term505 A x s f b)). Qed.
Lemma lem7135180 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7135181 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term509 A x s f b) = (term511 A x s f b).
Proof. exact (MK_COMB (@lem7135179 A x s f b) (@lem7135180 b)). Qed.
Lemma lem7135183 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135184 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7135183 real Prop f x). Qed.
Lemma lem7135185 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term511 A x s f b) = (term512 A x s f b).
Proof. exact (@lem7135184 (term510 A x s f b) b). Qed.
Lemma lem7135186 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term509 A x s f b) = (term512 A x s f b).
Proof. exact (TRANS (@lem7135181 A x s f b) (@lem7135185 A x s f b)). Qed.
Lemma lem7135187 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term508 A x s f b) = (term512 A x s f b).
Proof. exact (TRANS (@lem7135175 A x s f b) (@lem7135186 A x s f b)). Qed.
Lemma lem7135188 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term513 A x s f b) = (term514 A x s f b).
Proof. exact (MK_COMB (@lem7135138) (@lem7135187 A x s f b)). Qed.
Lemma lem7135189 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem7135198 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135199 {A : Type'} (f : type645 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real -> A) f x).
Proof. exact (@lem7135198 (A -> Prop) (type715 A) f x). Qed.
Lemma lem7135200 {A : Type'} (x : type645 A) (s : A -> Prop) : (x s) = (@I ((A -> Prop) -> (A -> real) -> real -> A) x s).
Proof. exact (@lem7135199 A x s). Qed.
Lemma lem7135201 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7135202 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) : (x s f) = (@I ((A -> Prop) -> (A -> real) -> real -> A) x s f).
Proof. exact (MK_COMB (@lem7135200 A x s) (@lem7135201 A f)). Qed.
Lemma lem7135204 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135205 {A : Type'} (f : type715 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real -> A) f x).
Proof. exact (@lem7135204 (A -> real) (real -> A) f x). Qed.
Lemma lem7135206 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real -> A) x s f) = (term500 A x s f).
Proof. exact (@lem7135205 A (@I ((A -> Prop) -> (A -> real) -> real -> A) x s) f). Qed.
Lemma lem7135207 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) : (x s f) = (term500 A x s f).
Proof. exact (TRANS (@lem7135202 A x s f) (@lem7135206 A x s f)). Qed.
Lemma lem7135208 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7135209 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (x s f b) = (term501 A x s f b).
Proof. exact (MK_COMB (@lem7135207 A x s f) (@lem7135208 b)). Qed.
Lemma lem7135211 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135212 {A : Type'} (f : real -> A) (x : real) : (f x) = (@I (real -> A) f x).
Proof. exact (@lem7135211 real A f x). Qed.
Lemma lem7135213 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term501 A x s f b) = (term502 A x s f b).
Proof. exact (@lem7135212 A (term500 A x s f) b). Qed.
Lemma lem7135215 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (x s f b) = (term502 A x s f b).
Proof. exact (TRANS (@lem7135209 A x s f b) (@lem7135213 A x s f b)). Qed.
Lemma lem7135216 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7135217 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term515 A x s f b) = (term516 A x s f b).
Proof. exact (MK_COMB (@lem7135189 A) (@lem7135215 A x s f b)). Qed.
Lemma lem7135218 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term517 A x f b s) = (term518 A x f b s).
Proof. exact (MK_COMB (@lem7135217 A x s f b) (@lem7135216 A s)). Qed.
Lemma lem7135220 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135221 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7135220 A (type686 A) f x). Qed.
Lemma lem7135222 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term516 A x s f b) = (term519 A x s f b).
Proof. exact (@lem7135221 A (@IN A) (term502 A x s f b)). Qed.
Lemma lem7135223 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7135224 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term518 A x f b s) = (term520 A x f b s).
Proof. exact (MK_COMB (@lem7135222 A x s f b) (@lem7135223 A s)). Qed.
Lemma lem7135226 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135227 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7135226 (A -> Prop) Prop f x). Qed.
Lemma lem7135228 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term520 A x f b s) = (term521 A x f b s).
Proof. exact (@lem7135227 A (term519 A x s f b) s). Qed.
Lemma lem7135229 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term518 A x f b s) = (term521 A x f b s).
Proof. exact (TRANS (@lem7135224 A x f b s) (@lem7135228 A x f b s)). Qed.
Lemma lem7135230 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term517 A x f b s) = (term521 A x f b s).
Proof. exact (TRANS (@lem7135218 A x f b s) (@lem7135229 A x f b s)). Qed.
Lemma lem7135231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7135232 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term522 A x f b s) = (term523 A x f b s).
Proof. exact (MK_COMB (@lem7135231) (@lem7135230 A x f b s)). Qed.
Lemma lem7135233 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term524 A x s f b) = (term525 A x s f b).
Proof. exact (MK_COMB (@lem7135232 A x f b s) (@lem7135188 A x s f b)). Qed.
Lemma lem7135234 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7135239 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135240 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7135239 (A -> Prop) Prop f x). Qed.
Lemma lem7135242 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7135240 A (@FINITE A) s). Qed.
Lemma lem7135243 {A : Type'} (s : A -> Prop) : (term296 A s) = (term419 A s).
Proof. exact (MK_COMB (@lem7135234) (@lem7135242 A s)). Qed.
Lemma lem7135244 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7135245 {A : Type'} (s : A -> Prop) : (term278 A s) = (term420 A s).
Proof. exact (MK_COMB (@lem7135244) (@lem7135243 A s)). Qed.
Lemma lem7135246 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term526 A x s f b) = (term527 A x s f b).
Proof. exact (MK_COMB (@lem7135245 A s) (@lem7135233 A x s f b)). Qed.
Lemma lem7135247 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7135248 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term528 A x s f b) = (term529 A x s f b).
Proof. exact (MK_COMB (@lem7135247) (@lem7135246 A x s f b)). Qed.
Lemma lem7135249 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) (b : real) : (term530 A x f s b) = (term531 A x f s b).
Proof. exact (MK_COMB (@lem7135248 A x s f b) (@lem7135137 A f s b)). Qed.
Lemma lem7135250 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) : (term532 A x f s) = (term533 A x f s).
Proof. exact (fun_ext (fun b : real => @lem7135249 A x f s b)). Qed.
Lemma lem7135251 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7135252 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) : (term534 A x f s) = (term535 A x f s).
Proof. exact (MK_COMB (@lem7135251) (@lem7135250 A x f s)). Qed.
Lemma lem7135253 {A : Type'} (x : type645 A) (s : A -> Prop) : (term536 A x s) = (term537 A x s).
Proof. exact (fun_ext (fun f : A -> real => @lem7135252 A x f s)). Qed.
Lemma lem7135254 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7135255 {A : Type'} (x : type645 A) (s : A -> Prop) : (term395 A x s) = (term538 A x s).
Proof. exact (MK_COMB (@lem7135254 A) (@lem7135253 A x s)). Qed.
Lemma lem7135256 {A : Type'} (x : type645 A) : (term397 A x) = (term539 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7135255 A x s)). Qed.
Lemma lem7135257 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7135258 {A : Type'} (x : type645 A) : (term399 A x) = (term540 A x).
Proof. exact (MK_COMB (@lem7135257 A) (@lem7135256 A x)). Qed.
Lemma lem7135259 {A : Type'} (x : type645 A) (h1 : term399 A x) : term540 A x.
Proof. exact (EQ_MP (@lem7135258 A x) (@lem7134637 A x h1)). Qed.
Lemma lem7135260 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7135261 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7135268 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135269 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7135268 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7135270 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7135269 A (@sum A) s). Qed.
Lemma lem7135271 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7135272 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f).
Proof. exact (MK_COMB (@lem7135270 A s) (@lem7135271 A f)). Qed.
Lemma lem7135274 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135275 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7135274 (A -> real) real f x). Qed.
Lemma lem7135276 {A : Type'} (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f) = (term483 A s f).
Proof. exact (@lem7135275 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) f). Qed.
Lemma lem7135278 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (term483 A s f).
Proof. exact (TRANS (@lem7135272 A s f) (@lem7135276 A s f)). Qed.
Lemma lem7135279 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7135280 {A : Type'} (s : A -> Prop) (f : A -> real) : (term494 A s f) = (term495 A s f).
Proof. exact (MK_COMB (@lem7135261) (@lem7135278 A s f)). Qed.
Lemma lem7135281 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term64 A s f b) = (term541 A s f b).
Proof. exact (MK_COMB (@lem7135280 A s f) (@lem7135279 b)). Qed.
Lemma lem7135283 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135284 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7135283 real (real -> Prop) f x). Qed.
Lemma lem7135285 {A : Type'} (s : A -> Prop) (f : A -> real) : (term495 A s f) = (term497 A s f).
Proof. exact (@lem7135284 real_le (term483 A s f)). Qed.
Lemma lem7135286 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7135287 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term541 A s f b) = (term542 A s f b).
Proof. exact (MK_COMB (@lem7135285 A s f) (@lem7135286 b)). Qed.
Lemma lem7135289 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135290 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7135289 real Prop f x). Qed.
Lemma lem7135291 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term542 A s f b) = (term543 A s f b).
Proof. exact (@lem7135290 (term497 A s f) b). Qed.
Lemma lem7135292 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term541 A s f b) = (term543 A s f b).
Proof. exact (TRANS (@lem7135287 A s f b) (@lem7135291 A s f b)). Qed.
Lemma lem7135293 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term64 A s f b) = (term543 A s f b).
Proof. exact (TRANS (@lem7135281 A s f b) (@lem7135292 A s f b)). Qed.
Lemma lem7135294 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term84 A s f b) = (term544 A s f b).
Proof. exact (MK_COMB (@lem7135260) (@lem7135293 A s f b)). Qed.
Lemma lem7135295 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7135300 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135302 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7135300 A real f x). Qed.
Lemma lem7135305 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7135310 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135311 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem7135310 (A -> Prop) nat f x). Qed.
Lemma lem7135313 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem7135311 A (@CARD A) s). Qed.
Lemma lem7135314 {A : Type'} (s : A -> Prop) : (term484 A s) = (term485 A s).
Proof. exact (MK_COMB (@lem7135305) (@lem7135313 A s)). Qed.
Lemma lem7135316 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135317 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7135316 nat real f x). Qed.
Lemma lem7135318 {A : Type'} (s : A -> Prop) : (term485 A s) = (term486 A s).
Proof. exact (@lem7135317 real_of_num (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem7135319 {A : Type'} (s : A -> Prop) : (term484 A s) = (term486 A s).
Proof. exact (TRANS (@lem7135314 A s) (@lem7135318 A s)). Qed.
Lemma lem7135320 (b : real) : (real_div b) = (real_div b).
Proof. exact (eq_refl (real_div b)). Qed.
Lemma lem7135321 {A : Type'} (b : real) (s : A -> Prop) : (term545 A b s) = (term546 A b s).
Proof. exact (MK_COMB (@lem7135320 b) (@lem7135319 A s)). Qed.
Lemma lem7135323 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135324 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7135323 real (real -> real) f x). Qed.
Lemma lem7135325 (b : real) : (real_div b) = (@I (real -> real -> real) real_div b).
Proof. exact (@lem7135324 real_div b). Qed.
Lemma lem7135326 {A : Type'} (s : A -> Prop) : (term486 A s) = (term486 A s).
Proof. exact (eq_refl (term486 A s)). Qed.
Lemma lem7135327 {A : Type'} (b : real) (s : A -> Prop) : (term546 A b s) = (term547 A b s).
Proof. exact (MK_COMB (@lem7135325 b) (@lem7135326 A s)). Qed.
Lemma lem7135329 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135330 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7135329 real real f x). Qed.
Lemma lem7135331 {A : Type'} (b : real) (s : A -> Prop) : (term547 A b s) = (term548 A b s).
Proof. exact (@lem7135330 (@I (real -> real -> real) real_div b) (term486 A s)). Qed.
Lemma lem7135332 {A : Type'} (b : real) (s : A -> Prop) : (term546 A b s) = (term548 A b s).
Proof. exact (TRANS (@lem7135327 A b s) (@lem7135331 A b s)). Qed.
Lemma lem7135333 {A : Type'} (b : real) (s : A -> Prop) : (term545 A b s) = (term548 A b s).
Proof. exact (TRANS (@lem7135321 A b s) (@lem7135332 A b s)). Qed.
Lemma lem7135334 {A : Type'} (f : A -> real) (x : A) : (term549 A f x) = (term550 A f x).
Proof. exact (MK_COMB (@lem7135295) (@lem7135302 A f x)). Qed.
Lemma lem7135335 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term79 A f x b s) = (term551 A f x b s).
Proof. exact (MK_COMB (@lem7135334 A f x) (@lem7135333 A b s)). Qed.
Lemma lem7135337 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135338 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7135337 real (real -> Prop) f x). Qed.
Lemma lem7135339 {A : Type'} (f : A -> real) (x : A) : (term550 A f x) = (term552 A f x).
Proof. exact (@lem7135338 real_le (@I (A -> real) f x)). Qed.
Lemma lem7135340 {A : Type'} (b : real) (s : A -> Prop) : (term548 A b s) = (term548 A b s).
Proof. exact (eq_refl (term548 A b s)). Qed.
Lemma lem7135341 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term551 A f x b s) = (term553 A f x b s).
Proof. exact (MK_COMB (@lem7135339 A f x) (@lem7135340 A b s)). Qed.
Lemma lem7135343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135344 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7135343 real Prop f x). Qed.
Lemma lem7135345 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term553 A f x b s) = (term554 A f x b s).
Proof. exact (@lem7135344 (term552 A f x) (term548 A b s)). Qed.
Lemma lem7135346 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term551 A f x b s) = (term554 A f x b s).
Proof. exact (TRANS (@lem7135341 A f x b s) (@lem7135345 A f x b s)). Qed.
Lemma lem7135347 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term79 A f x b s) = (term554 A f x b s).
Proof. exact (TRANS (@lem7135335 A f x b s) (@lem7135346 A f x b s)). Qed.
Lemma lem7135348 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7135355 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135356 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7135355 A (type686 A) f x). Qed.
Lemma lem7135357 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7135356 A (@IN A) x). Qed.
Lemma lem7135358 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7135359 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem7135357 A x) (@lem7135358 A s)). Qed.
Lemma lem7135361 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135362 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7135361 (A -> Prop) Prop f x). Qed.
Lemma lem7135363 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term555 A x s).
Proof. exact (@lem7135362 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem7135365 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term555 A x s).
Proof. exact (TRANS (@lem7135359 A x s) (@lem7135363 A x s)). Qed.
Lemma lem7135366 {A : Type'} (x : A) (s : A -> Prop) : (term556 A x s) = (term557 A x s).
Proof. exact (MK_COMB (@lem7135348) (@lem7135365 A x s)). Qed.
Lemma lem7135367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7135368 {A : Type'} (x : A) (s : A -> Prop) : (term558 A x s) = (term559 A x s).
Proof. exact (MK_COMB (@lem7135367) (@lem7135366 A x s)). Qed.
Lemma lem7135369 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term78 A f x b s) = (term560 A f x b s).
Proof. exact (MK_COMB (@lem7135368 A x s) (@lem7135347 A f x b s)). Qed.
Lemma lem7135370 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term80 A f b s) = (term561 A f b s).
Proof. exact (fun_ext (fun x : A => @lem7135369 A f x b s)). Qed.
Lemma lem7135371 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7135372 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term81 A f b s) = (term562 A f b s).
Proof. exact (MK_COMB (@lem7135371 A) (@lem7135370 A f b s)). Qed.
Lemma lem7135381 {A : Type'} (s : A -> Prop) : (term68 A s) = (term68 A s).
Proof. exact (eq_refl (term68 A s)). Qed.
Lemma lem7135382 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term82 A f b s) = (term563 A f b s).
Proof. exact (MK_COMB (@lem7135381 A s) (@lem7135372 A f b s)). Qed.
Lemma lem7135387 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7135388 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7135387 (A -> Prop) Prop f x). Qed.
Lemma lem7135390 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7135388 A (@FINITE A) s). Qed.
Lemma lem7135391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7135392 {A : Type'} (s : A -> Prop) : (term39 A s) = (term405 A s).
Proof. exact (MK_COMB (@lem7135391) (@lem7135390 A s)). Qed.
Lemma lem7135393 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term83 A f b s) = (term564 A f b s).
Proof. exact (MK_COMB (@lem7135392 A s) (@lem7135382 A f b s)). Qed.
Lemma lem7135394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7135395 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term86 A f b s) = (term565 A f b s).
Proof. exact (MK_COMB (@lem7135394) (@lem7135393 A f b s)). Qed.
Lemma lem7135396 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term88 A s f b) = (term566 A s f b).
Proof. exact (MK_COMB (@lem7135395 A f b s) (@lem7135294 A s f b)). Qed.
Lemma lem7135397 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term566 A s f b.
Proof. exact (EQ_MP (@lem7135396 A s f b) (@lem7134640 A s f b h1)). Qed.
Lemma lem7135399 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term564 A f b s.
Proof. exact (proj1 (@lem7135397 A s f b h1)). Qed.
Lemma lem7135400 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term563 A f b s.
Proof. exact (proj2 (@lem7135399 A s f b h1)). Qed.
Lemma lem7135402 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term562 A f b s.
Proof. exact (proj2 (@lem7135400 A s f b h1)). Qed.
Lemma lem7135404 (h1 : term56) : term458.
Proof. exact (proj2 (@lem7135008 h1)). Qed.
Lemma lem7135406 {A : Type'} (h1 : term59 A) : term439 A.
Proof. exact (proj2 (@lem7134934 A h1)). Qed.
Lemma lem7135409 {A : Type'} (h1 : term12 A) : term427 A.
Proof. exact (proj1 (@lem7134856 A h1)). Qed.
Lemma lem7135419 (y : real) (x : real) : (term478 y x) = (term478 y x).
Proof. exact (eq_refl (term478 y x)). Qed.
Lemma lem7135420 (x : real) : (term479 x) = (term479 x).
Proof. exact (fun_ext (fun y : real => @lem7135419 y x)). Qed.
Lemma lem7135421 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7135422 (x : real) : (term480 x) = (term480 x).
Proof. exact (MK_COMB (@lem7135421) (@lem7135420 x)). Qed.
Lemma lem7135423 : term481 = term481.
Proof. exact (fun_ext (fun x : real => @lem7135422 x)). Qed.
Lemma lem7135424 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7135426 : term482 = term482.
Proof. exact (MK_COMB (@lem7135424) (@lem7135423)). Qed.
Lemma lem7135427 (h1 : term52) : term482.
Proof. exact (EQ_MP (@lem7135426) (@lem7135074 h1)). Qed.
Lemma lem7135429 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term499 A f s b) = (term499 A f s b).
Proof. exact (eq_refl (term499 A f s b)). Qed.
Lemma lem7135446 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term527 A x s f b) = (term567 A x s f b).
Proof. exact (@lem19490 (term521 A x f b s) (term419 A s) (term514 A x s f b)). Qed.
Lemma lem7135447 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7135448 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term529 A x s f b) = (term568 A x s f b).
Proof. exact (MK_COMB (@lem7135447) (@lem7135446 A x s f b)). Qed.
Lemma lem7135449 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) (b : real) : (term531 A x f s b) = (term569 A x f s b).
Proof. exact (MK_COMB (@lem7135448 A x s f b) (@lem7135429 A f s b)). Qed.
Lemma lem7135456 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) (b : real) : (term569 A x f s b) = (term570 A x f s b).
Proof. exact (@lem19699 (term571 A x f b s) (term572 A x s f b) (term499 A f s b)). Qed.
Lemma lem7135457 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) (b : real) : (term531 A x f s b) = (term570 A x f s b).
Proof. exact (TRANS (@lem7135449 A x f s b) (@lem7135456 A x f s b)). Qed.
Lemma lem7135458 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) : (term533 A x f s) = (term573 A x f s).
Proof. exact (fun_ext (fun b : real => @lem7135457 A x f s b)). Qed.
Lemma lem7135459 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7135460 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) : (term535 A x f s) = (term574 A x f s).
Proof. exact (MK_COMB (@lem7135459) (@lem7135458 A x f s)). Qed.
Lemma lem7135461 {A : Type'} (x : type645 A) (s : A -> Prop) : (term537 A x s) = (term575 A x s).
Proof. exact (fun_ext (fun f : A -> real => @lem7135460 A x f s)). Qed.
Lemma lem7135462 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7135463 {A : Type'} (x : type645 A) (s : A -> Prop) : (term538 A x s) = (term576 A x s).
Proof. exact (MK_COMB (@lem7135462 A) (@lem7135461 A x s)). Qed.
Lemma lem7135464 {A : Type'} (x : type645 A) : (term539 A x) = (term577 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7135463 A x s)). Qed.
Lemma lem7135465 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7135467 {A : Type'} (x : type645 A) : (term540 A x) = (term578 A x).
Proof. exact (MK_COMB (@lem7135465 A) (@lem7135464 A x)). Qed.
Lemma lem7135468 {A : Type'} (x : type645 A) (h1 : term399 A x) : term578 A x.
Proof. exact (EQ_MP (@lem7135467 A x) (@lem7135259 A x h1)). Qed.
Lemma lem7135488 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term560 A f x b s) = (term560 A f x b s).
Proof. exact (eq_refl (term560 A f x b s)). Qed.
Lemma lem7135489 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term561 A f b s) = (term561 A f b s).
Proof. exact (fun_ext (fun x : A => @lem7135488 A f x b s)). Qed.
Lemma lem7135490 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7135492 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term562 A f b s) = (term562 A f b s).
Proof. exact (MK_COMB (@lem7135490 A) (@lem7135489 A f b s)). Qed.
Lemma lem7135493 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term562 A f b s.
Proof. exact (EQ_MP (@lem7135492 A f b s) (@lem7135402 A s f b h1)). Qed.
Lemma lem7135517 (m : nat) (n : nat) : (term454 m n) = (term454 m n).
Proof. exact (eq_refl (term454 m n)). Qed.
Lemma lem7135518 (m : nat) : (term455 m) = (term455 m).
Proof. exact (fun_ext (fun n : nat => @lem7135517 m n)). Qed.
Lemma lem7135519 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7135520 (m : nat) : (term456 m) = (term456 m).
Proof. exact (MK_COMB (@lem7135519) (@lem7135518 m)). Qed.
Lemma lem7135521 : term457 = term457.
Proof. exact (fun_ext (fun m : nat => @lem7135520 m)). Qed.
Lemma lem7135522 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7135524 : term458 = term458.
Proof. exact (MK_COMB (@lem7135522) (@lem7135521)). Qed.
Lemma lem7135525 (h1 : term56) : term458.
Proof. exact (EQ_MP (@lem7135524) (@lem7135404 h1)). Qed.
Lemma lem7135546 {A : Type'} (s : A -> Prop) : (term437 A s) = (term437 A s).
Proof. exact (eq_refl (term437 A s)). Qed.
Lemma lem7135547 {A : Type'} : (term438 A) = (term438 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7135546 A s)). Qed.
Lemma lem7135548 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7135550 {A : Type'} : (term439 A) = (term439 A).
Proof. exact (MK_COMB (@lem7135548 A) (@lem7135547 A)). Qed.
Lemma lem7135551 {A : Type'} (h1 : term59 A) : term439 A.
Proof. exact (EQ_MP (@lem7135550 A) (@lem7135406 A h1)). Qed.
Lemma lem7135565 {A : Type'} (s : A -> Prop) (n : nat) : (term423 A s n) = (term423 A s n).
Proof. exact (eq_refl (term423 A s n)). Qed.
Lemma lem7135566 {A : Type'} (s : A -> Prop) : (term424 A s) = (term424 A s).
Proof. exact (fun_ext (fun n : nat => @lem7135565 A s n)). Qed.
Lemma lem7135567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7135568 {A : Type'} (s : A -> Prop) : (term425 A s) = (term425 A s).
Proof. exact (MK_COMB (@lem7135567) (@lem7135566 A s)). Qed.
Lemma lem7135569 {A : Type'} : (term426 A) = (term426 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7135568 A s)). Qed.
Lemma lem7135570 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7135572 {A : Type'} : (term427 A) = (term427 A).
Proof. exact (MK_COMB (@lem7135570 A) (@lem7135569 A)). Qed.
Lemma lem7135573 {A : Type'} (h1 : term12 A) : term427 A.
Proof. exact (EQ_MP (@lem7135572 A) (@lem7135409 A h1)). Qed.
Lemma lem7135648 (_95230 : real) (h1 : term52) : term579 _95230.
Proof. exact (@lem7135427 h1 _95230). Qed.
Lemma lem7135649 (_95230 : real) : (term579 _95230) = (term480 _95230).
Proof. exact (eq_refl (term579 _95230)). Qed.
Lemma lem7135650 (_95230 : real) (h1 : term52) : term480 _95230.
Proof. exact (EQ_MP (@lem7135649 _95230) (@lem7135648 _95230 h1)). Qed.
Lemma lem7135651 (_95230 : real) (_95231 : real) (h1 : term52) : term580 _95230 _95231.
Proof. exact (@lem7135650 _95230 h1 _95231). Qed.
Lemma lem7135652 (_95231 : real) (_95230 : real) : (term580 _95230 _95231) = (term478 _95231 _95230).
Proof. exact (eq_refl (term580 _95230 _95231)). Qed.
Lemma lem7135654 {A : Type'} (_95232 : A -> Prop) (x : type645 A) (h1 : term399 A x) : term581 A x _95232.
Proof. exact (@lem7135468 A x h1 _95232). Qed.
Lemma lem7135655 {A : Type'} (x : type645 A) (_95232 : A -> Prop) : (term581 A x _95232) = (term576 A x _95232).
Proof. exact (eq_refl (term581 A x _95232)). Qed.
Lemma lem7135656 {A : Type'} (_95232 : A -> Prop) (x : type645 A) (h1 : term399 A x) : term576 A x _95232.
Proof. exact (EQ_MP (@lem7135655 A x _95232) (@lem7135654 A _95232 x h1)). Qed.
Lemma lem7135657 {A : Type'} (_95232 : A -> Prop) (_95233 : A -> real) (x : type645 A) (h1 : term399 A x) : term582 A x _95232 _95233.
Proof. exact (@lem7135656 A _95232 x h1 _95233). Qed.
Lemma lem7135658 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95232 : A -> Prop) : (term582 A x _95232 _95233) = (term574 A x _95233 _95232).
Proof. exact (eq_refl (term582 A x _95232 _95233)). Qed.
Lemma lem7135659 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (x : type645 A) (h1 : term399 A x) : term574 A x _95233 _95232.
Proof. exact (EQ_MP (@lem7135658 A x _95233 _95232) (@lem7135657 A _95232 _95233 x h1)). Qed.
Lemma lem7135660 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) (x : type645 A) (h1 : term399 A x) : term583 A x _95233 _95232 _95234.
Proof. exact (@lem7135659 A _95233 _95232 x h1 _95234). Qed.
Lemma lem7135661 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : (term583 A x _95233 _95232 _95234) = (term570 A x _95233 _95232 _95234).
Proof. exact (eq_refl (term583 A x _95233 _95232 _95234)). Qed.
Lemma lem7135662 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) (x : type645 A) (h1 : term399 A x) : term570 A x _95233 _95232 _95234.
Proof. exact (EQ_MP (@lem7135661 A x _95233 _95232 _95234) (@lem7135660 A _95233 _95232 _95234 x h1)). Qed.
Lemma lem7135663 {A : Type'} (_95235 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term584 A f b s _95235.
Proof. exact (@lem7135493 A s f b h1 _95235). Qed.
Lemma lem7135664 {A : Type'} (f : A -> real) (_95235 : A) (b : real) (s : A -> Prop) : (term584 A f b s _95235) = (term560 A f _95235 b s).
Proof. exact (eq_refl (term584 A f b s _95235)). Qed.
Lemma lem7135672 (_95238 : nat) (h1 : term56) : term585 _95238.
Proof. exact (@lem7135525 h1 _95238). Qed.
Lemma lem7135673 (_95238 : nat) : (term585 _95238) = (term456 _95238).
Proof. exact (eq_refl (term585 _95238)). Qed.
Lemma lem7135674 (_95238 : nat) (h1 : term56) : term456 _95238.
Proof. exact (EQ_MP (@lem7135673 _95238) (@lem7135672 _95238 h1)). Qed.
Lemma lem7135675 (_95238 : nat) (_95239 : nat) (h1 : term56) : term586 _95238 _95239.
Proof. exact (@lem7135674 _95238 h1 _95239). Qed.
Lemma lem7135676 (_95238 : nat) (_95239 : nat) : (term586 _95238 _95239) = (term454 _95238 _95239).
Proof. exact (eq_refl (term586 _95238 _95239)). Qed.
Lemma lem7135681 {A : Type'} (_95241 : A -> Prop) (h1 : term59 A) : term587 A _95241.
Proof. exact (@lem7135551 A h1 _95241). Qed.
Lemma lem7135682 {A : Type'} (_95241 : A -> Prop) : (term587 A _95241) = (term437 A _95241).
Proof. exact (eq_refl (term587 A _95241)). Qed.
Lemma lem7135684 {A : Type'} (_95242 : A -> Prop) (h1 : term12 A) : term588 A _95242.
Proof. exact (@lem7135573 A h1 _95242). Qed.
Lemma lem7135685 {A : Type'} (_95242 : A -> Prop) : (term588 A _95242) = (term425 A _95242).
Proof. exact (eq_refl (term588 A _95242)). Qed.
Lemma lem7135686 {A : Type'} (_95242 : A -> Prop) (h1 : term12 A) : term425 A _95242.
Proof. exact (EQ_MP (@lem7135685 A _95242) (@lem7135684 A _95242 h1)). Qed.
Lemma lem7135687 {A : Type'} (_95242 : A -> Prop) (_95243 : nat) (h1 : term12 A) : term589 A _95242 _95243.
Proof. exact (@lem7135686 A _95242 h1 _95243). Qed.
Lemma lem7135688 {A : Type'} (_95242 : A -> Prop) (_95243 : nat) : (term589 A _95242 _95243) = (term423 A _95242 _95243).
Proof. exact (eq_refl (term589 A _95242 _95243)). Qed.
Lemma lem7135712 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) (x : type645 A) (h1 : term399 A x) : term590 A x _95233 _95232 _95234.
Proof. exact (proj2 (@lem7135662 A _95233 _95232 _95234 x h1)). Qed.
Lemma lem7135713 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) (x : type645 A) (h1 : term399 A x) : term591 A x _95233 _95232 _95234.
Proof. exact (proj1 (@lem7135662 A _95233 _95232 _95234 x h1)). Qed.
Lemma lem7135719 (_95231 : real) (_95230 : real) (h1 : term52) : term478 _95231 _95230.
Proof. exact (EQ_MP (@lem7135652 _95231 _95230) (@lem7135651 _95230 _95231 h1)). Qed.
Lemma lem7135725 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term440 A s.
Proof. exact (proj1 (@lem7135400 A s f b h1)). Qed.
Lemma lem7135731 {A : Type'} (_95235 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term560 A f _95235 b s.
Proof. exact (EQ_MP (@lem7135664 A f _95235 b s) (@lem7135663 A _95235 s f b h1)). Qed.
Lemma lem7135743 (_95238 : nat) (_95239 : nat) (h1 : term56) : term454 _95238 _95239.
Proof. exact (EQ_MP (@lem7135676 _95238 _95239) (@lem7135675 _95238 _95239 h1)). Qed.
Lemma lem7135755 {A : Type'} (_95241 : A -> Prop) (h1 : term59 A) : term437 A _95241.
Proof. exact (EQ_MP (@lem7135682 A _95241) (@lem7135681 A _95241 h1)). Qed.
Lemma lem7135765 {A : Type'} (_95242 : A -> Prop) (_95243 : nat) (h1 : term12 A) : term423 A _95242 _95243.
Proof. exact (EQ_MP (@lem7135688 A _95242 _95243) (@lem7135687 A _95242 _95243 h1)). Qed.
Lemma lem7135810 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : (term591 A x _95233 _95232 _95234) = (term592 A x _95233 _95232 _95234).
Proof. exact (@lem7132632 (term419 A _95232) (term521 A x _95233 _95234 _95232) (term499 A _95233 _95232 _95234)). Qed.
Lemma lem7135811 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) (x : type645 A) (h1 : term399 A x) : term592 A x _95233 _95232 _95234.
Proof. exact (EQ_MP (@lem7135810 A x _95233 _95232 _95234) (@lem7135713 A _95233 _95232 _95234 x h1)). Qed.
Lemma lem7135822 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : (term590 A x _95233 _95232 _95234) = (term593 A x _95233 _95232 _95234).
Proof. exact (@lem7132632 (term419 A _95232) (term514 A x _95232 _95233 _95234) (term499 A _95233 _95232 _95234)). Qed.
Lemma lem7135823 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) (x : type645 A) (h1 : term399 A x) : term593 A x _95233 _95232 _95234.
Proof. exact (EQ_MP (@lem7135822 A x _95233 _95232 _95234) (@lem7135712 A _95233 _95232 _95234 x h1)). Qed.
Lemma lem7135881 : (@I (real -> Prop)) = (@I (real -> Prop)).
Proof. exact (eq_refl (@I (real -> Prop))). Qed.
Lemma lem7135882 (_95262 : real -> Prop) (_95264 : real -> Prop) (h1 : _95262 = _95264) : _95262 = _95264.
Proof. exact (h1). Qed.
Lemma lem7135883 (_95263 : real) (_95265 : real) (h1 : _95263 = _95265) : _95263 = _95265.
Proof. exact (h1). Qed.
Lemma lem7135884 (_95262 : real -> Prop) (_95264 : real -> Prop) (h1 : _95262 = _95264) : (@I (real -> Prop) _95262) = (@I (real -> Prop) _95264).
Proof. exact (MK_COMB (@lem7135881) (@lem7135882 _95262 _95264 h1)). Qed.
Lemma lem7135885 (_95262 : real -> Prop) (_95264 : real -> Prop) (_95263 : real) (_95265 : real) (h1 : _95262 = _95264) (h2 : _95263 = _95265) : (@I (real -> Prop) _95262 _95263) = (@I (real -> Prop) _95264 _95265).
Proof. exact (MK_COMB (@lem7135884 _95262 _95264 h1) (@lem7135883 _95263 _95265 h2)). Qed.
Lemma lem7135887 (b : Prop) (a : Prop) : term594 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem7135888 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : term595 _95264 _95265 _95262 _95263.
Proof. exact (@lem7135887 (@I (real -> Prop) _95264 _95265) (@I (real -> Prop) _95262 _95263)). Qed.
Lemma lem7135889 (_95262 : real -> Prop) (_95264 : real -> Prop) (_95263 : real) (_95265 : real) (h1 : _95262 = _95264) (h2 : _95263 = _95265) : term596 _95264 _95265 _95262 _95263.
Proof. exact (@lem7135888 _95264 _95265 _95262 _95263 (@lem7135885 _95262 _95264 _95263 _95265 h1 h2)). Qed.
Lemma lem7135890 (_95265 : real) (_95263 : real) (_95262 : real -> Prop) (_95264 : real -> Prop) (h1 : _95262 = _95264) : term597 _95264 _95265 _95262 _95263.
Proof. exact (fun h0 : _95263 = _95265 => @lem7135889 _95262 _95264 _95263 _95265 h1 h0). Qed.
Lemma lem7135892 (a : Prop) (b : Prop) : (a -> b) = (term598 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7135893 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term597 _95264 _95265 _95262 _95263) = (term599 _95264 _95265 _95262 _95263).
Proof. exact (@lem7135892 (_95263 = _95265) (term596 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7135894 (_95265 : real) (_95263 : real) (_95262 : real -> Prop) (_95264 : real -> Prop) (h1 : _95262 = _95264) : term599 _95264 _95265 _95262 _95263.
Proof. exact (EQ_MP (@lem7135893 _95264 _95265 _95262 _95263) (@lem7135890 _95265 _95263 _95262 _95264 h1)). Qed.
Lemma lem7135895 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : term600 _95264 _95265 _95262 _95263.
Proof. exact (fun h0 : _95262 = _95264 => @lem7135894 _95265 _95263 _95262 _95264 h0). Qed.
Lemma lem7135897 (a : Prop) (b : Prop) : (a -> b) = (term598 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7135898 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term600 _95264 _95265 _95262 _95263) = (term601 _95264 _95265 _95262 _95263).
Proof. exact (@lem7135897 (_95262 = _95264) (term599 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7135899 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : term601 _95264 _95265 _95262 _95263.
Proof. exact (EQ_MP (@lem7135898 _95264 _95265 _95262 _95263) (@lem7135895 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136191 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem7135399 A s f b h1)). Qed.
Lemma lem7136192 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term602 A s.
Proof. exact (fun h0 : term419 A s => @lem7136191 A s f b h1). Qed.
Lemma lem7136194 (p : Prop) : (term603 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7136195 {A : Type'} (s : A -> Prop) : (term602 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7136194 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem7136196 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7136195 A s) (@lem7136192 A s f b h1)). Qed.
Lemma lem7136198 (x : real -> Prop) : x = x.
Proof. exact (@lem21386 (real -> Prop) x). Qed.
Lemma lem7136199 {A : Type'} (s : A -> Prop) (f : A -> real) : (term497 A s f) = (term497 A s f).
Proof. exact (@lem7136198 (term497 A s f)). Qed.
Lemma lem7136200 {A : Type'} (s : A -> Prop) (f : A -> real) : term604 A s f.
Proof. exact (fun h0 : term605 A s f => @lem7136199 A s f). Qed.
Lemma lem7136202 (p : Prop) : (term603 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7136203 {A : Type'} (s : A -> Prop) (f : A -> real) : (term604 A s f) = ((term497 A s f) = (term497 A s f)).
Proof. exact (@lem7136202 ((term497 A s f) = (term497 A s f))). Qed.
Lemma lem7136204 {A : Type'} (s : A -> Prop) (f : A -> real) : (term497 A s f) = (term497 A s f).
Proof. exact (EQ_MP (@lem7136203 A s f) (@lem7136200 A s f)). Qed.
Lemma lem7136206 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term544 A s f b.
Proof. exact (proj2 (@lem7135397 A s f b h1)). Qed.
Lemma lem7136207 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term606 A s f b.
Proof. exact (fun h0 : term543 A s f b => @lem7136206 A s f b h1). Qed.
Lemma lem7136209 (p : Prop) : (term607 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7136210 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term606 A s f b) = (term544 A s f b).
Proof. exact (@lem7136209 (term543 A s f b)). Qed.
Lemma lem7136211 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term544 A s f b.
Proof. exact (EQ_MP (@lem7136210 A s f b) (@lem7136207 A s f b h1)). Qed.
Lemma lem7136213 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem7135399 A s f b h1)). Qed.
Lemma lem7136214 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term602 A s.
Proof. exact (fun h0 : term419 A s => @lem7136213 A s f b h1). Qed.
Lemma lem7136216 (p : Prop) : (term603 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7136217 {A : Type'} (s : A -> Prop) : (term602 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7136216 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem7136218 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7136217 A s) (@lem7136214 A s f b h1)). Qed.
Lemma lem7136220 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem7135399 A s f b h1)). Qed.
Lemma lem7136221 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term602 A s.
Proof. exact (fun h0 : term419 A s => @lem7136220 A s f b h1). Qed.
Lemma lem7136223 (p : Prop) : (term603 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7136224 {A : Type'} (s : A -> Prop) : (term602 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7136223 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem7136225 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7136224 A s) (@lem7136221 A s f b h1)). Qed.
Lemma lem7136228 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term608 A f b s) : term608 A f b s.
Proof. exact (h1). Qed.
Lemma lem7136229 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term608 A f b s) : term609 A f b s.
Proof. exact (fun h0 : term610 A f b s => @lem7136228 A f b s h1). Qed.
Lemma lem7136231 (p : Prop) : (term607 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7136232 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term609 A f b s) = (term608 A f b s).
Proof. exact (@lem7136231 (term610 A f b s)). Qed.
Lemma lem7136233 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term608 A f b s) : term608 A f b s.
Proof. exact (EQ_MP (@lem7136232 A f b s) (@lem7136229 A f b s h1)). Qed.
Lemma lem7136239 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7136240 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : (term592 A x _95233 _95232 _95234) = (term611 A x _95233 _95232 _95234).
Proof. exact (@lem7136239 (term521 A x _95233 _95234 _95232) (term419 A _95232) (term499 A _95233 _95232 _95234)). Qed.
Lemma lem7136254 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7136255 {A : Type'} (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) : (term612 A _95233 _95232 _95234) = (term613 A _95233 _95234 _95232).
Proof. exact (@lem7136254 (term499 A _95233 _95232 _95234) (term419 A _95232)). Qed.
Lemma lem7136261 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) : (term614 A x _95233 _95234 _95232) = (term614 A x _95233 _95234 _95232).
Proof. exact (eq_refl (term614 A x _95233 _95234 _95232)). Qed.
Lemma lem7136262 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) : (term611 A x _95233 _95232 _95234) = (term615 A x _95233 _95234 _95232).
Proof. exact (MK_COMB (@lem7136261 A x _95233 _95234 _95232) (@lem7136255 A _95233 _95234 _95232)). Qed.
Lemma lem7136273 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) : (term592 A x _95233 _95232 _95234) = (term615 A x _95233 _95234 _95232).
Proof. exact (TRANS (@lem7136240 A x _95233 _95232 _95234) (@lem7136262 A x _95233 _95234 _95232)). Qed.
Lemma lem7136274 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7136275 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) : (term616 A x _95233 _95232 _95234) = (term617 A x _95233 _95234 _95232).
Proof. exact (MK_COMB (@lem7136274) (@lem7136273 A x _95233 _95234 _95232)). Qed.
Lemma lem7136289 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7136290 {A : Type'} (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) : (term612 A _95233 _95232 _95234) = (term613 A _95233 _95234 _95232).
Proof. exact (@lem7136289 (term499 A _95233 _95232 _95234) (term419 A _95232)). Qed.
Lemma lem7136296 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) : (term614 A x _95233 _95234 _95232) = (term614 A x _95233 _95234 _95232).
Proof. exact (eq_refl (term614 A x _95233 _95234 _95232)). Qed.
Lemma lem7136297 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) : (term611 A x _95233 _95232 _95234) = (term615 A x _95233 _95234 _95232).
Proof. exact (MK_COMB (@lem7136296 A x _95233 _95234 _95232) (@lem7136290 A _95233 _95234 _95232)). Qed.
Lemma lem7136308 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) : ((term592 A x _95233 _95232 _95234) = (term611 A x _95233 _95232 _95234)) = ((term615 A x _95233 _95234 _95232) = (term615 A x _95233 _95234 _95232)).
Proof. exact (MK_COMB (@lem7136275 A x _95233 _95234 _95232) (@lem7136297 A x _95233 _95234 _95232)). Qed.
Lemma lem7136310 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7136311 (x : Prop) : (x = x) = True.
Proof. exact (@lem7136310 Prop x). Qed.
Lemma lem7136312 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) : ((term615 A x _95233 _95234 _95232) = (term615 A x _95233 _95234 _95232)) = True.
Proof. exact (@lem7136311 (term615 A x _95233 _95234 _95232)). Qed.
Lemma lem7136313 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : ((term592 A x _95233 _95232 _95234) = (term611 A x _95233 _95232 _95234)) = True.
Proof. exact (TRANS (@lem7136308 A x _95233 _95234 _95232) (@lem7136312 A x _95233 _95234 _95232)). Qed.
Lemma lem7136314 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : True = ((term592 A x _95233 _95232 _95234) = (term611 A x _95233 _95232 _95234)).
Proof. exact (SYM (@lem7136313 A x _95233 _95232 _95234)). Qed.
Lemma lem7136315 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : (term592 A x _95233 _95232 _95234) = (term611 A x _95233 _95232 _95234).
Proof. exact (EQ_MP (@lem7136314 A x _95233 _95232 _95234) (@lem0)). Qed.
Lemma lem7136316 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) (x : type645 A) (h1 : term399 A x) : term611 A x _95233 _95232 _95234.
Proof. exact (EQ_MP (@lem7136315 A x _95233 _95232 _95234) (@lem7135811 A _95233 _95232 _95234 x h1)). Qed.
Lemma lem7136318 (b : Prop) (a : Prop) : (a \/ b) = (term618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7136319 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) : (term611 A x _95233 _95232 _95234) = (term619 A x _95233 _95234 _95232).
Proof. exact (@lem7136318 (term612 A _95233 _95232 _95234) (term521 A x _95233 _95234 _95232)). Qed.
Lemma lem7136321 (a : Prop) (b : Prop) : (term620 a b) = (term621 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7136322 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : (term622 A _95233 _95232 _95234) = (term623 A _95233 _95232 _95234).
Proof. exact (@lem7136321 (term419 A _95232) (term499 A _95233 _95232 _95234)). Qed.
Lemma lem7136324 (a : Prop) : (term624 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7136325 {A : Type'} (_95232 : A -> Prop) : (term625 A _95232) = (@I ((A -> Prop) -> Prop) (@FINITE A) _95232).
Proof. exact (@lem7136324 (@I ((A -> Prop) -> Prop) (@FINITE A) _95232)). Qed.
Lemma lem7136326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7136327 {A : Type'} (_95232 : A -> Prop) : (term626 A _95232) = (term405 A _95232).
Proof. exact (MK_COMB (@lem7136326) (@lem7136325 A _95232)). Qed.
Lemma lem7136328 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : (term627 A _95233 _95232 _95234) = (term627 A _95233 _95232 _95234).
Proof. exact (eq_refl (term627 A _95233 _95232 _95234)). Qed.
Lemma lem7136329 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : (term623 A _95233 _95232 _95234) = (term628 A _95233 _95232 _95234).
Proof. exact (MK_COMB (@lem7136327 A _95232) (@lem7136328 A _95233 _95232 _95234)). Qed.
Lemma lem7136330 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : (term622 A _95233 _95232 _95234) = (term628 A _95233 _95232 _95234).
Proof. exact (TRANS (@lem7136322 A _95233 _95232 _95234) (@lem7136329 A _95233 _95232 _95234)). Qed.
Lemma lem7136331 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7136332 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : (term629 A _95233 _95232 _95234) = (term630 A _95233 _95232 _95234).
Proof. exact (MK_COMB (@lem7136331) (@lem7136330 A _95233 _95232 _95234)). Qed.
Lemma lem7136333 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) : (term521 A x _95233 _95234 _95232) = (term521 A x _95233 _95234 _95232).
Proof. exact (eq_refl (term521 A x _95233 _95234 _95232)). Qed.
Lemma lem7136334 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) : (term619 A x _95233 _95234 _95232) = (term631 A x _95233 _95234 _95232).
Proof. exact (MK_COMB (@lem7136332 A _95233 _95232 _95234) (@lem7136333 A x _95233 _95234 _95232)). Qed.
Lemma lem7136335 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) : (term611 A x _95233 _95232 _95234) = (term631 A x _95233 _95234 _95232).
Proof. exact (TRANS (@lem7136319 A x _95233 _95234 _95232) (@lem7136334 A x _95233 _95234 _95232)). Qed.
Lemma lem7136337 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term608 A f b s) (h2 : term88 A s f b) : term632 A f b s.
Proof. exact (conj (@lem7136225 A s f b h2) (@lem7136233 A f b s h1)). Qed.
Lemma lem7136339 {A : Type'} (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) (x : type645 A) (h1 : term399 A x) : term631 A x _95233 _95234 _95232.
Proof. exact (EQ_MP (@lem7136335 A x _95233 _95234 _95232) (@lem7136316 A _95233 _95232 _95234 x h1)). Qed.
Lemma lem7136340 {A : Type'} (_95233 : A -> real) (_95234 : real) (_95232 : A -> Prop) (x : type645 A) (h1 : term399 A x) : term631 A x _95233 _95234 _95232.
Proof. exact (@lem7136339 A _95233 _95234 _95232 x h1). Qed.
Lemma lem7136341 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (x : type645 A) (h1 : term399 A x) : term633 A x f b s.
Proof. exact (@lem7136340 A f (term548 A b s) s x h1). Qed.
Lemma lem7136344 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term608 A f b s) (h3 : term88 A s f b) : term634 A x f b s.
Proof. exact (@lem7136341 A f b s x h1 (@lem7136337 A s f b h2 h3)). Qed.
Lemma lem7136345 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term608 A f b s) (h3 : term88 A s f b) : term635 A x f b s.
Proof. exact (fun h0 : term636 A x f b s => @lem7136344 A x s f b h1 h2 h3). Qed.
Lemma lem7136347 (p : Prop) : (term603 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7136348 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term635 A x f b s) = (term634 A x f b s).
Proof. exact (@lem7136347 (term634 A x f b s)). Qed.
Lemma lem7136349 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term608 A f b s) (h3 : term88 A s f b) : term634 A x f b s.
Proof. exact (EQ_MP (@lem7136348 A x f b s) (@lem7136345 A x s f b h1 h2 h3)). Qed.
Lemma lem7136355 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7136356 {A : Type'} (f : A -> real) (b : real) (_95235 : A) (s : A -> Prop) : (term560 A f _95235 b s) = (term637 A f b _95235 s).
Proof. exact (@lem7136355 (term554 A f _95235 b s) (term557 A _95235 s)). Qed.
Lemma lem7136362 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7136363 {A : Type'} (f : A -> real) (b : real) (_95235 : A) (s : A -> Prop) : (term638 A f _95235 b s) = (term639 A f b _95235 s).
Proof. exact (MK_COMB (@lem7136362) (@lem7136356 A f b _95235 s)). Qed.
Lemma lem7136369 {A : Type'} (f : A -> real) (b : real) (_95235 : A) (s : A -> Prop) : (term637 A f b _95235 s) = (term637 A f b _95235 s).
Proof. exact (eq_refl (term637 A f b _95235 s)). Qed.
Lemma lem7136370 {A : Type'} (f : A -> real) (b : real) (_95235 : A) (s : A -> Prop) : ((term560 A f _95235 b s) = (term637 A f b _95235 s)) = ((term637 A f b _95235 s) = (term637 A f b _95235 s)).
Proof. exact (MK_COMB (@lem7136363 A f b _95235 s) (@lem7136369 A f b _95235 s)). Qed.
Lemma lem7136372 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7136373 (x : Prop) : (x = x) = True.
Proof. exact (@lem7136372 Prop x). Qed.
Lemma lem7136374 {A : Type'} (f : A -> real) (b : real) (_95235 : A) (s : A -> Prop) : ((term637 A f b _95235 s) = (term637 A f b _95235 s)) = True.
Proof. exact (@lem7136373 (term637 A f b _95235 s)). Qed.
Lemma lem7136375 {A : Type'} (f : A -> real) (b : real) (_95235 : A) (s : A -> Prop) : ((term560 A f _95235 b s) = (term637 A f b _95235 s)) = True.
Proof. exact (TRANS (@lem7136370 A f b _95235 s) (@lem7136374 A f b _95235 s)). Qed.
Lemma lem7136376 {A : Type'} (f : A -> real) (b : real) (_95235 : A) (s : A -> Prop) : True = ((term560 A f _95235 b s) = (term637 A f b _95235 s)).
Proof. exact (SYM (@lem7136375 A f b _95235 s)). Qed.
Lemma lem7136377 {A : Type'} (f : A -> real) (b : real) (_95235 : A) (s : A -> Prop) : (term560 A f _95235 b s) = (term637 A f b _95235 s).
Proof. exact (EQ_MP (@lem7136376 A f b _95235 s) (@lem0)). Qed.
Lemma lem7136378 {A : Type'} (_95235 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term637 A f b _95235 s.
Proof. exact (EQ_MP (@lem7136377 A f b _95235 s) (@lem7135731 A _95235 s f b h1)). Qed.
Lemma lem7136380 (b : Prop) (a : Prop) : (a \/ b) = (term618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7136381 {A : Type'} (f : A -> real) (_95235 : A) (b : real) (s : A -> Prop) : (term637 A f b _95235 s) = (term640 A f _95235 b s).
Proof. exact (@lem7136380 (term557 A _95235 s) (term554 A f _95235 b s)). Qed.
Lemma lem7136383 (a : Prop) : (term624 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7136384 {A : Type'} (_95235 : A) (s : A -> Prop) : (term641 A _95235 s) = (term555 A _95235 s).
Proof. exact (@lem7136383 (term555 A _95235 s)). Qed.
Lemma lem7136385 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7136386 {A : Type'} (_95235 : A) (s : A -> Prop) : (term642 A _95235 s) = (term643 A _95235 s).
Proof. exact (MK_COMB (@lem7136385) (@lem7136384 A _95235 s)). Qed.
Lemma lem7136387 {A : Type'} (f : A -> real) (_95235 : A) (b : real) (s : A -> Prop) : (term554 A f _95235 b s) = (term554 A f _95235 b s).
Proof. exact (eq_refl (term554 A f _95235 b s)). Qed.
Lemma lem7136388 {A : Type'} (f : A -> real) (_95235 : A) (b : real) (s : A -> Prop) : (term640 A f _95235 b s) = (term644 A f _95235 b s).
Proof. exact (MK_COMB (@lem7136386 A _95235 s) (@lem7136387 A f _95235 b s)). Qed.
Lemma lem7136389 {A : Type'} (f : A -> real) (_95235 : A) (b : real) (s : A -> Prop) : (term637 A f b _95235 s) = (term644 A f _95235 b s).
Proof. exact (TRANS (@lem7136381 A f _95235 b s) (@lem7136388 A f _95235 b s)). Qed.
Lemma lem7136392 {A : Type'} (_95235 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term644 A f _95235 b s.
Proof. exact (EQ_MP (@lem7136389 A f _95235 b s) (@lem7136378 A _95235 s f b h1)). Qed.
Lemma lem7136393 {A : Type'} (_95235 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term644 A f _95235 b s.
Proof. exact (@lem7136392 A _95235 s f b h1). Qed.
Lemma lem7136394 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term645 A x f b s.
Proof. exact (@lem7136393 A (term646 A x f b s) s f b h1). Qed.
Lemma lem7136397 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term608 A f b s) (h3 : term88 A s f b) : term647 A x f b s.
Proof. exact (@lem7136394 A x s f b h3 (@lem7136349 A x s f b h1 h2 h3)). Qed.
Lemma lem7136398 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term608 A f b s) (h3 : term88 A s f b) : term648 A x f b s.
Proof. exact (fun h0 : term649 A x f b s => @lem7136397 A x s f b h1 h2 h3). Qed.
Lemma lem7136400 (p : Prop) : (term603 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7136401 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term648 A x f b s) = (term647 A x f b s).
Proof. exact (@lem7136400 (term647 A x f b s)). Qed.
Lemma lem7136402 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term608 A f b s) (h3 : term88 A s f b) : term647 A x f b s.
Proof. exact (EQ_MP (@lem7136401 A x f b s) (@lem7136398 A x s f b h1 h2 h3)). Qed.
Lemma lem7136418 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7136419 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : (term650 A x _95233 _95232 _95234) = (term651 A x _95232 _95233 _95234).
Proof. exact (@lem7136418 (term499 A _95233 _95232 _95234) (term514 A x _95232 _95233 _95234)). Qed.
Lemma lem7136425 {A : Type'} (_95232 : A -> Prop) : (term420 A _95232) = (term420 A _95232).
Proof. exact (eq_refl (term420 A _95232)). Qed.
Lemma lem7136426 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : (term593 A x _95233 _95232 _95234) = (term652 A x _95232 _95233 _95234).
Proof. exact (MK_COMB (@lem7136425 A _95232) (@lem7136419 A x _95232 _95233 _95234)). Qed.
Lemma lem7136430 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7136431 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : (term652 A x _95232 _95233 _95234) = (term653 A x _95232 _95233 _95234).
Proof. exact (@lem7136430 (term499 A _95233 _95232 _95234) (term419 A _95232) (term514 A x _95232 _95233 _95234)). Qed.
Lemma lem7136447 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : (term593 A x _95233 _95232 _95234) = (term653 A x _95232 _95233 _95234).
Proof. exact (TRANS (@lem7136426 A x _95232 _95233 _95234) (@lem7136431 A x _95232 _95233 _95234)). Qed.
Lemma lem7136448 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7136449 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : (term654 A x _95233 _95232 _95234) = (term655 A x _95232 _95233 _95234).
Proof. exact (MK_COMB (@lem7136448) (@lem7136447 A x _95232 _95233 _95234)). Qed.
Lemma lem7136465 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : (term653 A x _95232 _95233 _95234) = (term653 A x _95232 _95233 _95234).
Proof. exact (eq_refl (term653 A x _95232 _95233 _95234)). Qed.
Lemma lem7136466 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : ((term593 A x _95233 _95232 _95234) = (term653 A x _95232 _95233 _95234)) = ((term653 A x _95232 _95233 _95234) = (term653 A x _95232 _95233 _95234)).
Proof. exact (MK_COMB (@lem7136449 A x _95232 _95233 _95234) (@lem7136465 A x _95232 _95233 _95234)). Qed.
Lemma lem7136468 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7136469 (x : Prop) : (x = x) = True.
Proof. exact (@lem7136468 Prop x). Qed.
Lemma lem7136470 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : ((term653 A x _95232 _95233 _95234) = (term653 A x _95232 _95233 _95234)) = True.
Proof. exact (@lem7136469 (term653 A x _95232 _95233 _95234)). Qed.
Lemma lem7136471 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : ((term593 A x _95233 _95232 _95234) = (term653 A x _95232 _95233 _95234)) = True.
Proof. exact (TRANS (@lem7136466 A x _95232 _95233 _95234) (@lem7136470 A x _95232 _95233 _95234)). Qed.
Lemma lem7136472 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : True = ((term593 A x _95233 _95232 _95234) = (term653 A x _95232 _95233 _95234)).
Proof. exact (SYM (@lem7136471 A x _95232 _95233 _95234)). Qed.
Lemma lem7136473 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : (term593 A x _95233 _95232 _95234) = (term653 A x _95232 _95233 _95234).
Proof. exact (EQ_MP (@lem7136472 A x _95232 _95233 _95234) (@lem0)). Qed.
Lemma lem7136474 {A : Type'} (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) (x : type645 A) (h1 : term399 A x) : term653 A x _95232 _95233 _95234.
Proof. exact (EQ_MP (@lem7136473 A x _95232 _95233 _95234) (@lem7135823 A _95233 _95232 _95234 x h1)). Qed.
Lemma lem7136476 (b : Prop) (a : Prop) : (a \/ b) = (term618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7136477 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : (term653 A x _95232 _95233 _95234) = (term656 A x _95233 _95232 _95234).
Proof. exact (@lem7136476 (term572 A x _95232 _95233 _95234) (term499 A _95233 _95232 _95234)). Qed.
Lemma lem7136479 (a : Prop) (b : Prop) : (term620 a b) = (term621 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7136480 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : (term657 A x _95232 _95233 _95234) = (term658 A x _95232 _95233 _95234).
Proof. exact (@lem7136479 (term419 A _95232) (term514 A x _95232 _95233 _95234)). Qed.
Lemma lem7136482 (a : Prop) : (term624 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7136483 {A : Type'} (_95232 : A -> Prop) : (term625 A _95232) = (@I ((A -> Prop) -> Prop) (@FINITE A) _95232).
Proof. exact (@lem7136482 (@I ((A -> Prop) -> Prop) (@FINITE A) _95232)). Qed.
Lemma lem7136484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7136485 {A : Type'} (_95232 : A -> Prop) : (term626 A _95232) = (term405 A _95232).
Proof. exact (MK_COMB (@lem7136484) (@lem7136483 A _95232)). Qed.
Lemma lem7136487 (a : Prop) : (term624 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7136488 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : (term659 A x _95232 _95233 _95234) = (term512 A x _95232 _95233 _95234).
Proof. exact (@lem7136487 (term512 A x _95232 _95233 _95234)). Qed.
Lemma lem7136489 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : (term658 A x _95232 _95233 _95234) = (term660 A x _95232 _95233 _95234).
Proof. exact (MK_COMB (@lem7136485 A _95232) (@lem7136488 A x _95232 _95233 _95234)). Qed.
Lemma lem7136490 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : (term657 A x _95232 _95233 _95234) = (term660 A x _95232 _95233 _95234).
Proof. exact (TRANS (@lem7136480 A x _95232 _95233 _95234) (@lem7136489 A x _95232 _95233 _95234)). Qed.
Lemma lem7136491 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7136492 {A : Type'} (x : type645 A) (_95232 : A -> Prop) (_95233 : A -> real) (_95234 : real) : (term661 A x _95232 _95233 _95234) = (term662 A x _95232 _95233 _95234).
Proof. exact (MK_COMB (@lem7136491) (@lem7136490 A x _95232 _95233 _95234)). Qed.
Lemma lem7136493 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : (term499 A _95233 _95232 _95234) = (term499 A _95233 _95232 _95234).
Proof. exact (eq_refl (term499 A _95233 _95232 _95234)). Qed.
Lemma lem7136494 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : (term656 A x _95233 _95232 _95234) = (term663 A x _95233 _95232 _95234).
Proof. exact (MK_COMB (@lem7136492 A x _95232 _95233 _95234) (@lem7136493 A _95233 _95232 _95234)). Qed.
Lemma lem7136495 {A : Type'} (x : type645 A) (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) : (term653 A x _95232 _95233 _95234) = (term663 A x _95233 _95232 _95234).
Proof. exact (TRANS (@lem7136477 A x _95233 _95232 _95234) (@lem7136494 A x _95233 _95232 _95234)). Qed.
Lemma lem7136497 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term608 A f b s) (h3 : term88 A s f b) : term664 A x f b s.
Proof. exact (conj (@lem7136218 A s f b h3) (@lem7136402 A x s f b h1 h2 h3)). Qed.
Lemma lem7136499 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) (x : type645 A) (h1 : term399 A x) : term663 A x _95233 _95232 _95234.
Proof. exact (EQ_MP (@lem7136495 A x _95233 _95232 _95234) (@lem7136474 A _95232 _95233 _95234 x h1)). Qed.
Lemma lem7136500 {A : Type'} (_95233 : A -> real) (_95232 : A -> Prop) (_95234 : real) (x : type645 A) (h1 : term399 A x) : term663 A x _95233 _95232 _95234.
Proof. exact (@lem7136499 A _95233 _95232 _95234 x h1). Qed.
Lemma lem7136501 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (x : type645 A) (h1 : term399 A x) : term665 A x f b s.
Proof. exact (@lem7136500 A f s (term548 A b s) x h1). Qed.
Lemma lem7136504 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term608 A f b s) (h3 : term88 A s f b) : term610 A f b s.
Proof. exact (@lem7136501 A f b s x h1 (@lem7136497 A x s f b h1 h2 h3)). Qed.
Lemma lem7136505 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term88 A s f b) : term666 A f b s.
Proof. exact (fun h0 : term608 A f b s => @lem7136504 A x s f b h1 h0 h2). Qed.
Lemma lem7136507 (p : Prop) : (term603 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7136508 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term666 A f b s) = (term610 A f b s).
Proof. exact (@lem7136507 (term610 A f b s)). Qed.
Lemma lem7136509 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term88 A s f b) : term610 A f b s.
Proof. exact (EQ_MP (@lem7136508 A f b s) (@lem7136505 A x s f b h1 h2)). Qed.
Lemma lem7136527 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7136528 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term599 _95264 _95265 _95262 _95263) = (term667 _95264 _95265 _95262 _95263).
Proof. exact (@lem7136527 (@I (real -> Prop) _95264 _95265) (term668 _95263 _95265) (term669 _95262 _95263)). Qed.
Lemma lem7136546 (_95262 : real -> Prop) (_95264 : real -> Prop) : (term670 _95262 _95264) = (term670 _95262 _95264).
Proof. exact (eq_refl (term670 _95262 _95264)). Qed.
Lemma lem7136547 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term601 _95264 _95265 _95262 _95263) = (term671 _95264 _95265 _95262 _95263).
Proof. exact (MK_COMB (@lem7136546 _95262 _95264) (@lem7136528 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136551 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7136552 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term671 _95264 _95265 _95262 _95263) = (term672 _95264 _95265 _95262 _95263).
Proof. exact (@lem7136551 (@I (real -> Prop) _95264 _95265) (term673 _95262 _95264) (term674 _95265 _95262 _95263)). Qed.
Lemma lem7136582 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term601 _95264 _95265 _95262 _95263) = (term672 _95264 _95265 _95262 _95263).
Proof. exact (TRANS (@lem7136547 _95264 _95265 _95262 _95263) (@lem7136552 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7136584 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term675 _95264 _95265 _95262 _95263) = (term676 _95264 _95265 _95262 _95263).
Proof. exact (MK_COMB (@lem7136583) (@lem7136582 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136588 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7136589 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term677 _95264 _95265 _95262 _95263) = (term601 _95264 _95265 _95262 _95263).
Proof. exact (@lem7136588 (term673 _95262 _95264) (term668 _95263 _95265) (term596 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136605 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7136606 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term599 _95264 _95265 _95262 _95263) = (term667 _95264 _95265 _95262 _95263).
Proof. exact (@lem7136605 (@I (real -> Prop) _95264 _95265) (term668 _95263 _95265) (term669 _95262 _95263)). Qed.
Lemma lem7136624 (_95262 : real -> Prop) (_95264 : real -> Prop) : (term670 _95262 _95264) = (term670 _95262 _95264).
Proof. exact (eq_refl (term670 _95262 _95264)). Qed.
Lemma lem7136625 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term601 _95264 _95265 _95262 _95263) = (term671 _95264 _95265 _95262 _95263).
Proof. exact (MK_COMB (@lem7136624 _95262 _95264) (@lem7136606 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136629 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7136630 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term671 _95264 _95265 _95262 _95263) = (term672 _95264 _95265 _95262 _95263).
Proof. exact (@lem7136629 (@I (real -> Prop) _95264 _95265) (term673 _95262 _95264) (term674 _95265 _95262 _95263)). Qed.
Lemma lem7136660 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term601 _95264 _95265 _95262 _95263) = (term672 _95264 _95265 _95262 _95263).
Proof. exact (TRANS (@lem7136625 _95264 _95265 _95262 _95263) (@lem7136630 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136661 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term677 _95264 _95265 _95262 _95263) = (term672 _95264 _95265 _95262 _95263).
Proof. exact (TRANS (@lem7136589 _95264 _95265 _95262 _95263) (@lem7136660 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136662 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : ((term601 _95264 _95265 _95262 _95263) = (term677 _95264 _95265 _95262 _95263)) = ((term672 _95264 _95265 _95262 _95263) = (term672 _95264 _95265 _95262 _95263)).
Proof. exact (MK_COMB (@lem7136584 _95264 _95265 _95262 _95263) (@lem7136661 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136664 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7136665 (x : Prop) : (x = x) = True.
Proof. exact (@lem7136664 Prop x). Qed.
Lemma lem7136666 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : ((term672 _95264 _95265 _95262 _95263) = (term672 _95264 _95265 _95262 _95263)) = True.
Proof. exact (@lem7136665 (term672 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136667 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : ((term601 _95264 _95265 _95262 _95263) = (term677 _95264 _95265 _95262 _95263)) = True.
Proof. exact (TRANS (@lem7136662 _95264 _95265 _95262 _95263) (@lem7136666 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136668 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : True = ((term601 _95264 _95265 _95262 _95263) = (term677 _95264 _95265 _95262 _95263)).
Proof. exact (SYM (@lem7136667 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136669 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term601 _95264 _95265 _95262 _95263) = (term677 _95264 _95265 _95262 _95263).
Proof. exact (EQ_MP (@lem7136668 _95264 _95265 _95262 _95263) (@lem0)). Qed.
Lemma lem7136670 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : term677 _95264 _95265 _95262 _95263.
Proof. exact (EQ_MP (@lem7136669 _95264 _95265 _95262 _95263) (@lem7135899 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136672 (b : Prop) (a : Prop) : (a \/ b) = (term618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7136673 (_95264 : real -> Prop) (_95262 : real -> Prop) (_95263 : real) (_95265 : real) : (term677 _95264 _95265 _95262 _95263) = (term678 _95264 _95262 _95263 _95265).
Proof. exact (@lem7136672 (term679 _95264 _95265 _95262 _95263) (term668 _95263 _95265)). Qed.
Lemma lem7136675 (a : Prop) (b : Prop) : (term620 a b) = (term621 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7136676 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term680 _95264 _95265 _95262 _95263) = (term681 _95264 _95265 _95262 _95263).
Proof. exact (@lem7136675 (term673 _95262 _95264) (term596 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136678 (a : Prop) : (term624 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7136679 (_95262 : real -> Prop) (_95264 : real -> Prop) : (term682 _95262 _95264) = (_95262 = _95264).
Proof. exact (@lem7136678 (_95262 = _95264)). Qed.
Lemma lem7136680 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7136681 (_95262 : real -> Prop) (_95264 : real -> Prop) : (term683 _95262 _95264) = (term684 _95262 _95264).
Proof. exact (MK_COMB (@lem7136680) (@lem7136679 _95262 _95264)). Qed.
Lemma lem7136683 (a : Prop) (b : Prop) : (term620 a b) = (term621 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7136684 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term685 _95264 _95265 _95262 _95263) = (term686 _95264 _95265 _95262 _95263).
Proof. exact (@lem7136683 (@I (real -> Prop) _95264 _95265) (term669 _95262 _95263)). Qed.
Lemma lem7136686 (a : Prop) : (term624 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7136687 (_95262 : real -> Prop) (_95263 : real) : (term687 _95262 _95263) = (@I (real -> Prop) _95262 _95263).
Proof. exact (@lem7136686 (@I (real -> Prop) _95262 _95263)). Qed.
Lemma lem7136688 (_95264 : real -> Prop) (_95265 : real) : (term688 _95264 _95265) = (term688 _95264 _95265).
Proof. exact (eq_refl (term688 _95264 _95265)). Qed.
Lemma lem7136689 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term686 _95264 _95265 _95262 _95263) = (term689 _95264 _95265 _95262 _95263).
Proof. exact (MK_COMB (@lem7136688 _95264 _95265) (@lem7136687 _95262 _95263)). Qed.
Lemma lem7136690 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term685 _95264 _95265 _95262 _95263) = (term689 _95264 _95265 _95262 _95263).
Proof. exact (TRANS (@lem7136684 _95264 _95265 _95262 _95263) (@lem7136689 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136691 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term681 _95264 _95265 _95262 _95263) = (term690 _95264 _95265 _95262 _95263).
Proof. exact (MK_COMB (@lem7136681 _95262 _95264) (@lem7136690 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136692 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term680 _95264 _95265 _95262 _95263) = (term690 _95264 _95265 _95262 _95263).
Proof. exact (TRANS (@lem7136676 _95264 _95265 _95262 _95263) (@lem7136691 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136693 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7136694 (_95264 : real -> Prop) (_95265 : real) (_95262 : real -> Prop) (_95263 : real) : (term691 _95264 _95265 _95262 _95263) = (term692 _95264 _95265 _95262 _95263).
Proof. exact (MK_COMB (@lem7136693) (@lem7136692 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136695 (_95263 : real) (_95265 : real) : (term668 _95263 _95265) = (term668 _95263 _95265).
Proof. exact (eq_refl (term668 _95263 _95265)). Qed.
Lemma lem7136696 (_95264 : real -> Prop) (_95262 : real -> Prop) (_95263 : real) (_95265 : real) : (term678 _95264 _95262 _95263 _95265) = (term693 _95264 _95262 _95263 _95265).
Proof. exact (MK_COMB (@lem7136694 _95264 _95265 _95262 _95263) (@lem7136695 _95263 _95265)). Qed.
Lemma lem7136697 (_95264 : real -> Prop) (_95262 : real -> Prop) (_95263 : real) (_95265 : real) : (term677 _95264 _95265 _95262 _95263) = (term693 _95264 _95262 _95263 _95265).
Proof. exact (TRANS (@lem7136673 _95264 _95262 _95263 _95265) (@lem7136696 _95264 _95262 _95263 _95265)). Qed.
Lemma lem7136699 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term88 A s f b) : term694 A f b s.
Proof. exact (conj (@lem7136211 A s f b h2) (@lem7136509 A x s f b h1 h2)). Qed.
Lemma lem7136700 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term88 A s f b) : term695 A f b s.
Proof. exact (conj (@lem7136204 A s f) (@lem7136699 A x s f b h1 h2)). Qed.
Lemma lem7136702 (_95264 : real -> Prop) (_95262 : real -> Prop) (_95263 : real) (_95265 : real) : term693 _95264 _95262 _95263 _95265.
Proof. exact (EQ_MP (@lem7136697 _95264 _95262 _95263 _95265) (@lem7136670 _95264 _95265 _95262 _95263)). Qed.
Lemma lem7136703 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : term696 A f s b.
Proof. exact (@lem7136702 (term497 A s f) (term497 A s f) (term697 A b s) b). Qed.
Lemma lem7136706 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term88 A s f b) : term698 A s b.
Proof. exact (@lem7136703 A f s b (@lem7136700 A x s f b h1 h2)). Qed.
Lemma lem7136707 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term88 A s f b) : term699 A s b.
Proof. exact (fun h0 : (term697 A b s) = b => @lem7136706 A x s f b h1 h2). Qed.
Lemma lem7136709 (p : Prop) : (term607 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7136710 {A : Type'} (s : A -> Prop) (b : real) : (term699 A s b) = (term698 A s b).
Proof. exact (@lem7136709 ((term697 A b s) = b)). Qed.
Lemma lem7136711 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term88 A s f b) : term698 A s b.
Proof. exact (EQ_MP (@lem7136710 A s b) (@lem7136707 A x s f b h1 h2)). Qed.
Lemma lem7136713 (b : Prop) (a : Prop) : (a \/ b) = (term618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7136716 (_95230 : real) (_95231 : real) : (term478 _95231 _95230) = (term700 _95230 _95231).
Proof. exact (@lem7136713 ((term472 _95230 _95231) = _95230) (_95231 = term476)). Qed.
Lemma lem7136719 (_95230 : real) (_95231 : real) (h1 : term52) : term700 _95230 _95231.
Proof. exact (EQ_MP (@lem7136716 _95230 _95231) (@lem7135719 _95231 _95230 h1)). Qed.
Lemma lem7136720 {A : Type'} (b : real) (s : A -> Prop) (h1 : term52) : term701 A b s.
Proof. exact (@lem7136719 b (term486 A s) h1). Qed.
Lemma lem7136723 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term52) (h3 : term88 A s f b) : (term486 A s) = term476.
Proof. exact (@lem7136720 A b s h2 (@lem7136711 A x s f b h1 h3)). Qed.
Lemma lem7136724 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term52) (h3 : term88 A s f b) : term702 A s.
Proof. exact (fun h0 : term703 A s => @lem7136723 A x s f b h1 h2 h3). Qed.
Lemma lem7136726 (p : Prop) : (term603 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7136727 {A : Type'} (s : A -> Prop) : (term702 A s) = ((term486 A s) = term476).
Proof. exact (@lem7136726 ((term486 A s) = term476)). Qed.
Lemma lem7136728 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term52) (h3 : term88 A s f b) : (term486 A s) = term476.
Proof. exact (EQ_MP (@lem7136727 A s) (@lem7136724 A x s f b h1 h2 h3)). Qed.
Lemma lem7136734 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7136735 (_95238 : nat) (_95239 : nat) : (term454 _95238 _95239) = (term704 _95238 _95239).
Proof. exact (@lem7136734 (_95238 = _95239) (term451 _95238 _95239)). Qed.
Lemma lem7136745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7136746 (_95238 : nat) (_95239 : nat) : (term705 _95238 _95239) = (term706 _95238 _95239).
Proof. exact (MK_COMB (@lem7136745) (@lem7136735 _95238 _95239)). Qed.
Lemma lem7136756 (_95238 : nat) (_95239 : nat) : (term704 _95238 _95239) = (term704 _95238 _95239).
Proof. exact (eq_refl (term704 _95238 _95239)). Qed.
Lemma lem7136757 (_95238 : nat) (_95239 : nat) : ((term454 _95238 _95239) = (term704 _95238 _95239)) = ((term704 _95238 _95239) = (term704 _95238 _95239)).
Proof. exact (MK_COMB (@lem7136746 _95238 _95239) (@lem7136756 _95238 _95239)). Qed.
Lemma lem7136759 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7136760 (x : Prop) : (x = x) = True.
Proof. exact (@lem7136759 Prop x). Qed.
Lemma lem7136761 (_95238 : nat) (_95239 : nat) : ((term704 _95238 _95239) = (term704 _95238 _95239)) = True.
Proof. exact (@lem7136760 (term704 _95238 _95239)). Qed.
Lemma lem7136762 (_95238 : nat) (_95239 : nat) : ((term454 _95238 _95239) = (term704 _95238 _95239)) = True.
Proof. exact (TRANS (@lem7136757 _95238 _95239) (@lem7136761 _95238 _95239)). Qed.
Lemma lem7136763 (_95238 : nat) (_95239 : nat) : True = ((term454 _95238 _95239) = (term704 _95238 _95239)).
Proof. exact (SYM (@lem7136762 _95238 _95239)). Qed.
Lemma lem7136764 (_95238 : nat) (_95239 : nat) : (term454 _95238 _95239) = (term704 _95238 _95239).
Proof. exact (EQ_MP (@lem7136763 _95238 _95239) (@lem0)). Qed.
Lemma lem7136765 (_95238 : nat) (_95239 : nat) (h1 : term56) : term704 _95238 _95239.
Proof. exact (EQ_MP (@lem7136764 _95238 _95239) (@lem7135743 _95238 _95239 h1)). Qed.
Lemma lem7136767 (b : Prop) (a : Prop) : (a \/ b) = (term618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7136768 (_95238 : nat) (_95239 : nat) : (term704 _95238 _95239) = (term707 _95238 _95239).
Proof. exact (@lem7136767 (term451 _95238 _95239) (_95238 = _95239)). Qed.
Lemma lem7136770 (a : Prop) : (term624 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7136771 (_95238 : nat) (_95239 : nat) : (term708 _95238 _95239) = ((@I (nat -> real) real_of_num _95238) = (@I (nat -> real) real_of_num _95239)).
Proof. exact (@lem7136770 ((@I (nat -> real) real_of_num _95238) = (@I (nat -> real) real_of_num _95239))). Qed.
Lemma lem7136772 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7136773 (_95238 : nat) (_95239 : nat) : (term709 _95238 _95239) = (term710 _95238 _95239).
Proof. exact (MK_COMB (@lem7136772) (@lem7136771 _95238 _95239)). Qed.
Lemma lem7136774 (_95238 : nat) (_95239 : nat) : (_95238 = _95239) = (_95238 = _95239).
Proof. exact (eq_refl (_95238 = _95239)). Qed.
Lemma lem7136775 (_95238 : nat) (_95239 : nat) : (term707 _95238 _95239) = (term711 _95238 _95239).
Proof. exact (MK_COMB (@lem7136773 _95238 _95239) (@lem7136774 _95238 _95239)). Qed.
Lemma lem7136776 (_95238 : nat) (_95239 : nat) : (term704 _95238 _95239) = (term711 _95238 _95239).
Proof. exact (TRANS (@lem7136768 _95238 _95239) (@lem7136775 _95238 _95239)). Qed.
Lemma lem7136779 (_95238 : nat) (_95239 : nat) (h1 : term56) : term711 _95238 _95239.
Proof. exact (EQ_MP (@lem7136776 _95238 _95239) (@lem7136765 _95238 _95239 h1)). Qed.
Lemma lem7136780 {A : Type'} (s : A -> Prop) (h1 : term56) : term712 A s.
Proof. exact (@lem7136779 (@I ((A -> Prop) -> nat) (@CARD A) s) (@I (nat -> nat) NUMERAL 0) h1). Qed.
Lemma lem7136783 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term56) (h3 : term52) (h4 : term88 A s f b) : (@I ((A -> Prop) -> nat) (@CARD A) s) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7136780 A s h2 (@lem7136728 A x s f b h1 h3 h4)). Qed.
Lemma lem7136784 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term56) (h3 : term52) (h4 : term88 A s f b) : term713 A s.
Proof. exact (fun h0 : term714 A s => @lem7136783 A x s f b h1 h2 h3 h4). Qed.
Lemma lem7136786 (p : Prop) : (term603 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7136787 {A : Type'} (s : A -> Prop) : (term713 A s) = ((@I ((A -> Prop) -> nat) (@CARD A) s) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (@lem7136786 ((@I ((A -> Prop) -> nat) (@CARD A) s) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem7136788 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term56) (h3 : term52) (h4 : term88 A s f b) : (@I ((A -> Prop) -> nat) (@CARD A) s) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (EQ_MP (@lem7136787 A s) (@lem7136784 A x s f b h1 h2 h3 h4)). Qed.
Lemma lem7136790 (b : Prop) (a : Prop) : (a \/ b) = (term618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7136791 {A : Type'} (_95242 : A -> Prop) (_95243 : nat) : (term423 A _95242 _95243) = (term715 A _95242 _95243).
Proof. exact (@lem7136790 (term421 A _95242 _95243) (term407 A _95242 _95243)). Qed.
Lemma lem7136793 (a : Prop) (b : Prop) : (term620 a b) = (term621 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7136794 {A : Type'} (_95242 : A -> Prop) (_95243 : nat) : (term716 A _95242 _95243) = (term717 A _95242 _95243).
Proof. exact (@lem7136793 (term419 A _95242) (term418 A _95242 _95243)). Qed.
Lemma lem7136796 (a : Prop) : (term624 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7136797 {A : Type'} (_95242 : A -> Prop) : (term625 A _95242) = (@I ((A -> Prop) -> Prop) (@FINITE A) _95242).
Proof. exact (@lem7136796 (@I ((A -> Prop) -> Prop) (@FINITE A) _95242)). Qed.
Lemma lem7136798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7136799 {A : Type'} (_95242 : A -> Prop) : (term626 A _95242) = (term405 A _95242).
Proof. exact (MK_COMB (@lem7136798) (@lem7136797 A _95242)). Qed.
Lemma lem7136801 (a : Prop) : (term624 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7136802 {A : Type'} (_95242 : A -> Prop) (_95243 : nat) : (term718 A _95242 _95243) = ((@I ((A -> Prop) -> nat) (@CARD A) _95242) = _95243).
Proof. exact (@lem7136801 ((@I ((A -> Prop) -> nat) (@CARD A) _95242) = _95243)). Qed.
Lemma lem7136803 {A : Type'} (_95242 : A -> Prop) (_95243 : nat) : (term717 A _95242 _95243) = (term406 A _95242 _95243).
Proof. exact (MK_COMB (@lem7136799 A _95242) (@lem7136802 A _95242 _95243)). Qed.
Lemma lem7136804 {A : Type'} (_95242 : A -> Prop) (_95243 : nat) : (term716 A _95242 _95243) = (term406 A _95242 _95243).
Proof. exact (TRANS (@lem7136794 A _95242 _95243) (@lem7136803 A _95242 _95243)). Qed.
Lemma lem7136805 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7136806 {A : Type'} (_95242 : A -> Prop) (_95243 : nat) : (term719 A _95242 _95243) = (term720 A _95242 _95243).
Proof. exact (MK_COMB (@lem7136805) (@lem7136804 A _95242 _95243)). Qed.
Lemma lem7136807 {A : Type'} (_95242 : A -> Prop) (_95243 : nat) : (term407 A _95242 _95243) = (term407 A _95242 _95243).
Proof. exact (eq_refl (term407 A _95242 _95243)). Qed.
Lemma lem7136808 {A : Type'} (_95242 : A -> Prop) (_95243 : nat) : (term715 A _95242 _95243) = (term721 A _95242 _95243).
Proof. exact (MK_COMB (@lem7136806 A _95242 _95243) (@lem7136807 A _95242 _95243)). Qed.
Lemma lem7136809 {A : Type'} (_95242 : A -> Prop) (_95243 : nat) : (term423 A _95242 _95243) = (term721 A _95242 _95243).
Proof. exact (TRANS (@lem7136791 A _95242 _95243) (@lem7136808 A _95242 _95243)). Qed.
Lemma lem7136811 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term56) (h3 : term52) (h4 : term88 A s f b) : term722 A s.
Proof. exact (conj (@lem7136196 A s f b h4) (@lem7136788 A x s f b h1 h2 h3 h4)). Qed.
Lemma lem7136813 {A : Type'} (_95242 : A -> Prop) (_95243 : nat) (h1 : term12 A) : term721 A _95242 _95243.
Proof. exact (EQ_MP (@lem7136809 A _95242 _95243) (@lem7135765 A _95242 _95243 h1)). Qed.
Lemma lem7136814 {A : Type'} (_95242 : A -> Prop) (_95243 : nat) (h1 : term12 A) : term721 A _95242 _95243.
Proof. exact (@lem7136813 A _95242 _95243 h1). Qed.
Lemma lem7136815 {A : Type'} (s : A -> Prop) (h1 : term12 A) : term723 A s.
Proof. exact (@lem7136814 A s (@I (nat -> nat) NUMERAL 0) h1). Qed.
Lemma lem7136818 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term12 A) (h3 : term56) (h4 : term52) (h5 : term88 A s f b) : term432 A s.
Proof. exact (@lem7136815 A s h2 (@lem7136811 A x s f b h1 h3 h4 h5)). Qed.
Lemma lem7136819 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term12 A) (h3 : term56) (h4 : term52) (h5 : term88 A s f b) : term724 A s.
Proof. exact (fun h0 : term434 A s => @lem7136818 A x s f b h1 h2 h3 h4 h5). Qed.
Lemma lem7136821 (p : Prop) : (term603 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7136822 {A : Type'} (s : A -> Prop) : (term724 A s) = (term432 A s).
Proof. exact (@lem7136821 (term432 A s)). Qed.
Lemma lem7136823 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term12 A) (h3 : term56) (h4 : term52) (h5 : term88 A s f b) : term432 A s.
Proof. exact (EQ_MP (@lem7136822 A s) (@lem7136819 A x s f b h1 h2 h3 h4 h5)). Qed.
Lemma lem7136829 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7136830 {A : Type'} (_95241 : A -> Prop) : (term437 A _95241) = (term725 A _95241).
Proof. exact (@lem7136829 (_95241 = (@EMPTY A)) (term434 A _95241)). Qed.
Lemma lem7136838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7136839 {A : Type'} (_95241 : A -> Prop) : (term726 A _95241) = (term727 A _95241).
Proof. exact (MK_COMB (@lem7136838) (@lem7136830 A _95241)). Qed.
Lemma lem7136847 {A : Type'} (_95241 : A -> Prop) : (term725 A _95241) = (term725 A _95241).
Proof. exact (eq_refl (term725 A _95241)). Qed.
Lemma lem7136848 {A : Type'} (_95241 : A -> Prop) : ((term437 A _95241) = (term725 A _95241)) = ((term725 A _95241) = (term725 A _95241)).
Proof. exact (MK_COMB (@lem7136839 A _95241) (@lem7136847 A _95241)). Qed.
Lemma lem7136850 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7136851 (x : Prop) : (x = x) = True.
Proof. exact (@lem7136850 Prop x). Qed.
Lemma lem7136852 {A : Type'} (_95241 : A -> Prop) : ((term725 A _95241) = (term725 A _95241)) = True.
Proof. exact (@lem7136851 (term725 A _95241)). Qed.
Lemma lem7136853 {A : Type'} (_95241 : A -> Prop) : ((term437 A _95241) = (term725 A _95241)) = True.
Proof. exact (TRANS (@lem7136848 A _95241) (@lem7136852 A _95241)). Qed.
Lemma lem7136854 {A : Type'} (_95241 : A -> Prop) : True = ((term437 A _95241) = (term725 A _95241)).
Proof. exact (SYM (@lem7136853 A _95241)). Qed.
Lemma lem7136855 {A : Type'} (_95241 : A -> Prop) : (term437 A _95241) = (term725 A _95241).
Proof. exact (EQ_MP (@lem7136854 A _95241) (@lem0)). Qed.
Lemma lem7136856 {A : Type'} (_95241 : A -> Prop) (h1 : term59 A) : term725 A _95241.
Proof. exact (EQ_MP (@lem7136855 A _95241) (@lem7135755 A _95241 h1)). Qed.
Lemma lem7136858 (b : Prop) (a : Prop) : (a \/ b) = (term618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7136859 {A : Type'} (_95241 : A -> Prop) : (term725 A _95241) = (term728 A _95241).
Proof. exact (@lem7136858 (term434 A _95241) (_95241 = (@EMPTY A))). Qed.
Lemma lem7136861 (a : Prop) : (term624 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7136862 {A : Type'} (_95241 : A -> Prop) : (term729 A _95241) = (term432 A _95241).
Proof. exact (@lem7136861 (term432 A _95241)). Qed.
Lemma lem7136863 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7136864 {A : Type'} (_95241 : A -> Prop) : (term730 A _95241) = (term731 A _95241).
Proof. exact (MK_COMB (@lem7136863) (@lem7136862 A _95241)). Qed.
Lemma lem7136865 {A : Type'} (_95241 : A -> Prop) : (_95241 = (@EMPTY A)) = (_95241 = (@EMPTY A)).
Proof. exact (eq_refl (_95241 = (@EMPTY A))). Qed.
Lemma lem7136866 {A : Type'} (_95241 : A -> Prop) : (term728 A _95241) = (term732 A _95241).
Proof. exact (MK_COMB (@lem7136864 A _95241) (@lem7136865 A _95241)). Qed.
Lemma lem7136867 {A : Type'} (_95241 : A -> Prop) : (term725 A _95241) = (term732 A _95241).
Proof. exact (TRANS (@lem7136859 A _95241) (@lem7136866 A _95241)). Qed.
Lemma lem7136870 {A : Type'} (_95241 : A -> Prop) (h1 : term59 A) : term732 A _95241.
Proof. exact (EQ_MP (@lem7136867 A _95241) (@lem7136856 A _95241 h1)). Qed.
Lemma lem7136871 {A : Type'} (_95241 : A -> Prop) (h1 : term59 A) : term732 A _95241.
Proof. exact (@lem7136870 A _95241 h1). Qed.
Lemma lem7136872 {A : Type'} (s : A -> Prop) (h1 : term59 A) : term732 A s.
Proof. exact (@lem7136871 A s h1). Qed.
Lemma lem7136875 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term12 A) (h3 : term59 A) (h4 : term56) (h5 : term52) (h6 : term88 A s f b) : s = (@EMPTY A).
Proof. exact (@lem7136872 A s h3 (@lem7136823 A x s f b h1 h2 h4 h5 h6)). Qed.
Lemma lem7136876 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term12 A) (h3 : term59 A) (h4 : term56) (h5 : term52) (h6 : term88 A s f b) : term733 A s.
Proof. exact (fun h0 : term440 A s => @lem7136875 A x s f b h1 h2 h3 h4 h5 h6). Qed.
Lemma lem7136878 (p : Prop) : (term603 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7136879 {A : Type'} (s : A -> Prop) : (term733 A s) = (s = (@EMPTY A)).
Proof. exact (@lem7136878 (s = (@EMPTY A))). Qed.
Lemma lem7136880 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term12 A) (h3 : term59 A) (h4 : term56) (h5 : term52) (h6 : term88 A s f b) : s = (@EMPTY A).
Proof. exact (EQ_MP (@lem7136879 A s) (@lem7136876 A x s f b h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem7136883 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7136885 {A : Type'} (s : A -> Prop) : (term440 A s) = (term734 A s).
Proof. exact (@lem7136883 (s = (@EMPTY A))). Qed.
Lemma lem7136888 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term88 A s f b) : term734 A s.
Proof. exact (EQ_MP (@lem7136885 A s) (@lem7135725 A s f b h1)). Qed.
Lemma lem7136891 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term12 A) (h3 : term59 A) (h4 : term56) (h5 : term52) (h6 : term88 A s f b) : False.
Proof. exact (@lem7136888 A s f b h6 (@lem7136880 A x s f b h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem7136892 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term12 A) (h3 : term59 A) (h4 : term56) (h5 : term52) (h6 : term88 A s f b) : term735.
Proof. exact (fun h0 : ~ False => @lem7136891 A x s f b h1 h2 h3 h4 h5 h6). Qed.
Lemma lem7136894 (p : Prop) : (term603 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7136895 : term735 = False.
Proof. exact (@lem7136894 False). Qed.
Lemma lem7136896 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term399 A x) (h2 : term12 A) (h3 : term59 A) (h4 : term56) (h5 : term52) (h6 : term88 A s f b) : False.
Proof. exact (EQ_MP (@lem7136895) (@lem7136892 A x s f b h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem7136897 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (h1 : term399 A x) (h2 : term12 A) (h3 : term59 A) (h4 : term56) (h5 : term52) (h6 : term98 A s f) : False.
Proof. exact (ex_elim (@lem7134639 A s f h6) (fun b : real => fun h0 : term97 A s f b => @lem7136896 A x s f b h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem7136898 {A : Type'} (x : type645 A) (s : A -> Prop) (h1 : term399 A x) (h2 : term12 A) (h3 : term59 A) (h4 : term56) (h5 : term52) (h6 : term107 A s) : False.
Proof. exact (ex_elim (@lem7134638 A s h6) (fun f : A -> real => fun h0 : term106 A s f => @lem7136897 A x s f h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem7136899 {A : Type'} (x : type645 A) (h1 : term399 A x) (h2 : term12 A) (h3 : term59 A) (h4 : term56) (h5 : term52) (h6 : term10 A) : False.
Proof. exact (ex_elim (@lem7133241 A h6) (fun s : A -> Prop => fun h0 : term114 A s => @lem7136898 A x s h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem7136900 {A : Type'} (h1 : term11 A) (h2 : term12 A) (h3 : term59 A) (h4 : term56) (h5 : term52) (h6 : term10 A) : False.
Proof. exact (ex_elim (@lem7134636 A h1) (fun x : type645 A => fun h0 : term401 A x => @lem7136899 A x h0 h2 h3 h4 h5 h6)). Qed.
Lemma lem7136901 {A : Type'} (h1 : term12 A) (h2 : term59 A) (h3 : term56) (h4 : term52) (h5 : term10 A) : term17 A.
Proof. exact (fun h0 : term11 A => @lem7136900 A h0 h1 h2 h3 h4 h5). Qed.
Lemma lem7136902 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem69 (term11 A)). Qed.
Lemma lem7136903 {A : Type'} (h1 : term12 A) (h2 : term59 A) (h3 : term56) (h4 : term52) (h5 : term10 A) : term18 A.
Proof. exact (EQ_MP (@lem7136902 A) (@lem7136901 A h1 h2 h3 h4 h5)). Qed.
Lemma lem7136904 {A : Type'} (h1 : term12 A) (h2 : term59 A) (h3 : term56) (h4 : term10 A) : term21 A.
Proof. exact (fun h0 : term52 => @lem7136903 A h1 h2 h3 h0 h4). Qed.
Lemma lem7136905 {A : Type'} (h1 : term12 A) (h2 : term59 A) (h3 : term10 A) : term24 A.
Proof. exact (fun h0 : term56 => @lem7136904 A h1 h2 h0 h3). Qed.
Lemma lem7136906 {A : Type'} (h1 : term12 A) (h2 : term10 A) : term27 A.
Proof. exact (fun h0 : term59 A => @lem7136905 A h1 h0 h2). Qed.
Lemma lem7136907 {A : Type'} (h1 : term10 A) : term30 A.
Proof. exact (fun h0 : term12 A => @lem7136906 A h0 h1). Qed.
Lemma lem7136908 {_100044 A : Type'} (h1 : term10 A) : term32 _100044 A.
Proof. exact (fun h0 : term12 _100044 => @lem7136907 A h1). Qed.
Lemma lem7136909 {_100044 A : Type'} : term34 _100044 A.
Proof. exact (fun h0 : term10 A => @lem7136908 _100044 A h0). Qed.
Lemma lem7136910 {_100044 A : Type'} : term13 _100044 A.
Proof. exact (EQ_MP (@lem7133071 _100044 A) (@lem7136909 _100044 A)). Qed.
Lemma lem7136912 {_100044 A : Type'} : term13 _100044 A.
Proof. exact (@lem7132662 _100044 A (@lem7136910 _100044 A)). Qed.
Lemma lem7136913 {_100044 A : Type'} (h1 : term10 A) : term31 _100044 A.
Proof. exact (@lem7136912 _100044 A (@lem7132637 A h1)). Qed.
Lemma lem7136914 {A : Type'} (h1 : term10 A) : term29 A.
Proof. exact (@lem7136913 Prop A h1 (@lem3863773 Prop)). Qed.
Lemma lem7136915 {A : Type'} (h1 : term10 A) : term26 A.
Proof. exact (@lem7136914 A h1 (@lem7132644 A)). Qed.
Lemma lem7136916 {A : Type'} (h1 : term10 A) : term23 A.
Proof. exact (@lem7136915 A h1 (@lem3864294 A)). Qed.
Lemma lem7136917 {A : Type'} (h1 : term10 A) : term20 A.
Proof. exact (@lem7136916 A h1 (@lem1340231)). Qed.
Lemma lem7136918 {A : Type'} (h1 : term10 A) : term17 A.
Proof. exact (@lem7136917 A h1 (@lem1593226)). Qed.
Lemma lem7136919 {A : Type'} (h1 : term10 A) : False.
Proof. exact (@lem7136918 A h1 (@lem7132638 A)). Qed.
Lemma lem7136920 {A : Type'} (h1 : term10 A) : (term10 A) = False.
Proof. exact (prop_ext (fun h2 : term10 A => @lem7136919 A h1) (fun h2 : False => @lem7132637 A h1)). Qed.
Lemma lem7136921 {A : Type'} (h1 : term10 A) : False.
Proof. exact (EQ_MP (@lem7136920 A h1) (@lem7132637 A h1)). Qed.
Lemma lem7136922 {A : Type'} : term9 A.
Proof. exact (fun h0 : term10 A => @lem7136921 A h0). Qed.
Lemma lem7136923 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem7132636 A) (@lem7136922 A)). Qed.
