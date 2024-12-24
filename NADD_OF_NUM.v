Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_OF_NUM_term_abbrevs.
Require Import DIST_REFL_spec.
Require Import LE_0_spec.
Require Import MULT_AC_spec.
Require Import is_nadd_spec.
Require Import nadd_of_num_spec.
Require Import thm0_spec.
Require Import thm1262760_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1268739 (n : nat) (m : nat) (p : nat) : term0 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem1268743 (n : nat) : term1 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1268744 (n : nat) : (term1 n) = (term2 n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem1268745 (n : nat) : term2 n.
Proof. exact (EQ_MP (@lem1268744 n) (@lem1268743 n)). Qed.
Lemma lem1268746 (n : nat) : (term2 n) = ((term2 n) = True).
Proof. exact (@lem7 (term2 n)). Qed.
Lemma lem1268748 (n : nat) : term3 n.
Proof. exact (@lem1244783 n). Qed.
Lemma lem1268749 (n : nat) : (term3 n) = ((term4 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem1268751 (r : nat -> nat) (h1 : (is_nadd r) = ((term5 r) = r)) : (is_nadd r) = ((term5 r) = r).
Proof. exact (h1). Qed.
Lemma lem1268752 (r : nat -> nat) (h1 : (is_nadd r) = ((term5 r) = r)) : ((term5 r) = r) = (is_nadd r).
Proof. exact (SYM (@lem1268751 r h1)). Qed.
Lemma lem1268753 (r : nat -> nat) (h1 : ((term5 r) = r) = (is_nadd r)) : ((term5 r) = r) = (is_nadd r).
Proof. exact (h1). Qed.
Lemma lem1268754 (r : nat -> nat) (h1 : ((term5 r) = r) = (is_nadd r)) : (is_nadd r) = ((term5 r) = r).
Proof. exact (SYM (@lem1268753 r h1)). Qed.
Lemma lem1268755 (r : nat -> nat) : ((is_nadd r) = ((term5 r) = r)) = (((term5 r) = r) = (is_nadd r)).
Proof. exact (prop_ext (fun h1 : (is_nadd r) = ((term5 r) = r) => @lem1268752 r h1) (fun h1 : ((term5 r) = r) = (is_nadd r) => @lem1268754 r h1)). Qed.
Lemma lem1268757 (x : nat -> nat) : term6 x.
Proof. exact (@lem1262615 x). Qed.
Lemma lem1268758 (x : nat -> nat) : (term6 x) = ((is_nadd x) = (term7 x)).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1268760 (k : nat) : term8 k.
Proof. exact (@lem1268738 k). Qed.
Lemma lem1268761 (k : nat) : (term8 k) = ((nadd_of_num k) = (term9 k)).
Proof. exact (eq_refl (term8 k)). Qed.
Lemma lem1268770 (k : nat) : (nadd_of_num k) = (term9 k).
Proof. exact (EQ_MP (@lem1268761 k) (@lem1268760 k)). Qed.
Lemma lem1268771 : dest_nadd = dest_nadd.
Proof. exact (eq_refl dest_nadd). Qed.
Lemma lem1268772 (k : nat) : (term10 k) = (term11 k).
Proof. exact (MK_COMB (@lem1268771) (@lem1268770 k)). Qed.
Lemma lem1268773 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem1268774 (k : nat) : (term12 k) = (term13 k).
Proof. exact (MK_COMB (@lem1268773) (@lem1268772 k)). Qed.
Lemma lem1268775 (k : nat) : (term14 k) = (term14 k).
Proof. exact (eq_refl (term14 k)). Qed.
Lemma lem1268776 (k : nat) : ((term10 k) = (term14 k)) = ((term11 k) = (term14 k)).
Proof. exact (MK_COMB (@lem1268774 k) (@lem1268775 k)). Qed.
Lemma lem1268778 (r : nat -> nat) : ((term5 r) = r) = (is_nadd r).
Proof. exact (EQ_MP (@lem1268755 r) (@lem1262760 r)). Qed.
Lemma lem1268779 (k : nat) : ((term11 k) = (term14 k)) = (term15 k).
Proof. exact (@lem1268778 (term14 k)). Qed.
Lemma lem1268781 (x : nat -> nat) : (is_nadd x) = (term7 x).
Proof. exact (EQ_MP (@lem1268758 x) (@lem1268757 x)). Qed.
Lemma lem1268782 (k : nat) : (term15 k) = (term16 k).
Proof. exact (@lem1268781 (term14 k)). Qed.
Lemma lem1268796 {A B : Type'} (f : A -> B) (y : A) : (term17 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1268797 (f : nat -> nat) (y : nat) : (term18 f y) = (f y).
Proof. exact (@lem1268796 nat nat f y). Qed.
Lemma lem1268798 (k : nat) (n : nat) : (term19 k n) = (term20 k n).
Proof. exact (@lem1268797 (term14 k) n). Qed.
Lemma lem1268799 (k : nat) (n : nat) : (term20 k n) = (Nat.mul k n).
Proof. exact (eq_refl (term20 k n)). Qed.
Lemma lem1268800 (k : nat) : (term21 k) = (term14 k).
Proof. exact (fun_ext (fun n : nat => @lem1268799 k n)). Qed.
Lemma lem1268801 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1268802 (k : nat) (n : nat) : (term19 k n) = (term20 k n).
Proof. exact (MK_COMB (@lem1268800 k) (@lem1268801 n)). Qed.
Lemma lem1268803 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1268804 (k : nat) (n : nat) : (term22 k n) = (term23 k n).
Proof. exact (MK_COMB (@lem1268803) (@lem1268802 k n)). Qed.
Lemma lem1268805 (k : nat) (n : nat) : (term20 k n) = (Nat.mul k n).
Proof. exact (eq_refl (term20 k n)). Qed.
Lemma lem1268806 (k : nat) (n : nat) : ((term19 k n) = (term20 k n)) = ((term20 k n) = (Nat.mul k n)).
Proof. exact (MK_COMB (@lem1268804 k n) (@lem1268805 k n)). Qed.
Lemma lem1268807 (k : nat) (n : nat) : (term20 k n) = (Nat.mul k n).
Proof. exact (EQ_MP (@lem1268806 k n) (@lem1268798 k n)). Qed.
Lemma lem1268808 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1268809 (m : nat) (k : nat) (n : nat) : (term24 m k n) = (term25 m k n).
Proof. exact (MK_COMB (@lem1268808 m) (@lem1268807 k n)). Qed.
Lemma lem1268810 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1268811 (m : nat) (k : nat) (n : nat) : (term26 m k n) = (term27 m k n).
Proof. exact (MK_COMB (@lem1268810) (@lem1268809 m k n)). Qed.
Lemma lem1268813 {A B : Type'} (f : A -> B) (y : A) : (term17 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1268814 (f : nat -> nat) (y : nat) : (term18 f y) = (f y).
Proof. exact (@lem1268813 nat nat f y). Qed.
Lemma lem1268815 (k : nat) (m : nat) : (term19 k m) = (term20 k m).
Proof. exact (@lem1268814 (term14 k) m). Qed.
Lemma lem1268816 (k : nat) (n : nat) : (term20 k n) = (Nat.mul k n).
Proof. exact (eq_refl (term20 k n)). Qed.
Lemma lem1268817 (k : nat) : (term21 k) = (term14 k).
Proof. exact (fun_ext (fun n : nat => @lem1268816 k n)). Qed.
Lemma lem1268818 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1268819 (k : nat) (m : nat) : (term19 k m) = (term20 k m).
Proof. exact (MK_COMB (@lem1268817 k) (@lem1268818 m)). Qed.
Lemma lem1268820 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1268821 (k : nat) (m : nat) : (term22 k m) = (term23 k m).
Proof. exact (MK_COMB (@lem1268820) (@lem1268819 k m)). Qed.
Lemma lem1268822 (k : nat) (m : nat) : (term20 k m) = (Nat.mul k m).
Proof. exact (eq_refl (term20 k m)). Qed.
Lemma lem1268823 (k : nat) (m : nat) : ((term19 k m) = (term20 k m)) = ((term20 k m) = (Nat.mul k m)).
Proof. exact (MK_COMB (@lem1268821 k m) (@lem1268822 k m)). Qed.
Lemma lem1268824 (k : nat) (m : nat) : (term20 k m) = (Nat.mul k m).
Proof. exact (EQ_MP (@lem1268823 k m) (@lem1268815 k m)). Qed.
Lemma lem1268825 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem1268826 (n : nat) (k : nat) (m : nat) : (term24 n k m) = (term25 n k m).
Proof. exact (MK_COMB (@lem1268825 n) (@lem1268824 k m)). Qed.
Lemma lem1268827 (n : nat) (k : nat) (m : nat) : (term28 n k m) = (term29 n k m).
Proof. exact (MK_COMB (@lem1268811 m k n) (@lem1268826 n k m)). Qed.
Lemma lem1268828 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1268829 (n : nat) (k : nat) (m : nat) : (term30 n k m) = (term31 n k m).
Proof. exact (MK_COMB (@lem1268828) (@lem1268827 n k m)). Qed.
Lemma lem1268830 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1268831 (n : nat) (k : nat) (m : nat) : (term32 n k m) = (term33 n k m).
Proof. exact (MK_COMB (@lem1268830) (@lem1268829 n k m)). Qed.
Lemma lem1268832 (B : nat) (m : nat) (n : nat) : (term34 B m n) = (term34 B m n).
Proof. exact (eq_refl (term34 B m n)). Qed.
Lemma lem1268833 (k : nat) (B : nat) (m : nat) (n : nat) : (term35 k B m n) = (term36 k B m n).
Proof. exact (MK_COMB (@lem1268831 n k m) (@lem1268832 B m n)). Qed.
Lemma lem1268834 (k : nat) (B : nat) (m : nat) : (term37 k B m) = (term38 k B m).
Proof. exact (fun_ext (fun n : nat => @lem1268833 k B m n)). Qed.
Lemma lem1268835 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1268836 (k : nat) (B : nat) (m : nat) : (term39 k B m) = (term40 k B m).
Proof. exact (MK_COMB (@lem1268835) (@lem1268834 k B m)). Qed.
Lemma lem1268841 (k : nat) (B : nat) : (term41 k B) = (term42 k B).
Proof. exact (fun_ext (fun m : nat => @lem1268836 k B m)). Qed.
Lemma lem1268842 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1268843 (k : nat) (B : nat) : (term43 k B) = (term44 k B).
Proof. exact (MK_COMB (@lem1268842) (@lem1268841 k B)). Qed.
Lemma lem1268848 (k : nat) : (term45 k) = (term46 k).
Proof. exact (fun_ext (fun B : nat => @lem1268843 k B)). Qed.
Lemma lem1268849 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1268850 (k : nat) : (term16 k) = (term47 k).
Proof. exact (MK_COMB (@lem1268849) (@lem1268848 k)). Qed.
Lemma lem1268855 (k : nat) : (term15 k) = (term47 k).
Proof. exact (TRANS (@lem1268782 k) (@lem1268850 k)). Qed.
Lemma lem1268856 (k : nat) : ((term11 k) = (term14 k)) = (term47 k).
Proof. exact (TRANS (@lem1268779 k) (@lem1268855 k)). Qed.
Lemma lem1268857 (k : nat) : ((term10 k) = (term14 k)) = (term47 k).
Proof. exact (TRANS (@lem1268776 k) (@lem1268856 k)). Qed.
Lemma lem1268858 : term48 = term49.
Proof. exact (fun_ext (fun k : nat => @lem1268857 k)). Qed.
Lemma lem1268859 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1268860 : term50 = term51.
Proof. exact (MK_COMB (@lem1268859) (@lem1268858)). Qed.
Lemma lem1268865 : term51 = term50.
Proof. exact (SYM (@lem1268860)). Qed.
Lemma lem1268885 (n : nat) (m : nat) (p : nat) : (term25 m n p) = (term25 n m p).
Proof. exact (proj2 (@lem1268739 n m p)). Qed.
Lemma lem1268886 (k : nat) (m : nat) (n : nat) : (term25 m k n) = (term25 k m n).
Proof. exact (@lem1268885 k m n). Qed.
Lemma lem1268895 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1268896 (k : nat) (m : nat) (n : nat) : (term27 m k n) = (term27 k m n).
Proof. exact (MK_COMB (@lem1268895) (@lem1268886 k m n)). Qed.
Lemma lem1268898 (n : nat) (m : nat) (p : nat) : (term25 m n p) = (term25 n m p).
Proof. exact (proj2 (@lem1268739 n m p)). Qed.
Lemma lem1268899 (k : nat) (n : nat) (m : nat) : (term25 n k m) = (term25 k n m).
Proof. exact (@lem1268898 k n m). Qed.
Lemma lem1268907 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1268908 (m : nat) (n : nat) : (Nat.mul n m) = (Nat.mul m n).
Proof. exact (@lem1268907 m n). Qed.
Lemma lem1268911 (k : nat) : (Nat.mul k) = (Nat.mul k).
Proof. exact (eq_refl (Nat.mul k)). Qed.
Lemma lem1268912 (k : nat) (m : nat) (n : nat) : (term25 k n m) = (term25 k m n).
Proof. exact (MK_COMB (@lem1268911 k) (@lem1268908 m n)). Qed.
Lemma lem1268919 (k : nat) (m : nat) (n : nat) : (term25 n k m) = (term25 k m n).
Proof. exact (TRANS (@lem1268899 k n m) (@lem1268912 k m n)). Qed.
Lemma lem1268920 (k : nat) (m : nat) (n : nat) : (term29 n k m) = (term52 k m n).
Proof. exact (MK_COMB (@lem1268896 k m n) (@lem1268919 k m n)). Qed.
Lemma lem1268921 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1268922 (k : nat) (m : nat) (n : nat) : (term31 n k m) = (term53 k m n).
Proof. exact (MK_COMB (@lem1268921) (@lem1268920 k m n)). Qed.
Lemma lem1268924 (n : nat) : (term4 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1268749 n) (@lem1268748 n)). Qed.
Lemma lem1268925 (k : nat) (m : nat) (n : nat) : (term53 k m n) = (NUMERAL 0).
Proof. exact (@lem1268924 (term25 k m n)). Qed.
Lemma lem1268926 (n : nat) (k : nat) (m : nat) : (term31 n k m) = (NUMERAL 0).
Proof. exact (TRANS (@lem1268922 k m n) (@lem1268925 k m n)). Qed.
Lemma lem1268927 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1268928 (n : nat) (k : nat) (m : nat) : (term33 n k m) = term54.
Proof. exact (MK_COMB (@lem1268927) (@lem1268926 n k m)). Qed.
Lemma lem1268932 (B : nat) (m : nat) (n : nat) : (term34 B m n) = (term34 B m n).
Proof. exact (eq_refl (term34 B m n)). Qed.
Lemma lem1268933 (k : nat) (B : nat) (m : nat) (n : nat) : (term36 k B m n) = (term55 B m n).
Proof. exact (MK_COMB (@lem1268928 n k m) (@lem1268932 B m n)). Qed.
Lemma lem1268935 (n : nat) : (term2 n) = True.
Proof. exact (EQ_MP (@lem1268746 n) (@lem1268745 n)). Qed.
Lemma lem1268936 (B : nat) (m : nat) (n : nat) : (term55 B m n) = True.
Proof. exact (@lem1268935 (term34 B m n)). Qed.
Lemma lem1268937 (k : nat) (B : nat) (m : nat) (n : nat) : (term36 k B m n) = True.
Proof. exact (TRANS (@lem1268933 k B m n) (@lem1268936 B m n)). Qed.
Lemma lem1268938 (k : nat) (B : nat) (m : nat) : (term38 k B m) = term56.
Proof. exact (fun_ext (fun n : nat => @lem1268937 k B m n)). Qed.
Lemma lem1268939 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1268940 (k : nat) (B : nat) (m : nat) : (term40 k B m) = term57.
Proof. exact (MK_COMB (@lem1268939) (@lem1268938 k B m)). Qed.
Lemma lem1268942 {A : Type'} (t : Prop) : (term58 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1268943 (t : Prop) : (term59 t) = t.
Proof. exact (@lem1268942 nat t). Qed.
Lemma lem1268944 : term57 = True.
Proof. exact (@lem1268943 True). Qed.
Lemma lem1268945 (k : nat) (B : nat) (m : nat) : (term40 k B m) = True.
Proof. exact (TRANS (@lem1268940 k B m) (@lem1268944)). Qed.
Lemma lem1268946 (k : nat) (B : nat) : (term42 k B) = term56.
Proof. exact (fun_ext (fun m : nat => @lem1268945 k B m)). Qed.
Lemma lem1268947 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1268948 (k : nat) (B : nat) : (term44 k B) = term57.
Proof. exact (MK_COMB (@lem1268947) (@lem1268946 k B)). Qed.
Lemma lem1268950 {A : Type'} (t : Prop) : (term58 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1268951 (t : Prop) : (term59 t) = t.
Proof. exact (@lem1268950 nat t). Qed.
Lemma lem1268952 : term57 = True.
Proof. exact (@lem1268951 True). Qed.
Lemma lem1268953 (k : nat) (B : nat) : (term44 k B) = True.
Proof. exact (TRANS (@lem1268948 k B) (@lem1268952)). Qed.
Lemma lem1268954 (k : nat) : (term46 k) = term56.
Proof. exact (fun_ext (fun B : nat => @lem1268953 k B)). Qed.
Lemma lem1268955 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1268956 (k : nat) : (term47 k) = term60.
Proof. exact (MK_COMB (@lem1268955) (@lem1268954 k)). Qed.
Lemma lem1268958 {A : Type'} (t : Prop) : (term61 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1268959 (t : Prop) : (term62 t) = t.
Proof. exact (@lem1268958 nat t). Qed.
Lemma lem1268960 : term60 = True.
Proof. exact (@lem1268959 True). Qed.
Lemma lem1268961 (k : nat) : (term47 k) = True.
Proof. exact (TRANS (@lem1268956 k) (@lem1268960)). Qed.
Lemma lem1268962 : term49 = term56.
Proof. exact (fun_ext (fun k : nat => @lem1268961 k)). Qed.
Lemma lem1268963 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1268964 : term51 = term57.
Proof. exact (MK_COMB (@lem1268963) (@lem1268962)). Qed.
Lemma lem1268966 {A : Type'} (t : Prop) : (term58 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1268967 (t : Prop) : (term59 t) = t.
Proof. exact (@lem1268966 nat t). Qed.
Lemma lem1268968 : term57 = True.
Proof. exact (@lem1268967 True). Qed.
Lemma lem1268969 : term51 = True.
Proof. exact (TRANS (@lem1268964) (@lem1268968)). Qed.
Lemma lem1268970 : True = term51.
Proof. exact (SYM (@lem1268969)). Qed.
Lemma lem1268971 : term51.
Proof. exact (EQ_MP (@lem1268970) (@lem0)). Qed.
Lemma lem1268972 : term50.
Proof. exact (EQ_MP (@lem1268865) (@lem1268971)). Qed.
