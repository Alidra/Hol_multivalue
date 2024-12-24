Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADD_ASSOC_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem77777 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem77778 : term1.
Proof. exact (@lem77777 term2). Qed.
Lemma lem77779 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem77780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem77781 : term5 = term6.
Proof. exact (MK_COMB (@lem77780) (@lem77779)). Qed.
Lemma lem77782 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem77783 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem77784 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem77783) (@lem77782 m)). Qed.
Lemma lem77785 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem77786 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem77784 m) (@lem77785 m)). Qed.
Lemma lem77787 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem77786 m)). Qed.
Lemma lem77788 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77789 : term17 = term18.
Proof. exact (MK_COMB (@lem77788) (@lem77787)). Qed.
Lemma lem77790 : term19 = term20.
Proof. exact (MK_COMB (@lem77781) (@lem77789)). Qed.
Lemma lem77791 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem77792 : term21 = term22.
Proof. exact (MK_COMB (@lem77791) (@lem77790)). Qed.
Lemma lem77793 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem77794 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem77793 m)). Qed.
Lemma lem77795 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77796 : term24 = term25.
Proof. exact (MK_COMB (@lem77795) (@lem77794)). Qed.
Lemma lem77797 : term1 = term26.
Proof. exact (MK_COMB (@lem77792) (@lem77796)). Qed.
Lemma lem77798 : term26.
Proof. exact (EQ_MP (@lem77797) (@lem77778)). Qed.
Lemma lem77799 (m : nat) (h1 : term8 m) : term8 m.
Proof. exact (h1). Qed.
Lemma lem77820 : term27.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem77821 (n : nat) : term28 n.
Proof. exact (@lem77820 n). Qed.
Lemma lem77822 (n : nat) : (term28 n) = ((term29 n) = n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem77835 (n : nat) : (term29 n) = n.
Proof. exact (EQ_MP (@lem77822 n) (@lem77821 n)). Qed.
Lemma lem77836 (n : nat) (p : nat) : (term30 n p) = (Nat.add n p).
Proof. exact (@lem77835 (Nat.add n p)). Qed.
Lemma lem77837 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem77838 (n : nat) (p : nat) : (term31 n p) = (term32 n p).
Proof. exact (MK_COMB (@lem77837) (@lem77836 n p)). Qed.
Lemma lem77840 (n : nat) : (term29 n) = n.
Proof. exact (EQ_MP (@lem77822 n) (@lem77821 n)). Qed.
Lemma lem77841 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem77842 (n : nat) : (term33 n) = (Nat.add n).
Proof. exact (MK_COMB (@lem77841) (@lem77840 n)). Qed.
Lemma lem77843 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem77844 (n : nat) (p : nat) : (term34 n p) = (Nat.add n p).
Proof. exact (MK_COMB (@lem77842 n) (@lem77843 p)). Qed.
Lemma lem77845 (n : nat) (p : nat) : ((term30 n p) = (term34 n p)) = ((Nat.add n p) = (Nat.add n p)).
Proof. exact (MK_COMB (@lem77838 n p) (@lem77844 n p)). Qed.
Lemma lem77847 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem77848 (x : nat) : (x = x) = True.
Proof. exact (@lem77847 nat x). Qed.
Lemma lem77849 (n : nat) (p : nat) : ((Nat.add n p) = (Nat.add n p)) = True.
Proof. exact (@lem77848 (Nat.add n p)). Qed.
Lemma lem77850 (n : nat) (p : nat) : ((term30 n p) = (term34 n p)) = True.
Proof. exact (TRANS (@lem77845 n p) (@lem77849 n p)). Qed.
Lemma lem77851 (n : nat) : (term35 n) = term36.
Proof. exact (fun_ext (fun p : nat => @lem77850 n p)). Qed.
Lemma lem77852 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77853 (n : nat) : (term37 n) = term38.
Proof. exact (MK_COMB (@lem77852) (@lem77851 n)). Qed.
Lemma lem77855 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem77856 (t : Prop) : (term40 t) = t.
Proof. exact (@lem77855 nat t). Qed.
Lemma lem77857 : term38 = True.
Proof. exact (@lem77856 True). Qed.
Lemma lem77858 (n : nat) : (term37 n) = True.
Proof. exact (TRANS (@lem77853 n) (@lem77857)). Qed.
Lemma lem77859 : term41 = term36.
Proof. exact (fun_ext (fun n : nat => @lem77858 n)). Qed.
Lemma lem77860 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77861 : term4 = term38.
Proof. exact (MK_COMB (@lem77860) (@lem77859)). Qed.
Lemma lem77863 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem77864 (t : Prop) : (term40 t) = t.
Proof. exact (@lem77863 nat t). Qed.
Lemma lem77865 : term38 = True.
Proof. exact (@lem77864 True). Qed.
Lemma lem77866 : term4 = True.
Proof. exact (TRANS (@lem77861) (@lem77865)). Qed.
Lemma lem77867 : True = term4.
Proof. exact (SYM (@lem77866)). Qed.
Lemma lem77868 : term4.
Proof. exact (EQ_MP (@lem77867) (@lem0)). Qed.
Lemma lem77869 : term42.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem77870 : term43.
Proof. exact (proj2 (@lem77869)). Qed.
Lemma lem77878 : term44.
Proof. exact (proj1 (@lem77870)). Qed.
Lemma lem77879 (m : nat) : term45 m.
Proof. exact (@lem77878 m). Qed.
Lemma lem77880 (m : nat) : (term45 m) = (term46 m).
Proof. exact (eq_refl (term45 m)). Qed.
Lemma lem77881 (m : nat) : term46 m.
Proof. exact (EQ_MP (@lem77880 m) (@lem77879 m)). Qed.
Lemma lem77882 (m : nat) (n : nat) : term47 m n.
Proof. exact (@lem77881 m n). Qed.
Lemma lem77883 (m : nat) (n : nat) : (term47 m n) = ((term48 m n) = (term49 m n)).
Proof. exact (eq_refl (term47 m n)). Qed.
Lemma lem77893 (n : nat) (m : nat) (h1 : term8 m) : term50 m n.
Proof. exact (@lem77799 m h1 n). Qed.
Lemma lem77894 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem77895 (n : nat) (m : nat) (h1 : term8 m) : term51 m n.
Proof. exact (EQ_MP (@lem77894 m n) (@lem77893 n m h1)). Qed.
Lemma lem77896 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : term52 m n p.
Proof. exact (@lem77895 n m h1 p). Qed.
Lemma lem77897 (m : nat) (n : nat) (p : nat) : (term52 m n p) = ((term53 m n p) = (term54 m n p)).
Proof. exact (eq_refl (term52 m n p)). Qed.
Lemma lem77910 (m : nat) (n : nat) : (term48 m n) = (term49 m n).
Proof. exact (EQ_MP (@lem77883 m n) (@lem77882 m n)). Qed.
Lemma lem77911 (m : nat) (n : nat) (p : nat) : (term55 m n p) = (term56 m n p).
Proof. exact (@lem77910 m (Nat.add n p)). Qed.
Lemma lem77913 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (term53 m n p) = (term54 m n p).
Proof. exact (EQ_MP (@lem77897 m n p) (@lem77896 n p m h1)). Qed.
Lemma lem77914 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem77915 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (term56 m n p) = (term57 m n p).
Proof. exact (MK_COMB (@lem77914) (@lem77913 n p m h1)). Qed.
Lemma lem77916 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (term55 m n p) = (term57 m n p).
Proof. exact (TRANS (@lem77911 m n p) (@lem77915 n p m h1)). Qed.
Lemma lem77917 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem77918 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (term58 m n p) = (term59 m n p).
Proof. exact (MK_COMB (@lem77917) (@lem77916 n p m h1)). Qed.
Lemma lem77920 (m : nat) (n : nat) : (term48 m n) = (term49 m n).
Proof. exact (EQ_MP (@lem77883 m n) (@lem77882 m n)). Qed.
Lemma lem77921 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem77922 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (MK_COMB (@lem77921) (@lem77920 m n)). Qed.
Lemma lem77923 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem77924 (m : nat) (n : nat) (p : nat) : (term62 m n p) = (term63 m n p).
Proof. exact (MK_COMB (@lem77922 m n) (@lem77923 p)). Qed.
Lemma lem77926 (m : nat) (n : nat) : (term48 m n) = (term49 m n).
Proof. exact (EQ_MP (@lem77883 m n) (@lem77882 m n)). Qed.
Lemma lem77927 (m : nat) (n : nat) (p : nat) : (term63 m n p) = (term57 m n p).
Proof. exact (@lem77926 (Nat.add m n) p). Qed.
Lemma lem77928 (m : nat) (n : nat) (p : nat) : (term62 m n p) = (term57 m n p).
Proof. exact (TRANS (@lem77924 m n p) (@lem77927 m n p)). Qed.
Lemma lem77929 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : ((term55 m n p) = (term62 m n p)) = ((term57 m n p) = (term57 m n p)).
Proof. exact (MK_COMB (@lem77918 n p m h1) (@lem77928 m n p)). Qed.
Lemma lem77931 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem77932 (x : nat) : (x = x) = True.
Proof. exact (@lem77931 nat x). Qed.
Lemma lem77933 (m : nat) (n : nat) (p : nat) : ((term57 m n p) = (term57 m n p)) = True.
Proof. exact (@lem77932 (term57 m n p)). Qed.
Lemma lem77934 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : ((term55 m n p) = (term62 m n p)) = True.
Proof. exact (TRANS (@lem77929 n p m h1) (@lem77933 m n p)). Qed.
Lemma lem77935 (n : nat) (m : nat) (h1 : term8 m) : (term64 m n) = term36.
Proof. exact (fun_ext (fun p : nat => @lem77934 n p m h1)). Qed.
Lemma lem77936 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77937 (n : nat) (m : nat) (h1 : term8 m) : (term65 m n) = term38.
Proof. exact (MK_COMB (@lem77936) (@lem77935 n m h1)). Qed.
Lemma lem77939 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem77940 (t : Prop) : (term40 t) = t.
Proof. exact (@lem77939 nat t). Qed.
Lemma lem77941 : term38 = True.
Proof. exact (@lem77940 True). Qed.
Lemma lem77942 (n : nat) (m : nat) (h1 : term8 m) : (term65 m n) = True.
Proof. exact (TRANS (@lem77937 n m h1) (@lem77941)). Qed.
Lemma lem77943 (m : nat) (h1 : term8 m) : (term66 m) = term36.
Proof. exact (fun_ext (fun n : nat => @lem77942 n m h1)). Qed.
Lemma lem77944 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77945 (m : nat) (h1 : term8 m) : (term12 m) = term38.
Proof. exact (MK_COMB (@lem77944) (@lem77943 m h1)). Qed.
Lemma lem77947 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem77948 (t : Prop) : (term40 t) = t.
Proof. exact (@lem77947 nat t). Qed.
Lemma lem77949 : term38 = True.
Proof. exact (@lem77948 True). Qed.
Lemma lem77950 (m : nat) (h1 : term8 m) : (term12 m) = True.
Proof. exact (TRANS (@lem77945 m h1) (@lem77949)). Qed.
Lemma lem77951 (m : nat) (h1 : term8 m) : True = (term12 m).
Proof. exact (SYM (@lem77950 m h1)). Qed.
Lemma lem77952 (m : nat) (h1 : term8 m) : term12 m.
Proof. exact (EQ_MP (@lem77951 m h1) (@lem0)). Qed.
Lemma lem77953 (m : nat) : term14 m.
Proof. exact (fun h0 : term8 m => @lem77952 m h0). Qed.
Lemma lem77958 : term18.
Proof. exact (fun m : nat => @lem77953 m). Qed.
Lemma lem77959 : term20.
Proof. exact (conj (@lem77868) (@lem77958)). Qed.
Lemma lem77960 : term25.
Proof. exact (@lem77798 (@lem77959)). Qed.
