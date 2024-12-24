Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LEFT_SUB_DISTRIB_term_abbrevs.
Require Import ADD_SUB_spec.
Require Import ADD_SYM_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_CASES_spec.
Require Import LE_EXISTS_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import MULT_CLAUSES_spec.
Require Import SUB_EQ_0_spec.
Require Import thm0_spec.
Require Import thm1832_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem136771 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem136772 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem136773 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem136772 m) (@lem136771 m)). Qed.
Lemma lem136774 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem136773 m n). Qed.
Lemma lem136775 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem136788 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem136775 n m) (@lem136774 m n)). Qed.
Lemma lem136789 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem136790 (n : nat) (m : nat) : (term3 m n) = (term3 n m).
Proof. exact (MK_COMB (@lem136789) (@lem136788 n m)). Qed.
Lemma lem136791 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem136792 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem136790 n m) (@lem136791 n)). Qed.
Lemma lem136793 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem136794 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem136793) (@lem136792 m n)). Qed.
Lemma lem136795 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem136796 (n : nat) (m : nat) : ((term4 m n) = m) = ((term5 m n) = m).
Proof. exact (MK_COMB (@lem136794 m n) (@lem136795 m)). Qed.
Lemma lem136797 (m : nat) : (term8 m) = (term9 m).
Proof. exact (fun_ext (fun n : nat => @lem136796 n m)). Qed.
Lemma lem136798 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136799 (m : nat) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem136798) (@lem136797 m)). Qed.
Lemma lem136800 : term12 = term13.
Proof. exact (fun_ext (fun m : nat => @lem136799 m)). Qed.
Lemma lem136801 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136802 : term14 = term15.
Proof. exact (MK_COMB (@lem136801) (@lem136800)). Qed.
Lemma lem136803 : term15.
Proof. exact (EQ_MP (@lem136802) (@lem135886)). Qed.
Lemma lem136804 (m : nat) : term16 m.
Proof. exact (@lem136803 m). Qed.
Lemma lem136805 (m : nat) : (term16 m) = (term11 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem136806 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem136805 m) (@lem136804 m)). Qed.
Lemma lem136807 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem136806 m n). Qed.
Lemma lem136808 (n : nat) (m : nat) : (term17 m n) = ((term5 m n) = m).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem136810 (m : nat) : term18 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem136811 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem136812 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem136811 m) (@lem136810 m)). Qed.
Lemma lem136813 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem136812 m n). Qed.
Lemma lem136814 (n : nat) (m : nat) : (term20 m n) = (term21 n m).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem136815 (n : nat) (m : nat) : term21 n m.
Proof. exact (EQ_MP (@lem136814 n m) (@lem136813 m n)). Qed.
Lemma lem136816 (n : nat) (m : nat) (p : nat) : term22 n m p.
Proof. exact (@lem136815 n m p). Qed.
Lemma lem136817 (n : nat) (m : nat) (p : nat) : (term22 n m p) = ((term23 m n p) = (term24 n m p)).
Proof. exact (eq_refl (term22 n m p)). Qed.
Lemma lem136819 (m : nat) : term25 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem136820 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem136821 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem136820 m) (@lem136819 m)). Qed.
Lemma lem136822 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem136821 m n). Qed.
Lemma lem136823 (n : nat) (m : nat) : (term27 m n) = ((Peano.le m n) = (term28 n m)).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem136825 (n : nat) : term29 n.
Proof. exact (@lem96155 n). Qed.
Lemma lem136826 (n : nat) : (term29 n) = (term30 n).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem136827 (n : nat) : term30 n.
Proof. exact (EQ_MP (@lem136826 n) (@lem136825 n)). Qed.
Lemma lem136828 (n : nat) (p : nat) : term31 n p.
Proof. exact (@lem136827 n p). Qed.
Lemma lem136829 (p : nat) (n : nat) : (term31 n p) = (term32 p n).
Proof. exact (eq_refl (term31 n p)). Qed.
Lemma lem136830 (p : nat) (n : nat) : term32 p n.
Proof. exact (EQ_MP (@lem136829 p n) (@lem136828 n p)). Qed.
Lemma lem136831 (n : nat) (p : nat) (h1 : Peano.le n p) : Peano.le n p.
Proof. exact (h1). Qed.
Lemma lem136832 (p : nat) (n : nat) (h1 : Peano.le p n) : Peano.le p n.
Proof. exact (h1). Qed.
Lemma lem136833 (n : nat) (m : nat) (p : nat) (h1 : (term33 m n p) = (term34 n m p)) : (term33 m n p) = (term34 n m p).
Proof. exact (h1). Qed.
Lemma lem136834 (n : nat) (m : nat) (p : nat) (h1 : (term33 m n p) = (term34 n m p)) : (term34 n m p) = (term33 m n p).
Proof. exact (SYM (@lem136833 n m p h1)). Qed.
Lemma lem136835 (m : nat) (n : nat) (p : nat) (h1 : (term34 n m p) = (term33 m n p)) : (term34 n m p) = (term33 m n p).
Proof. exact (h1). Qed.
Lemma lem136836 (m : nat) (n : nat) (p : nat) (h1 : (term34 n m p) = (term33 m n p)) : (term33 m n p) = (term34 n m p).
Proof. exact (SYM (@lem136835 m n p h1)). Qed.
Lemma lem136837 (m : nat) (n : nat) (p : nat) : ((term33 m n p) = (term34 n m p)) = ((term34 n m p) = (term33 m n p)).
Proof. exact (prop_ext (fun h1 : (term33 m n p) = (term34 n m p) => @lem136834 n m p h1) (fun h1 : (term34 n m p) = (term33 m n p) => @lem136836 m n p h1)). Qed.
Lemma lem136838 (n : nat) (m : nat) (p : nat) : ((term34 n m p) = (term33 m n p)) = ((term33 m n p) = (term34 n m p)).
Proof. exact (SYM (@lem136837 m n p)). Qed.
Lemma lem136841 (m : nat) (n : nat) (h1 : ((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n)) : ((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n).
Proof. exact (h1). Qed.
Lemma lem136842 (m : nat) (n : nat) (h1 : ((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n)) : (Peano.le m n) = ((Nat.sub m n) = (NUMERAL 0)).
Proof. exact (SYM (@lem136841 m n h1)). Qed.
Lemma lem136843 (m : nat) (n : nat) (h1 : (Peano.le m n) = ((Nat.sub m n) = (NUMERAL 0))) : (Peano.le m n) = ((Nat.sub m n) = (NUMERAL 0)).
Proof. exact (h1). Qed.
Lemma lem136844 (m : nat) (n : nat) (h1 : (Peano.le m n) = ((Nat.sub m n) = (NUMERAL 0))) : ((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n).
Proof. exact (SYM (@lem136843 m n h1)). Qed.
Lemma lem136845 (m : nat) (n : nat) : (((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n)) = ((Peano.le m n) = ((Nat.sub m n) = (NUMERAL 0))).
Proof. exact (prop_ext (fun h1 : ((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n) => @lem136842 m n h1) (fun h1 : (Peano.le m n) = ((Nat.sub m n) = (NUMERAL 0)) => @lem136844 m n h1)). Qed.
Lemma lem136846 (m : nat) : (term35 m) = (term36 m).
Proof. exact (fun_ext (fun n : nat => @lem136845 m n)). Qed.
Lemma lem136847 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136848 (m : nat) : (term37 m) = (term38 m).
Proof. exact (MK_COMB (@lem136847) (@lem136846 m)). Qed.
Lemma lem136849 : term39 = term40.
Proof. exact (fun_ext (fun m : nat => @lem136848 m)). Qed.
Lemma lem136850 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136851 : term41 = term42.
Proof. exact (MK_COMB (@lem136850) (@lem136849)). Qed.
Lemma lem136852 : term42.
Proof. exact (EQ_MP (@lem136851) (@lem136259)). Qed.
Lemma lem136853 (m : nat) : term43 m.
Proof. exact (@lem136852 m). Qed.
Lemma lem136854 (m : nat) : (term43 m) = (term38 m).
Proof. exact (eq_refl (term43 m)). Qed.
Lemma lem136855 (m : nat) : term38 m.
Proof. exact (EQ_MP (@lem136854 m) (@lem136853 m)). Qed.
Lemma lem136856 (m : nat) (n : nat) : term44 m n.
Proof. exact (@lem136855 m n). Qed.
Lemma lem136857 (m : nat) (n : nat) : (term44 m n) = ((Peano.le m n) = ((Nat.sub m n) = (NUMERAL 0))).
Proof. exact (eq_refl (term44 m n)). Qed.
Lemma lem136860 (m : nat) (n : nat) : (Peano.le m n) = ((Nat.sub m n) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem136857 m n) (@lem136856 m n)). Qed.
Lemma lem136861 (n : nat) (p : nat) : (Peano.le n p) = ((Nat.sub n p) = (NUMERAL 0)).
Proof. exact (@lem136860 n p). Qed.
Lemma lem136868 (n : nat) (p : nat) (h1 : Peano.le n p) : (Nat.sub n p) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem136861 n p) (@lem136831 n p h1)). Qed.
Lemma lem136869 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem136870 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : (term33 m n p) = (term45 m).
Proof. exact (MK_COMB (@lem136869 m) (@lem136868 n p h1)). Qed.
Lemma lem136871 (n : nat) (m : nat) (p : nat) : (term46 n m p) = (term46 n m p).
Proof. exact (eq_refl (term46 n m p)). Qed.
Lemma lem136872 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : ((term34 n m p) = (term33 m n p)) = ((term34 n m p) = (term45 m)).
Proof. exact (MK_COMB (@lem136871 n m p) (@lem136870 m n p h1)). Qed.
Lemma lem136875 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : ((term34 n m p) = (term45 m)) = ((term34 n m p) = (term33 m n p)).
Proof. exact (SYM (@lem136872 m n p h1)). Qed.
Lemma lem136876 (m : nat) : term47 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem136877 (m : nat) : (term47 m) = (term48 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem136878 (m : nat) : term48 m.
Proof. exact (EQ_MP (@lem136877 m) (@lem136876 m)). Qed.
Lemma lem136879 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem136878 m n). Qed.
Lemma lem136880 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem136881 (m : nat) (n : nat) : term50 m n.
Proof. exact (EQ_MP (@lem136880 m n) (@lem136879 m n)). Qed.
Lemma lem136882 (m : nat) (n : nat) (p : nat) : term51 m n p.
Proof. exact (@lem136881 m n p). Qed.
Lemma lem136883 (m : nat) (n : nat) (p : nat) : (term51 m n p) = ((term52 n m p) = (term53 m n p)).
Proof. exact (eq_refl (term51 m n p)). Qed.
Lemma lem136885 (m : nat) : term54 m.
Proof. exact (@lem136259 m). Qed.
Lemma lem136886 (m : nat) : (term54 m) = (term37 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem136887 (m : nat) : term37 m.
Proof. exact (EQ_MP (@lem136886 m) (@lem136885 m)). Qed.
Lemma lem136888 (m : nat) (n : nat) : term55 m n.
Proof. exact (@lem136887 m n). Qed.
Lemma lem136889 (m : nat) (n : nat) : (term55 m n) = (((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n)).
Proof. exact (eq_refl (term55 m n)). Qed.
Lemma lem136891 : term56.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem136917 : term57.
Proof. exact (proj1 (@lem136891)). Qed.
Lemma lem136918 (m : nat) : term58 m.
Proof. exact (@lem136917 m). Qed.
Lemma lem136919 (m : nat) : (term58 m) = ((term45 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term58 m)). Qed.
Lemma lem136925 (n : nat) (p : nat) : (Peano.le n p) = ((Peano.le n p) = True).
Proof. exact (@lem7 (Peano.le n p)). Qed.
Lemma lem136930 (m : nat) : (term45 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem136919 m) (@lem136918 m)). Qed.
Lemma lem136931 (n : nat) (m : nat) (p : nat) : (term46 n m p) = (term46 n m p).
Proof. exact (eq_refl (term46 n m p)). Qed.
Lemma lem136932 (n : nat) (m : nat) (p : nat) : ((term34 n m p) = (term45 m)) = ((term34 n m p) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem136931 n m p) (@lem136930 m)). Qed.
Lemma lem136934 (m : nat) (n : nat) : ((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n).
Proof. exact (EQ_MP (@lem136889 m n) (@lem136888 m n)). Qed.
Lemma lem136935 (n : nat) (m : nat) (p : nat) : ((term34 n m p) = (NUMERAL 0)) = (term52 n m p).
Proof. exact (@lem136934 (Nat.mul m n) (Nat.mul m p)). Qed.
Lemma lem136937 (m : nat) (n : nat) (p : nat) : (term52 n m p) = (term53 m n p).
Proof. exact (EQ_MP (@lem136883 m n p) (@lem136882 m n p)). Qed.
Lemma lem136943 (n : nat) (p : nat) (h1 : Peano.le n p) : (Peano.le n p) = True.
Proof. exact (EQ_MP (@lem136925 n p) (@lem136831 n p h1)). Qed.
Lemma lem136944 (m : nat) : (term59 m) = (term59 m).
Proof. exact (eq_refl (term59 m)). Qed.
Lemma lem136945 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : (term53 m n p) = (term60 m).
Proof. exact (MK_COMB (@lem136944 m) (@lem136943 n p h1)). Qed.
Lemma lem136947 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem136948 (m : nat) : (term60 m) = True.
Proof. exact (@lem136947 (m = (NUMERAL 0))). Qed.
Lemma lem136949 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : (term53 m n p) = True.
Proof. exact (TRANS (@lem136945 m n p h1) (@lem136948 m)). Qed.
Lemma lem136950 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : (term52 n m p) = True.
Proof. exact (TRANS (@lem136937 m n p) (@lem136949 m n p h1)). Qed.
Lemma lem136951 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : ((term34 n m p) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem136935 n m p) (@lem136950 m n p h1)). Qed.
Lemma lem136952 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : ((term34 n m p) = (term45 m)) = True.
Proof. exact (TRANS (@lem136932 n m p) (@lem136951 m n p h1)). Qed.
Lemma lem136953 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : True = ((term34 n m p) = (term45 m)).
Proof. exact (SYM (@lem136952 m n p h1)). Qed.
Lemma lem136954 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : (term34 n m p) = (term45 m).
Proof. exact (EQ_MP (@lem136953 m n p h1) (@lem0)). Qed.
Lemma lem136955 (m : nat) (n : nat) (p : nat) (h1 : Peano.le n p) : (term34 n m p) = (term33 m n p).
Proof. exact (EQ_MP (@lem136875 m n p h1) (@lem136954 m n p h1)). Qed.
Lemma lem136957 (n : nat) (m : nat) : (Peano.le m n) = (term28 n m).
Proof. exact (EQ_MP (@lem136823 n m) (@lem136822 m n)). Qed.
Lemma lem136958 (n : nat) (p : nat) : (Peano.le p n) = (term28 n p).
Proof. exact (@lem136957 n p). Qed.
Lemma lem136965 (p : nat) (n : nat) (h1 : Peano.le p n) : term28 n p.
Proof. exact (EQ_MP (@lem136958 n p) (@lem136832 p n h1)). Qed.
Lemma lem136966 (n : nat) (p : nat) (d : nat) (h1 : n = (Nat.add p d)) : n = (Nat.add p d).
Proof. exact (h1). Qed.
Lemma lem136967 (m : nat) (p : nat) : (term61 m p) = (term61 m p).
Proof. exact (eq_refl (term61 m p)). Qed.
Lemma lem136968 (m : nat) (n : nat) (p : nat) (d : nat) (h1 : n = (Nat.add p d)) : (term62 m p n) = (term63 m p d).
Proof. exact (MK_COMB (@lem136967 m p) (@lem136966 n p d h1)). Qed.
Lemma lem136969 (m : nat) (d : nat) (p : nat) : (term63 m p d) = ((term64 d m p) = (term65 m d p)).
Proof. exact (eq_refl (term63 m p d)). Qed.
Lemma lem136970 (m : nat) (p : nat) (n : nat) : (term66 m p n) = (term66 m p n).
Proof. exact (eq_refl (term66 m p n)). Qed.
Lemma lem136971 (n : nat) (m : nat) (d : nat) (p : nat) : ((term62 m p n) = (term63 m p d)) = ((term62 m p n) = ((term64 d m p) = (term65 m d p))).
Proof. exact (MK_COMB (@lem136970 m p n) (@lem136969 m d p)). Qed.
Lemma lem136972 (m : nat) (n : nat) (p : nat) : (term62 m p n) = ((term34 n m p) = (term33 m n p)).
Proof. exact (eq_refl (term62 m p n)). Qed.
Lemma lem136973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem136974 (m : nat) (n : nat) (p : nat) : (term66 m p n) = (term67 m n p).
Proof. exact (MK_COMB (@lem136973) (@lem136972 m n p)). Qed.
Lemma lem136975 (m : nat) (d : nat) (p : nat) : ((term64 d m p) = (term65 m d p)) = ((term64 d m p) = (term65 m d p)).
Proof. exact (eq_refl ((term64 d m p) = (term65 m d p))). Qed.
Lemma lem136976 (n : nat) (m : nat) (d : nat) (p : nat) : ((term62 m p n) = ((term64 d m p) = (term65 m d p))) = (((term34 n m p) = (term33 m n p)) = ((term64 d m p) = (term65 m d p))).
Proof. exact (MK_COMB (@lem136974 m n p) (@lem136975 m d p)). Qed.
Lemma lem136977 (n : nat) (m : nat) (d : nat) (p : nat) : ((term62 m p n) = (term63 m p d)) = (((term34 n m p) = (term33 m n p)) = ((term64 d m p) = (term65 m d p))).
Proof. exact (TRANS (@lem136971 n m d p) (@lem136976 n m d p)). Qed.
Lemma lem136978 (m : nat) (n : nat) (p : nat) (d : nat) (h1 : n = (Nat.add p d)) : ((term34 n m p) = (term33 m n p)) = ((term64 d m p) = (term65 m d p)).
Proof. exact (EQ_MP (@lem136977 n m d p) (@lem136968 m n p d h1)). Qed.
Lemma lem136979 (m : nat) (n : nat) (p : nat) (d : nat) (h1 : n = (Nat.add p d)) : ((term64 d m p) = (term65 m d p)) = ((term34 n m p) = (term33 m n p)).
Proof. exact (SYM (@lem136978 m n p d h1)). Qed.
Lemma lem136983 (n : nat) (m : nat) (p : nat) : (term23 m n p) = (term24 n m p).
Proof. exact (EQ_MP (@lem136817 n m p) (@lem136816 n m p)). Qed.
Lemma lem136984 (p : nat) (m : nat) (d : nat) : (term23 m p d) = (term24 p m d).
Proof. exact (@lem136983 p m d). Qed.
Lemma lem136985 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem136986 (p : nat) (m : nat) (d : nat) : (term68 m p d) = (term69 p m d).
Proof. exact (MK_COMB (@lem136985) (@lem136984 p m d)). Qed.
Lemma lem136987 (m : nat) (p : nat) : (Nat.mul m p) = (Nat.mul m p).
Proof. exact (eq_refl (Nat.mul m p)). Qed.
Lemma lem136988 (d : nat) (m : nat) (p : nat) : (term64 d m p) = (term70 d m p).
Proof. exact (MK_COMB (@lem136986 p m d) (@lem136987 m p)). Qed.
Lemma lem136989 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem136990 (d : nat) (m : nat) (p : nat) : (term71 d m p) = (term72 d m p).
Proof. exact (MK_COMB (@lem136989) (@lem136988 d m p)). Qed.
Lemma lem136991 (m : nat) (d : nat) (p : nat) : (term65 m d p) = (term65 m d p).
Proof. exact (eq_refl (term65 m d p)). Qed.
Lemma lem136992 (m : nat) (d : nat) (p : nat) : ((term64 d m p) = (term65 m d p)) = ((term70 d m p) = (term65 m d p)).
Proof. exact (MK_COMB (@lem136990 d m p) (@lem136991 m d p)). Qed.
Lemma lem136995 (m : nat) (d : nat) (p : nat) : ((term70 d m p) = (term65 m d p)) = ((term64 d m p) = (term65 m d p)).
Proof. exact (SYM (@lem136992 m d p)). Qed.
Lemma lem136999 (n : nat) (m : nat) : (term5 m n) = m.
Proof. exact (EQ_MP (@lem136808 n m) (@lem136807 m n)). Qed.
Lemma lem137000 (p : nat) (m : nat) (d : nat) : (term70 d m p) = (Nat.mul m d).
Proof. exact (@lem136999 (Nat.mul m p) (Nat.mul m d)). Qed.
Lemma lem137001 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem137002 (p : nat) (m : nat) (d : nat) : (term72 d m p) = (term73 m d).
Proof. exact (MK_COMB (@lem137001) (@lem137000 p m d)). Qed.
Lemma lem137004 (n : nat) (m : nat) : (term5 m n) = m.
Proof. exact (EQ_MP (@lem136808 n m) (@lem136807 m n)). Qed.
Lemma lem137005 (p : nat) (d : nat) : (term5 d p) = d.
Proof. exact (@lem137004 p d). Qed.
Lemma lem137006 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem137007 (p : nat) (m : nat) (d : nat) : (term65 m d p) = (Nat.mul m d).
Proof. exact (MK_COMB (@lem137006 m) (@lem137005 p d)). Qed.
Lemma lem137008 (p : nat) (m : nat) (d : nat) : ((term70 d m p) = (term65 m d p)) = ((Nat.mul m d) = (Nat.mul m d)).
Proof. exact (MK_COMB (@lem137002 p m d) (@lem137007 p m d)). Qed.
Lemma lem137010 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem137011 (x : nat) : (x = x) = True.
Proof. exact (@lem137010 nat x). Qed.
Lemma lem137012 (m : nat) (d : nat) : ((Nat.mul m d) = (Nat.mul m d)) = True.
Proof. exact (@lem137011 (Nat.mul m d)). Qed.
Lemma lem137013 (m : nat) (d : nat) (p : nat) : ((term70 d m p) = (term65 m d p)) = True.
Proof. exact (TRANS (@lem137008 p m d) (@lem137012 m d)). Qed.
Lemma lem137014 (m : nat) (d : nat) (p : nat) : True = ((term70 d m p) = (term65 m d p)).
Proof. exact (SYM (@lem137013 m d p)). Qed.
Lemma lem137015 (m : nat) (d : nat) (p : nat) : (term70 d m p) = (term65 m d p).
Proof. exact (EQ_MP (@lem137014 m d p) (@lem0)). Qed.
Lemma lem137016 (m : nat) (d : nat) (p : nat) : (term64 d m p) = (term65 m d p).
Proof. exact (EQ_MP (@lem136995 m d p) (@lem137015 m d p)). Qed.
Lemma lem137017 (m : nat) (n : nat) (p : nat) (d : nat) (h1 : n = (Nat.add p d)) : (term34 n m p) = (term33 m n p).
Proof. exact (EQ_MP (@lem136979 m n p d h1) (@lem137016 m d p)). Qed.
Lemma lem137018 (m : nat) (p : nat) (n : nat) (h1 : Peano.le p n) : (term34 n m p) = (term33 m n p).
Proof. exact (ex_elim (@lem136965 p n h1) (fun d : nat => fun h0 : term74 n p d => @lem137017 m n p d h0)). Qed.
Lemma lem137019 (m : nat) (n : nat) (p : nat) : (term34 n m p) = (term33 m n p).
Proof. exact (or_elim (@lem136830 p n) (fun h0 : Peano.le n p => @lem136955 m n p h0) (fun h0 : Peano.le p n => @lem137018 m p n h0)). Qed.
Lemma lem137020 (n : nat) (m : nat) (p : nat) : (term33 m n p) = (term34 n m p).
Proof. exact (EQ_MP (@lem136838 n m p) (@lem137019 m n p)). Qed.
Lemma lem137025 (n : nat) (m : nat) : term75 n m.
Proof. exact (fun p : nat => @lem137020 n m p). Qed.
Lemma lem137030 (m : nat) : term76 m.
Proof. exact (fun n : nat => @lem137025 n m). Qed.
Lemma lem137035 : term77.
Proof. exact (fun m : nat => @lem137030 m). Qed.
