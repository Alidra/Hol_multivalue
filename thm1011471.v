Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1011471_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import DISJ_ACI_spec.
Require Import LE_ADD_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm1856_spec.
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
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm75543_spec.
Lemma lem1010776 (n : nat) : term0 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem1010777 (n : nat) : (term0 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1010779 (m : nat) (n : nat) (p : nat) (h1 : (Nat.add m n) = p) : (Nat.add m n) = p.
Proof. exact (h1). Qed.
Lemma lem1010780 (m : nat) (n : nat) (p : nat) (h1 : (Nat.add m n) = p) : p = (Nat.add m n).
Proof. exact (SYM (@lem1010779 m n p h1)). Qed.
Lemma lem1010781 (n : nat) : (term1 n) = (term1 n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem1010782 (m : nat) (n : nat) (p : nat) (h1 : (Nat.add m n) = p) : (term2 n p) = (term3 m n).
Proof. exact (MK_COMB (@lem1010781 n) (@lem1010780 m n p h1)). Qed.
Lemma lem1010783 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = True).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1010784 (n : nat) (p : nat) : (term5 n p) = (term5 n p).
Proof. exact (eq_refl (term5 n p)). Qed.
Lemma lem1010785 (p : nat) (m : nat) (n : nat) : ((term2 n p) = (term3 m n)) = ((term2 n p) = ((term4 m n) = True)).
Proof. exact (MK_COMB (@lem1010784 n p) (@lem1010783 m n)). Qed.
Lemma lem1010786 (n : nat) (p : nat) : (term2 n p) = ((term6 n p) = True).
Proof. exact (eq_refl (term2 n p)). Qed.
Lemma lem1010787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1010788 (n : nat) (p : nat) : (term5 n p) = (term7 n p).
Proof. exact (MK_COMB (@lem1010787) (@lem1010786 n p)). Qed.
Lemma lem1010789 (m : nat) (n : nat) : ((term4 m n) = True) = ((term4 m n) = True).
Proof. exact (eq_refl ((term4 m n) = True)). Qed.
Lemma lem1010790 (p : nat) (m : nat) (n : nat) : ((term2 n p) = ((term4 m n) = True)) = (((term6 n p) = True) = ((term4 m n) = True)).
Proof. exact (MK_COMB (@lem1010788 n p) (@lem1010789 m n)). Qed.
Lemma lem1010791 (p : nat) (m : nat) (n : nat) : ((term2 n p) = (term3 m n)) = (((term6 n p) = True) = ((term4 m n) = True)).
Proof. exact (TRANS (@lem1010785 p m n) (@lem1010790 p m n)). Qed.
Lemma lem1010792 (m : nat) (n : nat) (p : nat) (h1 : (Nat.add m n) = p) : ((term6 n p) = True) = ((term4 m n) = True).
Proof. exact (EQ_MP (@lem1010791 p m n) (@lem1010782 m n p h1)). Qed.
Lemma lem1010793 (m : nat) (n : nat) (p : nat) (h1 : (Nat.add m n) = p) : ((term4 m n) = True) = ((term6 n p) = True).
Proof. exact (SYM (@lem1010792 m n p h1)). Qed.
Lemma lem1010795 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem1010796 (m : nat) (n : nat) : ((term4 m n) = True) = (term4 m n).
Proof. exact (@lem1010795 (term4 m n)). Qed.
Lemma lem1010798 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1010777 n) (@lem1010776 n)). Qed.
Lemma lem1010799 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1010800 (n : nat) : (term8 n) = (Peano.le n).
Proof. exact (MK_COMB (@lem1010799) (@lem1010798 n)). Qed.
Lemma lem1010802 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1010777 n) (@lem1010776 n)). Qed.
Lemma lem1010803 (m : nat) (n : nat) : (term9 m n) = (Nat.add m n).
Proof. exact (@lem1010802 (Nat.add m n)). Qed.
Lemma lem1010804 (m : nat) (n : nat) : (term4 m n) = (term10 m n).
Proof. exact (MK_COMB (@lem1010800 n) (@lem1010803 m n)). Qed.
Lemma lem1010805 (m : nat) (n : nat) : ((term4 m n) = True) = (term10 m n).
Proof. exact (TRANS (@lem1010796 m n) (@lem1010804 m n)). Qed.
Lemma lem1010806 (m : nat) (n : nat) : (term10 m n) = ((term4 m n) = True).
Proof. exact (SYM (@lem1010805 m n)). Qed.
Lemma lem1010808 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1010809 (m : nat) (n : nat) : (term10 m n) = (term12 m n).
Proof. exact (@lem1010808 (term10 m n)). Qed.
Lemma lem1010810 (m : nat) (n : nat) : (term12 m n) = (term10 m n).
Proof. exact (SYM (@lem1010809 m n)). Qed.
Lemma lem1010811 (m : nat) (n : nat) (h1 : term13 m n) : term13 m n.
Proof. exact (h1). Qed.
Lemma lem1010814 (m : nat) (n : nat) (h1 : term14 m n) : term14 m n.
Proof. exact (h1). Qed.
Lemma lem1010815 (m : nat) (n : nat) : term15 m n.
Proof. exact (fun h0 : term14 m n => @lem1010814 m n h0). Qed.
Lemma lem1010816 (m : nat) (n : nat) (h1 : term15 m n) : term15 m n.
Proof. exact (h1). Qed.
Lemma lem1010817 (m : nat) (n : nat) (h1 : term14 m n) : term14 m n.
Proof. exact (h1). Qed.
Lemma lem1010818 (m : nat) (n : nat) (h1 : term14 m n) (h2 : term15 m n) : term14 m n.
Proof. exact (@lem1010816 m n h2 (@lem1010817 m n h1)). Qed.
Lemma lem1010819 (m : nat) (n : nat) (h1 : term14 m n) : term16 m n.
Proof. exact (fun h0 : term15 m n => @lem1010818 m n h1 h0). Qed.
Lemma lem1010820 (m : nat) (n : nat) (h1 : term15 m n) : term15 m n.
Proof. exact (h1). Qed.
Lemma lem1010821 (m : nat) (n : nat) (h1 : term14 m n) (h2 : term15 m n) : term14 m n.
Proof. exact (@lem1010819 m n h1 (@lem1010820 m n h2)). Qed.
Lemma lem1010822 (m : nat) (n : nat) (h1 : term15 m n) : term15 m n.
Proof. exact (fun h0 : term14 m n => @lem1010821 m n h0 h1). Qed.
Lemma lem1010823 (m : nat) (n : nat) : term17 m n.
Proof. exact (fun h0 : term15 m n => @lem1010822 m n h0). Qed.
Lemma lem1010826 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem1010823 m n (@lem1010815 m n)). Qed.
Lemma lem1010848 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1010849 : term18 = term19.
Proof. exact (@lem1010848 term20). Qed.
Lemma lem1010858 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1010859 : term22 = term23.
Proof. exact (MK_COMB (@lem1010858) (@lem1010849)). Qed.
Lemma lem1010862 (m : nat) (n : nat) : (term24 m n) = (term24 m n).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem1010863 (m : nat) (n : nat) : (term14 m n) = (term25 m n).
Proof. exact (MK_COMB (@lem1010862 m n) (@lem1010859)). Qed.
Lemma lem1010866 (n : nat) : (term26 n) = (term27 n).
Proof. exact (fun_ext (fun m : nat => @lem1010863 m n)). Qed.
Lemma lem1010867 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010868 (n : nat) : (term28 n) = (term29 n).
Proof. exact (MK_COMB (@lem1010867) (@lem1010866 n)). Qed.
Lemma lem1010873 : term30 = term31.
Proof. exact (fun_ext (fun n : nat => @lem1010868 n)). Qed.
Lemma lem1010874 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010883 : term32 = term33.
Proof. exact (MK_COMB (@lem1010874) (@lem1010873)). Qed.
Lemma lem1010884 (m : nat) (n : nat) : (term34 m n) = (term34 m n).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem1010885 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem1010884 m n)). Qed.
Lemma lem1010886 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010887 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem1010886) (@lem1010885 m)). Qed.
Lemma lem1010888 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem1010887 m)). Qed.
Lemma lem1010889 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010890 : term20 = term20.
Proof. exact (MK_COMB (@lem1010889) (@lem1010888)). Qed.
Lemma lem1010891 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1010892 : term19 = term19.
Proof. exact (MK_COMB (@lem1010891) (@lem1010890)). Qed.
Lemma lem1010893 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1010894 (m : nat) : (term38 m) = (term38 m).
Proof. exact (fun_ext (fun n : nat => @lem1010893 n m)). Qed.
Lemma lem1010895 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010896 (m : nat) : (term39 m) = (term39 m).
Proof. exact (MK_COMB (@lem1010895) (@lem1010894 m)). Qed.
Lemma lem1010897 : term40 = term40.
Proof. exact (fun_ext (fun m : nat => @lem1010896 m)). Qed.
Lemma lem1010898 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010899 : term41 = term41.
Proof. exact (MK_COMB (@lem1010898) (@lem1010897)). Qed.
Lemma lem1010900 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1010901 : term21 = term21.
Proof. exact (MK_COMB (@lem1010900) (@lem1010899)). Qed.
Lemma lem1010902 : term23 = term23.
Proof. exact (MK_COMB (@lem1010901) (@lem1010892)). Qed.
Lemma lem1010907 (m : nat) (n : nat) : (term24 m n) = (term24 m n).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem1010908 (m : nat) (n : nat) : (term25 m n) = (term25 m n).
Proof. exact (MK_COMB (@lem1010907 m n) (@lem1010902)). Qed.
Lemma lem1010909 (n : nat) : (term27 n) = (term27 n).
Proof. exact (fun_ext (fun m : nat => @lem1010908 m n)). Qed.
Lemma lem1010910 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010911 (n : nat) : (term29 n) = (term29 n).
Proof. exact (MK_COMB (@lem1010910) (@lem1010909 n)). Qed.
Lemma lem1010912 : term31 = term31.
Proof. exact (fun_ext (fun n : nat => @lem1010911 n)). Qed.
Lemma lem1010913 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010914 : term33 = term33.
Proof. exact (MK_COMB (@lem1010913) (@lem1010912)). Qed.
Lemma lem1010957 : term32 = term33.
Proof. exact (TRANS (@lem1010883) (@lem1010914)). Qed.
Lemma lem1010958 : term33 = term32.
Proof. exact (SYM (@lem1010957)). Qed.
Lemma lem1010960 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem1010961 (h1 : term20) : term20.
Proof. exact (h1). Qed.
Lemma lem1010967 (m : nat) (n : nat) (h1 : term13 m n) : term13 m n.
Proof. exact (h1). Qed.
Lemma lem1010968 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1010969 (m : nat) : (term38 m) = (term38 m).
Proof. exact (fun_ext (fun n : nat => @lem1010968 n m)). Qed.
Lemma lem1010970 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010971 (m : nat) : (term39 m) = (term39 m).
Proof. exact (MK_COMB (@lem1010970) (@lem1010969 m)). Qed.
Lemma lem1010972 : term40 = term40.
Proof. exact (fun_ext (fun m : nat => @lem1010971 m)). Qed.
Lemma lem1010973 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010986 : term41 = term41.
Proof. exact (MK_COMB (@lem1010973) (@lem1010972)). Qed.
Lemma lem1010987 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem1010986) (@lem1010960 h1)). Qed.
Lemma lem1010988 (m : nat) (n : nat) : (term34 m n) = (term34 m n).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem1010989 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem1010988 m n)). Qed.
Lemma lem1010990 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010991 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem1010990) (@lem1010989 m)). Qed.
Lemma lem1010992 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem1010991 m)). Qed.
Lemma lem1010993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1011006 : term20 = term20.
Proof. exact (MK_COMB (@lem1010993) (@lem1010992)). Qed.
Lemma lem1011007 (h1 : term20) : term20.
Proof. exact (EQ_MP (@lem1011006) (@lem1010961 h1)). Qed.
Lemma lem1011019 (m : nat) (n : nat) (h1 : term13 m n) : term13 m n.
Proof. exact (h1). Qed.
Lemma lem1011032 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1011033 (m : nat) : (term38 m) = (term38 m).
Proof. exact (fun_ext (fun n : nat => @lem1011032 n m)). Qed.
Lemma lem1011034 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1011035 (m : nat) : (term39 m) = (term39 m).
Proof. exact (MK_COMB (@lem1011034) (@lem1011033 m)). Qed.
Lemma lem1011036 : term40 = term40.
Proof. exact (fun_ext (fun m : nat => @lem1011035 m)). Qed.
Lemma lem1011037 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1011038 : term41 = term41.
Proof. exact (MK_COMB (@lem1011037) (@lem1011036)). Qed.
Lemma lem1011039 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem1011038) (@lem1010987 h1)). Qed.
Lemma lem1011048 (m : nat) (n : nat) : (term34 m n) = (term34 m n).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem1011049 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem1011048 m n)). Qed.
Lemma lem1011050 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1011051 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem1011050) (@lem1011049 m)). Qed.
Lemma lem1011052 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem1011051 m)). Qed.
Lemma lem1011053 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1011054 : term20 = term20.
Proof. exact (MK_COMB (@lem1011053) (@lem1011052)). Qed.
Lemma lem1011055 (h1 : term20) : term20.
Proof. exact (EQ_MP (@lem1011054) (@lem1011007 h1)). Qed.
Lemma lem1011059 (m : nat) (n : nat) (h1 : term13 m n) : term13 m n.
Proof. exact (h1). Qed.
Lemma lem1011061 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1011062 (m : nat) : (term38 m) = (term38 m).
Proof. exact (fun_ext (fun n : nat => @lem1011061 n m)). Qed.
Lemma lem1011063 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1011064 (m : nat) : (term39 m) = (term39 m).
Proof. exact (MK_COMB (@lem1011063) (@lem1011062 m)). Qed.
Lemma lem1011065 : term40 = term40.
Proof. exact (fun_ext (fun m : nat => @lem1011064 m)). Qed.
Lemma lem1011066 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1011068 : term41 = term41.
Proof. exact (MK_COMB (@lem1011066) (@lem1011065)). Qed.
Lemma lem1011069 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem1011068) (@lem1011039 h1)). Qed.
Lemma lem1011071 (m : nat) (n : nat) : (term34 m n) = (term34 m n).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem1011072 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem1011071 m n)). Qed.
Lemma lem1011073 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1011074 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem1011073) (@lem1011072 m)). Qed.
Lemma lem1011075 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem1011074 m)). Qed.
Lemma lem1011076 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1011078 : term20 = term20.
Proof. exact (MK_COMB (@lem1011076) (@lem1011075)). Qed.
Lemma lem1011079 (h1 : term20) : term20.
Proof. exact (EQ_MP (@lem1011078) (@lem1011055 h1)). Qed.
Lemma lem1011080 (_16424 : nat) (h1 : term41) : term42 _16424.
Proof. exact (@lem1011069 h1 _16424). Qed.
Lemma lem1011081 (_16424 : nat) : (term42 _16424) = (term39 _16424).
Proof. exact (eq_refl (term42 _16424)). Qed.
Lemma lem1011082 (_16424 : nat) (h1 : term41) : term39 _16424.
Proof. exact (EQ_MP (@lem1011081 _16424) (@lem1011080 _16424 h1)). Qed.
Lemma lem1011083 (_16424 : nat) (_16425 : nat) (h1 : term41) : term43 _16424 _16425.
Proof. exact (@lem1011082 _16424 h1 _16425). Qed.
Lemma lem1011084 (_16425 : nat) (_16424 : nat) : (term43 _16424 _16425) = ((Nat.add _16424 _16425) = (Nat.add _16425 _16424)).
Proof. exact (eq_refl (term43 _16424 _16425)). Qed.
Lemma lem1011086 (_16426 : nat) (h1 : term20) : term44 _16426.
Proof. exact (@lem1011079 h1 _16426). Qed.
Lemma lem1011087 (_16426 : nat) : (term44 _16426) = (term36 _16426).
Proof. exact (eq_refl (term44 _16426)). Qed.
Lemma lem1011088 (_16426 : nat) (h1 : term20) : term36 _16426.
Proof. exact (EQ_MP (@lem1011087 _16426) (@lem1011086 _16426 h1)). Qed.
Lemma lem1011089 (_16426 : nat) (_16427 : nat) (h1 : term20) : term45 _16426 _16427.
Proof. exact (@lem1011088 _16426 h1 _16427). Qed.
Lemma lem1011090 (_16426 : nat) (_16427 : nat) : (term45 _16426 _16427) = (term34 _16426 _16427).
Proof. exact (eq_refl (term45 _16426 _16427)). Qed.
Lemma lem1011093 (m : nat) (n : nat) (h1 : term13 m n) : term13 m n.
Proof. exact (h1). Qed.
Lemma lem1011098 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1011099 (_16428 : nat) (_16430 : nat) (h1 : _16428 = _16430) : _16428 = _16430.
Proof. exact (h1). Qed.
Lemma lem1011100 (_16429 : nat) (_16431 : nat) (h1 : _16429 = _16431) : _16429 = _16431.
Proof. exact (h1). Qed.
Lemma lem1011101 (_16428 : nat) (_16430 : nat) (h1 : _16428 = _16430) : (Peano.le _16428) = (Peano.le _16430).
Proof. exact (MK_COMB (@lem1011098) (@lem1011099 _16428 _16430 h1)). Qed.
Lemma lem1011102 (_16428 : nat) (_16430 : nat) (_16429 : nat) (_16431 : nat) (h1 : _16428 = _16430) (h2 : _16429 = _16431) : (Peano.le _16428 _16429) = (Peano.le _16430 _16431).
Proof. exact (MK_COMB (@lem1011101 _16428 _16430 h1) (@lem1011100 _16429 _16431 h2)). Qed.
Lemma lem1011104 (b : Prop) (a : Prop) : term46 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1011105 (_16430 : nat) (_16431 : nat) (_16428 : nat) (_16429 : nat) : term47 _16430 _16431 _16428 _16429.
Proof. exact (@lem1011104 (Peano.le _16430 _16431) (Peano.le _16428 _16429)). Qed.
Lemma lem1011106 (_16428 : nat) (_16430 : nat) (_16429 : nat) (_16431 : nat) (h1 : _16428 = _16430) (h2 : _16429 = _16431) : term48 _16430 _16431 _16428 _16429.
Proof. exact (@lem1011105 _16430 _16431 _16428 _16429 (@lem1011102 _16428 _16430 _16429 _16431 h1 h2)). Qed.
Lemma lem1011107 (_16431 : nat) (_16429 : nat) (_16428 : nat) (_16430 : nat) (h1 : _16428 = _16430) : term49 _16430 _16431 _16428 _16429.
Proof. exact (fun h0 : _16429 = _16431 => @lem1011106 _16428 _16430 _16429 _16431 h1 h0). Qed.
Lemma lem1011109 (a : Prop) (b : Prop) : (a -> b) = (term50 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1011110 (_16430 : nat) (_16431 : nat) (_16428 : nat) (_16429 : nat) : (term49 _16430 _16431 _16428 _16429) = (term51 _16430 _16431 _16428 _16429).
Proof. exact (@lem1011109 (_16429 = _16431) (term48 _16430 _16431 _16428 _16429)). Qed.
Lemma lem1011111 (_16431 : nat) (_16429 : nat) (_16428 : nat) (_16430 : nat) (h1 : _16428 = _16430) : term51 _16430 _16431 _16428 _16429.
Proof. exact (EQ_MP (@lem1011110 _16430 _16431 _16428 _16429) (@lem1011107 _16431 _16429 _16428 _16430 h1)). Qed.
Lemma lem1011112 (_16430 : nat) (_16431 : nat) (_16428 : nat) (_16429 : nat) : term52 _16430 _16431 _16428 _16429.
Proof. exact (fun h0 : _16428 = _16430 => @lem1011111 _16431 _16429 _16428 _16430 h0). Qed.
Lemma lem1011114 (a : Prop) (b : Prop) : (a -> b) = (term50 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1011115 (_16430 : nat) (_16431 : nat) (_16428 : nat) (_16429 : nat) : (term52 _16430 _16431 _16428 _16429) = (term53 _16430 _16431 _16428 _16429).
Proof. exact (@lem1011114 (_16428 = _16430) (term51 _16430 _16431 _16428 _16429)). Qed.
Lemma lem1011116 (_16430 : nat) (_16431 : nat) (_16428 : nat) (_16429 : nat) : term53 _16430 _16431 _16428 _16429.
Proof. exact (EQ_MP (@lem1011115 _16430 _16431 _16428 _16429) (@lem1011112 _16430 _16431 _16428 _16429)). Qed.
Lemma lem1011135 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1011136 (n : nat) : n = n.
Proof. exact (@lem1011135 n). Qed.
Lemma lem1011137 (n : nat) : term54 n.
Proof. exact (fun h0 : term55 n => @lem1011136 n). Qed.
Lemma lem1011139 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1011140 (n : nat) : (term54 n) = (n = n).
Proof. exact (@lem1011139 (n = n)). Qed.
Lemma lem1011141 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem1011140 n) (@lem1011137 n)). Qed.
Lemma lem1011143 (_16425 : nat) (_16424 : nat) (h1 : term41) : (Nat.add _16424 _16425) = (Nat.add _16425 _16424).
Proof. exact (EQ_MP (@lem1011084 _16425 _16424) (@lem1011083 _16424 _16425 h1)). Qed.
Lemma lem1011144 (m : nat) (n : nat) (h1 : term41) : (Nat.add n m) = (Nat.add m n).
Proof. exact (@lem1011143 m n h1). Qed.
Lemma lem1011145 (m : nat) (n : nat) (h1 : term41) : term57 m n.
Proof. exact (fun h0 : term58 m n => @lem1011144 m n h1). Qed.
Lemma lem1011147 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1011148 (m : nat) (n : nat) : (term57 m n) = ((Nat.add n m) = (Nat.add m n)).
Proof. exact (@lem1011147 ((Nat.add n m) = (Nat.add m n))). Qed.
Lemma lem1011149 (m : nat) (n : nat) (h1 : term41) : (Nat.add n m) = (Nat.add m n).
Proof. exact (EQ_MP (@lem1011148 m n) (@lem1011145 m n h1)). Qed.
Lemma lem1011151 (_16426 : nat) (_16427 : nat) (h1 : term20) : term34 _16426 _16427.
Proof. exact (EQ_MP (@lem1011090 _16426 _16427) (@lem1011089 _16426 _16427 h1)). Qed.
Lemma lem1011152 (n : nat) (m : nat) (h1 : term20) : term34 n m.
Proof. exact (@lem1011151 n m h1). Qed.
Lemma lem1011153 (n : nat) (m : nat) (h1 : term20) : term59 n m.
Proof. exact (fun h0 : term60 n m => @lem1011152 n m h1). Qed.
Lemma lem1011155 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1011156 (n : nat) (m : nat) : (term59 n m) = (term34 n m).
Proof. exact (@lem1011155 (term34 n m)). Qed.
Lemma lem1011157 (n : nat) (m : nat) (h1 : term20) : term34 n m.
Proof. exact (EQ_MP (@lem1011156 n m) (@lem1011153 n m h1)). Qed.
Lemma lem1011175 (q : Prop) (p : Prop) (r : Prop) : (term61 p q r) = (term61 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1011176 (_16430 : nat) (_16431 : nat) (_16428 : nat) (_16429 : nat) : (term51 _16430 _16431 _16428 _16429) = (term62 _16430 _16431 _16428 _16429).
Proof. exact (@lem1011175 (Peano.le _16430 _16431) (term63 _16429 _16431) (term64 _16428 _16429)). Qed.
Lemma lem1011190 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1011191 (_16428 : nat) (_16429 : nat) (_16431 : nat) : (term65 _16431 _16428 _16429) = (term66 _16428 _16429 _16431).
Proof. exact (@lem1011190 (term64 _16428 _16429) (term63 _16429 _16431)). Qed.
Lemma lem1011199 (_16430 : nat) (_16431 : nat) : (term67 _16430 _16431) = (term67 _16430 _16431).
Proof. exact (eq_refl (term67 _16430 _16431)). Qed.
Lemma lem1011200 (_16430 : nat) (_16428 : nat) (_16429 : nat) (_16431 : nat) : (term62 _16430 _16431 _16428 _16429) = (term68 _16430 _16428 _16429 _16431).
Proof. exact (MK_COMB (@lem1011199 _16430 _16431) (@lem1011191 _16428 _16429 _16431)). Qed.
Lemma lem1011211 (_16430 : nat) (_16428 : nat) (_16429 : nat) (_16431 : nat) : (term51 _16430 _16431 _16428 _16429) = (term68 _16430 _16428 _16429 _16431).
Proof. exact (TRANS (@lem1011176 _16430 _16431 _16428 _16429) (@lem1011200 _16430 _16428 _16429 _16431)). Qed.
Lemma lem1011212 (_16428 : nat) (_16430 : nat) : (term69 _16428 _16430) = (term69 _16428 _16430).
Proof. exact (eq_refl (term69 _16428 _16430)). Qed.
Lemma lem1011213 (_16430 : nat) (_16428 : nat) (_16429 : nat) (_16431 : nat) : (term53 _16430 _16431 _16428 _16429) = (term70 _16430 _16428 _16429 _16431).
Proof. exact (MK_COMB (@lem1011212 _16428 _16430) (@lem1011211 _16430 _16428 _16429 _16431)). Qed.
Lemma lem1011217 (q : Prop) (p : Prop) (r : Prop) : (term61 p q r) = (term61 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1011218 (_16430 : nat) (_16428 : nat) (_16429 : nat) (_16431 : nat) : (term70 _16430 _16428 _16429 _16431) = (term71 _16430 _16428 _16429 _16431).
Proof. exact (@lem1011217 (Peano.le _16430 _16431) (term63 _16428 _16430) (term66 _16428 _16429 _16431)). Qed.
Lemma lem1011232 (q : Prop) (p : Prop) (r : Prop) : (term61 p q r) = (term61 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1011233 (_16428 : nat) (_16430 : nat) (_16429 : nat) (_16431 : nat) : (term72 _16430 _16428 _16429 _16431) = (term73 _16428 _16430 _16429 _16431).
Proof. exact (@lem1011232 (term64 _16428 _16429) (term63 _16428 _16430) (term63 _16429 _16431)). Qed.
Lemma lem1011253 (_16430 : nat) (_16431 : nat) : (term67 _16430 _16431) = (term67 _16430 _16431).
Proof. exact (eq_refl (term67 _16430 _16431)). Qed.
Lemma lem1011254 (_16428 : nat) (_16430 : nat) (_16429 : nat) (_16431 : nat) : (term71 _16430 _16428 _16429 _16431) = (term74 _16428 _16430 _16429 _16431).
Proof. exact (MK_COMB (@lem1011253 _16430 _16431) (@lem1011233 _16428 _16430 _16429 _16431)). Qed.
Lemma lem1011265 (_16428 : nat) (_16430 : nat) (_16429 : nat) (_16431 : nat) : (term70 _16430 _16428 _16429 _16431) = (term74 _16428 _16430 _16429 _16431).
Proof. exact (TRANS (@lem1011218 _16430 _16428 _16429 _16431) (@lem1011254 _16428 _16430 _16429 _16431)). Qed.
Lemma lem1011266 (_16428 : nat) (_16430 : nat) (_16429 : nat) (_16431 : nat) : (term53 _16430 _16431 _16428 _16429) = (term74 _16428 _16430 _16429 _16431).
Proof. exact (TRANS (@lem1011213 _16430 _16428 _16429 _16431) (@lem1011265 _16428 _16430 _16429 _16431)). Qed.
Lemma lem1011267 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1011268 (_16428 : nat) (_16430 : nat) (_16429 : nat) (_16431 : nat) : (term75 _16430 _16431 _16428 _16429) = (term76 _16428 _16430 _16429 _16431).
Proof. exact (MK_COMB (@lem1011267) (@lem1011266 _16428 _16430 _16429 _16431)). Qed.
Lemma lem1011294 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1011295 (_16428 : nat) (_16429 : nat) (_16431 : nat) : (term65 _16431 _16428 _16429) = (term66 _16428 _16429 _16431).
Proof. exact (@lem1011294 (term64 _16428 _16429) (term63 _16429 _16431)). Qed.
Lemma lem1011303 (_16428 : nat) (_16430 : nat) : (term69 _16428 _16430) = (term69 _16428 _16430).
Proof. exact (eq_refl (term69 _16428 _16430)). Qed.
Lemma lem1011304 (_16430 : nat) (_16428 : nat) (_16429 : nat) (_16431 : nat) : (term77 _16430 _16431 _16428 _16429) = (term72 _16430 _16428 _16429 _16431).
Proof. exact (MK_COMB (@lem1011303 _16428 _16430) (@lem1011295 _16428 _16429 _16431)). Qed.
Lemma lem1011308 (q : Prop) (p : Prop) (r : Prop) : (term61 p q r) = (term61 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1011309 (_16428 : nat) (_16430 : nat) (_16429 : nat) (_16431 : nat) : (term72 _16430 _16428 _16429 _16431) = (term73 _16428 _16430 _16429 _16431).
Proof. exact (@lem1011308 (term64 _16428 _16429) (term63 _16428 _16430) (term63 _16429 _16431)). Qed.
Lemma lem1011329 (_16428 : nat) (_16430 : nat) (_16429 : nat) (_16431 : nat) : (term77 _16430 _16431 _16428 _16429) = (term73 _16428 _16430 _16429 _16431).
Proof. exact (TRANS (@lem1011304 _16430 _16428 _16429 _16431) (@lem1011309 _16428 _16430 _16429 _16431)). Qed.
Lemma lem1011330 (_16430 : nat) (_16431 : nat) : (term67 _16430 _16431) = (term67 _16430 _16431).
Proof. exact (eq_refl (term67 _16430 _16431)). Qed.
Lemma lem1011331 (_16428 : nat) (_16430 : nat) (_16429 : nat) (_16431 : nat) : (term78 _16430 _16431 _16428 _16429) = (term74 _16428 _16430 _16429 _16431).
Proof. exact (MK_COMB (@lem1011330 _16430 _16431) (@lem1011329 _16428 _16430 _16429 _16431)). Qed.
Lemma lem1011342 (_16428 : nat) (_16430 : nat) (_16429 : nat) (_16431 : nat) : ((term53 _16430 _16431 _16428 _16429) = (term78 _16430 _16431 _16428 _16429)) = ((term74 _16428 _16430 _16429 _16431) = (term74 _16428 _16430 _16429 _16431)).
Proof. exact (MK_COMB (@lem1011268 _16428 _16430 _16429 _16431) (@lem1011331 _16428 _16430 _16429 _16431)). Qed.
Lemma lem1011344 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1011345 (x : Prop) : (x = x) = True.
Proof. exact (@lem1011344 Prop x). Qed.
Lemma lem1011346 (_16428 : nat) (_16430 : nat) (_16429 : nat) (_16431 : nat) : ((term74 _16428 _16430 _16429 _16431) = (term74 _16428 _16430 _16429 _16431)) = True.
Proof. exact (@lem1011345 (term74 _16428 _16430 _16429 _16431)). Qed.
Lemma lem1011347 (_16430 : nat) (_16431 : nat) (_16428 : nat) (_16429 : nat) : ((term53 _16430 _16431 _16428 _16429) = (term78 _16430 _16431 _16428 _16429)) = True.
Proof. exact (TRANS (@lem1011342 _16428 _16430 _16429 _16431) (@lem1011346 _16428 _16430 _16429 _16431)). Qed.
Lemma lem1011348 (_16430 : nat) (_16431 : nat) (_16428 : nat) (_16429 : nat) : True = ((term53 _16430 _16431 _16428 _16429) = (term78 _16430 _16431 _16428 _16429)).
Proof. exact (SYM (@lem1011347 _16430 _16431 _16428 _16429)). Qed.
Lemma lem1011349 (_16430 : nat) (_16431 : nat) (_16428 : nat) (_16429 : nat) : (term53 _16430 _16431 _16428 _16429) = (term78 _16430 _16431 _16428 _16429).
Proof. exact (EQ_MP (@lem1011348 _16430 _16431 _16428 _16429) (@lem0)). Qed.
Lemma lem1011350 (_16430 : nat) (_16431 : nat) (_16428 : nat) (_16429 : nat) : term78 _16430 _16431 _16428 _16429.
Proof. exact (EQ_MP (@lem1011349 _16430 _16431 _16428 _16429) (@lem1011116 _16430 _16431 _16428 _16429)). Qed.
Lemma lem1011352 (b : Prop) (a : Prop) : (a \/ b) = (term79 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1011353 (_16428 : nat) (_16429 : nat) (_16430 : nat) (_16431 : nat) : (term78 _16430 _16431 _16428 _16429) = (term80 _16428 _16429 _16430 _16431).
Proof. exact (@lem1011352 (term77 _16430 _16431 _16428 _16429) (Peano.le _16430 _16431)). Qed.
Lemma lem1011355 (a : Prop) (b : Prop) : (term81 a b) = (term82 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1011356 (_16430 : nat) (_16431 : nat) (_16428 : nat) (_16429 : nat) : (term83 _16430 _16431 _16428 _16429) = (term84 _16430 _16431 _16428 _16429).
Proof. exact (@lem1011355 (term63 _16428 _16430) (term65 _16431 _16428 _16429)). Qed.
Lemma lem1011358 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1011359 (_16428 : nat) (_16430 : nat) : (term86 _16428 _16430) = (_16428 = _16430).
Proof. exact (@lem1011358 (_16428 = _16430)). Qed.
Lemma lem1011360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1011361 (_16428 : nat) (_16430 : nat) : (term87 _16428 _16430) = (term88 _16428 _16430).
Proof. exact (MK_COMB (@lem1011360) (@lem1011359 _16428 _16430)). Qed.
Lemma lem1011363 (a : Prop) (b : Prop) : (term81 a b) = (term82 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1011364 (_16431 : nat) (_16428 : nat) (_16429 : nat) : (term89 _16431 _16428 _16429) = (term90 _16431 _16428 _16429).
Proof. exact (@lem1011363 (term63 _16429 _16431) (term64 _16428 _16429)). Qed.
Lemma lem1011366 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1011367 (_16429 : nat) (_16431 : nat) : (term86 _16429 _16431) = (_16429 = _16431).
Proof. exact (@lem1011366 (_16429 = _16431)). Qed.
Lemma lem1011368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1011369 (_16429 : nat) (_16431 : nat) : (term87 _16429 _16431) = (term88 _16429 _16431).
Proof. exact (MK_COMB (@lem1011368) (@lem1011367 _16429 _16431)). Qed.
Lemma lem1011371 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1011372 (_16428 : nat) (_16429 : nat) : (term91 _16428 _16429) = (Peano.le _16428 _16429).
Proof. exact (@lem1011371 (Peano.le _16428 _16429)). Qed.
Lemma lem1011373 (_16431 : nat) (_16428 : nat) (_16429 : nat) : (term90 _16431 _16428 _16429) = (term92 _16431 _16428 _16429).
Proof. exact (MK_COMB (@lem1011369 _16429 _16431) (@lem1011372 _16428 _16429)). Qed.
Lemma lem1011374 (_16431 : nat) (_16428 : nat) (_16429 : nat) : (term89 _16431 _16428 _16429) = (term92 _16431 _16428 _16429).
Proof. exact (TRANS (@lem1011364 _16431 _16428 _16429) (@lem1011373 _16431 _16428 _16429)). Qed.
Lemma lem1011375 (_16430 : nat) (_16431 : nat) (_16428 : nat) (_16429 : nat) : (term84 _16430 _16431 _16428 _16429) = (term93 _16430 _16431 _16428 _16429).
Proof. exact (MK_COMB (@lem1011361 _16428 _16430) (@lem1011374 _16431 _16428 _16429)). Qed.
Lemma lem1011376 (_16430 : nat) (_16431 : nat) (_16428 : nat) (_16429 : nat) : (term83 _16430 _16431 _16428 _16429) = (term93 _16430 _16431 _16428 _16429).
Proof. exact (TRANS (@lem1011356 _16430 _16431 _16428 _16429) (@lem1011375 _16430 _16431 _16428 _16429)). Qed.
Lemma lem1011377 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1011378 (_16430 : nat) (_16431 : nat) (_16428 : nat) (_16429 : nat) : (term94 _16430 _16431 _16428 _16429) = (term95 _16430 _16431 _16428 _16429).
Proof. exact (MK_COMB (@lem1011377) (@lem1011376 _16430 _16431 _16428 _16429)). Qed.
Lemma lem1011379 (_16430 : nat) (_16431 : nat) : (Peano.le _16430 _16431) = (Peano.le _16430 _16431).
Proof. exact (eq_refl (Peano.le _16430 _16431)). Qed.
Lemma lem1011380 (_16428 : nat) (_16429 : nat) (_16430 : nat) (_16431 : nat) : (term80 _16428 _16429 _16430 _16431) = (term96 _16428 _16429 _16430 _16431).
Proof. exact (MK_COMB (@lem1011378 _16430 _16431 _16428 _16429) (@lem1011379 _16430 _16431)). Qed.
Lemma lem1011381 (_16428 : nat) (_16429 : nat) (_16430 : nat) (_16431 : nat) : (term78 _16430 _16431 _16428 _16429) = (term96 _16428 _16429 _16430 _16431).
Proof. exact (TRANS (@lem1011353 _16428 _16429 _16430 _16431) (@lem1011380 _16428 _16429 _16430 _16431)). Qed.
Lemma lem1011383 (n : nat) (m : nat) (h1 : term20) (h2 : term41) : term97 n m.
Proof. exact (conj (@lem1011149 m n h2) (@lem1011157 n m h1)). Qed.
Lemma lem1011384 (n : nat) (m : nat) (h1 : term20) (h2 : term41) : term98 n m.
Proof. exact (conj (@lem1011141 n) (@lem1011383 n m h1 h2)). Qed.
Lemma lem1011386 (_16428 : nat) (_16429 : nat) (_16430 : nat) (_16431 : nat) : term96 _16428 _16429 _16430 _16431.
Proof. exact (EQ_MP (@lem1011381 _16428 _16429 _16430 _16431) (@lem1011350 _16430 _16431 _16428 _16429)). Qed.
Lemma lem1011387 (m : nat) (n : nat) : term99 m n.
Proof. exact (@lem1011386 n (Nat.add n m) n (Nat.add m n)). Qed.
Lemma lem1011390 (m : nat) (n : nat) (h1 : term20) (h2 : term41) : term10 m n.
Proof. exact (@lem1011387 m n (@lem1011384 n m h1 h2)). Qed.
Lemma lem1011391 (m : nat) (n : nat) (h1 : term20) (h2 : term41) : term100 m n.
Proof. exact (fun h0 : term13 m n => @lem1011390 m n h1 h2). Qed.
Lemma lem1011393 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1011394 (m : nat) (n : nat) : (term100 m n) = (term10 m n).
Proof. exact (@lem1011393 (term10 m n)). Qed.
Lemma lem1011395 (m : nat) (n : nat) (h1 : term20) (h2 : term41) : term10 m n.
Proof. exact (EQ_MP (@lem1011394 m n) (@lem1011391 m n h1 h2)). Qed.
Lemma lem1011398 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1011400 (m : nat) (n : nat) : (term13 m n) = (term101 m n).
Proof. exact (@lem1011398 (term10 m n)). Qed.
Lemma lem1011403 (m : nat) (n : nat) (h1 : term13 m n) : term101 m n.
Proof. exact (EQ_MP (@lem1011400 m n) (@lem1011093 m n h1)). Qed.
Lemma lem1011406 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : False.
Proof. exact (@lem1011403 m n h3 (@lem1011395 m n h1 h2)). Qed.
Lemma lem1011407 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : term102.
Proof. exact (fun h0 : ~ False => @lem1011406 m n h1 h2 h3). Qed.
Lemma lem1011409 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1011410 : term102 = False.
Proof. exact (@lem1011409 False). Qed.
Lemma lem1011411 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : False.
Proof. exact (EQ_MP (@lem1011410) (@lem1011407 m n h1 h2 h3)). Qed.
Lemma lem1011412 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : (term13 m n) = False.
Proof. exact (prop_ext (fun h4 : term13 m n => @lem1011411 m n h1 h2 h3) (fun h4 : False => @lem1011093 m n h3)). Qed.
Lemma lem1011413 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : False.
Proof. exact (EQ_MP (@lem1011412 m n h1 h2 h3) (@lem1011093 m n h3)). Qed.
Lemma lem1011414 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : (term13 m n) = False.
Proof. exact (prop_ext (fun h4 : term13 m n => @lem1011413 m n h1 h2 h3) (fun h4 : False => @lem1011059 m n h3)). Qed.
Lemma lem1011415 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : False.
Proof. exact (EQ_MP (@lem1011414 m n h1 h2 h3) (@lem1011059 m n h3)). Qed.
Lemma lem1011416 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : term20 = False.
Proof. exact (prop_ext (fun h4 : term20 => @lem1011415 m n h1 h2 h3) (fun h4 : False => @lem1011079 h1)). Qed.
Lemma lem1011417 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : False.
Proof. exact (EQ_MP (@lem1011416 m n h1 h2 h3) (@lem1011079 h1)). Qed.
Lemma lem1011418 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : term41 = False.
Proof. exact (prop_ext (fun h4 : term41 => @lem1011417 m n h1 h2 h3) (fun h4 : False => @lem1011069 h2)). Qed.
Lemma lem1011419 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : False.
Proof. exact (EQ_MP (@lem1011418 m n h1 h2 h3) (@lem1011069 h2)). Qed.
Lemma lem1011420 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : (term13 m n) = False.
Proof. exact (prop_ext (fun h4 : term13 m n => @lem1011419 m n h1 h2 h3) (fun h4 : False => @lem1011059 m n h3)). Qed.
Lemma lem1011421 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : False.
Proof. exact (EQ_MP (@lem1011420 m n h1 h2 h3) (@lem1011059 m n h3)). Qed.
Lemma lem1011422 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : term20 = False.
Proof. exact (prop_ext (fun h4 : term20 => @lem1011421 m n h1 h2 h3) (fun h4 : False => @lem1011055 h1)). Qed.
Lemma lem1011423 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : False.
Proof. exact (EQ_MP (@lem1011422 m n h1 h2 h3) (@lem1011055 h1)). Qed.
Lemma lem1011424 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : term41 = False.
Proof. exact (prop_ext (fun h4 : term41 => @lem1011423 m n h1 h2 h3) (fun h4 : False => @lem1011039 h2)). Qed.
Lemma lem1011425 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : False.
Proof. exact (EQ_MP (@lem1011424 m n h1 h2 h3) (@lem1011039 h2)). Qed.
Lemma lem1011426 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : (term13 m n) = False.
Proof. exact (prop_ext (fun h4 : term13 m n => @lem1011425 m n h1 h2 h3) (fun h4 : False => @lem1011019 m n h3)). Qed.
Lemma lem1011427 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : False.
Proof. exact (EQ_MP (@lem1011426 m n h1 h2 h3) (@lem1011019 m n h3)). Qed.
Lemma lem1011428 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : term20 = False.
Proof. exact (prop_ext (fun h4 : term20 => @lem1011427 m n h1 h2 h3) (fun h4 : False => @lem1011007 h1)). Qed.
Lemma lem1011429 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : False.
Proof. exact (EQ_MP (@lem1011428 m n h1 h2 h3) (@lem1011007 h1)). Qed.
Lemma lem1011430 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : term41 = False.
Proof. exact (prop_ext (fun h4 : term41 => @lem1011429 m n h1 h2 h3) (fun h4 : False => @lem1010987 h2)). Qed.
Lemma lem1011431 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : False.
Proof. exact (EQ_MP (@lem1011430 m n h1 h2 h3) (@lem1010987 h2)). Qed.
Lemma lem1011432 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : (term13 m n) = False.
Proof. exact (prop_ext (fun h4 : term13 m n => @lem1011431 m n h1 h2 h3) (fun h4 : False => @lem1010967 m n h3)). Qed.
Lemma lem1011433 (m : nat) (n : nat) (h1 : term20) (h2 : term41) (h3 : term13 m n) : False.
Proof. exact (EQ_MP (@lem1011432 m n h1 h2 h3) (@lem1010967 m n h3)). Qed.
Lemma lem1011434 (m : nat) (n : nat) (h1 : term41) (h2 : term13 m n) : term18.
Proof. exact (fun h0 : term20 => @lem1011433 m n h0 h1 h2). Qed.
Lemma lem1011435 : term18 = term19.
Proof. exact (@lem69 term20). Qed.
Lemma lem1011436 (m : nat) (n : nat) (h1 : term41) (h2 : term13 m n) : term19.
Proof. exact (EQ_MP (@lem1011435) (@lem1011434 m n h1 h2)). Qed.
Lemma lem1011437 (m : nat) (n : nat) (h1 : term13 m n) : term23.
Proof. exact (fun h0 : term41 => @lem1011436 m n h0 h1). Qed.
Lemma lem1011438 (m : nat) (n : nat) : term25 m n.
Proof. exact (fun h0 : term13 m n => @lem1011437 m n h0). Qed.
Lemma lem1011443 (n : nat) : term29 n.
Proof. exact (fun m : nat => @lem1011438 m n). Qed.
Lemma lem1011448 : term33.
Proof. exact (fun n : nat => @lem1011443 n). Qed.
Lemma lem1011449 : term32.
Proof. exact (EQ_MP (@lem1010958) (@lem1011448)). Qed.
Lemma lem1011450 (n : nat) : term103 n.
Proof. exact (@lem1011449 n). Qed.
Lemma lem1011451 (n : nat) : (term103 n) = (term28 n).
Proof. exact (eq_refl (term103 n)). Qed.
Lemma lem1011452 (n : nat) : term28 n.
Proof. exact (EQ_MP (@lem1011451 n) (@lem1011450 n)). Qed.
Lemma lem1011453 (n : nat) (m : nat) : term104 n m.
Proof. exact (@lem1011452 n m). Qed.
Lemma lem1011454 (m : nat) (n : nat) : (term104 n m) = (term14 m n).
Proof. exact (eq_refl (term104 n m)). Qed.
Lemma lem1011455 (m : nat) (n : nat) : term14 m n.
Proof. exact (EQ_MP (@lem1011454 m n) (@lem1011453 n m)). Qed.
Lemma lem1011457 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem1010826 m n (@lem1011455 m n)). Qed.
Lemma lem1011458 (m : nat) (n : nat) (h1 : term13 m n) : term22.
Proof. exact (@lem1011457 m n (@lem1010811 m n h1)). Qed.
Lemma lem1011459 (m : nat) (n : nat) (h1 : term13 m n) : term18.
Proof. exact (@lem1011458 m n h1 (@lem77775)). Qed.
Lemma lem1011460 (m : nat) (n : nat) (h1 : term13 m n) : False.
Proof. exact (@lem1011459 m n h1 (@lem100517)). Qed.
Lemma lem1011461 (m : nat) (n : nat) (h1 : term13 m n) : (term13 m n) = False.
Proof. exact (prop_ext (fun h2 : term13 m n => @lem1011460 m n h1) (fun h2 : False => @lem1010811 m n h1)). Qed.
Lemma lem1011462 (m : nat) (n : nat) (h1 : term13 m n) : False.
Proof. exact (EQ_MP (@lem1011461 m n h1) (@lem1010811 m n h1)). Qed.
Lemma lem1011463 (m : nat) (n : nat) : term12 m n.
Proof. exact (fun h0 : term13 m n => @lem1011462 m n h0). Qed.
Lemma lem1011464 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem1010810 m n) (@lem1011463 m n)). Qed.
Lemma lem1011465 (m : nat) (n : nat) : (term4 m n) = True.
Proof. exact (EQ_MP (@lem1010806 m n) (@lem1011464 m n)). Qed.
Lemma lem1011466 (m : nat) (n : nat) (p : nat) (h1 : (Nat.add m n) = p) : (term6 n p) = True.
Proof. exact (EQ_MP (@lem1010793 m n p h1) (@lem1011465 m n)). Qed.
Lemma lem1011469 (m : nat) (n : nat) (p : nat) : term105 m n p.
Proof. exact (fun h0 : (Nat.add m n) = p => @lem1011466 m n p h0). Qed.
Lemma lem1011470 (m : nat) (n : nat) (p : nat) (h1 : (Nat.add m n) = p) : (Nat.add m n) = p.
Proof. exact (h1). Qed.
Lemma lem1011471 (m : nat) (n : nat) (p : nat) (h1 : (Nat.add m n) = p) : (term6 n p) = True.
Proof. exact (@lem1011469 m n p (@lem1011470 m n p h1)). Qed.
