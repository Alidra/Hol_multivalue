Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_SUBSET_LE_term_abbrevs.
Require Import CARD_SUBSET_spec.
Require Import CARD_SUBSET_EQ_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LE_ANTISYM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm69_spec.
Lemma lem3902683 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3902684 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3902685 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3902684 t1) (@lem3902683 t1)). Qed.
Lemma lem3902686 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3902685 t1 t2). Qed.
Lemma lem3902687 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3902688 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3902687 t1 t2) (@lem3902686 t1 t2)). Qed.
Lemma lem3902689 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3902688 t1 t2 t3). Qed.
Lemma lem3902690 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3902691 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3902690 t1 t2 t3) (@lem3902689 t1 t2 t3)). Qed.
Lemma lem3902692 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3902691 t1 t2 t3)). Qed.
Lemma lem3902694 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3902695 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (@lem3902694 (term8 A)). Qed.
Lemma lem3902696 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem3902695 A)). Qed.
Lemma lem3902697 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem3902698 {A : Type'} : term11 A.
Proof. exact (@lem3902682 A). Qed.
Lemma lem3902701 {A : Type'} : term12 A.
Proof. exact (@lem3900203 A). Qed.
Lemma lem3902707 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem3902708 {A : Type'} : term14 A.
Proof. exact (fun h0 : term13 A => @lem3902707 A h0). Qed.
Lemma lem3902709 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (h1). Qed.
Lemma lem3902710 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem3902711 {A : Type'} (h1 : term13 A) (h2 : term14 A) : term13 A.
Proof. exact (@lem3902709 A h2 (@lem3902710 A h1)). Qed.
Lemma lem3902712 {A : Type'} (h1 : term13 A) : term15 A.
Proof. exact (fun h0 : term14 A => @lem3902711 A h1 h0). Qed.
Lemma lem3902713 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (h1). Qed.
Lemma lem3902714 {A : Type'} (h1 : term13 A) (h2 : term14 A) : term13 A.
Proof. exact (@lem3902712 A h1 (@lem3902713 A h2)). Qed.
Lemma lem3902715 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (fun h0 : term13 A => @lem3902714 A h0 h1). Qed.
Lemma lem3902716 {A : Type'} : term16 A.
Proof. exact (fun h0 : term14 A => @lem3902715 A h0). Qed.
Lemma lem3902719 {A : Type'} : term14 A.
Proof. exact (@lem3902716 A (@lem3902708 A)). Qed.
Lemma lem3902720 {A : Type'} : term14 A.
Proof. exact (@lem3902719 A). Qed.
Lemma lem3902766 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3902767 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem3902766 (term11 A)). Qed.
Lemma lem3902780 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem3902781 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem3902780 A) (@lem3902767 A)). Qed.
Lemma lem3902784 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem3902785 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem3902784) (@lem3902781 A)). Qed.
Lemma lem3902788 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (eq_refl (term25 A)). Qed.
Lemma lem3902795 {A : Type'} : (term13 A) = (term26 A).
Proof. exact (MK_COMB (@lem3902788 A) (@lem3902785 A)). Qed.
Lemma lem3902804 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term27 A a b) = (term27 A a b).
Proof. exact (eq_refl (term27 A a b)). Qed.
Lemma lem3902805 {A : Type'} (a : A -> Prop) : (term28 A a) = (term28 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3902804 A a b)). Qed.
Lemma lem3902806 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3902807 {A : Type'} (a : A -> Prop) : (term29 A a) = (term29 A a).
Proof. exact (MK_COMB (@lem3902806 A) (@lem3902805 A a)). Qed.
Lemma lem3902808 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3902807 A a)). Qed.
Lemma lem3902809 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3902810 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem3902809 A) (@lem3902808 A)). Qed.
Lemma lem3902811 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3902812 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem3902811) (@lem3902810 A)). Qed.
Lemma lem3902825 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term31 A a b) = (term31 A a b).
Proof. exact (eq_refl (term31 A a b)). Qed.
Lemma lem3902826 {A : Type'} (a : A -> Prop) : (term32 A a) = (term32 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3902825 A a b)). Qed.
Lemma lem3902827 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3902828 {A : Type'} (a : A -> Prop) : (term33 A a) = (term33 A a).
Proof. exact (MK_COMB (@lem3902827 A) (@lem3902826 A a)). Qed.
Lemma lem3902829 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3902828 A a)). Qed.
Lemma lem3902830 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3902831 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem3902830 A) (@lem3902829 A)). Qed.
Lemma lem3902832 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3902833 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem3902832) (@lem3902831 A)). Qed.
Lemma lem3902834 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (MK_COMB (@lem3902833 A) (@lem3902812 A)). Qed.
Lemma lem3902843 (m : nat) (n : nat) : ((term35 n m) = (m = n)) = ((term35 n m) = (m = n)).
Proof. exact (eq_refl ((term35 n m) = (m = n))). Qed.
Lemma lem3902844 (m : nat) : (term36 m) = (term36 m).
Proof. exact (fun_ext (fun n : nat => @lem3902843 m n)). Qed.
Lemma lem3902845 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3902846 (m : nat) : (term37 m) = (term37 m).
Proof. exact (MK_COMB (@lem3902845) (@lem3902844 m)). Qed.
Lemma lem3902847 : term38 = term38.
Proof. exact (fun_ext (fun m : nat => @lem3902846 m)). Qed.
Lemma lem3902848 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3902849 : term39 = term39.
Proof. exact (MK_COMB (@lem3902848) (@lem3902847)). Qed.
Lemma lem3902850 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3902851 : term22 = term22.
Proof. exact (MK_COMB (@lem3902850) (@lem3902849)). Qed.
Lemma lem3902852 {A : Type'} : (term24 A) = (term24 A).
Proof. exact (MK_COMB (@lem3902851) (@lem3902834 A)). Qed.
Lemma lem3902865 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term40 A a b) = (term40 A a b).
Proof. exact (eq_refl (term40 A a b)). Qed.
Lemma lem3902866 {A : Type'} (a : A -> Prop) : (term41 A a) = (term41 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3902865 A a b)). Qed.
Lemma lem3902867 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3902868 {A : Type'} (a : A -> Prop) : (term42 A a) = (term42 A a).
Proof. exact (MK_COMB (@lem3902867 A) (@lem3902866 A a)). Qed.
Lemma lem3902869 {A : Type'} : (term43 A) = (term43 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3902868 A a)). Qed.
Lemma lem3902870 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3902871 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (MK_COMB (@lem3902870 A) (@lem3902869 A)). Qed.
Lemma lem3902872 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3902873 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem3902872) (@lem3902871 A)). Qed.
Lemma lem3902874 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3902875 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (MK_COMB (@lem3902874) (@lem3902873 A)). Qed.
Lemma lem3902876 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem3902875 A) (@lem3902852 A)). Qed.
Lemma lem3902951 {A : Type'} : (term13 A) = (term26 A).
Proof. exact (TRANS (@lem3902795 A) (@lem3902876 A)). Qed.
Lemma lem3902952 {A : Type'} : (term26 A) = (term13 A).
Proof. exact (SYM (@lem3902951 A)). Qed.
Lemma lem3902953 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem3902954 (h1 : term39) : term39.
Proof. exact (h1). Qed.
Lemma lem3902955 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem3902956 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem3902971 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term44 A a b) = (term45 A a b).
Proof. exact (@lem17362 (term46 A b a) (a = b)). Qed.
Lemma lem3902972 {A : Type'} (P : type686 A) : (term47 A P) = (term48 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3902973 {A : Type'} (a : A -> Prop) : (term49 A a) = (term50 A a).
Proof. exact (@lem3902972 A (term41 A a)). Qed.
Lemma lem3902974 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term51 A a b) = (term40 A a b).
Proof. exact (eq_refl (term51 A a b)). Qed.
Lemma lem3902975 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3902976 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term52 A a b) = (term44 A a b).
Proof. exact (MK_COMB (@lem3902975) (@lem3902974 A a b)). Qed.
Lemma lem3902977 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term52 A a b) = (term45 A a b).
Proof. exact (TRANS (@lem3902976 A a b) (@lem3902971 A a b)). Qed.
Lemma lem3902978 {A : Type'} (a : A -> Prop) : (term53 A a) = (term54 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3902977 A a b)). Qed.
Lemma lem3902979 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3902980 {A : Type'} (a : A -> Prop) : (term50 A a) = (term55 A a).
Proof. exact (MK_COMB (@lem3902979 A) (@lem3902978 A a)). Qed.
Lemma lem3902981 {A : Type'} (a : A -> Prop) : (term49 A a) = (term55 A a).
Proof. exact (TRANS (@lem3902973 A a) (@lem3902980 A a)). Qed.
Lemma lem3902982 {A : Type'} (P : type686 A) : (term47 A P) = (term48 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3902983 {A : Type'} : (term10 A) = (term56 A).
Proof. exact (@lem3902982 A (term43 A)). Qed.
Lemma lem3902984 {A : Type'} (a : A -> Prop) : (term57 A a) = (term42 A a).
Proof. exact (eq_refl (term57 A a)). Qed.
Lemma lem3902985 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3902986 {A : Type'} (a : A -> Prop) : (term58 A a) = (term49 A a).
Proof. exact (MK_COMB (@lem3902985) (@lem3902984 A a)). Qed.
Lemma lem3902987 {A : Type'} (a : A -> Prop) : (term58 A a) = (term55 A a).
Proof. exact (TRANS (@lem3902986 A a) (@lem3902981 A a)). Qed.
Lemma lem3902988 {A : Type'} : (term59 A) = (term60 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3902987 A a)). Qed.
Lemma lem3902989 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3902990 {A : Type'} : (term56 A) = (term61 A).
Proof. exact (MK_COMB (@lem3902989 A) (@lem3902988 A)). Qed.
Lemma lem3903047 {A : Type'} : (term10 A) = (term61 A).
Proof. exact (TRANS (@lem3902983 A) (@lem3902990 A)). Qed.
Lemma lem3903048 {A : Type'} (h1 : term10 A) : term61 A.
Proof. exact (EQ_MP (@lem3903047 A) (@lem3902953 A h1)). Qed.
Lemma lem3903057 (n : nat) (m : nat) : (term62 n m) = (term63 n m).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n m)). Qed.
Lemma lem3903062 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem3903063 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3903064 (n : nat) (m : nat) : (term64 n m) = (term65 n m).
Proof. exact (MK_COMB (@lem3903063) (@lem3903057 n m)). Qed.
Lemma lem3903065 (m : nat) (n : nat) : (term66 m n) = (term67 m n).
Proof. exact (MK_COMB (@lem3903064 n m) (@lem3903062 m n)). Qed.
Lemma lem3903070 (m : nat) (n : nat) : (term68 m n) = (term68 m n).
Proof. exact (eq_refl (term68 m n)). Qed.
Lemma lem3903071 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (MK_COMB (@lem3903070 m n) (@lem3903065 m n)). Qed.
Lemma lem3903072 (m : nat) (n : nat) : ((term35 n m) = (m = n)) = (term69 m n).
Proof. exact (@lem17784 (term35 n m) (m = n)). Qed.
Lemma lem3903073 (m : nat) (n : nat) : ((term35 n m) = (m = n)) = (term70 m n).
Proof. exact (TRANS (@lem3903072 m n) (@lem3903071 m n)). Qed.
Lemma lem3903074 (m : nat) : (term36 m) = (term71 m).
Proof. exact (fun_ext (fun n : nat => @lem3903073 m n)). Qed.
Lemma lem3903075 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3903076 (m : nat) : (term37 m) = (term72 m).
Proof. exact (MK_COMB (@lem3903075) (@lem3903074 m)). Qed.
Lemma lem3903077 : term38 = term73.
Proof. exact (fun_ext (fun m : nat => @lem3903076 m)). Qed.
Lemma lem3903078 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3903079 : term39 = term74.
Proof. exact (MK_COMB (@lem3903078) (@lem3903077)). Qed.
Lemma lem3903085 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3903086 (P : nat -> Prop) (Q : nat -> Prop) : (term77 P Q) = (term78 P Q).
Proof. exact (@lem3903085 nat P Q). Qed.
Lemma lem3903087 (m : nat) : (term79 m) = (term80 m).
Proof. exact (@lem3903086 (term81 m) (term82 m)). Qed.
Lemma lem3903088 (m : nat) (n : nat) : (term83 m n) = (term84 m n).
Proof. exact (eq_refl (term83 m n)). Qed.
Lemma lem3903089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3903090 (m : nat) (n : nat) : (term85 m n) = (term68 m n).
Proof. exact (MK_COMB (@lem3903089) (@lem3903088 m n)). Qed.
Lemma lem3903091 (m : nat) (n : nat) : (term86 m n) = (term67 m n).
Proof. exact (eq_refl (term86 m n)). Qed.
Lemma lem3903092 (m : nat) (n : nat) : (term87 m n) = (term70 m n).
Proof. exact (MK_COMB (@lem3903090 m n) (@lem3903091 m n)). Qed.
Lemma lem3903093 (m : nat) : (term88 m) = (term71 m).
Proof. exact (fun_ext (fun n : nat => @lem3903092 m n)). Qed.
Lemma lem3903094 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3903095 (m : nat) : (term79 m) = (term72 m).
Proof. exact (MK_COMB (@lem3903094) (@lem3903093 m)). Qed.
Lemma lem3903096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3903097 (m : nat) : (term89 m) = (term90 m).
Proof. exact (MK_COMB (@lem3903096) (@lem3903095 m)). Qed.
Lemma lem3903098 (m : nat) (n : nat) : (term83 m n) = (term84 m n).
Proof. exact (eq_refl (term83 m n)). Qed.
Lemma lem3903099 (m : nat) : (term91 m) = (term81 m).
Proof. exact (fun_ext (fun n : nat => @lem3903098 m n)). Qed.
Lemma lem3903100 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3903101 (m : nat) : (term92 m) = (term93 m).
Proof. exact (MK_COMB (@lem3903100) (@lem3903099 m)). Qed.
Lemma lem3903102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3903103 (m : nat) : (term94 m) = (term95 m).
Proof. exact (MK_COMB (@lem3903102) (@lem3903101 m)). Qed.
Lemma lem3903104 (m : nat) (n : nat) : (term86 m n) = (term67 m n).
Proof. exact (eq_refl (term86 m n)). Qed.
Lemma lem3903105 (m : nat) : (term96 m) = (term82 m).
Proof. exact (fun_ext (fun n : nat => @lem3903104 m n)). Qed.
Lemma lem3903106 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3903107 (m : nat) : (term97 m) = (term98 m).
Proof. exact (MK_COMB (@lem3903106) (@lem3903105 m)). Qed.
Lemma lem3903108 (m : nat) : (term80 m) = (term99 m).
Proof. exact (MK_COMB (@lem3903103 m) (@lem3903107 m)). Qed.
Lemma lem3903109 (m : nat) : ((term79 m) = (term80 m)) = ((term72 m) = (term99 m)).
Proof. exact (MK_COMB (@lem3903097 m) (@lem3903108 m)). Qed.
Lemma lem3903110 (m : nat) : (term72 m) = (term99 m).
Proof. exact (EQ_MP (@lem3903109 m) (@lem3903087 m)). Qed.
Lemma lem3903207 : term73 = term100.
Proof. exact (fun_ext (fun m : nat => @lem3903110 m)). Qed.
Lemma lem3903208 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3903209 : term74 = term101.
Proof. exact (MK_COMB (@lem3903208) (@lem3903207)). Qed.
Lemma lem3903211 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3903212 (P : nat -> Prop) (Q : nat -> Prop) : (term77 P Q) = (term78 P Q).
Proof. exact (@lem3903211 nat P Q). Qed.
Lemma lem3903213 : term102 = term103.
Proof. exact (@lem3903212 term104 term105). Qed.
Lemma lem3903214 (m : nat) : (term106 m) = (term93 m).
Proof. exact (eq_refl (term106 m)). Qed.
Lemma lem3903215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3903216 (m : nat) : (term107 m) = (term95 m).
Proof. exact (MK_COMB (@lem3903215) (@lem3903214 m)). Qed.
Lemma lem3903217 (m : nat) : (term108 m) = (term98 m).
Proof. exact (eq_refl (term108 m)). Qed.
Lemma lem3903218 (m : nat) : (term109 m) = (term99 m).
Proof. exact (MK_COMB (@lem3903216 m) (@lem3903217 m)). Qed.
Lemma lem3903219 : term110 = term100.
Proof. exact (fun_ext (fun m : nat => @lem3903218 m)). Qed.
Lemma lem3903220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3903221 : term102 = term101.
Proof. exact (MK_COMB (@lem3903220) (@lem3903219)). Qed.
Lemma lem3903222 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3903223 : term111 = term112.
Proof. exact (MK_COMB (@lem3903222) (@lem3903221)). Qed.
Lemma lem3903224 (m : nat) : (term106 m) = (term93 m).
Proof. exact (eq_refl (term106 m)). Qed.
Lemma lem3903225 : term113 = term104.
Proof. exact (fun_ext (fun m : nat => @lem3903224 m)). Qed.
Lemma lem3903226 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3903227 : term114 = term115.
Proof. exact (MK_COMB (@lem3903226) (@lem3903225)). Qed.
Lemma lem3903228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3903229 : term116 = term117.
Proof. exact (MK_COMB (@lem3903228) (@lem3903227)). Qed.
Lemma lem3903230 (m : nat) : (term108 m) = (term98 m).
Proof. exact (eq_refl (term108 m)). Qed.
Lemma lem3903231 : term118 = term105.
Proof. exact (fun_ext (fun m : nat => @lem3903230 m)). Qed.
Lemma lem3903232 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3903233 : term119 = term120.
Proof. exact (MK_COMB (@lem3903232) (@lem3903231)). Qed.
Lemma lem3903234 : term103 = term121.
Proof. exact (MK_COMB (@lem3903229) (@lem3903233)). Qed.
Lemma lem3903235 : (term102 = term103) = (term101 = term121).
Proof. exact (MK_COMB (@lem3903223) (@lem3903234)). Qed.
Lemma lem3903236 : term101 = term121.
Proof. exact (EQ_MP (@lem3903235) (@lem3903213)). Qed.
Lemma lem3903343 : term74 = term121.
Proof. exact (TRANS (@lem3903209) (@lem3903236)). Qed.
Lemma lem3903344 : term39 = term121.
Proof. exact (TRANS (@lem3903079) (@lem3903343)). Qed.
Lemma lem3903345 (h1 : term39) : term121.
Proof. exact (EQ_MP (@lem3903344) (@lem3902954 h1)). Qed.
Lemma lem3903353 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term122 A a b) = (term123 A a b).
Proof. exact (@lem17045 (@SUBSET A a b) ((@CARD A a) = (@CARD A b))). Qed.
Lemma lem3903355 {A : Type'} (b : A -> Prop) : (term124 A b) = (term124 A b).
Proof. exact (eq_refl (term124 A b)). Qed.
Lemma lem3903356 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term125 A a b) = (term126 A a b).
Proof. exact (MK_COMB (@lem3903355 A b) (@lem3903353 A a b)). Qed.
Lemma lem3903357 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term127 A a b) = (term125 A a b).
Proof. exact (@lem17045 (@FINITE A b) (term128 A a b)). Qed.
Lemma lem3903358 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term127 A a b) = (term126 A a b).
Proof. exact (TRANS (@lem3903357 A a b) (@lem3903356 A a b)). Qed.
Lemma lem3903359 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (a = b) = (a = b).
Proof. exact (eq_refl (a = b)). Qed.
Lemma lem3903360 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3903361 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term129 A a b) = (term130 A a b).
Proof. exact (MK_COMB (@lem3903360) (@lem3903358 A a b)). Qed.
Lemma lem3903362 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term131 A a b) = (term132 A a b).
Proof. exact (MK_COMB (@lem3903361 A a b) (@lem3903359 A a b)). Qed.
Lemma lem3903363 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term31 A a b) = (term131 A a b).
Proof. exact (@lem17265 (term133 A a b) (a = b)). Qed.
Lemma lem3903364 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term31 A a b) = (term132 A a b).
Proof. exact (TRANS (@lem3903363 A a b) (@lem3903362 A a b)). Qed.
Lemma lem3903365 {A : Type'} (a : A -> Prop) : (term32 A a) = (term134 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3903364 A a b)). Qed.
Lemma lem3903366 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3903367 {A : Type'} (a : A -> Prop) : (term33 A a) = (term135 A a).
Proof. exact (MK_COMB (@lem3903366 A) (@lem3903365 A a)). Qed.
Lemma lem3903368 {A : Type'} : (term34 A) = (term136 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3903367 A a)). Qed.
Lemma lem3903369 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3903426 {A : Type'} : (term12 A) = (term137 A).
Proof. exact (MK_COMB (@lem3903369 A) (@lem3903368 A)). Qed.
Lemma lem3903427 {A : Type'} (h1 : term12 A) : term137 A.
Proof. exact (EQ_MP (@lem3903426 A) (@lem3902955 A h1)). Qed.
Lemma lem3903434 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term138 A a b) = (term139 A a b).
Proof. exact (@lem17045 (@SUBSET A a b) (@FINITE A b)). Qed.
Lemma lem3903435 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term140 A a b) = (term140 A a b).
Proof. exact (eq_refl (term140 A a b)). Qed.
Lemma lem3903436 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3903437 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term141 A a b) = (term142 A a b).
Proof. exact (MK_COMB (@lem3903436) (@lem3903434 A a b)). Qed.
Lemma lem3903438 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term143 A a b) = (term144 A a b).
Proof. exact (MK_COMB (@lem3903437 A a b) (@lem3903435 A a b)). Qed.
Lemma lem3903439 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term27 A a b) = (term143 A a b).
Proof. exact (@lem17265 (term145 A a b) (term140 A a b)). Qed.
Lemma lem3903440 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term27 A a b) = (term144 A a b).
Proof. exact (TRANS (@lem3903439 A a b) (@lem3903438 A a b)). Qed.
Lemma lem3903441 {A : Type'} (a : A -> Prop) : (term28 A a) = (term146 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3903440 A a b)). Qed.
Lemma lem3903442 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3903443 {A : Type'} (a : A -> Prop) : (term29 A a) = (term147 A a).
Proof. exact (MK_COMB (@lem3903442 A) (@lem3903441 A a)). Qed.
Lemma lem3903444 {A : Type'} : (term30 A) = (term148 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3903443 A a)). Qed.
Lemma lem3903445 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3903502 {A : Type'} : (term11 A) = (term149 A).
Proof. exact (MK_COMB (@lem3903445 A) (@lem3903444 A)). Qed.
Lemma lem3903503 {A : Type'} (h1 : term11 A) : term149 A.
Proof. exact (EQ_MP (@lem3903502 A) (@lem3902956 A h1)). Qed.
Lemma lem3903504 {A : Type'} (a : A -> Prop) (h1 : term55 A a) : term55 A a.
Proof. exact (h1). Qed.
Lemma lem3903530 (m : nat) (n : nat) : (term67 m n) = (term67 m n).
Proof. exact (eq_refl (term67 m n)). Qed.
Lemma lem3903531 (m : nat) : (term82 m) = (term82 m).
Proof. exact (fun_ext (fun n : nat => @lem3903530 m n)). Qed.
Lemma lem3903532 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3903533 (m : nat) : (term98 m) = (term98 m).
Proof. exact (MK_COMB (@lem3903532) (@lem3903531 m)). Qed.
Lemma lem3903534 : term105 = term105.
Proof. exact (fun_ext (fun m : nat => @lem3903533 m)). Qed.
Lemma lem3903535 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3903536 : term120 = term120.
Proof. exact (MK_COMB (@lem3903535) (@lem3903534)). Qed.
Lemma lem3903559 (m : nat) (n : nat) : (term84 m n) = (term84 m n).
Proof. exact (eq_refl (term84 m n)). Qed.
Lemma lem3903560 (m : nat) : (term81 m) = (term81 m).
Proof. exact (fun_ext (fun n : nat => @lem3903559 m n)). Qed.
Lemma lem3903561 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3903562 (m : nat) : (term93 m) = (term93 m).
Proof. exact (MK_COMB (@lem3903561) (@lem3903560 m)). Qed.
Lemma lem3903563 : term104 = term104.
Proof. exact (fun_ext (fun m : nat => @lem3903562 m)). Qed.
Lemma lem3903564 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3903565 : term115 = term115.
Proof. exact (MK_COMB (@lem3903564) (@lem3903563)). Qed.
Lemma lem3903566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3903567 : term117 = term117.
Proof. exact (MK_COMB (@lem3903566) (@lem3903565)). Qed.
Lemma lem3903568 : term121 = term121.
Proof. exact (MK_COMB (@lem3903567) (@lem3903536)). Qed.
Lemma lem3903569 (h1 : term39) : term121.
Proof. exact (EQ_MP (@lem3903568) (@lem3903345 h1)). Qed.
Lemma lem3903606 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term132 A a b) = (term132 A a b).
Proof. exact (eq_refl (term132 A a b)). Qed.
Lemma lem3903607 {A : Type'} (a : A -> Prop) : (term134 A a) = (term134 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3903606 A a b)). Qed.
Lemma lem3903608 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3903609 {A : Type'} (a : A -> Prop) : (term135 A a) = (term135 A a).
Proof. exact (MK_COMB (@lem3903608 A) (@lem3903607 A a)). Qed.
Lemma lem3903610 {A : Type'} : (term136 A) = (term136 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3903609 A a)). Qed.
Lemma lem3903611 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3903612 {A : Type'} : (term137 A) = (term137 A).
Proof. exact (MK_COMB (@lem3903611 A) (@lem3903610 A)). Qed.
Lemma lem3903613 {A : Type'} (h1 : term12 A) : term137 A.
Proof. exact (EQ_MP (@lem3903612 A) (@lem3903427 A h1)). Qed.
Lemma lem3903640 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term144 A a b) = (term144 A a b).
Proof. exact (eq_refl (term144 A a b)). Qed.
Lemma lem3903641 {A : Type'} (a : A -> Prop) : (term146 A a) = (term146 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3903640 A a b)). Qed.
Lemma lem3903642 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3903643 {A : Type'} (a : A -> Prop) : (term147 A a) = (term147 A a).
Proof. exact (MK_COMB (@lem3903642 A) (@lem3903641 A a)). Qed.
Lemma lem3903644 {A : Type'} : (term148 A) = (term148 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3903643 A a)). Qed.
Lemma lem3903645 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3903646 {A : Type'} : (term149 A) = (term149 A).
Proof. exact (MK_COMB (@lem3903645 A) (@lem3903644 A)). Qed.
Lemma lem3903647 {A : Type'} (h1 : term11 A) : term149 A.
Proof. exact (EQ_MP (@lem3903646 A) (@lem3903503 A h1)). Qed.
Lemma lem3903681 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term45 A a b.
Proof. exact (h1). Qed.
Lemma lem3903683 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term46 A b a.
Proof. exact (proj1 (@lem3903681 A a b h1)). Qed.
Lemma lem3903684 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term150 A b a.
Proof. exact (proj2 (@lem3903683 A a b h1)). Qed.
Lemma lem3903688 (h1 : term39) : term120.
Proof. exact (proj2 (@lem3903569 h1)). Qed.
Lemma lem3903709 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term132 A a b) = (term132 A a b).
Proof. exact (eq_refl (term132 A a b)). Qed.
Lemma lem3903710 {A : Type'} (a : A -> Prop) : (term134 A a) = (term134 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3903709 A a b)). Qed.
Lemma lem3903711 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3903712 {A : Type'} (a : A -> Prop) : (term135 A a) = (term135 A a).
Proof. exact (MK_COMB (@lem3903711 A) (@lem3903710 A a)). Qed.
Lemma lem3903713 {A : Type'} : (term136 A) = (term136 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3903712 A a)). Qed.
Lemma lem3903714 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3903716 {A : Type'} : (term137 A) = (term137 A).
Proof. exact (MK_COMB (@lem3903714 A) (@lem3903713 A)). Qed.
Lemma lem3903717 {A : Type'} (h1 : term12 A) : term137 A.
Proof. exact (EQ_MP (@lem3903716 A) (@lem3903613 A h1)). Qed.
Lemma lem3903731 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term144 A a b) = (term144 A a b).
Proof. exact (eq_refl (term144 A a b)). Qed.
Lemma lem3903732 {A : Type'} (a : A -> Prop) : (term146 A a) = (term146 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3903731 A a b)). Qed.
Lemma lem3903733 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3903734 {A : Type'} (a : A -> Prop) : (term147 A a) = (term147 A a).
Proof. exact (MK_COMB (@lem3903733 A) (@lem3903732 A a)). Qed.
Lemma lem3903735 {A : Type'} : (term148 A) = (term148 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3903734 A a)). Qed.
Lemma lem3903736 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3903738 {A : Type'} : (term149 A) = (term149 A).
Proof. exact (MK_COMB (@lem3903736 A) (@lem3903735 A)). Qed.
Lemma lem3903739 {A : Type'} (h1 : term11 A) : term149 A.
Proof. exact (EQ_MP (@lem3903738 A) (@lem3903647 A h1)). Qed.
Lemma lem3903795 (m : nat) (n : nat) : (term67 m n) = (term67 m n).
Proof. exact (eq_refl (term67 m n)). Qed.
Lemma lem3903796 (m : nat) : (term82 m) = (term82 m).
Proof. exact (fun_ext (fun n : nat => @lem3903795 m n)). Qed.
Lemma lem3903797 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3903798 (m : nat) : (term98 m) = (term98 m).
Proof. exact (MK_COMB (@lem3903797) (@lem3903796 m)). Qed.
Lemma lem3903799 : term105 = term105.
Proof. exact (fun_ext (fun m : nat => @lem3903798 m)). Qed.
Lemma lem3903800 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3903802 : term120 = term120.
Proof. exact (MK_COMB (@lem3903800) (@lem3903799)). Qed.
Lemma lem3903803 (h1 : term39) : term120.
Proof. exact (EQ_MP (@lem3903802) (@lem3903688 h1)). Qed.
Lemma lem3903804 {A : Type'} (_45316 : A -> Prop) (h1 : term12 A) : term151 A _45316.
Proof. exact (@lem3903717 A h1 _45316). Qed.
Lemma lem3903805 {A : Type'} (_45316 : A -> Prop) : (term151 A _45316) = (term135 A _45316).
Proof. exact (eq_refl (term151 A _45316)). Qed.
Lemma lem3903806 {A : Type'} (_45316 : A -> Prop) (h1 : term12 A) : term135 A _45316.
Proof. exact (EQ_MP (@lem3903805 A _45316) (@lem3903804 A _45316 h1)). Qed.
Lemma lem3903807 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) (h1 : term12 A) : term152 A _45316 _45317.
Proof. exact (@lem3903806 A _45316 h1 _45317). Qed.
Lemma lem3903808 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term152 A _45316 _45317) = (term132 A _45316 _45317).
Proof. exact (eq_refl (term152 A _45316 _45317)). Qed.
Lemma lem3903809 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) (h1 : term12 A) : term132 A _45316 _45317.
Proof. exact (EQ_MP (@lem3903808 A _45316 _45317) (@lem3903807 A _45316 _45317 h1)). Qed.
Lemma lem3903810 {A : Type'} (_45318 : A -> Prop) (h1 : term11 A) : term153 A _45318.
Proof. exact (@lem3903739 A h1 _45318). Qed.
Lemma lem3903811 {A : Type'} (_45318 : A -> Prop) : (term153 A _45318) = (term147 A _45318).
Proof. exact (eq_refl (term153 A _45318)). Qed.
Lemma lem3903812 {A : Type'} (_45318 : A -> Prop) (h1 : term11 A) : term147 A _45318.
Proof. exact (EQ_MP (@lem3903811 A _45318) (@lem3903810 A _45318 h1)). Qed.
Lemma lem3903813 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) (h1 : term11 A) : term154 A _45318 _45319.
Proof. exact (@lem3903812 A _45318 h1 _45319). Qed.
Lemma lem3903814 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term154 A _45318 _45319) = (term144 A _45318 _45319).
Proof. exact (eq_refl (term154 A _45318 _45319)). Qed.
Lemma lem3903815 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) (h1 : term11 A) : term144 A _45318 _45319.
Proof. exact (EQ_MP (@lem3903814 A _45318 _45319) (@lem3903813 A _45318 _45319 h1)). Qed.
Lemma lem3903822 (_45322 : nat) (h1 : term39) : term108 _45322.
Proof. exact (@lem3903803 h1 _45322). Qed.
Lemma lem3903823 (_45322 : nat) : (term108 _45322) = (term98 _45322).
Proof. exact (eq_refl (term108 _45322)). Qed.
Lemma lem3903824 (_45322 : nat) (h1 : term39) : term98 _45322.
Proof. exact (EQ_MP (@lem3903823 _45322) (@lem3903822 _45322 h1)). Qed.
Lemma lem3903825 (_45322 : nat) (_45323 : nat) (h1 : term39) : term86 _45322 _45323.
Proof. exact (@lem3903824 _45322 h1 _45323). Qed.
Lemma lem3903826 (_45322 : nat) (_45323 : nat) : (term86 _45322 _45323) = (term67 _45322 _45323).
Proof. exact (eq_refl (term86 _45322 _45323)). Qed.
Lemma lem3903827 (_45322 : nat) (_45323 : nat) (h1 : term39) : term67 _45322 _45323.
Proof. exact (EQ_MP (@lem3903826 _45322 _45323) (@lem3903825 _45322 _45323 h1)). Qed.
Lemma lem3903833 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term132 A _45316 _45317) = (term155 A _45316 _45317).
Proof. exact (@lem3902692 (term156 A _45317) (term123 A _45316 _45317) (_45316 = _45317)). Qed.
Lemma lem3903840 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term157 A _45316 _45317) = (term158 A _45316 _45317).
Proof. exact (@lem3902692 (term159 A _45316 _45317) (term160 A _45316 _45317) (_45316 = _45317)). Qed.
Lemma lem3903841 {A : Type'} (_45317 : A -> Prop) : (term124 A _45317) = (term124 A _45317).
Proof. exact (eq_refl (term124 A _45317)). Qed.
Lemma lem3903844 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term155 A _45316 _45317) = (term161 A _45316 _45317).
Proof. exact (MK_COMB (@lem3903841 A _45317) (@lem3903840 A _45316 _45317)). Qed.
Lemma lem3903846 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term132 A _45316 _45317) = (term161 A _45316 _45317).
Proof. exact (TRANS (@lem3903833 A _45316 _45317) (@lem3903844 A _45316 _45317)). Qed.
Lemma lem3903847 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) (h1 : term12 A) : term161 A _45316 _45317.
Proof. exact (EQ_MP (@lem3903846 A _45316 _45317) (@lem3903809 A _45316 _45317 h1)). Qed.
Lemma lem3903858 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term144 A _45318 _45319) = (term162 A _45318 _45319).
Proof. exact (@lem3902692 (term159 A _45318 _45319) (term156 A _45319) (term140 A _45318 _45319)). Qed.
Lemma lem3903859 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) (h1 : term11 A) : term162 A _45318 _45319.
Proof. exact (EQ_MP (@lem3903858 A _45318 _45319) (@lem3903815 A _45318 _45319 h1)). Qed.
Lemma lem3903861 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term163 A a b.
Proof. exact (proj2 (@lem3903681 A a b h1)). Qed.
Lemma lem3903878 (_45322 : nat) (_45323 : nat) : (term67 _45322 _45323) = (term164 _45322 _45323).
Proof. exact (@lem3902692 (term165 _45322 _45323) (term165 _45323 _45322) (_45322 = _45323)). Qed.
Lemma lem3903879 (_45322 : nat) (_45323 : nat) (h1 : term39) : term164 _45322 _45323.
Proof. exact (EQ_MP (@lem3903878 _45322 _45323) (@lem3903827 _45322 _45323 h1)). Qed.
Lemma lem3903955 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : @FINITE A b.
Proof. exact (proj1 (@lem3903683 A a b h1)). Qed.
Lemma lem3903956 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term166 A b.
Proof. exact (fun h0 : term156 A b => @lem3903955 A a b h1). Qed.
Lemma lem3903958 (p : Prop) : (term167 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3903959 {A : Type'} (b : A -> Prop) : (term166 A b) = (@FINITE A b).
Proof. exact (@lem3903958 (@FINITE A b)). Qed.
Lemma lem3903960 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : @FINITE A b.
Proof. exact (EQ_MP (@lem3903959 A b) (@lem3903956 A a b h1)). Qed.
Lemma lem3903962 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : @SUBSET A a b.
Proof. exact (proj1 (@lem3903684 A a b h1)). Qed.
Lemma lem3903963 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term168 A a b.
Proof. exact (fun h0 : term159 A a b => @lem3903962 A a b h1). Qed.
Lemma lem3903965 (p : Prop) : (term167 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3903966 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term168 A a b) = (@SUBSET A a b).
Proof. exact (@lem3903965 (@SUBSET A a b)). Qed.
Lemma lem3903967 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : @SUBSET A a b.
Proof. exact (EQ_MP (@lem3903966 A a b) (@lem3903963 A a b h1)). Qed.
Lemma lem3903969 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : @SUBSET A a b.
Proof. exact (proj1 (@lem3903684 A a b h1)). Qed.
Lemma lem3903970 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term168 A a b.
Proof. exact (fun h0 : term159 A a b => @lem3903969 A a b h1). Qed.
Lemma lem3903972 (p : Prop) : (term167 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3903973 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term168 A a b) = (@SUBSET A a b).
Proof. exact (@lem3903972 (@SUBSET A a b)). Qed.
Lemma lem3903974 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : @SUBSET A a b.
Proof. exact (EQ_MP (@lem3903973 A a b) (@lem3903970 A a b h1)). Qed.
Lemma lem3903976 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : @FINITE A b.
Proof. exact (proj1 (@lem3903683 A a b h1)). Qed.
Lemma lem3903977 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term166 A b.
Proof. exact (fun h0 : term156 A b => @lem3903976 A a b h1). Qed.
Lemma lem3903979 (p : Prop) : (term167 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3903980 {A : Type'} (b : A -> Prop) : (term166 A b) = (@FINITE A b).
Proof. exact (@lem3903979 (@FINITE A b)). Qed.
Lemma lem3903981 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : @FINITE A b.
Proof. exact (EQ_MP (@lem3903980 A b) (@lem3903977 A a b h1)). Qed.
Lemma lem3903987 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3903988 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term162 A _45318 _45319) = (term169 A _45318 _45319).
Proof. exact (@lem3903987 (term156 A _45319) (term159 A _45318 _45319) (term140 A _45318 _45319)). Qed.
Lemma lem3904002 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3904003 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term170 A _45318 _45319) = (term171 A _45318 _45319).
Proof. exact (@lem3904002 (term140 A _45318 _45319) (term159 A _45318 _45319)). Qed.
Lemma lem3904009 {A : Type'} (_45319 : A -> Prop) : (term124 A _45319) = (term124 A _45319).
Proof. exact (eq_refl (term124 A _45319)). Qed.
Lemma lem3904010 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term169 A _45318 _45319) = (term172 A _45318 _45319).
Proof. exact (MK_COMB (@lem3904009 A _45319) (@lem3904003 A _45318 _45319)). Qed.
Lemma lem3904014 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3904015 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term172 A _45318 _45319) = (term173 A _45318 _45319).
Proof. exact (@lem3904014 (term140 A _45318 _45319) (term156 A _45319) (term159 A _45318 _45319)). Qed.
Lemma lem3904031 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term169 A _45318 _45319) = (term173 A _45318 _45319).
Proof. exact (TRANS (@lem3904010 A _45318 _45319) (@lem3904015 A _45318 _45319)). Qed.
Lemma lem3904032 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term162 A _45318 _45319) = (term173 A _45318 _45319).
Proof. exact (TRANS (@lem3903988 A _45318 _45319) (@lem3904031 A _45318 _45319)). Qed.
Lemma lem3904033 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3904034 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term174 A _45318 _45319) = (term175 A _45318 _45319).
Proof. exact (MK_COMB (@lem3904033) (@lem3904032 A _45318 _45319)). Qed.
Lemma lem3904048 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3904049 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term139 A _45318 _45319) = (term176 A _45318 _45319).
Proof. exact (@lem3904048 (term156 A _45319) (term159 A _45318 _45319)). Qed.
Lemma lem3904055 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term177 A _45318 _45319) = (term177 A _45318 _45319).
Proof. exact (eq_refl (term177 A _45318 _45319)). Qed.
Lemma lem3904056 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term178 A _45318 _45319) = (term173 A _45318 _45319).
Proof. exact (MK_COMB (@lem3904055 A _45318 _45319) (@lem3904049 A _45318 _45319)). Qed.
Lemma lem3904067 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : ((term162 A _45318 _45319) = (term178 A _45318 _45319)) = ((term173 A _45318 _45319) = (term173 A _45318 _45319)).
Proof. exact (MK_COMB (@lem3904034 A _45318 _45319) (@lem3904056 A _45318 _45319)). Qed.
Lemma lem3904069 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3904070 (x : Prop) : (x = x) = True.
Proof. exact (@lem3904069 Prop x). Qed.
Lemma lem3904071 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : ((term173 A _45318 _45319) = (term173 A _45318 _45319)) = True.
Proof. exact (@lem3904070 (term173 A _45318 _45319)). Qed.
Lemma lem3904072 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : ((term162 A _45318 _45319) = (term178 A _45318 _45319)) = True.
Proof. exact (TRANS (@lem3904067 A _45318 _45319) (@lem3904071 A _45318 _45319)). Qed.
Lemma lem3904073 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : True = ((term162 A _45318 _45319) = (term178 A _45318 _45319)).
Proof. exact (SYM (@lem3904072 A _45318 _45319)). Qed.
Lemma lem3904074 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term162 A _45318 _45319) = (term178 A _45318 _45319).
Proof. exact (EQ_MP (@lem3904073 A _45318 _45319) (@lem0)). Qed.
Lemma lem3904075 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) (h1 : term11 A) : term178 A _45318 _45319.
Proof. exact (EQ_MP (@lem3904074 A _45318 _45319) (@lem3903859 A _45318 _45319 h1)). Qed.
Lemma lem3904077 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3904078 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term178 A _45318 _45319) = (term180 A _45318 _45319).
Proof. exact (@lem3904077 (term139 A _45318 _45319) (term140 A _45318 _45319)). Qed.
Lemma lem3904080 (a : Prop) (b : Prop) : (term181 a b) = (term182 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3904081 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term183 A _45318 _45319) = (term184 A _45318 _45319).
Proof. exact (@lem3904080 (term159 A _45318 _45319) (term156 A _45319)). Qed.
Lemma lem3904083 (a : Prop) : (term185 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3904084 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term186 A _45318 _45319) = (@SUBSET A _45318 _45319).
Proof. exact (@lem3904083 (@SUBSET A _45318 _45319)). Qed.
Lemma lem3904085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3904086 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term187 A _45318 _45319) = (term188 A _45318 _45319).
Proof. exact (MK_COMB (@lem3904085) (@lem3904084 A _45318 _45319)). Qed.
Lemma lem3904088 (a : Prop) : (term185 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3904089 {A : Type'} (_45319 : A -> Prop) : (term189 A _45319) = (@FINITE A _45319).
Proof. exact (@lem3904088 (@FINITE A _45319)). Qed.
Lemma lem3904090 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term184 A _45318 _45319) = (term145 A _45318 _45319).
Proof. exact (MK_COMB (@lem3904086 A _45318 _45319) (@lem3904089 A _45319)). Qed.
Lemma lem3904091 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term183 A _45318 _45319) = (term145 A _45318 _45319).
Proof. exact (TRANS (@lem3904081 A _45318 _45319) (@lem3904090 A _45318 _45319)). Qed.
Lemma lem3904092 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3904093 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term190 A _45318 _45319) = (term191 A _45318 _45319).
Proof. exact (MK_COMB (@lem3904092) (@lem3904091 A _45318 _45319)). Qed.
Lemma lem3904094 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term140 A _45318 _45319) = (term140 A _45318 _45319).
Proof. exact (eq_refl (term140 A _45318 _45319)). Qed.
Lemma lem3904095 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term180 A _45318 _45319) = (term27 A _45318 _45319).
Proof. exact (MK_COMB (@lem3904093 A _45318 _45319) (@lem3904094 A _45318 _45319)). Qed.
Lemma lem3904096 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) : (term178 A _45318 _45319) = (term27 A _45318 _45319).
Proof. exact (TRANS (@lem3904078 A _45318 _45319) (@lem3904095 A _45318 _45319)). Qed.
Lemma lem3904098 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term145 A a b.
Proof. exact (conj (@lem3903974 A a b h1) (@lem3903981 A a b h1)). Qed.
Lemma lem3904100 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) (h1 : term11 A) : term27 A _45318 _45319.
Proof. exact (EQ_MP (@lem3904096 A _45318 _45319) (@lem3904075 A _45318 _45319 h1)). Qed.
Lemma lem3904101 {A : Type'} (_45318 : A -> Prop) (_45319 : A -> Prop) (h1 : term11 A) : term27 A _45318 _45319.
Proof. exact (@lem3904100 A _45318 _45319 h1). Qed.
Lemma lem3904102 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term11 A) : term27 A a b.
Proof. exact (@lem3904101 A a b h1). Qed.
Lemma lem3904105 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term11 A) (h2 : term45 A a b) : term140 A a b.
Proof. exact (@lem3904102 A a b h1 (@lem3904098 A a b h2)). Qed.
Lemma lem3904106 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term11 A) (h2 : term45 A a b) : term192 A a b.
Proof. exact (fun h0 : term193 A a b => @lem3904105 A a b h1 h2). Qed.
Lemma lem3904108 (p : Prop) : (term167 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3904109 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term192 A a b) = (term140 A a b).
Proof. exact (@lem3904108 (term140 A a b)). Qed.
Lemma lem3904110 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term11 A) (h2 : term45 A a b) : term140 A a b.
Proof. exact (EQ_MP (@lem3904109 A a b) (@lem3904106 A a b h1 h2)). Qed.
Lemma lem3904112 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term140 A b a.
Proof. exact (proj2 (@lem3903684 A a b h1)). Qed.
Lemma lem3904113 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term192 A b a.
Proof. exact (fun h0 : term193 A b a => @lem3904112 A a b h1). Qed.
Lemma lem3904115 (p : Prop) : (term167 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3904116 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term192 A b a) = (term140 A b a).
Proof. exact (@lem3904115 (term140 A b a)). Qed.
Lemma lem3904117 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term140 A b a.
Proof. exact (EQ_MP (@lem3904116 A b a) (@lem3904113 A a b h1)). Qed.
Lemma lem3904133 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3904134 (_45323 : nat) (_45322 : nat) : (term194 _45322 _45323) = (term195 _45323 _45322).
Proof. exact (@lem3904133 (_45322 = _45323) (term165 _45323 _45322)). Qed.
Lemma lem3904142 (_45322 : nat) (_45323 : nat) : (term196 _45322 _45323) = (term196 _45322 _45323).
Proof. exact (eq_refl (term196 _45322 _45323)). Qed.
Lemma lem3904143 (_45323 : nat) (_45322 : nat) : (term164 _45322 _45323) = (term197 _45323 _45322).
Proof. exact (MK_COMB (@lem3904142 _45322 _45323) (@lem3904134 _45323 _45322)). Qed.
Lemma lem3904147 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3904148 (_45323 : nat) (_45322 : nat) : (term197 _45323 _45322) = (term198 _45323 _45322).
Proof. exact (@lem3904147 (_45322 = _45323) (term165 _45322 _45323) (term165 _45323 _45322)). Qed.
Lemma lem3904166 (_45323 : nat) (_45322 : nat) : (term164 _45322 _45323) = (term198 _45323 _45322).
Proof. exact (TRANS (@lem3904143 _45323 _45322) (@lem3904148 _45323 _45322)). Qed.
Lemma lem3904167 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3904168 (_45323 : nat) (_45322 : nat) : (term199 _45322 _45323) = (term200 _45323 _45322).
Proof. exact (MK_COMB (@lem3904167) (@lem3904166 _45323 _45322)). Qed.
Lemma lem3904186 (_45323 : nat) (_45322 : nat) : (term198 _45323 _45322) = (term198 _45323 _45322).
Proof. exact (eq_refl (term198 _45323 _45322)). Qed.
Lemma lem3904187 (_45323 : nat) (_45322 : nat) : ((term164 _45322 _45323) = (term198 _45323 _45322)) = ((term198 _45323 _45322) = (term198 _45323 _45322)).
Proof. exact (MK_COMB (@lem3904168 _45323 _45322) (@lem3904186 _45323 _45322)). Qed.
Lemma lem3904189 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3904190 (x : Prop) : (x = x) = True.
Proof. exact (@lem3904189 Prop x). Qed.
Lemma lem3904191 (_45323 : nat) (_45322 : nat) : ((term198 _45323 _45322) = (term198 _45323 _45322)) = True.
Proof. exact (@lem3904190 (term198 _45323 _45322)). Qed.
Lemma lem3904192 (_45323 : nat) (_45322 : nat) : ((term164 _45322 _45323) = (term198 _45323 _45322)) = True.
Proof. exact (TRANS (@lem3904187 _45323 _45322) (@lem3904191 _45323 _45322)). Qed.
Lemma lem3904193 (_45323 : nat) (_45322 : nat) : True = ((term164 _45322 _45323) = (term198 _45323 _45322)).
Proof. exact (SYM (@lem3904192 _45323 _45322)). Qed.
Lemma lem3904194 (_45323 : nat) (_45322 : nat) : (term164 _45322 _45323) = (term198 _45323 _45322).
Proof. exact (EQ_MP (@lem3904193 _45323 _45322) (@lem0)). Qed.
Lemma lem3904195 (_45323 : nat) (_45322 : nat) (h1 : term39) : term198 _45323 _45322.
Proof. exact (EQ_MP (@lem3904194 _45323 _45322) (@lem3903879 _45322 _45323 h1)). Qed.
Lemma lem3904197 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3904198 (_45322 : nat) (_45323 : nat) : (term198 _45323 _45322) = (term201 _45322 _45323).
Proof. exact (@lem3904197 (term63 _45323 _45322) (_45322 = _45323)). Qed.
Lemma lem3904200 (a : Prop) (b : Prop) : (term181 a b) = (term182 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3904201 (_45323 : nat) (_45322 : nat) : (term202 _45323 _45322) = (term203 _45323 _45322).
Proof. exact (@lem3904200 (term165 _45322 _45323) (term165 _45323 _45322)). Qed.
Lemma lem3904203 (a : Prop) : (term185 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3904204 (_45322 : nat) (_45323 : nat) : (term204 _45322 _45323) = (Peano.le _45322 _45323).
Proof. exact (@lem3904203 (Peano.le _45322 _45323)). Qed.
Lemma lem3904205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3904206 (_45322 : nat) (_45323 : nat) : (term205 _45322 _45323) = (term206 _45322 _45323).
Proof. exact (MK_COMB (@lem3904205) (@lem3904204 _45322 _45323)). Qed.
Lemma lem3904208 (a : Prop) : (term185 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3904209 (_45323 : nat) (_45322 : nat) : (term204 _45323 _45322) = (Peano.le _45323 _45322).
Proof. exact (@lem3904208 (Peano.le _45323 _45322)). Qed.
Lemma lem3904210 (_45323 : nat) (_45322 : nat) : (term203 _45323 _45322) = (term35 _45323 _45322).
Proof. exact (MK_COMB (@lem3904206 _45322 _45323) (@lem3904209 _45323 _45322)). Qed.
Lemma lem3904211 (_45323 : nat) (_45322 : nat) : (term202 _45323 _45322) = (term35 _45323 _45322).
Proof. exact (TRANS (@lem3904201 _45323 _45322) (@lem3904210 _45323 _45322)). Qed.
Lemma lem3904212 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3904213 (_45323 : nat) (_45322 : nat) : (term207 _45323 _45322) = (term208 _45323 _45322).
Proof. exact (MK_COMB (@lem3904212) (@lem3904211 _45323 _45322)). Qed.
Lemma lem3904214 (_45322 : nat) (_45323 : nat) : (_45322 = _45323) = (_45322 = _45323).
Proof. exact (eq_refl (_45322 = _45323)). Qed.
Lemma lem3904215 (_45322 : nat) (_45323 : nat) : (term201 _45322 _45323) = (term209 _45322 _45323).
Proof. exact (MK_COMB (@lem3904213 _45323 _45322) (@lem3904214 _45322 _45323)). Qed.
Lemma lem3904216 (_45322 : nat) (_45323 : nat) : (term198 _45323 _45322) = (term209 _45322 _45323).
Proof. exact (TRANS (@lem3904198 _45322 _45323) (@lem3904215 _45322 _45323)). Qed.
Lemma lem3904218 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term11 A) (h2 : term45 A a b) : term210 A b a.
Proof. exact (conj (@lem3904110 A a b h1 h2) (@lem3904117 A a b h2)). Qed.
Lemma lem3904220 (_45322 : nat) (_45323 : nat) (h1 : term39) : term209 _45322 _45323.
Proof. exact (EQ_MP (@lem3904216 _45322 _45323) (@lem3904195 _45323 _45322 h1)). Qed.
Lemma lem3904221 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term39) : term211 A a b.
Proof. exact (@lem3904220 (@CARD A a) (@CARD A b) h1). Qed.
Lemma lem3904224 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term11 A) (h2 : term39) (h3 : term45 A a b) : (@CARD A a) = (@CARD A b).
Proof. exact (@lem3904221 A a b h2 (@lem3904218 A a b h1 h3)). Qed.
Lemma lem3904225 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term11 A) (h2 : term39) (h3 : term45 A a b) : term212 A a b.
Proof. exact (fun h0 : term160 A a b => @lem3904224 A a b h1 h2 h3). Qed.
Lemma lem3904227 (p : Prop) : (term167 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3904228 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term212 A a b) = ((@CARD A a) = (@CARD A b)).
Proof. exact (@lem3904227 ((@CARD A a) = (@CARD A b))). Qed.
Lemma lem3904229 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term11 A) (h2 : term39) (h3 : term45 A a b) : (@CARD A a) = (@CARD A b).
Proof. exact (EQ_MP (@lem3904228 A a b) (@lem3904225 A a b h1 h2 h3)). Qed.
Lemma lem3904245 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3904246 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term158 A _45316 _45317) = (term213 A _45316 _45317).
Proof. exact (@lem3904245 (term160 A _45316 _45317) (term159 A _45316 _45317) (_45316 = _45317)). Qed.
Lemma lem3904262 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3904263 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term214 A _45316 _45317) = (term215 A _45316 _45317).
Proof. exact (@lem3904262 (_45316 = _45317) (term159 A _45316 _45317)). Qed.
Lemma lem3904271 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term216 A _45316 _45317) = (term216 A _45316 _45317).
Proof. exact (eq_refl (term216 A _45316 _45317)). Qed.
Lemma lem3904272 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term213 A _45316 _45317) = (term217 A _45316 _45317).
Proof. exact (MK_COMB (@lem3904271 A _45316 _45317) (@lem3904263 A _45316 _45317)). Qed.
Lemma lem3904276 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3904277 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term217 A _45316 _45317) = (term218 A _45316 _45317).
Proof. exact (@lem3904276 (_45316 = _45317) (term160 A _45316 _45317) (term159 A _45316 _45317)). Qed.
Lemma lem3904297 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term213 A _45316 _45317) = (term218 A _45316 _45317).
Proof. exact (TRANS (@lem3904272 A _45316 _45317) (@lem3904277 A _45316 _45317)). Qed.
Lemma lem3904298 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term158 A _45316 _45317) = (term218 A _45316 _45317).
Proof. exact (TRANS (@lem3904246 A _45316 _45317) (@lem3904297 A _45316 _45317)). Qed.
Lemma lem3904299 {A : Type'} (_45317 : A -> Prop) : (term124 A _45317) = (term124 A _45317).
Proof. exact (eq_refl (term124 A _45317)). Qed.
Lemma lem3904300 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term161 A _45316 _45317) = (term219 A _45316 _45317).
Proof. exact (MK_COMB (@lem3904299 A _45317) (@lem3904298 A _45316 _45317)). Qed.
Lemma lem3904304 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3904305 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term219 A _45316 _45317) = (term220 A _45316 _45317).
Proof. exact (@lem3904304 (_45316 = _45317) (term156 A _45317) (term221 A _45316 _45317)). Qed.
Lemma lem3904321 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3904322 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term222 A _45316 _45317) = (term223 A _45316 _45317).
Proof. exact (@lem3904321 (term160 A _45316 _45317) (term156 A _45317) (term159 A _45316 _45317)). Qed.
Lemma lem3904340 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term224 A _45316 _45317) = (term224 A _45316 _45317).
Proof. exact (eq_refl (term224 A _45316 _45317)). Qed.
Lemma lem3904341 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term220 A _45316 _45317) = (term225 A _45316 _45317).
Proof. exact (MK_COMB (@lem3904340 A _45316 _45317) (@lem3904322 A _45316 _45317)). Qed.
Lemma lem3904352 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term219 A _45316 _45317) = (term225 A _45316 _45317).
Proof. exact (TRANS (@lem3904305 A _45316 _45317) (@lem3904341 A _45316 _45317)). Qed.
Lemma lem3904353 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term161 A _45316 _45317) = (term225 A _45316 _45317).
Proof. exact (TRANS (@lem3904300 A _45316 _45317) (@lem3904352 A _45316 _45317)). Qed.
Lemma lem3904354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3904355 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term226 A _45316 _45317) = (term227 A _45316 _45317).
Proof. exact (MK_COMB (@lem3904354) (@lem3904353 A _45316 _45317)). Qed.
Lemma lem3904381 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3904382 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term123 A _45316 _45317) = (term221 A _45316 _45317).
Proof. exact (@lem3904381 (term160 A _45316 _45317) (term159 A _45316 _45317)). Qed.
Lemma lem3904390 {A : Type'} (_45317 : A -> Prop) : (term124 A _45317) = (term124 A _45317).
Proof. exact (eq_refl (term124 A _45317)). Qed.
Lemma lem3904391 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term126 A _45316 _45317) = (term222 A _45316 _45317).
Proof. exact (MK_COMB (@lem3904390 A _45317) (@lem3904382 A _45316 _45317)). Qed.
Lemma lem3904395 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3904396 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term222 A _45316 _45317) = (term223 A _45316 _45317).
Proof. exact (@lem3904395 (term160 A _45316 _45317) (term156 A _45317) (term159 A _45316 _45317)). Qed.
Lemma lem3904414 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term126 A _45316 _45317) = (term223 A _45316 _45317).
Proof. exact (TRANS (@lem3904391 A _45316 _45317) (@lem3904396 A _45316 _45317)). Qed.
Lemma lem3904415 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term224 A _45316 _45317) = (term224 A _45316 _45317).
Proof. exact (eq_refl (term224 A _45316 _45317)). Qed.
Lemma lem3904416 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term228 A _45316 _45317) = (term225 A _45316 _45317).
Proof. exact (MK_COMB (@lem3904415 A _45316 _45317) (@lem3904414 A _45316 _45317)). Qed.
Lemma lem3904427 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : ((term161 A _45316 _45317) = (term228 A _45316 _45317)) = ((term225 A _45316 _45317) = (term225 A _45316 _45317)).
Proof. exact (MK_COMB (@lem3904355 A _45316 _45317) (@lem3904416 A _45316 _45317)). Qed.
Lemma lem3904429 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3904430 (x : Prop) : (x = x) = True.
Proof. exact (@lem3904429 Prop x). Qed.
Lemma lem3904431 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : ((term225 A _45316 _45317) = (term225 A _45316 _45317)) = True.
Proof. exact (@lem3904430 (term225 A _45316 _45317)). Qed.
Lemma lem3904432 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : ((term161 A _45316 _45317) = (term228 A _45316 _45317)) = True.
Proof. exact (TRANS (@lem3904427 A _45316 _45317) (@lem3904431 A _45316 _45317)). Qed.
Lemma lem3904433 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : True = ((term161 A _45316 _45317) = (term228 A _45316 _45317)).
Proof. exact (SYM (@lem3904432 A _45316 _45317)). Qed.
Lemma lem3904434 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term161 A _45316 _45317) = (term228 A _45316 _45317).
Proof. exact (EQ_MP (@lem3904433 A _45316 _45317) (@lem0)). Qed.
Lemma lem3904435 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) (h1 : term12 A) : term228 A _45316 _45317.
Proof. exact (EQ_MP (@lem3904434 A _45316 _45317) (@lem3903847 A _45316 _45317 h1)). Qed.
Lemma lem3904437 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3904438 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term228 A _45316 _45317) = (term229 A _45316 _45317).
Proof. exact (@lem3904437 (term126 A _45316 _45317) (_45316 = _45317)). Qed.
Lemma lem3904440 (a : Prop) (b : Prop) : (term181 a b) = (term182 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3904441 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term230 A _45316 _45317) = (term231 A _45316 _45317).
Proof. exact (@lem3904440 (term156 A _45317) (term123 A _45316 _45317)). Qed.
Lemma lem3904443 (a : Prop) : (term185 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3904444 {A : Type'} (_45317 : A -> Prop) : (term189 A _45317) = (@FINITE A _45317).
Proof. exact (@lem3904443 (@FINITE A _45317)). Qed.
Lemma lem3904445 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3904446 {A : Type'} (_45317 : A -> Prop) : (term232 A _45317) = (term233 A _45317).
Proof. exact (MK_COMB (@lem3904445) (@lem3904444 A _45317)). Qed.
Lemma lem3904448 (a : Prop) (b : Prop) : (term181 a b) = (term182 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3904449 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term234 A _45316 _45317) = (term235 A _45316 _45317).
Proof. exact (@lem3904448 (term159 A _45316 _45317) (term160 A _45316 _45317)). Qed.
Lemma lem3904451 (a : Prop) : (term185 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3904452 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term186 A _45316 _45317) = (@SUBSET A _45316 _45317).
Proof. exact (@lem3904451 (@SUBSET A _45316 _45317)). Qed.
Lemma lem3904453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3904454 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term187 A _45316 _45317) = (term188 A _45316 _45317).
Proof. exact (MK_COMB (@lem3904453) (@lem3904452 A _45316 _45317)). Qed.
Lemma lem3904456 (a : Prop) : (term185 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3904457 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term236 A _45316 _45317) = ((@CARD A _45316) = (@CARD A _45317)).
Proof. exact (@lem3904456 ((@CARD A _45316) = (@CARD A _45317))). Qed.
Lemma lem3904458 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term235 A _45316 _45317) = (term128 A _45316 _45317).
Proof. exact (MK_COMB (@lem3904454 A _45316 _45317) (@lem3904457 A _45316 _45317)). Qed.
Lemma lem3904459 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term234 A _45316 _45317) = (term128 A _45316 _45317).
Proof. exact (TRANS (@lem3904449 A _45316 _45317) (@lem3904458 A _45316 _45317)). Qed.
Lemma lem3904460 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term231 A _45316 _45317) = (term133 A _45316 _45317).
Proof. exact (MK_COMB (@lem3904446 A _45317) (@lem3904459 A _45316 _45317)). Qed.
Lemma lem3904461 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term230 A _45316 _45317) = (term133 A _45316 _45317).
Proof. exact (TRANS (@lem3904441 A _45316 _45317) (@lem3904460 A _45316 _45317)). Qed.
Lemma lem3904462 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3904463 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term237 A _45316 _45317) = (term238 A _45316 _45317).
Proof. exact (MK_COMB (@lem3904462) (@lem3904461 A _45316 _45317)). Qed.
Lemma lem3904464 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (_45316 = _45317) = (_45316 = _45317).
Proof. exact (eq_refl (_45316 = _45317)). Qed.
Lemma lem3904465 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term229 A _45316 _45317) = (term31 A _45316 _45317).
Proof. exact (MK_COMB (@lem3904463 A _45316 _45317) (@lem3904464 A _45316 _45317)). Qed.
Lemma lem3904466 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) : (term228 A _45316 _45317) = (term31 A _45316 _45317).
Proof. exact (TRANS (@lem3904438 A _45316 _45317) (@lem3904465 A _45316 _45317)). Qed.
Lemma lem3904468 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term11 A) (h2 : term39) (h3 : term45 A a b) : term128 A a b.
Proof. exact (conj (@lem3903967 A a b h3) (@lem3904229 A a b h1 h2 h3)). Qed.
Lemma lem3904469 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term11 A) (h2 : term39) (h3 : term45 A a b) : term133 A a b.
Proof. exact (conj (@lem3903960 A a b h3) (@lem3904468 A a b h1 h2 h3)). Qed.
Lemma lem3904471 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) (h1 : term12 A) : term31 A _45316 _45317.
Proof. exact (EQ_MP (@lem3904466 A _45316 _45317) (@lem3904435 A _45316 _45317 h1)). Qed.
Lemma lem3904472 {A : Type'} (_45316 : A -> Prop) (_45317 : A -> Prop) (h1 : term12 A) : term31 A _45316 _45317.
Proof. exact (@lem3904471 A _45316 _45317 h1). Qed.
Lemma lem3904473 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term12 A) : term31 A a b.
Proof. exact (@lem3904472 A a b h1). Qed.
Lemma lem3904476 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term12 A) (h2 : term11 A) (h3 : term39) (h4 : term45 A a b) : a = b.
Proof. exact (@lem3904473 A a b h1 (@lem3904469 A a b h2 h3 h4)). Qed.
Lemma lem3904477 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term12 A) (h2 : term11 A) (h3 : term39) (h4 : term45 A a b) : term239 A a b.
Proof. exact (fun h0 : term163 A a b => @lem3904476 A a b h1 h2 h3 h4). Qed.
Lemma lem3904479 (p : Prop) : (term167 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3904480 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term239 A a b) = (a = b).
Proof. exact (@lem3904479 (a = b)). Qed.
Lemma lem3904481 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term12 A) (h2 : term11 A) (h3 : term39) (h4 : term45 A a b) : a = b.
Proof. exact (EQ_MP (@lem3904480 A a b) (@lem3904477 A a b h1 h2 h3 h4)). Qed.
Lemma lem3904484 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3904486 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term163 A a b) = (term240 A a b).
Proof. exact (@lem3904484 (a = b)). Qed.
Lemma lem3904489 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term240 A a b.
Proof. exact (EQ_MP (@lem3904486 A a b) (@lem3903861 A a b h1)). Qed.
Lemma lem3904492 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term12 A) (h2 : term11 A) (h3 : term39) (h4 : term45 A a b) : False.
Proof. exact (@lem3904489 A a b h4 (@lem3904481 A a b h1 h2 h3 h4)). Qed.
Lemma lem3904493 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term12 A) (h2 : term11 A) (h3 : term39) (h4 : term45 A a b) : term241.
Proof. exact (fun h0 : ~ False => @lem3904492 A a b h1 h2 h3 h4). Qed.
Lemma lem3904495 (p : Prop) : (term167 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3904496 : term241 = False.
Proof. exact (@lem3904495 False). Qed.
Lemma lem3904497 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term12 A) (h2 : term11 A) (h3 : term39) (h4 : term45 A a b) : False.
Proof. exact (EQ_MP (@lem3904496) (@lem3904493 A a b h1 h2 h3 h4)). Qed.
Lemma lem3904498 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term12 A) (h2 : term11 A) (h3 : term39) (h4 : term45 A a b) : (term45 A a b) = False.
Proof. exact (prop_ext (fun h5 : term45 A a b => @lem3904497 A a b h1 h2 h3 h4) (fun h5 : False => @lem3903681 A a b h4)). Qed.
Lemma lem3904499 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term12 A) (h2 : term11 A) (h3 : term39) (h4 : term45 A a b) : False.
Proof. exact (EQ_MP (@lem3904498 A a b h1 h2 h3 h4) (@lem3903681 A a b h4)). Qed.
Lemma lem3904500 {A : Type'} (a : A -> Prop) (h1 : term12 A) (h2 : term11 A) (h3 : term39) (h4 : term55 A a) : False.
Proof. exact (ex_elim (@lem3903504 A a h4) (fun b : A -> Prop => fun h0 : term54 A a b => @lem3904499 A a b h1 h2 h3 h0)). Qed.
Lemma lem3904501 {A : Type'} (h1 : term12 A) (h2 : term11 A) (h3 : term39) (h4 : term10 A) : False.
Proof. exact (ex_elim (@lem3903048 A h4) (fun a : A -> Prop => fun h0 : term60 A a => @lem3904500 A a h1 h2 h3 h0)). Qed.
Lemma lem3904502 {A : Type'} (h1 : term12 A) (h2 : term39) (h3 : term10 A) : term17 A.
Proof. exact (fun h0 : term11 A => @lem3904501 A h1 h0 h2 h3). Qed.
Lemma lem3904503 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem69 (term11 A)). Qed.
Lemma lem3904504 {A : Type'} (h1 : term12 A) (h2 : term39) (h3 : term10 A) : term18 A.
Proof. exact (EQ_MP (@lem3904503 A) (@lem3904502 A h1 h2 h3)). Qed.
Lemma lem3904505 {A : Type'} (h1 : term39) (h2 : term10 A) : term21 A.
Proof. exact (fun h0 : term12 A => @lem3904504 A h0 h1 h2). Qed.
Lemma lem3904506 {A : Type'} (h1 : term10 A) : term24 A.
Proof. exact (fun h0 : term39 => @lem3904505 A h0 h1). Qed.
Lemma lem3904507 {A : Type'} : term26 A.
Proof. exact (fun h0 : term10 A => @lem3904506 A h0). Qed.
Lemma lem3904508 {A : Type'} : term13 A.
Proof. exact (EQ_MP (@lem3902952 A) (@lem3904507 A)). Qed.
Lemma lem3904510 {A : Type'} : term13 A.
Proof. exact (@lem3902720 A (@lem3904508 A)). Qed.
Lemma lem3904511 {A : Type'} (h1 : term10 A) : term23 A.
Proof. exact (@lem3904510 A (@lem3902697 A h1)). Qed.
Lemma lem3904512 {A : Type'} (h1 : term10 A) : term20 A.
Proof. exact (@lem3904511 A h1 (@lem92426)). Qed.
Lemma lem3904513 {A : Type'} (h1 : term10 A) : term17 A.
Proof. exact (@lem3904512 A h1 (@lem3902701 A)). Qed.
Lemma lem3904514 {A : Type'} (h1 : term10 A) : False.
Proof. exact (@lem3904513 A h1 (@lem3902698 A)). Qed.
Lemma lem3904515 {A : Type'} (h1 : term10 A) : (term10 A) = False.
Proof. exact (prop_ext (fun h2 : term10 A => @lem3904514 A h1) (fun h2 : False => @lem3902697 A h1)). Qed.
Lemma lem3904516 {A : Type'} (h1 : term10 A) : False.
Proof. exact (EQ_MP (@lem3904515 A h1) (@lem3902697 A h1)). Qed.
Lemma lem3904517 {A : Type'} : term9 A.
Proof. exact (fun h0 : term10 A => @lem3904516 A h0). Qed.
Lemma lem3904518 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem3902696 A) (@lem3904517 A)). Qed.
