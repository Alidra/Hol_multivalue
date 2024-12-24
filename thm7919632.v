Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7919632_term_abbrevs.
Require Import DIMINDEX_GE_1_spec.
Require Import DISJ_ACI_spec.
Require Import IN_NUMSEG_spec.
Require Import LE_1_spec.
Require Import LE_REFL_spec.
Require Import MULT_EQ_0_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17784_spec.
Require Import thm1842_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
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
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem7917690 (n : nat) : term0 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem7917691 (n : nat) : (term0 n) = (Peano.le n n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem7917692 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem7917691 n) (@lem7917690 n)). Qed.
Lemma lem7917693 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem7917695 (m : nat) : term1 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7917696 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem7917697 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem7917696 m) (@lem7917695 m)). Qed.
Lemma lem7917698 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem7917697 m n). Qed.
Lemma lem7917699 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem7917700 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem7917699 m n) (@lem7917698 m n)). Qed.
Lemma lem7917701 (m : nat) (n : nat) (p : nat) : term5 m n p.
Proof. exact (@lem7917700 m n p). Qed.
Lemma lem7917702 (m : nat) (p : nat) (n : nat) : (term5 m n p) = ((term6 p m n) = (term7 m p n)).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem7917705 (m : nat) (p : nat) (n : nat) : (term6 p m n) = (term7 m p n).
Proof. exact (EQ_MP (@lem7917702 m p n) (@lem7917701 m n p)). Qed.
Lemma lem7917706 {A B : Type'} : (term8 A B) = (term9 A B).
Proof. exact (@lem7917705 term10 term10 (term11 A B)). Qed.
Lemma lem7917710 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem7917693 n) (@lem7917692 n)). Qed.
Lemma lem7917711 : term12 = True.
Proof. exact (@lem7917710 term10). Qed.
Lemma lem7917712 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7917713 : term13 = (and True).
Proof. exact (MK_COMB (@lem7917712) (@lem7917711)). Qed.
Lemma lem7917716 {A B : Type'} : (term14 A B) = (term14 A B).
Proof. exact (eq_refl (term14 A B)). Qed.
Lemma lem7917717 {A B : Type'} : (term9 A B) = (term15 A B).
Proof. exact (MK_COMB (@lem7917713) (@lem7917716 A B)). Qed.
Lemma lem7917719 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7917720 {A B : Type'} : (term15 A B) = (term14 A B).
Proof. exact (@lem7917719 (term14 A B)). Qed.
Lemma lem7917723 {A B : Type'} : (term9 A B) = (term14 A B).
Proof. exact (TRANS (@lem7917717 A B) (@lem7917720 A B)). Qed.
Lemma lem7917724 {A B : Type'} : (term8 A B) = (term14 A B).
Proof. exact (TRANS (@lem7917706 A B) (@lem7917723 A B)). Qed.
Lemma lem7917725 {A B : Type'} : (term14 A B) = (term8 A B).
Proof. exact (SYM (@lem7917724 A B)). Qed.
Lemma lem7917727 (p : Prop) : p = (term16 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7917728 {A B : Type'} : (term14 A B) = (term17 A B).
Proof. exact (@lem7917727 (term14 A B)). Qed.
Lemma lem7917729 {A B : Type'} : (term17 A B) = (term14 A B).
Proof. exact (SYM (@lem7917728 A B)). Qed.
Lemma lem7917730 {A B : Type'} (h1 : term18 A B) : term18 A B.
Proof. exact (h1). Qed.
Lemma lem7917732 {B : Type'} : term19 B.
Proof. exact (@lem7594654 B). Qed.
Lemma lem7917735 {A B : Type'} (h1 : term20 A B) : term20 A B.
Proof. exact (h1). Qed.
Lemma lem7917736 {A B : Type'} : term21 A B.
Proof. exact (fun h0 : term20 A B => @lem7917735 A B h0). Qed.
Lemma lem7917737 {A B : Type'} (h1 : term21 A B) : term21 A B.
Proof. exact (h1). Qed.
Lemma lem7917738 {A B : Type'} (h1 : term20 A B) : term20 A B.
Proof. exact (h1). Qed.
Lemma lem7917739 {A B : Type'} (h1 : term20 A B) (h2 : term21 A B) : term20 A B.
Proof. exact (@lem7917737 A B h2 (@lem7917738 A B h1)). Qed.
Lemma lem7917740 {A B : Type'} (h1 : term20 A B) : term22 A B.
Proof. exact (fun h0 : term21 A B => @lem7917739 A B h1 h0). Qed.
Lemma lem7917741 {A B : Type'} (h1 : term21 A B) : term21 A B.
Proof. exact (h1). Qed.
Lemma lem7917742 {A B : Type'} (h1 : term20 A B) (h2 : term21 A B) : term20 A B.
Proof. exact (@lem7917740 A B h1 (@lem7917741 A B h2)). Qed.
Lemma lem7917743 {A B : Type'} (h1 : term21 A B) : term21 A B.
Proof. exact (fun h0 : term20 A B => @lem7917742 A B h0 h1). Qed.
Lemma lem7917744 {A B : Type'} : term23 A B.
Proof. exact (fun h0 : term21 A B => @lem7917743 A B h0). Qed.
Lemma lem7917747 {A B : Type'} : term21 A B.
Proof. exact (@lem7917744 A B (@lem7917736 A B)). Qed.
Lemma lem7917748 {A B : Type'} : term21 A B.
Proof. exact (@lem7917747 A B). Qed.
Lemma lem7917776 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7917777 : term24 = term25.
Proof. exact (@lem7917776 term26). Qed.
Lemma lem7917824 {B : Type'} : (term27 B) = (term27 B).
Proof. exact (eq_refl (term27 B)). Qed.
Lemma lem7917825 {B : Type'} : (term28 B) = (term29 B).
Proof. exact (MK_COMB (@lem7917824 B) (@lem7917777)). Qed.
Lemma lem7917828 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (eq_refl (term27 A)). Qed.
Lemma lem7917829 {A B : Type'} : (term30 A B) = (term31 A B).
Proof. exact (MK_COMB (@lem7917828 A) (@lem7917825 B)). Qed.
Lemma lem7917832 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem7917833 {A B : Type'} : (term33 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem7917832) (@lem7917829 A B)). Qed.
Lemma lem7917836 {A B : Type'} : (term35 A B) = (term35 A B).
Proof. exact (eq_refl (term35 A B)). Qed.
Lemma lem7917843 {A B : Type'} : (term20 A B) = (term36 A B).
Proof. exact (MK_COMB (@lem7917836 A B) (@lem7917833 A B)). Qed.
Lemma lem7917850 (n : nat) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem7917851 : term38 = term38.
Proof. exact (fun_ext (fun n : nat => @lem7917850 n)). Qed.
Lemma lem7917852 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7917853 : term39 = term39.
Proof. exact (MK_COMB (@lem7917852) (@lem7917851)). Qed.
Lemma lem7917858 (n : nat) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem7917859 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem7917858 n)). Qed.
Lemma lem7917860 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7917861 : term42 = term42.
Proof. exact (MK_COMB (@lem7917860) (@lem7917859)). Qed.
Lemma lem7917862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7917863 : term43 = term43.
Proof. exact (MK_COMB (@lem7917862) (@lem7917861)). Qed.
Lemma lem7917864 : term44 = term44.
Proof. exact (MK_COMB (@lem7917863) (@lem7917853)). Qed.
Lemma lem7917869 (n : nat) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem7917870 : term46 = term46.
Proof. exact (fun_ext (fun n : nat => @lem7917869 n)). Qed.
Lemma lem7917871 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7917872 : term47 = term47.
Proof. exact (MK_COMB (@lem7917871) (@lem7917870)). Qed.
Lemma lem7917873 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7917874 : term48 = term48.
Proof. exact (MK_COMB (@lem7917873) (@lem7917872)). Qed.
Lemma lem7917875 : term49 = term49.
Proof. exact (MK_COMB (@lem7917874) (@lem7917864)). Qed.
Lemma lem7917882 (n : nat) : (term50 n) = (term50 n).
Proof. exact (eq_refl (term50 n)). Qed.
Lemma lem7917883 : term51 = term51.
Proof. exact (fun_ext (fun n : nat => @lem7917882 n)). Qed.
Lemma lem7917884 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7917885 : term52 = term52.
Proof. exact (MK_COMB (@lem7917884) (@lem7917883)). Qed.
Lemma lem7917886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7917887 : term53 = term53.
Proof. exact (MK_COMB (@lem7917886) (@lem7917885)). Qed.
Lemma lem7917888 : term54 = term54.
Proof. exact (MK_COMB (@lem7917887) (@lem7917875)). Qed.
Lemma lem7917895 (n : nat) : (term55 n) = (term55 n).
Proof. exact (eq_refl (term55 n)). Qed.
Lemma lem7917896 : term56 = term56.
Proof. exact (fun_ext (fun n : nat => @lem7917895 n)). Qed.
Lemma lem7917897 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7917898 : term57 = term57.
Proof. exact (MK_COMB (@lem7917897) (@lem7917896)). Qed.
Lemma lem7917899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7917900 : term58 = term58.
Proof. exact (MK_COMB (@lem7917899) (@lem7917898)). Qed.
Lemma lem7917901 : term59 = term59.
Proof. exact (MK_COMB (@lem7917900) (@lem7917888)). Qed.
Lemma lem7917908 (n : nat) : (term60 n) = (term60 n).
Proof. exact (eq_refl (term60 n)). Qed.
Lemma lem7917909 : term61 = term61.
Proof. exact (fun_ext (fun n : nat => @lem7917908 n)). Qed.
Lemma lem7917910 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7917911 : term62 = term62.
Proof. exact (MK_COMB (@lem7917910) (@lem7917909)). Qed.
Lemma lem7917912 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7917913 : term63 = term63.
Proof. exact (MK_COMB (@lem7917912) (@lem7917911)). Qed.
Lemma lem7917914 : term26 = term26.
Proof. exact (MK_COMB (@lem7917913) (@lem7917901)). Qed.
Lemma lem7917915 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7917916 : term25 = term25.
Proof. exact (MK_COMB (@lem7917915) (@lem7917914)). Qed.
Lemma lem7917917 {B : Type'} (s : B -> Prop) : (term64 B s) = (term64 B s).
Proof. exact (eq_refl (term64 B s)). Qed.
Lemma lem7917918 {B : Type'} : (term65 B) = (term65 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem7917917 B s)). Qed.
Lemma lem7917919 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7917920 {B : Type'} : (term19 B) = (term19 B).
Proof. exact (MK_COMB (@lem7917919 B) (@lem7917918 B)). Qed.
Lemma lem7917921 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7917922 {B : Type'} : (term27 B) = (term27 B).
Proof. exact (MK_COMB (@lem7917921) (@lem7917920 B)). Qed.
Lemma lem7917923 {B : Type'} : (term29 B) = (term29 B).
Proof. exact (MK_COMB (@lem7917922 B) (@lem7917916)). Qed.
Lemma lem7917924 {A : Type'} (s : A -> Prop) : (term64 A s) = (term64 A s).
Proof. exact (eq_refl (term64 A s)). Qed.
Lemma lem7917925 {A : Type'} : (term65 A) = (term65 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7917924 A s)). Qed.
Lemma lem7917926 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7917927 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7917926 A) (@lem7917925 A)). Qed.
Lemma lem7917928 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7917929 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (MK_COMB (@lem7917928) (@lem7917927 A)). Qed.
Lemma lem7917930 {A B : Type'} : (term31 A B) = (term31 A B).
Proof. exact (MK_COMB (@lem7917929 A) (@lem7917923 B)). Qed.
Lemma lem7917939 (m : nat) (n : nat) : (((Nat.mul m n) = (NUMERAL 0)) = (term66 m n)) = (((Nat.mul m n) = (NUMERAL 0)) = (term66 m n)).
Proof. exact (eq_refl (((Nat.mul m n) = (NUMERAL 0)) = (term66 m n))). Qed.
Lemma lem7917940 (m : nat) : (term67 m) = (term67 m).
Proof. exact (fun_ext (fun n : nat => @lem7917939 m n)). Qed.
Lemma lem7917941 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7917942 (m : nat) : (term68 m) = (term68 m).
Proof. exact (MK_COMB (@lem7917941) (@lem7917940 m)). Qed.
Lemma lem7917943 : term69 = term69.
Proof. exact (fun_ext (fun m : nat => @lem7917942 m)). Qed.
Lemma lem7917944 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7917945 : term70 = term70.
Proof. exact (MK_COMB (@lem7917944) (@lem7917943)). Qed.
Lemma lem7917946 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7917947 : term32 = term32.
Proof. exact (MK_COMB (@lem7917946) (@lem7917945)). Qed.
Lemma lem7917948 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem7917947) (@lem7917930 A B)). Qed.
Lemma lem7917953 {A B : Type'} : (term35 A B) = (term35 A B).
Proof. exact (eq_refl (term35 A B)). Qed.
Lemma lem7917954 {A B : Type'} : (term36 A B) = (term36 A B).
Proof. exact (MK_COMB (@lem7917953 A B) (@lem7917948 A B)). Qed.
Lemma lem7918049 {A B : Type'} : (term20 A B) = (term36 A B).
Proof. exact (TRANS (@lem7917843 A B) (@lem7917954 A B)). Qed.
Lemma lem7918050 {A B : Type'} : (term36 A B) = (term20 A B).
Proof. exact (SYM (@lem7918049 A B)). Qed.
Lemma lem7918052 (h1 : term70) : term70.
Proof. exact (h1). Qed.
Lemma lem7918053 {A : Type'} (h1 : term19 A) : term19 A.
Proof. exact (h1). Qed.
Lemma lem7918054 {B : Type'} (h1 : term19 B) : term19 B.
Proof. exact (h1). Qed.
Lemma lem7918055 (h1 : term26) : term26.
Proof. exact (h1). Qed.
Lemma lem7918061 {A B : Type'} (h1 : term18 A B) : term18 A B.
Proof. exact (h1). Qed.
Lemma lem7918072 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (@lem17160 (m = (NUMERAL 0)) (n = (NUMERAL 0))). Qed.
Lemma lem7918078 (m : nat) (n : nat) : (term73 m n) = (term73 m n).
Proof. exact (eq_refl (term73 m n)). Qed.
Lemma lem7918080 (m : nat) (n : nat) : (term74 m n) = (term74 m n).
Proof. exact (eq_refl (term74 m n)). Qed.
Lemma lem7918081 (m : nat) (n : nat) : (term75 m n) = (term76 m n).
Proof. exact (MK_COMB (@lem7918080 m n) (@lem7918072 m n)). Qed.
Lemma lem7918082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7918083 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem7918082) (@lem7918081 m n)). Qed.
Lemma lem7918084 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (MK_COMB (@lem7918083 m n) (@lem7918078 m n)). Qed.
Lemma lem7918085 (m : nat) (n : nat) : (((Nat.mul m n) = (NUMERAL 0)) = (term66 m n)) = (term79 m n).
Proof. exact (@lem17784 ((Nat.mul m n) = (NUMERAL 0)) (term66 m n)). Qed.
Lemma lem7918086 (m : nat) (n : nat) : (((Nat.mul m n) = (NUMERAL 0)) = (term66 m n)) = (term80 m n).
Proof. exact (TRANS (@lem7918085 m n) (@lem7918084 m n)). Qed.
Lemma lem7918087 (m : nat) : (term67 m) = (term81 m).
Proof. exact (fun_ext (fun n : nat => @lem7918086 m n)). Qed.
Lemma lem7918088 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918089 (m : nat) : (term68 m) = (term82 m).
Proof. exact (MK_COMB (@lem7918088) (@lem7918087 m)). Qed.
Lemma lem7918090 : term69 = term83.
Proof. exact (fun_ext (fun m : nat => @lem7918089 m)). Qed.
Lemma lem7918091 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918092 : term70 = term84.
Proof. exact (MK_COMB (@lem7918091) (@lem7918090)). Qed.
Lemma lem7918098 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term85 A P Q) = (term86 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7918099 (P : nat -> Prop) (Q : nat -> Prop) : (term87 P Q) = (term88 P Q).
Proof. exact (@lem7918098 nat P Q). Qed.
Lemma lem7918100 (m : nat) : (term89 m) = (term90 m).
Proof. exact (@lem7918099 (term91 m) (term92 m)). Qed.
Lemma lem7918101 (m : nat) (n : nat) : (term93 m n) = (term76 m n).
Proof. exact (eq_refl (term93 m n)). Qed.
Lemma lem7918102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7918103 (m : nat) (n : nat) : (term94 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem7918102) (@lem7918101 m n)). Qed.
Lemma lem7918104 (m : nat) (n : nat) : (term95 m n) = (term73 m n).
Proof. exact (eq_refl (term95 m n)). Qed.
Lemma lem7918105 (m : nat) (n : nat) : (term96 m n) = (term80 m n).
Proof. exact (MK_COMB (@lem7918103 m n) (@lem7918104 m n)). Qed.
Lemma lem7918106 (m : nat) : (term97 m) = (term81 m).
Proof. exact (fun_ext (fun n : nat => @lem7918105 m n)). Qed.
Lemma lem7918107 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918108 (m : nat) : (term89 m) = (term82 m).
Proof. exact (MK_COMB (@lem7918107) (@lem7918106 m)). Qed.
Lemma lem7918109 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7918110 (m : nat) : (term98 m) = (term99 m).
Proof. exact (MK_COMB (@lem7918109) (@lem7918108 m)). Qed.
Lemma lem7918111 (m : nat) (n : nat) : (term93 m n) = (term76 m n).
Proof. exact (eq_refl (term93 m n)). Qed.
Lemma lem7918112 (m : nat) : (term100 m) = (term91 m).
Proof. exact (fun_ext (fun n : nat => @lem7918111 m n)). Qed.
Lemma lem7918113 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918114 (m : nat) : (term101 m) = (term102 m).
Proof. exact (MK_COMB (@lem7918113) (@lem7918112 m)). Qed.
Lemma lem7918115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7918116 (m : nat) : (term103 m) = (term104 m).
Proof. exact (MK_COMB (@lem7918115) (@lem7918114 m)). Qed.
Lemma lem7918117 (m : nat) (n : nat) : (term95 m n) = (term73 m n).
Proof. exact (eq_refl (term95 m n)). Qed.
Lemma lem7918118 (m : nat) : (term105 m) = (term92 m).
Proof. exact (fun_ext (fun n : nat => @lem7918117 m n)). Qed.
Lemma lem7918119 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918120 (m : nat) : (term106 m) = (term107 m).
Proof. exact (MK_COMB (@lem7918119) (@lem7918118 m)). Qed.
Lemma lem7918121 (m : nat) : (term90 m) = (term108 m).
Proof. exact (MK_COMB (@lem7918116 m) (@lem7918120 m)). Qed.
Lemma lem7918122 (m : nat) : ((term89 m) = (term90 m)) = ((term82 m) = (term108 m)).
Proof. exact (MK_COMB (@lem7918110 m) (@lem7918121 m)). Qed.
Lemma lem7918123 (m : nat) : (term82 m) = (term108 m).
Proof. exact (EQ_MP (@lem7918122 m) (@lem7918100 m)). Qed.
Lemma lem7918220 : term83 = term109.
Proof. exact (fun_ext (fun m : nat => @lem7918123 m)). Qed.
Lemma lem7918221 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918222 : term84 = term110.
Proof. exact (MK_COMB (@lem7918221) (@lem7918220)). Qed.
Lemma lem7918224 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term85 A P Q) = (term86 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7918225 (P : nat -> Prop) (Q : nat -> Prop) : (term87 P Q) = (term88 P Q).
Proof. exact (@lem7918224 nat P Q). Qed.
Lemma lem7918226 : term111 = term112.
Proof. exact (@lem7918225 term113 term114). Qed.
Lemma lem7918227 (m : nat) : (term115 m) = (term102 m).
Proof. exact (eq_refl (term115 m)). Qed.
Lemma lem7918228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7918229 (m : nat) : (term116 m) = (term104 m).
Proof. exact (MK_COMB (@lem7918228) (@lem7918227 m)). Qed.
Lemma lem7918230 (m : nat) : (term117 m) = (term107 m).
Proof. exact (eq_refl (term117 m)). Qed.
Lemma lem7918231 (m : nat) : (term118 m) = (term108 m).
Proof. exact (MK_COMB (@lem7918229 m) (@lem7918230 m)). Qed.
Lemma lem7918232 : term119 = term109.
Proof. exact (fun_ext (fun m : nat => @lem7918231 m)). Qed.
Lemma lem7918233 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918234 : term111 = term110.
Proof. exact (MK_COMB (@lem7918233) (@lem7918232)). Qed.
Lemma lem7918235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7918236 : term120 = term121.
Proof. exact (MK_COMB (@lem7918235) (@lem7918234)). Qed.
Lemma lem7918237 (m : nat) : (term115 m) = (term102 m).
Proof. exact (eq_refl (term115 m)). Qed.
Lemma lem7918238 : term122 = term113.
Proof. exact (fun_ext (fun m : nat => @lem7918237 m)). Qed.
Lemma lem7918239 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918240 : term123 = term124.
Proof. exact (MK_COMB (@lem7918239) (@lem7918238)). Qed.
Lemma lem7918241 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7918242 : term125 = term126.
Proof. exact (MK_COMB (@lem7918241) (@lem7918240)). Qed.
Lemma lem7918243 (m : nat) : (term117 m) = (term107 m).
Proof. exact (eq_refl (term117 m)). Qed.
Lemma lem7918244 : term127 = term114.
Proof. exact (fun_ext (fun m : nat => @lem7918243 m)). Qed.
Lemma lem7918245 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918246 : term128 = term129.
Proof. exact (MK_COMB (@lem7918245) (@lem7918244)). Qed.
Lemma lem7918247 : term112 = term130.
Proof. exact (MK_COMB (@lem7918242) (@lem7918246)). Qed.
Lemma lem7918248 : (term111 = term112) = (term110 = term130).
Proof. exact (MK_COMB (@lem7918236) (@lem7918247)). Qed.
Lemma lem7918249 : term110 = term130.
Proof. exact (EQ_MP (@lem7918248) (@lem7918226)). Qed.
Lemma lem7918356 : term84 = term130.
Proof. exact (TRANS (@lem7918222) (@lem7918249)). Qed.
Lemma lem7918357 : term70 = term130.
Proof. exact (TRANS (@lem7918092) (@lem7918356)). Qed.
Lemma lem7918358 (h1 : term70) : term130.
Proof. exact (EQ_MP (@lem7918357) (@lem7918052 h1)). Qed.
Lemma lem7918359 {A : Type'} (s : A -> Prop) : (term64 A s) = (term64 A s).
Proof. exact (eq_refl (term64 A s)). Qed.
Lemma lem7918360 {A : Type'} : (term65 A) = (term65 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7918359 A s)). Qed.
Lemma lem7918361 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7918370 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7918361 A) (@lem7918360 A)). Qed.
Lemma lem7918371 {A : Type'} (h1 : term19 A) : term19 A.
Proof. exact (EQ_MP (@lem7918370 A) (@lem7918053 A h1)). Qed.
Lemma lem7918372 {B : Type'} (s : B -> Prop) : (term64 B s) = (term64 B s).
Proof. exact (eq_refl (term64 B s)). Qed.
Lemma lem7918373 {B : Type'} : (term65 B) = (term65 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem7918372 B s)). Qed.
Lemma lem7918374 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7918383 {B : Type'} : (term19 B) = (term19 B).
Proof. exact (MK_COMB (@lem7918374 B) (@lem7918373 B)). Qed.
Lemma lem7918384 {B : Type'} (h1 : term19 B) : term19 B.
Proof. exact (EQ_MP (@lem7918383 B) (@lem7918054 B h1)). Qed.
Lemma lem7918387 (n : nat) : (term131 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem7918388 (n : nat) : (term132 n) = (term132 n).
Proof. exact (eq_refl (term132 n)). Qed.
Lemma lem7918389 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7918390 (n : nat) : (term133 n) = (term134 n).
Proof. exact (MK_COMB (@lem7918389) (@lem7918387 n)). Qed.
Lemma lem7918391 (n : nat) : (term135 n) = (term136 n).
Proof. exact (MK_COMB (@lem7918390 n) (@lem7918388 n)). Qed.
Lemma lem7918392 (n : nat) : (term60 n) = (term135 n).
Proof. exact (@lem17265 (term137 n) (term132 n)). Qed.
Lemma lem7918393 (n : nat) : (term60 n) = (term136 n).
Proof. exact (TRANS (@lem7918392 n) (@lem7918391 n)). Qed.
Lemma lem7918394 : term61 = term138.
Proof. exact (fun_ext (fun n : nat => @lem7918393 n)). Qed.
Lemma lem7918395 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918396 : term62 = term139.
Proof. exact (MK_COMB (@lem7918395) (@lem7918394)). Qed.
Lemma lem7918399 (n : nat) : (term131 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem7918400 (n : nat) : (term140 n) = (term140 n).
Proof. exact (eq_refl (term140 n)). Qed.
Lemma lem7918401 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7918402 (n : nat) : (term133 n) = (term134 n).
Proof. exact (MK_COMB (@lem7918401) (@lem7918399 n)). Qed.
Lemma lem7918403 (n : nat) : (term141 n) = (term142 n).
Proof. exact (MK_COMB (@lem7918402 n) (@lem7918400 n)). Qed.
Lemma lem7918404 (n : nat) : (term55 n) = (term141 n).
Proof. exact (@lem17265 (term137 n) (term140 n)). Qed.
Lemma lem7918405 (n : nat) : (term55 n) = (term142 n).
Proof. exact (TRANS (@lem7918404 n) (@lem7918403 n)). Qed.
Lemma lem7918406 : term56 = term143.
Proof. exact (fun_ext (fun n : nat => @lem7918405 n)). Qed.
Lemma lem7918407 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918408 : term57 = term144.
Proof. exact (MK_COMB (@lem7918407) (@lem7918406)). Qed.
Lemma lem7918415 (n : nat) : (term50 n) = (term145 n).
Proof. exact (@lem17265 (term132 n) (term137 n)). Qed.
Lemma lem7918416 : term51 = term146.
Proof. exact (fun_ext (fun n : nat => @lem7918415 n)). Qed.
Lemma lem7918417 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918418 : term52 = term147.
Proof. exact (MK_COMB (@lem7918417) (@lem7918416)). Qed.
Lemma lem7918425 (n : nat) : (term45 n) = (term148 n).
Proof. exact (@lem17265 (term132 n) (term140 n)). Qed.
Lemma lem7918426 : term46 = term149.
Proof. exact (fun_ext (fun n : nat => @lem7918425 n)). Qed.
Lemma lem7918427 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918428 : term47 = term150.
Proof. exact (MK_COMB (@lem7918427) (@lem7918426)). Qed.
Lemma lem7918435 (n : nat) : (term40 n) = (term151 n).
Proof. exact (@lem17265 (term140 n) (term132 n)). Qed.
Lemma lem7918436 : term41 = term152.
Proof. exact (fun_ext (fun n : nat => @lem7918435 n)). Qed.
Lemma lem7918437 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918438 : term42 = term153.
Proof. exact (MK_COMB (@lem7918437) (@lem7918436)). Qed.
Lemma lem7918445 (n : nat) : (term37 n) = (term154 n).
Proof. exact (@lem17265 (term140 n) (term137 n)). Qed.
Lemma lem7918446 : term38 = term155.
Proof. exact (fun_ext (fun n : nat => @lem7918445 n)). Qed.
Lemma lem7918447 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918448 : term39 = term156.
Proof. exact (MK_COMB (@lem7918447) (@lem7918446)). Qed.
Lemma lem7918449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7918450 : term43 = term157.
Proof. exact (MK_COMB (@lem7918449) (@lem7918438)). Qed.
Lemma lem7918451 : term44 = term158.
Proof. exact (MK_COMB (@lem7918450) (@lem7918448)). Qed.
Lemma lem7918452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7918453 : term48 = term159.
Proof. exact (MK_COMB (@lem7918452) (@lem7918428)). Qed.
Lemma lem7918454 : term49 = term160.
Proof. exact (MK_COMB (@lem7918453) (@lem7918451)). Qed.
Lemma lem7918455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7918456 : term53 = term161.
Proof. exact (MK_COMB (@lem7918455) (@lem7918418)). Qed.
Lemma lem7918457 : term54 = term162.
Proof. exact (MK_COMB (@lem7918456) (@lem7918454)). Qed.
Lemma lem7918458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7918459 : term58 = term163.
Proof. exact (MK_COMB (@lem7918458) (@lem7918408)). Qed.
Lemma lem7918460 : term59 = term164.
Proof. exact (MK_COMB (@lem7918459) (@lem7918457)). Qed.
Lemma lem7918461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7918462 : term63 = term165.
Proof. exact (MK_COMB (@lem7918461) (@lem7918396)). Qed.
Lemma lem7918755 : term26 = term166.
Proof. exact (MK_COMB (@lem7918462) (@lem7918460)). Qed.
Lemma lem7918756 (h1 : term26) : term166.
Proof. exact (EQ_MP (@lem7918755) (@lem7918055 h1)). Qed.
Lemma lem7918776 {A B : Type'} (h1 : term18 A B) : term18 A B.
Proof. exact (h1). Qed.
Lemma lem7918809 (m : nat) (n : nat) : (term73 m n) = (term73 m n).
Proof. exact (eq_refl (term73 m n)). Qed.
Lemma lem7918810 (m : nat) : (term92 m) = (term92 m).
Proof. exact (fun_ext (fun n : nat => @lem7918809 m n)). Qed.
Lemma lem7918811 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918812 (m : nat) : (term107 m) = (term107 m).
Proof. exact (MK_COMB (@lem7918811) (@lem7918810 m)). Qed.
Lemma lem7918813 : term114 = term114.
Proof. exact (fun_ext (fun m : nat => @lem7918812 m)). Qed.
Lemma lem7918814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918815 : term129 = term129.
Proof. exact (MK_COMB (@lem7918814) (@lem7918813)). Qed.
Lemma lem7918850 (m : nat) (n : nat) : (term76 m n) = (term76 m n).
Proof. exact (eq_refl (term76 m n)). Qed.
Lemma lem7918851 (m : nat) : (term91 m) = (term91 m).
Proof. exact (fun_ext (fun n : nat => @lem7918850 m n)). Qed.
Lemma lem7918852 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918853 (m : nat) : (term102 m) = (term102 m).
Proof. exact (MK_COMB (@lem7918852) (@lem7918851 m)). Qed.
Lemma lem7918854 : term113 = term113.
Proof. exact (fun_ext (fun m : nat => @lem7918853 m)). Qed.
Lemma lem7918855 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918856 : term124 = term124.
Proof. exact (MK_COMB (@lem7918855) (@lem7918854)). Qed.
Lemma lem7918857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7918858 : term126 = term126.
Proof. exact (MK_COMB (@lem7918857) (@lem7918856)). Qed.
Lemma lem7918859 : term130 = term130.
Proof. exact (MK_COMB (@lem7918858) (@lem7918815)). Qed.
Lemma lem7918860 (h1 : term70) : term130.
Proof. exact (EQ_MP (@lem7918859) (@lem7918358 h1)). Qed.
Lemma lem7918871 {A : Type'} (s : A -> Prop) : (term64 A s) = (term64 A s).
Proof. exact (eq_refl (term64 A s)). Qed.
Lemma lem7918872 {A : Type'} : (term65 A) = (term65 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7918871 A s)). Qed.
Lemma lem7918873 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7918874 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7918873 A) (@lem7918872 A)). Qed.
Lemma lem7918875 {A : Type'} (h1 : term19 A) : term19 A.
Proof. exact (EQ_MP (@lem7918874 A) (@lem7918371 A h1)). Qed.
Lemma lem7918886 {B : Type'} (s : B -> Prop) : (term64 B s) = (term64 B s).
Proof. exact (eq_refl (term64 B s)). Qed.
Lemma lem7918887 {B : Type'} : (term65 B) = (term65 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem7918886 B s)). Qed.
Lemma lem7918888 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7918889 {B : Type'} : (term19 B) = (term19 B).
Proof. exact (MK_COMB (@lem7918888 B) (@lem7918887 B)). Qed.
Lemma lem7918890 {B : Type'} (h1 : term19 B) : term19 B.
Proof. exact (EQ_MP (@lem7918889 B) (@lem7918384 B h1)). Qed.
Lemma lem7918913 (n : nat) : (term154 n) = (term154 n).
Proof. exact (eq_refl (term154 n)). Qed.
Lemma lem7918914 : term155 = term155.
Proof. exact (fun_ext (fun n : nat => @lem7918913 n)). Qed.
Lemma lem7918915 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918916 : term156 = term156.
Proof. exact (MK_COMB (@lem7918915) (@lem7918914)). Qed.
Lemma lem7918937 (n : nat) : (term151 n) = (term151 n).
Proof. exact (eq_refl (term151 n)). Qed.
Lemma lem7918938 : term152 = term152.
Proof. exact (fun_ext (fun n : nat => @lem7918937 n)). Qed.
Lemma lem7918939 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918940 : term153 = term153.
Proof. exact (MK_COMB (@lem7918939) (@lem7918938)). Qed.
Lemma lem7918941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7918942 : term157 = term157.
Proof. exact (MK_COMB (@lem7918941) (@lem7918940)). Qed.
Lemma lem7918943 : term158 = term158.
Proof. exact (MK_COMB (@lem7918942) (@lem7918916)). Qed.
Lemma lem7918964 (n : nat) : (term148 n) = (term148 n).
Proof. exact (eq_refl (term148 n)). Qed.
Lemma lem7918965 : term149 = term149.
Proof. exact (fun_ext (fun n : nat => @lem7918964 n)). Qed.
Lemma lem7918966 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918967 : term150 = term150.
Proof. exact (MK_COMB (@lem7918966) (@lem7918965)). Qed.
Lemma lem7918968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7918969 : term159 = term159.
Proof. exact (MK_COMB (@lem7918968) (@lem7918967)). Qed.
Lemma lem7918970 : term160 = term160.
Proof. exact (MK_COMB (@lem7918969) (@lem7918943)). Qed.
Lemma lem7918991 (n : nat) : (term145 n) = (term145 n).
Proof. exact (eq_refl (term145 n)). Qed.
Lemma lem7918992 : term146 = term146.
Proof. exact (fun_ext (fun n : nat => @lem7918991 n)). Qed.
Lemma lem7918993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7918994 : term147 = term147.
Proof. exact (MK_COMB (@lem7918993) (@lem7918992)). Qed.
Lemma lem7918995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7918996 : term161 = term161.
Proof. exact (MK_COMB (@lem7918995) (@lem7918994)). Qed.
Lemma lem7918997 : term162 = term162.
Proof. exact (MK_COMB (@lem7918996) (@lem7918970)). Qed.
Lemma lem7919016 (n : nat) : (term142 n) = (term142 n).
Proof. exact (eq_refl (term142 n)). Qed.
Lemma lem7919017 : term143 = term143.
Proof. exact (fun_ext (fun n : nat => @lem7919016 n)). Qed.
Lemma lem7919018 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7919019 : term144 = term144.
Proof. exact (MK_COMB (@lem7919018) (@lem7919017)). Qed.
Lemma lem7919020 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7919021 : term163 = term163.
Proof. exact (MK_COMB (@lem7919020) (@lem7919019)). Qed.
Lemma lem7919022 : term164 = term164.
Proof. exact (MK_COMB (@lem7919021) (@lem7918997)). Qed.
Lemma lem7919039 (n : nat) : (term136 n) = (term136 n).
Proof. exact (eq_refl (term136 n)). Qed.
Lemma lem7919040 : term138 = term138.
Proof. exact (fun_ext (fun n : nat => @lem7919039 n)). Qed.
Lemma lem7919041 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7919042 : term139 = term139.
Proof. exact (MK_COMB (@lem7919041) (@lem7919040)). Qed.
Lemma lem7919043 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7919044 : term165 = term165.
Proof. exact (MK_COMB (@lem7919043) (@lem7919042)). Qed.
Lemma lem7919045 : term166 = term166.
Proof. exact (MK_COMB (@lem7919044) (@lem7919022)). Qed.
Lemma lem7919046 (h1 : term26) : term166.
Proof. exact (EQ_MP (@lem7919045) (@lem7918756 h1)). Qed.
Lemma lem7919047 (h1 : term26) : term164.
Proof. exact (proj2 (@lem7919046 h1)). Qed.
Lemma lem7919049 (h1 : term26) : term162.
Proof. exact (proj2 (@lem7919047 h1)). Qed.
Lemma lem7919050 (h1 : term26) : term144.
Proof. exact (proj1 (@lem7919047 h1)). Qed.
Lemma lem7919051 (h1 : term26) : term160.
Proof. exact (proj2 (@lem7919049 h1)). Qed.
Lemma lem7919053 (h1 : term26) : term158.
Proof. exact (proj2 (@lem7919051 h1)). Qed.
Lemma lem7919055 (h1 : term26) : term156.
Proof. exact (proj2 (@lem7919053 h1)). Qed.
Lemma lem7919057 (h1 : term70) : term129.
Proof. exact (proj2 (@lem7918860 h1)). Qed.
Lemma lem7919062 {A B : Type'} (h1 : term18 A B) : term18 A B.
Proof. exact (h1). Qed.
Lemma lem7919064 {A : Type'} (s : A -> Prop) : (term64 A s) = (term64 A s).
Proof. exact (eq_refl (term64 A s)). Qed.
Lemma lem7919065 {A : Type'} : (term65 A) = (term65 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7919064 A s)). Qed.
Lemma lem7919066 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7919068 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7919066 A) (@lem7919065 A)). Qed.
Lemma lem7919069 {A : Type'} (h1 : term19 A) : term19 A.
Proof. exact (EQ_MP (@lem7919068 A) (@lem7918875 A h1)). Qed.
Lemma lem7919071 {B : Type'} (s : B -> Prop) : (term64 B s) = (term64 B s).
Proof. exact (eq_refl (term64 B s)). Qed.
Lemma lem7919072 {B : Type'} : (term65 B) = (term65 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem7919071 B s)). Qed.
Lemma lem7919073 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7919075 {B : Type'} : (term19 B) = (term19 B).
Proof. exact (MK_COMB (@lem7919073 B) (@lem7919072 B)). Qed.
Lemma lem7919076 {B : Type'} (h1 : term19 B) : term19 B.
Proof. exact (EQ_MP (@lem7919075 B) (@lem7918890 B h1)). Qed.
Lemma lem7919097 (n : nat) : (term142 n) = (term142 n).
Proof. exact (eq_refl (term142 n)). Qed.
Lemma lem7919098 : term143 = term143.
Proof. exact (fun_ext (fun n : nat => @lem7919097 n)). Qed.
Lemma lem7919099 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7919101 : term144 = term144.
Proof. exact (MK_COMB (@lem7919099) (@lem7919098)). Qed.
Lemma lem7919102 (h1 : term26) : term144.
Proof. exact (EQ_MP (@lem7919101) (@lem7919050 h1)). Qed.
Lemma lem7919149 (n : nat) : (term154 n) = (term154 n).
Proof. exact (eq_refl (term154 n)). Qed.
Lemma lem7919150 : term155 = term155.
Proof. exact (fun_ext (fun n : nat => @lem7919149 n)). Qed.
Lemma lem7919151 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7919153 : term156 = term156.
Proof. exact (MK_COMB (@lem7919151) (@lem7919150)). Qed.
Lemma lem7919154 (h1 : term26) : term156.
Proof. exact (EQ_MP (@lem7919153) (@lem7919055 h1)). Qed.
Lemma lem7919194 (m : nat) (n : nat) : (term73 m n) = (term73 m n).
Proof. exact (eq_refl (term73 m n)). Qed.
Lemma lem7919195 (m : nat) : (term92 m) = (term92 m).
Proof. exact (fun_ext (fun n : nat => @lem7919194 m n)). Qed.
Lemma lem7919196 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7919197 (m : nat) : (term107 m) = (term107 m).
Proof. exact (MK_COMB (@lem7919196) (@lem7919195 m)). Qed.
Lemma lem7919198 : term114 = term114.
Proof. exact (fun_ext (fun m : nat => @lem7919197 m)). Qed.
Lemma lem7919199 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7919201 : term129 = term129.
Proof. exact (MK_COMB (@lem7919199) (@lem7919198)). Qed.
Lemma lem7919202 (h1 : term70) : term129.
Proof. exact (EQ_MP (@lem7919201) (@lem7919057 h1)). Qed.
Lemma lem7919203 {A : Type'} (_103643 : A -> Prop) (h1 : term19 A) : term167 A _103643.
Proof. exact (@lem7919069 A h1 _103643). Qed.
Lemma lem7919204 {A : Type'} (_103643 : A -> Prop) : (term167 A _103643) = (term64 A _103643).
Proof. exact (eq_refl (term167 A _103643)). Qed.
Lemma lem7919206 {B : Type'} (_103644 : B -> Prop) (h1 : term19 B) : term167 B _103644.
Proof. exact (@lem7919076 B h1 _103644). Qed.
Lemma lem7919207 {B : Type'} (_103644 : B -> Prop) : (term167 B _103644) = (term64 B _103644).
Proof. exact (eq_refl (term167 B _103644)). Qed.
Lemma lem7919212 (_103646 : nat) (h1 : term26) : term168 _103646.
Proof. exact (@lem7919102 h1 _103646). Qed.
Lemma lem7919213 (_103646 : nat) : (term168 _103646) = (term142 _103646).
Proof. exact (eq_refl (term168 _103646)). Qed.
Lemma lem7919224 (_103650 : nat) (h1 : term26) : term169 _103650.
Proof. exact (@lem7919154 h1 _103650). Qed.
Lemma lem7919225 (_103650 : nat) : (term169 _103650) = (term154 _103650).
Proof. exact (eq_refl (term169 _103650)). Qed.
Lemma lem7919233 (_103653 : nat) (h1 : term70) : term117 _103653.
Proof. exact (@lem7919202 h1 _103653). Qed.
Lemma lem7919234 (_103653 : nat) : (term117 _103653) = (term107 _103653).
Proof. exact (eq_refl (term117 _103653)). Qed.
Lemma lem7919235 (_103653 : nat) (h1 : term70) : term107 _103653.
Proof. exact (EQ_MP (@lem7919234 _103653) (@lem7919233 _103653 h1)). Qed.
Lemma lem7919236 (_103653 : nat) (_103654 : nat) (h1 : term70) : term95 _103653 _103654.
Proof. exact (@lem7919235 _103653 h1 _103654). Qed.
Lemma lem7919237 (_103653 : nat) (_103654 : nat) : (term95 _103653 _103654) = (term73 _103653 _103654).
Proof. exact (eq_refl (term95 _103653 _103654)). Qed.
Lemma lem7919242 {A B : Type'} (h1 : term18 A B) : term18 A B.
Proof. exact (h1). Qed.
Lemma lem7919258 (_103646 : nat) (h1 : term26) : term142 _103646.
Proof. exact (EQ_MP (@lem7919213 _103646) (@lem7919212 _103646 h1)). Qed.
Lemma lem7919282 (_103650 : nat) (h1 : term26) : term154 _103650.
Proof. exact (EQ_MP (@lem7919225 _103650) (@lem7919224 _103650 h1)). Qed.
Lemma lem7919292 (_103653 : nat) (_103654 : nat) (h1 : term70) : term73 _103653 _103654.
Proof. exact (EQ_MP (@lem7919237 _103653 _103654) (@lem7919236 _103653 _103654 h1)). Qed.
Lemma lem7919397 {A : Type'} (_103643 : A -> Prop) (h1 : term19 A) : term64 A _103643.
Proof. exact (EQ_MP (@lem7919204 A _103643) (@lem7919203 A _103643 h1)). Qed.
Lemma lem7919398 {A : Type'} (_103643 : A -> Prop) (h1 : term19 A) : term64 A _103643.
Proof. exact (@lem7919397 A _103643 h1). Qed.
Lemma lem7919399 {A : Type'} (h1 : term19 A) : term170 A.
Proof. exact (@lem7919398 A (@UNIV A) h1). Qed.
Lemma lem7919400 {A : Type'} (h1 : term19 A) : term171 A.
Proof. exact (fun h0 : term172 A => @lem7919399 A h1). Qed.
Lemma lem7919402 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7919403 {A : Type'} : (term171 A) = (term170 A).
Proof. exact (@lem7919402 (term170 A)). Qed.
Lemma lem7919404 {A : Type'} (h1 : term19 A) : term170 A.
Proof. exact (EQ_MP (@lem7919403 A) (@lem7919400 A h1)). Qed.
Lemma lem7919417 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7919418 (_103650 : nat) : (term174 _103650) = (term154 _103650).
Proof. exact (@lem7919417 (term175 _103650) (term137 _103650)). Qed.
Lemma lem7919426 (_103650 : nat) : (term176 _103650) = (term176 _103650).
Proof. exact (eq_refl (term176 _103650)). Qed.
Lemma lem7919427 (_103650 : nat) : ((term154 _103650) = (term174 _103650)) = ((term154 _103650) = (term154 _103650)).
Proof. exact (MK_COMB (@lem7919426 _103650) (@lem7919418 _103650)). Qed.
Lemma lem7919429 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7919430 (x : Prop) : (x = x) = True.
Proof. exact (@lem7919429 Prop x). Qed.
Lemma lem7919431 (_103650 : nat) : ((term154 _103650) = (term154 _103650)) = True.
Proof. exact (@lem7919430 (term154 _103650)). Qed.
Lemma lem7919432 (_103650 : nat) : ((term154 _103650) = (term174 _103650)) = True.
Proof. exact (TRANS (@lem7919427 _103650) (@lem7919431 _103650)). Qed.
Lemma lem7919433 (_103650 : nat) : True = ((term154 _103650) = (term174 _103650)).
Proof. exact (SYM (@lem7919432 _103650)). Qed.
Lemma lem7919434 (_103650 : nat) : (term154 _103650) = (term174 _103650).
Proof. exact (EQ_MP (@lem7919433 _103650) (@lem0)). Qed.
Lemma lem7919435 (_103650 : nat) (h1 : term26) : term174 _103650.
Proof. exact (EQ_MP (@lem7919434 _103650) (@lem7919282 _103650 h1)). Qed.
Lemma lem7919437 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7919438 (_103650 : nat) : (term174 _103650) = (term178 _103650).
Proof. exact (@lem7919437 (term175 _103650) (term137 _103650)). Qed.
Lemma lem7919440 (a : Prop) : (term179 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7919441 (_103650 : nat) : (term180 _103650) = (term140 _103650).
Proof. exact (@lem7919440 (term140 _103650)). Qed.
Lemma lem7919442 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7919443 (_103650 : nat) : (term181 _103650) = (term182 _103650).
Proof. exact (MK_COMB (@lem7919442) (@lem7919441 _103650)). Qed.
Lemma lem7919444 (_103650 : nat) : (term137 _103650) = (term137 _103650).
Proof. exact (eq_refl (term137 _103650)). Qed.
Lemma lem7919445 (_103650 : nat) : (term178 _103650) = (term37 _103650).
Proof. exact (MK_COMB (@lem7919443 _103650) (@lem7919444 _103650)). Qed.
Lemma lem7919446 (_103650 : nat) : (term174 _103650) = (term37 _103650).
Proof. exact (TRANS (@lem7919438 _103650) (@lem7919445 _103650)). Qed.
Lemma lem7919449 (_103650 : nat) (h1 : term26) : term37 _103650.
Proof. exact (EQ_MP (@lem7919446 _103650) (@lem7919435 _103650 h1)). Qed.
Lemma lem7919450 {A : Type'} (h1 : term26) : term183 A.
Proof. exact (@lem7919449 (@dimindex A (@UNIV A)) h1). Qed.
Lemma lem7919453 {A : Type'} (h1 : term19 A) (h2 : term26) : term184 A.
Proof. exact (@lem7919450 A h2 (@lem7919404 A h1)). Qed.
Lemma lem7919454 {A : Type'} (h1 : term19 A) (h2 : term26) : term185 A.
Proof. exact (fun h0 : (@dimindex A (@UNIV A)) = (NUMERAL 0) => @lem7919453 A h1 h2). Qed.
Lemma lem7919456 (p : Prop) : (term186 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7919457 {A : Type'} : (term185 A) = (term184 A).
Proof. exact (@lem7919456 ((@dimindex A (@UNIV A)) = (NUMERAL 0))). Qed.
Lemma lem7919458 {A : Type'} (h1 : term19 A) (h2 : term26) : term184 A.
Proof. exact (EQ_MP (@lem7919457 A) (@lem7919454 A h1 h2)). Qed.
Lemma lem7919460 {B : Type'} (_103644 : B -> Prop) (h1 : term19 B) : term64 B _103644.
Proof. exact (EQ_MP (@lem7919207 B _103644) (@lem7919206 B _103644 h1)). Qed.
Lemma lem7919461 {B : Type'} (_103644 : B -> Prop) (h1 : term19 B) : term64 B _103644.
Proof. exact (@lem7919460 B _103644 h1). Qed.
Lemma lem7919462 {B : Type'} (h1 : term19 B) : term170 B.
Proof. exact (@lem7919461 B (@UNIV B) h1). Qed.
Lemma lem7919463 {B : Type'} (h1 : term19 B) : term171 B.
Proof. exact (fun h0 : term172 B => @lem7919462 B h1). Qed.
Lemma lem7919465 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7919466 {B : Type'} : (term171 B) = (term170 B).
Proof. exact (@lem7919465 (term170 B)). Qed.
Lemma lem7919467 {B : Type'} (h1 : term19 B) : term170 B.
Proof. exact (EQ_MP (@lem7919466 B) (@lem7919463 B h1)). Qed.
Lemma lem7919469 (_103650 : nat) (h1 : term26) : term37 _103650.
Proof. exact (EQ_MP (@lem7919446 _103650) (@lem7919435 _103650 h1)). Qed.
Lemma lem7919470 {B : Type'} (h1 : term26) : term183 B.
Proof. exact (@lem7919469 (@dimindex B (@UNIV B)) h1). Qed.
Lemma lem7919473 {B : Type'} (h1 : term19 B) (h2 : term26) : term184 B.
Proof. exact (@lem7919470 B h2 (@lem7919467 B h1)). Qed.
Lemma lem7919474 {B : Type'} (h1 : term19 B) (h2 : term26) : term185 B.
Proof. exact (fun h0 : (@dimindex B (@UNIV B)) = (NUMERAL 0) => @lem7919473 B h1 h2). Qed.
Lemma lem7919476 (p : Prop) : (term186 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7919477 {B : Type'} : (term185 B) = (term184 B).
Proof. exact (@lem7919476 ((@dimindex B (@UNIV B)) = (NUMERAL 0))). Qed.
Lemma lem7919478 {B : Type'} (h1 : term19 B) (h2 : term26) : term184 B.
Proof. exact (EQ_MP (@lem7919477 B) (@lem7919474 B h1 h2)). Qed.
Lemma lem7919480 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7919481 (_103653 : nat) (_103654 : nat) : (term73 _103653 _103654) = (term187 _103653 _103654).
Proof. exact (@lem7919480 (term66 _103653 _103654) (term188 _103653 _103654)). Qed.
Lemma lem7919483 (a : Prop) (b : Prop) : (term189 a b) = (term190 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7919484 (_103653 : nat) (_103654 : nat) : (term71 _103653 _103654) = (term72 _103653 _103654).
Proof. exact (@lem7919483 (_103653 = (NUMERAL 0)) (_103654 = (NUMERAL 0))). Qed.
Lemma lem7919485 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7919486 (_103653 : nat) (_103654 : nat) : (term191 _103653 _103654) = (term192 _103653 _103654).
Proof. exact (MK_COMB (@lem7919485) (@lem7919484 _103653 _103654)). Qed.
Lemma lem7919487 (_103653 : nat) (_103654 : nat) : (term188 _103653 _103654) = (term188 _103653 _103654).
Proof. exact (eq_refl (term188 _103653 _103654)). Qed.
Lemma lem7919488 (_103653 : nat) (_103654 : nat) : (term187 _103653 _103654) = (term193 _103653 _103654).
Proof. exact (MK_COMB (@lem7919486 _103653 _103654) (@lem7919487 _103653 _103654)). Qed.
Lemma lem7919489 (_103653 : nat) (_103654 : nat) : (term73 _103653 _103654) = (term193 _103653 _103654).
Proof. exact (TRANS (@lem7919481 _103653 _103654) (@lem7919488 _103653 _103654)). Qed.
Lemma lem7919491 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term26) : term194 A B.
Proof. exact (conj (@lem7919458 A h1 h3) (@lem7919478 B h2 h3)). Qed.
Lemma lem7919493 (_103653 : nat) (_103654 : nat) (h1 : term70) : term193 _103653 _103654.
Proof. exact (EQ_MP (@lem7919489 _103653 _103654) (@lem7919292 _103653 _103654 h1)). Qed.
Lemma lem7919494 {A B : Type'} (h1 : term70) : term195 A B.
Proof. exact (@lem7919493 (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B)) h1). Qed.
Lemma lem7919497 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term26) : term196 A B.
Proof. exact (@lem7919494 A B h3 (@lem7919491 A B h1 h2 h4)). Qed.
Lemma lem7919498 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term26) : term197 A B.
Proof. exact (fun h0 : (term11 A B) = (NUMERAL 0) => @lem7919497 A B h1 h2 h3 h4). Qed.
Lemma lem7919500 (p : Prop) : (term186 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7919501 {A B : Type'} : (term197 A B) = (term196 A B).
Proof. exact (@lem7919500 ((term11 A B) = (NUMERAL 0))). Qed.
Lemma lem7919502 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term26) : term196 A B.
Proof. exact (EQ_MP (@lem7919501 A B) (@lem7919498 A B h1 h2 h3 h4)). Qed.
Lemma lem7919508 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7919509 (_103646 : nat) : (term142 _103646) = (term198 _103646).
Proof. exact (@lem7919508 (term140 _103646) (_103646 = (NUMERAL 0))). Qed.
Lemma lem7919517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7919518 (_103646 : nat) : (term199 _103646) = (term200 _103646).
Proof. exact (MK_COMB (@lem7919517) (@lem7919509 _103646)). Qed.
Lemma lem7919526 (_103646 : nat) : (term198 _103646) = (term198 _103646).
Proof. exact (eq_refl (term198 _103646)). Qed.
Lemma lem7919527 (_103646 : nat) : ((term142 _103646) = (term198 _103646)) = ((term198 _103646) = (term198 _103646)).
Proof. exact (MK_COMB (@lem7919518 _103646) (@lem7919526 _103646)). Qed.
Lemma lem7919529 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7919530 (x : Prop) : (x = x) = True.
Proof. exact (@lem7919529 Prop x). Qed.
Lemma lem7919531 (_103646 : nat) : ((term198 _103646) = (term198 _103646)) = True.
Proof. exact (@lem7919530 (term198 _103646)). Qed.
Lemma lem7919532 (_103646 : nat) : ((term142 _103646) = (term198 _103646)) = True.
Proof. exact (TRANS (@lem7919527 _103646) (@lem7919531 _103646)). Qed.
Lemma lem7919533 (_103646 : nat) : True = ((term142 _103646) = (term198 _103646)).
Proof. exact (SYM (@lem7919532 _103646)). Qed.
Lemma lem7919534 (_103646 : nat) : (term142 _103646) = (term198 _103646).
Proof. exact (EQ_MP (@lem7919533 _103646) (@lem0)). Qed.
Lemma lem7919535 (_103646 : nat) (h1 : term26) : term198 _103646.
Proof. exact (EQ_MP (@lem7919534 _103646) (@lem7919258 _103646 h1)). Qed.
Lemma lem7919537 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7919540 (_103646 : nat) : (term198 _103646) = (term55 _103646).
Proof. exact (@lem7919537 (_103646 = (NUMERAL 0)) (term140 _103646)). Qed.
Lemma lem7919543 (_103646 : nat) (h1 : term26) : term55 _103646.
Proof. exact (EQ_MP (@lem7919540 _103646) (@lem7919535 _103646 h1)). Qed.
Lemma lem7919544 {A B : Type'} (h1 : term26) : term201 A B.
Proof. exact (@lem7919543 (term11 A B) h1). Qed.
Lemma lem7919547 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term26) : term14 A B.
Proof. exact (@lem7919544 A B h4 (@lem7919502 A B h1 h2 h3 h4)). Qed.
Lemma lem7919548 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term26) : term202 A B.
Proof. exact (fun h0 : term18 A B => @lem7919547 A B h1 h2 h3 h4). Qed.
Lemma lem7919550 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7919551 {A B : Type'} : (term202 A B) = (term14 A B).
Proof. exact (@lem7919550 (term14 A B)). Qed.
Lemma lem7919552 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term26) : term14 A B.
Proof. exact (EQ_MP (@lem7919551 A B) (@lem7919548 A B h1 h2 h3 h4)). Qed.
Lemma lem7919555 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7919557 {A B : Type'} : (term18 A B) = (term203 A B).
Proof. exact (@lem7919555 (term14 A B)). Qed.
Lemma lem7919560 {A B : Type'} (h1 : term18 A B) : term203 A B.
Proof. exact (EQ_MP (@lem7919557 A B) (@lem7919242 A B h1)). Qed.
Lemma lem7919563 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : False.
Proof. exact (@lem7919560 A B h4 (@lem7919552 A B h1 h2 h3 h5)). Qed.
Lemma lem7919564 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : term204.
Proof. exact (fun h0 : ~ False => @lem7919563 A B h1 h2 h3 h4 h5). Qed.
Lemma lem7919566 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7919567 : term204 = False.
Proof. exact (@lem7919566 False). Qed.
Lemma lem7919568 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : False.
Proof. exact (EQ_MP (@lem7919567) (@lem7919564 A B h1 h2 h3 h4 h5)). Qed.
Lemma lem7919569 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : (term18 A B) = False.
Proof. exact (prop_ext (fun h6 : term18 A B => @lem7919568 A B h1 h2 h3 h4 h5) (fun h6 : False => @lem7919242 A B h4)). Qed.
Lemma lem7919570 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : False.
Proof. exact (EQ_MP (@lem7919569 A B h1 h2 h3 h4 h5) (@lem7919242 A B h4)). Qed.
Lemma lem7919571 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : (term18 A B) = False.
Proof. exact (prop_ext (fun h6 : term18 A B => @lem7919570 A B h1 h2 h3 h4 h5) (fun h6 : False => @lem7919062 A B h4)). Qed.
Lemma lem7919572 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : False.
Proof. exact (EQ_MP (@lem7919571 A B h1 h2 h3 h4 h5) (@lem7919062 A B h4)). Qed.
Lemma lem7919573 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : (term19 B) = False.
Proof. exact (prop_ext (fun h6 : term19 B => @lem7919572 A B h1 h2 h3 h4 h5) (fun h6 : False => @lem7919076 B h2)). Qed.
Lemma lem7919574 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : False.
Proof. exact (EQ_MP (@lem7919573 A B h1 h2 h3 h4 h5) (@lem7919076 B h2)). Qed.
Lemma lem7919575 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : (term19 A) = False.
Proof. exact (prop_ext (fun h6 : term19 A => @lem7919574 A B h1 h2 h3 h4 h5) (fun h6 : False => @lem7919069 A h1)). Qed.
Lemma lem7919576 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : False.
Proof. exact (EQ_MP (@lem7919575 A B h1 h2 h3 h4 h5) (@lem7919069 A h1)). Qed.
Lemma lem7919577 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : (term18 A B) = False.
Proof. exact (prop_ext (fun h6 : term18 A B => @lem7919576 A B h1 h2 h3 h4 h5) (fun h6 : False => @lem7919062 A B h4)). Qed.
Lemma lem7919578 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : False.
Proof. exact (EQ_MP (@lem7919577 A B h1 h2 h3 h4 h5) (@lem7919062 A B h4)). Qed.
Lemma lem7919579 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : (term19 B) = False.
Proof. exact (prop_ext (fun h6 : term19 B => @lem7919578 A B h1 h2 h3 h4 h5) (fun h6 : False => @lem7918890 B h2)). Qed.
Lemma lem7919580 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : False.
Proof. exact (EQ_MP (@lem7919579 A B h1 h2 h3 h4 h5) (@lem7918890 B h2)). Qed.
Lemma lem7919581 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : (term19 A) = False.
Proof. exact (prop_ext (fun h6 : term19 A => @lem7919580 A B h1 h2 h3 h4 h5) (fun h6 : False => @lem7918875 A h1)). Qed.
Lemma lem7919582 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : False.
Proof. exact (EQ_MP (@lem7919581 A B h1 h2 h3 h4 h5) (@lem7918875 A h1)). Qed.
Lemma lem7919583 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : (term18 A B) = False.
Proof. exact (prop_ext (fun h6 : term18 A B => @lem7919582 A B h1 h2 h3 h4 h5) (fun h6 : False => @lem7918776 A B h4)). Qed.
Lemma lem7919584 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : False.
Proof. exact (EQ_MP (@lem7919583 A B h1 h2 h3 h4 h5) (@lem7918776 A B h4)). Qed.
Lemma lem7919585 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : (term19 B) = False.
Proof. exact (prop_ext (fun h6 : term19 B => @lem7919584 A B h1 h2 h3 h4 h5) (fun h6 : False => @lem7918384 B h2)). Qed.
Lemma lem7919586 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : False.
Proof. exact (EQ_MP (@lem7919585 A B h1 h2 h3 h4 h5) (@lem7918384 B h2)). Qed.
Lemma lem7919587 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : (term19 A) = False.
Proof. exact (prop_ext (fun h6 : term19 A => @lem7919586 A B h1 h2 h3 h4 h5) (fun h6 : False => @lem7918371 A h1)). Qed.
Lemma lem7919588 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : False.
Proof. exact (EQ_MP (@lem7919587 A B h1 h2 h3 h4 h5) (@lem7918371 A h1)). Qed.
Lemma lem7919589 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : (term18 A B) = False.
Proof. exact (prop_ext (fun h6 : term18 A B => @lem7919588 A B h1 h2 h3 h4 h5) (fun h6 : False => @lem7918061 A B h4)). Qed.
Lemma lem7919590 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) (h5 : term26) : False.
Proof. exact (EQ_MP (@lem7919589 A B h1 h2 h3 h4 h5) (@lem7918061 A B h4)). Qed.
Lemma lem7919591 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) : term24.
Proof. exact (fun h0 : term26 => @lem7919590 A B h1 h2 h3 h4 h0). Qed.
Lemma lem7919592 : term24 = term25.
Proof. exact (@lem69 term26). Qed.
Lemma lem7919593 {A B : Type'} (h1 : term19 A) (h2 : term19 B) (h3 : term70) (h4 : term18 A B) : term25.
Proof. exact (EQ_MP (@lem7919592) (@lem7919591 A B h1 h2 h3 h4)). Qed.
Lemma lem7919594 {A B : Type'} (h1 : term19 A) (h2 : term70) (h3 : term18 A B) : term29 B.
Proof. exact (fun h0 : term19 B => @lem7919593 A B h1 h0 h2 h3). Qed.
Lemma lem7919595 {A B : Type'} (h1 : term70) (h2 : term18 A B) : term31 A B.
Proof. exact (fun h0 : term19 A => @lem7919594 A B h0 h1 h2). Qed.
Lemma lem7919596 {A B : Type'} (h1 : term18 A B) : term34 A B.
Proof. exact (fun h0 : term70 => @lem7919595 A B h0 h1). Qed.
Lemma lem7919597 {A B : Type'} : term36 A B.
Proof. exact (fun h0 : term18 A B => @lem7919596 A B h0). Qed.
Lemma lem7919598 {A B : Type'} : term20 A B.
Proof. exact (EQ_MP (@lem7918050 A B) (@lem7919597 A B)). Qed.
Lemma lem7919600 {A B : Type'} : term20 A B.
Proof. exact (@lem7917748 A B (@lem7919598 A B)). Qed.
Lemma lem7919601 {A B : Type'} (h1 : term18 A B) : term33 A B.
Proof. exact (@lem7919600 A B (@lem7917730 A B h1)). Qed.
Lemma lem7919602 {A B : Type'} (h1 : term18 A B) : term30 A B.
Proof. exact (@lem7919601 A B h1 (@lem83870)). Qed.
Lemma lem7919603 {A B : Type'} (h1 : term18 A B) : term28 B.
Proof. exact (@lem7919602 A B h1 (@lem7594654 A)). Qed.
Lemma lem7919604 {A B : Type'} (h1 : term18 A B) : term24.
Proof. exact (@lem7919603 A B h1 (@lem7917732 B)). Qed.
Lemma lem7919605 {A B : Type'} (h1 : term18 A B) : False.
Proof. exact (@lem7919604 A B h1 (@lem99082)). Qed.
Lemma lem7919606 {A B : Type'} (h1 : term18 A B) : (term18 A B) = False.
Proof. exact (prop_ext (fun h2 : term18 A B => @lem7919605 A B h1) (fun h2 : False => @lem7917730 A B h1)). Qed.
Lemma lem7919607 {A B : Type'} (h1 : term18 A B) : False.
Proof. exact (EQ_MP (@lem7919606 A B h1) (@lem7917730 A B h1)). Qed.
Lemma lem7919608 {A B : Type'} : term17 A B.
Proof. exact (fun h0 : term18 A B => @lem7919607 A B h0). Qed.
Lemma lem7919609 {A B : Type'} : term14 A B.
Proof. exact (EQ_MP (@lem7917729 A B) (@lem7919608 A B)). Qed.
Lemma lem7919610 {A B : Type'} : term8 A B.
Proof. exact (EQ_MP (@lem7917725 A B) (@lem7919609 A B)). Qed.
Lemma lem7919611 {A B : Type'} : term205 A B.
Proof. exact (ex_intro (term206 A B) term10 (@lem7919610 A B)). Qed.
Lemma lem7919613 {A : Type'} : (@ex A) = (term207 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem7919614 : (@ex nat) = term208.
Proof. exact (@lem7919613 nat). Qed.
Lemma lem7919615 {A B : Type'} : (term206 A B) = (term206 A B).
Proof. exact (eq_refl (term206 A B)). Qed.
Lemma lem7919616 {A B : Type'} : (term205 A B) = (term209 A B).
Proof. exact (MK_COMB (@lem7919614) (@lem7919615 A B)). Qed.
Lemma lem7919617 {A B : Type'} : (term209 A B) = (term210 A B).
Proof. exact (eq_refl (term209 A B)). Qed.
Lemma lem7919618 {A B : Type'} : (term205 A B) = (term210 A B).
Proof. exact (TRANS (@lem7919616 A B) (@lem7919617 A B)). Qed.
Lemma lem7919619 {A B : Type'} : term210 A B.
Proof. exact (EQ_MP (@lem7919618 A B) (@lem7919611 A B)). Qed.
Lemma lem7919620 {A B : Type'} (a : finite_prod A B) : (term211 A B a) = a.
Proof. exact (@axiom_35 A B a). Qed.
Lemma lem7919621 {A B : Type'} (r : nat) : (term212 A B r) = ((term213 A B r) = r).
Proof. exact (@axiom_36 A B r). Qed.
Lemma lem7919624 {A B : Type'} (r : nat) : (term212 A B r) = (term214 A B r).
Proof. exact (eq_refl (term212 A B r)). Qed.
Lemma lem7919625 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7919626 {A B : Type'} (r : nat) : (term215 A B r) = (term216 A B r).
Proof. exact (MK_COMB (@lem7919625) (@lem7919624 A B r)). Qed.
Lemma lem7919627 {A B : Type'} (r : nat) : ((term213 A B r) = r) = ((term213 A B r) = r).
Proof. exact (eq_refl ((term213 A B r) = r)). Qed.
Lemma lem7919628 {A B : Type'} (r : nat) : ((term212 A B r) = ((term213 A B r) = r)) = ((term214 A B r) = ((term213 A B r) = r)).
Proof. exact (MK_COMB (@lem7919626 A B r) (@lem7919627 A B r)). Qed.
Lemma lem7919629 {A B : Type'} (r : nat) : (term214 A B r) = ((term213 A B r) = r).
Proof. exact (EQ_MP (@lem7919628 A B r) (@lem7919621 A B r)). Qed.
Lemma lem7919630 {A B : Type'} : term217 A B.
Proof. exact (fun r : nat => @lem7919629 A B r). Qed.
Lemma lem7919631 {A B : Type'} : term218 A B.
Proof. exact (fun a : finite_prod A B => @lem7919620 A B a). Qed.
Lemma lem7919632 {A B : Type'} : term219 A B.
Proof. exact (conj (@lem7919631 A B) (@lem7919630 A B)). Qed.
