Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_LE_TWICE_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import DISJ_ACI_spec.
Require Import DIVISION_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LE_1_spec.
Require Import LE_ADD_RCANCEL_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_REFL_spec.
Require Import LE_TRANS_spec.
Require Import LT_ADD_RCANCEL_spec.
Require Import LT_IMP_LE_spec.
Require Import MOD_UNIQ_spec.
Require Import MULT_2_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import SUB_ADD_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem178722 (n : nat) (h1 : (term0 n) = (Nat.add n n)) : (term0 n) = (Nat.add n n).
Proof. exact (h1). Qed.
Lemma lem178723 (n : nat) (h1 : (term0 n) = (Nat.add n n)) : (Nat.add n n) = (term0 n).
Proof. exact (SYM (@lem178722 n h1)). Qed.
Lemma lem178724 (n : nat) (h1 : (Nat.add n n) = (term0 n)) : (Nat.add n n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem178725 (n : nat) (h1 : (Nat.add n n) = (term0 n)) : (term0 n) = (Nat.add n n).
Proof. exact (SYM (@lem178724 n h1)). Qed.
Lemma lem178726 (n : nat) : ((term0 n) = (Nat.add n n)) = ((Nat.add n n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (Nat.add n n) => @lem178723 n h1) (fun h1 : (Nat.add n n) = (term0 n) => @lem178725 n h1)). Qed.
Lemma lem178727 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem178726 n)). Qed.
Lemma lem178728 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178729 : term3 = term4.
Proof. exact (MK_COMB (@lem178728) (@lem178727)). Qed.
Lemma lem178730 : term4.
Proof. exact (EQ_MP (@lem178729) (@lem84996)). Qed.
Lemma lem178742 (p : Prop) : p = (term5 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem178743 (n : nat) (m : nat) : ((term6 n m) = (term7 n m)) = (term8 n m).
Proof. exact (@lem178742 ((term6 n m) = (term7 n m))). Qed.
Lemma lem178744 (n : nat) (m : nat) : (term8 n m) = ((term6 n m) = (term7 n m)).
Proof. exact (SYM (@lem178743 n m)). Qed.
Lemma lem178745 (n : nat) (m : nat) (h1 : term9 n m) : term9 n m.
Proof. exact (h1). Qed.
Lemma lem178748 (n : nat) (m : nat) (h1 : term10 n m) : term10 n m.
Proof. exact (h1). Qed.
Lemma lem178749 (n : nat) (m : nat) : term11 n m.
Proof. exact (fun h0 : term10 n m => @lem178748 n m h0). Qed.
Lemma lem178750 (n : nat) (m : nat) (h1 : term11 n m) : term11 n m.
Proof. exact (h1). Qed.
Lemma lem178751 (n : nat) (m : nat) (h1 : term10 n m) : term10 n m.
Proof. exact (h1). Qed.
Lemma lem178752 (n : nat) (m : nat) (h1 : term10 n m) (h2 : term11 n m) : term10 n m.
Proof. exact (@lem178750 n m h2 (@lem178751 n m h1)). Qed.
Lemma lem178753 (n : nat) (m : nat) (h1 : term10 n m) : term12 n m.
Proof. exact (fun h0 : term11 n m => @lem178752 n m h1 h0). Qed.
Lemma lem178754 (n : nat) (m : nat) (h1 : term11 n m) : term11 n m.
Proof. exact (h1). Qed.
Lemma lem178755 (n : nat) (m : nat) (h1 : term10 n m) (h2 : term11 n m) : term10 n m.
Proof. exact (@lem178753 n m h1 (@lem178754 n m h2)). Qed.
Lemma lem178756 (n : nat) (m : nat) (h1 : term11 n m) : term11 n m.
Proof. exact (fun h0 : term10 n m => @lem178755 n m h0 h1). Qed.
Lemma lem178757 (n : nat) (m : nat) : term13 n m.
Proof. exact (fun h0 : term11 n m => @lem178756 n m h0). Qed.
Lemma lem178760 (n : nat) (m : nat) : term11 n m.
Proof. exact (@lem178757 n m (@lem178749 n m)). Qed.
Lemma lem178772 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem178773 : term14 = term15.
Proof. exact (@lem178772 term16). Qed.
Lemma lem178786 (n : nat) (m : nat) : (term17 n m) = (term17 n m).
Proof. exact (eq_refl (term17 n m)). Qed.
Lemma lem178787 (n : nat) (m : nat) : (term10 n m) = (term18 n m).
Proof. exact (MK_COMB (@lem178786 n m) (@lem178773)). Qed.
Lemma lem178790 (m : nat) : (term19 m) = (term20 m).
Proof. exact (fun_ext (fun n : nat => @lem178787 n m)). Qed.
Lemma lem178791 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178792 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem178791) (@lem178790 m)). Qed.
Lemma lem178797 : term23 = term24.
Proof. exact (fun_ext (fun m : nat => @lem178792 m)). Qed.
Lemma lem178798 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178807 : term25 = term26.
Proof. exact (MK_COMB (@lem178798) (@lem178797)). Qed.
Lemma lem178812 (p : nat) (m : nat) (n : nat) : ((term27 m n p) = (Peano.lt m n)) = ((term27 m n p) = (Peano.lt m n)).
Proof. exact (eq_refl ((term27 m n p) = (Peano.lt m n))). Qed.
Lemma lem178813 (m : nat) (n : nat) : (term28 m n) = (term28 m n).
Proof. exact (fun_ext (fun p : nat => @lem178812 p m n)). Qed.
Lemma lem178814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178815 (m : nat) (n : nat) : (term29 m n) = (term29 m n).
Proof. exact (MK_COMB (@lem178814) (@lem178813 m n)). Qed.
Lemma lem178816 (m : nat) : (term30 m) = (term30 m).
Proof. exact (fun_ext (fun n : nat => @lem178815 m n)). Qed.
Lemma lem178817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178818 (m : nat) : (term31 m) = (term31 m).
Proof. exact (MK_COMB (@lem178817) (@lem178816 m)). Qed.
Lemma lem178819 : term32 = term32.
Proof. exact (fun_ext (fun m : nat => @lem178818 m)). Qed.
Lemma lem178820 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178821 : term16 = term16.
Proof. exact (MK_COMB (@lem178820) (@lem178819)). Qed.
Lemma lem178822 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem178823 : term15 = term15.
Proof. exact (MK_COMB (@lem178822) (@lem178821)). Qed.
Lemma lem178832 (n : nat) (m : nat) : (term17 n m) = (term17 n m).
Proof. exact (eq_refl (term17 n m)). Qed.
Lemma lem178833 (n : nat) (m : nat) : (term18 n m) = (term18 n m).
Proof. exact (MK_COMB (@lem178832 n m) (@lem178823)). Qed.
Lemma lem178834 (m : nat) : (term20 m) = (term20 m).
Proof. exact (fun_ext (fun n : nat => @lem178833 n m)). Qed.
Lemma lem178835 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178836 (m : nat) : (term22 m) = (term22 m).
Proof. exact (MK_COMB (@lem178835) (@lem178834 m)). Qed.
Lemma lem178837 : term24 = term24.
Proof. exact (fun_ext (fun m : nat => @lem178836 m)). Qed.
Lemma lem178838 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178839 : term26 = term26.
Proof. exact (MK_COMB (@lem178838) (@lem178837)). Qed.
Lemma lem178874 : term25 = term26.
Proof. exact (TRANS (@lem178807) (@lem178839)). Qed.
Lemma lem178875 : term26 = term25.
Proof. exact (SYM (@lem178874)). Qed.
Lemma lem178876 (n : nat) (m : nat) (h1 : term9 n m) : term9 n m.
Proof. exact (h1). Qed.
Lemma lem178877 (h1 : term16) : term16.
Proof. exact (h1). Qed.
Lemma lem178896 (n : nat) (m : nat) : (term9 n m) = (term33 n m).
Proof. exact (@lem17646 (term6 n m) (term7 n m)). Qed.
Lemma lem178912 (p : nat) (m : nat) (n : nat) : ((term27 m n p) = (Peano.lt m n)) = (term34 p m n).
Proof. exact (@lem17784 (term27 m n p) (Peano.lt m n)). Qed.
Lemma lem178913 (m : nat) (n : nat) : (term28 m n) = (term35 m n).
Proof. exact (fun_ext (fun p : nat => @lem178912 p m n)). Qed.
Lemma lem178914 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178915 (m : nat) (n : nat) : (term29 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem178914) (@lem178913 m n)). Qed.
Lemma lem178916 (m : nat) : (term30 m) = (term37 m).
Proof. exact (fun_ext (fun n : nat => @lem178915 m n)). Qed.
Lemma lem178917 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178918 (m : nat) : (term31 m) = (term38 m).
Proof. exact (MK_COMB (@lem178917) (@lem178916 m)). Qed.
Lemma lem178919 : term32 = term39.
Proof. exact (fun_ext (fun m : nat => @lem178918 m)). Qed.
Lemma lem178920 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178921 : term16 = term40.
Proof. exact (MK_COMB (@lem178920) (@lem178919)). Qed.
Lemma lem178931 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term41 A P Q) = (term42 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem178932 (P : nat -> Prop) (Q : nat -> Prop) : (term43 P Q) = (term44 P Q).
Proof. exact (@lem178931 nat P Q). Qed.
Lemma lem178933 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (@lem178932 (term47 m n) (term48 m n)). Qed.
Lemma lem178934 (p : nat) (m : nat) (n : nat) : (term49 m n p) = (term50 p m n).
Proof. exact (eq_refl (term49 m n p)). Qed.
Lemma lem178935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem178936 (p : nat) (m : nat) (n : nat) : (term51 m n p) = (term52 p m n).
Proof. exact (MK_COMB (@lem178935) (@lem178934 p m n)). Qed.
Lemma lem178937 (p : nat) (m : nat) (n : nat) : (term53 m n p) = (term54 p m n).
Proof. exact (eq_refl (term53 m n p)). Qed.
Lemma lem178938 (p : nat) (m : nat) (n : nat) : (term55 m n p) = (term34 p m n).
Proof. exact (MK_COMB (@lem178936 p m n) (@lem178937 p m n)). Qed.
Lemma lem178939 (m : nat) (n : nat) : (term56 m n) = (term35 m n).
Proof. exact (fun_ext (fun p : nat => @lem178938 p m n)). Qed.
Lemma lem178940 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178941 (m : nat) (n : nat) : (term45 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem178940) (@lem178939 m n)). Qed.
Lemma lem178942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem178943 (m : nat) (n : nat) : (term57 m n) = (term58 m n).
Proof. exact (MK_COMB (@lem178942) (@lem178941 m n)). Qed.
Lemma lem178944 (p : nat) (m : nat) (n : nat) : (term49 m n p) = (term50 p m n).
Proof. exact (eq_refl (term49 m n p)). Qed.
Lemma lem178945 (m : nat) (n : nat) : (term59 m n) = (term47 m n).
Proof. exact (fun_ext (fun p : nat => @lem178944 p m n)). Qed.
Lemma lem178946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178947 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (MK_COMB (@lem178946) (@lem178945 m n)). Qed.
Lemma lem178948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem178949 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (MK_COMB (@lem178948) (@lem178947 m n)). Qed.
Lemma lem178950 (p : nat) (m : nat) (n : nat) : (term53 m n p) = (term54 p m n).
Proof. exact (eq_refl (term53 m n p)). Qed.
Lemma lem178951 (m : nat) (n : nat) : (term64 m n) = (term48 m n).
Proof. exact (fun_ext (fun p : nat => @lem178950 p m n)). Qed.
Lemma lem178952 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178953 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (MK_COMB (@lem178952) (@lem178951 m n)). Qed.
Lemma lem178954 (m : nat) (n : nat) : (term46 m n) = (term67 m n).
Proof. exact (MK_COMB (@lem178949 m n) (@lem178953 m n)). Qed.
Lemma lem178955 (m : nat) (n : nat) : ((term45 m n) = (term46 m n)) = ((term36 m n) = (term67 m n)).
Proof. exact (MK_COMB (@lem178943 m n) (@lem178954 m n)). Qed.
Lemma lem178956 (m : nat) (n : nat) : (term36 m n) = (term67 m n).
Proof. exact (EQ_MP (@lem178955 m n) (@lem178933 m n)). Qed.
Lemma lem178978 {A : Type'} (P : A -> Prop) (Q : Prop) : (term68 A P Q) = (term69 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem178979 (P : nat -> Prop) (Q : Prop) : (term70 P Q) = (term71 P Q).
Proof. exact (@lem178978 nat P Q). Qed.
Lemma lem178980 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (@lem178979 (term74 m n) (term75 m n)). Qed.
Lemma lem178981 (m : nat) (n : nat) (p : nat) : (term76 m n p) = (term27 m n p).
Proof. exact (eq_refl (term76 m n p)). Qed.
Lemma lem178982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem178983 (m : nat) (n : nat) (p : nat) : (term77 m n p) = (term78 m n p).
Proof. exact (MK_COMB (@lem178982) (@lem178981 m n p)). Qed.
Lemma lem178984 (m : nat) (n : nat) : (term75 m n) = (term75 m n).
Proof. exact (eq_refl (term75 m n)). Qed.
Lemma lem178985 (p : nat) (m : nat) (n : nat) : (term79 p m n) = (term50 p m n).
Proof. exact (MK_COMB (@lem178983 m n p) (@lem178984 m n)). Qed.
Lemma lem178986 (m : nat) (n : nat) : (term80 m n) = (term47 m n).
Proof. exact (fun_ext (fun p : nat => @lem178985 p m n)). Qed.
Lemma lem178987 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178988 (m : nat) (n : nat) : (term72 m n) = (term61 m n).
Proof. exact (MK_COMB (@lem178987) (@lem178986 m n)). Qed.
Lemma lem178989 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem178990 (m : nat) (n : nat) : (term81 m n) = (term82 m n).
Proof. exact (MK_COMB (@lem178989) (@lem178988 m n)). Qed.
Lemma lem178991 (m : nat) (n : nat) (p : nat) : (term76 m n p) = (term27 m n p).
Proof. exact (eq_refl (term76 m n p)). Qed.
Lemma lem178992 (m : nat) (n : nat) : (term83 m n) = (term74 m n).
Proof. exact (fun_ext (fun p : nat => @lem178991 m n p)). Qed.
Lemma lem178993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178994 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (MK_COMB (@lem178993) (@lem178992 m n)). Qed.
Lemma lem178995 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem178996 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (MK_COMB (@lem178995) (@lem178994 m n)). Qed.
Lemma lem178997 (m : nat) (n : nat) : (term75 m n) = (term75 m n).
Proof. exact (eq_refl (term75 m n)). Qed.
Lemma lem178998 (m : nat) (n : nat) : (term73 m n) = (term88 m n).
Proof. exact (MK_COMB (@lem178996 m n) (@lem178997 m n)). Qed.
Lemma lem178999 (m : nat) (n : nat) : ((term72 m n) = (term73 m n)) = ((term61 m n) = (term88 m n)).
Proof. exact (MK_COMB (@lem178990 m n) (@lem178998 m n)). Qed.
Lemma lem179000 (m : nat) (n : nat) : (term61 m n) = (term88 m n).
Proof. exact (EQ_MP (@lem178999 m n) (@lem178980 m n)). Qed.
Lemma lem179005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem179006 (m : nat) (n : nat) : (term63 m n) = (term89 m n).
Proof. exact (MK_COMB (@lem179005) (@lem179000 m n)). Qed.
Lemma lem179028 {A : Type'} (P : A -> Prop) (Q : Prop) : (term68 A P Q) = (term69 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem179029 (P : nat -> Prop) (Q : Prop) : (term70 P Q) = (term71 P Q).
Proof. exact (@lem179028 nat P Q). Qed.
Lemma lem179030 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (@lem179029 (term92 m n) (Peano.lt m n)). Qed.
Lemma lem179031 (m : nat) (n : nat) (p : nat) : (term93 m n p) = (term94 m n p).
Proof. exact (eq_refl (term93 m n p)). Qed.
Lemma lem179032 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem179033 (m : nat) (n : nat) (p : nat) : (term95 m n p) = (term96 m n p).
Proof. exact (MK_COMB (@lem179032) (@lem179031 m n p)). Qed.
Lemma lem179034 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem179035 (p : nat) (m : nat) (n : nat) : (term97 p m n) = (term54 p m n).
Proof. exact (MK_COMB (@lem179033 m n p) (@lem179034 m n)). Qed.
Lemma lem179036 (m : nat) (n : nat) : (term98 m n) = (term48 m n).
Proof. exact (fun_ext (fun p : nat => @lem179035 p m n)). Qed.
Lemma lem179037 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179038 (m : nat) (n : nat) : (term90 m n) = (term66 m n).
Proof. exact (MK_COMB (@lem179037) (@lem179036 m n)). Qed.
Lemma lem179039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem179040 (m : nat) (n : nat) : (term99 m n) = (term100 m n).
Proof. exact (MK_COMB (@lem179039) (@lem179038 m n)). Qed.
Lemma lem179041 (m : nat) (n : nat) (p : nat) : (term93 m n p) = (term94 m n p).
Proof. exact (eq_refl (term93 m n p)). Qed.
Lemma lem179042 (m : nat) (n : nat) : (term101 m n) = (term92 m n).
Proof. exact (fun_ext (fun p : nat => @lem179041 m n p)). Qed.
Lemma lem179043 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179044 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (MK_COMB (@lem179043) (@lem179042 m n)). Qed.
Lemma lem179045 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem179046 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (MK_COMB (@lem179045) (@lem179044 m n)). Qed.
Lemma lem179047 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem179048 (m : nat) (n : nat) : (term91 m n) = (term106 m n).
Proof. exact (MK_COMB (@lem179046 m n) (@lem179047 m n)). Qed.
Lemma lem179049 (m : nat) (n : nat) : ((term90 m n) = (term91 m n)) = ((term66 m n) = (term106 m n)).
Proof. exact (MK_COMB (@lem179040 m n) (@lem179048 m n)). Qed.
Lemma lem179050 (m : nat) (n : nat) : (term66 m n) = (term106 m n).
Proof. exact (EQ_MP (@lem179049 m n) (@lem179030 m n)). Qed.
Lemma lem179055 (m : nat) (n : nat) : (term67 m n) = (term107 m n).
Proof. exact (MK_COMB (@lem179006 m n) (@lem179050 m n)). Qed.
Lemma lem179056 (m : nat) (n : nat) : (term36 m n) = (term107 m n).
Proof. exact (TRANS (@lem178956 m n) (@lem179055 m n)). Qed.
Lemma lem179057 (m : nat) : (term37 m) = (term108 m).
Proof. exact (fun_ext (fun n : nat => @lem179056 m n)). Qed.
Lemma lem179058 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179059 (m : nat) : (term38 m) = (term109 m).
Proof. exact (MK_COMB (@lem179058) (@lem179057 m)). Qed.
Lemma lem179061 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term41 A P Q) = (term42 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem179062 (P : nat -> Prop) (Q : nat -> Prop) : (term43 P Q) = (term44 P Q).
Proof. exact (@lem179061 nat P Q). Qed.
Lemma lem179063 (m : nat) : (term110 m) = (term111 m).
Proof. exact (@lem179062 (term112 m) (term113 m)). Qed.
Lemma lem179064 (m : nat) (n : nat) : (term114 m n) = (term88 m n).
Proof. exact (eq_refl (term114 m n)). Qed.
Lemma lem179065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem179066 (m : nat) (n : nat) : (term115 m n) = (term89 m n).
Proof. exact (MK_COMB (@lem179065) (@lem179064 m n)). Qed.
Lemma lem179067 (m : nat) (n : nat) : (term116 m n) = (term106 m n).
Proof. exact (eq_refl (term116 m n)). Qed.
Lemma lem179068 (m : nat) (n : nat) : (term117 m n) = (term107 m n).
Proof. exact (MK_COMB (@lem179066 m n) (@lem179067 m n)). Qed.
Lemma lem179069 (m : nat) : (term118 m) = (term108 m).
Proof. exact (fun_ext (fun n : nat => @lem179068 m n)). Qed.
Lemma lem179070 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179071 (m : nat) : (term110 m) = (term109 m).
Proof. exact (MK_COMB (@lem179070) (@lem179069 m)). Qed.
Lemma lem179072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem179073 (m : nat) : (term119 m) = (term120 m).
Proof. exact (MK_COMB (@lem179072) (@lem179071 m)). Qed.
Lemma lem179074 (m : nat) (n : nat) : (term114 m n) = (term88 m n).
Proof. exact (eq_refl (term114 m n)). Qed.
Lemma lem179075 (m : nat) : (term121 m) = (term112 m).
Proof. exact (fun_ext (fun n : nat => @lem179074 m n)). Qed.
Lemma lem179076 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179077 (m : nat) : (term122 m) = (term123 m).
Proof. exact (MK_COMB (@lem179076) (@lem179075 m)). Qed.
Lemma lem179078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem179079 (m : nat) : (term124 m) = (term125 m).
Proof. exact (MK_COMB (@lem179078) (@lem179077 m)). Qed.
Lemma lem179080 (m : nat) (n : nat) : (term116 m n) = (term106 m n).
Proof. exact (eq_refl (term116 m n)). Qed.
Lemma lem179081 (m : nat) : (term126 m) = (term113 m).
Proof. exact (fun_ext (fun n : nat => @lem179080 m n)). Qed.
Lemma lem179082 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179083 (m : nat) : (term127 m) = (term128 m).
Proof. exact (MK_COMB (@lem179082) (@lem179081 m)). Qed.
Lemma lem179084 (m : nat) : (term111 m) = (term129 m).
Proof. exact (MK_COMB (@lem179079 m) (@lem179083 m)). Qed.
Lemma lem179085 (m : nat) : ((term110 m) = (term111 m)) = ((term109 m) = (term129 m)).
Proof. exact (MK_COMB (@lem179073 m) (@lem179084 m)). Qed.
Lemma lem179086 (m : nat) : (term109 m) = (term129 m).
Proof. exact (EQ_MP (@lem179085 m) (@lem179063 m)). Qed.
Lemma lem179191 (m : nat) : (term38 m) = (term129 m).
Proof. exact (TRANS (@lem179059 m) (@lem179086 m)). Qed.
Lemma lem179192 : term39 = term130.
Proof. exact (fun_ext (fun m : nat => @lem179191 m)). Qed.
Lemma lem179193 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179194 : term40 = term131.
Proof. exact (MK_COMB (@lem179193) (@lem179192)). Qed.
Lemma lem179196 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term41 A P Q) = (term42 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem179197 (P : nat -> Prop) (Q : nat -> Prop) : (term43 P Q) = (term44 P Q).
Proof. exact (@lem179196 nat P Q). Qed.
Lemma lem179198 : term132 = term133.
Proof. exact (@lem179197 term134 term135). Qed.
Lemma lem179199 (m : nat) : (term136 m) = (term123 m).
Proof. exact (eq_refl (term136 m)). Qed.
Lemma lem179200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem179201 (m : nat) : (term137 m) = (term125 m).
Proof. exact (MK_COMB (@lem179200) (@lem179199 m)). Qed.
Lemma lem179202 (m : nat) : (term138 m) = (term128 m).
Proof. exact (eq_refl (term138 m)). Qed.
Lemma lem179203 (m : nat) : (term139 m) = (term129 m).
Proof. exact (MK_COMB (@lem179201 m) (@lem179202 m)). Qed.
Lemma lem179204 : term140 = term130.
Proof. exact (fun_ext (fun m : nat => @lem179203 m)). Qed.
Lemma lem179205 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179206 : term132 = term131.
Proof. exact (MK_COMB (@lem179205) (@lem179204)). Qed.
Lemma lem179207 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem179208 : term141 = term142.
Proof. exact (MK_COMB (@lem179207) (@lem179206)). Qed.
Lemma lem179209 (m : nat) : (term136 m) = (term123 m).
Proof. exact (eq_refl (term136 m)). Qed.
Lemma lem179210 : term143 = term134.
Proof. exact (fun_ext (fun m : nat => @lem179209 m)). Qed.
Lemma lem179211 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179212 : term144 = term145.
Proof. exact (MK_COMB (@lem179211) (@lem179210)). Qed.
Lemma lem179213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem179214 : term146 = term147.
Proof. exact (MK_COMB (@lem179213) (@lem179212)). Qed.
Lemma lem179215 (m : nat) : (term138 m) = (term128 m).
Proof. exact (eq_refl (term138 m)). Qed.
Lemma lem179216 : term148 = term135.
Proof. exact (fun_ext (fun m : nat => @lem179215 m)). Qed.
Lemma lem179217 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179218 : term149 = term150.
Proof. exact (MK_COMB (@lem179217) (@lem179216)). Qed.
Lemma lem179219 : term133 = term151.
Proof. exact (MK_COMB (@lem179214) (@lem179218)). Qed.
Lemma lem179220 : (term132 = term133) = (term131 = term151).
Proof. exact (MK_COMB (@lem179208) (@lem179219)). Qed.
Lemma lem179221 : term131 = term151.
Proof. exact (EQ_MP (@lem179220) (@lem179198)). Qed.
Lemma lem179336 : term40 = term151.
Proof. exact (TRANS (@lem179194) (@lem179221)). Qed.
Lemma lem179337 : term16 = term151.
Proof. exact (TRANS (@lem178921) (@lem179336)). Qed.
Lemma lem179338 (h1 : term16) : term151.
Proof. exact (EQ_MP (@lem179337) (@lem178877 h1)). Qed.
Lemma lem179404 (n : nat) (m : nat) (h1 : term9 n m) : term33 n m.
Proof. exact (EQ_MP (@lem178896 n m) (@lem178876 n m h1)). Qed.
Lemma lem179409 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem179424 (m : nat) (n : nat) (p : nat) : (term94 m n p) = (term94 m n p).
Proof. exact (eq_refl (term94 m n p)). Qed.
Lemma lem179425 (m : nat) (n : nat) : (term92 m n) = (term92 m n).
Proof. exact (fun_ext (fun p : nat => @lem179424 m n p)). Qed.
Lemma lem179426 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179427 (m : nat) (n : nat) : (term103 m n) = (term103 m n).
Proof. exact (MK_COMB (@lem179426) (@lem179425 m n)). Qed.
Lemma lem179428 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem179429 (m : nat) (n : nat) : (term105 m n) = (term105 m n).
Proof. exact (MK_COMB (@lem179428) (@lem179427 m n)). Qed.
Lemma lem179430 (m : nat) (n : nat) : (term106 m n) = (term106 m n).
Proof. exact (MK_COMB (@lem179429 m n) (@lem179409 m n)). Qed.
Lemma lem179431 (m : nat) : (term113 m) = (term113 m).
Proof. exact (fun_ext (fun n : nat => @lem179430 m n)). Qed.
Lemma lem179432 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179433 (m : nat) : (term128 m) = (term128 m).
Proof. exact (MK_COMB (@lem179432) (@lem179431 m)). Qed.
Lemma lem179434 : term135 = term135.
Proof. exact (fun_ext (fun m : nat => @lem179433 m)). Qed.
Lemma lem179435 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179436 : term150 = term150.
Proof. exact (MK_COMB (@lem179435) (@lem179434)). Qed.
Lemma lem179443 (m : nat) (n : nat) : (term75 m n) = (term75 m n).
Proof. exact (eq_refl (term75 m n)). Qed.
Lemma lem179456 (m : nat) (n : nat) (p : nat) : (term27 m n p) = (term27 m n p).
Proof. exact (eq_refl (term27 m n p)). Qed.
Lemma lem179457 (m : nat) (n : nat) : (term74 m n) = (term74 m n).
Proof. exact (fun_ext (fun p : nat => @lem179456 m n p)). Qed.
Lemma lem179458 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179459 (m : nat) (n : nat) : (term85 m n) = (term85 m n).
Proof. exact (MK_COMB (@lem179458) (@lem179457 m n)). Qed.
Lemma lem179460 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem179461 (m : nat) (n : nat) : (term87 m n) = (term87 m n).
Proof. exact (MK_COMB (@lem179460) (@lem179459 m n)). Qed.
Lemma lem179462 (m : nat) (n : nat) : (term88 m n) = (term88 m n).
Proof. exact (MK_COMB (@lem179461 m n) (@lem179443 m n)). Qed.
Lemma lem179463 (m : nat) : (term112 m) = (term112 m).
Proof. exact (fun_ext (fun n : nat => @lem179462 m n)). Qed.
Lemma lem179464 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179465 (m : nat) : (term123 m) = (term123 m).
Proof. exact (MK_COMB (@lem179464) (@lem179463 m)). Qed.
Lemma lem179466 : term134 = term134.
Proof. exact (fun_ext (fun m : nat => @lem179465 m)). Qed.
Lemma lem179467 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179468 : term145 = term145.
Proof. exact (MK_COMB (@lem179467) (@lem179466)). Qed.
Lemma lem179469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem179470 : term147 = term147.
Proof. exact (MK_COMB (@lem179469) (@lem179468)). Qed.
Lemma lem179471 : term151 = term151.
Proof. exact (MK_COMB (@lem179470) (@lem179436)). Qed.
Lemma lem179472 (h1 : term16) : term151.
Proof. exact (EQ_MP (@lem179471) (@lem179338 h1)). Qed.
Lemma lem179473 (h1 : term16) : term150.
Proof. exact (proj2 (@lem179472 h1)). Qed.
Lemma lem179474 (h1 : term16) : term145.
Proof. exact (proj1 (@lem179472 h1)). Qed.
Lemma lem179475 (n : nat) (m : nat) (h1 : term152 n m) : term152 n m.
Proof. exact (h1). Qed.
Lemma lem179476 (n : nat) (m : nat) (h1 : term153 n m) : term153 n m.
Proof. exact (h1). Qed.
Lemma lem179482 {A : Type'} (P : A -> Prop) (Q : Prop) : (term69 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem179483 (P : nat -> Prop) (Q : Prop) : (term71 P Q) = (term70 P Q).
Proof. exact (@lem179482 nat P Q). Qed.
Lemma lem179484 (m : nat) (n : nat) : (term73 m n) = (term72 m n).
Proof. exact (@lem179483 (term74 m n) (term75 m n)). Qed.
Lemma lem179485 (m : nat) (n : nat) (p : nat) : (term76 m n p) = (term27 m n p).
Proof. exact (eq_refl (term76 m n p)). Qed.
Lemma lem179486 (m : nat) (n : nat) : (term83 m n) = (term74 m n).
Proof. exact (fun_ext (fun p : nat => @lem179485 m n p)). Qed.
Lemma lem179487 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179488 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (MK_COMB (@lem179487) (@lem179486 m n)). Qed.
Lemma lem179489 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem179490 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (MK_COMB (@lem179489) (@lem179488 m n)). Qed.
Lemma lem179491 (m : nat) (n : nat) : (term75 m n) = (term75 m n).
Proof. exact (eq_refl (term75 m n)). Qed.
Lemma lem179492 (m : nat) (n : nat) : (term73 m n) = (term88 m n).
Proof. exact (MK_COMB (@lem179490 m n) (@lem179491 m n)). Qed.
Lemma lem179493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem179494 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (MK_COMB (@lem179493) (@lem179492 m n)). Qed.
Lemma lem179495 (m : nat) (n : nat) (p : nat) : (term76 m n p) = (term27 m n p).
Proof. exact (eq_refl (term76 m n p)). Qed.
Lemma lem179496 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem179497 (m : nat) (n : nat) (p : nat) : (term77 m n p) = (term78 m n p).
Proof. exact (MK_COMB (@lem179496) (@lem179495 m n p)). Qed.
Lemma lem179498 (m : nat) (n : nat) : (term75 m n) = (term75 m n).
Proof. exact (eq_refl (term75 m n)). Qed.
Lemma lem179499 (p : nat) (m : nat) (n : nat) : (term79 p m n) = (term50 p m n).
Proof. exact (MK_COMB (@lem179497 m n p) (@lem179498 m n)). Qed.
Lemma lem179500 (m : nat) (n : nat) : (term80 m n) = (term47 m n).
Proof. exact (fun_ext (fun p : nat => @lem179499 p m n)). Qed.
Lemma lem179501 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179502 (m : nat) (n : nat) : (term72 m n) = (term61 m n).
Proof. exact (MK_COMB (@lem179501) (@lem179500 m n)). Qed.
Lemma lem179503 (m : nat) (n : nat) : ((term73 m n) = (term72 m n)) = ((term88 m n) = (term61 m n)).
Proof. exact (MK_COMB (@lem179494 m n) (@lem179502 m n)). Qed.
Lemma lem179504 (m : nat) (n : nat) : (term88 m n) = (term61 m n).
Proof. exact (EQ_MP (@lem179503 m n) (@lem179484 m n)). Qed.
Lemma lem179505 (m : nat) : (term112 m) = (term156 m).
Proof. exact (fun_ext (fun n : nat => @lem179504 m n)). Qed.
Lemma lem179506 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179507 (m : nat) : (term123 m) = (term157 m).
Proof. exact (MK_COMB (@lem179506) (@lem179505 m)). Qed.
Lemma lem179508 : term134 = term158.
Proof. exact (fun_ext (fun m : nat => @lem179507 m)). Qed.
Lemma lem179509 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179510 : term145 = term159.
Proof. exact (MK_COMB (@lem179509) (@lem179508)). Qed.
Lemma lem179517 (p : nat) (m : nat) (n : nat) : (term50 p m n) = (term50 p m n).
Proof. exact (eq_refl (term50 p m n)). Qed.
Lemma lem179518 (m : nat) (n : nat) : (term47 m n) = (term47 m n).
Proof. exact (fun_ext (fun p : nat => @lem179517 p m n)). Qed.
Lemma lem179519 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179520 (m : nat) (n : nat) : (term61 m n) = (term61 m n).
Proof. exact (MK_COMB (@lem179519) (@lem179518 m n)). Qed.
Lemma lem179521 (m : nat) : (term156 m) = (term156 m).
Proof. exact (fun_ext (fun n : nat => @lem179520 m n)). Qed.
Lemma lem179522 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179523 (m : nat) : (term157 m) = (term157 m).
Proof. exact (MK_COMB (@lem179522) (@lem179521 m)). Qed.
Lemma lem179524 : term158 = term158.
Proof. exact (fun_ext (fun m : nat => @lem179523 m)). Qed.
Lemma lem179525 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179526 : term159 = term159.
Proof. exact (MK_COMB (@lem179525) (@lem179524)). Qed.
Lemma lem179527 : term145 = term159.
Proof. exact (TRANS (@lem179510) (@lem179526)). Qed.
Lemma lem179528 (h1 : term16) : term159.
Proof. exact (EQ_MP (@lem179527) (@lem179474 h1)). Qed.
Lemma lem179634 {A : Type'} (P : A -> Prop) (Q : Prop) : (term69 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem179635 (P : nat -> Prop) (Q : Prop) : (term71 P Q) = (term70 P Q).
Proof. exact (@lem179634 nat P Q). Qed.
Lemma lem179636 (m : nat) (n : nat) : (term91 m n) = (term90 m n).
Proof. exact (@lem179635 (term92 m n) (Peano.lt m n)). Qed.
Lemma lem179637 (m : nat) (n : nat) (p : nat) : (term93 m n p) = (term94 m n p).
Proof. exact (eq_refl (term93 m n p)). Qed.
Lemma lem179638 (m : nat) (n : nat) : (term101 m n) = (term92 m n).
Proof. exact (fun_ext (fun p : nat => @lem179637 m n p)). Qed.
Lemma lem179639 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179640 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (MK_COMB (@lem179639) (@lem179638 m n)). Qed.
Lemma lem179641 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem179642 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (MK_COMB (@lem179641) (@lem179640 m n)). Qed.
Lemma lem179643 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem179644 (m : nat) (n : nat) : (term91 m n) = (term106 m n).
Proof. exact (MK_COMB (@lem179642 m n) (@lem179643 m n)). Qed.
Lemma lem179645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem179646 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (MK_COMB (@lem179645) (@lem179644 m n)). Qed.
Lemma lem179647 (m : nat) (n : nat) (p : nat) : (term93 m n p) = (term94 m n p).
Proof. exact (eq_refl (term93 m n p)). Qed.
Lemma lem179648 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem179649 (m : nat) (n : nat) (p : nat) : (term95 m n p) = (term96 m n p).
Proof. exact (MK_COMB (@lem179648) (@lem179647 m n p)). Qed.
Lemma lem179650 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem179651 (p : nat) (m : nat) (n : nat) : (term97 p m n) = (term54 p m n).
Proof. exact (MK_COMB (@lem179649 m n p) (@lem179650 m n)). Qed.
Lemma lem179652 (m : nat) (n : nat) : (term98 m n) = (term48 m n).
Proof. exact (fun_ext (fun p : nat => @lem179651 p m n)). Qed.
Lemma lem179653 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179654 (m : nat) (n : nat) : (term90 m n) = (term66 m n).
Proof. exact (MK_COMB (@lem179653) (@lem179652 m n)). Qed.
Lemma lem179655 (m : nat) (n : nat) : ((term91 m n) = (term90 m n)) = ((term106 m n) = (term66 m n)).
Proof. exact (MK_COMB (@lem179646 m n) (@lem179654 m n)). Qed.
Lemma lem179656 (m : nat) (n : nat) : (term106 m n) = (term66 m n).
Proof. exact (EQ_MP (@lem179655 m n) (@lem179636 m n)). Qed.
Lemma lem179657 (m : nat) : (term113 m) = (term162 m).
Proof. exact (fun_ext (fun n : nat => @lem179656 m n)). Qed.
Lemma lem179658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179659 (m : nat) : (term128 m) = (term163 m).
Proof. exact (MK_COMB (@lem179658) (@lem179657 m)). Qed.
Lemma lem179660 : term135 = term164.
Proof. exact (fun_ext (fun m : nat => @lem179659 m)). Qed.
Lemma lem179661 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179662 : term150 = term165.
Proof. exact (MK_COMB (@lem179661) (@lem179660)). Qed.
Lemma lem179669 (p : nat) (m : nat) (n : nat) : (term54 p m n) = (term54 p m n).
Proof. exact (eq_refl (term54 p m n)). Qed.
Lemma lem179670 (m : nat) (n : nat) : (term48 m n) = (term48 m n).
Proof. exact (fun_ext (fun p : nat => @lem179669 p m n)). Qed.
Lemma lem179671 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179672 (m : nat) (n : nat) : (term66 m n) = (term66 m n).
Proof. exact (MK_COMB (@lem179671) (@lem179670 m n)). Qed.
Lemma lem179673 (m : nat) : (term162 m) = (term162 m).
Proof. exact (fun_ext (fun n : nat => @lem179672 m n)). Qed.
Lemma lem179674 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179675 (m : nat) : (term163 m) = (term163 m).
Proof. exact (MK_COMB (@lem179674) (@lem179673 m)). Qed.
Lemma lem179676 : term164 = term164.
Proof. exact (fun_ext (fun m : nat => @lem179675 m)). Qed.
Lemma lem179677 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem179678 : term165 = term165.
Proof. exact (MK_COMB (@lem179677) (@lem179676)). Qed.
Lemma lem179679 : term150 = term165.
Proof. exact (TRANS (@lem179662) (@lem179678)). Qed.
Lemma lem179680 (h1 : term16) : term165.
Proof. exact (EQ_MP (@lem179679) (@lem179473 h1)). Qed.
Lemma lem179689 (_3728 : nat) (h1 : term16) : term166 _3728.
Proof. exact (@lem179528 h1 _3728). Qed.
Lemma lem179690 (_3728 : nat) : (term166 _3728) = (term157 _3728).
Proof. exact (eq_refl (term166 _3728)). Qed.
Lemma lem179691 (_3728 : nat) (h1 : term16) : term157 _3728.
Proof. exact (EQ_MP (@lem179690 _3728) (@lem179689 _3728 h1)). Qed.
Lemma lem179692 (_3728 : nat) (_3729 : nat) (h1 : term16) : term167 _3728 _3729.
Proof. exact (@lem179691 _3728 h1 _3729). Qed.
Lemma lem179693 (_3728 : nat) (_3729 : nat) : (term167 _3728 _3729) = (term61 _3728 _3729).
Proof. exact (eq_refl (term167 _3728 _3729)). Qed.
Lemma lem179694 (_3728 : nat) (_3729 : nat) (h1 : term16) : term61 _3728 _3729.
Proof. exact (EQ_MP (@lem179693 _3728 _3729) (@lem179692 _3728 _3729 h1)). Qed.
Lemma lem179695 (_3728 : nat) (_3729 : nat) (_3730 : nat) (h1 : term16) : term49 _3728 _3729 _3730.
Proof. exact (@lem179694 _3728 _3729 h1 _3730). Qed.
Lemma lem179696 (_3730 : nat) (_3728 : nat) (_3729 : nat) : (term49 _3728 _3729 _3730) = (term50 _3730 _3728 _3729).
Proof. exact (eq_refl (term49 _3728 _3729 _3730)). Qed.
Lemma lem179716 (_3737 : nat) (h1 : term16) : term168 _3737.
Proof. exact (@lem179680 h1 _3737). Qed.
Lemma lem179717 (_3737 : nat) : (term168 _3737) = (term163 _3737).
Proof. exact (eq_refl (term168 _3737)). Qed.
Lemma lem179718 (_3737 : nat) (h1 : term16) : term163 _3737.
Proof. exact (EQ_MP (@lem179717 _3737) (@lem179716 _3737 h1)). Qed.
Lemma lem179719 (_3737 : nat) (_3738 : nat) (h1 : term16) : term169 _3737 _3738.
Proof. exact (@lem179718 _3737 h1 _3738). Qed.
Lemma lem179720 (_3737 : nat) (_3738 : nat) : (term169 _3737 _3738) = (term66 _3737 _3738).
Proof. exact (eq_refl (term169 _3737 _3738)). Qed.
Lemma lem179721 (_3737 : nat) (_3738 : nat) (h1 : term16) : term66 _3737 _3738.
Proof. exact (EQ_MP (@lem179720 _3737 _3738) (@lem179719 _3737 _3738 h1)). Qed.
Lemma lem179722 (_3737 : nat) (_3738 : nat) (_3739 : nat) (h1 : term16) : term53 _3737 _3738 _3739.
Proof. exact (@lem179721 _3737 _3738 h1 _3739). Qed.
Lemma lem179723 (_3739 : nat) (_3737 : nat) (_3738 : nat) : (term53 _3737 _3738 _3739) = (term54 _3739 _3737 _3738).
Proof. exact (eq_refl (term53 _3737 _3738 _3739)). Qed.
Lemma lem179730 (_3730 : nat) (_3728 : nat) (_3729 : nat) (h1 : term16) : term50 _3730 _3728 _3729.
Proof. exact (EQ_MP (@lem179696 _3730 _3728 _3729) (@lem179695 _3728 _3729 _3730 h1)). Qed.
Lemma lem179740 (n : nat) (m : nat) (h1 : term152 n m) : term170 n m.
Proof. exact (proj2 (@lem179475 n m h1)). Qed.
Lemma lem179752 (_3739 : nat) (_3737 : nat) (_3738 : nat) (h1 : term16) : term54 _3739 _3737 _3738.
Proof. exact (EQ_MP (@lem179723 _3739 _3737 _3738) (@lem179722 _3737 _3738 _3739 h1)). Qed.
Lemma lem179754 (n : nat) (m : nat) (h1 : term153 n m) : term171 n m.
Proof. exact (proj1 (@lem179476 n m h1)). Qed.
Lemma lem179758 (n : nat) (m : nat) (h1 : term152 n m) : term6 n m.
Proof. exact (proj1 (@lem179475 n m h1)). Qed.
Lemma lem179759 (n : nat) (m : nat) (h1 : term152 n m) : term172 n m.
Proof. exact (fun h0 : term171 n m => @lem179758 n m h1). Qed.
Lemma lem179761 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem179762 (n : nat) (m : nat) : (term172 n m) = (term6 n m).
Proof. exact (@lem179761 (term6 n m)). Qed.
Lemma lem179763 (n : nat) (m : nat) (h1 : term152 n m) : term6 n m.
Proof. exact (EQ_MP (@lem179762 n m) (@lem179759 n m h1)). Qed.
Lemma lem179765 (b : Prop) (a : Prop) : (a \/ b) = (term174 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem179766 (_3728 : nat) (_3729 : nat) (_3730 : nat) : (term50 _3730 _3728 _3729) = (term175 _3728 _3729 _3730).
Proof. exact (@lem179765 (term75 _3728 _3729) (term27 _3728 _3729 _3730)). Qed.
Lemma lem179768 (a : Prop) : (term176 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem179769 (_3728 : nat) (_3729 : nat) : (term177 _3728 _3729) = (Peano.lt _3728 _3729).
Proof. exact (@lem179768 (Peano.lt _3728 _3729)). Qed.
Lemma lem179770 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem179771 (_3728 : nat) (_3729 : nat) : (term178 _3728 _3729) = (term179 _3728 _3729).
Proof. exact (MK_COMB (@lem179770) (@lem179769 _3728 _3729)). Qed.
Lemma lem179772 (_3728 : nat) (_3729 : nat) (_3730 : nat) : (term27 _3728 _3729 _3730) = (term27 _3728 _3729 _3730).
Proof. exact (eq_refl (term27 _3728 _3729 _3730)). Qed.
Lemma lem179773 (_3728 : nat) (_3729 : nat) (_3730 : nat) : (term175 _3728 _3729 _3730) = (term180 _3728 _3729 _3730).
Proof. exact (MK_COMB (@lem179771 _3728 _3729) (@lem179772 _3728 _3729 _3730)). Qed.
Lemma lem179774 (_3728 : nat) (_3729 : nat) (_3730 : nat) : (term50 _3730 _3728 _3729) = (term180 _3728 _3729 _3730).
Proof. exact (TRANS (@lem179766 _3728 _3729 _3730) (@lem179773 _3728 _3729 _3730)). Qed.
Lemma lem179777 (_3728 : nat) (_3729 : nat) (_3730 : nat) (h1 : term16) : term180 _3728 _3729 _3730.
Proof. exact (EQ_MP (@lem179774 _3728 _3729 _3730) (@lem179730 _3730 _3728 _3729 h1)). Qed.
Lemma lem179778 (n : nat) (m : nat) (_3730 : nat) (h1 : term16) : term181 n m _3730.
Proof. exact (@lem179777 (Nat.sub n m) m _3730 h1). Qed.
Lemma lem179781 (_3730 : nat) (n : nat) (m : nat) (h1 : term16) (h2 : term152 n m) : term182 n m _3730.
Proof. exact (@lem179778 n m _3730 h1 (@lem179763 n m h2)). Qed.
Lemma lem179782 (n : nat) (m : nat) (h1 : term16) (h2 : term152 n m) : term7 n m.
Proof. exact (@lem179781 m n m h1 h2). Qed.
Lemma lem179783 (n : nat) (m : nat) (h1 : term16) (h2 : term152 n m) : term183 n m.
Proof. exact (fun h0 : term170 n m => @lem179782 n m h1 h2). Qed.
Lemma lem179785 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem179786 (n : nat) (m : nat) : (term183 n m) = (term7 n m).
Proof. exact (@lem179785 (term7 n m)). Qed.
Lemma lem179787 (n : nat) (m : nat) (h1 : term16) (h2 : term152 n m) : term7 n m.
Proof. exact (EQ_MP (@lem179786 n m) (@lem179783 n m h1 h2)). Qed.
Lemma lem179790 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem179792 (n : nat) (m : nat) : (term170 n m) = (term184 n m).
Proof. exact (@lem179790 (term7 n m)). Qed.
Lemma lem179795 (n : nat) (m : nat) (h1 : term152 n m) : term184 n m.
Proof. exact (EQ_MP (@lem179792 n m) (@lem179740 n m h1)). Qed.
Lemma lem179798 (n : nat) (m : nat) (h1 : term16) (h2 : term152 n m) : False.
Proof. exact (@lem179795 n m h2 (@lem179787 n m h1 h2)). Qed.
Lemma lem179799 (n : nat) (m : nat) (h1 : term16) (h2 : term152 n m) : term185.
Proof. exact (fun h0 : ~ False => @lem179798 n m h1 h2). Qed.
Lemma lem179801 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem179802 : term185 = False.
Proof. exact (@lem179801 False). Qed.
Lemma lem179803 (n : nat) (m : nat) (h1 : term16) (h2 : term152 n m) : False.
Proof. exact (EQ_MP (@lem179802) (@lem179799 n m h1 h2)). Qed.
Lemma lem179805 (n : nat) (m : nat) (h1 : term153 n m) : term7 n m.
Proof. exact (proj2 (@lem179476 n m h1)). Qed.
Lemma lem179806 (n : nat) (m : nat) (h1 : term153 n m) : term183 n m.
Proof. exact (fun h0 : term170 n m => @lem179805 n m h1). Qed.
Lemma lem179808 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem179809 (n : nat) (m : nat) : (term183 n m) = (term7 n m).
Proof. exact (@lem179808 (term7 n m)). Qed.
Lemma lem179810 (n : nat) (m : nat) (h1 : term153 n m) : term7 n m.
Proof. exact (EQ_MP (@lem179809 n m) (@lem179806 n m h1)). Qed.
Lemma lem179816 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem179817 (_3737 : nat) (_3738 : nat) (_3739 : nat) : (term54 _3739 _3737 _3738) = (term186 _3737 _3738 _3739).
Proof. exact (@lem179816 (Peano.lt _3737 _3738) (term94 _3737 _3738 _3739)). Qed.
Lemma lem179823 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem179824 (_3737 : nat) (_3738 : nat) (_3739 : nat) : (term187 _3739 _3737 _3738) = (term188 _3737 _3738 _3739).
Proof. exact (MK_COMB (@lem179823) (@lem179817 _3737 _3738 _3739)). Qed.
Lemma lem179830 (_3737 : nat) (_3738 : nat) (_3739 : nat) : (term186 _3737 _3738 _3739) = (term186 _3737 _3738 _3739).
Proof. exact (eq_refl (term186 _3737 _3738 _3739)). Qed.
Lemma lem179831 (_3737 : nat) (_3738 : nat) (_3739 : nat) : ((term54 _3739 _3737 _3738) = (term186 _3737 _3738 _3739)) = ((term186 _3737 _3738 _3739) = (term186 _3737 _3738 _3739)).
Proof. exact (MK_COMB (@lem179824 _3737 _3738 _3739) (@lem179830 _3737 _3738 _3739)). Qed.
Lemma lem179833 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem179834 (x : Prop) : (x = x) = True.
Proof. exact (@lem179833 Prop x). Qed.
Lemma lem179835 (_3737 : nat) (_3738 : nat) (_3739 : nat) : ((term186 _3737 _3738 _3739) = (term186 _3737 _3738 _3739)) = True.
Proof. exact (@lem179834 (term186 _3737 _3738 _3739)). Qed.
Lemma lem179836 (_3737 : nat) (_3738 : nat) (_3739 : nat) : ((term54 _3739 _3737 _3738) = (term186 _3737 _3738 _3739)) = True.
Proof. exact (TRANS (@lem179831 _3737 _3738 _3739) (@lem179835 _3737 _3738 _3739)). Qed.
Lemma lem179837 (_3737 : nat) (_3738 : nat) (_3739 : nat) : True = ((term54 _3739 _3737 _3738) = (term186 _3737 _3738 _3739)).
Proof. exact (SYM (@lem179836 _3737 _3738 _3739)). Qed.
Lemma lem179838 (_3737 : nat) (_3738 : nat) (_3739 : nat) : (term54 _3739 _3737 _3738) = (term186 _3737 _3738 _3739).
Proof. exact (EQ_MP (@lem179837 _3737 _3738 _3739) (@lem0)). Qed.
Lemma lem179839 (_3737 : nat) (_3738 : nat) (_3739 : nat) (h1 : term16) : term186 _3737 _3738 _3739.
Proof. exact (EQ_MP (@lem179838 _3737 _3738 _3739) (@lem179752 _3739 _3737 _3738 h1)). Qed.
Lemma lem179841 (b : Prop) (a : Prop) : (a \/ b) = (term174 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem179842 (_3739 : nat) (_3737 : nat) (_3738 : nat) : (term186 _3737 _3738 _3739) = (term189 _3739 _3737 _3738).
Proof. exact (@lem179841 (term94 _3737 _3738 _3739) (Peano.lt _3737 _3738)). Qed.
Lemma lem179844 (a : Prop) : (term176 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem179845 (_3737 : nat) (_3738 : nat) (_3739 : nat) : (term190 _3737 _3738 _3739) = (term27 _3737 _3738 _3739).
Proof. exact (@lem179844 (term27 _3737 _3738 _3739)). Qed.
Lemma lem179846 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem179847 (_3737 : nat) (_3738 : nat) (_3739 : nat) : (term191 _3737 _3738 _3739) = (term192 _3737 _3738 _3739).
Proof. exact (MK_COMB (@lem179846) (@lem179845 _3737 _3738 _3739)). Qed.
Lemma lem179848 (_3737 : nat) (_3738 : nat) : (Peano.lt _3737 _3738) = (Peano.lt _3737 _3738).
Proof. exact (eq_refl (Peano.lt _3737 _3738)). Qed.
Lemma lem179849 (_3739 : nat) (_3737 : nat) (_3738 : nat) : (term189 _3739 _3737 _3738) = (term193 _3739 _3737 _3738).
Proof. exact (MK_COMB (@lem179847 _3737 _3738 _3739) (@lem179848 _3737 _3738)). Qed.
Lemma lem179850 (_3739 : nat) (_3737 : nat) (_3738 : nat) : (term186 _3737 _3738 _3739) = (term193 _3739 _3737 _3738).
Proof. exact (TRANS (@lem179842 _3739 _3737 _3738) (@lem179849 _3739 _3737 _3738)). Qed.
Lemma lem179853 (_3739 : nat) (_3737 : nat) (_3738 : nat) (h1 : term16) : term193 _3739 _3737 _3738.
Proof. exact (EQ_MP (@lem179850 _3739 _3737 _3738) (@lem179839 _3737 _3738 _3739 h1)). Qed.
Lemma lem179854 (n : nat) (m : nat) (h1 : term16) : term194 n m.
Proof. exact (@lem179853 m (Nat.sub n m) m h1). Qed.
Lemma lem179857 (n : nat) (m : nat) (h1 : term16) (h2 : term153 n m) : term6 n m.
Proof. exact (@lem179854 n m h1 (@lem179810 n m h2)). Qed.
Lemma lem179858 (n : nat) (m : nat) (h1 : term16) (h2 : term153 n m) : term172 n m.
Proof. exact (fun h0 : term171 n m => @lem179857 n m h1 h2). Qed.
Lemma lem179860 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem179861 (n : nat) (m : nat) : (term172 n m) = (term6 n m).
Proof. exact (@lem179860 (term6 n m)). Qed.
Lemma lem179862 (n : nat) (m : nat) (h1 : term16) (h2 : term153 n m) : term6 n m.
Proof. exact (EQ_MP (@lem179861 n m) (@lem179858 n m h1 h2)). Qed.
Lemma lem179865 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem179867 (n : nat) (m : nat) : (term171 n m) = (term195 n m).
Proof. exact (@lem179865 (term6 n m)). Qed.
Lemma lem179870 (n : nat) (m : nat) (h1 : term153 n m) : term195 n m.
Proof. exact (EQ_MP (@lem179867 n m) (@lem179754 n m h1)). Qed.
Lemma lem179873 (n : nat) (m : nat) (h1 : term16) (h2 : term153 n m) : False.
Proof. exact (@lem179870 n m h2 (@lem179862 n m h1 h2)). Qed.
Lemma lem179874 (n : nat) (m : nat) (h1 : term16) (h2 : term153 n m) : term185.
Proof. exact (fun h0 : ~ False => @lem179873 n m h1 h2). Qed.
Lemma lem179876 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem179877 : term185 = False.
Proof. exact (@lem179876 False). Qed.
Lemma lem179878 (n : nat) (m : nat) (h1 : term16) (h2 : term153 n m) : False.
Proof. exact (EQ_MP (@lem179877) (@lem179874 n m h1 h2)). Qed.
Lemma lem179879 (n : nat) (m : nat) (h1 : term16) (h2 : term9 n m) : False.
Proof. exact (or_elim (@lem179404 n m h2) (fun h0 : term152 n m => @lem179803 n m h1 h0) (fun h0 : term153 n m => @lem179878 n m h1 h0)). Qed.
Lemma lem179880 (n : nat) (m : nat) (h1 : term9 n m) : term14.
Proof. exact (fun h0 : term16 => @lem179879 n m h0 h1). Qed.
Lemma lem179881 : term14 = term15.
Proof. exact (@lem69 term16). Qed.
Lemma lem179882 (n : nat) (m : nat) (h1 : term9 n m) : term15.
Proof. exact (EQ_MP (@lem179881) (@lem179880 n m h1)). Qed.
Lemma lem179883 (n : nat) (m : nat) : term18 n m.
Proof. exact (fun h0 : term9 n m => @lem179882 n m h0). Qed.
Lemma lem179888 (m : nat) : term22 m.
Proof. exact (fun n : nat => @lem179883 n m). Qed.
Lemma lem179893 : term26.
Proof. exact (fun m : nat => @lem179888 m). Qed.
Lemma lem179894 : term25.
Proof. exact (EQ_MP (@lem178875) (@lem179893)). Qed.
Lemma lem179895 (m : nat) : term196 m.
Proof. exact (@lem179894 m). Qed.
Lemma lem179896 (m : nat) : (term196 m) = (term21 m).
Proof. exact (eq_refl (term196 m)). Qed.
Lemma lem179897 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem179896 m) (@lem179895 m)). Qed.
Lemma lem179898 (m : nat) (n : nat) : term197 m n.
Proof. exact (@lem179897 m n). Qed.
Lemma lem179899 (n : nat) (m : nat) : (term197 m n) = (term10 n m).
Proof. exact (eq_refl (term197 m n)). Qed.
Lemma lem179900 (n : nat) (m : nat) : term10 n m.
Proof. exact (EQ_MP (@lem179899 n m) (@lem179898 m n)). Qed.
Lemma lem179902 (n : nat) (m : nat) : term10 n m.
Proof. exact (@lem178760 n m (@lem179900 n m)). Qed.
Lemma lem179903 (n : nat) (m : nat) (h1 : term9 n m) : term14.
Proof. exact (@lem179902 n m (@lem178745 n m h1)). Qed.
Lemma lem179904 (n : nat) (m : nat) (h1 : term9 n m) : False.
Proof. exact (@lem179903 n m h1 (@lem101179)). Qed.
Lemma lem179905 (n : nat) (m : nat) (h1 : term9 n m) : (term9 n m) = False.
Proof. exact (prop_ext (fun h2 : term9 n m => @lem179904 n m h1) (fun h2 : False => @lem178745 n m h1)). Qed.
Lemma lem179906 (n : nat) (m : nat) (h1 : term9 n m) : False.
Proof. exact (EQ_MP (@lem179905 n m h1) (@lem178745 n m h1)). Qed.
Lemma lem179907 (n : nat) (m : nat) : term8 n m.
Proof. exact (fun h0 : term9 n m => @lem179906 n m h0). Qed.
Lemma lem179909 (m : nat) : term198 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem179910 (m : nat) : (term198 m) = (term199 m).
Proof. exact (eq_refl (term198 m)). Qed.
Lemma lem179911 (m : nat) : term199 m.
Proof. exact (EQ_MP (@lem179910 m) (@lem179909 m)). Qed.
Lemma lem179912 (m : nat) (n : nat) : term200 m n.
Proof. exact (@lem179911 m n). Qed.
Lemma lem179913 (n : nat) (m : nat) : (term200 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term200 m n)). Qed.
Lemma lem179915 (h1 : term201) : term201.
Proof. exact (h1). Qed.
Lemma lem179916 (m : nat) (h1 : term201) : term202 m.
Proof. exact (@lem179915 h1 m). Qed.
Lemma lem179917 (m : nat) : (term202 m) = (term203 m).
Proof. exact (eq_refl (term202 m)). Qed.
Lemma lem179918 (m : nat) (h1 : term201) : term203 m.
Proof. exact (EQ_MP (@lem179917 m) (@lem179916 m h1)). Qed.
Lemma lem179919 (m : nat) (n : nat) (h1 : term201) : term204 m n.
Proof. exact (@lem179918 m h1 n). Qed.
Lemma lem179920 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (eq_refl (term204 m n)). Qed.
Lemma lem179921 (m : nat) (n : nat) (h1 : term201) : term205 m n.
Proof. exact (EQ_MP (@lem179920 m n) (@lem179919 m n h1)). Qed.
Lemma lem179922 (m : nat) (n : nat) (q : nat) (h1 : term201) : term206 m n q.
Proof. exact (@lem179921 m n h1 q). Qed.
Lemma lem179923 (q : nat) (m : nat) (n : nat) : (term206 m n q) = (term207 q m n).
Proof. exact (eq_refl (term206 m n q)). Qed.
Lemma lem179924 (q : nat) (m : nat) (n : nat) (h1 : term201) : term207 q m n.
Proof. exact (EQ_MP (@lem179923 q m n) (@lem179922 m n q h1)). Qed.
Lemma lem179925 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term201) : term208 q m n r.
Proof. exact (@lem179924 q m n h1 r). Qed.
Lemma lem179926 (q : nat) (m : nat) (n : nat) (r : nat) : (term208 q m n r) = (term209 q m n r).
Proof. exact (eq_refl (term208 q m n r)). Qed.
Lemma lem179927 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term201) : term209 q m n r.
Proof. exact (EQ_MP (@lem179926 q m n r) (@lem179925 q m n r h1)). Qed.
Lemma lem179928 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term210 m q r n) : term210 m q r n.
Proof. exact (h1). Qed.
Lemma lem179929 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term201) (h2 : term210 m q r n) : (Nat.modulo m n) = r.
Proof. exact (@lem179927 q m n r h1 (@lem179928 m q r n h2)). Qed.
Lemma lem179930 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term210 m q r n) : term211 m n r.
Proof. exact (fun h0 : term201 => @lem179929 m q r n h0 h1). Qed.
Lemma lem179931 (m : nat) (r : nat) (n : nat) (h1 : term212 m r n) : term212 m r n.
Proof. exact (h1). Qed.
Lemma lem179932 (m : nat) (r : nat) (n : nat) (h1 : term212 m r n) : term211 m n r.
Proof. exact (ex_elim (@lem179931 m r n h1) (fun q : nat => fun h0 : term213 m r n q => @lem179930 m q r n h0)). Qed.
Lemma lem179933 (h1 : term201) : term201.
Proof. exact (h1). Qed.
Lemma lem179934 (m : nat) (r : nat) (n : nat) (h1 : term201) (h2 : term212 m r n) : (Nat.modulo m n) = r.
Proof. exact (@lem179932 m r n h2 (@lem179933 h1)). Qed.
Lemma lem179935 (m : nat) (n : nat) (r : nat) (h1 : term201) : term214 m n r.
Proof. exact (fun h0 : term212 m r n => @lem179934 m r n h1 h0). Qed.
Lemma lem179936 (m : nat) (n : nat) (h1 : term201) : term215 m n.
Proof. exact (fun r : nat => @lem179935 m n r h1). Qed.
Lemma lem179937 (m : nat) (h1 : term201) : term216 m.
Proof. exact (fun n : nat => @lem179936 m n h1). Qed.
Lemma lem179938 (h1 : term201) : term217.
Proof. exact (fun m : nat => @lem179937 m h1). Qed.
Lemma lem179939 : term218.
Proof. exact (fun h0 : term201 => @lem179938 h0). Qed.
Lemma lem179940 : term217.
Proof. exact (@lem179939 (@lem169705)). Qed.
Lemma lem179941 (m : nat) : term219 m.
Proof. exact (@lem179940 m). Qed.
Lemma lem179942 (m : nat) : (term219 m) = (term216 m).
Proof. exact (eq_refl (term219 m)). Qed.
Lemma lem179943 (m : nat) : term216 m.
Proof. exact (EQ_MP (@lem179942 m) (@lem179941 m)). Qed.
Lemma lem179944 (m : nat) (n : nat) : term220 m n.
Proof. exact (@lem179943 m n). Qed.
Lemma lem179945 (m : nat) (n : nat) : (term220 m n) = (term215 m n).
Proof. exact (eq_refl (term220 m n)). Qed.
Lemma lem179946 (m : nat) (n : nat) : term215 m n.
Proof. exact (EQ_MP (@lem179945 m n) (@lem179944 m n)). Qed.
Lemma lem179947 (m : nat) (n : nat) (r : nat) : term221 m n r.
Proof. exact (@lem179946 m n r). Qed.
Lemma lem179948 (m : nat) (n : nat) (r : nat) : (term221 m n r) = (term214 m n r).
Proof. exact (eq_refl (term221 m n r)). Qed.
Lemma lem179950 (m : nat) : term198 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem179951 (m : nat) : (term198 m) = (term199 m).
Proof. exact (eq_refl (term198 m)). Qed.
Lemma lem179952 (m : nat) : term199 m.
Proof. exact (EQ_MP (@lem179951 m) (@lem179950 m)). Qed.
Lemma lem179953 (m : nat) (n : nat) : term200 m n.
Proof. exact (@lem179952 m n). Qed.
Lemma lem179954 (n : nat) (m : nat) : (term200 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term200 m n)). Qed.
Lemma lem179956 (m : nat) : term222 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem179957 (m : nat) : (term222 m) = (term223 m).
Proof. exact (eq_refl (term222 m)). Qed.
Lemma lem179958 (m : nat) : term223 m.
Proof. exact (EQ_MP (@lem179957 m) (@lem179956 m)). Qed.
Lemma lem179959 (m : nat) (n : nat) : term224 m n.
Proof. exact (@lem179958 m n). Qed.
Lemma lem179960 (n : nat) (m : nat) : (term224 m n) = ((term225 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term224 m n)). Qed.
Lemma lem179962 (m : nat) (n : nat) : term226 m n.
Proof. exact (@lem9784 (term227 m n)). Qed.
Lemma lem179963 (m : nat) (n : nat) : (term226 m n) = (term228 m n).
Proof. exact (eq_refl (term226 m n)). Qed.
Lemma lem179964 (m : nat) (n : nat) : term228 m n.
Proof. exact (EQ_MP (@lem179963 m n) (@lem179962 m n)). Qed.
Lemma lem179965 (m : nat) (n : nat) (h1 : term227 m n) : term227 m n.
Proof. exact (h1). Qed.
Lemma lem179966 (m : nat) (n : nat) (h1 : term229 m n) : term229 m n.
Proof. exact (h1). Qed.
Lemma lem179967 (m : nat) (n : nat) (h1 : term230 m n) : term230 m n.
Proof. exact (h1). Qed.
Lemma lem179968 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem179969 (m : nat) (h1 : term231 m) : term231 m.
Proof. exact (h1). Qed.
Lemma lem179970 (h1 : term232) : term232.
Proof. exact (h1). Qed.
Lemma lem179971 (m : nat) (h1 : term232) : term233 m.
Proof. exact (@lem179970 h1 m). Qed.
Lemma lem179972 (m : nat) : (term233 m) = (term234 m).
Proof. exact (eq_refl (term233 m)). Qed.
Lemma lem179973 (m : nat) (h1 : term232) : term234 m.
Proof. exact (EQ_MP (@lem179972 m) (@lem179971 m h1)). Qed.
Lemma lem179974 (m : nat) (n : nat) (h1 : term232) : term235 m n.
Proof. exact (@lem179973 m h1 n). Qed.
Lemma lem179975 (n : nat) (m : nat) : (term235 m n) = (term236 n m).
Proof. exact (eq_refl (term235 m n)). Qed.
Lemma lem179976 (n : nat) (m : nat) (h1 : term232) : term236 n m.
Proof. exact (EQ_MP (@lem179975 n m) (@lem179974 m n h1)). Qed.
Lemma lem179977 (n : nat) (m : nat) (p : nat) (h1 : term232) : term237 n m p.
Proof. exact (@lem179976 n m h1 p). Qed.
Lemma lem179978 (n : nat) (m : nat) (p : nat) : (term237 n m p) = (term238 n m p).
Proof. exact (eq_refl (term237 n m p)). Qed.
Lemma lem179979 (n : nat) (m : nat) (p : nat) (h1 : term232) : term238 n m p.
Proof. exact (EQ_MP (@lem179978 n m p) (@lem179977 n m p h1)). Qed.
Lemma lem179980 (m : nat) (n : nat) (p : nat) (h1 : term239 m n p) : term239 m n p.
Proof. exact (h1). Qed.
Lemma lem179981 (m : nat) (n : nat) (p : nat) (h1 : term232) (h2 : term239 m n p) : Peano.le m p.
Proof. exact (@lem179979 n m p h1 (@lem179980 m n p h2)). Qed.
Lemma lem179982 (m : nat) (n : nat) (p : nat) (h1 : term239 m n p) : term240 m p.
Proof. exact (fun h0 : term232 => @lem179981 m n p h0 h1). Qed.
Lemma lem179983 (m : nat) (p : nat) (h1 : term241 m p) : term241 m p.
Proof. exact (h1). Qed.
Lemma lem179984 (m : nat) (p : nat) (h1 : term241 m p) : term240 m p.
Proof. exact (ex_elim (@lem179983 m p h1) (fun n : nat => fun h0 : term242 m p n => @lem179982 m n p h0)). Qed.
Lemma lem179985 (h1 : term232) : term232.
Proof. exact (h1). Qed.
Lemma lem179986 (m : nat) (p : nat) (h1 : term232) (h2 : term241 m p) : Peano.le m p.
Proof. exact (@lem179984 m p h2 (@lem179985 h1)). Qed.
Lemma lem179987 (m : nat) (p : nat) (h1 : term232) : term243 m p.
Proof. exact (fun h0 : term241 m p => @lem179986 m p h1 h0). Qed.
Lemma lem179988 (m : nat) (h1 : term232) : term244 m.
Proof. exact (fun p : nat => @lem179987 m p h1). Qed.
Lemma lem179989 (h1 : term232) : term245.
Proof. exact (fun m : nat => @lem179988 m h1). Qed.
Lemma lem179990 : term246.
Proof. exact (fun h0 : term232 => @lem179989 h0). Qed.
Lemma lem179991 : term245.
Proof. exact (@lem179990 (@lem93743)). Qed.
Lemma lem179992 (m : nat) : term247 m.
Proof. exact (@lem179991 m). Qed.
Lemma lem179993 (m : nat) : (term247 m) = (term244 m).
Proof. exact (eq_refl (term247 m)). Qed.
Lemma lem179994 (m : nat) : term244 m.
Proof. exact (EQ_MP (@lem179993 m) (@lem179992 m)). Qed.
Lemma lem179995 (m : nat) (p : nat) : term248 m p.
Proof. exact (@lem179994 m p). Qed.
Lemma lem179996 (m : nat) (p : nat) : (term248 m p) = (term243 m p).
Proof. exact (eq_refl (term248 m p)). Qed.
Lemma lem179999 (m : nat) (p : nat) : term243 m p.
Proof. exact (EQ_MP (@lem179996 m p) (@lem179995 m p)). Qed.
Lemma lem180000 (m : nat) (n : nat) : term249 m n.
Proof. exact (@lem179999 (term250 n m) n). Qed.
Lemma lem180001 : term251.
Proof. exact (proj2 (@lem99082)). Qed.
Lemma lem180002 : term252.
Proof. exact (proj2 (@lem180001)). Qed.
Lemma lem180060 : term253.
Proof. exact (proj1 (@lem180002)). Qed.
Lemma lem180061 (n : nat) : term254 n.
Proof. exact (@lem180060 n). Qed.
Lemma lem180062 (n : nat) : (term254 n) = (term255 n).
Proof. exact (eq_refl (term254 n)). Qed.
Lemma lem180063 (n : nat) : term255 n.
Proof. exact (EQ_MP (@lem180062 n) (@lem180061 n)). Qed.
Lemma lem180064 (n : nat) (h1 : term231 n) : term231 n.
Proof. exact (h1). Qed.
Lemma lem180065 (n : nat) (h1 : term231 n) : term256 n.
Proof. exact (@lem180063 n (@lem180064 n h1)). Qed.
Lemma lem180066 (n : nat) : term257 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem180067 (n : nat) (h1 : term231 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem180066 n (@lem180065 n h1)). Qed.
Lemma lem180115 (m : nat) : term258 m.
Proof. exact (@lem98439 m). Qed.
Lemma lem180116 (m : nat) : (term258 m) = (term259 m).
Proof. exact (eq_refl (term258 m)). Qed.
Lemma lem180117 (m : nat) : term259 m.
Proof. exact (EQ_MP (@lem180116 m) (@lem180115 m)). Qed.
Lemma lem180118 (m : nat) (n : nat) : term260 m n.
Proof. exact (@lem180117 m n). Qed.
Lemma lem180119 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (eq_refl (term260 m n)). Qed.
Lemma lem180120 (m : nat) (n : nat) : term261 m n.
Proof. exact (EQ_MP (@lem180119 m n) (@lem180118 m n)). Qed.
Lemma lem180121 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem180122 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.le m n.
Proof. exact (@lem180120 m n (@lem180121 m n h1)). Qed.
Lemma lem180123 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem180124 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem180123 m n) (@lem180122 m n h1)). Qed.
Lemma lem180130 (m : nat) : term262 m.
Proof. exact (@lem157261 m). Qed.
Lemma lem180131 (m : nat) : (term262 m) = (term263 m).
Proof. exact (eq_refl (term262 m)). Qed.
Lemma lem180132 (m : nat) : term263 m.
Proof. exact (EQ_MP (@lem180131 m) (@lem180130 m)). Qed.
Lemma lem180133 (m : nat) (n : nat) : term264 m n.
Proof. exact (@lem180132 m n). Qed.
Lemma lem180134 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (eq_refl (term264 m n)). Qed.
Lemma lem180135 (m : nat) (n : nat) : term265 m n.
Proof. exact (EQ_MP (@lem180134 m n) (@lem180133 m n)). Qed.
Lemma lem180136 (n : nat) (h1 : term256 n) : term256 n.
Proof. exact (h1). Qed.
Lemma lem180137 (m : nat) (n : nat) (h1 : term256 n) : term266 m n.
Proof. exact (@lem180135 m n (@lem180136 n h1)). Qed.
Lemma lem180138 (m : nat) (n : nat) (h1 : term256 n) : term267 m n.
Proof. exact (proj2 (@lem180137 m n h1)). Qed.
Lemma lem180139 (m : nat) (n : nat) : (term267 m n) = ((term267 m n) = True).
Proof. exact (@lem7 (term267 m n)). Qed.
Lemma lem180140 (m : nat) (n : nat) (h1 : term256 n) : (term267 m n) = True.
Proof. exact (EQ_MP (@lem180139 m n) (@lem180138 m n h1)). Qed.
Lemma lem180157 (m : nat) : term268 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem180158 (m : nat) : (term268 m) = (term269 m).
Proof. exact (eq_refl (term268 m)). Qed.
Lemma lem180159 (m : nat) : term269 m.
Proof. exact (EQ_MP (@lem180158 m) (@lem180157 m)). Qed.
Lemma lem180160 (m : nat) (n : nat) : term270 m n.
Proof. exact (@lem180159 m n). Qed.
Lemma lem180161 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (eq_refl (term270 m n)). Qed.
Lemma lem180162 (m : nat) (n : nat) : term271 m n.
Proof. exact (EQ_MP (@lem180161 m n) (@lem180160 m n)). Qed.
Lemma lem180163 (m : nat) (n : nat) (p : nat) : term272 m n p.
Proof. exact (@lem180162 m n p). Qed.
Lemma lem180164 (m : nat) (n : nat) (p : nat) : (term272 m n p) = ((term273 n m p) = (term274 m n p)).
Proof. exact (eq_refl (term272 m n p)). Qed.
Lemma lem180166 (m : nat) : (term231 m) = ((term231 m) = True).
Proof. exact (@lem7 (term231 m)). Qed.
Lemma lem180170 (m : nat) (n : nat) : (term227 m n) = ((term227 m n) = True).
Proof. exact (@lem7 (term227 m n)). Qed.
Lemma lem180181 (m : nat) (n : nat) (p : nat) : (term273 n m p) = (term274 m n p).
Proof. exact (EQ_MP (@lem180164 m n p) (@lem180163 m n p)). Qed.
Lemma lem180182 (n : nat) (m : nat) : (term275 n m) = (term276 n m).
Proof. exact (@lem180181 term277 (Nat.modulo n m) m). Qed.
Lemma lem180825 (m : nat) (n : nat) : term278 m n.
Proof. exact (fun h0 : Peano.lt m n => @lem180124 m n h0). Qed.
Lemma lem180826 (n : nat) (m : nat) : term279 n m.
Proof. exact (@lem180825 (Nat.modulo n m) m). Qed.
Lemma lem180828 (m : nat) (n : nat) : term280 m n.
Proof. exact (fun h0 : term256 n => @lem180140 m n h0). Qed.
Lemma lem180829 (n : nat) (m : nat) : term280 n m.
Proof. exact (@lem180828 n m). Qed.
Lemma lem180867 (n : nat) : term281 n.
Proof. exact (fun h0 : term231 n => @lem180067 n h0). Qed.
Lemma lem180868 (m : nat) : term281 m.
Proof. exact (@lem180867 m). Qed.
Lemma lem180870 (m : nat) (h1 : term231 m) : (term231 m) = True.
Proof. exact (EQ_MP (@lem180166 m) (@lem179969 m h1)). Qed.
Lemma lem180873 (m : nat) (h1 : term231 m) : True = (term231 m).
Proof. exact (SYM (@lem180870 m h1)). Qed.
Lemma lem180874 (m : nat) (h1 : term231 m) : term231 m.
Proof. exact (EQ_MP (@lem180873 m h1) (@lem0)). Qed.
Lemma lem180875 (m : nat) (h1 : term231 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem180868 m (@lem180874 m h1)). Qed.
Lemma lem180878 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem180879 (m : nat) (h1 : term231 m) : (term256 m) = (~ False).
Proof. exact (MK_COMB (@lem180878) (@lem180875 m h1)). Qed.
Lemma lem180881 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem180884 (m : nat) (h1 : term231 m) : (term256 m) = True.
Proof. exact (TRANS (@lem180879 m h1) (@lem180881)). Qed.
Lemma lem180885 (m : nat) (h1 : term231 m) : True = (term256 m).
Proof. exact (SYM (@lem180884 m h1)). Qed.
Lemma lem180886 (m : nat) (h1 : term231 m) : term256 m.
Proof. exact (EQ_MP (@lem180885 m h1) (@lem0)). Qed.
Lemma lem180887 (n : nat) (m : nat) (h1 : term231 m) : (term267 n m) = True.
Proof. exact (@lem180829 n m (@lem180886 m h1)). Qed.
Lemma lem180890 (n : nat) (m : nat) (h1 : term231 m) : True = (term267 n m).
Proof. exact (SYM (@lem180887 n m h1)). Qed.
Lemma lem180891 (n : nat) (m : nat) (h1 : term231 m) : term267 n m.
Proof. exact (EQ_MP (@lem180890 n m h1) (@lem0)). Qed.
Lemma lem180892 (n : nat) (m : nat) (h1 : term231 m) : (term282 n m) = True.
Proof. exact (@lem180826 n m (@lem180891 n m h1)). Qed.
Lemma lem180895 : term283 = term283.
Proof. exact (eq_refl term283). Qed.
Lemma lem180896 (n : nat) (m : nat) (h1 : term231 m) : (term276 n m) = term284.
Proof. exact (MK_COMB (@lem180895) (@lem180892 n m h1)). Qed.
Lemma lem180898 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem180899 : term284 = True.
Proof. exact (@lem180898 (term277 = (NUMERAL 0))). Qed.
Lemma lem180902 (n : nat) (m : nat) (h1 : term231 m) : (term276 n m) = True.
Proof. exact (TRANS (@lem180896 n m h1) (@lem180899)). Qed.
Lemma lem180903 (n : nat) (m : nat) (h1 : term231 m) : (term275 n m) = True.
Proof. exact (TRANS (@lem180182 n m) (@lem180902 n m h1)). Qed.
Lemma lem180904 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem180905 (n : nat) (m : nat) (h1 : term231 m) : (term285 n m) = (and True).
Proof. exact (MK_COMB (@lem180904) (@lem180903 n m h1)). Qed.
Lemma lem180913 (m : nat) (n : nat) (h1 : term227 m n) : (term227 m n) = True.
Proof. exact (EQ_MP (@lem180170 m n) (@lem179965 m n h1)). Qed.
Lemma lem180916 (m : nat) (n : nat) (h1 : term231 m) (h2 : term227 m n) : (term286 m n) = (True /\ True).
Proof. exact (MK_COMB (@lem180905 n m h1) (@lem180913 m n h2)). Qed.
Lemma lem180918 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem180919 : (True /\ True) = True.
Proof. exact (@lem180918 True). Qed.
Lemma lem180922 (m : nat) (n : nat) (h1 : term231 m) (h2 : term227 m n) : (term286 m n) = True.
Proof. exact (TRANS (@lem180916 m n h1 h2) (@lem180919)). Qed.
Lemma lem180923 (m : nat) (n : nat) (h1 : term231 m) (h2 : term227 m n) : True = (term286 m n).
Proof. exact (SYM (@lem180922 m n h1 h2)). Qed.
Lemma lem180924 (m : nat) (n : nat) (h1 : term231 m) (h2 : term227 m n) : term286 m n.
Proof. exact (EQ_MP (@lem180923 m n h1 h2) (@lem0)). Qed.
Lemma lem180925 (m : nat) (n : nat) (h1 : term231 m) (h2 : term227 m n) : term287 m n.
Proof. exact (ex_intro (term288 m n) (term0 m) (@lem180924 m n h1 h2)). Qed.
Lemma lem180926 (m : nat) (n : nat) (h1 : term231 m) (h2 : term227 m n) : term289 m n.
Proof. exact (@lem180000 m n (@lem180925 m n h1 h2)). Qed.
Lemma lem180928 (m : nat) (h1 : term231 m) : term231 m.
Proof. exact (h1). Qed.
Lemma lem180930 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem180932 (n : nat) (m : nat) : (term225 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem179960 n m) (@lem179959 m n)). Qed.
Lemma lem180933 (n : nat) (m : nat) : (term229 m n) = (term290 n m).
Proof. exact (@lem180932 n (term0 m)). Qed.
Lemma lem180934 (m : nat) (n : nat) (h1 : term229 m n) : term290 n m.
Proof. exact (EQ_MP (@lem180933 n m) (@lem179966 m n h1)). Qed.
Lemma lem180935 (h1 : term232) : term232.
Proof. exact (h1). Qed.
Lemma lem180936 (m : nat) (h1 : term232) : term233 m.
Proof. exact (@lem180935 h1 m). Qed.
Lemma lem180937 (m : nat) : (term233 m) = (term234 m).
Proof. exact (eq_refl (term233 m)). Qed.
Lemma lem180938 (m : nat) (h1 : term232) : term234 m.
Proof. exact (EQ_MP (@lem180937 m) (@lem180936 m h1)). Qed.
Lemma lem180939 (m : nat) (n : nat) (h1 : term232) : term235 m n.
Proof. exact (@lem180938 m h1 n). Qed.
Lemma lem180940 (n : nat) (m : nat) : (term235 m n) = (term236 n m).
Proof. exact (eq_refl (term235 m n)). Qed.
Lemma lem180941 (n : nat) (m : nat) (h1 : term232) : term236 n m.
Proof. exact (EQ_MP (@lem180940 n m) (@lem180939 m n h1)). Qed.
Lemma lem180942 (n : nat) (m : nat) (p : nat) (h1 : term232) : term237 n m p.
Proof. exact (@lem180941 n m h1 p). Qed.
Lemma lem180943 (n : nat) (m : nat) (p : nat) : (term237 n m p) = (term238 n m p).
Proof. exact (eq_refl (term237 n m p)). Qed.
Lemma lem180944 (n : nat) (m : nat) (p : nat) (h1 : term232) : term238 n m p.
Proof. exact (EQ_MP (@lem180943 n m p) (@lem180942 n m p h1)). Qed.
Lemma lem180945 (m : nat) (n : nat) (p : nat) (h1 : term239 m n p) : term239 m n p.
Proof. exact (h1). Qed.
Lemma lem180946 (m : nat) (n : nat) (p : nat) (h1 : term232) (h2 : term239 m n p) : Peano.le m p.
Proof. exact (@lem180944 n m p h1 (@lem180945 m n p h2)). Qed.
Lemma lem180947 (m : nat) (n : nat) (p : nat) (h1 : term239 m n p) : term240 m p.
Proof. exact (fun h0 : term232 => @lem180946 m n p h0 h1). Qed.
Lemma lem180948 (m : nat) (p : nat) (h1 : term241 m p) : term241 m p.
Proof. exact (h1). Qed.
Lemma lem180949 (m : nat) (p : nat) (h1 : term241 m p) : term240 m p.
Proof. exact (ex_elim (@lem180948 m p h1) (fun n : nat => fun h0 : term242 m p n => @lem180947 m n p h0)). Qed.
Lemma lem180950 (h1 : term232) : term232.
Proof. exact (h1). Qed.
Lemma lem180951 (m : nat) (p : nat) (h1 : term232) (h2 : term241 m p) : Peano.le m p.
Proof. exact (@lem180949 m p h2 (@lem180950 h1)). Qed.
Lemma lem180952 (m : nat) (p : nat) (h1 : term232) : term243 m p.
Proof. exact (fun h0 : term241 m p => @lem180951 m p h1 h0). Qed.
Lemma lem180953 (m : nat) (h1 : term232) : term244 m.
Proof. exact (fun p : nat => @lem180952 m p h1). Qed.
Lemma lem180954 (h1 : term232) : term245.
Proof. exact (fun m : nat => @lem180953 m h1). Qed.
Lemma lem180955 : term246.
Proof. exact (fun h0 : term232 => @lem180954 h0). Qed.
Lemma lem180956 : term245.
Proof. exact (@lem180955 (@lem93743)). Qed.
Lemma lem180957 (m : nat) : term247 m.
Proof. exact (@lem180956 m). Qed.
Lemma lem180958 (m : nat) : (term247 m) = (term244 m).
Proof. exact (eq_refl (term247 m)). Qed.
Lemma lem180959 (m : nat) : term244 m.
Proof. exact (EQ_MP (@lem180958 m) (@lem180957 m)). Qed.
Lemma lem180960 (m : nat) (p : nat) : term248 m p.
Proof. exact (@lem180959 m p). Qed.
Lemma lem180961 (m : nat) (p : nat) : (term248 m p) = (term243 m p).
Proof. exact (eq_refl (term248 m p)). Qed.
Lemma lem180964 (m : nat) (p : nat) : term243 m p.
Proof. exact (EQ_MP (@lem180961 m p) (@lem180960 m p)). Qed.
Lemma lem180965 (m : nat) (n : nat) : term249 m n.
Proof. exact (@lem180964 (term250 n m) n). Qed.
Lemma lem180966 : term251.
Proof. exact (proj2 (@lem99082)). Qed.
Lemma lem180967 : term252.
Proof. exact (proj2 (@lem180966)). Qed.
Lemma lem181025 : term253.
Proof. exact (proj1 (@lem180967)). Qed.
Lemma lem181026 (n : nat) : term254 n.
Proof. exact (@lem181025 n). Qed.
Lemma lem181027 (n : nat) : (term254 n) = (term255 n).
Proof. exact (eq_refl (term254 n)). Qed.
Lemma lem181028 (n : nat) : term255 n.
Proof. exact (EQ_MP (@lem181027 n) (@lem181026 n)). Qed.
Lemma lem181029 (n : nat) (h1 : term231 n) : term231 n.
Proof. exact (h1). Qed.
Lemma lem181030 (n : nat) (h1 : term231 n) : term256 n.
Proof. exact (@lem181028 n (@lem181029 n h1)). Qed.
Lemma lem181031 (n : nat) : term257 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem181032 (n : nat) (h1 : term231 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem181031 n (@lem181030 n h1)). Qed.
Lemma lem181080 (m : nat) : term258 m.
Proof. exact (@lem98439 m). Qed.
Lemma lem181081 (m : nat) : (term258 m) = (term259 m).
Proof. exact (eq_refl (term258 m)). Qed.
Lemma lem181082 (m : nat) : term259 m.
Proof. exact (EQ_MP (@lem181081 m) (@lem181080 m)). Qed.
Lemma lem181083 (m : nat) (n : nat) : term260 m n.
Proof. exact (@lem181082 m n). Qed.
Lemma lem181084 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (eq_refl (term260 m n)). Qed.
Lemma lem181085 (m : nat) (n : nat) : term261 m n.
Proof. exact (EQ_MP (@lem181084 m n) (@lem181083 m n)). Qed.
Lemma lem181086 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem181087 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.le m n.
Proof. exact (@lem181085 m n (@lem181086 m n h1)). Qed.
Lemma lem181088 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem181089 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem181088 m n) (@lem181087 m n h1)). Qed.
Lemma lem181095 (m : nat) : term262 m.
Proof. exact (@lem157261 m). Qed.
Lemma lem181096 (m : nat) : (term262 m) = (term263 m).
Proof. exact (eq_refl (term262 m)). Qed.
Lemma lem181097 (m : nat) : term263 m.
Proof. exact (EQ_MP (@lem181096 m) (@lem181095 m)). Qed.
Lemma lem181098 (m : nat) (n : nat) : term264 m n.
Proof. exact (@lem181097 m n). Qed.
Lemma lem181099 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (eq_refl (term264 m n)). Qed.
Lemma lem181100 (m : nat) (n : nat) : term265 m n.
Proof. exact (EQ_MP (@lem181099 m n) (@lem181098 m n)). Qed.
Lemma lem181101 (n : nat) (h1 : term256 n) : term256 n.
Proof. exact (h1). Qed.
Lemma lem181102 (m : nat) (n : nat) (h1 : term256 n) : term266 m n.
Proof. exact (@lem181100 m n (@lem181101 n h1)). Qed.
Lemma lem181103 (m : nat) (n : nat) (h1 : term256 n) : term267 m n.
Proof. exact (proj2 (@lem181102 m n h1)). Qed.
Lemma lem181104 (m : nat) (n : nat) : (term267 m n) = ((term267 m n) = True).
Proof. exact (@lem7 (term267 m n)). Qed.
Lemma lem181105 (m : nat) (n : nat) (h1 : term256 n) : (term267 m n) = True.
Proof. exact (EQ_MP (@lem181104 m n) (@lem181103 m n h1)). Qed.
Lemma lem181122 (m : nat) : term291 m.
Proof. exact (@lem100973 m). Qed.
Lemma lem181123 (m : nat) : (term291 m) = (term292 m).
Proof. exact (eq_refl (term291 m)). Qed.
Lemma lem181124 (m : nat) : term292 m.
Proof. exact (EQ_MP (@lem181123 m) (@lem181122 m)). Qed.
Lemma lem181125 (m : nat) (n : nat) : term293 m n.
Proof. exact (@lem181124 m n). Qed.
Lemma lem181126 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (eq_refl (term293 m n)). Qed.
Lemma lem181127 (m : nat) (n : nat) : term294 m n.
Proof. exact (EQ_MP (@lem181126 m n) (@lem181125 m n)). Qed.
Lemma lem181128 (m : nat) (n : nat) (p : nat) : term295 m n p.
Proof. exact (@lem181127 m n p). Qed.
Lemma lem181129 (p : nat) (m : nat) (n : nat) : (term295 m n p) = ((term296 m n p) = (Peano.le m n)).
Proof. exact (eq_refl (term295 m n p)). Qed.
Lemma lem181131 (n : nat) : term297 n.
Proof. exact (@lem84996 n). Qed.
Lemma lem181132 (n : nat) : (term297 n) = ((term0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term297 n)). Qed.
Lemma lem181134 (m : nat) : (term231 m) = ((term231 m) = True).
Proof. exact (@lem7 (term231 m)). Qed.
Lemma lem181296 (n : nat) : (term0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem181132 n) (@lem181131 n)). Qed.
Lemma lem181297 (n : nat) (m : nat) : (term250 n m) = (term298 n m).
Proof. exact (@lem181296 (Nat.modulo n m)). Qed.
Lemma lem181324 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem181325 (n : nat) (m : nat) : (term299 n m) = (term300 n m).
Proof. exact (MK_COMB (@lem181324) (@lem181297 n m)). Qed.
Lemma lem181374 (n : nat) (m : nat) : (term301 n m) = (term301 n m).
Proof. exact (eq_refl (term301 n m)). Qed.
Lemma lem181375 (n : nat) (m : nat) : (term302 n m) = (term303 n m).
Proof. exact (MK_COMB (@lem181325 n m) (@lem181374 n m)). Qed.
Lemma lem181377 (p : nat) (m : nat) (n : nat) : (term296 m n p) = (Peano.le m n).
Proof. exact (EQ_MP (@lem181129 p m n) (@lem181128 m n p)). Qed.
Lemma lem181378 (n : nat) (m : nat) : (term303 n m) = (term282 n m).
Proof. exact (@lem181377 (Nat.modulo n m) (Nat.modulo n m) m). Qed.
Lemma lem181380 (m : nat) (n : nat) : term278 m n.
Proof. exact (fun h0 : Peano.lt m n => @lem181089 m n h0). Qed.
Lemma lem181381 (n : nat) (m : nat) : term279 n m.
Proof. exact (@lem181380 (Nat.modulo n m) m). Qed.
Lemma lem181383 (m : nat) (n : nat) : term280 m n.
Proof. exact (fun h0 : term256 n => @lem181105 m n h0). Qed.
Lemma lem181384 (n : nat) (m : nat) : term280 n m.
Proof. exact (@lem181383 n m). Qed.
Lemma lem181422 (n : nat) : term281 n.
Proof. exact (fun h0 : term231 n => @lem181032 n h0). Qed.
Lemma lem181423 (m : nat) : term281 m.
Proof. exact (@lem181422 m). Qed.
Lemma lem181425 (m : nat) (h1 : term231 m) : (term231 m) = True.
Proof. exact (EQ_MP (@lem181134 m) (@lem180928 m h1)). Qed.
Lemma lem181428 (m : nat) (h1 : term231 m) : True = (term231 m).
Proof. exact (SYM (@lem181425 m h1)). Qed.
Lemma lem181429 (m : nat) (h1 : term231 m) : term231 m.
Proof. exact (EQ_MP (@lem181428 m h1) (@lem0)). Qed.
Lemma lem181430 (m : nat) (h1 : term231 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem181423 m (@lem181429 m h1)). Qed.
Lemma lem181433 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem181434 (m : nat) (h1 : term231 m) : (term256 m) = (~ False).
Proof. exact (MK_COMB (@lem181433) (@lem181430 m h1)). Qed.
Lemma lem181436 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem181439 (m : nat) (h1 : term231 m) : (term256 m) = True.
Proof. exact (TRANS (@lem181434 m h1) (@lem181436)). Qed.
Lemma lem181440 (m : nat) (h1 : term231 m) : True = (term256 m).
Proof. exact (SYM (@lem181439 m h1)). Qed.
Lemma lem181441 (m : nat) (h1 : term231 m) : term256 m.
Proof. exact (EQ_MP (@lem181440 m h1) (@lem0)). Qed.
Lemma lem181442 (n : nat) (m : nat) (h1 : term231 m) : (term267 n m) = True.
Proof. exact (@lem181384 n m (@lem181441 m h1)). Qed.
Lemma lem181445 (n : nat) (m : nat) (h1 : term231 m) : True = (term267 n m).
Proof. exact (SYM (@lem181442 n m h1)). Qed.
Lemma lem181446 (n : nat) (m : nat) (h1 : term231 m) : term267 n m.
Proof. exact (EQ_MP (@lem181445 n m h1) (@lem0)). Qed.
Lemma lem181447 (n : nat) (m : nat) (h1 : term231 m) : (term282 n m) = True.
Proof. exact (@lem181381 n m (@lem181446 n m h1)). Qed.
Lemma lem181450 (n : nat) (m : nat) (h1 : term231 m) : (term303 n m) = True.
Proof. exact (TRANS (@lem181378 n m) (@lem181447 n m h1)). Qed.
Lemma lem181451 (n : nat) (m : nat) (h1 : term231 m) : (term302 n m) = True.
Proof. exact (TRANS (@lem181375 n m) (@lem181450 n m h1)). Qed.
Lemma lem181452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem181453 (n : nat) (m : nat) (h1 : term231 m) : (term304 n m) = (and True).
Proof. exact (MK_COMB (@lem181452) (@lem181451 n m h1)). Qed.
Lemma lem181517 (m : nat) (n : nat) : (term305 m n) = (term305 m n).
Proof. exact (eq_refl (term305 m n)). Qed.
Lemma lem181518 (n : nat) (m : nat) (h1 : term231 m) : (term306 m n) = (term307 m n).
Proof. exact (MK_COMB (@lem181453 n m h1) (@lem181517 m n)). Qed.
Lemma lem181520 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem181521 (m : nat) (n : nat) : (term307 m n) = (term305 m n).
Proof. exact (@lem181520 (term305 m n)). Qed.
Lemma lem181579 (n : nat) (m : nat) (h1 : term231 m) : (term306 m n) = (term305 m n).
Proof. exact (TRANS (@lem181518 n m h1) (@lem181521 m n)). Qed.
Lemma lem181580 (n : nat) (m : nat) (h1 : term231 m) : (term305 m n) = (term306 m n).
Proof. exact (SYM (@lem181579 n m h1)). Qed.
Lemma lem181582 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem179954 n m) (@lem179953 m n)). Qed.
Lemma lem181583 (n : nat) (m : nat) : (term301 n m) = (term308 n m).
Proof. exact (@lem181582 (Nat.modulo n m) m). Qed.
Lemma lem181584 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem181585 (n : nat) (m : nat) : (term309 n m) = (term310 n m).
Proof. exact (MK_COMB (@lem181584) (@lem181583 n m)). Qed.
Lemma lem181586 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem181587 (m : nat) (n : nat) : (term305 m n) = (term311 m n).
Proof. exact (MK_COMB (@lem181585 n m) (@lem181586 n)). Qed.
Lemma lem181588 (m : nat) (n : nat) : (term311 m n) = (term305 m n).
Proof. exact (SYM (@lem181587 m n)). Qed.
Lemma lem181590 (m : nat) : term312 m.
Proof. exact (@lem136494 m). Qed.
Lemma lem181591 (m : nat) : (term312 m) = (term313 m).
Proof. exact (eq_refl (term312 m)). Qed.
Lemma lem181592 (m : nat) : term313 m.
Proof. exact (EQ_MP (@lem181591 m) (@lem181590 m)). Qed.
Lemma lem181593 (m : nat) (n : nat) : term314 m n.
Proof. exact (@lem181592 m n). Qed.
Lemma lem181594 (n : nat) (m : nat) : (term314 m n) = (term315 n m).
Proof. exact (eq_refl (term314 m n)). Qed.
Lemma lem181595 (n : nat) (m : nat) : term315 n m.
Proof. exact (EQ_MP (@lem181594 n m) (@lem181593 m n)). Qed.
Lemma lem181596 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem181597 (n : nat) (m : nat) (h1 : Peano.le n m) : (term316 m n) = m.
Proof. exact (@lem181595 n m (@lem181596 n m h1)). Qed.
Lemma lem181603 (n : nat) : term317 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem181604 (n : nat) : (term317 n) = (Peano.le n n).
Proof. exact (eq_refl (term317 n)). Qed.
Lemma lem181605 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem181604 n) (@lem181603 n)). Qed.
Lemma lem181606 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem181610 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem181617 (n : nat) (m : nat) (h1 : (Nat.modulo n m) = (Nat.sub n m)) : (Nat.modulo n m) = (Nat.sub n m).
Proof. exact (h1). Qed.
Lemma lem181618 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem181619 (n : nat) (m : nat) (h1 : (Nat.modulo n m) = (Nat.sub n m)) : (term318 n m) = (term319 n m).
Proof. exact (MK_COMB (@lem181618) (@lem181617 n m h1)). Qed.
Lemma lem181620 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem181621 (n : nat) (m : nat) (h1 : (Nat.modulo n m) = (Nat.sub n m)) : (term308 n m) = (term316 n m).
Proof. exact (MK_COMB (@lem181619 n m h1) (@lem181620 m)). Qed.
Lemma lem181623 (n : nat) (m : nat) : term315 n m.
Proof. exact (fun h0 : Peano.le n m => @lem181597 n m h0). Qed.
Lemma lem181624 (m : nat) (n : nat) : term315 m n.
Proof. exact (@lem181623 m n). Qed.
Lemma lem181626 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem181610 m n) (@lem180930 m n h1)). Qed.
Lemma lem181627 (m : nat) (n : nat) (h1 : Peano.le m n) : True = (Peano.le m n).
Proof. exact (SYM (@lem181626 m n h1)). Qed.
Lemma lem181628 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem181627 m n h1) (@lem0)). Qed.
Lemma lem181629 (m : nat) (n : nat) (h1 : Peano.le m n) : (term316 n m) = n.
Proof. exact (@lem181624 m n (@lem181628 m n h1)). Qed.
Lemma lem181630 (n : nat) (m : nat) (h1 : Peano.le m n) (h2 : (Nat.modulo n m) = (Nat.sub n m)) : (term308 n m) = n.
Proof. exact (TRANS (@lem181621 n m h2) (@lem181629 m n h1)). Qed.
Lemma lem181631 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem181632 (n : nat) (m : nat) (h1 : Peano.le m n) (h2 : (Nat.modulo n m) = (Nat.sub n m)) : (term310 n m) = (Peano.le n).
Proof. exact (MK_COMB (@lem181631) (@lem181630 n m h1 h2)). Qed.
Lemma lem181633 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem181634 (n : nat) (m : nat) (h1 : Peano.le m n) (h2 : (Nat.modulo n m) = (Nat.sub n m)) : (term311 m n) = (Peano.le n n).
Proof. exact (MK_COMB (@lem181632 n m h1 h2) (@lem181633 n)). Qed.
Lemma lem181636 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem181606 n) (@lem181605 n)). Qed.
Lemma lem181637 (n : nat) (m : nat) (h1 : Peano.le m n) (h2 : (Nat.modulo n m) = (Nat.sub n m)) : (term311 m n) = True.
Proof. exact (TRANS (@lem181634 n m h1 h2) (@lem181636 n)). Qed.
Lemma lem181638 (n : nat) (m : nat) (h1 : Peano.le m n) (h2 : (Nat.modulo n m) = (Nat.sub n m)) : True = (term311 m n).
Proof. exact (SYM (@lem181637 n m h1 h2)). Qed.
Lemma lem181639 (n : nat) (m : nat) (h1 : Peano.le m n) (h2 : (Nat.modulo n m) = (Nat.sub n m)) : term311 m n.
Proof. exact (EQ_MP (@lem181638 n m h1 h2) (@lem0)). Qed.
Lemma lem181641 (m : nat) (n : nat) (r : nat) : term214 m n r.
Proof. exact (EQ_MP (@lem179948 m n r) (@lem179947 m n r)). Qed.
Lemma lem181642 (n : nat) (m : nat) : term320 n m.
Proof. exact (@lem181641 n m (Nat.sub n m)). Qed.
Lemma lem181648 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem179913 n m) (@lem179912 m n)). Qed.
Lemma lem181649 (n : nat) (m : nat) : (term321 n m) = (term322 n m).
Proof. exact (@lem181648 (Nat.sub n m) (term323 m)). Qed.
Lemma lem181650 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem181651 (n : nat) (m : nat) : (n = (term321 n m)) = (n = (term322 n m)).
Proof. exact (MK_COMB (@lem181650 n) (@lem181649 n m)). Qed.
Lemma lem181652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem181653 (n : nat) (m : nat) : (term324 n m) = (term325 n m).
Proof. exact (MK_COMB (@lem181652) (@lem181651 n m)). Qed.
Lemma lem181654 (n : nat) (m : nat) : (term6 n m) = (term6 n m).
Proof. exact (eq_refl (term6 n m)). Qed.
Lemma lem181655 (n : nat) (m : nat) : (term326 n m) = (term327 n m).
Proof. exact (MK_COMB (@lem181653 n m) (@lem181654 n m)). Qed.
Lemma lem181656 (n : nat) (m : nat) : (term327 n m) = (term326 n m).
Proof. exact (SYM (@lem181655 n m)). Qed.
Lemma lem181657 (m : nat) : term312 m.
Proof. exact (@lem136494 m). Qed.
Lemma lem181658 (m : nat) : (term312 m) = (term313 m).
Proof. exact (eq_refl (term312 m)). Qed.
Lemma lem181659 (m : nat) : term313 m.
Proof. exact (EQ_MP (@lem181658 m) (@lem181657 m)). Qed.
Lemma lem181660 (m : nat) (n : nat) : term314 m n.
Proof. exact (@lem181659 m n). Qed.
Lemma lem181661 (n : nat) (m : nat) : (term314 m n) = (term315 n m).
Proof. exact (eq_refl (term314 m n)). Qed.
Lemma lem181662 (n : nat) (m : nat) : term315 n m.
Proof. exact (EQ_MP (@lem181661 n m) (@lem181660 m n)). Qed.
Lemma lem181663 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem181664 (n : nat) (m : nat) (h1 : Peano.le n m) : (term316 m n) = m.
Proof. exact (@lem181662 n m (@lem181663 n m h1)). Qed.
Lemma lem181670 : term328.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem181671 : term329.
Proof. exact (proj2 (@lem181670)). Qed.
Lemma lem181692 : term330.
Proof. exact (proj1 (@lem181671)). Qed.
Lemma lem181693 (n : nat) : term331 n.
Proof. exact (@lem181692 n). Qed.
Lemma lem181694 (n : nat) : (term331 n) = ((term323 n) = n).
Proof. exact (eq_refl (term331 n)). Qed.
Lemma lem181706 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem181717 (n : nat) : (term323 n) = n.
Proof. exact (EQ_MP (@lem181694 n) (@lem181693 n)). Qed.
Lemma lem181718 (m : nat) : (term323 m) = m.
Proof. exact (@lem181717 m). Qed.
Lemma lem181719 (n : nat) (m : nat) : (term319 n m) = (term319 n m).
Proof. exact (eq_refl (term319 n m)). Qed.
Lemma lem181720 (n : nat) (m : nat) : (term322 n m) = (term316 n m).
Proof. exact (MK_COMB (@lem181719 n m) (@lem181718 m)). Qed.
Lemma lem181722 (n : nat) (m : nat) : term315 n m.
Proof. exact (fun h0 : Peano.le n m => @lem181664 n m h0). Qed.
Lemma lem181723 (m : nat) (n : nat) : term315 m n.
Proof. exact (@lem181722 m n). Qed.
Lemma lem181725 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem181706 m n) (@lem180930 m n h1)). Qed.
Lemma lem181726 (m : nat) (n : nat) (h1 : Peano.le m n) : True = (Peano.le m n).
Proof. exact (SYM (@lem181725 m n h1)). Qed.
Lemma lem181727 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem181726 m n h1) (@lem0)). Qed.
Lemma lem181728 (m : nat) (n : nat) (h1 : Peano.le m n) : (term316 n m) = n.
Proof. exact (@lem181723 m n (@lem181727 m n h1)). Qed.
Lemma lem181729 (m : nat) (n : nat) (h1 : Peano.le m n) : (term322 n m) = n.
Proof. exact (TRANS (@lem181720 n m) (@lem181728 m n h1)). Qed.
Lemma lem181730 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem181731 (m : nat) (n : nat) (h1 : Peano.le m n) : (n = (term322 n m)) = (n = n).
Proof. exact (MK_COMB (@lem181730 n) (@lem181729 m n h1)). Qed.
Lemma lem181733 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem181734 (x : nat) : (x = x) = True.
Proof. exact (@lem181733 nat x). Qed.
Lemma lem181735 (n : nat) : (n = n) = True.
Proof. exact (@lem181734 n). Qed.
Lemma lem181736 (m : nat) (n : nat) (h1 : Peano.le m n) : (n = (term322 n m)) = True.
Proof. exact (TRANS (@lem181731 m n h1) (@lem181735 n)). Qed.
Lemma lem181737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem181738 (m : nat) (n : nat) (h1 : Peano.le m n) : (term325 n m) = (and True).
Proof. exact (MK_COMB (@lem181737) (@lem181736 m n h1)). Qed.
Lemma lem181739 (n : nat) (m : nat) : (term6 n m) = (term6 n m).
Proof. exact (eq_refl (term6 n m)). Qed.
Lemma lem181740 (m : nat) (n : nat) (h1 : Peano.le m n) : (term327 n m) = (term332 n m).
Proof. exact (MK_COMB (@lem181738 m n h1) (@lem181739 n m)). Qed.
Lemma lem181742 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem181743 (n : nat) (m : nat) : (term332 n m) = (term6 n m).
Proof. exact (@lem181742 (term6 n m)). Qed.
Lemma lem181744 (m : nat) (n : nat) (h1 : Peano.le m n) : (term327 n m) = (term6 n m).
Proof. exact (TRANS (@lem181740 m n h1) (@lem181743 n m)). Qed.
Lemma lem181745 (m : nat) (n : nat) (h1 : Peano.le m n) : (term6 n m) = (term327 n m).
Proof. exact (SYM (@lem181744 m n h1)). Qed.
Lemma lem181747 (n : nat) (m : nat) : (term6 n m) = (term7 n m).
Proof. exact (EQ_MP (@lem178744 n m) (@lem179907 n m)). Qed.
Lemma lem181748 (n : nat) (m : nat) : (term7 n m) = (term6 n m).
Proof. exact (SYM (@lem181747 n m)). Qed.
Lemma lem181749 (m : nat) : term312 m.
Proof. exact (@lem136494 m). Qed.
Lemma lem181750 (m : nat) : (term312 m) = (term313 m).
Proof. exact (eq_refl (term312 m)). Qed.
Lemma lem181751 (m : nat) : term313 m.
Proof. exact (EQ_MP (@lem181750 m) (@lem181749 m)). Qed.
Lemma lem181752 (m : nat) (n : nat) : term314 m n.
Proof. exact (@lem181751 m n). Qed.
Lemma lem181753 (n : nat) (m : nat) : (term314 m n) = (term315 n m).
Proof. exact (eq_refl (term314 m n)). Qed.
Lemma lem181754 (n : nat) (m : nat) : term315 n m.
Proof. exact (EQ_MP (@lem181753 n m) (@lem181752 m n)). Qed.
Lemma lem181755 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem181756 (n : nat) (m : nat) (h1 : Peano.le n m) : (term316 m n) = m.
Proof. exact (@lem181754 n m (@lem181755 n m h1)). Qed.
Lemma lem181762 (n : nat) : term333 n.
Proof. exact (@lem178730 n). Qed.
Lemma lem181763 (n : nat) : (term333 n) = ((Nat.add n n) = (term0 n)).
Proof. exact (eq_refl (term333 n)). Qed.
Lemma lem181767 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem181769 (n : nat) (m : nat) : (term290 n m) = ((term290 n m) = True).
Proof. exact (@lem7 (term290 n m)). Qed.
Lemma lem181772 (n : nat) (m : nat) : term315 n m.
Proof. exact (fun h0 : Peano.le n m => @lem181756 n m h0). Qed.
Lemma lem181773 (m : nat) (n : nat) : term315 m n.
Proof. exact (@lem181772 m n). Qed.
Lemma lem181775 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem181767 m n) (@lem180930 m n h1)). Qed.
Lemma lem181776 (m : nat) (n : nat) (h1 : Peano.le m n) : True = (Peano.le m n).
Proof. exact (SYM (@lem181775 m n h1)). Qed.
Lemma lem181777 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem181776 m n h1) (@lem0)). Qed.
Lemma lem181778 (m : nat) (n : nat) (h1 : Peano.le m n) : (term316 n m) = n.
Proof. exact (@lem181773 m n (@lem181777 m n h1)). Qed.
Lemma lem181779 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem181780 (m : nat) (n : nat) (h1 : Peano.le m n) : (term334 n m) = (Peano.lt n).
Proof. exact (MK_COMB (@lem181779) (@lem181778 m n h1)). Qed.
Lemma lem181782 (n : nat) : (Nat.add n n) = (term0 n).
Proof. exact (EQ_MP (@lem181763 n) (@lem181762 n)). Qed.
Lemma lem181783 (m : nat) : (Nat.add m m) = (term0 m).
Proof. exact (@lem181782 m). Qed.
Lemma lem181784 (m : nat) (n : nat) (h1 : Peano.le m n) : (term7 n m) = (term290 n m).
Proof. exact (MK_COMB (@lem181780 m n h1) (@lem181783 m)). Qed.
Lemma lem181786 (m : nat) (n : nat) (h1 : term229 m n) : (term290 n m) = True.
Proof. exact (EQ_MP (@lem181769 n m) (@lem180934 m n h1)). Qed.
Lemma lem181787 (m : nat) (n : nat) (h1 : term229 m n) (h2 : Peano.le m n) : (term7 n m) = True.
Proof. exact (TRANS (@lem181784 m n h2) (@lem181786 m n h1)). Qed.
Lemma lem181788 (m : nat) (n : nat) (h1 : term229 m n) (h2 : Peano.le m n) : True = (term7 n m).
Proof. exact (SYM (@lem181787 m n h1 h2)). Qed.
Lemma lem181789 (m : nat) (n : nat) (h1 : term229 m n) (h2 : Peano.le m n) : term7 n m.
Proof. exact (EQ_MP (@lem181788 m n h1 h2) (@lem0)). Qed.
Lemma lem181790 (m : nat) (n : nat) (h1 : term229 m n) (h2 : Peano.le m n) : term6 n m.
Proof. exact (EQ_MP (@lem181748 n m) (@lem181789 m n h1 h2)). Qed.
Lemma lem181791 (m : nat) (n : nat) (h1 : term229 m n) (h2 : Peano.le m n) : term327 n m.
Proof. exact (EQ_MP (@lem181745 m n h2) (@lem181790 m n h1 h2)). Qed.
Lemma lem181792 (m : nat) (n : nat) (h1 : term229 m n) (h2 : Peano.le m n) : term326 n m.
Proof. exact (EQ_MP (@lem181656 n m) (@lem181791 m n h1 h2)). Qed.
Lemma lem181793 (m : nat) (n : nat) (h1 : term229 m n) (h2 : Peano.le m n) : term335 n m.
Proof. exact (ex_intro (term336 n m) term337 (@lem181792 m n h1 h2)). Qed.
Lemma lem181794 (m : nat) (n : nat) (h1 : term229 m n) (h2 : Peano.le m n) : (Nat.modulo n m) = (Nat.sub n m).
Proof. exact (@lem181642 n m (@lem181793 m n h1 h2)). Qed.
Lemma lem181795 (m : nat) (n : nat) (h1 : term229 m n) (h2 : Peano.le m n) : ((Nat.modulo n m) = (Nat.sub n m)) = (term311 m n).
Proof. exact (prop_ext (fun h3 : (Nat.modulo n m) = (Nat.sub n m) => @lem181639 n m h2 h3) (fun h3 : term311 m n => @lem181794 m n h1 h2)). Qed.
Lemma lem181796 (m : nat) (n : nat) (h1 : term229 m n) (h2 : Peano.le m n) : term311 m n.
Proof. exact (EQ_MP (@lem181795 m n h1 h2) (@lem181794 m n h1 h2)). Qed.
Lemma lem181797 (m : nat) (n : nat) (h1 : term229 m n) (h2 : Peano.le m n) : term305 m n.
Proof. exact (EQ_MP (@lem181588 m n) (@lem181796 m n h1 h2)). Qed.
Lemma lem181798 (m : nat) (n : nat) (h1 : term229 m n) (h2 : term231 m) (h3 : Peano.le m n) : term306 m n.
Proof. exact (EQ_MP (@lem181580 n m h2) (@lem181797 m n h1 h3)). Qed.
Lemma lem181799 (m : nat) (n : nat) (h1 : term229 m n) (h2 : term231 m) (h3 : Peano.le m n) : term287 m n.
Proof. exact (ex_intro (term288 m n) (term301 n m) (@lem181798 m n h1 h2 h3)). Qed.
Lemma lem181800 (m : nat) (n : nat) (h1 : term229 m n) (h2 : term231 m) (h3 : Peano.le m n) : term289 m n.
Proof. exact (@lem180965 m n (@lem181799 m n h1 h2 h3)). Qed.
Lemma lem181801 (m : nat) (n : nat) (h1 : term229 m n) (h2 : term231 m) (h3 : Peano.le m n) : (Peano.le m n) = (term289 m n).
Proof. exact (prop_ext (fun h4 : Peano.le m n => @lem181800 m n h1 h2 h3) (fun h4 : term289 m n => @lem180930 m n h3)). Qed.
Lemma lem181802 (m : nat) (n : nat) (h1 : term229 m n) (h2 : term231 m) (h3 : Peano.le m n) : term289 m n.
Proof. exact (EQ_MP (@lem181801 m n h1 h2 h3) (@lem180930 m n h3)). Qed.
Lemma lem181803 (m : nat) (n : nat) (h1 : term229 m n) (h2 : term231 m) (h3 : Peano.le m n) : (term231 m) = (term289 m n).
Proof. exact (prop_ext (fun h4 : term231 m => @lem181802 m n h1 h2 h3) (fun h4 : term289 m n => @lem180928 m h2)). Qed.
Lemma lem181804 (m : nat) (n : nat) (h1 : term229 m n) (h2 : term231 m) (h3 : Peano.le m n) : term289 m n.
Proof. exact (EQ_MP (@lem181803 m n h1 h2 h3) (@lem180928 m h2)). Qed.
Lemma lem181805 (m : nat) (n : nat) (h1 : term231 m) (h2 : Peano.le m n) : term289 m n.
Proof. exact (or_elim (@lem179964 m n) (fun h0 : term227 m n => @lem180926 m n h1 h0) (fun h0 : term229 m n => @lem181804 m n h0 h1 h2)). Qed.
Lemma lem181806 (m : nat) (n : nat) (h1 : term230 m n) : Peano.le m n.
Proof. exact (proj2 (@lem179967 m n h1)). Qed.
Lemma lem181807 (m : nat) (n : nat) (h1 : term230 m n) : term231 m.
Proof. exact (proj1 (@lem179967 m n h1)). Qed.
Lemma lem181808 (m : nat) (n : nat) (h1 : term231 m) (h2 : Peano.le m n) : (Peano.le m n) = (term289 m n).
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem181805 m n h1 h2) (fun h3 : term289 m n => @lem179968 m n h2)). Qed.
Lemma lem181809 (m : nat) (n : nat) (h1 : term231 m) (h2 : Peano.le m n) : term289 m n.
Proof. exact (EQ_MP (@lem181808 m n h1 h2) (@lem179968 m n h2)). Qed.
Lemma lem181810 (m : nat) (n : nat) (h1 : term231 m) (h2 : Peano.le m n) : (term231 m) = (term289 m n).
Proof. exact (prop_ext (fun h3 : term231 m => @lem181809 m n h1 h2) (fun h3 : term289 m n => @lem179969 m h1)). Qed.
Lemma lem181811 (m : nat) (n : nat) (h1 : term231 m) (h2 : Peano.le m n) : term289 m n.
Proof. exact (EQ_MP (@lem181810 m n h1 h2) (@lem179969 m h1)). Qed.
Lemma lem181812 (n : nat) (m : nat) (h1 : term230 m n) (h2 : term231 m) : (Peano.le m n) = (term289 m n).
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem181811 m n h2 h3) (fun h3 : term289 m n => @lem181806 m n h1)). Qed.
Lemma lem181813 (n : nat) (m : nat) (h1 : term230 m n) (h2 : term231 m) : term289 m n.
Proof. exact (EQ_MP (@lem181812 n m h1 h2) (@lem181806 m n h1)). Qed.
Lemma lem181814 (m : nat) (n : nat) (h1 : term230 m n) : (term231 m) = (term289 m n).
Proof. exact (prop_ext (fun h2 : term231 m => @lem181813 n m h1 h2) (fun h2 : term289 m n => @lem181807 m n h1)). Qed.
Lemma lem181815 (m : nat) (n : nat) (h1 : term230 m n) : term289 m n.
Proof. exact (EQ_MP (@lem181814 m n h1) (@lem181807 m n h1)). Qed.
Lemma lem181816 (m : nat) (n : nat) : term338 m n.
Proof. exact (fun h0 : term230 m n => @lem181815 m n h0). Qed.
Lemma lem181821 (m : nat) : term339 m.
Proof. exact (fun n : nat => @lem181816 m n). Qed.
Lemma lem181826 : term340.
Proof. exact (fun m : nat => @lem181821 m). Qed.
