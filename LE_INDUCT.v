Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_INDUCT_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import DISJ_ACI_spec.
Require Import LE_EXISTS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem117751 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem117752 (R : type1605) : ((term1 R) = (term2 R)) = (term3 R).
Proof. exact (@lem117751 ((term1 R) = (term2 R))). Qed.
Lemma lem117753 (R : type1605) : (term3 R) = ((term1 R) = (term2 R)).
Proof. exact (SYM (@lem117752 R)). Qed.
Lemma lem117754 (R : type1605) (h1 : term4 R) : term4 R.
Proof. exact (h1). Qed.
Lemma lem117757 (R : type1605) (h1 : term5 R) : term5 R.
Proof. exact (h1). Qed.
Lemma lem117758 (R : type1605) : term6 R.
Proof. exact (fun h0 : term5 R => @lem117757 R h0). Qed.
Lemma lem117759 (R : type1605) (h1 : term6 R) : term6 R.
Proof. exact (h1). Qed.
Lemma lem117760 (R : type1605) (h1 : term5 R) : term5 R.
Proof. exact (h1). Qed.
Lemma lem117761 (R : type1605) (h1 : term5 R) (h2 : term6 R) : term5 R.
Proof. exact (@lem117759 R h2 (@lem117760 R h1)). Qed.
Lemma lem117762 (R : type1605) (h1 : term5 R) : term7 R.
Proof. exact (fun h0 : term6 R => @lem117761 R h1 h0). Qed.
Lemma lem117763 (R : type1605) (h1 : term6 R) : term6 R.
Proof. exact (h1). Qed.
Lemma lem117764 (R : type1605) (h1 : term5 R) (h2 : term6 R) : term5 R.
Proof. exact (@lem117762 R h1 (@lem117763 R h2)). Qed.
Lemma lem117765 (R : type1605) (h1 : term6 R) : term6 R.
Proof. exact (fun h0 : term5 R => @lem117764 R h0 h1). Qed.
Lemma lem117766 (R : type1605) : term8 R.
Proof. exact (fun h0 : term6 R => @lem117765 R h0). Qed.
Lemma lem117769 (R : type1605) : term6 R.
Proof. exact (@lem117766 R (@lem117758 R)). Qed.
Lemma lem117795 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem117796 : term9 = term10.
Proof. exact (@lem117795 term11). Qed.
Lemma lem117809 (R : type1605) : (term12 R) = (term12 R).
Proof. exact (eq_refl (term12 R)). Qed.
Lemma lem117810 (R : type1605) : (term5 R) = (term13 R).
Proof. exact (MK_COMB (@lem117809 R) (@lem117796)). Qed.
Lemma lem117813 : term14 = term15.
Proof. exact (fun_ext (fun R : type1605 => @lem117810 R)). Qed.
Lemma lem117814 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem117823 : term16 = term17.
Proof. exact (MK_COMB (@lem117814) (@lem117813)). Qed.
Lemma lem117824 (n : nat) (m : nat) (d : nat) : (n = (Nat.add m d)) = (n = (Nat.add m d)).
Proof. exact (eq_refl (n = (Nat.add m d))). Qed.
Lemma lem117825 (n : nat) (m : nat) : (term18 n m) = (term18 n m).
Proof. exact (fun_ext (fun d : nat => @lem117824 n m d)). Qed.
Lemma lem117826 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem117827 (n : nat) (m : nat) : (term19 n m) = (term19 n m).
Proof. exact (MK_COMB (@lem117826) (@lem117825 n m)). Qed.
Lemma lem117830 (m : nat) (n : nat) : (term20 m n) = (term20 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem117831 (n : nat) (m : nat) : ((Peano.le m n) = (term19 n m)) = ((Peano.le m n) = (term19 n m)).
Proof. exact (MK_COMB (@lem117830 m n) (@lem117827 n m)). Qed.
Lemma lem117832 (m : nat) : (term21 m) = (term21 m).
Proof. exact (fun_ext (fun n : nat => @lem117831 n m)). Qed.
Lemma lem117833 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117834 (m : nat) : (term22 m) = (term22 m).
Proof. exact (MK_COMB (@lem117833) (@lem117832 m)). Qed.
Lemma lem117835 : term23 = term23.
Proof. exact (fun_ext (fun m : nat => @lem117834 m)). Qed.
Lemma lem117836 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117837 : term11 = term11.
Proof. exact (MK_COMB (@lem117836) (@lem117835)). Qed.
Lemma lem117838 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem117839 : term10 = term10.
Proof. exact (MK_COMB (@lem117838) (@lem117837)). Qed.
Lemma lem117840 (R : type1605) (m : nat) (d : nat) : (term24 R m d) = (term24 R m d).
Proof. exact (eq_refl (term24 R m d)). Qed.
Lemma lem117841 (R : type1605) (m : nat) : (term25 R m) = (term25 R m).
Proof. exact (fun_ext (fun d : nat => @lem117840 R m d)). Qed.
Lemma lem117842 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117843 (R : type1605) (m : nat) : (term26 R m) = (term26 R m).
Proof. exact (MK_COMB (@lem117842) (@lem117841 R m)). Qed.
Lemma lem117844 (R : type1605) : (term27 R) = (term27 R).
Proof. exact (fun_ext (fun m : nat => @lem117843 R m)). Qed.
Lemma lem117845 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117846 (R : type1605) : (term2 R) = (term2 R).
Proof. exact (MK_COMB (@lem117845) (@lem117844 R)). Qed.
Lemma lem117851 (R : type1605) (m : nat) (n : nat) : (term28 R m n) = (term28 R m n).
Proof. exact (eq_refl (term28 R m n)). Qed.
Lemma lem117852 (R : type1605) (m : nat) : (term29 R m) = (term29 R m).
Proof. exact (fun_ext (fun n : nat => @lem117851 R m n)). Qed.
Lemma lem117853 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117854 (R : type1605) (m : nat) : (term30 R m) = (term30 R m).
Proof. exact (MK_COMB (@lem117853) (@lem117852 R m)). Qed.
Lemma lem117855 (R : type1605) : (term31 R) = (term31 R).
Proof. exact (fun_ext (fun m : nat => @lem117854 R m)). Qed.
Lemma lem117856 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117857 (R : type1605) : (term1 R) = (term1 R).
Proof. exact (MK_COMB (@lem117856) (@lem117855 R)). Qed.
Lemma lem117858 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem117859 (R : type1605) : (term32 R) = (term32 R).
Proof. exact (MK_COMB (@lem117858) (@lem117857 R)). Qed.
Lemma lem117860 (R : type1605) : ((term1 R) = (term2 R)) = ((term1 R) = (term2 R)).
Proof. exact (MK_COMB (@lem117859 R) (@lem117846 R)). Qed.
Lemma lem117861 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem117862 (R : type1605) : (term4 R) = (term4 R).
Proof. exact (MK_COMB (@lem117861) (@lem117860 R)). Qed.
Lemma lem117863 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117864 (R : type1605) : (term12 R) = (term12 R).
Proof. exact (MK_COMB (@lem117863) (@lem117862 R)). Qed.
Lemma lem117865 (R : type1605) : (term13 R) = (term13 R).
Proof. exact (MK_COMB (@lem117864 R) (@lem117839)). Qed.
Lemma lem117866 : term15 = term15.
Proof. exact (fun_ext (fun R : type1605 => @lem117865 R)). Qed.
Lemma lem117867 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem117868 : term17 = term17.
Proof. exact (MK_COMB (@lem117867) (@lem117866)). Qed.
Lemma lem117923 : term16 = term17.
Proof. exact (TRANS (@lem117823) (@lem117868)). Qed.
Lemma lem117924 : term17 = term16.
Proof. exact (SYM (@lem117923)). Qed.
Lemma lem117925 (R : type1605) (h1 : term4 R) : term4 R.
Proof. exact (h1). Qed.
Lemma lem117926 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem117935 (R : type1605) (m : nat) (n : nat) : (term33 R m n) = (term34 R m n).
Proof. exact (@lem17362 (Peano.le m n) (R m n)). Qed.
Lemma lem117940 (R : type1605) (m : nat) (n : nat) : (term28 R m n) = (term35 R m n).
Proof. exact (@lem17265 (Peano.le m n) (R m n)). Qed.
Lemma lem117941 (P : nat -> Prop) : (term36 P) = (term37 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem117942 (R : type1605) (m : nat) : (term38 R m) = (term39 R m).
Proof. exact (@lem117941 (term29 R m)). Qed.
Lemma lem117943 (R : type1605) (m : nat) (n : nat) : (term40 R m n) = (term28 R m n).
Proof. exact (eq_refl (term40 R m n)). Qed.
Lemma lem117944 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem117945 (R : type1605) (m : nat) (n : nat) : (term41 R m n) = (term33 R m n).
Proof. exact (MK_COMB (@lem117944) (@lem117943 R m n)). Qed.
Lemma lem117946 (R : type1605) (m : nat) (n : nat) : (term41 R m n) = (term34 R m n).
Proof. exact (TRANS (@lem117945 R m n) (@lem117935 R m n)). Qed.
Lemma lem117947 (R : type1605) (m : nat) : (term42 R m) = (term43 R m).
Proof. exact (fun_ext (fun n : nat => @lem117946 R m n)). Qed.
Lemma lem117948 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem117949 (R : type1605) (m : nat) : (term39 R m) = (term44 R m).
Proof. exact (MK_COMB (@lem117948) (@lem117947 R m)). Qed.
Lemma lem117950 (R : type1605) (m : nat) : (term38 R m) = (term44 R m).
Proof. exact (TRANS (@lem117942 R m) (@lem117949 R m)). Qed.
Lemma lem117951 (R : type1605) (m : nat) : (term29 R m) = (term45 R m).
Proof. exact (fun_ext (fun n : nat => @lem117940 R m n)). Qed.
Lemma lem117952 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117953 (R : type1605) (m : nat) : (term30 R m) = (term46 R m).
Proof. exact (MK_COMB (@lem117952) (@lem117951 R m)). Qed.
Lemma lem117954 (P : nat -> Prop) : (term36 P) = (term37 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem117955 (R : type1605) : (term47 R) = (term48 R).
Proof. exact (@lem117954 (term31 R)). Qed.
Lemma lem117956 (R : type1605) (m : nat) : (term49 R m) = (term30 R m).
Proof. exact (eq_refl (term49 R m)). Qed.
Lemma lem117957 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem117958 (R : type1605) (m : nat) : (term50 R m) = (term38 R m).
Proof. exact (MK_COMB (@lem117957) (@lem117956 R m)). Qed.
Lemma lem117959 (R : type1605) (m : nat) : (term50 R m) = (term44 R m).
Proof. exact (TRANS (@lem117958 R m) (@lem117950 R m)). Qed.
Lemma lem117960 (R : type1605) : (term51 R) = (term52 R).
Proof. exact (fun_ext (fun m : nat => @lem117959 R m)). Qed.
Lemma lem117961 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem117962 (R : type1605) : (term48 R) = (term53 R).
Proof. exact (MK_COMB (@lem117961) (@lem117960 R)). Qed.
Lemma lem117963 (R : type1605) : (term47 R) = (term53 R).
Proof. exact (TRANS (@lem117955 R) (@lem117962 R)). Qed.
Lemma lem117964 (R : type1605) : (term31 R) = (term54 R).
Proof. exact (fun_ext (fun m : nat => @lem117953 R m)). Qed.
Lemma lem117965 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117966 (R : type1605) : (term1 R) = (term55 R).
Proof. exact (MK_COMB (@lem117965) (@lem117964 R)). Qed.
Lemma lem117968 (R : type1605) (m : nat) (d : nat) : (term24 R m d) = (term24 R m d).
Proof. exact (eq_refl (term24 R m d)). Qed.
Lemma lem117969 (P : nat -> Prop) : (term36 P) = (term37 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem117970 (R : type1605) (m : nat) : (term56 R m) = (term57 R m).
Proof. exact (@lem117969 (term25 R m)). Qed.
Lemma lem117971 (R : type1605) (m : nat) (d : nat) : (term58 R m d) = (term24 R m d).
Proof. exact (eq_refl (term58 R m d)). Qed.
Lemma lem117972 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem117974 (R : type1605) (m : nat) (d : nat) : (term59 R m d) = (term60 R m d).
Proof. exact (MK_COMB (@lem117972) (@lem117971 R m d)). Qed.
Lemma lem117975 (R : type1605) (m : nat) : (term61 R m) = (term62 R m).
Proof. exact (fun_ext (fun d : nat => @lem117974 R m d)). Qed.
Lemma lem117976 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem117977 (R : type1605) (m : nat) : (term57 R m) = (term63 R m).
Proof. exact (MK_COMB (@lem117976) (@lem117975 R m)). Qed.
Lemma lem117978 (R : type1605) (m : nat) : (term56 R m) = (term63 R m).
Proof. exact (TRANS (@lem117970 R m) (@lem117977 R m)). Qed.
Lemma lem117979 (R : type1605) (m : nat) : (term25 R m) = (term25 R m).
Proof. exact (fun_ext (fun d : nat => @lem117968 R m d)). Qed.
Lemma lem117980 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117981 (R : type1605) (m : nat) : (term26 R m) = (term26 R m).
Proof. exact (MK_COMB (@lem117980) (@lem117979 R m)). Qed.
Lemma lem117982 (P : nat -> Prop) : (term36 P) = (term37 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem117983 (R : type1605) : (term64 R) = (term65 R).
Proof. exact (@lem117982 (term27 R)). Qed.
Lemma lem117984 (R : type1605) (m : nat) : (term66 R m) = (term26 R m).
Proof. exact (eq_refl (term66 R m)). Qed.
Lemma lem117985 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem117986 (R : type1605) (m : nat) : (term67 R m) = (term56 R m).
Proof. exact (MK_COMB (@lem117985) (@lem117984 R m)). Qed.
Lemma lem117987 (R : type1605) (m : nat) : (term67 R m) = (term63 R m).
Proof. exact (TRANS (@lem117986 R m) (@lem117978 R m)). Qed.
Lemma lem117988 (R : type1605) : (term68 R) = (term69 R).
Proof. exact (fun_ext (fun m : nat => @lem117987 R m)). Qed.
Lemma lem117989 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem117990 (R : type1605) : (term65 R) = (term70 R).
Proof. exact (MK_COMB (@lem117989) (@lem117988 R)). Qed.
Lemma lem117991 (R : type1605) : (term64 R) = (term70 R).
Proof. exact (TRANS (@lem117983 R) (@lem117990 R)). Qed.
Lemma lem117992 (R : type1605) : (term27 R) = (term27 R).
Proof. exact (fun_ext (fun m : nat => @lem117981 R m)). Qed.
Lemma lem117993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117994 (R : type1605) : (term2 R) = (term2 R).
Proof. exact (MK_COMB (@lem117993) (@lem117992 R)). Qed.
Lemma lem117995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem117996 (R : type1605) : (term71 R) = (term72 R).
Proof. exact (MK_COMB (@lem117995) (@lem117963 R)). Qed.
Lemma lem117997 (R : type1605) : (term73 R) = (term74 R).
Proof. exact (MK_COMB (@lem117996 R) (@lem117994 R)). Qed.
Lemma lem117998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem117999 (R : type1605) : (term75 R) = (term76 R).
Proof. exact (MK_COMB (@lem117998) (@lem117966 R)). Qed.
Lemma lem118000 (R : type1605) : (term77 R) = (term78 R).
Proof. exact (MK_COMB (@lem117999 R) (@lem117991 R)). Qed.
Lemma lem118001 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem118002 (R : type1605) : (term79 R) = (term80 R).
Proof. exact (MK_COMB (@lem118001) (@lem118000 R)). Qed.
Lemma lem118003 (R : type1605) : (term81 R) = (term82 R).
Proof. exact (MK_COMB (@lem118002 R) (@lem117997 R)). Qed.
Lemma lem118004 (R : type1605) : (term4 R) = (term81 R).
Proof. exact (@lem17646 (term1 R) (term2 R)). Qed.
Lemma lem118005 (R : type1605) : (term4 R) = (term82 R).
Proof. exact (TRANS (@lem118004 R) (@lem118003 R)). Qed.
Lemma lem118128 {A : Type'} (P : Prop) (Q : A -> Prop) : (term83 A P Q) = (term84 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem118129 (P : Prop) (Q : nat -> Prop) : (term85 P Q) = (term86 P Q).
Proof. exact (@lem118128 nat P Q). Qed.
Lemma lem118130 (R : type1605) : (term87 R) = (term88 R).
Proof. exact (@lem118129 (term55 R) (term69 R)). Qed.
Lemma lem118131 (R : type1605) (m : nat) : (term89 R m) = (term63 R m).
Proof. exact (eq_refl (term89 R m)). Qed.
Lemma lem118132 (R : type1605) : (term90 R) = (term69 R).
Proof. exact (fun_ext (fun m : nat => @lem118131 R m)). Qed.
Lemma lem118133 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118134 (R : type1605) : (term91 R) = (term70 R).
Proof. exact (MK_COMB (@lem118133) (@lem118132 R)). Qed.
Lemma lem118135 (R : type1605) : (term76 R) = (term76 R).
Proof. exact (eq_refl (term76 R)). Qed.
Lemma lem118136 (R : type1605) : (term87 R) = (term78 R).
Proof. exact (MK_COMB (@lem118135 R) (@lem118134 R)). Qed.
Lemma lem118137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem118138 (R : type1605) : (term92 R) = (term93 R).
Proof. exact (MK_COMB (@lem118137) (@lem118136 R)). Qed.
Lemma lem118139 (R : type1605) (m : nat) : (term89 R m) = (term63 R m).
Proof. exact (eq_refl (term89 R m)). Qed.
Lemma lem118140 (R : type1605) : (term76 R) = (term76 R).
Proof. exact (eq_refl (term76 R)). Qed.
Lemma lem118141 (R : type1605) (m : nat) : (term94 R m) = (term95 R m).
Proof. exact (MK_COMB (@lem118140 R) (@lem118139 R m)). Qed.
Lemma lem118142 (R : type1605) : (term96 R) = (term97 R).
Proof. exact (fun_ext (fun m : nat => @lem118141 R m)). Qed.
Lemma lem118143 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118144 (R : type1605) : (term88 R) = (term98 R).
Proof. exact (MK_COMB (@lem118143) (@lem118142 R)). Qed.
Lemma lem118145 (R : type1605) : ((term87 R) = (term88 R)) = ((term78 R) = (term98 R)).
Proof. exact (MK_COMB (@lem118138 R) (@lem118144 R)). Qed.
Lemma lem118146 (R : type1605) : (term78 R) = (term98 R).
Proof. exact (EQ_MP (@lem118145 R) (@lem118130 R)). Qed.
Lemma lem118148 {A : Type'} (P : Prop) (Q : A -> Prop) : (term83 A P Q) = (term84 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem118149 (P : Prop) (Q : nat -> Prop) : (term85 P Q) = (term86 P Q).
Proof. exact (@lem118148 nat P Q). Qed.
Lemma lem118150 (R : type1605) (m : nat) : (term99 R m) = (term100 R m).
Proof. exact (@lem118149 (term55 R) (term62 R m)). Qed.
Lemma lem118151 (R : type1605) (m : nat) (d : nat) : (term101 R m d) = (term60 R m d).
Proof. exact (eq_refl (term101 R m d)). Qed.
Lemma lem118152 (R : type1605) (m : nat) : (term102 R m) = (term62 R m).
Proof. exact (fun_ext (fun d : nat => @lem118151 R m d)). Qed.
Lemma lem118153 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118154 (R : type1605) (m : nat) : (term103 R m) = (term63 R m).
Proof. exact (MK_COMB (@lem118153) (@lem118152 R m)). Qed.
Lemma lem118155 (R : type1605) : (term76 R) = (term76 R).
Proof. exact (eq_refl (term76 R)). Qed.
Lemma lem118156 (R : type1605) (m : nat) : (term99 R m) = (term95 R m).
Proof. exact (MK_COMB (@lem118155 R) (@lem118154 R m)). Qed.
Lemma lem118157 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem118158 (R : type1605) (m : nat) : (term104 R m) = (term105 R m).
Proof. exact (MK_COMB (@lem118157) (@lem118156 R m)). Qed.
Lemma lem118159 (R : type1605) (m : nat) (d : nat) : (term101 R m d) = (term60 R m d).
Proof. exact (eq_refl (term101 R m d)). Qed.
Lemma lem118160 (R : type1605) : (term76 R) = (term76 R).
Proof. exact (eq_refl (term76 R)). Qed.
Lemma lem118161 (R : type1605) (m : nat) (d : nat) : (term106 R m d) = (term107 R m d).
Proof. exact (MK_COMB (@lem118160 R) (@lem118159 R m d)). Qed.
Lemma lem118162 (R : type1605) (m : nat) : (term108 R m) = (term109 R m).
Proof. exact (fun_ext (fun d : nat => @lem118161 R m d)). Qed.
Lemma lem118163 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118164 (R : type1605) (m : nat) : (term100 R m) = (term110 R m).
Proof. exact (MK_COMB (@lem118163) (@lem118162 R m)). Qed.
Lemma lem118165 (R : type1605) (m : nat) : ((term99 R m) = (term100 R m)) = ((term95 R m) = (term110 R m)).
Proof. exact (MK_COMB (@lem118158 R m) (@lem118164 R m)). Qed.
Lemma lem118166 (R : type1605) (m : nat) : (term95 R m) = (term110 R m).
Proof. exact (EQ_MP (@lem118165 R m) (@lem118150 R m)). Qed.
Lemma lem118167 (R : type1605) : (term97 R) = (term111 R).
Proof. exact (fun_ext (fun m : nat => @lem118166 R m)). Qed.
Lemma lem118168 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118169 (R : type1605) : (term98 R) = (term112 R).
Proof. exact (MK_COMB (@lem118168) (@lem118167 R)). Qed.
Lemma lem118170 (R : type1605) : (term78 R) = (term112 R).
Proof. exact (TRANS (@lem118146 R) (@lem118169 R)). Qed.
Lemma lem118171 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem118172 (R : type1605) : (term80 R) = (term113 R).
Proof. exact (MK_COMB (@lem118171) (@lem118170 R)). Qed.
Lemma lem118174 {A : Type'} (P : A -> Prop) (Q : Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem118175 (P : nat -> Prop) (Q : Prop) : (term116 P Q) = (term117 P Q).
Proof. exact (@lem118174 nat P Q). Qed.
Lemma lem118176 (R : type1605) : (term118 R) = (term119 R).
Proof. exact (@lem118175 (term52 R) (term2 R)). Qed.
Lemma lem118177 (R : type1605) (m : nat) : (term120 R m) = (term44 R m).
Proof. exact (eq_refl (term120 R m)). Qed.
Lemma lem118178 (R : type1605) : (term121 R) = (term52 R).
Proof. exact (fun_ext (fun m : nat => @lem118177 R m)). Qed.
Lemma lem118179 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118180 (R : type1605) : (term122 R) = (term53 R).
Proof. exact (MK_COMB (@lem118179) (@lem118178 R)). Qed.
Lemma lem118181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem118182 (R : type1605) : (term123 R) = (term72 R).
Proof. exact (MK_COMB (@lem118181) (@lem118180 R)). Qed.
Lemma lem118183 (R : type1605) : (term2 R) = (term2 R).
Proof. exact (eq_refl (term2 R)). Qed.
Lemma lem118184 (R : type1605) : (term118 R) = (term74 R).
Proof. exact (MK_COMB (@lem118182 R) (@lem118183 R)). Qed.
Lemma lem118185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem118186 (R : type1605) : (term124 R) = (term125 R).
Proof. exact (MK_COMB (@lem118185) (@lem118184 R)). Qed.
Lemma lem118187 (R : type1605) (m : nat) : (term120 R m) = (term44 R m).
Proof. exact (eq_refl (term120 R m)). Qed.
Lemma lem118188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem118189 (R : type1605) (m : nat) : (term126 R m) = (term127 R m).
Proof. exact (MK_COMB (@lem118188) (@lem118187 R m)). Qed.
Lemma lem118190 (R : type1605) : (term2 R) = (term2 R).
Proof. exact (eq_refl (term2 R)). Qed.
Lemma lem118191 (m : nat) (R : type1605) : (term128 m R) = (term129 m R).
Proof. exact (MK_COMB (@lem118189 R m) (@lem118190 R)). Qed.
Lemma lem118192 (R : type1605) : (term130 R) = (term131 R).
Proof. exact (fun_ext (fun m : nat => @lem118191 m R)). Qed.
Lemma lem118193 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118194 (R : type1605) : (term119 R) = (term132 R).
Proof. exact (MK_COMB (@lem118193) (@lem118192 R)). Qed.
Lemma lem118195 (R : type1605) : ((term118 R) = (term119 R)) = ((term74 R) = (term132 R)).
Proof. exact (MK_COMB (@lem118186 R) (@lem118194 R)). Qed.
Lemma lem118196 (R : type1605) : (term74 R) = (term132 R).
Proof. exact (EQ_MP (@lem118195 R) (@lem118176 R)). Qed.
Lemma lem118198 {A : Type'} (P : A -> Prop) (Q : Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem118199 (P : nat -> Prop) (Q : Prop) : (term116 P Q) = (term117 P Q).
Proof. exact (@lem118198 nat P Q). Qed.
Lemma lem118200 (m : nat) (R : type1605) : (term133 m R) = (term134 m R).
Proof. exact (@lem118199 (term43 R m) (term2 R)). Qed.
Lemma lem118201 (R : type1605) (m : nat) (n : nat) : (term135 R m n) = (term34 R m n).
Proof. exact (eq_refl (term135 R m n)). Qed.
Lemma lem118202 (R : type1605) (m : nat) : (term136 R m) = (term43 R m).
Proof. exact (fun_ext (fun n : nat => @lem118201 R m n)). Qed.
Lemma lem118203 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118204 (R : type1605) (m : nat) : (term137 R m) = (term44 R m).
Proof. exact (MK_COMB (@lem118203) (@lem118202 R m)). Qed.
Lemma lem118205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem118206 (R : type1605) (m : nat) : (term138 R m) = (term127 R m).
Proof. exact (MK_COMB (@lem118205) (@lem118204 R m)). Qed.
Lemma lem118207 (R : type1605) : (term2 R) = (term2 R).
Proof. exact (eq_refl (term2 R)). Qed.
Lemma lem118208 (m : nat) (R : type1605) : (term133 m R) = (term129 m R).
Proof. exact (MK_COMB (@lem118206 R m) (@lem118207 R)). Qed.
Lemma lem118209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem118210 (m : nat) (R : type1605) : (term139 m R) = (term140 m R).
Proof. exact (MK_COMB (@lem118209) (@lem118208 m R)). Qed.
Lemma lem118211 (R : type1605) (m : nat) (n : nat) : (term135 R m n) = (term34 R m n).
Proof. exact (eq_refl (term135 R m n)). Qed.
Lemma lem118212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem118213 (R : type1605) (m : nat) (n : nat) : (term141 R m n) = (term142 R m n).
Proof. exact (MK_COMB (@lem118212) (@lem118211 R m n)). Qed.
Lemma lem118214 (R : type1605) : (term2 R) = (term2 R).
Proof. exact (eq_refl (term2 R)). Qed.
Lemma lem118215 (m : nat) (n : nat) (R : type1605) : (term143 m n R) = (term144 m n R).
Proof. exact (MK_COMB (@lem118213 R m n) (@lem118214 R)). Qed.
Lemma lem118216 (m : nat) (R : type1605) : (term145 m R) = (term146 m R).
Proof. exact (fun_ext (fun n : nat => @lem118215 m n R)). Qed.
Lemma lem118217 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118218 (m : nat) (R : type1605) : (term134 m R) = (term147 m R).
Proof. exact (MK_COMB (@lem118217) (@lem118216 m R)). Qed.
Lemma lem118219 (m : nat) (R : type1605) : ((term133 m R) = (term134 m R)) = ((term129 m R) = (term147 m R)).
Proof. exact (MK_COMB (@lem118210 m R) (@lem118218 m R)). Qed.
Lemma lem118220 (m : nat) (R : type1605) : (term129 m R) = (term147 m R).
Proof. exact (EQ_MP (@lem118219 m R) (@lem118200 m R)). Qed.
Lemma lem118221 (R : type1605) : (term131 R) = (term148 R).
Proof. exact (fun_ext (fun m : nat => @lem118220 m R)). Qed.
Lemma lem118222 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118223 (R : type1605) : (term132 R) = (term149 R).
Proof. exact (MK_COMB (@lem118222) (@lem118221 R)). Qed.
Lemma lem118224 (R : type1605) : (term74 R) = (term149 R).
Proof. exact (TRANS (@lem118196 R) (@lem118223 R)). Qed.
Lemma lem118225 (R : type1605) : (term82 R) = (term150 R).
Proof. exact (MK_COMB (@lem118172 R) (@lem118224 R)). Qed.
Lemma lem118227 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem118228 (P : nat -> Prop) (Q : nat -> Prop) : (term153 P Q) = (term154 P Q).
Proof. exact (@lem118227 nat P Q). Qed.
Lemma lem118229 (R : type1605) : (term155 R) = (term156 R).
Proof. exact (@lem118228 (term111 R) (term148 R)). Qed.
Lemma lem118230 (R : type1605) (m : nat) : (term157 R m) = (term110 R m).
Proof. exact (eq_refl (term157 R m)). Qed.
Lemma lem118231 (R : type1605) : (term158 R) = (term111 R).
Proof. exact (fun_ext (fun m : nat => @lem118230 R m)). Qed.
Lemma lem118232 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118233 (R : type1605) : (term159 R) = (term112 R).
Proof. exact (MK_COMB (@lem118232) (@lem118231 R)). Qed.
Lemma lem118234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem118235 (R : type1605) : (term160 R) = (term113 R).
Proof. exact (MK_COMB (@lem118234) (@lem118233 R)). Qed.
Lemma lem118236 (m : nat) (R : type1605) : (term161 R m) = (term147 m R).
Proof. exact (eq_refl (term161 R m)). Qed.
Lemma lem118237 (R : type1605) : (term162 R) = (term148 R).
Proof. exact (fun_ext (fun m : nat => @lem118236 m R)). Qed.
Lemma lem118238 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118239 (R : type1605) : (term163 R) = (term149 R).
Proof. exact (MK_COMB (@lem118238) (@lem118237 R)). Qed.
Lemma lem118240 (R : type1605) : (term155 R) = (term150 R).
Proof. exact (MK_COMB (@lem118235 R) (@lem118239 R)). Qed.
Lemma lem118241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem118242 (R : type1605) : (term164 R) = (term165 R).
Proof. exact (MK_COMB (@lem118241) (@lem118240 R)). Qed.
Lemma lem118243 (R : type1605) (m : nat) : (term157 R m) = (term110 R m).
Proof. exact (eq_refl (term157 R m)). Qed.
Lemma lem118244 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem118245 (R : type1605) (m : nat) : (term166 R m) = (term167 R m).
Proof. exact (MK_COMB (@lem118244) (@lem118243 R m)). Qed.
Lemma lem118246 (m : nat) (R : type1605) : (term161 R m) = (term147 m R).
Proof. exact (eq_refl (term161 R m)). Qed.
Lemma lem118247 (m : nat) (R : type1605) : (term168 R m) = (term169 m R).
Proof. exact (MK_COMB (@lem118245 R m) (@lem118246 m R)). Qed.
Lemma lem118248 (R : type1605) : (term170 R) = (term171 R).
Proof. exact (fun_ext (fun m : nat => @lem118247 m R)). Qed.
Lemma lem118249 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118250 (R : type1605) : (term156 R) = (term172 R).
Proof. exact (MK_COMB (@lem118249) (@lem118248 R)). Qed.
Lemma lem118251 (R : type1605) : ((term155 R) = (term156 R)) = ((term150 R) = (term172 R)).
Proof. exact (MK_COMB (@lem118242 R) (@lem118250 R)). Qed.
Lemma lem118252 (R : type1605) : (term150 R) = (term172 R).
Proof. exact (EQ_MP (@lem118251 R) (@lem118229 R)). Qed.
Lemma lem118254 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem118255 (P : nat -> Prop) (Q : nat -> Prop) : (term153 P Q) = (term154 P Q).
Proof. exact (@lem118254 nat P Q). Qed.
Lemma lem118256 (m : nat) (R : type1605) : (term173 m R) = (term174 m R).
Proof. exact (@lem118255 (term109 R m) (term146 m R)). Qed.
Lemma lem118257 (R : type1605) (m : nat) (d : nat) : (term175 R m d) = (term107 R m d).
Proof. exact (eq_refl (term175 R m d)). Qed.
Lemma lem118258 (R : type1605) (m : nat) : (term176 R m) = (term109 R m).
Proof. exact (fun_ext (fun d : nat => @lem118257 R m d)). Qed.
Lemma lem118259 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118260 (R : type1605) (m : nat) : (term177 R m) = (term110 R m).
Proof. exact (MK_COMB (@lem118259) (@lem118258 R m)). Qed.
Lemma lem118261 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem118262 (R : type1605) (m : nat) : (term178 R m) = (term167 R m).
Proof. exact (MK_COMB (@lem118261) (@lem118260 R m)). Qed.
Lemma lem118263 (m : nat) (d : nat) (R : type1605) : (term179 m R d) = (term144 m d R).
Proof. exact (eq_refl (term179 m R d)). Qed.
Lemma lem118264 (m : nat) (R : type1605) : (term180 m R) = (term146 m R).
Proof. exact (fun_ext (fun d : nat => @lem118263 m d R)). Qed.
Lemma lem118265 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118266 (m : nat) (R : type1605) : (term181 m R) = (term147 m R).
Proof. exact (MK_COMB (@lem118265) (@lem118264 m R)). Qed.
Lemma lem118267 (m : nat) (R : type1605) : (term173 m R) = (term169 m R).
Proof. exact (MK_COMB (@lem118262 R m) (@lem118266 m R)). Qed.
Lemma lem118268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem118269 (m : nat) (R : type1605) : (term182 m R) = (term183 m R).
Proof. exact (MK_COMB (@lem118268) (@lem118267 m R)). Qed.
Lemma lem118270 (R : type1605) (m : nat) (d : nat) : (term175 R m d) = (term107 R m d).
Proof. exact (eq_refl (term175 R m d)). Qed.
Lemma lem118271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem118272 (R : type1605) (m : nat) (d : nat) : (term184 R m d) = (term185 R m d).
Proof. exact (MK_COMB (@lem118271) (@lem118270 R m d)). Qed.
Lemma lem118273 (m : nat) (d : nat) (R : type1605) : (term179 m R d) = (term144 m d R).
Proof. exact (eq_refl (term179 m R d)). Qed.
Lemma lem118274 (m : nat) (d : nat) (R : type1605) : (term186 m R d) = (term187 m d R).
Proof. exact (MK_COMB (@lem118272 R m d) (@lem118273 m d R)). Qed.
Lemma lem118275 (m : nat) (R : type1605) : (term188 m R) = (term189 m R).
Proof. exact (fun_ext (fun d : nat => @lem118274 m d R)). Qed.
Lemma lem118276 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118277 (m : nat) (R : type1605) : (term174 m R) = (term190 m R).
Proof. exact (MK_COMB (@lem118276) (@lem118275 m R)). Qed.
Lemma lem118278 (m : nat) (R : type1605) : ((term173 m R) = (term174 m R)) = ((term169 m R) = (term190 m R)).
Proof. exact (MK_COMB (@lem118269 m R) (@lem118277 m R)). Qed.
Lemma lem118279 (m : nat) (R : type1605) : (term169 m R) = (term190 m R).
Proof. exact (EQ_MP (@lem118278 m R) (@lem118256 m R)). Qed.
Lemma lem118282 (m : nat) (R : type1605) : (term191 m R) = (term191 m R).
Proof. exact (eq_refl (term191 m R)). Qed.
Lemma lem118283 (m : nat) (R : type1605) : (term191 m R) = ((term169 m R) = (term190 m R)).
Proof. exact (eq_refl (term191 m R)). Qed.
Lemma lem118284 (m : nat) (R : type1605) : (term192 m R) = (term192 m R).
Proof. exact (eq_refl (term192 m R)). Qed.
Lemma lem118285 (m : nat) (R : type1605) : ((term191 m R) = (term191 m R)) = ((term191 m R) = ((term169 m R) = (term190 m R))).
Proof. exact (MK_COMB (@lem118284 m R) (@lem118283 m R)). Qed.
Lemma lem118286 (m : nat) (R : type1605) : (term191 m R) = ((term169 m R) = (term190 m R)).
Proof. exact (eq_refl (term191 m R)). Qed.
Lemma lem118287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem118288 (m : nat) (R : type1605) : (term192 m R) = (term193 m R).
Proof. exact (MK_COMB (@lem118287) (@lem118286 m R)). Qed.
Lemma lem118289 (m : nat) (R : type1605) : ((term169 m R) = (term190 m R)) = ((term169 m R) = (term190 m R)).
Proof. exact (eq_refl ((term169 m R) = (term190 m R))). Qed.
Lemma lem118290 (m : nat) (R : type1605) : ((term191 m R) = ((term169 m R) = (term190 m R))) = (((term169 m R) = (term190 m R)) = ((term169 m R) = (term190 m R))).
Proof. exact (MK_COMB (@lem118288 m R) (@lem118289 m R)). Qed.
Lemma lem118291 (m : nat) (R : type1605) : ((term191 m R) = (term191 m R)) = (((term169 m R) = (term190 m R)) = ((term169 m R) = (term190 m R))).
Proof. exact (TRANS (@lem118285 m R) (@lem118290 m R)). Qed.
Lemma lem118292 (m : nat) (R : type1605) : ((term169 m R) = (term190 m R)) = ((term169 m R) = (term190 m R)).
Proof. exact (EQ_MP (@lem118291 m R) (@lem118282 m R)). Qed.
Lemma lem118293 (m : nat) (R : type1605) : (term169 m R) = (term190 m R).
Proof. exact (EQ_MP (@lem118292 m R) (@lem118279 m R)). Qed.
Lemma lem118294 (R : type1605) : (term171 R) = (term194 R).
Proof. exact (fun_ext (fun m : nat => @lem118293 m R)). Qed.
Lemma lem118295 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118296 (R : type1605) : (term172 R) = (term195 R).
Proof. exact (MK_COMB (@lem118295) (@lem118294 R)). Qed.
Lemma lem118297 (R : type1605) : (term150 R) = (term195 R).
Proof. exact (TRANS (@lem118252 R) (@lem118296 R)). Qed.
Lemma lem118299 (R : type1605) : (term82 R) = (term195 R).
Proof. exact (TRANS (@lem118225 R) (@lem118297 R)). Qed.
Lemma lem118300 (R : type1605) : (term4 R) = (term195 R).
Proof. exact (TRANS (@lem118005 R) (@lem118299 R)). Qed.
Lemma lem118301 (R : type1605) (h1 : term4 R) : term195 R.
Proof. exact (EQ_MP (@lem118300 R) (@lem117925 R h1)). Qed.
Lemma lem118305 (n : nat) (m : nat) (d : nat) : (n = (Nat.add m d)) = (n = (Nat.add m d)).
Proof. exact (eq_refl (n = (Nat.add m d))). Qed.
Lemma lem118306 (P : nat -> Prop) : (term196 P) = (term197 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem118307 (n : nat) (m : nat) : (term198 n m) = (term199 n m).
Proof. exact (@lem118306 (term18 n m)). Qed.
Lemma lem118308 (n : nat) (m : nat) (d : nat) : (term200 n m d) = (n = (Nat.add m d)).
Proof. exact (eq_refl (term200 n m d)). Qed.
Lemma lem118309 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem118311 (n : nat) (m : nat) (d : nat) : (term201 n m d) = (term202 n m d).
Proof. exact (MK_COMB (@lem118309) (@lem118308 n m d)). Qed.
Lemma lem118312 (n : nat) (m : nat) : (term203 n m) = (term204 n m).
Proof. exact (fun_ext (fun d : nat => @lem118311 n m d)). Qed.
Lemma lem118313 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118314 (n : nat) (m : nat) : (term199 n m) = (term205 n m).
Proof. exact (MK_COMB (@lem118313) (@lem118312 n m)). Qed.
Lemma lem118315 (n : nat) (m : nat) : (term198 n m) = (term205 n m).
Proof. exact (TRANS (@lem118307 n m) (@lem118314 n m)). Qed.
Lemma lem118316 (n : nat) (m : nat) : (term18 n m) = (term18 n m).
Proof. exact (fun_ext (fun d : nat => @lem118305 n m d)). Qed.
Lemma lem118317 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118318 (n : nat) (m : nat) : (term19 n m) = (term19 n m).
Proof. exact (MK_COMB (@lem118317) (@lem118316 n m)). Qed.
Lemma lem118320 (m : nat) (n : nat) : (term206 m n) = (term206 m n).
Proof. exact (eq_refl (term206 m n)). Qed.
Lemma lem118321 (n : nat) (m : nat) : (term207 n m) = (term207 n m).
Proof. exact (MK_COMB (@lem118320 m n) (@lem118318 n m)). Qed.
Lemma lem118323 (m : nat) (n : nat) : (term208 m n) = (term208 m n).
Proof. exact (eq_refl (term208 m n)). Qed.
Lemma lem118324 (n : nat) (m : nat) : (term209 n m) = (term210 n m).
Proof. exact (MK_COMB (@lem118323 m n) (@lem118315 n m)). Qed.
Lemma lem118325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem118326 (n : nat) (m : nat) : (term211 n m) = (term212 n m).
Proof. exact (MK_COMB (@lem118325) (@lem118324 n m)). Qed.
Lemma lem118327 (n : nat) (m : nat) : (term213 n m) = (term214 n m).
Proof. exact (MK_COMB (@lem118326 n m) (@lem118321 n m)). Qed.
Lemma lem118328 (n : nat) (m : nat) : ((Peano.le m n) = (term19 n m)) = (term213 n m).
Proof. exact (@lem17784 (Peano.le m n) (term19 n m)). Qed.
Lemma lem118329 (n : nat) (m : nat) : ((Peano.le m n) = (term19 n m)) = (term214 n m).
Proof. exact (TRANS (@lem118328 n m) (@lem118327 n m)). Qed.
Lemma lem118330 (m : nat) : (term21 m) = (term215 m).
Proof. exact (fun_ext (fun n : nat => @lem118329 n m)). Qed.
Lemma lem118331 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118332 (m : nat) : (term22 m) = (term216 m).
Proof. exact (MK_COMB (@lem118331) (@lem118330 m)). Qed.
Lemma lem118333 : term23 = term217.
Proof. exact (fun_ext (fun m : nat => @lem118332 m)). Qed.
Lemma lem118334 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118335 : term11 = term218.
Proof. exact (MK_COMB (@lem118334) (@lem118333)). Qed.
Lemma lem118341 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term219 A P Q) = (term220 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem118342 (P : nat -> Prop) (Q : nat -> Prop) : (term221 P Q) = (term222 P Q).
Proof. exact (@lem118341 nat P Q). Qed.
Lemma lem118343 (m : nat) : (term223 m) = (term224 m).
Proof. exact (@lem118342 (term225 m) (term226 m)). Qed.
Lemma lem118344 (n : nat) (m : nat) : (term227 m n) = (term210 n m).
Proof. exact (eq_refl (term227 m n)). Qed.
Lemma lem118345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem118346 (n : nat) (m : nat) : (term228 m n) = (term212 n m).
Proof. exact (MK_COMB (@lem118345) (@lem118344 n m)). Qed.
Lemma lem118347 (n : nat) (m : nat) : (term229 m n) = (term207 n m).
Proof. exact (eq_refl (term229 m n)). Qed.
Lemma lem118348 (n : nat) (m : nat) : (term230 m n) = (term214 n m).
Proof. exact (MK_COMB (@lem118346 n m) (@lem118347 n m)). Qed.
Lemma lem118349 (m : nat) : (term231 m) = (term215 m).
Proof. exact (fun_ext (fun n : nat => @lem118348 n m)). Qed.
Lemma lem118350 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118351 (m : nat) : (term223 m) = (term216 m).
Proof. exact (MK_COMB (@lem118350) (@lem118349 m)). Qed.
Lemma lem118352 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem118353 (m : nat) : (term232 m) = (term233 m).
Proof. exact (MK_COMB (@lem118352) (@lem118351 m)). Qed.
Lemma lem118354 (n : nat) (m : nat) : (term227 m n) = (term210 n m).
Proof. exact (eq_refl (term227 m n)). Qed.
Lemma lem118355 (m : nat) : (term234 m) = (term225 m).
Proof. exact (fun_ext (fun n : nat => @lem118354 n m)). Qed.
Lemma lem118356 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118357 (m : nat) : (term235 m) = (term236 m).
Proof. exact (MK_COMB (@lem118356) (@lem118355 m)). Qed.
Lemma lem118358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem118359 (m : nat) : (term237 m) = (term238 m).
Proof. exact (MK_COMB (@lem118358) (@lem118357 m)). Qed.
Lemma lem118360 (n : nat) (m : nat) : (term229 m n) = (term207 n m).
Proof. exact (eq_refl (term229 m n)). Qed.
Lemma lem118361 (m : nat) : (term239 m) = (term226 m).
Proof. exact (fun_ext (fun n : nat => @lem118360 n m)). Qed.
Lemma lem118362 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118363 (m : nat) : (term240 m) = (term241 m).
Proof. exact (MK_COMB (@lem118362) (@lem118361 m)). Qed.
Lemma lem118364 (m : nat) : (term224 m) = (term242 m).
Proof. exact (MK_COMB (@lem118359 m) (@lem118363 m)). Qed.
Lemma lem118365 (m : nat) : ((term223 m) = (term224 m)) = ((term216 m) = (term242 m)).
Proof. exact (MK_COMB (@lem118353 m) (@lem118364 m)). Qed.
Lemma lem118366 (m : nat) : (term216 m) = (term242 m).
Proof. exact (EQ_MP (@lem118365 m) (@lem118343 m)). Qed.
Lemma lem118471 : term217 = term243.
Proof. exact (fun_ext (fun m : nat => @lem118366 m)). Qed.
Lemma lem118472 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118473 : term218 = term244.
Proof. exact (MK_COMB (@lem118472) (@lem118471)). Qed.
Lemma lem118475 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term219 A P Q) = (term220 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem118476 (P : nat -> Prop) (Q : nat -> Prop) : (term221 P Q) = (term222 P Q).
Proof. exact (@lem118475 nat P Q). Qed.
Lemma lem118477 : term245 = term246.
Proof. exact (@lem118476 term247 term248). Qed.
Lemma lem118478 (m : nat) : (term249 m) = (term236 m).
Proof. exact (eq_refl (term249 m)). Qed.
Lemma lem118479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem118480 (m : nat) : (term250 m) = (term238 m).
Proof. exact (MK_COMB (@lem118479) (@lem118478 m)). Qed.
Lemma lem118481 (m : nat) : (term251 m) = (term241 m).
Proof. exact (eq_refl (term251 m)). Qed.
Lemma lem118482 (m : nat) : (term252 m) = (term242 m).
Proof. exact (MK_COMB (@lem118480 m) (@lem118481 m)). Qed.
Lemma lem118483 : term253 = term243.
Proof. exact (fun_ext (fun m : nat => @lem118482 m)). Qed.
Lemma lem118484 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118485 : term245 = term244.
Proof. exact (MK_COMB (@lem118484) (@lem118483)). Qed.
Lemma lem118486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem118487 : term254 = term255.
Proof. exact (MK_COMB (@lem118486) (@lem118485)). Qed.
Lemma lem118488 (m : nat) : (term249 m) = (term236 m).
Proof. exact (eq_refl (term249 m)). Qed.
Lemma lem118489 : term256 = term247.
Proof. exact (fun_ext (fun m : nat => @lem118488 m)). Qed.
Lemma lem118490 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118491 : term257 = term258.
Proof. exact (MK_COMB (@lem118490) (@lem118489)). Qed.
Lemma lem118492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem118493 : term259 = term260.
Proof. exact (MK_COMB (@lem118492) (@lem118491)). Qed.
Lemma lem118494 (m : nat) : (term251 m) = (term241 m).
Proof. exact (eq_refl (term251 m)). Qed.
Lemma lem118495 : term261 = term248.
Proof. exact (fun_ext (fun m : nat => @lem118494 m)). Qed.
Lemma lem118496 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118497 : term262 = term263.
Proof. exact (MK_COMB (@lem118496) (@lem118495)). Qed.
Lemma lem118498 : term246 = term264.
Proof. exact (MK_COMB (@lem118493) (@lem118497)). Qed.
Lemma lem118499 : (term245 = term246) = (term244 = term264).
Proof. exact (MK_COMB (@lem118487) (@lem118498)). Qed.
Lemma lem118500 : term244 = term264.
Proof. exact (EQ_MP (@lem118499) (@lem118477)). Qed.
Lemma lem118613 : term218 = term264.
Proof. exact (TRANS (@lem118473) (@lem118500)). Qed.
Lemma lem118615 {A : Type'} (P : Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem118616 (P : Prop) (Q : nat -> Prop) : (term267 P Q) = (term268 P Q).
Proof. exact (@lem118615 nat P Q). Qed.
Lemma lem118617 (n : nat) (m : nat) : (term269 n m) = (term270 n m).
Proof. exact (@lem118616 (term271 m n) (term18 n m)). Qed.
Lemma lem118618 (n : nat) (m : nat) (d : nat) : (term200 n m d) = (n = (Nat.add m d)).
Proof. exact (eq_refl (term200 n m d)). Qed.
Lemma lem118619 (n : nat) (m : nat) : (term272 n m) = (term18 n m).
Proof. exact (fun_ext (fun d : nat => @lem118618 n m d)). Qed.
Lemma lem118620 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118621 (n : nat) (m : nat) : (term273 n m) = (term19 n m).
Proof. exact (MK_COMB (@lem118620) (@lem118619 n m)). Qed.
Lemma lem118622 (m : nat) (n : nat) : (term206 m n) = (term206 m n).
Proof. exact (eq_refl (term206 m n)). Qed.
Lemma lem118623 (n : nat) (m : nat) : (term269 n m) = (term207 n m).
Proof. exact (MK_COMB (@lem118622 m n) (@lem118621 n m)). Qed.
Lemma lem118624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem118625 (n : nat) (m : nat) : (term274 n m) = (term275 n m).
Proof. exact (MK_COMB (@lem118624) (@lem118623 n m)). Qed.
Lemma lem118626 (n : nat) (m : nat) (d : nat) : (term200 n m d) = (n = (Nat.add m d)).
Proof. exact (eq_refl (term200 n m d)). Qed.
Lemma lem118627 (m : nat) (n : nat) : (term206 m n) = (term206 m n).
Proof. exact (eq_refl (term206 m n)). Qed.
Lemma lem118628 (n : nat) (m : nat) (d : nat) : (term276 n m d) = (term277 n m d).
Proof. exact (MK_COMB (@lem118627 m n) (@lem118626 n m d)). Qed.
Lemma lem118629 (n : nat) (m : nat) : (term278 n m) = (term279 n m).
Proof. exact (fun_ext (fun d : nat => @lem118628 n m d)). Qed.
Lemma lem118630 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118631 (n : nat) (m : nat) : (term270 n m) = (term280 n m).
Proof. exact (MK_COMB (@lem118630) (@lem118629 n m)). Qed.
Lemma lem118632 (n : nat) (m : nat) : ((term269 n m) = (term270 n m)) = ((term207 n m) = (term280 n m)).
Proof. exact (MK_COMB (@lem118625 n m) (@lem118631 n m)). Qed.
Lemma lem118633 (n : nat) (m : nat) : (term207 n m) = (term280 n m).
Proof. exact (EQ_MP (@lem118632 n m) (@lem118617 n m)). Qed.
Lemma lem118634 (m : nat) : (term226 m) = (term281 m).
Proof. exact (fun_ext (fun n : nat => @lem118633 n m)). Qed.
Lemma lem118635 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118636 (m : nat) : (term241 m) = (term282 m).
Proof. exact (MK_COMB (@lem118635) (@lem118634 m)). Qed.
Lemma lem118638 {A B : Type'} (P : type1413 A B) : (term283 A B P) = (term284 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem118639 (P : type1605) : (term285 P) = (term286 P).
Proof. exact (@lem118638 nat nat P). Qed.
Lemma lem118640 (m : nat) : (term287 m) = (term288 m).
Proof. exact (@lem118639 (term289 m)). Qed.
Lemma lem118641 (n : nat) (m : nat) : (term290 m n) = (term279 n m).
Proof. exact (eq_refl (term290 m n)). Qed.
Lemma lem118642 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem118643 (n : nat) (m : nat) (d : nat) : (term291 m n d) = (term292 n m d).
Proof. exact (MK_COMB (@lem118641 n m) (@lem118642 d)). Qed.
Lemma lem118644 (n : nat) (m : nat) (d : nat) : (term292 n m d) = (term277 n m d).
Proof. exact (eq_refl (term292 n m d)). Qed.
Lemma lem118645 (n : nat) (m : nat) (d : nat) : (term291 m n d) = (term277 n m d).
Proof. exact (TRANS (@lem118643 n m d) (@lem118644 n m d)). Qed.
Lemma lem118646 (n : nat) (m : nat) : (term293 m n) = (term279 n m).
Proof. exact (fun_ext (fun d : nat => @lem118645 n m d)). Qed.
Lemma lem118647 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem118648 (n : nat) (m : nat) : (term294 m n) = (term280 n m).
Proof. exact (MK_COMB (@lem118647) (@lem118646 n m)). Qed.
Lemma lem118649 (m : nat) : (term295 m) = (term281 m).
Proof. exact (fun_ext (fun n : nat => @lem118648 n m)). Qed.
Lemma lem118650 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118651 (m : nat) : (term287 m) = (term282 m).
Proof. exact (MK_COMB (@lem118650) (@lem118649 m)). Qed.
Lemma lem118652 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem118653 (m : nat) : (term296 m) = (term297 m).
Proof. exact (MK_COMB (@lem118652) (@lem118651 m)). Qed.
Lemma lem118654 (n : nat) (m : nat) : (term290 m n) = (term279 n m).
Proof. exact (eq_refl (term290 m n)). Qed.
Lemma lem118655 (d : nat -> nat) (n : nat) : (d n) = (d n).
Proof. exact (eq_refl (d n)). Qed.
Lemma lem118656 (m : nat) (d : nat -> nat) (n : nat) : (term298 m d n) = (term299 m d n).
Proof. exact (MK_COMB (@lem118654 n m) (@lem118655 d n)). Qed.
Lemma lem118657 (m : nat) (d : nat -> nat) (n : nat) : (term299 m d n) = (term300 m d n).
Proof. exact (eq_refl (term299 m d n)). Qed.
Lemma lem118658 (m : nat) (d : nat -> nat) (n : nat) : (term298 m d n) = (term300 m d n).
Proof. exact (TRANS (@lem118656 m d n) (@lem118657 m d n)). Qed.
Lemma lem118659 (m : nat) (d : nat -> nat) : (term301 m d) = (term302 m d).
Proof. exact (fun_ext (fun n : nat => @lem118658 m d n)). Qed.
Lemma lem118660 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118661 (m : nat) (d : nat -> nat) : (term303 m d) = (term304 m d).
Proof. exact (MK_COMB (@lem118660) (@lem118659 m d)). Qed.
Lemma lem118662 (m : nat) : (term305 m) = (term306 m).
Proof. exact (fun_ext (fun d : nat -> nat => @lem118661 m d)). Qed.
Lemma lem118663 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem118664 (m : nat) : (term288 m) = (term307 m).
Proof. exact (MK_COMB (@lem118663) (@lem118662 m)). Qed.
Lemma lem118665 (m : nat) : ((term287 m) = (term288 m)) = ((term282 m) = (term307 m)).
Proof. exact (MK_COMB (@lem118653 m) (@lem118664 m)). Qed.
Lemma lem118666 (m : nat) : (term282 m) = (term307 m).
Proof. exact (EQ_MP (@lem118665 m) (@lem118640 m)). Qed.
Lemma lem118667 (m : nat) : (term241 m) = (term307 m).
Proof. exact (TRANS (@lem118636 m) (@lem118666 m)). Qed.
Lemma lem118668 : term248 = term308.
Proof. exact (fun_ext (fun m : nat => @lem118667 m)). Qed.
Lemma lem118669 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118670 : term263 = term309.
Proof. exact (MK_COMB (@lem118669) (@lem118668)). Qed.
Lemma lem118672 {A B : Type'} (P : type1413 A B) : (term283 A B P) = (term284 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem118673 (P : type1586) : (term310 P) = (term311 P).
Proof. exact (@lem118672 nat (nat -> nat) P). Qed.
Lemma lem118674 : term312 = term313.
Proof. exact (@lem118673 term314). Qed.
Lemma lem118675 (m : nat) : (term315 m) = (term306 m).
Proof. exact (eq_refl (term315 m)). Qed.
Lemma lem118676 (d : nat -> nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem118677 (m : nat) (d : nat -> nat) : (term316 m d) = (term317 m d).
Proof. exact (MK_COMB (@lem118675 m) (@lem118676 d)). Qed.
Lemma lem118678 (m : nat) (d : nat -> nat) : (term317 m d) = (term304 m d).
Proof. exact (eq_refl (term317 m d)). Qed.
Lemma lem118679 (m : nat) (d : nat -> nat) : (term316 m d) = (term304 m d).
Proof. exact (TRANS (@lem118677 m d) (@lem118678 m d)). Qed.
Lemma lem118680 (m : nat) : (term318 m) = (term306 m).
Proof. exact (fun_ext (fun d : nat -> nat => @lem118679 m d)). Qed.
Lemma lem118681 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem118682 (m : nat) : (term319 m) = (term307 m).
Proof. exact (MK_COMB (@lem118681) (@lem118680 m)). Qed.
Lemma lem118683 : term320 = term308.
Proof. exact (fun_ext (fun m : nat => @lem118682 m)). Qed.
Lemma lem118684 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118685 : term312 = term309.
Proof. exact (MK_COMB (@lem118684) (@lem118683)). Qed.
Lemma lem118686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem118687 : term321 = term322.
Proof. exact (MK_COMB (@lem118686) (@lem118685)). Qed.
Lemma lem118688 (m : nat) : (term315 m) = (term306 m).
Proof. exact (eq_refl (term315 m)). Qed.
Lemma lem118689 (d : type1606) (m : nat) : (d m) = (d m).
Proof. exact (eq_refl (d m)). Qed.
Lemma lem118690 (d : type1606) (m : nat) : (term323 d m) = (term324 d m).
Proof. exact (MK_COMB (@lem118688 m) (@lem118689 d m)). Qed.
Lemma lem118691 (d : type1606) (m : nat) : (term324 d m) = (term325 d m).
Proof. exact (eq_refl (term324 d m)). Qed.
Lemma lem118692 (d : type1606) (m : nat) : (term323 d m) = (term325 d m).
Proof. exact (TRANS (@lem118690 d m) (@lem118691 d m)). Qed.
Lemma lem118693 (d : type1606) : (term326 d) = (term327 d).
Proof. exact (fun_ext (fun m : nat => @lem118692 d m)). Qed.
Lemma lem118694 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118695 (d : type1606) : (term328 d) = (term329 d).
Proof. exact (MK_COMB (@lem118694) (@lem118693 d)). Qed.
Lemma lem118696 : term330 = term331.
Proof. exact (fun_ext (fun d : type1606 => @lem118695 d)). Qed.
Lemma lem118697 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem118698 : term313 = term332.
Proof. exact (MK_COMB (@lem118697) (@lem118696)). Qed.
Lemma lem118699 : (term312 = term313) = (term309 = term332).
Proof. exact (MK_COMB (@lem118687) (@lem118698)). Qed.
Lemma lem118700 : term309 = term332.
Proof. exact (EQ_MP (@lem118699) (@lem118674)). Qed.
Lemma lem118701 : term263 = term332.
Proof. exact (TRANS (@lem118670) (@lem118700)). Qed.
Lemma lem118702 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem118703 : term264 = term333.
Proof. exact (MK_COMB (@lem118702) (@lem118701)). Qed.
Lemma lem118705 {A : Type'} (P : Prop) (Q : A -> Prop) : (term83 A P Q) = (term84 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem118706 (P : Prop) (Q : type961) : (term334 P Q) = (term335 P Q).
Proof. exact (@lem118705 type1606 P Q). Qed.
Lemma lem118707 : term336 = term337.
Proof. exact (@lem118706 term258 term331). Qed.
Lemma lem118708 (d : type1606) : (term338 d) = (term329 d).
Proof. exact (eq_refl (term338 d)). Qed.
Lemma lem118709 : term339 = term331.
Proof. exact (fun_ext (fun d : type1606 => @lem118708 d)). Qed.
Lemma lem118710 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem118711 : term340 = term332.
Proof. exact (MK_COMB (@lem118710) (@lem118709)). Qed.
Lemma lem118712 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem118713 : term336 = term333.
Proof. exact (MK_COMB (@lem118712) (@lem118711)). Qed.
Lemma lem118714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem118715 : term341 = term342.
Proof. exact (MK_COMB (@lem118714) (@lem118713)). Qed.
Lemma lem118716 (d : type1606) : (term338 d) = (term329 d).
Proof. exact (eq_refl (term338 d)). Qed.
Lemma lem118717 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem118718 (d : type1606) : (term343 d) = (term344 d).
Proof. exact (MK_COMB (@lem118717) (@lem118716 d)). Qed.
Lemma lem118719 : term345 = term346.
Proof. exact (fun_ext (fun d : type1606 => @lem118718 d)). Qed.
Lemma lem118720 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem118721 : term337 = term347.
Proof. exact (MK_COMB (@lem118720) (@lem118719)). Qed.
Lemma lem118722 : (term336 = term337) = (term333 = term347).
Proof. exact (MK_COMB (@lem118715) (@lem118721)). Qed.
Lemma lem118723 : term333 = term347.
Proof. exact (EQ_MP (@lem118722) (@lem118707)). Qed.
Lemma lem118724 : term264 = term347.
Proof. exact (TRANS (@lem118703) (@lem118723)). Qed.
Lemma lem118725 : term218 = term347.
Proof. exact (TRANS (@lem118613) (@lem118724)). Qed.
Lemma lem118726 : term11 = term347.
Proof. exact (TRANS (@lem118335) (@lem118725)). Qed.
Lemma lem118727 (h1 : term11) : term347.
Proof. exact (EQ_MP (@lem118726) (@lem117926 h1)). Qed.
Lemma lem118728 (d : type1606) (h1 : term344 d) : term344 d.
Proof. exact (h1). Qed.
Lemma lem118729 (m : nat) (R : type1605) (h1 : term190 m R) : term190 m R.
Proof. exact (h1). Qed.
Lemma lem118730 (m : nat) (d' : nat) (R : type1605) (h1 : term187 m d' R) : term187 m d' R.
Proof. exact (h1). Qed.
Lemma lem118753 (d : type1606) (m : nat) (n : nat) : (term348 d m n) = (term348 d m n).
Proof. exact (eq_refl (term348 d m n)). Qed.
Lemma lem118754 (d : type1606) (m : nat) : (term349 d m) = (term349 d m).
Proof. exact (fun_ext (fun n : nat => @lem118753 d m n)). Qed.
Lemma lem118755 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118756 (d : type1606) (m : nat) : (term325 d m) = (term325 d m).
Proof. exact (MK_COMB (@lem118755) (@lem118754 d m)). Qed.
Lemma lem118757 (d : type1606) : (term327 d) = (term327 d).
Proof. exact (fun_ext (fun m : nat => @lem118756 d m)). Qed.
Lemma lem118758 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118759 (d : type1606) : (term329 d) = (term329 d).
Proof. exact (MK_COMB (@lem118758) (@lem118757 d)). Qed.
Lemma lem118770 (n : nat) (m : nat) (d : nat) : (term202 n m d) = (term202 n m d).
Proof. exact (eq_refl (term202 n m d)). Qed.
Lemma lem118771 (n : nat) (m : nat) : (term204 n m) = (term204 n m).
Proof. exact (fun_ext (fun d : nat => @lem118770 n m d)). Qed.
Lemma lem118772 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118773 (n : nat) (m : nat) : (term205 n m) = (term205 n m).
Proof. exact (MK_COMB (@lem118772) (@lem118771 n m)). Qed.
Lemma lem118780 (m : nat) (n : nat) : (term208 m n) = (term208 m n).
Proof. exact (eq_refl (term208 m n)). Qed.
Lemma lem118781 (n : nat) (m : nat) : (term210 n m) = (term210 n m).
Proof. exact (MK_COMB (@lem118780 m n) (@lem118773 n m)). Qed.
Lemma lem118782 (m : nat) : (term225 m) = (term225 m).
Proof. exact (fun_ext (fun n : nat => @lem118781 n m)). Qed.
Lemma lem118783 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118784 (m : nat) : (term236 m) = (term236 m).
Proof. exact (MK_COMB (@lem118783) (@lem118782 m)). Qed.
Lemma lem118785 : term247 = term247.
Proof. exact (fun_ext (fun m : nat => @lem118784 m)). Qed.
Lemma lem118786 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118787 : term258 = term258.
Proof. exact (MK_COMB (@lem118786) (@lem118785)). Qed.
Lemma lem118788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem118789 : term260 = term260.
Proof. exact (MK_COMB (@lem118788) (@lem118787)). Qed.
Lemma lem118790 (d : type1606) : (term344 d) = (term344 d).
Proof. exact (MK_COMB (@lem118789) (@lem118759 d)). Qed.
Lemma lem118791 (d : type1606) (h1 : term344 d) : term344 d.
Proof. exact (EQ_MP (@lem118790 d) (@lem118728 d h1)). Qed.
Lemma lem118800 (R : type1605) (m : nat) (d : nat) : (term24 R m d) = (term24 R m d).
Proof. exact (eq_refl (term24 R m d)). Qed.
Lemma lem118801 (R : type1605) (m : nat) : (term25 R m) = (term25 R m).
Proof. exact (fun_ext (fun d : nat => @lem118800 R m d)). Qed.
Lemma lem118802 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118803 (R : type1605) (m : nat) : (term26 R m) = (term26 R m).
Proof. exact (MK_COMB (@lem118802) (@lem118801 R m)). Qed.
Lemma lem118804 (R : type1605) : (term27 R) = (term27 R).
Proof. exact (fun_ext (fun m : nat => @lem118803 R m)). Qed.
Lemma lem118805 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118806 (R : type1605) : (term2 R) = (term2 R).
Proof. exact (MK_COMB (@lem118805) (@lem118804 R)). Qed.
Lemma lem118823 (R : type1605) (m : nat) (d' : nat) : (term142 R m d') = (term142 R m d').
Proof. exact (eq_refl (term142 R m d')). Qed.
Lemma lem118824 (m : nat) (d' : nat) (R : type1605) : (term144 m d' R) = (term144 m d' R).
Proof. exact (MK_COMB (@lem118823 R m d') (@lem118806 R)). Qed.
Lemma lem118835 (R : type1605) (m : nat) (d' : nat) : (term60 R m d') = (term60 R m d').
Proof. exact (eq_refl (term60 R m d')). Qed.
Lemma lem118850 (R : type1605) (m : nat) (n : nat) : (term35 R m n) = (term35 R m n).
Proof. exact (eq_refl (term35 R m n)). Qed.
Lemma lem118851 (R : type1605) (m : nat) : (term45 R m) = (term45 R m).
Proof. exact (fun_ext (fun n : nat => @lem118850 R m n)). Qed.
Lemma lem118852 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118853 (R : type1605) (m : nat) : (term46 R m) = (term46 R m).
Proof. exact (MK_COMB (@lem118852) (@lem118851 R m)). Qed.
Lemma lem118854 (R : type1605) : (term54 R) = (term54 R).
Proof. exact (fun_ext (fun m : nat => @lem118853 R m)). Qed.
Lemma lem118855 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118856 (R : type1605) : (term55 R) = (term55 R).
Proof. exact (MK_COMB (@lem118855) (@lem118854 R)). Qed.
Lemma lem118857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem118858 (R : type1605) : (term76 R) = (term76 R).
Proof. exact (MK_COMB (@lem118857) (@lem118856 R)). Qed.
Lemma lem118859 (R : type1605) (m : nat) (d' : nat) : (term107 R m d') = (term107 R m d').
Proof. exact (MK_COMB (@lem118858 R) (@lem118835 R m d')). Qed.
Lemma lem118860 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem118861 (R : type1605) (m : nat) (d' : nat) : (term185 R m d') = (term185 R m d').
Proof. exact (MK_COMB (@lem118860) (@lem118859 R m d')). Qed.
Lemma lem118862 (m : nat) (d' : nat) (R : type1605) : (term187 m d' R) = (term187 m d' R).
Proof. exact (MK_COMB (@lem118861 R m d') (@lem118824 m d' R)). Qed.
Lemma lem118863 (m : nat) (d' : nat) (R : type1605) (h1 : term187 m d' R) : term187 m d' R.
Proof. exact (EQ_MP (@lem118862 m d' R) (@lem118730 m d' R h1)). Qed.
Lemma lem118864 (d : type1606) (h1 : term344 d) : term329 d.
Proof. exact (proj2 (@lem118791 d h1)). Qed.
Lemma lem118865 (d : type1606) (h1 : term344 d) : term258.
Proof. exact (proj1 (@lem118791 d h1)). Qed.
Lemma lem118866 (R : type1605) (m : nat) (d' : nat) (h1 : term107 R m d') : term107 R m d'.
Proof. exact (h1). Qed.
Lemma lem118867 (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : term144 m d' R.
Proof. exact (h1). Qed.
Lemma lem118869 (R : type1605) (m : nat) (d' : nat) (h1 : term107 R m d') : term55 R.
Proof. exact (proj1 (@lem118866 R m d' h1)). Qed.
Lemma lem118870 (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : term2 R.
Proof. exact (proj2 (@lem118867 m d' R h1)). Qed.
Lemma lem118871 (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : term34 R m d'.
Proof. exact (proj1 (@lem118867 m d' R h1)). Qed.
Lemma lem118875 {A : Type'} (P : Prop) (Q : A -> Prop) : (term350 A P Q) = (term351 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem118876 (P : Prop) (Q : nat -> Prop) : (term352 P Q) = (term353 P Q).
Proof. exact (@lem118875 nat P Q). Qed.
Lemma lem118877 (n : nat) (m : nat) : (term354 n m) = (term355 n m).
Proof. exact (@lem118876 (Peano.le m n) (term204 n m)). Qed.
Lemma lem118878 (n : nat) (m : nat) (d : nat) : (term356 n m d) = (term202 n m d).
Proof. exact (eq_refl (term356 n m d)). Qed.
Lemma lem118879 (n : nat) (m : nat) : (term357 n m) = (term204 n m).
Proof. exact (fun_ext (fun d : nat => @lem118878 n m d)). Qed.
Lemma lem118880 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118881 (n : nat) (m : nat) : (term358 n m) = (term205 n m).
Proof. exact (MK_COMB (@lem118880) (@lem118879 n m)). Qed.
Lemma lem118882 (m : nat) (n : nat) : (term208 m n) = (term208 m n).
Proof. exact (eq_refl (term208 m n)). Qed.
Lemma lem118883 (n : nat) (m : nat) : (term354 n m) = (term210 n m).
Proof. exact (MK_COMB (@lem118882 m n) (@lem118881 n m)). Qed.
Lemma lem118884 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem118885 (n : nat) (m : nat) : (term359 n m) = (term360 n m).
Proof. exact (MK_COMB (@lem118884) (@lem118883 n m)). Qed.
Lemma lem118886 (n : nat) (m : nat) (d : nat) : (term356 n m d) = (term202 n m d).
Proof. exact (eq_refl (term356 n m d)). Qed.
Lemma lem118887 (m : nat) (n : nat) : (term208 m n) = (term208 m n).
Proof. exact (eq_refl (term208 m n)). Qed.
Lemma lem118888 (n : nat) (m : nat) (d : nat) : (term361 n m d) = (term362 n m d).
Proof. exact (MK_COMB (@lem118887 m n) (@lem118886 n m d)). Qed.
Lemma lem118889 (n : nat) (m : nat) : (term363 n m) = (term364 n m).
Proof. exact (fun_ext (fun d : nat => @lem118888 n m d)). Qed.
Lemma lem118890 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118891 (n : nat) (m : nat) : (term355 n m) = (term365 n m).
Proof. exact (MK_COMB (@lem118890) (@lem118889 n m)). Qed.
Lemma lem118892 (n : nat) (m : nat) : ((term354 n m) = (term355 n m)) = ((term210 n m) = (term365 n m)).
Proof. exact (MK_COMB (@lem118885 n m) (@lem118891 n m)). Qed.
Lemma lem118893 (n : nat) (m : nat) : (term210 n m) = (term365 n m).
Proof. exact (EQ_MP (@lem118892 n m) (@lem118877 n m)). Qed.
Lemma lem118894 (m : nat) : (term225 m) = (term366 m).
Proof. exact (fun_ext (fun n : nat => @lem118893 n m)). Qed.
Lemma lem118895 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118896 (m : nat) : (term236 m) = (term367 m).
Proof. exact (MK_COMB (@lem118895) (@lem118894 m)). Qed.
Lemma lem118897 : term247 = term368.
Proof. exact (fun_ext (fun m : nat => @lem118896 m)). Qed.
Lemma lem118898 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118899 : term258 = term369.
Proof. exact (MK_COMB (@lem118898) (@lem118897)). Qed.
Lemma lem118906 (n : nat) (m : nat) (d : nat) : (term362 n m d) = (term362 n m d).
Proof. exact (eq_refl (term362 n m d)). Qed.
Lemma lem118907 (n : nat) (m : nat) : (term364 n m) = (term364 n m).
Proof. exact (fun_ext (fun d : nat => @lem118906 n m d)). Qed.
Lemma lem118908 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118909 (n : nat) (m : nat) : (term365 n m) = (term365 n m).
Proof. exact (MK_COMB (@lem118908) (@lem118907 n m)). Qed.
Lemma lem118910 (m : nat) : (term366 m) = (term366 m).
Proof. exact (fun_ext (fun n : nat => @lem118909 n m)). Qed.
Lemma lem118911 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118912 (m : nat) : (term367 m) = (term367 m).
Proof. exact (MK_COMB (@lem118911) (@lem118910 m)). Qed.
Lemma lem118913 : term368 = term368.
Proof. exact (fun_ext (fun m : nat => @lem118912 m)). Qed.
Lemma lem118914 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118915 : term369 = term369.
Proof. exact (MK_COMB (@lem118914) (@lem118913)). Qed.
Lemma lem118916 : term258 = term369.
Proof. exact (TRANS (@lem118899) (@lem118915)). Qed.
Lemma lem118917 (d : type1606) (h1 : term344 d) : term369.
Proof. exact (EQ_MP (@lem118916) (@lem118865 d h1)). Qed.
Lemma lem118941 (R : type1605) (m : nat) (n : nat) : (term35 R m n) = (term35 R m n).
Proof. exact (eq_refl (term35 R m n)). Qed.
Lemma lem118942 (R : type1605) (m : nat) : (term45 R m) = (term45 R m).
Proof. exact (fun_ext (fun n : nat => @lem118941 R m n)). Qed.
Lemma lem118943 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118944 (R : type1605) (m : nat) : (term46 R m) = (term46 R m).
Proof. exact (MK_COMB (@lem118943) (@lem118942 R m)). Qed.
Lemma lem118945 (R : type1605) : (term54 R) = (term54 R).
Proof. exact (fun_ext (fun m : nat => @lem118944 R m)). Qed.
Lemma lem118946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem118948 (R : type1605) : (term55 R) = (term55 R).
Proof. exact (MK_COMB (@lem118946) (@lem118945 R)). Qed.
Lemma lem118949 (R : type1605) (m : nat) (d' : nat) (h1 : term107 R m d') : term55 R.
Proof. exact (EQ_MP (@lem118948 R) (@lem118869 R m d' h1)). Qed.
Lemma lem119005 (d : type1606) (m : nat) (n : nat) : (term348 d m n) = (term348 d m n).
Proof. exact (eq_refl (term348 d m n)). Qed.
Lemma lem119006 (d : type1606) (m : nat) : (term349 d m) = (term349 d m).
Proof. exact (fun_ext (fun n : nat => @lem119005 d m n)). Qed.
Lemma lem119007 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem119008 (d : type1606) (m : nat) : (term325 d m) = (term325 d m).
Proof. exact (MK_COMB (@lem119007) (@lem119006 d m)). Qed.
Lemma lem119009 (d : type1606) : (term327 d) = (term327 d).
Proof. exact (fun_ext (fun m : nat => @lem119008 d m)). Qed.
Lemma lem119010 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem119012 (d : type1606) : (term329 d) = (term329 d).
Proof. exact (MK_COMB (@lem119010) (@lem119009 d)). Qed.
Lemma lem119013 (d : type1606) (h1 : term344 d) : term329 d.
Proof. exact (EQ_MP (@lem119012 d) (@lem118864 d h1)). Qed.
Lemma lem119015 (R : type1605) (m : nat) (d : nat) : (term24 R m d) = (term24 R m d).
Proof. exact (eq_refl (term24 R m d)). Qed.
Lemma lem119016 (R : type1605) (m : nat) : (term25 R m) = (term25 R m).
Proof. exact (fun_ext (fun d : nat => @lem119015 R m d)). Qed.
Lemma lem119017 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem119018 (R : type1605) (m : nat) : (term26 R m) = (term26 R m).
Proof. exact (MK_COMB (@lem119017) (@lem119016 R m)). Qed.
Lemma lem119019 (R : type1605) : (term27 R) = (term27 R).
Proof. exact (fun_ext (fun m : nat => @lem119018 R m)). Qed.
Lemma lem119020 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem119022 (R : type1605) : (term2 R) = (term2 R).
Proof. exact (MK_COMB (@lem119020) (@lem119019 R)). Qed.
Lemma lem119023 (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : term2 R.
Proof. exact (EQ_MP (@lem119022 R) (@lem118870 m d' R h1)). Qed.
Lemma lem119032 (_2482 : nat) (d : type1606) (h1 : term344 d) : term370 _2482.
Proof. exact (@lem118917 d h1 _2482). Qed.
Lemma lem119033 (_2482 : nat) : (term370 _2482) = (term367 _2482).
Proof. exact (eq_refl (term370 _2482)). Qed.
Lemma lem119034 (_2482 : nat) (d : type1606) (h1 : term344 d) : term367 _2482.
Proof. exact (EQ_MP (@lem119033 _2482) (@lem119032 _2482 d h1)). Qed.
Lemma lem119035 (_2482 : nat) (_2483 : nat) (d : type1606) (h1 : term344 d) : term371 _2482 _2483.
Proof. exact (@lem119034 _2482 d h1 _2483). Qed.
Lemma lem119036 (_2483 : nat) (_2482 : nat) : (term371 _2482 _2483) = (term365 _2483 _2482).
Proof. exact (eq_refl (term371 _2482 _2483)). Qed.
Lemma lem119037 (_2483 : nat) (_2482 : nat) (d : type1606) (h1 : term344 d) : term365 _2483 _2482.
Proof. exact (EQ_MP (@lem119036 _2483 _2482) (@lem119035 _2482 _2483 d h1)). Qed.
Lemma lem119038 (_2483 : nat) (_2482 : nat) (_2484 : nat) (d : type1606) (h1 : term344 d) : term372 _2483 _2482 _2484.
Proof. exact (@lem119037 _2483 _2482 d h1 _2484). Qed.
Lemma lem119039 (_2483 : nat) (_2482 : nat) (_2484 : nat) : (term372 _2483 _2482 _2484) = (term362 _2483 _2482 _2484).
Proof. exact (eq_refl (term372 _2483 _2482 _2484)). Qed.
Lemma lem119047 (_2487 : nat) (R : type1605) (m : nat) (d' : nat) (h1 : term107 R m d') : term373 R _2487.
Proof. exact (@lem118949 R m d' h1 _2487). Qed.
Lemma lem119048 (R : type1605) (_2487 : nat) : (term373 R _2487) = (term46 R _2487).
Proof. exact (eq_refl (term373 R _2487)). Qed.
Lemma lem119049 (_2487 : nat) (R : type1605) (m : nat) (d' : nat) (h1 : term107 R m d') : term46 R _2487.
Proof. exact (EQ_MP (@lem119048 R _2487) (@lem119047 _2487 R m d' h1)). Qed.
Lemma lem119050 (_2487 : nat) (_2488 : nat) (R : type1605) (m : nat) (d' : nat) (h1 : term107 R m d') : term374 R _2487 _2488.
Proof. exact (@lem119049 _2487 R m d' h1 _2488). Qed.
Lemma lem119051 (R : type1605) (_2487 : nat) (_2488 : nat) : (term374 R _2487 _2488) = (term35 R _2487 _2488).
Proof. exact (eq_refl (term374 R _2487 _2488)). Qed.
Lemma lem119062 (_2492 : nat) (d : type1606) (h1 : term344 d) : term375 d _2492.
Proof. exact (@lem119013 d h1 _2492). Qed.
Lemma lem119063 (d : type1606) (_2492 : nat) : (term375 d _2492) = (term325 d _2492).
Proof. exact (eq_refl (term375 d _2492)). Qed.
Lemma lem119064 (_2492 : nat) (d : type1606) (h1 : term344 d) : term325 d _2492.
Proof. exact (EQ_MP (@lem119063 d _2492) (@lem119062 _2492 d h1)). Qed.
Lemma lem119065 (_2492 : nat) (_2493 : nat) (d : type1606) (h1 : term344 d) : term376 d _2492 _2493.
Proof. exact (@lem119064 _2492 d h1 _2493). Qed.
Lemma lem119066 (d : type1606) (_2492 : nat) (_2493 : nat) : (term376 d _2492 _2493) = (term348 d _2492 _2493).
Proof. exact (eq_refl (term376 d _2492 _2493)). Qed.
Lemma lem119068 (_2494 : nat) (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : term66 R _2494.
Proof. exact (@lem119023 m d' R h1 _2494). Qed.
Lemma lem119069 (R : type1605) (_2494 : nat) : (term66 R _2494) = (term26 R _2494).
Proof. exact (eq_refl (term66 R _2494)). Qed.
Lemma lem119070 (_2494 : nat) (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : term26 R _2494.
Proof. exact (EQ_MP (@lem119069 R _2494) (@lem119068 _2494 m d' R h1)). Qed.
Lemma lem119071 (_2494 : nat) (_2495 : nat) (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : term58 R _2494 _2495.
Proof. exact (@lem119070 _2494 m d' R h1 _2495). Qed.
Lemma lem119072 (R : type1605) (_2494 : nat) (_2495 : nat) : (term58 R _2494 _2495) = (term24 R _2494 _2495).
Proof. exact (eq_refl (term58 R _2494 _2495)). Qed.
Lemma lem119079 (_2483 : nat) (_2482 : nat) (_2484 : nat) (d : type1606) (h1 : term344 d) : term362 _2483 _2482 _2484.
Proof. exact (EQ_MP (@lem119039 _2483 _2482 _2484) (@lem119038 _2483 _2482 _2484 d h1)). Qed.
Lemma lem119091 (_2487 : nat) (_2488 : nat) (R : type1605) (m : nat) (d' : nat) (h1 : term107 R m d') : term35 R _2487 _2488.
Proof. exact (EQ_MP (@lem119051 R _2487 _2488) (@lem119050 _2487 _2488 R m d' h1)). Qed.
Lemma lem119093 (R : type1605) (m : nat) (d' : nat) (h1 : term107 R m d') : term60 R m d'.
Proof. exact (proj2 (@lem118866 R m d' h1)). Qed.
Lemma lem119105 (_2492 : nat) (_2493 : nat) (d : type1606) (h1 : term344 d) : term348 d _2492 _2493.
Proof. exact (EQ_MP (@lem119066 d _2492 _2493) (@lem119065 _2492 _2493 d h1)). Qed.
Lemma lem119111 (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : term377 R m d'.
Proof. exact (proj2 (@lem118871 m d' R h1)). Qed.
Lemma lem119183 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem119184 (m : nat) (d' : nat) : (Nat.add m d') = (Nat.add m d').
Proof. exact (@lem119183 (Nat.add m d')). Qed.
Lemma lem119185 (m : nat) (d' : nat) : term378 m d'.
Proof. exact (fun h0 : term379 m d' => @lem119184 m d'). Qed.
Lemma lem119187 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem119188 (m : nat) (d' : nat) : (term378 m d') = ((Nat.add m d') = (Nat.add m d')).
Proof. exact (@lem119187 ((Nat.add m d') = (Nat.add m d'))). Qed.
Lemma lem119189 (m : nat) (d' : nat) : (Nat.add m d') = (Nat.add m d').
Proof. exact (EQ_MP (@lem119188 m d') (@lem119185 m d')). Qed.
Lemma lem119191 (b : Prop) (a : Prop) : (a \/ b) = (term381 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem119192 (_2484 : nat) (_2482 : nat) (_2483 : nat) : (term362 _2483 _2482 _2484) = (term382 _2484 _2482 _2483).
Proof. exact (@lem119191 (term202 _2483 _2482 _2484) (Peano.le _2482 _2483)). Qed.
Lemma lem119194 (a : Prop) : (term383 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem119195 (_2483 : nat) (_2482 : nat) (_2484 : nat) : (term384 _2483 _2482 _2484) = (_2483 = (Nat.add _2482 _2484)).
Proof. exact (@lem119194 (_2483 = (Nat.add _2482 _2484))). Qed.
Lemma lem119196 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem119197 (_2483 : nat) (_2482 : nat) (_2484 : nat) : (term385 _2483 _2482 _2484) = (term386 _2483 _2482 _2484).
Proof. exact (MK_COMB (@lem119196) (@lem119195 _2483 _2482 _2484)). Qed.
Lemma lem119198 (_2482 : nat) (_2483 : nat) : (Peano.le _2482 _2483) = (Peano.le _2482 _2483).
Proof. exact (eq_refl (Peano.le _2482 _2483)). Qed.
Lemma lem119199 (_2484 : nat) (_2482 : nat) (_2483 : nat) : (term382 _2484 _2482 _2483) = (term387 _2484 _2482 _2483).
Proof. exact (MK_COMB (@lem119197 _2483 _2482 _2484) (@lem119198 _2482 _2483)). Qed.
Lemma lem119200 (_2484 : nat) (_2482 : nat) (_2483 : nat) : (term362 _2483 _2482 _2484) = (term387 _2484 _2482 _2483).
Proof. exact (TRANS (@lem119192 _2484 _2482 _2483) (@lem119199 _2484 _2482 _2483)). Qed.
Lemma lem119203 (_2484 : nat) (_2482 : nat) (_2483 : nat) (d : type1606) (h1 : term344 d) : term387 _2484 _2482 _2483.
Proof. exact (EQ_MP (@lem119200 _2484 _2482 _2483) (@lem119079 _2483 _2482 _2484 d h1)). Qed.
Lemma lem119204 (m : nat) (d' : nat) (d : type1606) (h1 : term344 d) : term388 m d'.
Proof. exact (@lem119203 d' m (Nat.add m d') d h1). Qed.
Lemma lem119207 (m : nat) (d' : nat) (d : type1606) (h1 : term344 d) : term389 m d'.
Proof. exact (@lem119204 m d' d h1 (@lem119189 m d')). Qed.
Lemma lem119208 (m : nat) (d' : nat) (d : type1606) (h1 : term344 d) : term390 m d'.
Proof. exact (fun h0 : term391 m d' => @lem119207 m d' d h1). Qed.
Lemma lem119210 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem119211 (m : nat) (d' : nat) : (term390 m d') = (term389 m d').
Proof. exact (@lem119210 (term389 m d')). Qed.
Lemma lem119212 (m : nat) (d' : nat) (d : type1606) (h1 : term344 d) : term389 m d'.
Proof. exact (EQ_MP (@lem119211 m d') (@lem119208 m d' d h1)). Qed.
Lemma lem119218 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem119219 (R : type1605) (_2487 : nat) (_2488 : nat) : (term35 R _2487 _2488) = (term392 R _2487 _2488).
Proof. exact (@lem119218 (R _2487 _2488) (term271 _2487 _2488)). Qed.
Lemma lem119225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem119226 (R : type1605) (_2487 : nat) (_2488 : nat) : (term393 R _2487 _2488) = (term394 R _2487 _2488).
Proof. exact (MK_COMB (@lem119225) (@lem119219 R _2487 _2488)). Qed.
Lemma lem119232 (R : type1605) (_2487 : nat) (_2488 : nat) : (term392 R _2487 _2488) = (term392 R _2487 _2488).
Proof. exact (eq_refl (term392 R _2487 _2488)). Qed.
Lemma lem119233 (R : type1605) (_2487 : nat) (_2488 : nat) : ((term35 R _2487 _2488) = (term392 R _2487 _2488)) = ((term392 R _2487 _2488) = (term392 R _2487 _2488)).
Proof. exact (MK_COMB (@lem119226 R _2487 _2488) (@lem119232 R _2487 _2488)). Qed.
Lemma lem119235 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem119236 (x : Prop) : (x = x) = True.
Proof. exact (@lem119235 Prop x). Qed.
Lemma lem119237 (R : type1605) (_2487 : nat) (_2488 : nat) : ((term392 R _2487 _2488) = (term392 R _2487 _2488)) = True.
Proof. exact (@lem119236 (term392 R _2487 _2488)). Qed.
Lemma lem119238 (R : type1605) (_2487 : nat) (_2488 : nat) : ((term35 R _2487 _2488) = (term392 R _2487 _2488)) = True.
Proof. exact (TRANS (@lem119233 R _2487 _2488) (@lem119237 R _2487 _2488)). Qed.
Lemma lem119239 (R : type1605) (_2487 : nat) (_2488 : nat) : True = ((term35 R _2487 _2488) = (term392 R _2487 _2488)).
Proof. exact (SYM (@lem119238 R _2487 _2488)). Qed.
Lemma lem119240 (R : type1605) (_2487 : nat) (_2488 : nat) : (term35 R _2487 _2488) = (term392 R _2487 _2488).
Proof. exact (EQ_MP (@lem119239 R _2487 _2488) (@lem0)). Qed.
Lemma lem119241 (_2487 : nat) (_2488 : nat) (R : type1605) (m : nat) (d' : nat) (h1 : term107 R m d') : term392 R _2487 _2488.
Proof. exact (EQ_MP (@lem119240 R _2487 _2488) (@lem119091 _2487 _2488 R m d' h1)). Qed.
Lemma lem119243 (b : Prop) (a : Prop) : (a \/ b) = (term381 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem119244 (R : type1605) (_2487 : nat) (_2488 : nat) : (term392 R _2487 _2488) = (term395 R _2487 _2488).
Proof. exact (@lem119243 (term271 _2487 _2488) (R _2487 _2488)). Qed.
Lemma lem119246 (a : Prop) : (term383 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem119247 (_2487 : nat) (_2488 : nat) : (term396 _2487 _2488) = (Peano.le _2487 _2488).
Proof. exact (@lem119246 (Peano.le _2487 _2488)). Qed.
Lemma lem119248 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem119249 (_2487 : nat) (_2488 : nat) : (term397 _2487 _2488) = (term398 _2487 _2488).
Proof. exact (MK_COMB (@lem119248) (@lem119247 _2487 _2488)). Qed.
Lemma lem119250 (R : type1605) (_2487 : nat) (_2488 : nat) : (R _2487 _2488) = (R _2487 _2488).
Proof. exact (eq_refl (R _2487 _2488)). Qed.
Lemma lem119251 (R : type1605) (_2487 : nat) (_2488 : nat) : (term395 R _2487 _2488) = (term28 R _2487 _2488).
Proof. exact (MK_COMB (@lem119249 _2487 _2488) (@lem119250 R _2487 _2488)). Qed.
Lemma lem119252 (R : type1605) (_2487 : nat) (_2488 : nat) : (term392 R _2487 _2488) = (term28 R _2487 _2488).
Proof. exact (TRANS (@lem119244 R _2487 _2488) (@lem119251 R _2487 _2488)). Qed.
Lemma lem119255 (_2487 : nat) (_2488 : nat) (R : type1605) (m : nat) (d' : nat) (h1 : term107 R m d') : term28 R _2487 _2488.
Proof. exact (EQ_MP (@lem119252 R _2487 _2488) (@lem119241 _2487 _2488 R m d' h1)). Qed.
Lemma lem119256 (R : type1605) (m : nat) (d' : nat) (h1 : term107 R m d') : term399 R m d'.
Proof. exact (@lem119255 m (Nat.add m d') R m d' h1). Qed.
Lemma lem119259 (R : type1605) (m : nat) (d' : nat) (d : type1606) (h1 : term107 R m d') (h2 : term344 d) : term24 R m d'.
Proof. exact (@lem119256 R m d' h1 (@lem119212 m d' d h2)). Qed.
Lemma lem119260 (R : type1605) (m : nat) (d' : nat) (d : type1606) (h1 : term107 R m d') (h2 : term344 d) : term400 R m d'.
Proof. exact (fun h0 : term60 R m d' => @lem119259 R m d' d h1 h2). Qed.
Lemma lem119262 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem119263 (R : type1605) (m : nat) (d' : nat) : (term400 R m d') = (term24 R m d').
Proof. exact (@lem119262 (term24 R m d')). Qed.
Lemma lem119264 (R : type1605) (m : nat) (d' : nat) (d : type1606) (h1 : term107 R m d') (h2 : term344 d) : term24 R m d'.
Proof. exact (EQ_MP (@lem119263 R m d') (@lem119260 R m d' d h1 h2)). Qed.
Lemma lem119267 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem119269 (R : type1605) (m : nat) (d' : nat) : (term60 R m d') = (term401 R m d').
Proof. exact (@lem119267 (term24 R m d')). Qed.
Lemma lem119272 (R : type1605) (m : nat) (d' : nat) (h1 : term107 R m d') : term401 R m d'.
Proof. exact (EQ_MP (@lem119269 R m d') (@lem119093 R m d' h1)). Qed.
Lemma lem119275 (R : type1605) (m : nat) (d' : nat) (d : type1606) (h1 : term107 R m d') (h2 : term344 d) : False.
Proof. exact (@lem119272 R m d' h1 (@lem119264 R m d' d h1 h2)). Qed.
Lemma lem119276 (R : type1605) (m : nat) (d' : nat) (d : type1606) (h1 : term107 R m d') (h2 : term344 d) : term402.
Proof. exact (fun h0 : ~ False => @lem119275 R m d' d h1 h2). Qed.
Lemma lem119278 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem119279 : term402 = False.
Proof. exact (@lem119278 False). Qed.
Lemma lem119280 (R : type1605) (m : nat) (d' : nat) (d : type1606) (h1 : term107 R m d') (h2 : term344 d) : False.
Proof. exact (EQ_MP (@lem119279) (@lem119276 R m d' d h1 h2)). Qed.
Lemma lem119281 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem119282 (_2512 : nat) (_2514 : nat) (h1 : _2512 = _2514) : _2512 = _2514.
Proof. exact (h1). Qed.
Lemma lem119283 (_2513 : nat) (_2515 : nat) (h1 : _2513 = _2515) : _2513 = _2515.
Proof. exact (h1). Qed.
Lemma lem119284 (R : type1605) (_2512 : nat) (_2514 : nat) (h1 : _2512 = _2514) : (R _2512) = (R _2514).
Proof. exact (MK_COMB (@lem119281 R) (@lem119282 _2512 _2514 h1)). Qed.
Lemma lem119285 (R : type1605) (_2512 : nat) (_2514 : nat) (_2513 : nat) (_2515 : nat) (h1 : _2512 = _2514) (h2 : _2513 = _2515) : (R _2512 _2513) = (R _2514 _2515).
Proof. exact (MK_COMB (@lem119284 R _2512 _2514 h1) (@lem119283 _2513 _2515 h2)). Qed.
Lemma lem119287 (b : Prop) (a : Prop) : term403 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem119288 (_2514 : nat) (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : term404 _2514 _2515 R _2512 _2513.
Proof. exact (@lem119287 (R _2514 _2515) (R _2512 _2513)). Qed.
Lemma lem119289 (R : type1605) (_2512 : nat) (_2514 : nat) (_2513 : nat) (_2515 : nat) (h1 : _2512 = _2514) (h2 : _2513 = _2515) : term405 _2514 _2515 R _2512 _2513.
Proof. exact (@lem119288 _2514 _2515 R _2512 _2513 (@lem119285 R _2512 _2514 _2513 _2515 h1 h2)). Qed.
Lemma lem119290 (_2515 : nat) (R : type1605) (_2513 : nat) (_2512 : nat) (_2514 : nat) (h1 : _2512 = _2514) : term406 _2514 _2515 R _2512 _2513.
Proof. exact (fun h0 : _2513 = _2515 => @lem119289 R _2512 _2514 _2513 _2515 h1 h0). Qed.
Lemma lem119292 (a : Prop) (b : Prop) : (a -> b) = (term407 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem119293 (_2514 : nat) (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : (term406 _2514 _2515 R _2512 _2513) = (term408 _2514 _2515 R _2512 _2513).
Proof. exact (@lem119292 (_2513 = _2515) (term405 _2514 _2515 R _2512 _2513)). Qed.
Lemma lem119294 (_2515 : nat) (R : type1605) (_2513 : nat) (_2512 : nat) (_2514 : nat) (h1 : _2512 = _2514) : term408 _2514 _2515 R _2512 _2513.
Proof. exact (EQ_MP (@lem119293 _2514 _2515 R _2512 _2513) (@lem119290 _2515 R _2513 _2512 _2514 h1)). Qed.
Lemma lem119295 (_2514 : nat) (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : term409 _2514 _2515 R _2512 _2513.
Proof. exact (fun h0 : _2512 = _2514 => @lem119294 _2515 R _2513 _2512 _2514 h0). Qed.
Lemma lem119297 (a : Prop) (b : Prop) : (a -> b) = (term407 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem119298 (_2514 : nat) (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : (term409 _2514 _2515 R _2512 _2513) = (term410 _2514 _2515 R _2512 _2513).
Proof. exact (@lem119297 (_2512 = _2514) (term408 _2514 _2515 R _2512 _2513)). Qed.
Lemma lem119299 (_2514 : nat) (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : term410 _2514 _2515 R _2512 _2513.
Proof. exact (EQ_MP (@lem119298 _2514 _2515 R _2512 _2513) (@lem119295 _2514 _2515 R _2512 _2513)). Qed.
Lemma lem119350 (x : nat) (y : nat) (z : nat) : term411 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem119352 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem119353 (m : nat) : m = m.
Proof. exact (@lem119352 m). Qed.
Lemma lem119354 (m : nat) : term412 m.
Proof. exact (fun h0 : term413 m => @lem119353 m). Qed.
Lemma lem119356 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem119357 (m : nat) : (term412 m) = (m = m).
Proof. exact (@lem119356 (m = m)). Qed.
Lemma lem119358 (m : nat) : m = m.
Proof. exact (EQ_MP (@lem119357 m) (@lem119354 m)). Qed.
Lemma lem119360 (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : Peano.le m d'.
Proof. exact (proj1 (@lem118871 m d' R h1)). Qed.
Lemma lem119361 (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : term414 m d'.
Proof. exact (fun h0 : term271 m d' => @lem119360 m d' R h1). Qed.
Lemma lem119363 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem119364 (m : nat) (d' : nat) : (term414 m d') = (Peano.le m d').
Proof. exact (@lem119363 (Peano.le m d')). Qed.
Lemma lem119365 (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : Peano.le m d'.
Proof. exact (EQ_MP (@lem119364 m d') (@lem119361 m d' R h1)). Qed.
Lemma lem119371 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem119372 (d : type1606) (_2492 : nat) (_2493 : nat) : (term348 d _2492 _2493) = (term415 d _2492 _2493).
Proof. exact (@lem119371 (_2493 = (term416 d _2492 _2493)) (term271 _2492 _2493)). Qed.
Lemma lem119380 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem119381 (d : type1606) (_2492 : nat) (_2493 : nat) : (term417 d _2492 _2493) = (term418 d _2492 _2493).
Proof. exact (MK_COMB (@lem119380) (@lem119372 d _2492 _2493)). Qed.
Lemma lem119389 (d : type1606) (_2492 : nat) (_2493 : nat) : (term415 d _2492 _2493) = (term415 d _2492 _2493).
Proof. exact (eq_refl (term415 d _2492 _2493)). Qed.
Lemma lem119390 (d : type1606) (_2492 : nat) (_2493 : nat) : ((term348 d _2492 _2493) = (term415 d _2492 _2493)) = ((term415 d _2492 _2493) = (term415 d _2492 _2493)).
Proof. exact (MK_COMB (@lem119381 d _2492 _2493) (@lem119389 d _2492 _2493)). Qed.
Lemma lem119392 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem119393 (x : Prop) : (x = x) = True.
Proof. exact (@lem119392 Prop x). Qed.
Lemma lem119394 (d : type1606) (_2492 : nat) (_2493 : nat) : ((term415 d _2492 _2493) = (term415 d _2492 _2493)) = True.
Proof. exact (@lem119393 (term415 d _2492 _2493)). Qed.
Lemma lem119395 (d : type1606) (_2492 : nat) (_2493 : nat) : ((term348 d _2492 _2493) = (term415 d _2492 _2493)) = True.
Proof. exact (TRANS (@lem119390 d _2492 _2493) (@lem119394 d _2492 _2493)). Qed.
Lemma lem119396 (d : type1606) (_2492 : nat) (_2493 : nat) : True = ((term348 d _2492 _2493) = (term415 d _2492 _2493)).
Proof. exact (SYM (@lem119395 d _2492 _2493)). Qed.
Lemma lem119397 (d : type1606) (_2492 : nat) (_2493 : nat) : (term348 d _2492 _2493) = (term415 d _2492 _2493).
Proof. exact (EQ_MP (@lem119396 d _2492 _2493) (@lem0)). Qed.
Lemma lem119398 (_2492 : nat) (_2493 : nat) (d : type1606) (h1 : term344 d) : term415 d _2492 _2493.
Proof. exact (EQ_MP (@lem119397 d _2492 _2493) (@lem119105 _2492 _2493 d h1)). Qed.
Lemma lem119400 (b : Prop) (a : Prop) : (a \/ b) = (term381 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem119401 (d : type1606) (_2492 : nat) (_2493 : nat) : (term415 d _2492 _2493) = (term419 d _2492 _2493).
Proof. exact (@lem119400 (term271 _2492 _2493) (_2493 = (term416 d _2492 _2493))). Qed.
Lemma lem119403 (a : Prop) : (term383 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem119404 (_2492 : nat) (_2493 : nat) : (term396 _2492 _2493) = (Peano.le _2492 _2493).
Proof. exact (@lem119403 (Peano.le _2492 _2493)). Qed.
Lemma lem119405 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem119406 (_2492 : nat) (_2493 : nat) : (term397 _2492 _2493) = (term398 _2492 _2493).
Proof. exact (MK_COMB (@lem119405) (@lem119404 _2492 _2493)). Qed.
Lemma lem119407 (d : type1606) (_2492 : nat) (_2493 : nat) : (_2493 = (term416 d _2492 _2493)) = (_2493 = (term416 d _2492 _2493)).
Proof. exact (eq_refl (_2493 = (term416 d _2492 _2493))). Qed.
Lemma lem119408 (d : type1606) (_2492 : nat) (_2493 : nat) : (term419 d _2492 _2493) = (term420 d _2492 _2493).
Proof. exact (MK_COMB (@lem119406 _2492 _2493) (@lem119407 d _2492 _2493)). Qed.
Lemma lem119409 (d : type1606) (_2492 : nat) (_2493 : nat) : (term415 d _2492 _2493) = (term420 d _2492 _2493).
Proof. exact (TRANS (@lem119401 d _2492 _2493) (@lem119408 d _2492 _2493)). Qed.
Lemma lem119412 (_2492 : nat) (_2493 : nat) (d : type1606) (h1 : term344 d) : term420 d _2492 _2493.
Proof. exact (EQ_MP (@lem119409 d _2492 _2493) (@lem119398 _2492 _2493 d h1)). Qed.
Lemma lem119413 (m : nat) (d' : nat) (d : type1606) (h1 : term344 d) : term420 d m d'.
Proof. exact (@lem119412 m d' d h1). Qed.
Lemma lem119416 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term144 m d' R) : d' = (term416 d m d').
Proof. exact (@lem119413 m d' d h1 (@lem119365 m d' R h2)). Qed.
Lemma lem119417 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term144 m d' R) : term421 d m d'.
Proof. exact (fun h0 : term422 d m d' => @lem119416 d m d' R h1 h2). Qed.
Lemma lem119419 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem119420 (d : type1606) (m : nat) (d' : nat) : (term421 d m d') = (d' = (term416 d m d')).
Proof. exact (@lem119419 (d' = (term416 d m d'))). Qed.
Lemma lem119421 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term144 m d' R) : d' = (term416 d m d').
Proof. exact (EQ_MP (@lem119420 d m d') (@lem119417 d m d' R h1 h2)). Qed.
Lemma lem119423 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem119424 (d' : nat) : d' = d'.
Proof. exact (@lem119423 d'). Qed.
Lemma lem119425 (d' : nat) : term412 d'.
Proof. exact (fun h0 : term413 d' => @lem119424 d'). Qed.
Lemma lem119427 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem119428 (d' : nat) : (term412 d') = (d' = d').
Proof. exact (@lem119427 (d' = d')). Qed.
Lemma lem119429 (d' : nat) : d' = d'.
Proof. exact (EQ_MP (@lem119428 d') (@lem119425 d')). Qed.
Lemma lem119447 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem119448 (y : nat) (x : nat) (z : nat) : (term423 x y z) = (term424 y x z).
Proof. exact (@lem119447 (y = z) (term425 x z)). Qed.
Lemma lem119458 (x : nat) (y : nat) : (term426 x y) = (term426 x y).
Proof. exact (eq_refl (term426 x y)). Qed.
Lemma lem119459 (y : nat) (x : nat) (z : nat) : (term411 x y z) = (term427 y x z).
Proof. exact (MK_COMB (@lem119458 x y) (@lem119448 y x z)). Qed.
Lemma lem119463 (q : Prop) (p : Prop) (r : Prop) : (term428 p q r) = (term428 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem119464 (y : nat) (x : nat) (z : nat) : (term427 y x z) = (term429 y x z).
Proof. exact (@lem119463 (y = z) (term425 x y) (term425 x z)). Qed.
Lemma lem119486 (y : nat) (x : nat) (z : nat) : (term411 x y z) = (term429 y x z).
Proof. exact (TRANS (@lem119459 y x z) (@lem119464 y x z)). Qed.
Lemma lem119487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem119488 (y : nat) (x : nat) (z : nat) : (term430 x y z) = (term431 y x z).
Proof. exact (MK_COMB (@lem119487) (@lem119486 y x z)). Qed.
Lemma lem119510 (y : nat) (x : nat) (z : nat) : (term429 y x z) = (term429 y x z).
Proof. exact (eq_refl (term429 y x z)). Qed.
Lemma lem119511 (y : nat) (x : nat) (z : nat) : ((term411 x y z) = (term429 y x z)) = ((term429 y x z) = (term429 y x z)).
Proof. exact (MK_COMB (@lem119488 y x z) (@lem119510 y x z)). Qed.
Lemma lem119513 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem119514 (x : Prop) : (x = x) = True.
Proof. exact (@lem119513 Prop x). Qed.
Lemma lem119515 (y : nat) (x : nat) (z : nat) : ((term429 y x z) = (term429 y x z)) = True.
Proof. exact (@lem119514 (term429 y x z)). Qed.
Lemma lem119516 (y : nat) (x : nat) (z : nat) : ((term411 x y z) = (term429 y x z)) = True.
Proof. exact (TRANS (@lem119511 y x z) (@lem119515 y x z)). Qed.
Lemma lem119517 (y : nat) (x : nat) (z : nat) : True = ((term411 x y z) = (term429 y x z)).
Proof. exact (SYM (@lem119516 y x z)). Qed.
Lemma lem119518 (y : nat) (x : nat) (z : nat) : (term411 x y z) = (term429 y x z).
Proof. exact (EQ_MP (@lem119517 y x z) (@lem0)). Qed.
Lemma lem119519 (y : nat) (x : nat) (z : nat) : term429 y x z.
Proof. exact (EQ_MP (@lem119518 y x z) (@lem119350 x y z)). Qed.
Lemma lem119521 (b : Prop) (a : Prop) : (a \/ b) = (term381 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem119522 (x : nat) (y : nat) (z : nat) : (term429 y x z) = (term432 x y z).
Proof. exact (@lem119521 (term433 y x z) (y = z)). Qed.
Lemma lem119524 (a : Prop) (b : Prop) : (term434 a b) = (term435 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem119525 (y : nat) (x : nat) (z : nat) : (term436 y x z) = (term437 y x z).
Proof. exact (@lem119524 (term425 x y) (term425 x z)). Qed.
Lemma lem119527 (a : Prop) : (term383 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem119528 (x : nat) (y : nat) : (term438 x y) = (x = y).
Proof. exact (@lem119527 (x = y)). Qed.
Lemma lem119529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem119530 (x : nat) (y : nat) : (term439 x y) = (term440 x y).
Proof. exact (MK_COMB (@lem119529) (@lem119528 x y)). Qed.
Lemma lem119532 (a : Prop) : (term383 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem119533 (x : nat) (z : nat) : (term438 x z) = (x = z).
Proof. exact (@lem119532 (x = z)). Qed.
Lemma lem119534 (y : nat) (x : nat) (z : nat) : (term437 y x z) = (term441 y x z).
Proof. exact (MK_COMB (@lem119530 x y) (@lem119533 x z)). Qed.
Lemma lem119535 (y : nat) (x : nat) (z : nat) : (term436 y x z) = (term441 y x z).
Proof. exact (TRANS (@lem119525 y x z) (@lem119534 y x z)). Qed.
Lemma lem119536 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem119537 (y : nat) (x : nat) (z : nat) : (term442 y x z) = (term443 y x z).
Proof. exact (MK_COMB (@lem119536) (@lem119535 y x z)). Qed.
Lemma lem119538 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem119539 (x : nat) (y : nat) (z : nat) : (term432 x y z) = (term444 x y z).
Proof. exact (MK_COMB (@lem119537 y x z) (@lem119538 y z)). Qed.
Lemma lem119540 (x : nat) (y : nat) (z : nat) : (term429 y x z) = (term444 x y z).
Proof. exact (TRANS (@lem119522 x y z) (@lem119539 x y z)). Qed.
Lemma lem119542 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term144 m d' R) : term445 d m d'.
Proof. exact (conj (@lem119421 d m d' R h1 h2) (@lem119429 d')). Qed.
Lemma lem119544 (x : nat) (y : nat) (z : nat) : term444 x y z.
Proof. exact (EQ_MP (@lem119540 x y z) (@lem119519 y x z)). Qed.
Lemma lem119545 (d : type1606) (m : nat) (d' : nat) : term446 d m d'.
Proof. exact (@lem119544 d' (term416 d m d') d'). Qed.
Lemma lem119548 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term144 m d' R) : (term416 d m d') = d'.
Proof. exact (@lem119545 d m d' (@lem119542 d m d' R h1 h2)). Qed.
Lemma lem119549 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term144 m d' R) : term447 d m d'.
Proof. exact (fun h0 : term448 d m d' => @lem119548 d m d' R h1 h2). Qed.
Lemma lem119551 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem119552 (d : type1606) (m : nat) (d' : nat) : (term447 d m d') = ((term416 d m d') = d').
Proof. exact (@lem119551 ((term416 d m d') = d')). Qed.
Lemma lem119553 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term144 m d' R) : (term416 d m d') = d'.
Proof. exact (EQ_MP (@lem119552 d m d') (@lem119549 d m d' R h1 h2)). Qed.
Lemma lem119555 (_2494 : nat) (_2495 : nat) (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : term24 R _2494 _2495.
Proof. exact (EQ_MP (@lem119072 R _2494 _2495) (@lem119071 _2494 _2495 m d' R h1)). Qed.
Lemma lem119556 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : term449 R d m d'.
Proof. exact (@lem119555 m (d m d') m d' R h1). Qed.
Lemma lem119557 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : term450 R d m d'.
Proof. exact (fun h0 : term451 R d m d' => @lem119556 d m d' R h1). Qed.
Lemma lem119559 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem119560 (R : type1605) (d : type1606) (m : nat) (d' : nat) : (term450 R d m d') = (term449 R d m d').
Proof. exact (@lem119559 (term449 R d m d')). Qed.
Lemma lem119561 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : term449 R d m d'.
Proof. exact (EQ_MP (@lem119560 R d m d') (@lem119557 d m d' R h1)). Qed.
Lemma lem119579 (q : Prop) (p : Prop) (r : Prop) : (term428 p q r) = (term428 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem119580 (_2514 : nat) (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : (term408 _2514 _2515 R _2512 _2513) = (term452 _2514 _2515 R _2512 _2513).
Proof. exact (@lem119579 (R _2514 _2515) (term425 _2513 _2515) (term377 R _2512 _2513)). Qed.
Lemma lem119594 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem119595 (R : type1605) (_2512 : nat) (_2513 : nat) (_2515 : nat) : (term453 _2515 R _2512 _2513) = (term454 R _2512 _2513 _2515).
Proof. exact (@lem119594 (term377 R _2512 _2513) (term425 _2513 _2515)). Qed.
Lemma lem119603 (R : type1605) (_2514 : nat) (_2515 : nat) : (term455 R _2514 _2515) = (term455 R _2514 _2515).
Proof. exact (eq_refl (term455 R _2514 _2515)). Qed.
Lemma lem119604 (_2514 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) (_2515 : nat) : (term452 _2514 _2515 R _2512 _2513) = (term456 _2514 R _2512 _2513 _2515).
Proof. exact (MK_COMB (@lem119603 R _2514 _2515) (@lem119595 R _2512 _2513 _2515)). Qed.
Lemma lem119615 (_2514 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) (_2515 : nat) : (term408 _2514 _2515 R _2512 _2513) = (term456 _2514 R _2512 _2513 _2515).
Proof. exact (TRANS (@lem119580 _2514 _2515 R _2512 _2513) (@lem119604 _2514 R _2512 _2513 _2515)). Qed.
Lemma lem119616 (_2512 : nat) (_2514 : nat) : (term426 _2512 _2514) = (term426 _2512 _2514).
Proof. exact (eq_refl (term426 _2512 _2514)). Qed.
Lemma lem119617 (_2514 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) (_2515 : nat) : (term410 _2514 _2515 R _2512 _2513) = (term457 _2514 R _2512 _2513 _2515).
Proof. exact (MK_COMB (@lem119616 _2512 _2514) (@lem119615 _2514 R _2512 _2513 _2515)). Qed.
Lemma lem119621 (q : Prop) (p : Prop) (r : Prop) : (term428 p q r) = (term428 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem119622 (_2514 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) (_2515 : nat) : (term457 _2514 R _2512 _2513 _2515) = (term458 _2514 R _2512 _2513 _2515).
Proof. exact (@lem119621 (R _2514 _2515) (term425 _2512 _2514) (term454 R _2512 _2513 _2515)). Qed.
Lemma lem119636 (q : Prop) (p : Prop) (r : Prop) : (term428 p q r) = (term428 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem119637 (R : type1605) (_2512 : nat) (_2514 : nat) (_2513 : nat) (_2515 : nat) : (term459 _2514 R _2512 _2513 _2515) = (term460 R _2512 _2514 _2513 _2515).
Proof. exact (@lem119636 (term377 R _2512 _2513) (term425 _2512 _2514) (term425 _2513 _2515)). Qed.
Lemma lem119657 (R : type1605) (_2514 : nat) (_2515 : nat) : (term455 R _2514 _2515) = (term455 R _2514 _2515).
Proof. exact (eq_refl (term455 R _2514 _2515)). Qed.
Lemma lem119658 (R : type1605) (_2512 : nat) (_2514 : nat) (_2513 : nat) (_2515 : nat) : (term458 _2514 R _2512 _2513 _2515) = (term461 R _2512 _2514 _2513 _2515).
Proof. exact (MK_COMB (@lem119657 R _2514 _2515) (@lem119637 R _2512 _2514 _2513 _2515)). Qed.
Lemma lem119669 (R : type1605) (_2512 : nat) (_2514 : nat) (_2513 : nat) (_2515 : nat) : (term457 _2514 R _2512 _2513 _2515) = (term461 R _2512 _2514 _2513 _2515).
Proof. exact (TRANS (@lem119622 _2514 R _2512 _2513 _2515) (@lem119658 R _2512 _2514 _2513 _2515)). Qed.
Lemma lem119670 (R : type1605) (_2512 : nat) (_2514 : nat) (_2513 : nat) (_2515 : nat) : (term410 _2514 _2515 R _2512 _2513) = (term461 R _2512 _2514 _2513 _2515).
Proof. exact (TRANS (@lem119617 _2514 R _2512 _2513 _2515) (@lem119669 R _2512 _2514 _2513 _2515)). Qed.
Lemma lem119671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem119672 (R : type1605) (_2512 : nat) (_2514 : nat) (_2513 : nat) (_2515 : nat) : (term462 _2514 _2515 R _2512 _2513) = (term463 R _2512 _2514 _2513 _2515).
Proof. exact (MK_COMB (@lem119671) (@lem119670 R _2512 _2514 _2513 _2515)). Qed.
Lemma lem119698 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem119699 (R : type1605) (_2512 : nat) (_2513 : nat) (_2515 : nat) : (term453 _2515 R _2512 _2513) = (term454 R _2512 _2513 _2515).
Proof. exact (@lem119698 (term377 R _2512 _2513) (term425 _2513 _2515)). Qed.
Lemma lem119707 (_2512 : nat) (_2514 : nat) : (term426 _2512 _2514) = (term426 _2512 _2514).
Proof. exact (eq_refl (term426 _2512 _2514)). Qed.
Lemma lem119708 (_2514 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) (_2515 : nat) : (term464 _2514 _2515 R _2512 _2513) = (term459 _2514 R _2512 _2513 _2515).
Proof. exact (MK_COMB (@lem119707 _2512 _2514) (@lem119699 R _2512 _2513 _2515)). Qed.
Lemma lem119712 (q : Prop) (p : Prop) (r : Prop) : (term428 p q r) = (term428 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem119713 (R : type1605) (_2512 : nat) (_2514 : nat) (_2513 : nat) (_2515 : nat) : (term459 _2514 R _2512 _2513 _2515) = (term460 R _2512 _2514 _2513 _2515).
Proof. exact (@lem119712 (term377 R _2512 _2513) (term425 _2512 _2514) (term425 _2513 _2515)). Qed.
Lemma lem119733 (R : type1605) (_2512 : nat) (_2514 : nat) (_2513 : nat) (_2515 : nat) : (term464 _2514 _2515 R _2512 _2513) = (term460 R _2512 _2514 _2513 _2515).
Proof. exact (TRANS (@lem119708 _2514 R _2512 _2513 _2515) (@lem119713 R _2512 _2514 _2513 _2515)). Qed.
Lemma lem119734 (R : type1605) (_2514 : nat) (_2515 : nat) : (term455 R _2514 _2515) = (term455 R _2514 _2515).
Proof. exact (eq_refl (term455 R _2514 _2515)). Qed.
Lemma lem119735 (R : type1605) (_2512 : nat) (_2514 : nat) (_2513 : nat) (_2515 : nat) : (term465 _2514 _2515 R _2512 _2513) = (term461 R _2512 _2514 _2513 _2515).
Proof. exact (MK_COMB (@lem119734 R _2514 _2515) (@lem119733 R _2512 _2514 _2513 _2515)). Qed.
Lemma lem119746 (R : type1605) (_2512 : nat) (_2514 : nat) (_2513 : nat) (_2515 : nat) : ((term410 _2514 _2515 R _2512 _2513) = (term465 _2514 _2515 R _2512 _2513)) = ((term461 R _2512 _2514 _2513 _2515) = (term461 R _2512 _2514 _2513 _2515)).
Proof. exact (MK_COMB (@lem119672 R _2512 _2514 _2513 _2515) (@lem119735 R _2512 _2514 _2513 _2515)). Qed.
Lemma lem119748 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem119749 (x : Prop) : (x = x) = True.
Proof. exact (@lem119748 Prop x). Qed.
Lemma lem119750 (R : type1605) (_2512 : nat) (_2514 : nat) (_2513 : nat) (_2515 : nat) : ((term461 R _2512 _2514 _2513 _2515) = (term461 R _2512 _2514 _2513 _2515)) = True.
Proof. exact (@lem119749 (term461 R _2512 _2514 _2513 _2515)). Qed.
Lemma lem119751 (_2514 : nat) (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : ((term410 _2514 _2515 R _2512 _2513) = (term465 _2514 _2515 R _2512 _2513)) = True.
Proof. exact (TRANS (@lem119746 R _2512 _2514 _2513 _2515) (@lem119750 R _2512 _2514 _2513 _2515)). Qed.
Lemma lem119752 (_2514 : nat) (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : True = ((term410 _2514 _2515 R _2512 _2513) = (term465 _2514 _2515 R _2512 _2513)).
Proof. exact (SYM (@lem119751 _2514 _2515 R _2512 _2513)). Qed.
Lemma lem119753 (_2514 : nat) (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : (term410 _2514 _2515 R _2512 _2513) = (term465 _2514 _2515 R _2512 _2513).
Proof. exact (EQ_MP (@lem119752 _2514 _2515 R _2512 _2513) (@lem0)). Qed.
Lemma lem119754 (_2514 : nat) (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : term465 _2514 _2515 R _2512 _2513.
Proof. exact (EQ_MP (@lem119753 _2514 _2515 R _2512 _2513) (@lem119299 _2514 _2515 R _2512 _2513)). Qed.
Lemma lem119756 (b : Prop) (a : Prop) : (a \/ b) = (term381 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem119757 (_2512 : nat) (_2513 : nat) (R : type1605) (_2514 : nat) (_2515 : nat) : (term465 _2514 _2515 R _2512 _2513) = (term466 _2512 _2513 R _2514 _2515).
Proof. exact (@lem119756 (term464 _2514 _2515 R _2512 _2513) (R _2514 _2515)). Qed.
Lemma lem119759 (a : Prop) (b : Prop) : (term434 a b) = (term435 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem119760 (_2514 : nat) (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : (term467 _2514 _2515 R _2512 _2513) = (term468 _2514 _2515 R _2512 _2513).
Proof. exact (@lem119759 (term425 _2512 _2514) (term453 _2515 R _2512 _2513)). Qed.
Lemma lem119762 (a : Prop) : (term383 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem119763 (_2512 : nat) (_2514 : nat) : (term438 _2512 _2514) = (_2512 = _2514).
Proof. exact (@lem119762 (_2512 = _2514)). Qed.
Lemma lem119764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem119765 (_2512 : nat) (_2514 : nat) : (term439 _2512 _2514) = (term440 _2512 _2514).
Proof. exact (MK_COMB (@lem119764) (@lem119763 _2512 _2514)). Qed.
Lemma lem119767 (a : Prop) (b : Prop) : (term434 a b) = (term435 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem119768 (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : (term469 _2515 R _2512 _2513) = (term470 _2515 R _2512 _2513).
Proof. exact (@lem119767 (term425 _2513 _2515) (term377 R _2512 _2513)). Qed.
Lemma lem119770 (a : Prop) : (term383 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem119771 (_2513 : nat) (_2515 : nat) : (term438 _2513 _2515) = (_2513 = _2515).
Proof. exact (@lem119770 (_2513 = _2515)). Qed.
Lemma lem119772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem119773 (_2513 : nat) (_2515 : nat) : (term439 _2513 _2515) = (term440 _2513 _2515).
Proof. exact (MK_COMB (@lem119772) (@lem119771 _2513 _2515)). Qed.
Lemma lem119775 (a : Prop) : (term383 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem119776 (R : type1605) (_2512 : nat) (_2513 : nat) : (term471 R _2512 _2513) = (R _2512 _2513).
Proof. exact (@lem119775 (R _2512 _2513)). Qed.
Lemma lem119777 (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : (term470 _2515 R _2512 _2513) = (term472 _2515 R _2512 _2513).
Proof. exact (MK_COMB (@lem119773 _2513 _2515) (@lem119776 R _2512 _2513)). Qed.
Lemma lem119778 (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : (term469 _2515 R _2512 _2513) = (term472 _2515 R _2512 _2513).
Proof. exact (TRANS (@lem119768 _2515 R _2512 _2513) (@lem119777 _2515 R _2512 _2513)). Qed.
Lemma lem119779 (_2514 : nat) (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : (term468 _2514 _2515 R _2512 _2513) = (term473 _2514 _2515 R _2512 _2513).
Proof. exact (MK_COMB (@lem119765 _2512 _2514) (@lem119778 _2515 R _2512 _2513)). Qed.
Lemma lem119780 (_2514 : nat) (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : (term467 _2514 _2515 R _2512 _2513) = (term473 _2514 _2515 R _2512 _2513).
Proof. exact (TRANS (@lem119760 _2514 _2515 R _2512 _2513) (@lem119779 _2514 _2515 R _2512 _2513)). Qed.
Lemma lem119781 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem119782 (_2514 : nat) (_2515 : nat) (R : type1605) (_2512 : nat) (_2513 : nat) : (term474 _2514 _2515 R _2512 _2513) = (term475 _2514 _2515 R _2512 _2513).
Proof. exact (MK_COMB (@lem119781) (@lem119780 _2514 _2515 R _2512 _2513)). Qed.
Lemma lem119783 (R : type1605) (_2514 : nat) (_2515 : nat) : (R _2514 _2515) = (R _2514 _2515).
Proof. exact (eq_refl (R _2514 _2515)). Qed.
Lemma lem119784 (_2512 : nat) (_2513 : nat) (R : type1605) (_2514 : nat) (_2515 : nat) : (term466 _2512 _2513 R _2514 _2515) = (term476 _2512 _2513 R _2514 _2515).
Proof. exact (MK_COMB (@lem119782 _2514 _2515 R _2512 _2513) (@lem119783 R _2514 _2515)). Qed.
Lemma lem119785 (_2512 : nat) (_2513 : nat) (R : type1605) (_2514 : nat) (_2515 : nat) : (term465 _2514 _2515 R _2512 _2513) = (term476 _2512 _2513 R _2514 _2515).
Proof. exact (TRANS (@lem119757 _2512 _2513 R _2514 _2515) (@lem119784 _2512 _2513 R _2514 _2515)). Qed.
Lemma lem119787 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term144 m d' R) : term477 R d m d'.
Proof. exact (conj (@lem119553 d m d' R h1 h2) (@lem119561 d m d' R h2)). Qed.
Lemma lem119788 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term144 m d' R) : term478 R d m d'.
Proof. exact (conj (@lem119358 m) (@lem119787 d m d' R h1 h2)). Qed.
Lemma lem119790 (_2512 : nat) (_2513 : nat) (R : type1605) (_2514 : nat) (_2515 : nat) : term476 _2512 _2513 R _2514 _2515.
Proof. exact (EQ_MP (@lem119785 _2512 _2513 R _2514 _2515) (@lem119754 _2514 _2515 R _2512 _2513)). Qed.
Lemma lem119791 (d : type1606) (R : type1605) (m : nat) (d' : nat) : term479 d R m d'.
Proof. exact (@lem119790 m (term416 d m d') R m d'). Qed.
Lemma lem119794 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term144 m d' R) : R m d'.
Proof. exact (@lem119791 d R m d' (@lem119788 d m d' R h1 h2)). Qed.
Lemma lem119795 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term144 m d' R) : term480 R m d'.
Proof. exact (fun h0 : term377 R m d' => @lem119794 d m d' R h1 h2). Qed.
Lemma lem119797 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem119798 (R : type1605) (m : nat) (d' : nat) : (term480 R m d') = (R m d').
Proof. exact (@lem119797 (R m d')). Qed.
Lemma lem119799 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term144 m d' R) : R m d'.
Proof. exact (EQ_MP (@lem119798 R m d') (@lem119795 d m d' R h1 h2)). Qed.
Lemma lem119802 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem119804 (R : type1605) (m : nat) (d' : nat) : (term377 R m d') = (term481 R m d').
Proof. exact (@lem119802 (R m d')). Qed.
Lemma lem119807 (m : nat) (d' : nat) (R : type1605) (h1 : term144 m d' R) : term481 R m d'.
Proof. exact (EQ_MP (@lem119804 R m d') (@lem119111 m d' R h1)). Qed.
Lemma lem119810 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term144 m d' R) : False.
Proof. exact (@lem119807 m d' R h2 (@lem119799 d m d' R h1 h2)). Qed.
Lemma lem119811 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term144 m d' R) : term402.
Proof. exact (fun h0 : ~ False => @lem119810 d m d' R h1 h2). Qed.
Lemma lem119813 (p : Prop) : (term380 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem119814 : term402 = False.
Proof. exact (@lem119813 False). Qed.
Lemma lem119815 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term144 m d' R) : False.
Proof. exact (EQ_MP (@lem119814) (@lem119811 d m d' R h1 h2)). Qed.
Lemma lem119816 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term187 m d' R) : False.
Proof. exact (or_elim (@lem118863 m d' R h2) (fun h0 : term107 R m d' => @lem119280 R m d' d h0 h1) (fun h0 : term144 m d' R => @lem119815 d m d' R h1 h0)). Qed.
Lemma lem119817 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term187 m d' R) : (term187 m d' R) = False.
Proof. exact (prop_ext (fun h3 : term187 m d' R => @lem119816 d m d' R h1 h2) (fun h3 : False => @lem118863 m d' R h2)). Qed.
Lemma lem119818 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term187 m d' R) : False.
Proof. exact (EQ_MP (@lem119817 d m d' R h1 h2) (@lem118863 m d' R h2)). Qed.
Lemma lem119819 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term187 m d' R) : (term344 d) = False.
Proof. exact (prop_ext (fun h3 : term344 d => @lem119818 d m d' R h1 h2) (fun h3 : False => @lem118791 d h1)). Qed.
Lemma lem119820 (d : type1606) (m : nat) (d' : nat) (R : type1605) (h1 : term344 d) (h2 : term187 m d' R) : False.
Proof. exact (EQ_MP (@lem119819 d m d' R h1 h2) (@lem118791 d h1)). Qed.
Lemma lem119821 (m : nat) (R : type1605) (d : type1606) (h1 : term190 m R) (h2 : term344 d) : False.
Proof. exact (ex_elim (@lem118729 m R h1) (fun d' : nat => fun h0 : term189 m R d' => @lem119820 d m d' R h2 h0)). Qed.
Lemma lem119822 (R : type1605) (d : type1606) (h1 : term4 R) (h2 : term344 d) : False.
Proof. exact (ex_elim (@lem118301 R h1) (fun m : nat => fun h0 : term194 R m => @lem119821 m R d h0 h2)). Qed.
Lemma lem119823 (R : type1605) (h1 : term11) (h2 : term4 R) : False.
Proof. exact (ex_elim (@lem118727 h1) (fun d : type1606 => fun h0 : term346 d => @lem119822 R d h2 h0)). Qed.
Lemma lem119824 (R : type1605) (h1 : term4 R) : term9.
Proof. exact (fun h0 : term11 => @lem119823 R h0 h1). Qed.
Lemma lem119825 : term9 = term10.
Proof. exact (@lem69 term11). Qed.
Lemma lem119826 (R : type1605) (h1 : term4 R) : term10.
Proof. exact (EQ_MP (@lem119825) (@lem119824 R h1)). Qed.
Lemma lem119827 (R : type1605) : term13 R.
Proof. exact (fun h0 : term4 R => @lem119826 R h0). Qed.
Lemma lem119832 : term17.
Proof. exact (fun R : type1605 => @lem119827 R). Qed.
Lemma lem119833 : term16.
Proof. exact (EQ_MP (@lem117924) (@lem119832)). Qed.
Lemma lem119834 (R : type1605) : term482 R.
Proof. exact (@lem119833 R). Qed.
Lemma lem119835 (R : type1605) : (term482 R) = (term5 R).
Proof. exact (eq_refl (term482 R)). Qed.
Lemma lem119836 (R : type1605) : term5 R.
Proof. exact (EQ_MP (@lem119835 R) (@lem119834 R)). Qed.
Lemma lem119838 (R : type1605) : term5 R.
Proof. exact (@lem117769 R (@lem119836 R)). Qed.
Lemma lem119839 (R : type1605) (h1 : term4 R) : term9.
Proof. exact (@lem119838 R (@lem117754 R h1)). Qed.
Lemma lem119840 (R : type1605) (h1 : term4 R) : False.
Proof. exact (@lem119839 R h1 (@lem99708)). Qed.
Lemma lem119841 (R : type1605) (h1 : term4 R) : (term4 R) = False.
Proof. exact (prop_ext (fun h2 : term4 R => @lem119840 R h1) (fun h2 : False => @lem117754 R h1)). Qed.
Lemma lem119842 (R : type1605) (h1 : term4 R) : False.
Proof. exact (EQ_MP (@lem119841 R h1) (@lem117754 R h1)). Qed.
Lemma lem119843 (R : type1605) : term3 R.
Proof. exact (fun h0 : term4 R => @lem119842 R h0). Qed.
Lemma lem119846 (p : Prop) (q : Prop) (r : Prop) : (term483 p q r) = (term484 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem119847 (P : type1605) : (term485 P) = (term486 P).
Proof. exact (@lem119846 (term487 P) (term488 P) (term1 P)). Qed.
Lemma lem119865 (p : Prop) (q : Prop) (r : Prop) : (term483 p q r) = (term484 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem119866 (P : type1605) (m : nat) (n : nat) : (term489 P m n) = (term490 P m n).
Proof. exact (@lem119865 (Peano.le m n) (P m n) (term491 P m n)). Qed.
Lemma lem119871 (P : type1605) (m : nat) : (term492 P m) = (term493 P m).
Proof. exact (fun_ext (fun n : nat => @lem119866 P m n)). Qed.
Lemma lem119872 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem119873 (P : type1605) (m : nat) : (term494 P m) = (term495 P m).
Proof. exact (MK_COMB (@lem119872) (@lem119871 P m)). Qed.
Lemma lem119878 (P : type1605) : (term496 P) = (term497 P).
Proof. exact (fun_ext (fun m : nat => @lem119873 P m)). Qed.
Lemma lem119879 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem119880 (P : type1605) : (term488 P) = (term498 P).
Proof. exact (MK_COMB (@lem119879) (@lem119878 P)). Qed.
Lemma lem119882 (R : type1605) : (term1 R) = (term2 R).
Proof. exact (EQ_MP (@lem117753 R) (@lem119843 R)). Qed.
Lemma lem119883 (P : type1605) : (term499 P) = (term500 P).
Proof. exact (@lem119882 (term501 P)). Qed.
Lemma lem119884 (P : type1605) (m : nat) : (term502 P m) = (term503 P m).
Proof. exact (eq_refl (term502 P m)). Qed.
Lemma lem119885 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem119886 (P : type1605) (m : nat) (n : nat) : (term504 P m n) = (term505 P m n).
Proof. exact (MK_COMB (@lem119884 P m) (@lem119885 n)). Qed.
Lemma lem119887 (P : type1605) (m : nat) (n : nat) : (term505 P m n) = (term506 P m n).
Proof. exact (eq_refl (term505 P m n)). Qed.
Lemma lem119888 (P : type1605) (m : nat) (n : nat) : (term504 P m n) = (term506 P m n).
Proof. exact (TRANS (@lem119886 P m n) (@lem119887 P m n)). Qed.
Lemma lem119889 (m : nat) (n : nat) : (term398 m n) = (term398 m n).
Proof. exact (eq_refl (term398 m n)). Qed.
Lemma lem119890 (P : type1605) (m : nat) (n : nat) : (term507 P m n) = (term490 P m n).
Proof. exact (MK_COMB (@lem119889 m n) (@lem119888 P m n)). Qed.
Lemma lem119891 (P : type1605) (m : nat) : (term508 P m) = (term493 P m).
Proof. exact (fun_ext (fun n : nat => @lem119890 P m n)). Qed.
Lemma lem119892 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem119893 (P : type1605) (m : nat) : (term509 P m) = (term495 P m).
Proof. exact (MK_COMB (@lem119892) (@lem119891 P m)). Qed.
Lemma lem119894 (P : type1605) : (term510 P) = (term497 P).
Proof. exact (fun_ext (fun m : nat => @lem119893 P m)). Qed.
Lemma lem119895 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem119896 (P : type1605) : (term499 P) = (term498 P).
Proof. exact (MK_COMB (@lem119895) (@lem119894 P)). Qed.
Lemma lem119897 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem119898 (P : type1605) : (term511 P) = (term512 P).
Proof. exact (MK_COMB (@lem119897) (@lem119896 P)). Qed.
Lemma lem119899 (P : type1605) (m : nat) : (term502 P m) = (term503 P m).
Proof. exact (eq_refl (term502 P m)). Qed.
Lemma lem119900 (m : nat) (d : nat) : (Nat.add m d) = (Nat.add m d).
Proof. exact (eq_refl (Nat.add m d)). Qed.
Lemma lem119901 (P : type1605) (m : nat) (d : nat) : (term513 P m d) = (term514 P m d).
Proof. exact (MK_COMB (@lem119899 P m) (@lem119900 m d)). Qed.
Lemma lem119902 (P : type1605) (m : nat) (d : nat) : (term514 P m d) = (term515 P m d).
Proof. exact (eq_refl (term514 P m d)). Qed.
Lemma lem119903 (P : type1605) (m : nat) (d : nat) : (term513 P m d) = (term515 P m d).
Proof. exact (TRANS (@lem119901 P m d) (@lem119902 P m d)). Qed.
Lemma lem119904 (P : type1605) (m : nat) : (term516 P m) = (term517 P m).
Proof. exact (fun_ext (fun d : nat => @lem119903 P m d)). Qed.
Lemma lem119905 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem119906 (P : type1605) (m : nat) : (term518 P m) = (term519 P m).
Proof. exact (MK_COMB (@lem119905) (@lem119904 P m)). Qed.
Lemma lem119907 (P : type1605) : (term520 P) = (term521 P).
Proof. exact (fun_ext (fun m : nat => @lem119906 P m)). Qed.
Lemma lem119908 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem119909 (P : type1605) : (term500 P) = (term522 P).
Proof. exact (MK_COMB (@lem119908) (@lem119907 P)). Qed.
Lemma lem119910 (P : type1605) : ((term499 P) = (term500 P)) = ((term498 P) = (term522 P)).
Proof. exact (MK_COMB (@lem119898 P) (@lem119909 P)). Qed.
Lemma lem119911 (P : type1605) : (term498 P) = (term522 P).
Proof. exact (EQ_MP (@lem119910 P) (@lem119883 P)). Qed.
Lemma lem119922 (P : type1605) : (term488 P) = (term522 P).
Proof. exact (TRANS (@lem119880 P) (@lem119911 P)). Qed.
Lemma lem119923 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem119924 (P : type1605) : (term523 P) = (term524 P).
Proof. exact (MK_COMB (@lem119923) (@lem119922 P)). Qed.
Lemma lem119926 (R : type1605) : (term1 R) = (term2 R).
Proof. exact (EQ_MP (@lem117753 R) (@lem119843 R)). Qed.
Lemma lem119927 (P : type1605) : (term1 P) = (term2 P).
Proof. exact (@lem119926 P). Qed.
Lemma lem119936 (P : type1605) : (term525 P) = (term526 P).
Proof. exact (MK_COMB (@lem119924 P) (@lem119927 P)). Qed.
Lemma lem119939 (P : type1605) : (term527 P) = (term527 P).
Proof. exact (eq_refl (term527 P)). Qed.
Lemma lem119940 (P : type1605) : (term486 P) = (term528 P).
Proof. exact (MK_COMB (@lem119939 P) (@lem119936 P)). Qed.
Lemma lem119943 (P : type1605) : (term485 P) = (term528 P).
Proof. exact (TRANS (@lem119847 P) (@lem119940 P)). Qed.
Lemma lem119944 (P : type1605) : (term528 P) = (term485 P).
Proof. exact (SYM (@lem119943 P)). Qed.
Lemma lem119945 (P : type1605) (h1 : term487 P) : term487 P.
Proof. exact (h1). Qed.
Lemma lem119946 (P : type1605) (h1 : term522 P) : term522 P.
Proof. exact (h1). Qed.
Lemma lem119948 (P : nat -> Prop) : term529 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem119949 (P : type1605) (m : nat) : term530 P m.
Proof. exact (@lem119948 (term25 P m)). Qed.
Lemma lem119950 (P : type1605) (m : nat) : (term531 P m) = (term532 P m).
Proof. exact (eq_refl (term531 P m)). Qed.
Lemma lem119951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem119952 (P : type1605) (m : nat) : (term533 P m) = (term534 P m).
Proof. exact (MK_COMB (@lem119951) (@lem119950 P m)). Qed.
Lemma lem119953 (P : type1605) (m : nat) (d : nat) : (term58 P m d) = (term24 P m d).
Proof. exact (eq_refl (term58 P m d)). Qed.
Lemma lem119954 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem119955 (P : type1605) (m : nat) (d : nat) : (term535 P m d) = (term536 P m d).
Proof. exact (MK_COMB (@lem119954) (@lem119953 P m d)). Qed.
Lemma lem119956 (P : type1605) (m : nat) (d : nat) : (term537 P m d) = (term538 P m d).
Proof. exact (eq_refl (term537 P m d)). Qed.
Lemma lem119957 (P : type1605) (m : nat) (d : nat) : (term539 P m d) = (term540 P m d).
Proof. exact (MK_COMB (@lem119955 P m d) (@lem119956 P m d)). Qed.
Lemma lem119958 (P : type1605) (m : nat) : (term541 P m) = (term542 P m).
Proof. exact (fun_ext (fun d : nat => @lem119957 P m d)). Qed.
Lemma lem119959 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem119960 (P : type1605) (m : nat) : (term543 P m) = (term544 P m).
Proof. exact (MK_COMB (@lem119959) (@lem119958 P m)). Qed.
Lemma lem119961 (P : type1605) (m : nat) : (term545 P m) = (term546 P m).
Proof. exact (MK_COMB (@lem119952 P m) (@lem119960 P m)). Qed.
Lemma lem119962 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem119963 (P : type1605) (m : nat) : (term547 P m) = (term548 P m).
Proof. exact (MK_COMB (@lem119962) (@lem119961 P m)). Qed.
Lemma lem119964 (P : type1605) (m : nat) (d : nat) : (term58 P m d) = (term24 P m d).
Proof. exact (eq_refl (term58 P m d)). Qed.
Lemma lem119965 (P : type1605) (m : nat) : (term549 P m) = (term25 P m).
Proof. exact (fun_ext (fun d : nat => @lem119964 P m d)). Qed.
Lemma lem119966 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem119967 (P : type1605) (m : nat) : (term550 P m) = (term26 P m).
Proof. exact (MK_COMB (@lem119966) (@lem119965 P m)). Qed.
Lemma lem119968 (P : type1605) (m : nat) : (term530 P m) = (term551 P m).
Proof. exact (MK_COMB (@lem119963 P m) (@lem119967 P m)). Qed.
Lemma lem119969 (P : type1605) (m : nat) : term551 P m.
Proof. exact (EQ_MP (@lem119968 P m) (@lem119949 P m)). Qed.
Lemma lem119970 (P : type1605) (m : nat) (d : nat) (h1 : term24 P m d) : term24 P m d.
Proof. exact (h1). Qed.
Lemma lem119971 : term552.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem119987 : term553.
Proof. exact (proj1 (@lem119971)). Qed.
Lemma lem119988 (m : nat) : term554 m.
Proof. exact (@lem119987 m). Qed.
Lemma lem119989 (m : nat) : (term554 m) = ((term555 m) = m).
Proof. exact (eq_refl (term554 m)). Qed.
Lemma lem119995 (m : nat) (P : type1605) (h1 : term487 P) : term556 P m.
Proof. exact (@lem119945 P h1 m). Qed.
Lemma lem119996 (P : type1605) (m : nat) : (term556 P m) = (P m m).
Proof. exact (eq_refl (term556 P m)). Qed.
Lemma lem119997 (m : nat) (P : type1605) (h1 : term487 P) : P m m.
Proof. exact (EQ_MP (@lem119996 P m) (@lem119995 m P h1)). Qed.
Lemma lem119998 (P : type1605) (m : nat) : (P m m) = ((P m m) = True).
Proof. exact (@lem7 (P m m)). Qed.
Lemma lem120018 (m : nat) : (term555 m) = m.
Proof. exact (EQ_MP (@lem119989 m) (@lem119988 m)). Qed.
Lemma lem120019 (P : type1605) (m : nat) : (P m) = (P m).
Proof. exact (eq_refl (P m)). Qed.
Lemma lem120020 (P : type1605) (m : nat) : (term532 P m) = (P m m).
Proof. exact (MK_COMB (@lem120019 P m) (@lem120018 m)). Qed.
Lemma lem120022 (m : nat) (P : type1605) (h1 : term487 P) : (P m m) = True.
Proof. exact (EQ_MP (@lem119998 P m) (@lem119997 m P h1)). Qed.
Lemma lem120023 (m : nat) (P : type1605) (h1 : term487 P) : (term532 P m) = True.
Proof. exact (TRANS (@lem120020 P m) (@lem120022 m P h1)). Qed.
Lemma lem120024 (m : nat) (P : type1605) (h1 : term487 P) : True = (term532 P m).
Proof. exact (SYM (@lem120023 m P h1)). Qed.
Lemma lem120025 (m : nat) (P : type1605) (h1 : term487 P) : term532 P m.
Proof. exact (EQ_MP (@lem120024 m P h1) (@lem0)). Qed.
Lemma lem120026 : term552.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem120027 : term557.
Proof. exact (proj2 (@lem120026)). Qed.
Lemma lem120028 : term558.
Proof. exact (proj2 (@lem120027)). Qed.
Lemma lem120029 (m : nat) : term559 m.
Proof. exact (@lem120028 m). Qed.
Lemma lem120030 (m : nat) : (term559 m) = (term560 m).
Proof. exact (eq_refl (term559 m)). Qed.
Lemma lem120031 (m : nat) : term560 m.
Proof. exact (EQ_MP (@lem120030 m) (@lem120029 m)). Qed.
Lemma lem120032 (m : nat) (n : nat) : term561 m n.
Proof. exact (@lem120031 m n). Qed.
Lemma lem120033 (m : nat) (n : nat) : (term561 m n) = ((term562 m n) = (term563 m n)).
Proof. exact (eq_refl (term561 m n)). Qed.
Lemma lem120055 (m : nat) (P : type1605) (h1 : term522 P) : term564 P m.
Proof. exact (@lem119946 P h1 m). Qed.
Lemma lem120056 (P : type1605) (m : nat) : (term564 P m) = (term519 P m).
Proof. exact (eq_refl (term564 P m)). Qed.
Lemma lem120057 (m : nat) (P : type1605) (h1 : term522 P) : term519 P m.
Proof. exact (EQ_MP (@lem120056 P m) (@lem120055 m P h1)). Qed.
Lemma lem120058 (m : nat) (d : nat) (P : type1605) (h1 : term522 P) : term565 P m d.
Proof. exact (@lem120057 m P h1 d). Qed.
Lemma lem120059 (P : type1605) (m : nat) (d : nat) : (term565 P m d) = (term515 P m d).
Proof. exact (eq_refl (term565 P m d)). Qed.
Lemma lem120060 (m : nat) (d : nat) (P : type1605) (h1 : term522 P) : term515 P m d.
Proof. exact (EQ_MP (@lem120059 P m d) (@lem120058 m d P h1)). Qed.
Lemma lem120061 (P : type1605) (m : nat) (d : nat) (h1 : term24 P m d) : term24 P m d.
Proof. exact (h1). Qed.
Lemma lem120062 (P : type1605) (m : nat) (d : nat) (h1 : term522 P) (h2 : term24 P m d) : term566 P m d.
Proof. exact (@lem120060 m d P h1 (@lem120061 P m d h2)). Qed.
Lemma lem120063 (P : type1605) (m : nat) (d : nat) : (term566 P m d) = ((term566 P m d) = True).
Proof. exact (@lem7 (term566 P m d)). Qed.
Lemma lem120064 (P : type1605) (m : nat) (d : nat) (h1 : term522 P) (h2 : term24 P m d) : (term566 P m d) = True.
Proof. exact (EQ_MP (@lem120063 P m d) (@lem120062 P m d h1 h2)). Qed.
Lemma lem120070 (P : type1605) (m : nat) (d : nat) : (term24 P m d) = ((term24 P m d) = True).
Proof. exact (@lem7 (term24 P m d)). Qed.
Lemma lem120075 (m : nat) (n : nat) : (term562 m n) = (term563 m n).
Proof. exact (EQ_MP (@lem120033 m n) (@lem120032 m n)). Qed.
Lemma lem120076 (m : nat) (d : nat) : (term562 m d) = (term563 m d).
Proof. exact (@lem120075 m d). Qed.
Lemma lem120077 (P : type1605) (m : nat) : (P m) = (P m).
Proof. exact (eq_refl (P m)). Qed.
Lemma lem120078 (P : type1605) (m : nat) (d : nat) : (term538 P m d) = (term566 P m d).
Proof. exact (MK_COMB (@lem120077 P m) (@lem120076 m d)). Qed.
Lemma lem120080 (m : nat) (d : nat) (P : type1605) (h1 : term522 P) : term567 P m d.
Proof. exact (fun h0 : term24 P m d => @lem120064 P m d h1 h0). Qed.
Lemma lem120082 (P : type1605) (m : nat) (d : nat) (h1 : term24 P m d) : (term24 P m d) = True.
Proof. exact (EQ_MP (@lem120070 P m d) (@lem119970 P m d h1)). Qed.
Lemma lem120083 (P : type1605) (m : nat) (d : nat) (h1 : term24 P m d) : True = (term24 P m d).
Proof. exact (SYM (@lem120082 P m d h1)). Qed.
Lemma lem120084 (P : type1605) (m : nat) (d : nat) (h1 : term24 P m d) : term24 P m d.
Proof. exact (EQ_MP (@lem120083 P m d h1) (@lem0)). Qed.
Lemma lem120085 (P : type1605) (m : nat) (d : nat) (h1 : term522 P) (h2 : term24 P m d) : (term566 P m d) = True.
Proof. exact (@lem120080 m d P h1 (@lem120084 P m d h2)). Qed.
Lemma lem120086 (P : type1605) (m : nat) (d : nat) (h1 : term522 P) (h2 : term24 P m d) : (term538 P m d) = True.
Proof. exact (TRANS (@lem120078 P m d) (@lem120085 P m d h1 h2)). Qed.
Lemma lem120087 (P : type1605) (m : nat) (d : nat) (h1 : term522 P) (h2 : term24 P m d) : True = (term538 P m d).
Proof. exact (SYM (@lem120086 P m d h1 h2)). Qed.
Lemma lem120088 (P : type1605) (m : nat) (d : nat) (h1 : term522 P) (h2 : term24 P m d) : term538 P m d.
Proof. exact (EQ_MP (@lem120087 P m d h1 h2) (@lem0)). Qed.
Lemma lem120089 (m : nat) (d : nat) (P : type1605) (h1 : term522 P) : term540 P m d.
Proof. exact (fun h0 : term24 P m d => @lem120088 P m d h1 h0). Qed.
Lemma lem120094 (m : nat) (P : type1605) (h1 : term522 P) : term544 P m.
Proof. exact (fun d : nat => @lem120089 m d P h1). Qed.
Lemma lem120095 (m : nat) (P : type1605) (h1 : term522 P) (h2 : term487 P) : term546 P m.
Proof. exact (conj (@lem120025 m P h2) (@lem120094 m P h1)). Qed.
Lemma lem120096 (m : nat) (P : type1605) (h1 : term522 P) (h2 : term487 P) : term26 P m.
Proof. exact (@lem119969 P m (@lem120095 m P h1 h2)). Qed.
Lemma lem120101 (P : type1605) (h1 : term522 P) (h2 : term487 P) : term2 P.
Proof. exact (fun m : nat => @lem120096 m P h1 h2). Qed.
Lemma lem120102 (P : type1605) (h1 : term487 P) : term526 P.
Proof. exact (fun h0 : term522 P => @lem120101 P h0 h1). Qed.
Lemma lem120103 (P : type1605) : term528 P.
Proof. exact (fun h0 : term487 P => @lem120102 P h0). Qed.
Lemma lem120104 (P : type1605) : term485 P.
Proof. exact (EQ_MP (@lem119944 P) (@lem120103 P)). Qed.
Lemma lem120109 : term568.
Proof. exact (fun P : type1605 => @lem120104 P). Qed.
