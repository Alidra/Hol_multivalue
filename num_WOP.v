Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_WOP_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import num_WF_spec.
Require Import thm0_spec.
Require Import thm10568_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Lemma lem115791 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem115792 (P : nat -> Prop) (h1 : term0) : term1 P.
Proof. exact (@lem115791 h1 P). Qed.
Lemma lem115793 (P : nat -> Prop) : (term1 P) = (term2 P).
Proof. exact (eq_refl (term1 P)). Qed.
Lemma lem115794 (P : nat -> Prop) (h1 : term0) : term2 P.
Proof. exact (EQ_MP (@lem115793 P) (@lem115792 P h1)). Qed.
Lemma lem115795 (P : nat -> Prop) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem115796 (P : nat -> Prop) (h1 : term0) (h2 : term3 P) : term4 P.
Proof. exact (@lem115794 P h1 (@lem115795 P h2)). Qed.
Lemma lem115797 (P : nat -> Prop) (h1 : term3 P) : term5 P.
Proof. exact (fun h0 : term0 => @lem115796 P h0 h1). Qed.
Lemma lem115798 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem115799 (P : nat -> Prop) (h1 : term0) (h2 : term3 P) : term4 P.
Proof. exact (@lem115797 P h2 (@lem115798 h1)). Qed.
Lemma lem115800 (P : nat -> Prop) (h1 : term0) : term2 P.
Proof. exact (fun h0 : term3 P => @lem115799 P h1 h0). Qed.
Lemma lem115801 (h1 : term0) : term0.
Proof. exact (fun P : nat -> Prop => @lem115800 P h1). Qed.
Lemma lem115802 : term6.
Proof. exact (fun h0 : term0 => @lem115801 h0). Qed.
Lemma lem115803 : term0.
Proof. exact (@lem115802 (@lem115780)). Qed.
Lemma lem115804 (P : nat -> Prop) : term1 P.
Proof. exact (@lem115803 P). Qed.
Lemma lem115805 (P : nat -> Prop) : (term1 P) = (term2 P).
Proof. exact (eq_refl (term1 P)). Qed.
Lemma lem115807 {A : Type'} (P : A -> Prop) : term7 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem115808 {A : Type'} (P : A -> Prop) : (term7 A P) = ((term8 A P) = (term9 A P)).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem115821 (p : Prop) : p = (term10 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem115822 (P : nat -> Prop) : (term11 P) = (term12 P).
Proof. exact (@lem115821 (term11 P)). Qed.
Lemma lem115823 (P : nat -> Prop) : (term12 P) = (term11 P).
Proof. exact (SYM (@lem115822 P)). Qed.
Lemma lem115824 (P : nat -> Prop) (h1 : term13 P) : term13 P.
Proof. exact (h1). Qed.
Lemma lem115827 (P : nat -> Prop) (h1 : term12 P) : term12 P.
Proof. exact (h1). Qed.
Lemma lem115828 (P : nat -> Prop) : term14 P.
Proof. exact (fun h0 : term12 P => @lem115827 P h0). Qed.
Lemma lem115829 (P : nat -> Prop) (h1 : term14 P) : term14 P.
Proof. exact (h1). Qed.
Lemma lem115830 (P : nat -> Prop) (h1 : term12 P) : term12 P.
Proof. exact (h1). Qed.
Lemma lem115831 (P : nat -> Prop) (h1 : term12 P) (h2 : term14 P) : term12 P.
Proof. exact (@lem115829 P h2 (@lem115830 P h1)). Qed.
Lemma lem115832 (P : nat -> Prop) (h1 : term12 P) : term15 P.
Proof. exact (fun h0 : term14 P => @lem115831 P h1 h0). Qed.
Lemma lem115833 (P : nat -> Prop) (h1 : term14 P) : term14 P.
Proof. exact (h1). Qed.
Lemma lem115834 (P : nat -> Prop) (h1 : term12 P) (h2 : term14 P) : term12 P.
Proof. exact (@lem115832 P h1 (@lem115833 P h2)). Qed.
Lemma lem115835 (P : nat -> Prop) (h1 : term14 P) : term14 P.
Proof. exact (fun h0 : term12 P => @lem115834 P h0 h1). Qed.
Lemma lem115836 (P : nat -> Prop) : term16 P.
Proof. exact (fun h0 : term14 P => @lem115835 P h0). Qed.
Lemma lem115839 (P : nat -> Prop) : term14 P.
Proof. exact (@lem115836 P (@lem115828 P)). Qed.
Lemma lem115845 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem115846 (P : nat -> Prop) : (term12 P) = (term17 P).
Proof. exact (@lem115845 (term13 P)). Qed.
Lemma lem115848 (t : Prop) : (term18 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem115849 (P : nat -> Prop) : (term17 P) = (term11 P).
Proof. exact (@lem115848 (term11 P)). Qed.
Lemma lem115852 (P : nat -> Prop) : (term12 P) = (term11 P).
Proof. exact (TRANS (@lem115846 P) (@lem115849 P)). Qed.
Lemma lem115893 : term19 = term20.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem115852 P)). Qed.
Lemma lem115894 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem115903 : term21 = term22.
Proof. exact (MK_COMB (@lem115894) (@lem115893)). Qed.
Lemma lem115904 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem115905 (P : nat -> Prop) : (term23 P) = (term23 P).
Proof. exact (fun_ext (fun n : nat => @lem115904 P n)). Qed.
Lemma lem115906 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem115907 (P : nat -> Prop) : (term24 P) = (term24 P).
Proof. exact (MK_COMB (@lem115906) (@lem115905 P)). Qed.
Lemma lem115914 (n : nat) (P : nat -> Prop) (m : nat) : (term25 n P m) = (term25 n P m).
Proof. exact (eq_refl (term25 n P m)). Qed.
Lemma lem115915 (n : nat) (P : nat -> Prop) : (term26 n P) = (term26 n P).
Proof. exact (fun_ext (fun m : nat => @lem115914 n P m)). Qed.
Lemma lem115916 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem115917 (n : nat) (P : nat -> Prop) : (term27 n P) = (term27 n P).
Proof. exact (MK_COMB (@lem115916) (@lem115915 n P)). Qed.
Lemma lem115920 (P : nat -> Prop) (n : nat) : (term28 P n) = (term28 P n).
Proof. exact (eq_refl (term28 P n)). Qed.
Lemma lem115921 (n : nat) (P : nat -> Prop) : (term29 n P) = (term29 n P).
Proof. exact (MK_COMB (@lem115920 P n) (@lem115917 n P)). Qed.
Lemma lem115922 (P : nat -> Prop) : (term30 P) = (term30 P).
Proof. exact (fun_ext (fun n : nat => @lem115921 n P)). Qed.
Lemma lem115923 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem115924 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (MK_COMB (@lem115923) (@lem115922 P)). Qed.
Lemma lem115925 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem115926 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (MK_COMB (@lem115925) (@lem115924 P)). Qed.
Lemma lem115927 (P : nat -> Prop) : (term11 P) = (term11 P).
Proof. exact (MK_COMB (@lem115926 P) (@lem115907 P)). Qed.
Lemma lem115928 : term20 = term20.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem115927 P)). Qed.
Lemma lem115929 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem115930 : term22 = term22.
Proof. exact (MK_COMB (@lem115929) (@lem115928)). Qed.
Lemma lem115963 : term21 = term22.
Proof. exact (TRANS (@lem115903) (@lem115930)). Qed.
Lemma lem115964 : term22 = term21.
Proof. exact (SYM (@lem115963)). Qed.
Lemma lem115965 (P : nat -> Prop) (h1 : term31 P) : term31 P.
Proof. exact (h1). Qed.
Lemma lem115967 (p : Prop) : p = (term10 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem115968 (P : nat -> Prop) : (term24 P) = (term33 P).
Proof. exact (@lem115967 (term24 P)). Qed.
Lemma lem115969 (P : nat -> Prop) : (term33 P) = (term24 P).
Proof. exact (SYM (@lem115968 P)). Qed.
Lemma lem115970 (P : nat -> Prop) (h1 : term34 P) : term34 P.
Proof. exact (h1). Qed.
Lemma lem115978 (n : nat) (P : nat -> Prop) (m : nat) : (term25 n P m) = (term35 n P m).
Proof. exact (@lem17265 (Peano.lt m n) (term36 P m)). Qed.
Lemma lem115979 (n : nat) (P : nat -> Prop) : (term26 n P) = (term37 n P).
Proof. exact (fun_ext (fun m : nat => @lem115978 n P m)). Qed.
Lemma lem115980 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem115981 (n : nat) (P : nat -> Prop) : (term27 n P) = (term38 n P).
Proof. exact (MK_COMB (@lem115980) (@lem115979 n P)). Qed.
Lemma lem115983 (P : nat -> Prop) (n : nat) : (term28 P n) = (term28 P n).
Proof. exact (eq_refl (term28 P n)). Qed.
Lemma lem115984 (n : nat) (P : nat -> Prop) : (term29 n P) = (term39 n P).
Proof. exact (MK_COMB (@lem115983 P n) (@lem115981 n P)). Qed.
Lemma lem115985 (P : nat -> Prop) : (term30 P) = (term40 P).
Proof. exact (fun_ext (fun n : nat => @lem115984 n P)). Qed.
Lemma lem115986 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem116067 (P : nat -> Prop) : (term31 P) = (term41 P).
Proof. exact (MK_COMB (@lem115986) (@lem115985 P)). Qed.
Lemma lem116068 (P : nat -> Prop) (h1 : term31 P) : term41 P.
Proof. exact (EQ_MP (@lem116067 P) (@lem115965 P h1)). Qed.
Lemma lem116070 (P : nat -> Prop) : (term42 P) = (term43 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem116071 (P : nat -> Prop) : (term34 P) = (term44 P).
Proof. exact (@lem116070 (term23 P)). Qed.
Lemma lem116072 (P : nat -> Prop) (n : nat) : (term45 P n) = (P n).
Proof. exact (eq_refl (term45 P n)). Qed.
Lemma lem116073 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem116075 (P : nat -> Prop) (n : nat) : (term46 P n) = (term36 P n).
Proof. exact (MK_COMB (@lem116073) (@lem116072 P n)). Qed.
Lemma lem116076 (P : nat -> Prop) : (term47 P) = (term48 P).
Proof. exact (fun_ext (fun n : nat => @lem116075 P n)). Qed.
Lemma lem116077 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116078 (P : nat -> Prop) : (term44 P) = (term43 P).
Proof. exact (MK_COMB (@lem116077) (@lem116076 P)). Qed.
Lemma lem116087 (P : nat -> Prop) : (term34 P) = (term43 P).
Proof. exact (TRANS (@lem116071 P) (@lem116078 P)). Qed.
Lemma lem116088 (P : nat -> Prop) (h1 : term34 P) : term43 P.
Proof. exact (EQ_MP (@lem116087 P) (@lem115970 P h1)). Qed.
Lemma lem116089 (n : nat) (P : nat -> Prop) (h1 : term39 n P) : term39 n P.
Proof. exact (h1). Qed.
Lemma lem116094 (P : nat -> Prop) (n : nat) : (term36 P n) = (term36 P n).
Proof. exact (eq_refl (term36 P n)). Qed.
Lemma lem116095 (P : nat -> Prop) : (term48 P) = (term48 P).
Proof. exact (fun_ext (fun n : nat => @lem116094 P n)). Qed.
Lemma lem116096 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116097 (P : nat -> Prop) : (term43 P) = (term43 P).
Proof. exact (MK_COMB (@lem116096) (@lem116095 P)). Qed.
Lemma lem116098 (P : nat -> Prop) (h1 : term34 P) : term43 P.
Proof. exact (EQ_MP (@lem116097 P) (@lem116088 P h1)). Qed.
Lemma lem116113 (n : nat) (P : nat -> Prop) (m : nat) : (term35 n P m) = (term35 n P m).
Proof. exact (eq_refl (term35 n P m)). Qed.
Lemma lem116114 (n : nat) (P : nat -> Prop) : (term37 n P) = (term37 n P).
Proof. exact (fun_ext (fun m : nat => @lem116113 n P m)). Qed.
Lemma lem116115 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116116 (n : nat) (P : nat -> Prop) : (term38 n P) = (term38 n P).
Proof. exact (MK_COMB (@lem116115) (@lem116114 n P)). Qed.
Lemma lem116121 (P : nat -> Prop) (n : nat) : (term28 P n) = (term28 P n).
Proof. exact (eq_refl (term28 P n)). Qed.
Lemma lem116122 (n : nat) (P : nat -> Prop) : (term39 n P) = (term39 n P).
Proof. exact (MK_COMB (@lem116121 P n) (@lem116116 n P)). Qed.
Lemma lem116123 (n : nat) (P : nat -> Prop) (h1 : term39 n P) : term39 n P.
Proof. exact (EQ_MP (@lem116122 n P) (@lem116089 n P h1)). Qed.
Lemma lem116127 (P : nat -> Prop) (n : nat) : (term36 P n) = (term36 P n).
Proof. exact (eq_refl (term36 P n)). Qed.
Lemma lem116128 (P : nat -> Prop) : (term48 P) = (term48 P).
Proof. exact (fun_ext (fun n : nat => @lem116127 P n)). Qed.
Lemma lem116129 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116131 (P : nat -> Prop) : (term43 P) = (term43 P).
Proof. exact (MK_COMB (@lem116129) (@lem116128 P)). Qed.
Lemma lem116132 (P : nat -> Prop) (h1 : term34 P) : term43 P.
Proof. exact (EQ_MP (@lem116131 P) (@lem116098 P h1)). Qed.
Lemma lem116150 (_2468 : nat) (P : nat -> Prop) (h1 : term34 P) : term49 P _2468.
Proof. exact (@lem116132 P h1 _2468). Qed.
Lemma lem116151 (P : nat -> Prop) (_2468 : nat) : (term49 P _2468) = (term36 P _2468).
Proof. exact (eq_refl (term49 P _2468)). Qed.
Lemma lem116157 (_2468 : nat) (P : nat -> Prop) (h1 : term34 P) : term36 P _2468.
Proof. exact (EQ_MP (@lem116151 P _2468) (@lem116150 _2468 P h1)). Qed.
Lemma lem116167 (n : nat) (P : nat -> Prop) (h1 : term39 n P) : P n.
Proof. exact (proj1 (@lem116123 n P h1)). Qed.
Lemma lem116168 (n : nat) (P : nat -> Prop) (h1 : term39 n P) : term50 P n.
Proof. exact (fun h0 : term36 P n => @lem116167 n P h1). Qed.
Lemma lem116170 (p : Prop) : (term51 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem116171 (P : nat -> Prop) (n : nat) : (term50 P n) = (P n).
Proof. exact (@lem116170 (P n)). Qed.
Lemma lem116172 (n : nat) (P : nat -> Prop) (h1 : term39 n P) : P n.
Proof. exact (EQ_MP (@lem116171 P n) (@lem116168 n P h1)). Qed.
Lemma lem116175 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem116177 (P : nat -> Prop) (_2468 : nat) : (term36 P _2468) = (term52 P _2468).
Proof. exact (@lem116175 (P _2468)). Qed.
Lemma lem116180 (_2468 : nat) (P : nat -> Prop) (h1 : term34 P) : term52 P _2468.
Proof. exact (EQ_MP (@lem116177 P _2468) (@lem116157 _2468 P h1)). Qed.
Lemma lem116181 (n : nat) (P : nat -> Prop) (h1 : term34 P) : term52 P n.
Proof. exact (@lem116180 n P h1). Qed.
Lemma lem116184 (n : nat) (P : nat -> Prop) (h1 : term34 P) (h2 : term39 n P) : False.
Proof. exact (@lem116181 n P h1 (@lem116172 n P h2)). Qed.
Lemma lem116185 (n : nat) (P : nat -> Prop) (h1 : term34 P) (h2 : term39 n P) : term53.
Proof. exact (fun h0 : ~ False => @lem116184 n P h1 h2). Qed.
Lemma lem116187 (p : Prop) : (term51 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem116188 : term53 = False.
Proof. exact (@lem116187 False). Qed.
Lemma lem116189 (n : nat) (P : nat -> Prop) (h1 : term34 P) (h2 : term39 n P) : False.
Proof. exact (EQ_MP (@lem116188) (@lem116185 n P h1 h2)). Qed.
Lemma lem116190 (n : nat) (P : nat -> Prop) (h1 : term34 P) (h2 : term39 n P) : (term39 n P) = False.
Proof. exact (prop_ext (fun h3 : term39 n P => @lem116189 n P h1 h2) (fun h3 : False => @lem116123 n P h2)). Qed.
Lemma lem116191 (n : nat) (P : nat -> Prop) (h1 : term34 P) (h2 : term39 n P) : False.
Proof. exact (EQ_MP (@lem116190 n P h1 h2) (@lem116123 n P h2)). Qed.
Lemma lem116192 (P : nat -> Prop) (h1 : term31 P) (h2 : term34 P) : False.
Proof. exact (ex_elim (@lem116068 P h1) (fun n : nat => fun h0 : term40 P n => @lem116191 n P h2 h0)). Qed.
Lemma lem116193 (P : nat -> Prop) (h1 : term31 P) (h2 : term34 P) : (term34 P) = False.
Proof. exact (prop_ext (fun h3 : term34 P => @lem116192 P h1 h2) (fun h3 : False => @lem115970 P h2)). Qed.
Lemma lem116194 (P : nat -> Prop) (h1 : term31 P) (h2 : term34 P) : False.
Proof. exact (EQ_MP (@lem116193 P h1 h2) (@lem115970 P h2)). Qed.
Lemma lem116195 (P : nat -> Prop) (h1 : term31 P) : term33 P.
Proof. exact (fun h0 : term34 P => @lem116194 P h1 h0). Qed.
Lemma lem116196 (P : nat -> Prop) (h1 : term31 P) : term24 P.
Proof. exact (EQ_MP (@lem115969 P) (@lem116195 P h1)). Qed.
Lemma lem116197 (P : nat -> Prop) : term11 P.
Proof. exact (fun h0 : term31 P => @lem116196 P h0). Qed.
Lemma lem116202 : term22.
Proof. exact (fun P : nat -> Prop => @lem116197 P). Qed.
Lemma lem116203 : term21.
Proof. exact (EQ_MP (@lem115964) (@lem116202)). Qed.
Lemma lem116204 (P : nat -> Prop) : term54 P.
Proof. exact (@lem116203 P). Qed.
Lemma lem116205 (P : nat -> Prop) : (term54 P) = (term12 P).
Proof. exact (eq_refl (term54 P)). Qed.
Lemma lem116206 (P : nat -> Prop) : term12 P.
Proof. exact (EQ_MP (@lem116205 P) (@lem116204 P)). Qed.
Lemma lem116208 (P : nat -> Prop) : term12 P.
Proof. exact (@lem115839 P (@lem116206 P)). Qed.
Lemma lem116209 (P : nat -> Prop) (h1 : term13 P) : False.
Proof. exact (@lem116208 P (@lem115824 P h1)). Qed.
Lemma lem116210 (P : nat -> Prop) (h1 : term13 P) : (term13 P) = False.
Proof. exact (prop_ext (fun h2 : term13 P => @lem116209 P h1) (fun h2 : False => @lem115824 P h1)). Qed.
Lemma lem116211 (P : nat -> Prop) (h1 : term13 P) : False.
Proof. exact (EQ_MP (@lem116210 P h1) (@lem115824 P h1)). Qed.
Lemma lem116212 (P : nat -> Prop) : term12 P.
Proof. exact (fun h0 : term13 P => @lem116211 P h0). Qed.
Lemma lem116213 (P : nat -> Prop) : term11 P.
Proof. exact (EQ_MP (@lem115823 P) (@lem116212 P)). Qed.
Lemma lem116214 (P : nat -> Prop) : (term55 P) = (term56 P).
Proof. exact (@lem10568 (term31 P) (term24 P)). Qed.
Lemma lem116215 (P : nat -> Prop) : (term56 P) = (term55 P).
Proof. exact (SYM (@lem116214 P)). Qed.
Lemma lem116219 {A : Type'} (P : A -> Prop) : (term8 A P) = (term9 A P).
Proof. exact (EQ_MP (@lem115808 A P) (@lem115807 A P)). Qed.
Lemma lem116220 (P : nat -> Prop) : (term34 P) = (term43 P).
Proof. exact (@lem116219 nat P). Qed.
Lemma lem116221 (P : nat -> Prop) : (term57 P) = (term58 P).
Proof. exact (@lem116220 (term30 P)). Qed.
Lemma lem116222 (n : nat) (P : nat -> Prop) : (term59 P n) = (term29 n P).
Proof. exact (eq_refl (term59 P n)). Qed.
Lemma lem116223 (P : nat -> Prop) : (term60 P) = (term30 P).
Proof. exact (fun_ext (fun n : nat => @lem116222 n P)). Qed.
Lemma lem116224 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem116225 (P : nat -> Prop) : (term61 P) = (term31 P).
Proof. exact (MK_COMB (@lem116224) (@lem116223 P)). Qed.
Lemma lem116226 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem116227 (P : nat -> Prop) : (term57 P) = (term62 P).
Proof. exact (MK_COMB (@lem116226) (@lem116225 P)). Qed.
Lemma lem116228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem116229 (P : nat -> Prop) : (term63 P) = (term64 P).
Proof. exact (MK_COMB (@lem116228) (@lem116227 P)). Qed.
Lemma lem116230 (n : nat) (P : nat -> Prop) : (term59 P n) = (term29 n P).
Proof. exact (eq_refl (term59 P n)). Qed.
Lemma lem116231 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem116232 (n : nat) (P : nat -> Prop) : (term65 P n) = (term66 n P).
Proof. exact (MK_COMB (@lem116231) (@lem116230 n P)). Qed.
Lemma lem116233 (P : nat -> Prop) : (term67 P) = (term68 P).
Proof. exact (fun_ext (fun n : nat => @lem116232 n P)). Qed.
Lemma lem116234 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116235 (P : nat -> Prop) : (term58 P) = (term69 P).
Proof. exact (MK_COMB (@lem116234) (@lem116233 P)). Qed.
Lemma lem116236 (P : nat -> Prop) : ((term57 P) = (term58 P)) = ((term62 P) = (term69 P)).
Proof. exact (MK_COMB (@lem116229 P) (@lem116235 P)). Qed.
Lemma lem116237 (P : nat -> Prop) : (term62 P) = (term69 P).
Proof. exact (EQ_MP (@lem116236 P) (@lem116221 P)). Qed.
Lemma lem116250 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem116251 (P : nat -> Prop) : (term70 P) = (term71 P).
Proof. exact (MK_COMB (@lem116250) (@lem116237 P)). Qed.
Lemma lem116253 {A : Type'} (P : A -> Prop) : (term8 A P) = (term9 A P).
Proof. exact (EQ_MP (@lem115808 A P) (@lem115807 A P)). Qed.
Lemma lem116254 (P : nat -> Prop) : (term34 P) = (term43 P).
Proof. exact (@lem116253 nat P). Qed.
Lemma lem116259 (P : nat -> Prop) : (term56 P) = (term72 P).
Proof. exact (MK_COMB (@lem116251 P) (@lem116254 P)). Qed.
Lemma lem116262 (P : nat -> Prop) : (term72 P) = (term56 P).
Proof. exact (SYM (@lem116259 P)). Qed.
Lemma lem116263 (P : nat -> Prop) (h1 : term69 P) : term69 P.
Proof. exact (h1). Qed.
Lemma lem116265 (P : nat -> Prop) : term2 P.
Proof. exact (EQ_MP (@lem115805 P) (@lem115804 P)). Qed.
Lemma lem116266 (P : nat -> Prop) : term73 P.
Proof. exact (@lem116265 (term48 P)). Qed.
Lemma lem116267 (P : nat -> Prop) (m : nat) : (term49 P m) = (term36 P m).
Proof. exact (eq_refl (term49 P m)). Qed.
Lemma lem116268 (m : nat) (n : nat) : (term74 m n) = (term74 m n).
Proof. exact (eq_refl (term74 m n)). Qed.
Lemma lem116269 (n : nat) (P : nat -> Prop) (m : nat) : (term75 n P m) = (term25 n P m).
Proof. exact (MK_COMB (@lem116268 m n) (@lem116267 P m)). Qed.
Lemma lem116270 (n : nat) (P : nat -> Prop) : (term76 n P) = (term26 n P).
Proof. exact (fun_ext (fun m : nat => @lem116269 n P m)). Qed.
Lemma lem116271 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116272 (n : nat) (P : nat -> Prop) : (term77 n P) = (term27 n P).
Proof. exact (MK_COMB (@lem116271) (@lem116270 n P)). Qed.
Lemma lem116273 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem116274 (n : nat) (P : nat -> Prop) : (term78 n P) = (term79 n P).
Proof. exact (MK_COMB (@lem116273) (@lem116272 n P)). Qed.
Lemma lem116275 (P : nat -> Prop) (n : nat) : (term49 P n) = (term36 P n).
Proof. exact (eq_refl (term49 P n)). Qed.
Lemma lem116276 (P : nat -> Prop) (n : nat) : (term80 P n) = (term81 P n).
Proof. exact (MK_COMB (@lem116274 n P) (@lem116275 P n)). Qed.
Lemma lem116277 (P : nat -> Prop) : (term82 P) = (term83 P).
Proof. exact (fun_ext (fun n : nat => @lem116276 P n)). Qed.
Lemma lem116278 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116279 (P : nat -> Prop) : (term84 P) = (term85 P).
Proof. exact (MK_COMB (@lem116278) (@lem116277 P)). Qed.
Lemma lem116280 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem116281 (P : nat -> Prop) : (term86 P) = (term87 P).
Proof. exact (MK_COMB (@lem116280) (@lem116279 P)). Qed.
Lemma lem116282 (P : nat -> Prop) (n : nat) : (term49 P n) = (term36 P n).
Proof. exact (eq_refl (term49 P n)). Qed.
Lemma lem116283 (P : nat -> Prop) : (term88 P) = (term48 P).
Proof. exact (fun_ext (fun n : nat => @lem116282 P n)). Qed.
Lemma lem116284 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116285 (P : nat -> Prop) : (term89 P) = (term43 P).
Proof. exact (MK_COMB (@lem116284) (@lem116283 P)). Qed.
Lemma lem116286 (P : nat -> Prop) : (term73 P) = (term90 P).
Proof. exact (MK_COMB (@lem116281 P) (@lem116285 P)). Qed.
Lemma lem116287 (P : nat -> Prop) : term90 P.
Proof. exact (EQ_MP (@lem116286 P) (@lem116266 P)). Qed.
Lemma lem116289 (p : Prop) : p = (term10 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem116290 (P : nat -> Prop) : (term85 P) = (term91 P).
Proof. exact (@lem116289 (term85 P)). Qed.
Lemma lem116291 (P : nat -> Prop) : (term91 P) = (term85 P).
Proof. exact (SYM (@lem116290 P)). Qed.
Lemma lem116292 (P : nat -> Prop) (h1 : term92 P) : term92 P.
Proof. exact (h1). Qed.
Lemma lem116295 (P : nat -> Prop) (h1 : term93 P) : term93 P.
Proof. exact (h1). Qed.
Lemma lem116296 (P : nat -> Prop) : term94 P.
Proof. exact (fun h0 : term93 P => @lem116295 P h0). Qed.
Lemma lem116297 (P : nat -> Prop) (h1 : term94 P) : term94 P.
Proof. exact (h1). Qed.
Lemma lem116298 (P : nat -> Prop) (h1 : term93 P) : term93 P.
Proof. exact (h1). Qed.
Lemma lem116299 (P : nat -> Prop) (h1 : term93 P) (h2 : term94 P) : term93 P.
Proof. exact (@lem116297 P h2 (@lem116298 P h1)). Qed.
Lemma lem116300 (P : nat -> Prop) (h1 : term93 P) : term95 P.
Proof. exact (fun h0 : term94 P => @lem116299 P h1 h0). Qed.
Lemma lem116301 (P : nat -> Prop) (h1 : term94 P) : term94 P.
Proof. exact (h1). Qed.
Lemma lem116302 (P : nat -> Prop) (h1 : term93 P) (h2 : term94 P) : term93 P.
Proof. exact (@lem116300 P h1 (@lem116301 P h2)). Qed.
Lemma lem116303 (P : nat -> Prop) (h1 : term94 P) : term94 P.
Proof. exact (fun h0 : term93 P => @lem116302 P h0 h1). Qed.
Lemma lem116304 (P : nat -> Prop) : term96 P.
Proof. exact (fun h0 : term94 P => @lem116303 P h0). Qed.
Lemma lem116307 (P : nat -> Prop) : term94 P.
Proof. exact (@lem116304 P (@lem116296 P)). Qed.
Lemma lem116327 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem116328 (P : nat -> Prop) : (term91 P) = (term97 P).
Proof. exact (@lem116327 (term92 P)). Qed.
Lemma lem116330 (t : Prop) : (term18 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem116331 (P : nat -> Prop) : (term97 P) = (term85 P).
Proof. exact (@lem116330 (term85 P)). Qed.
Lemma lem116336 (P : nat -> Prop) : (term91 P) = (term85 P).
Proof. exact (TRANS (@lem116328 P) (@lem116331 P)). Qed.
Lemma lem116345 (P : nat -> Prop) : (term71 P) = (term71 P).
Proof. exact (eq_refl (term71 P)). Qed.
Lemma lem116346 (P : nat -> Prop) : (term93 P) = (term98 P).
Proof. exact (MK_COMB (@lem116345 P) (@lem116336 P)). Qed.
Lemma lem116349 : term99 = term100.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem116346 P)). Qed.
Lemma lem116350 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem116359 : term101 = term102.
Proof. exact (MK_COMB (@lem116350) (@lem116349)). Qed.
Lemma lem116362 (P : nat -> Prop) (n : nat) : (term36 P n) = (term36 P n).
Proof. exact (eq_refl (term36 P n)). Qed.
Lemma lem116369 (n : nat) (P : nat -> Prop) (m : nat) : (term25 n P m) = (term25 n P m).
Proof. exact (eq_refl (term25 n P m)). Qed.
Lemma lem116370 (n : nat) (P : nat -> Prop) : (term26 n P) = (term26 n P).
Proof. exact (fun_ext (fun m : nat => @lem116369 n P m)). Qed.
Lemma lem116371 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116372 (n : nat) (P : nat -> Prop) : (term27 n P) = (term27 n P).
Proof. exact (MK_COMB (@lem116371) (@lem116370 n P)). Qed.
Lemma lem116373 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem116374 (n : nat) (P : nat -> Prop) : (term79 n P) = (term79 n P).
Proof. exact (MK_COMB (@lem116373) (@lem116372 n P)). Qed.
Lemma lem116375 (P : nat -> Prop) (n : nat) : (term81 P n) = (term81 P n).
Proof. exact (MK_COMB (@lem116374 n P) (@lem116362 P n)). Qed.
Lemma lem116376 (P : nat -> Prop) : (term83 P) = (term83 P).
Proof. exact (fun_ext (fun n : nat => @lem116375 P n)). Qed.
Lemma lem116377 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116378 (P : nat -> Prop) : (term85 P) = (term85 P).
Proof. exact (MK_COMB (@lem116377) (@lem116376 P)). Qed.
Lemma lem116385 (n : nat) (P : nat -> Prop) (m : nat) : (term25 n P m) = (term25 n P m).
Proof. exact (eq_refl (term25 n P m)). Qed.
Lemma lem116386 (n : nat) (P : nat -> Prop) : (term26 n P) = (term26 n P).
Proof. exact (fun_ext (fun m : nat => @lem116385 n P m)). Qed.
Lemma lem116387 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116388 (n : nat) (P : nat -> Prop) : (term27 n P) = (term27 n P).
Proof. exact (MK_COMB (@lem116387) (@lem116386 n P)). Qed.
Lemma lem116391 (P : nat -> Prop) (n : nat) : (term28 P n) = (term28 P n).
Proof. exact (eq_refl (term28 P n)). Qed.
Lemma lem116392 (n : nat) (P : nat -> Prop) : (term29 n P) = (term29 n P).
Proof. exact (MK_COMB (@lem116391 P n) (@lem116388 n P)). Qed.
Lemma lem116393 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem116394 (n : nat) (P : nat -> Prop) : (term66 n P) = (term66 n P).
Proof. exact (MK_COMB (@lem116393) (@lem116392 n P)). Qed.
Lemma lem116395 (P : nat -> Prop) : (term68 P) = (term68 P).
Proof. exact (fun_ext (fun n : nat => @lem116394 n P)). Qed.
Lemma lem116396 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116397 (P : nat -> Prop) : (term69 P) = (term69 P).
Proof. exact (MK_COMB (@lem116396) (@lem116395 P)). Qed.
Lemma lem116398 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem116399 (P : nat -> Prop) : (term71 P) = (term71 P).
Proof. exact (MK_COMB (@lem116398) (@lem116397 P)). Qed.
Lemma lem116400 (P : nat -> Prop) : (term98 P) = (term98 P).
Proof. exact (MK_COMB (@lem116399 P) (@lem116378 P)). Qed.
Lemma lem116401 : term100 = term100.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem116400 P)). Qed.
Lemma lem116402 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem116403 : term102 = term102.
Proof. exact (MK_COMB (@lem116402) (@lem116401)). Qed.
Lemma lem116446 : term101 = term102.
Proof. exact (TRANS (@lem116359) (@lem116403)). Qed.
Lemma lem116447 : term102 = term101.
Proof. exact (SYM (@lem116446)). Qed.
Lemma lem116448 (P : nat -> Prop) (h1 : term69 P) : term69 P.
Proof. exact (h1). Qed.
Lemma lem116449 (n : nat) (P : nat -> Prop) (h1 : term27 n P) : term27 n P.
Proof. exact (h1). Qed.
Lemma lem116455 (P : nat -> Prop) (m : nat) : (term103 P m) = (P m).
Proof. exact (@lem16933 (P m)). Qed.
Lemma lem116457 (m : nat) (n : nat) : (term104 m n) = (term104 m n).
Proof. exact (eq_refl (term104 m n)). Qed.
Lemma lem116458 (n : nat) (P : nat -> Prop) (m : nat) : (term105 n P m) = (term106 n P m).
Proof. exact (MK_COMB (@lem116457 m n) (@lem116455 P m)). Qed.
Lemma lem116459 (n : nat) (P : nat -> Prop) (m : nat) : (term107 n P m) = (term105 n P m).
Proof. exact (@lem17362 (Peano.lt m n) (term36 P m)). Qed.
Lemma lem116460 (n : nat) (P : nat -> Prop) (m : nat) : (term107 n P m) = (term106 n P m).
Proof. exact (TRANS (@lem116459 n P m) (@lem116458 n P m)). Qed.
Lemma lem116461 (P : nat -> Prop) : (term108 P) = (term109 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem116462 (n : nat) (P : nat -> Prop) : (term110 n P) = (term111 n P).
Proof. exact (@lem116461 (term26 n P)). Qed.
Lemma lem116463 (n : nat) (P : nat -> Prop) (m : nat) : (term112 n P m) = (term25 n P m).
Proof. exact (eq_refl (term112 n P m)). Qed.
Lemma lem116464 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem116465 (n : nat) (P : nat -> Prop) (m : nat) : (term113 n P m) = (term107 n P m).
Proof. exact (MK_COMB (@lem116464) (@lem116463 n P m)). Qed.
Lemma lem116466 (n : nat) (P : nat -> Prop) (m : nat) : (term113 n P m) = (term106 n P m).
Proof. exact (TRANS (@lem116465 n P m) (@lem116460 n P m)). Qed.
Lemma lem116467 (n : nat) (P : nat -> Prop) : (term114 n P) = (term115 n P).
Proof. exact (fun_ext (fun m : nat => @lem116466 n P m)). Qed.
Lemma lem116468 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem116469 (n : nat) (P : nat -> Prop) : (term111 n P) = (term116 n P).
Proof. exact (MK_COMB (@lem116468) (@lem116467 n P)). Qed.
Lemma lem116470 (n : nat) (P : nat -> Prop) : (term110 n P) = (term116 n P).
Proof. exact (TRANS (@lem116462 n P) (@lem116469 n P)). Qed.
Lemma lem116472 (P : nat -> Prop) (n : nat) : (term117 P n) = (term117 P n).
Proof. exact (eq_refl (term117 P n)). Qed.
Lemma lem116473 (n : nat) (P : nat -> Prop) : (term118 n P) = (term119 n P).
Proof. exact (MK_COMB (@lem116472 P n) (@lem116470 n P)). Qed.
Lemma lem116474 (n : nat) (P : nat -> Prop) : (term66 n P) = (term118 n P).
Proof. exact (@lem17045 (P n) (term27 n P)). Qed.
Lemma lem116475 (n : nat) (P : nat -> Prop) : (term66 n P) = (term119 n P).
Proof. exact (TRANS (@lem116474 n P) (@lem116473 n P)). Qed.
Lemma lem116476 (P : nat -> Prop) : (term68 P) = (term120 P).
Proof. exact (fun_ext (fun n : nat => @lem116475 n P)). Qed.
Lemma lem116477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116478 (P : nat -> Prop) : (term69 P) = (term121 P).
Proof. exact (MK_COMB (@lem116477) (@lem116476 P)). Qed.
Lemma lem116561 {A : Type'} (P : Prop) (Q : A -> Prop) : (term122 A P Q) = (term123 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem116562 (P : Prop) (Q : nat -> Prop) : (term124 P Q) = (term125 P Q).
Proof. exact (@lem116561 nat P Q). Qed.
Lemma lem116563 (n : nat) (P : nat -> Prop) : (term126 n P) = (term127 n P).
Proof. exact (@lem116562 (term36 P n) (term115 n P)). Qed.
Lemma lem116564 (n : nat) (P : nat -> Prop) (m : nat) : (term128 n P m) = (term106 n P m).
Proof. exact (eq_refl (term128 n P m)). Qed.
Lemma lem116565 (n : nat) (P : nat -> Prop) : (term129 n P) = (term115 n P).
Proof. exact (fun_ext (fun m : nat => @lem116564 n P m)). Qed.
Lemma lem116566 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem116567 (n : nat) (P : nat -> Prop) : (term130 n P) = (term116 n P).
Proof. exact (MK_COMB (@lem116566) (@lem116565 n P)). Qed.
Lemma lem116568 (P : nat -> Prop) (n : nat) : (term117 P n) = (term117 P n).
Proof. exact (eq_refl (term117 P n)). Qed.
Lemma lem116569 (n : nat) (P : nat -> Prop) : (term126 n P) = (term119 n P).
Proof. exact (MK_COMB (@lem116568 P n) (@lem116567 n P)). Qed.
Lemma lem116570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem116571 (n : nat) (P : nat -> Prop) : (term131 n P) = (term132 n P).
Proof. exact (MK_COMB (@lem116570) (@lem116569 n P)). Qed.
Lemma lem116572 (n : nat) (P : nat -> Prop) (m : nat) : (term128 n P m) = (term106 n P m).
Proof. exact (eq_refl (term128 n P m)). Qed.
Lemma lem116573 (P : nat -> Prop) (n : nat) : (term117 P n) = (term117 P n).
Proof. exact (eq_refl (term117 P n)). Qed.
Lemma lem116574 (n : nat) (P : nat -> Prop) (m : nat) : (term133 n P m) = (term134 n P m).
Proof. exact (MK_COMB (@lem116573 P n) (@lem116572 n P m)). Qed.
Lemma lem116575 (n : nat) (P : nat -> Prop) : (term135 n P) = (term136 n P).
Proof. exact (fun_ext (fun m : nat => @lem116574 n P m)). Qed.
Lemma lem116576 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem116577 (n : nat) (P : nat -> Prop) : (term127 n P) = (term137 n P).
Proof. exact (MK_COMB (@lem116576) (@lem116575 n P)). Qed.
Lemma lem116578 (n : nat) (P : nat -> Prop) : ((term126 n P) = (term127 n P)) = ((term119 n P) = (term137 n P)).
Proof. exact (MK_COMB (@lem116571 n P) (@lem116577 n P)). Qed.
Lemma lem116579 (n : nat) (P : nat -> Prop) : (term119 n P) = (term137 n P).
Proof. exact (EQ_MP (@lem116578 n P) (@lem116563 n P)). Qed.
Lemma lem116580 (P : nat -> Prop) : (term120 P) = (term138 P).
Proof. exact (fun_ext (fun n : nat => @lem116579 n P)). Qed.
Lemma lem116581 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116582 (P : nat -> Prop) : (term121 P) = (term139 P).
Proof. exact (MK_COMB (@lem116581) (@lem116580 P)). Qed.
Lemma lem116584 {A B : Type'} (P : type1413 A B) : (term140 A B P) = (term141 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem116585 (P : type1605) : (term142 P) = (term143 P).
Proof. exact (@lem116584 nat nat P). Qed.
Lemma lem116586 (P : nat -> Prop) : (term144 P) = (term145 P).
Proof. exact (@lem116585 (term146 P)). Qed.
Lemma lem116587 (n : nat) (P : nat -> Prop) : (term147 P n) = (term136 n P).
Proof. exact (eq_refl (term147 P n)). Qed.
Lemma lem116588 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem116589 (n : nat) (P : nat -> Prop) (m : nat) : (term148 P n m) = (term149 n P m).
Proof. exact (MK_COMB (@lem116587 n P) (@lem116588 m)). Qed.
Lemma lem116590 (n : nat) (P : nat -> Prop) (m : nat) : (term149 n P m) = (term134 n P m).
Proof. exact (eq_refl (term149 n P m)). Qed.
Lemma lem116591 (n : nat) (P : nat -> Prop) (m : nat) : (term148 P n m) = (term134 n P m).
Proof. exact (TRANS (@lem116589 n P m) (@lem116590 n P m)). Qed.
Lemma lem116592 (n : nat) (P : nat -> Prop) : (term150 P n) = (term136 n P).
Proof. exact (fun_ext (fun m : nat => @lem116591 n P m)). Qed.
Lemma lem116593 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem116594 (n : nat) (P : nat -> Prop) : (term151 P n) = (term137 n P).
Proof. exact (MK_COMB (@lem116593) (@lem116592 n P)). Qed.
Lemma lem116595 (P : nat -> Prop) : (term152 P) = (term138 P).
Proof. exact (fun_ext (fun n : nat => @lem116594 n P)). Qed.
Lemma lem116596 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116597 (P : nat -> Prop) : (term144 P) = (term139 P).
Proof. exact (MK_COMB (@lem116596) (@lem116595 P)). Qed.
Lemma lem116598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem116599 (P : nat -> Prop) : (term153 P) = (term154 P).
Proof. exact (MK_COMB (@lem116598) (@lem116597 P)). Qed.
Lemma lem116600 (n : nat) (P : nat -> Prop) : (term147 P n) = (term136 n P).
Proof. exact (eq_refl (term147 P n)). Qed.
Lemma lem116601 (m : nat -> nat) (n : nat) : (m n) = (m n).
Proof. exact (eq_refl (m n)). Qed.
Lemma lem116602 (P : nat -> Prop) (m : nat -> nat) (n : nat) : (term155 P m n) = (term156 P m n).
Proof. exact (MK_COMB (@lem116600 n P) (@lem116601 m n)). Qed.
Lemma lem116603 (P : nat -> Prop) (m : nat -> nat) (n : nat) : (term156 P m n) = (term157 P m n).
Proof. exact (eq_refl (term156 P m n)). Qed.
Lemma lem116604 (P : nat -> Prop) (m : nat -> nat) (n : nat) : (term155 P m n) = (term157 P m n).
Proof. exact (TRANS (@lem116602 P m n) (@lem116603 P m n)). Qed.
Lemma lem116605 (P : nat -> Prop) (m : nat -> nat) : (term158 P m) = (term159 P m).
Proof. exact (fun_ext (fun n : nat => @lem116604 P m n)). Qed.
Lemma lem116606 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116607 (P : nat -> Prop) (m : nat -> nat) : (term160 P m) = (term161 P m).
Proof. exact (MK_COMB (@lem116606) (@lem116605 P m)). Qed.
Lemma lem116608 (P : nat -> Prop) : (term162 P) = (term163 P).
Proof. exact (fun_ext (fun m : nat -> nat => @lem116607 P m)). Qed.
Lemma lem116609 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem116610 (P : nat -> Prop) : (term145 P) = (term164 P).
Proof. exact (MK_COMB (@lem116609) (@lem116608 P)). Qed.
Lemma lem116611 (P : nat -> Prop) : ((term144 P) = (term145 P)) = ((term139 P) = (term164 P)).
Proof. exact (MK_COMB (@lem116599 P) (@lem116610 P)). Qed.
Lemma lem116612 (P : nat -> Prop) : (term139 P) = (term164 P).
Proof. exact (EQ_MP (@lem116611 P) (@lem116586 P)). Qed.
Lemma lem116614 (P : nat -> Prop) : (term121 P) = (term164 P).
Proof. exact (TRANS (@lem116582 P) (@lem116612 P)). Qed.
Lemma lem116615 (P : nat -> Prop) : (term69 P) = (term164 P).
Proof. exact (TRANS (@lem116478 P) (@lem116614 P)). Qed.
Lemma lem116616 (P : nat -> Prop) (h1 : term69 P) : term164 P.
Proof. exact (EQ_MP (@lem116615 P) (@lem116448 P h1)). Qed.
Lemma lem116623 (n : nat) (P : nat -> Prop) (m : nat) : (term25 n P m) = (term35 n P m).
Proof. exact (@lem17265 (Peano.lt m n) (term36 P m)). Qed.
Lemma lem116624 (n : nat) (P : nat -> Prop) : (term26 n P) = (term37 n P).
Proof. exact (fun_ext (fun m : nat => @lem116623 n P m)). Qed.
Lemma lem116625 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116678 (n : nat) (P : nat -> Prop) : (term27 n P) = (term38 n P).
Proof. exact (MK_COMB (@lem116625) (@lem116624 n P)). Qed.
Lemma lem116679 (n : nat) (P : nat -> Prop) (h1 : term27 n P) : term38 n P.
Proof. exact (EQ_MP (@lem116678 n P) (@lem116449 n P h1)). Qed.
Lemma lem116685 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem116686 (P : nat -> Prop) (m : nat -> nat) (h1 : term161 P m) : term161 P m.
Proof. exact (h1). Qed.
Lemma lem116701 (n : nat) (P : nat -> Prop) (m : nat) : (term35 n P m) = (term35 n P m).
Proof. exact (eq_refl (term35 n P m)). Qed.
Lemma lem116702 (n : nat) (P : nat -> Prop) : (term37 n P) = (term37 n P).
Proof. exact (fun_ext (fun m : nat => @lem116701 n P m)). Qed.
Lemma lem116703 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116704 (n : nat) (P : nat -> Prop) : (term38 n P) = (term38 n P).
Proof. exact (MK_COMB (@lem116703) (@lem116702 n P)). Qed.
Lemma lem116705 (n : nat) (P : nat -> Prop) (h1 : term27 n P) : term38 n P.
Proof. exact (EQ_MP (@lem116704 n P) (@lem116679 n P h1)). Qed.
Lemma lem116709 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem116732 (P : nat -> Prop) (m : nat -> nat) (n : nat) : (term157 P m n) = (term157 P m n).
Proof. exact (eq_refl (term157 P m n)). Qed.
Lemma lem116733 (P : nat -> Prop) (m : nat -> nat) : (term159 P m) = (term159 P m).
Proof. exact (fun_ext (fun n : nat => @lem116732 P m n)). Qed.
Lemma lem116734 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116735 (P : nat -> Prop) (m : nat -> nat) : (term161 P m) = (term161 P m).
Proof. exact (MK_COMB (@lem116734) (@lem116733 P m)). Qed.
Lemma lem116736 (P : nat -> Prop) (m : nat -> nat) (h1 : term161 P m) : term161 P m.
Proof. exact (EQ_MP (@lem116735 P m) (@lem116686 P m h1)). Qed.
Lemma lem116744 (n : nat) (P : nat -> Prop) (m : nat) : (term35 n P m) = (term35 n P m).
Proof. exact (eq_refl (term35 n P m)). Qed.
Lemma lem116745 (n : nat) (P : nat -> Prop) : (term37 n P) = (term37 n P).
Proof. exact (fun_ext (fun m : nat => @lem116744 n P m)). Qed.
Lemma lem116746 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116748 (n : nat) (P : nat -> Prop) : (term38 n P) = (term38 n P).
Proof. exact (MK_COMB (@lem116746) (@lem116745 n P)). Qed.
Lemma lem116749 (n : nat) (P : nat -> Prop) (h1 : term27 n P) : term38 n P.
Proof. exact (EQ_MP (@lem116748 n P) (@lem116705 n P h1)). Qed.
Lemma lem116753 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem116771 (P : nat -> Prop) (m : nat -> nat) (n : nat) : (term157 P m n) = (term165 P m n).
Proof. exact (@lem19490 (term166 m n) (term36 P n) (term167 P m n)). Qed.
Lemma lem116772 (P : nat -> Prop) (m : nat -> nat) : (term159 P m) = (term168 P m).
Proof. exact (fun_ext (fun n : nat => @lem116771 P m n)). Qed.
Lemma lem116773 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem116775 (P : nat -> Prop) (m : nat -> nat) : (term161 P m) = (term169 P m).
Proof. exact (MK_COMB (@lem116773) (@lem116772 P m)). Qed.
Lemma lem116776 (P : nat -> Prop) (m : nat -> nat) (h1 : term161 P m) : term169 P m.
Proof. exact (EQ_MP (@lem116775 P m) (@lem116736 P m h1)). Qed.
Lemma lem116777 (_2470 : nat) (n : nat) (P : nat -> Prop) (h1 : term27 n P) : term170 n P _2470.
Proof. exact (@lem116749 n P h1 _2470). Qed.
Lemma lem116778 (n : nat) (P : nat -> Prop) (_2470 : nat) : (term170 n P _2470) = (term35 n P _2470).
Proof. exact (eq_refl (term170 n P _2470)). Qed.
Lemma lem116780 (_2471 : nat) (P : nat -> Prop) (m : nat -> nat) (h1 : term161 P m) : term171 P m _2471.
Proof. exact (@lem116776 P m h1 _2471). Qed.
Lemma lem116781 (P : nat -> Prop) (m : nat -> nat) (_2471 : nat) : (term171 P m _2471) = (term165 P m _2471).
Proof. exact (eq_refl (term171 P m _2471)). Qed.
Lemma lem116782 (_2471 : nat) (P : nat -> Prop) (m : nat -> nat) (h1 : term161 P m) : term165 P m _2471.
Proof. exact (EQ_MP (@lem116781 P m _2471) (@lem116780 _2471 P m h1)). Qed.
Lemma lem116790 (_2470 : nat) (n : nat) (P : nat -> Prop) (h1 : term27 n P) : term35 n P _2470.
Proof. exact (EQ_MP (@lem116778 n P _2470) (@lem116777 _2470 n P h1)). Qed.
Lemma lem116792 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem116798 (_2471 : nat) (P : nat -> Prop) (m : nat -> nat) (h1 : term161 P m) : term172 P m _2471.
Proof. exact (proj1 (@lem116782 _2471 P m h1)). Qed.
Lemma lem116804 (_2471 : nat) (P : nat -> Prop) (m : nat -> nat) (h1 : term161 P m) : term173 P m _2471.
Proof. exact (proj2 (@lem116782 _2471 P m h1)). Qed.
Lemma lem116806 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem116807 (P : nat -> Prop) (n : nat) (h1 : P n) : term50 P n.
Proof. exact (fun h0 : term36 P n => @lem116806 P n h1). Qed.
Lemma lem116809 (p : Prop) : (term51 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem116810 (P : nat -> Prop) (n : nat) : (term50 P n) = (P n).
Proof. exact (@lem116809 (P n)). Qed.
Lemma lem116811 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (EQ_MP (@lem116810 P n) (@lem116807 P n h1)). Qed.
Lemma lem116817 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem116818 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : (term172 P m _2471) = (term174 m P _2471).
Proof. exact (@lem116817 (term166 m _2471) (term36 P _2471)). Qed.
Lemma lem116824 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem116825 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : (term175 P m _2471) = (term176 m P _2471).
Proof. exact (MK_COMB (@lem116824) (@lem116818 m P _2471)). Qed.
Lemma lem116831 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : (term174 m P _2471) = (term174 m P _2471).
Proof. exact (eq_refl (term174 m P _2471)). Qed.
Lemma lem116832 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : ((term172 P m _2471) = (term174 m P _2471)) = ((term174 m P _2471) = (term174 m P _2471)).
Proof. exact (MK_COMB (@lem116825 m P _2471) (@lem116831 m P _2471)). Qed.
Lemma lem116834 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem116835 (x : Prop) : (x = x) = True.
Proof. exact (@lem116834 Prop x). Qed.
Lemma lem116836 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : ((term174 m P _2471) = (term174 m P _2471)) = True.
Proof. exact (@lem116835 (term174 m P _2471)). Qed.
Lemma lem116837 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : ((term172 P m _2471) = (term174 m P _2471)) = True.
Proof. exact (TRANS (@lem116832 m P _2471) (@lem116836 m P _2471)). Qed.
Lemma lem116838 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : True = ((term172 P m _2471) = (term174 m P _2471)).
Proof. exact (SYM (@lem116837 m P _2471)). Qed.
Lemma lem116839 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : (term172 P m _2471) = (term174 m P _2471).
Proof. exact (EQ_MP (@lem116838 m P _2471) (@lem0)). Qed.
Lemma lem116840 (_2471 : nat) (P : nat -> Prop) (m : nat -> nat) (h1 : term161 P m) : term174 m P _2471.
Proof. exact (EQ_MP (@lem116839 m P _2471) (@lem116798 _2471 P m h1)). Qed.
Lemma lem116842 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem116843 (P : nat -> Prop) (m : nat -> nat) (_2471 : nat) : (term174 m P _2471) = (term178 P m _2471).
Proof. exact (@lem116842 (term36 P _2471) (term166 m _2471)). Qed.
Lemma lem116845 (a : Prop) : (term18 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem116846 (P : nat -> Prop) (_2471 : nat) : (term103 P _2471) = (P _2471).
Proof. exact (@lem116845 (P _2471)). Qed.
Lemma lem116847 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem116848 (P : nat -> Prop) (_2471 : nat) : (term179 P _2471) = (term180 P _2471).
Proof. exact (MK_COMB (@lem116847) (@lem116846 P _2471)). Qed.
Lemma lem116849 (m : nat -> nat) (_2471 : nat) : (term166 m _2471) = (term166 m _2471).
Proof. exact (eq_refl (term166 m _2471)). Qed.
Lemma lem116850 (P : nat -> Prop) (m : nat -> nat) (_2471 : nat) : (term178 P m _2471) = (term181 P m _2471).
Proof. exact (MK_COMB (@lem116848 P _2471) (@lem116849 m _2471)). Qed.
Lemma lem116851 (P : nat -> Prop) (m : nat -> nat) (_2471 : nat) : (term174 m P _2471) = (term181 P m _2471).
Proof. exact (TRANS (@lem116843 P m _2471) (@lem116850 P m _2471)). Qed.
Lemma lem116854 (_2471 : nat) (P : nat -> Prop) (m : nat -> nat) (h1 : term161 P m) : term181 P m _2471.
Proof. exact (EQ_MP (@lem116851 P m _2471) (@lem116840 _2471 P m h1)). Qed.
Lemma lem116855 (n : nat) (P : nat -> Prop) (m : nat -> nat) (h1 : term161 P m) : term181 P m n.
Proof. exact (@lem116854 n P m h1). Qed.
Lemma lem116858 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term161 P m) (h2 : P n) : term166 m n.
Proof. exact (@lem116855 n P m h1 (@lem116811 P n h2)). Qed.
Lemma lem116859 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term161 P m) (h2 : P n) : term182 m n.
Proof. exact (fun h0 : term183 m n => @lem116858 m P n h1 h2). Qed.
Lemma lem116861 (p : Prop) : (term51 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem116862 (m : nat -> nat) (n : nat) : (term182 m n) = (term166 m n).
Proof. exact (@lem116861 (term166 m n)). Qed.
Lemma lem116863 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term161 P m) (h2 : P n) : term166 m n.
Proof. exact (EQ_MP (@lem116862 m n) (@lem116859 m P n h1 h2)). Qed.
Lemma lem116865 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem116866 (P : nat -> Prop) (n : nat) (h1 : P n) : term50 P n.
Proof. exact (fun h0 : term36 P n => @lem116865 P n h1). Qed.
Lemma lem116868 (p : Prop) : (term51 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem116869 (P : nat -> Prop) (n : nat) : (term50 P n) = (P n).
Proof. exact (@lem116868 (P n)). Qed.
Lemma lem116870 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (EQ_MP (@lem116869 P n) (@lem116866 P n h1)). Qed.
Lemma lem116876 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem116877 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : (term173 P m _2471) = (term184 m P _2471).
Proof. exact (@lem116876 (term167 P m _2471) (term36 P _2471)). Qed.
Lemma lem116883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem116884 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : (term185 P m _2471) = (term186 m P _2471).
Proof. exact (MK_COMB (@lem116883) (@lem116877 m P _2471)). Qed.
Lemma lem116890 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : (term184 m P _2471) = (term184 m P _2471).
Proof. exact (eq_refl (term184 m P _2471)). Qed.
Lemma lem116891 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : ((term173 P m _2471) = (term184 m P _2471)) = ((term184 m P _2471) = (term184 m P _2471)).
Proof. exact (MK_COMB (@lem116884 m P _2471) (@lem116890 m P _2471)). Qed.
Lemma lem116893 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem116894 (x : Prop) : (x = x) = True.
Proof. exact (@lem116893 Prop x). Qed.
Lemma lem116895 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : ((term184 m P _2471) = (term184 m P _2471)) = True.
Proof. exact (@lem116894 (term184 m P _2471)). Qed.
Lemma lem116896 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : ((term173 P m _2471) = (term184 m P _2471)) = True.
Proof. exact (TRANS (@lem116891 m P _2471) (@lem116895 m P _2471)). Qed.
Lemma lem116897 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : True = ((term173 P m _2471) = (term184 m P _2471)).
Proof. exact (SYM (@lem116896 m P _2471)). Qed.
Lemma lem116898 (m : nat -> nat) (P : nat -> Prop) (_2471 : nat) : (term173 P m _2471) = (term184 m P _2471).
Proof. exact (EQ_MP (@lem116897 m P _2471) (@lem0)). Qed.
Lemma lem116899 (_2471 : nat) (P : nat -> Prop) (m : nat -> nat) (h1 : term161 P m) : term184 m P _2471.
Proof. exact (EQ_MP (@lem116898 m P _2471) (@lem116804 _2471 P m h1)). Qed.
Lemma lem116901 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem116902 (P : nat -> Prop) (m : nat -> nat) (_2471 : nat) : (term184 m P _2471) = (term187 P m _2471).
Proof. exact (@lem116901 (term36 P _2471) (term167 P m _2471)). Qed.
Lemma lem116904 (a : Prop) : (term18 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem116905 (P : nat -> Prop) (_2471 : nat) : (term103 P _2471) = (P _2471).
Proof. exact (@lem116904 (P _2471)). Qed.
Lemma lem116906 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem116907 (P : nat -> Prop) (_2471 : nat) : (term179 P _2471) = (term180 P _2471).
Proof. exact (MK_COMB (@lem116906) (@lem116905 P _2471)). Qed.
Lemma lem116908 (P : nat -> Prop) (m : nat -> nat) (_2471 : nat) : (term167 P m _2471) = (term167 P m _2471).
Proof. exact (eq_refl (term167 P m _2471)). Qed.
Lemma lem116909 (P : nat -> Prop) (m : nat -> nat) (_2471 : nat) : (term187 P m _2471) = (term188 P m _2471).
Proof. exact (MK_COMB (@lem116907 P _2471) (@lem116908 P m _2471)). Qed.
Lemma lem116910 (P : nat -> Prop) (m : nat -> nat) (_2471 : nat) : (term184 m P _2471) = (term188 P m _2471).
Proof. exact (TRANS (@lem116902 P m _2471) (@lem116909 P m _2471)). Qed.
Lemma lem116913 (_2471 : nat) (P : nat -> Prop) (m : nat -> nat) (h1 : term161 P m) : term188 P m _2471.
Proof. exact (EQ_MP (@lem116910 P m _2471) (@lem116899 _2471 P m h1)). Qed.
Lemma lem116914 (n : nat) (P : nat -> Prop) (m : nat -> nat) (h1 : term161 P m) : term188 P m n.
Proof. exact (@lem116913 n P m h1). Qed.
Lemma lem116917 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term161 P m) (h2 : P n) : term167 P m n.
Proof. exact (@lem116914 n P m h1 (@lem116870 P n h2)). Qed.
Lemma lem116918 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term161 P m) (h2 : P n) : term189 P m n.
Proof. exact (fun h0 : term190 P m n => @lem116917 m P n h1 h2). Qed.
Lemma lem116920 (p : Prop) : (term51 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem116921 (P : nat -> Prop) (m : nat -> nat) (n : nat) : (term189 P m n) = (term167 P m n).
Proof. exact (@lem116920 (term167 P m n)). Qed.
Lemma lem116922 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term161 P m) (h2 : P n) : term167 P m n.
Proof. exact (EQ_MP (@lem116921 P m n) (@lem116918 m P n h1 h2)). Qed.
Lemma lem116924 (a : Prop) (b : Prop) : (term191 a b) = (term192 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem116925 (n : nat) (P : nat -> Prop) (_2470 : nat) : (term35 n P _2470) = (term193 n P _2470).
Proof. exact (@lem116924 (Peano.lt _2470 n) (P _2470)). Qed.
Lemma lem116927 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem116928 (n : nat) (P : nat -> Prop) (_2470 : nat) : (term193 n P _2470) = (term194 n P _2470).
Proof. exact (@lem116927 (term106 n P _2470)). Qed.
Lemma lem116929 (n : nat) (P : nat -> Prop) (_2470 : nat) : (term35 n P _2470) = (term194 n P _2470).
Proof. exact (TRANS (@lem116925 n P _2470) (@lem116928 n P _2470)). Qed.
Lemma lem116931 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term161 P m) (h2 : P n) : term195 P m n.
Proof. exact (conj (@lem116863 m P n h1 h2) (@lem116922 m P n h1 h2)). Qed.
Lemma lem116933 (_2470 : nat) (n : nat) (P : nat -> Prop) (h1 : term27 n P) : term194 n P _2470.
Proof. exact (EQ_MP (@lem116929 n P _2470) (@lem116790 _2470 n P h1)). Qed.
Lemma lem116934 (m : nat -> nat) (n : nat) (P : nat -> Prop) (h1 : term27 n P) : term196 P m n.
Proof. exact (@lem116933 (m n) n P h1). Qed.
Lemma lem116937 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term27 n P) (h2 : term161 P m) (h3 : P n) : False.
Proof. exact (@lem116934 m n P h1 (@lem116931 m P n h2 h3)). Qed.
Lemma lem116938 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term27 n P) (h2 : term161 P m) (h3 : P n) : term53.
Proof. exact (fun h0 : ~ False => @lem116937 m P n h1 h2 h3). Qed.
Lemma lem116940 (p : Prop) : (term51 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem116941 : term53 = False.
Proof. exact (@lem116940 False). Qed.
Lemma lem116942 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term27 n P) (h2 : term161 P m) (h3 : P n) : False.
Proof. exact (EQ_MP (@lem116941) (@lem116938 m P n h1 h2 h3)). Qed.
Lemma lem116943 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term27 n P) (h2 : term161 P m) (h3 : P n) : (P n) = False.
Proof. exact (prop_ext (fun h4 : P n => @lem116942 m P n h1 h2 h3) (fun h4 : False => @lem116792 P n h3)). Qed.
Lemma lem116944 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term27 n P) (h2 : term161 P m) (h3 : P n) : False.
Proof. exact (EQ_MP (@lem116943 m P n h1 h2 h3) (@lem116792 P n h3)). Qed.
Lemma lem116945 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term27 n P) (h2 : term161 P m) (h3 : P n) : (P n) = False.
Proof. exact (prop_ext (fun h4 : P n => @lem116944 m P n h1 h2 h3) (fun h4 : False => @lem116753 P n h3)). Qed.
Lemma lem116946 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term27 n P) (h2 : term161 P m) (h3 : P n) : False.
Proof. exact (EQ_MP (@lem116945 m P n h1 h2 h3) (@lem116753 P n h3)). Qed.
Lemma lem116947 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term27 n P) (h2 : term161 P m) (h3 : P n) : (P n) = False.
Proof. exact (prop_ext (fun h4 : P n => @lem116946 m P n h1 h2 h3) (fun h4 : False => @lem116753 P n h3)). Qed.
Lemma lem116948 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term27 n P) (h2 : term161 P m) (h3 : P n) : False.
Proof. exact (EQ_MP (@lem116947 m P n h1 h2 h3) (@lem116753 P n h3)). Qed.
Lemma lem116949 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term27 n P) (h2 : term161 P m) (h3 : P n) : (term161 P m) = False.
Proof. exact (prop_ext (fun h4 : term161 P m => @lem116948 m P n h1 h2 h3) (fun h4 : False => @lem116736 P m h2)). Qed.
Lemma lem116950 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term27 n P) (h2 : term161 P m) (h3 : P n) : False.
Proof. exact (EQ_MP (@lem116949 m P n h1 h2 h3) (@lem116736 P m h2)). Qed.
Lemma lem116951 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term27 n P) (h2 : term161 P m) (h3 : P n) : (P n) = False.
Proof. exact (prop_ext (fun h4 : P n => @lem116950 m P n h1 h2 h3) (fun h4 : False => @lem116709 P n h3)). Qed.
Lemma lem116952 (m : nat -> nat) (P : nat -> Prop) (n : nat) (h1 : term27 n P) (h2 : term161 P m) (h3 : P n) : False.
Proof. exact (EQ_MP (@lem116951 m P n h1 h2 h3) (@lem116709 P n h3)). Qed.
Lemma lem116953 (P : nat -> Prop) (n : nat) (h1 : term69 P) (h2 : term27 n P) (h3 : P n) : False.
Proof. exact (ex_elim (@lem116616 P h1) (fun m : nat -> nat => fun h0 : term163 P m => @lem116952 m P n h2 h0 h3)). Qed.
Lemma lem116954 (P : nat -> Prop) (n : nat) (h1 : term69 P) (h2 : term27 n P) (h3 : P n) : (P n) = False.
Proof. exact (prop_ext (fun h4 : P n => @lem116953 P n h1 h2 h3) (fun h4 : False => @lem116685 P n h3)). Qed.
Lemma lem116955 (P : nat -> Prop) (n : nat) (h1 : term69 P) (h2 : term27 n P) (h3 : P n) : False.
Proof. exact (EQ_MP (@lem116954 P n h1 h2 h3) (@lem116685 P n h3)). Qed.
Lemma lem116956 (n : nat) (P : nat -> Prop) (h1 : term69 P) (h2 : term27 n P) : term52 P n.
Proof. exact (fun h0 : P n => @lem116955 P n h1 h2 h0). Qed.
Lemma lem116957 (P : nat -> Prop) (n : nat) : (term52 P n) = (term36 P n).
Proof. exact (@lem69 (P n)). Qed.
Lemma lem116958 (n : nat) (P : nat -> Prop) (h1 : term69 P) (h2 : term27 n P) : term36 P n.
Proof. exact (EQ_MP (@lem116957 P n) (@lem116956 n P h1 h2)). Qed.
Lemma lem116959 (n : nat) (P : nat -> Prop) (h1 : term69 P) : term81 P n.
Proof. exact (fun h0 : term27 n P => @lem116958 n P h1 h0). Qed.
Lemma lem116964 (P : nat -> Prop) (h1 : term69 P) : term85 P.
Proof. exact (fun n : nat => @lem116959 n P h1). Qed.
Lemma lem116965 (P : nat -> Prop) : term98 P.
Proof. exact (fun h0 : term69 P => @lem116964 P h0). Qed.
Lemma lem116970 : term102.
Proof. exact (fun P : nat -> Prop => @lem116965 P). Qed.
Lemma lem116971 : term101.
Proof. exact (EQ_MP (@lem116447) (@lem116970)). Qed.
Lemma lem116972 (P : nat -> Prop) : term197 P.
Proof. exact (@lem116971 P). Qed.
Lemma lem116973 (P : nat -> Prop) : (term197 P) = (term93 P).
Proof. exact (eq_refl (term197 P)). Qed.
Lemma lem116974 (P : nat -> Prop) : term93 P.
Proof. exact (EQ_MP (@lem116973 P) (@lem116972 P)). Qed.
Lemma lem116976 (P : nat -> Prop) : term93 P.
Proof. exact (@lem116307 P (@lem116974 P)). Qed.
Lemma lem116977 (P : nat -> Prop) (h1 : term69 P) : term91 P.
Proof. exact (@lem116976 P (@lem116263 P h1)). Qed.
Lemma lem116978 (P : nat -> Prop) (h1 : term69 P) (h2 : term92 P) : False.
Proof. exact (@lem116977 P h1 (@lem116292 P h2)). Qed.
Lemma lem116979 (P : nat -> Prop) (h1 : term69 P) (h2 : term92 P) : (term92 P) = False.
Proof. exact (prop_ext (fun h3 : term92 P => @lem116978 P h1 h2) (fun h3 : False => @lem116292 P h2)). Qed.
Lemma lem116980 (P : nat -> Prop) (h1 : term69 P) (h2 : term92 P) : False.
Proof. exact (EQ_MP (@lem116979 P h1 h2) (@lem116292 P h2)). Qed.
Lemma lem116981 (P : nat -> Prop) (h1 : term69 P) : term91 P.
Proof. exact (fun h0 : term92 P => @lem116980 P h1 h0). Qed.
Lemma lem116982 (P : nat -> Prop) (h1 : term69 P) : term85 P.
Proof. exact (EQ_MP (@lem116291 P) (@lem116981 P h1)). Qed.
Lemma lem116983 (P : nat -> Prop) (h1 : term69 P) : term43 P.
Proof. exact (@lem116287 P (@lem116982 P h1)). Qed.
Lemma lem116984 (P : nat -> Prop) : term72 P.
Proof. exact (fun h0 : term69 P => @lem116983 P h0). Qed.
Lemma lem116985 (P : nat -> Prop) : term56 P.
Proof. exact (EQ_MP (@lem116262 P) (@lem116984 P)). Qed.
Lemma lem116986 (P : nat -> Prop) : term55 P.
Proof. exact (EQ_MP (@lem116215 P) (@lem116985 P)). Qed.
Lemma lem116987 (P : nat -> Prop) : term198 P.
Proof. exact (conj (@lem116986 P) (@lem116213 P)). Qed.
Lemma lem116988 (P : nat -> Prop) : (term198 P) = ((term24 P) = (term31 P)).
Proof. exact (@lem32 (term24 P) (term31 P)). Qed.
Lemma lem116989 (P : nat -> Prop) : (term24 P) = (term31 P).
Proof. exact (EQ_MP (@lem116988 P) (@lem116987 P)). Qed.
Lemma lem116994 : term199.
Proof. exact (fun P : nat -> Prop => @lem116989 P). Qed.
