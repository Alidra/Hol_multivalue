Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5413112_term_abbrevs.
Require Import INT_POS_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367767_spec.
Require Import thm1367770_spec.
Require Import thm1367771_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm2841416_spec.
Require Import thm2841417_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem5405887 (m : nat) (x : nat) (n : nat) : ((term0 m x n) = (term1 m x n)) = ((term0 m x n) = (term1 m x n)).
Proof. exact (eq_refl ((term0 m x n) = (term1 m x n))). Qed.
Lemma lem5405888 (m : nat) (n : nat) : (term2 m n) = (term2 m n).
Proof. exact (fun_ext (fun x : nat => @lem5405887 m x n)). Qed.
Lemma lem5405889 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5405890 (m : nat) (n : nat) : (term3 m n) = (term3 m n).
Proof. exact (MK_COMB (@lem5405889) (@lem5405888 m n)). Qed.
Lemma lem5405893 (m : nat) (n : nat) : (term4 m n) = (term4 m n).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem5405895 (m : nat) (n : nat) : (term5 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem5405893 m n) (@lem5405890 m n)). Qed.
Lemma lem5405905 (m : nat) (x : nat) (n : nat) : (term6 m x n) = (term7 m x n).
Proof. exact (@lem17045 (Peano.le m x) (term8 x n)). Qed.
Lemma lem5405919 (m : nat) (x : nat) (n : nat) : (term9 m x n) = (term10 m x n).
Proof. exact (@lem17045 (Peano.le m x) (Peano.le x n)). Qed.
Lemma lem5405924 (x : nat) (n : nat) : (term11 x n) = (term11 x n).
Proof. exact (eq_refl (term11 x n)). Qed.
Lemma lem5405925 (m : nat) (x : nat) (n : nat) : (term12 m x n) = (term13 m x n).
Proof. exact (MK_COMB (@lem5405924 x n) (@lem5405919 m x n)). Qed.
Lemma lem5405926 (m : nat) (x : nat) (n : nat) : (term14 m x n) = (term12 m x n).
Proof. exact (@lem17160 (x = (S n)) (term15 m x n)). Qed.
Lemma lem5405927 (m : nat) (x : nat) (n : nat) : (term14 m x n) = (term13 m x n).
Proof. exact (TRANS (@lem5405926 m x n) (@lem5405925 m x n)). Qed.
Lemma lem5405930 (m : nat) (x : nat) (n : nat) : (term1 m x n) = (term1 m x n).
Proof. exact (eq_refl (term1 m x n)). Qed.
Lemma lem5405931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5405932 (m : nat) (x : nat) (n : nat) : (term16 m x n) = (term17 m x n).
Proof. exact (MK_COMB (@lem5405931) (@lem5405905 m x n)). Qed.
Lemma lem5405933 (m : nat) (x : nat) (n : nat) : (term18 m x n) = (term19 m x n).
Proof. exact (MK_COMB (@lem5405932 m x n) (@lem5405930 m x n)). Qed.
Lemma lem5405935 (m : nat) (x : nat) (n : nat) : (term20 m x n) = (term20 m x n).
Proof. exact (eq_refl (term20 m x n)). Qed.
Lemma lem5405936 (m : nat) (x : nat) (n : nat) : (term21 m x n) = (term22 m x n).
Proof. exact (MK_COMB (@lem5405935 m x n) (@lem5405927 m x n)). Qed.
Lemma lem5405937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5405938 (m : nat) (x : nat) (n : nat) : (term23 m x n) = (term24 m x n).
Proof. exact (MK_COMB (@lem5405937) (@lem5405936 m x n)). Qed.
Lemma lem5405939 (m : nat) (x : nat) (n : nat) : (term25 m x n) = (term26 m x n).
Proof. exact (MK_COMB (@lem5405938 m x n) (@lem5405933 m x n)). Qed.
Lemma lem5405940 (m : nat) (x : nat) (n : nat) : ((term0 m x n) = (term1 m x n)) = (term25 m x n).
Proof. exact (@lem17784 (term0 m x n) (term1 m x n)). Qed.
Lemma lem5405941 (m : nat) (x : nat) (n : nat) : ((term0 m x n) = (term1 m x n)) = (term26 m x n).
Proof. exact (TRANS (@lem5405940 m x n) (@lem5405939 m x n)). Qed.
Lemma lem5405942 (m : nat) (n : nat) : (term2 m n) = (term27 m n).
Proof. exact (fun_ext (fun x : nat => @lem5405941 m x n)). Qed.
Lemma lem5405943 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5405944 (m : nat) (n : nat) : (term3 m n) = (term28 m n).
Proof. exact (MK_COMB (@lem5405943) (@lem5405942 m n)). Qed.
Lemma lem5405946 (m : nat) (n : nat) : (term29 m n) = (term29 m n).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem5405947 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem5405946 m n) (@lem5405944 m n)). Qed.
Lemma lem5405948 (m : nat) (n : nat) : (term5 m n) = (term30 m n).
Proof. exact (@lem17265 (term8 m n) (term3 m n)). Qed.
Lemma lem5405949 (m : nat) (n : nat) : (term5 m n) = (term31 m n).
Proof. exact (TRANS (@lem5405948 m n) (@lem5405947 m n)). Qed.
Lemma lem5405950 (m : nat) (n : nat) : (term5 m n) = (term31 m n).
Proof. exact (TRANS (@lem5405895 m n) (@lem5405949 m n)). Qed.
Lemma lem5405951 (m : nat) (x : nat) (n : nat) : (term26 m x n) = (term26 m x n).
Proof. exact (eq_refl (term26 m x n)). Qed.
Lemma lem5405952 (m : nat) (n : nat) : (term27 m n) = (term27 m n).
Proof. exact (fun_ext (fun x : nat => @lem5405951 m x n)). Qed.
Lemma lem5405953 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5405954 (m : nat) (n : nat) : (term28 m n) = (term28 m n).
Proof. exact (MK_COMB (@lem5405953) (@lem5405952 m n)). Qed.
Lemma lem5405957 (m : nat) (n : nat) : (term29 m n) = (term29 m n).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem5405958 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem5405957 m n) (@lem5405954 m n)). Qed.
Lemma lem5405991 (m : nat) (n : nat) : (term5 m n) = (term31 m n).
Proof. exact (TRANS (@lem5405950 m n) (@lem5405958 m n)). Qed.
Lemma lem5405993 (m : nat) : (S m) = (term32 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem5405994 (n : nat) : (S n) = (term32 n).
Proof. exact (@lem5405993 n). Qed.
Lemma lem5405995 (m : nat) : (Peano.le m) = (Peano.le m).
Proof. exact (eq_refl (Peano.le m)). Qed.
Lemma lem5405996 (m : nat) (n : nat) : (term8 m n) = (term33 m n).
Proof. exact (MK_COMB (@lem5405995 m) (@lem5405994 n)). Qed.
Lemma lem5405997 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5405998 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem5405997) (@lem5405996 m n)). Qed.
Lemma lem5405999 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406000 (m : nat) (n : nat) : (term29 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem5405999) (@lem5405998 m n)). Qed.
Lemma lem5406002 (m : nat) : (S m) = (term32 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem5406003 (n : nat) : (S n) = (term32 n).
Proof. exact (@lem5406002 n). Qed.
Lemma lem5406004 (x : nat) : (Peano.le x) = (Peano.le x).
Proof. exact (eq_refl (Peano.le x)). Qed.
Lemma lem5406005 (x : nat) (n : nat) : (term8 x n) = (term33 x n).
Proof. exact (MK_COMB (@lem5406004 x) (@lem5406003 n)). Qed.
Lemma lem5406006 (m : nat) (x : nat) : (term37 m x) = (term37 m x).
Proof. exact (eq_refl (term37 m x)). Qed.
Lemma lem5406007 (m : nat) (x : nat) (n : nat) : (term0 m x n) = (term38 m x n).
Proof. exact (MK_COMB (@lem5406006 m x) (@lem5406005 x n)). Qed.
Lemma lem5406008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406009 (m : nat) (x : nat) (n : nat) : (term20 m x n) = (term39 m x n).
Proof. exact (MK_COMB (@lem5406008) (@lem5406007 m x n)). Qed.
Lemma lem5406011 (m : nat) : (S m) = (term32 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem5406012 (n : nat) : (S n) = (term32 n).
Proof. exact (@lem5406011 n). Qed.
Lemma lem5406013 (x : nat) : (@eq nat x) = (@eq nat x).
Proof. exact (eq_refl (@eq nat x)). Qed.
Lemma lem5406014 (x : nat) (n : nat) : (x = (S n)) = (x = (term32 n)).
Proof. exact (MK_COMB (@lem5406013 x) (@lem5406012 n)). Qed.
Lemma lem5406015 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5406016 (x : nat) (n : nat) : (term40 x n) = (term41 x n).
Proof. exact (MK_COMB (@lem5406015) (@lem5406014 x n)). Qed.
Lemma lem5406017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406018 (x : nat) (n : nat) : (term11 x n) = (term42 x n).
Proof. exact (MK_COMB (@lem5406017) (@lem5406016 x n)). Qed.
Lemma lem5406019 (m : nat) (x : nat) (n : nat) : (term10 m x n) = (term10 m x n).
Proof. exact (eq_refl (term10 m x n)). Qed.
Lemma lem5406020 (m : nat) (x : nat) (n : nat) : (term13 m x n) = (term43 m x n).
Proof. exact (MK_COMB (@lem5406018 x n) (@lem5406019 m x n)). Qed.
Lemma lem5406021 (m : nat) (x : nat) (n : nat) : (term22 m x n) = (term44 m x n).
Proof. exact (MK_COMB (@lem5406009 m x n) (@lem5406020 m x n)). Qed.
Lemma lem5406022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406023 (m : nat) (x : nat) (n : nat) : (term24 m x n) = (term45 m x n).
Proof. exact (MK_COMB (@lem5406022) (@lem5406021 m x n)). Qed.
Lemma lem5406025 (m : nat) : (S m) = (term32 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem5406026 (n : nat) : (S n) = (term32 n).
Proof. exact (@lem5406025 n). Qed.
Lemma lem5406027 (x : nat) : (Peano.le x) = (Peano.le x).
Proof. exact (eq_refl (Peano.le x)). Qed.
Lemma lem5406028 (x : nat) (n : nat) : (term8 x n) = (term33 x n).
Proof. exact (MK_COMB (@lem5406027 x) (@lem5406026 n)). Qed.
Lemma lem5406029 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5406030 (x : nat) (n : nat) : (term34 x n) = (term35 x n).
Proof. exact (MK_COMB (@lem5406029) (@lem5406028 x n)). Qed.
Lemma lem5406031 (m : nat) (x : nat) : (term46 m x) = (term46 m x).
Proof. exact (eq_refl (term46 m x)). Qed.
Lemma lem5406032 (m : nat) (x : nat) (n : nat) : (term7 m x n) = (term47 m x n).
Proof. exact (MK_COMB (@lem5406031 m x) (@lem5406030 x n)). Qed.
Lemma lem5406033 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406034 (m : nat) (x : nat) (n : nat) : (term17 m x n) = (term48 m x n).
Proof. exact (MK_COMB (@lem5406033) (@lem5406032 m x n)). Qed.
Lemma lem5406036 (m : nat) : (S m) = (term32 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem5406037 (n : nat) : (S n) = (term32 n).
Proof. exact (@lem5406036 n). Qed.
Lemma lem5406038 (x : nat) : (@eq nat x) = (@eq nat x).
Proof. exact (eq_refl (@eq nat x)). Qed.
Lemma lem5406039 (x : nat) (n : nat) : (x = (S n)) = (x = (term32 n)).
Proof. exact (MK_COMB (@lem5406038 x) (@lem5406037 n)). Qed.
Lemma lem5406040 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406041 (x : nat) (n : nat) : (term49 x n) = (term50 x n).
Proof. exact (MK_COMB (@lem5406040) (@lem5406039 x n)). Qed.
Lemma lem5406042 (m : nat) (x : nat) (n : nat) : (term15 m x n) = (term15 m x n).
Proof. exact (eq_refl (term15 m x n)). Qed.
Lemma lem5406043 (m : nat) (x : nat) (n : nat) : (term1 m x n) = (term51 m x n).
Proof. exact (MK_COMB (@lem5406041 x n) (@lem5406042 m x n)). Qed.
Lemma lem5406044 (m : nat) (x : nat) (n : nat) : (term19 m x n) = (term52 m x n).
Proof. exact (MK_COMB (@lem5406034 m x n) (@lem5406043 m x n)). Qed.
Lemma lem5406045 (m : nat) (x : nat) (n : nat) : (term26 m x n) = (term53 m x n).
Proof. exact (MK_COMB (@lem5406023 m x n) (@lem5406044 m x n)). Qed.
Lemma lem5406046 (m : nat) (n : nat) : (term27 m n) = (term54 m n).
Proof. exact (fun_ext (fun x : nat => @lem5406045 m x n)). Qed.
Lemma lem5406047 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5406048 (m : nat) (n : nat) : (term28 m n) = (term55 m n).
Proof. exact (MK_COMB (@lem5406047) (@lem5406046 m n)). Qed.
Lemma lem5406049 (m : nat) (n : nat) : (term31 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem5406000 m n) (@lem5406048 m n)). Qed.
Lemma lem5406050 (m : nat) (n : nat) : (term5 m n) = (term56 m n).
Proof. exact (TRANS (@lem5405991 m n) (@lem5406049 m n)). Qed.
Lemma lem5406161 (m : nat) (x : nat) (n : nat) : (term53 m x n) = (term53 m x n).
Proof. exact (eq_refl (term53 m x n)). Qed.
Lemma lem5406162 (m : nat) (n : nat) : (term54 m n) = (term54 m n).
Proof. exact (fun_ext (fun x : nat => @lem5406161 m x n)). Qed.
Lemma lem5406163 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5406164 (m : nat) (n : nat) : (term55 m n) = (term55 m n).
Proof. exact (MK_COMB (@lem5406163) (@lem5406162 m n)). Qed.
Lemma lem5406179 (m : nat) (n : nat) : (term36 m n) = (term36 m n).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem5406180 (m : nat) (n : nat) : (term56 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem5406179 m n) (@lem5406164 m n)). Qed.
Lemma lem5406181 (m : nat) (n : nat) : (term5 m n) = (term56 m n).
Proof. exact (TRANS (@lem5406050 m n) (@lem5406180 m n)). Qed.
Lemma lem5406183 {A : Type'} (P : Prop) (Q : A -> Prop) : (term57 A P Q) = (term58 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5406184 (P : Prop) (Q : nat -> Prop) : (term59 P Q) = (term60 P Q).
Proof. exact (@lem5406183 nat P Q). Qed.
Lemma lem5406185 (m : nat) (n : nat) : (term61 m n) = (term62 m n).
Proof. exact (@lem5406184 (term35 m n) (term54 m n)). Qed.
Lemma lem5406186 (m : nat) (x : nat) (n : nat) : (term63 m n x) = (term53 m x n).
Proof. exact (eq_refl (term63 m n x)). Qed.
Lemma lem5406187 (m : nat) (n : nat) : (term64 m n) = (term54 m n).
Proof. exact (fun_ext (fun x : nat => @lem5406186 m x n)). Qed.
Lemma lem5406188 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5406189 (m : nat) (n : nat) : (term65 m n) = (term55 m n).
Proof. exact (MK_COMB (@lem5406188) (@lem5406187 m n)). Qed.
Lemma lem5406190 (m : nat) (n : nat) : (term36 m n) = (term36 m n).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem5406191 (m : nat) (n : nat) : (term61 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem5406190 m n) (@lem5406189 m n)). Qed.
Lemma lem5406192 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5406193 (m : nat) (n : nat) : (term66 m n) = (term67 m n).
Proof. exact (MK_COMB (@lem5406192) (@lem5406191 m n)). Qed.
Lemma lem5406194 (m : nat) (x : nat) (n : nat) : (term63 m n x) = (term53 m x n).
Proof. exact (eq_refl (term63 m n x)). Qed.
Lemma lem5406195 (m : nat) (n : nat) : (term36 m n) = (term36 m n).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem5406196 (m : nat) (x : nat) (n : nat) : (term68 m n x) = (term69 m x n).
Proof. exact (MK_COMB (@lem5406195 m n) (@lem5406194 m x n)). Qed.
Lemma lem5406197 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (fun_ext (fun x : nat => @lem5406196 m x n)). Qed.
Lemma lem5406198 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5406199 (m : nat) (n : nat) : (term62 m n) = (term72 m n).
Proof. exact (MK_COMB (@lem5406198) (@lem5406197 m n)). Qed.
Lemma lem5406200 (m : nat) (n : nat) : ((term61 m n) = (term62 m n)) = ((term56 m n) = (term72 m n)).
Proof. exact (MK_COMB (@lem5406193 m n) (@lem5406199 m n)). Qed.
Lemma lem5406201 (m : nat) (n : nat) : (term56 m n) = (term72 m n).
Proof. exact (EQ_MP (@lem5406200 m n) (@lem5406185 m n)). Qed.
Lemma lem5406202 (m : nat) (n : nat) : (term5 m n) = (term72 m n).
Proof. exact (TRANS (@lem5406181 m n) (@lem5406201 m n)). Qed.
Lemma lem5406204 (m : nat) (n : nat) : (Peano.le m n) = (term73 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5406205 (m : nat) (n : nat) : (term33 m n) = (term74 m n).
Proof. exact (@lem5406204 m (term32 n)). Qed.
Lemma lem5406207 (m : nat) (n : nat) : (term75 m n) = (term76 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5406208 (n : nat) : (term77 n) = (term78 n).
Proof. exact (@lem5406207 n term79). Qed.
Lemma lem5406209 (m : nat) : (term80 m) = (term80 m).
Proof. exact (eq_refl (term80 m)). Qed.
Lemma lem5406210 (m : nat) (n : nat) : (term74 m n) = (term81 m n).
Proof. exact (MK_COMB (@lem5406209 m) (@lem5406208 n)). Qed.
Lemma lem5406211 (m : nat) (n : nat) : (term33 m n) = (term81 m n).
Proof. exact (TRANS (@lem5406205 m n) (@lem5406210 m n)). Qed.
Lemma lem5406212 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5406213 (m : nat) (n : nat) : (term35 m n) = (term82 m n).
Proof. exact (MK_COMB (@lem5406212) (@lem5406211 m n)). Qed.
Lemma lem5406214 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406215 (m : nat) (n : nat) : (term36 m n) = (term83 m n).
Proof. exact (MK_COMB (@lem5406214) (@lem5406213 m n)). Qed.
Lemma lem5406217 (m : nat) (n : nat) : (Peano.le m n) = (term73 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5406218 (m : nat) (x : nat) : (Peano.le m x) = (term73 m x).
Proof. exact (@lem5406217 m x). Qed.
Lemma lem5406219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406220 (m : nat) (x : nat) : (term37 m x) = (term84 m x).
Proof. exact (MK_COMB (@lem5406219) (@lem5406218 m x)). Qed.
Lemma lem5406222 (m : nat) (n : nat) : (Peano.le m n) = (term73 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5406223 (x : nat) (n : nat) : (term33 x n) = (term74 x n).
Proof. exact (@lem5406222 x (term32 n)). Qed.
Lemma lem5406225 (m : nat) (n : nat) : (term75 m n) = (term76 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5406226 (n : nat) : (term77 n) = (term78 n).
Proof. exact (@lem5406225 n term79). Qed.
Lemma lem5406227 (x : nat) : (term80 x) = (term80 x).
Proof. exact (eq_refl (term80 x)). Qed.
Lemma lem5406228 (x : nat) (n : nat) : (term74 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem5406227 x) (@lem5406226 n)). Qed.
Lemma lem5406229 (x : nat) (n : nat) : (term33 x n) = (term81 x n).
Proof. exact (TRANS (@lem5406223 x n) (@lem5406228 x n)). Qed.
Lemma lem5406230 (m : nat) (x : nat) (n : nat) : (term38 m x n) = (term85 m x n).
Proof. exact (MK_COMB (@lem5406220 m x) (@lem5406229 x n)). Qed.
Lemma lem5406231 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406232 (m : nat) (x : nat) (n : nat) : (term39 m x n) = (term86 m x n).
Proof. exact (MK_COMB (@lem5406231) (@lem5406230 m x n)). Qed.
Lemma lem5406234 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5406235 (x : nat) (n : nat) : (x = (term32 n)) = ((int_of_num x) = (term77 n)).
Proof. exact (@lem5406234 x (term32 n)). Qed.
Lemma lem5406239 (m : nat) (n : nat) : (term75 m n) = (term76 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5406240 (n : nat) : (term77 n) = (term78 n).
Proof. exact (@lem5406239 n term79). Qed.
Lemma lem5406241 (x : nat) : (term87 x) = (term87 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem5406242 (x : nat) (n : nat) : ((int_of_num x) = (term77 n)) = ((int_of_num x) = (term78 n)).
Proof. exact (MK_COMB (@lem5406241 x) (@lem5406240 n)). Qed.
Lemma lem5406243 (x : nat) (n : nat) : (x = (term32 n)) = ((int_of_num x) = (term78 n)).
Proof. exact (TRANS (@lem5406235 x n) (@lem5406242 x n)). Qed.
Lemma lem5406244 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5406245 (x : nat) (n : nat) : (term41 x n) = (term88 x n).
Proof. exact (MK_COMB (@lem5406244) (@lem5406243 x n)). Qed.
Lemma lem5406246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406247 (x : nat) (n : nat) : (term42 x n) = (term89 x n).
Proof. exact (MK_COMB (@lem5406246) (@lem5406245 x n)). Qed.
Lemma lem5406249 (m : nat) (n : nat) : (Peano.le m n) = (term73 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5406250 (m : nat) (x : nat) : (Peano.le m x) = (term73 m x).
Proof. exact (@lem5406249 m x). Qed.
Lemma lem5406251 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5406252 (m : nat) (x : nat) : (term90 m x) = (term91 m x).
Proof. exact (MK_COMB (@lem5406251) (@lem5406250 m x)). Qed.
Lemma lem5406253 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406254 (m : nat) (x : nat) : (term46 m x) = (term92 m x).
Proof. exact (MK_COMB (@lem5406253) (@lem5406252 m x)). Qed.
Lemma lem5406256 (m : nat) (n : nat) : (Peano.le m n) = (term73 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5406257 (x : nat) (n : nat) : (Peano.le x n) = (term73 x n).
Proof. exact (@lem5406256 x n). Qed.
Lemma lem5406258 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5406259 (x : nat) (n : nat) : (term90 x n) = (term91 x n).
Proof. exact (MK_COMB (@lem5406258) (@lem5406257 x n)). Qed.
Lemma lem5406260 (m : nat) (x : nat) (n : nat) : (term10 m x n) = (term93 m x n).
Proof. exact (MK_COMB (@lem5406254 m x) (@lem5406259 x n)). Qed.
Lemma lem5406261 (m : nat) (x : nat) (n : nat) : (term43 m x n) = (term94 m x n).
Proof. exact (MK_COMB (@lem5406247 x n) (@lem5406260 m x n)). Qed.
Lemma lem5406262 (m : nat) (x : nat) (n : nat) : (term44 m x n) = (term95 m x n).
Proof. exact (MK_COMB (@lem5406232 m x n) (@lem5406261 m x n)). Qed.
Lemma lem5406263 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406264 (m : nat) (x : nat) (n : nat) : (term45 m x n) = (term96 m x n).
Proof. exact (MK_COMB (@lem5406263) (@lem5406262 m x n)). Qed.
Lemma lem5406266 (m : nat) (n : nat) : (Peano.le m n) = (term73 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5406267 (m : nat) (x : nat) : (Peano.le m x) = (term73 m x).
Proof. exact (@lem5406266 m x). Qed.
Lemma lem5406268 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5406269 (m : nat) (x : nat) : (term90 m x) = (term91 m x).
Proof. exact (MK_COMB (@lem5406268) (@lem5406267 m x)). Qed.
Lemma lem5406270 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406271 (m : nat) (x : nat) : (term46 m x) = (term92 m x).
Proof. exact (MK_COMB (@lem5406270) (@lem5406269 m x)). Qed.
Lemma lem5406273 (m : nat) (n : nat) : (Peano.le m n) = (term73 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5406274 (x : nat) (n : nat) : (term33 x n) = (term74 x n).
Proof. exact (@lem5406273 x (term32 n)). Qed.
Lemma lem5406276 (m : nat) (n : nat) : (term75 m n) = (term76 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5406277 (n : nat) : (term77 n) = (term78 n).
Proof. exact (@lem5406276 n term79). Qed.
Lemma lem5406278 (x : nat) : (term80 x) = (term80 x).
Proof. exact (eq_refl (term80 x)). Qed.
Lemma lem5406279 (x : nat) (n : nat) : (term74 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem5406278 x) (@lem5406277 n)). Qed.
Lemma lem5406280 (x : nat) (n : nat) : (term33 x n) = (term81 x n).
Proof. exact (TRANS (@lem5406274 x n) (@lem5406279 x n)). Qed.
Lemma lem5406281 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5406282 (x : nat) (n : nat) : (term35 x n) = (term82 x n).
Proof. exact (MK_COMB (@lem5406281) (@lem5406280 x n)). Qed.
Lemma lem5406283 (m : nat) (x : nat) (n : nat) : (term47 m x n) = (term97 m x n).
Proof. exact (MK_COMB (@lem5406271 m x) (@lem5406282 x n)). Qed.
Lemma lem5406284 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406285 (m : nat) (x : nat) (n : nat) : (term48 m x n) = (term98 m x n).
Proof. exact (MK_COMB (@lem5406284) (@lem5406283 m x n)). Qed.
Lemma lem5406287 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5406288 (x : nat) (n : nat) : (x = (term32 n)) = ((int_of_num x) = (term77 n)).
Proof. exact (@lem5406287 x (term32 n)). Qed.
Lemma lem5406292 (m : nat) (n : nat) : (term75 m n) = (term76 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5406293 (n : nat) : (term77 n) = (term78 n).
Proof. exact (@lem5406292 n term79). Qed.
Lemma lem5406294 (x : nat) : (term87 x) = (term87 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem5406295 (x : nat) (n : nat) : ((int_of_num x) = (term77 n)) = ((int_of_num x) = (term78 n)).
Proof. exact (MK_COMB (@lem5406294 x) (@lem5406293 n)). Qed.
Lemma lem5406296 (x : nat) (n : nat) : (x = (term32 n)) = ((int_of_num x) = (term78 n)).
Proof. exact (TRANS (@lem5406288 x n) (@lem5406295 x n)). Qed.
Lemma lem5406297 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406298 (x : nat) (n : nat) : (term50 x n) = (term99 x n).
Proof. exact (MK_COMB (@lem5406297) (@lem5406296 x n)). Qed.
Lemma lem5406300 (m : nat) (n : nat) : (Peano.le m n) = (term73 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5406301 (m : nat) (x : nat) : (Peano.le m x) = (term73 m x).
Proof. exact (@lem5406300 m x). Qed.
Lemma lem5406302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406303 (m : nat) (x : nat) : (term37 m x) = (term84 m x).
Proof. exact (MK_COMB (@lem5406302) (@lem5406301 m x)). Qed.
Lemma lem5406305 (m : nat) (n : nat) : (Peano.le m n) = (term73 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5406306 (x : nat) (n : nat) : (Peano.le x n) = (term73 x n).
Proof. exact (@lem5406305 x n). Qed.
Lemma lem5406307 (m : nat) (x : nat) (n : nat) : (term15 m x n) = (term100 m x n).
Proof. exact (MK_COMB (@lem5406303 m x) (@lem5406306 x n)). Qed.
Lemma lem5406308 (m : nat) (x : nat) (n : nat) : (term51 m x n) = (term101 m x n).
Proof. exact (MK_COMB (@lem5406298 x n) (@lem5406307 m x n)). Qed.
Lemma lem5406309 (m : nat) (x : nat) (n : nat) : (term52 m x n) = (term102 m x n).
Proof. exact (MK_COMB (@lem5406285 m x n) (@lem5406308 m x n)). Qed.
Lemma lem5406310 (m : nat) (x : nat) (n : nat) : (term53 m x n) = (term103 m x n).
Proof. exact (MK_COMB (@lem5406264 m x n) (@lem5406309 m x n)). Qed.
Lemma lem5406311 (m : nat) (x : nat) (n : nat) : (term69 m x n) = (term104 m x n).
Proof. exact (MK_COMB (@lem5406215 m n) (@lem5406310 m x n)). Qed.
Lemma lem5406312 (m : nat) (n : nat) : (term71 m n) = (term105 m n).
Proof. exact (fun_ext (fun x : nat => @lem5406311 m x n)). Qed.
Lemma lem5406313 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5406314 (m : nat) (n : nat) : (term72 m n) = (term106 m n).
Proof. exact (MK_COMB (@lem5406313) (@lem5406312 m n)). Qed.
Lemma lem5406315 (m : nat) (n : nat) : (term5 m n) = (term106 m n).
Proof. exact (TRANS (@lem5406202 m n) (@lem5406314 m n)). Qed.
Lemma lem5406316 (m : nat) : term107 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem5406317 (m : nat) : (term107 m) = (term108 m).
Proof. exact (eq_refl (term107 m)). Qed.
Lemma lem5406318 (m : nat) : term108 m.
Proof. exact (EQ_MP (@lem5406317 m) (@lem5406316 m)). Qed.
Lemma lem5406319 (n : nat) : term107 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5406320 (n : nat) : (term107 n) = (term108 n).
Proof. exact (eq_refl (term107 n)). Qed.
Lemma lem5406321 (n : nat) : term108 n.
Proof. exact (EQ_MP (@lem5406320 n) (@lem5406319 n)). Qed.
Lemma lem5406322 (x : nat) : term107 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem5406323 (x : nat) : (term107 x) = (term108 x).
Proof. exact (eq_refl (term107 x)). Qed.
Lemma lem5406324 (x : nat) : term108 x.
Proof. exact (EQ_MP (@lem5406323 x) (@lem5406322 x)). Qed.
Lemma lem5406325 (_69903 : int) (_69905 : int) (_69904 : int) : (term109 _69903 _69905 _69904) = (term110 _69903 _69905 _69904).
Proof. exact (@lem2318604 (term110 _69903 _69905 _69904)). Qed.
Lemma lem5406362 (_69903 : int) (_69904 : int) : (term111 _69903 _69904) = (term112 _69903 _69904).
Proof. exact (@lem16933 (term112 _69903 _69904)). Qed.
Lemma lem5406369 (_69903 : int) (_69905 : int) (_69904 : int) : (term113 _69903 _69905 _69904) = (term114 _69903 _69905 _69904).
Proof. exact (@lem17045 (int_le _69903 _69905) (term112 _69905 _69904)). Qed.
Lemma lem5406372 (_69905 : int) (_69904 : int) : (term115 _69905 _69904) = (_69905 = (term116 _69904)).
Proof. exact (@lem16933 (_69905 = (term116 _69904))). Qed.
Lemma lem5406375 (_69903 : int) (_69905 : int) : (term117 _69903 _69905) = (int_le _69903 _69905).
Proof. exact (@lem16933 (int_le _69903 _69905)). Qed.
Lemma lem5406378 (_69905 : int) (_69904 : int) : (term117 _69905 _69904) = (int_le _69905 _69904).
Proof. exact (@lem16933 (int_le _69905 _69904)). Qed.
Lemma lem5406379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406380 (_69903 : int) (_69905 : int) : (term118 _69903 _69905) = (term119 _69903 _69905).
Proof. exact (MK_COMB (@lem5406379) (@lem5406375 _69903 _69905)). Qed.
Lemma lem5406381 (_69903 : int) (_69905 : int) (_69904 : int) : (term120 _69903 _69905 _69904) = (term121 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406380 _69903 _69905) (@lem5406378 _69905 _69904)). Qed.
Lemma lem5406382 (_69903 : int) (_69905 : int) (_69904 : int) : (term122 _69903 _69905 _69904) = (term120 _69903 _69905 _69904).
Proof. exact (@lem17160 (term123 _69903 _69905) (term123 _69905 _69904)). Qed.
Lemma lem5406383 (_69903 : int) (_69905 : int) (_69904 : int) : (term122 _69903 _69905 _69904) = (term121 _69903 _69905 _69904).
Proof. exact (TRANS (@lem5406382 _69903 _69905 _69904) (@lem5406381 _69903 _69905 _69904)). Qed.
Lemma lem5406384 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406385 (_69905 : int) (_69904 : int) : (term124 _69905 _69904) = (term125 _69905 _69904).
Proof. exact (MK_COMB (@lem5406384) (@lem5406372 _69905 _69904)). Qed.
Lemma lem5406386 (_69903 : int) (_69905 : int) (_69904 : int) : (term126 _69903 _69905 _69904) = (term127 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406385 _69905 _69904) (@lem5406383 _69903 _69905 _69904)). Qed.
Lemma lem5406387 (_69903 : int) (_69905 : int) (_69904 : int) : (term128 _69903 _69905 _69904) = (term126 _69903 _69905 _69904).
Proof. exact (@lem17045 (term129 _69905 _69904) (term130 _69903 _69905 _69904)). Qed.
Lemma lem5406388 (_69903 : int) (_69905 : int) (_69904 : int) : (term128 _69903 _69905 _69904) = (term127 _69903 _69905 _69904).
Proof. exact (TRANS (@lem5406387 _69903 _69905 _69904) (@lem5406386 _69903 _69905 _69904)). Qed.
Lemma lem5406389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406390 (_69903 : int) (_69905 : int) (_69904 : int) : (term131 _69903 _69905 _69904) = (term132 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406389) (@lem5406369 _69903 _69905 _69904)). Qed.
Lemma lem5406391 (_69903 : int) (_69905 : int) (_69904 : int) : (term133 _69903 _69905 _69904) = (term134 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406390 _69903 _69905 _69904) (@lem5406388 _69903 _69905 _69904)). Qed.
Lemma lem5406392 (_69903 : int) (_69905 : int) (_69904 : int) : (term135 _69903 _69905 _69904) = (term133 _69903 _69905 _69904).
Proof. exact (@lem17160 (term136 _69903 _69905 _69904) (term137 _69903 _69905 _69904)). Qed.
Lemma lem5406393 (_69903 : int) (_69905 : int) (_69904 : int) : (term135 _69903 _69905 _69904) = (term134 _69903 _69905 _69904).
Proof. exact (TRANS (@lem5406392 _69903 _69905 _69904) (@lem5406391 _69903 _69905 _69904)). Qed.
Lemma lem5406396 (_69903 : int) (_69905 : int) : (term117 _69903 _69905) = (int_le _69903 _69905).
Proof. exact (@lem16933 (int_le _69903 _69905)). Qed.
Lemma lem5406399 (_69905 : int) (_69904 : int) : (term111 _69905 _69904) = (term112 _69905 _69904).
Proof. exact (@lem16933 (term112 _69905 _69904)). Qed.
Lemma lem5406400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406401 (_69903 : int) (_69905 : int) : (term118 _69903 _69905) = (term119 _69903 _69905).
Proof. exact (MK_COMB (@lem5406400) (@lem5406396 _69903 _69905)). Qed.
Lemma lem5406402 (_69903 : int) (_69905 : int) (_69904 : int) : (term138 _69903 _69905 _69904) = (term136 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406401 _69903 _69905) (@lem5406399 _69905 _69904)). Qed.
Lemma lem5406403 (_69903 : int) (_69905 : int) (_69904 : int) : (term139 _69903 _69905 _69904) = (term138 _69903 _69905 _69904).
Proof. exact (@lem17160 (term123 _69903 _69905) (term140 _69905 _69904)). Qed.
Lemma lem5406404 (_69903 : int) (_69905 : int) (_69904 : int) : (term139 _69903 _69905 _69904) = (term136 _69903 _69905 _69904).
Proof. exact (TRANS (@lem5406403 _69903 _69905 _69904) (@lem5406402 _69903 _69905 _69904)). Qed.
Lemma lem5406412 (_69903 : int) (_69905 : int) (_69904 : int) : (term141 _69903 _69905 _69904) = (term130 _69903 _69905 _69904).
Proof. exact (@lem17045 (int_le _69903 _69905) (int_le _69905 _69904)). Qed.
Lemma lem5406414 (_69905 : int) (_69904 : int) : (term142 _69905 _69904) = (term142 _69905 _69904).
Proof. exact (eq_refl (term142 _69905 _69904)). Qed.
Lemma lem5406415 (_69903 : int) (_69905 : int) (_69904 : int) : (term143 _69903 _69905 _69904) = (term137 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406414 _69905 _69904) (@lem5406412 _69903 _69905 _69904)). Qed.
Lemma lem5406416 (_69903 : int) (_69905 : int) (_69904 : int) : (term144 _69903 _69905 _69904) = (term143 _69903 _69905 _69904).
Proof. exact (@lem17160 (_69905 = (term116 _69904)) (term121 _69903 _69905 _69904)). Qed.
Lemma lem5406417 (_69903 : int) (_69905 : int) (_69904 : int) : (term144 _69903 _69905 _69904) = (term137 _69903 _69905 _69904).
Proof. exact (TRANS (@lem5406416 _69903 _69905 _69904) (@lem5406415 _69903 _69905 _69904)). Qed.
Lemma lem5406418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406419 (_69903 : int) (_69905 : int) (_69904 : int) : (term145 _69903 _69905 _69904) = (term146 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406418) (@lem5406404 _69903 _69905 _69904)). Qed.
Lemma lem5406420 (_69903 : int) (_69905 : int) (_69904 : int) : (term147 _69903 _69905 _69904) = (term148 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406419 _69903 _69905 _69904) (@lem5406417 _69903 _69905 _69904)). Qed.
Lemma lem5406421 (_69903 : int) (_69905 : int) (_69904 : int) : (term149 _69903 _69905 _69904) = (term147 _69903 _69905 _69904).
Proof. exact (@lem17160 (term114 _69903 _69905 _69904) (term127 _69903 _69905 _69904)). Qed.
Lemma lem5406422 (_69903 : int) (_69905 : int) (_69904 : int) : (term149 _69903 _69905 _69904) = (term148 _69903 _69905 _69904).
Proof. exact (TRANS (@lem5406421 _69903 _69905 _69904) (@lem5406420 _69903 _69905 _69904)). Qed.
Lemma lem5406423 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406424 (_69903 : int) (_69905 : int) (_69904 : int) : (term150 _69903 _69905 _69904) = (term151 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406423) (@lem5406393 _69903 _69905 _69904)). Qed.
Lemma lem5406425 (_69903 : int) (_69905 : int) (_69904 : int) : (term152 _69903 _69905 _69904) = (term153 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406424 _69903 _69905 _69904) (@lem5406422 _69903 _69905 _69904)). Qed.
Lemma lem5406426 (_69903 : int) (_69905 : int) (_69904 : int) : (term154 _69903 _69905 _69904) = (term152 _69903 _69905 _69904).
Proof. exact (@lem17045 (term155 _69903 _69905 _69904) (term156 _69903 _69905 _69904)). Qed.
Lemma lem5406427 (_69903 : int) (_69905 : int) (_69904 : int) : (term154 _69903 _69905 _69904) = (term153 _69903 _69905 _69904).
Proof. exact (TRANS (@lem5406426 _69903 _69905 _69904) (@lem5406425 _69903 _69905 _69904)). Qed.
Lemma lem5406428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406429 (_69903 : int) (_69904 : int) : (term157 _69903 _69904) = (term158 _69903 _69904).
Proof. exact (MK_COMB (@lem5406428) (@lem5406362 _69903 _69904)). Qed.
Lemma lem5406430 (_69903 : int) (_69905 : int) (_69904 : int) : (term159 _69903 _69905 _69904) = (term160 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406429 _69903 _69904) (@lem5406427 _69903 _69905 _69904)). Qed.
Lemma lem5406431 (_69903 : int) (_69905 : int) (_69904 : int) : (term161 _69903 _69905 _69904) = (term159 _69903 _69905 _69904).
Proof. exact (@lem17160 (term140 _69903 _69904) (term162 _69903 _69905 _69904)). Qed.
Lemma lem5406432 (_69903 : int) (_69905 : int) (_69904 : int) : (term161 _69903 _69905 _69904) = (term160 _69903 _69905 _69904).
Proof. exact (TRANS (@lem5406431 _69903 _69905 _69904) (@lem5406430 _69903 _69905 _69904)). Qed.
Lemma lem5406434 (_69905 : int) : (term163 _69905) = (term163 _69905).
Proof. exact (eq_refl (term163 _69905)). Qed.
Lemma lem5406435 (_69903 : int) (_69905 : int) (_69904 : int) : (term164 _69903 _69905 _69904) = (term165 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406434 _69905) (@lem5406432 _69903 _69905 _69904)). Qed.
Lemma lem5406436 (_69903 : int) (_69905 : int) (_69904 : int) : (term166 _69903 _69905 _69904) = (term164 _69903 _69905 _69904).
Proof. exact (@lem17362 (term167 _69905) (term168 _69903 _69905 _69904)). Qed.
Lemma lem5406437 (_69903 : int) (_69905 : int) (_69904 : int) : (term166 _69903 _69905 _69904) = (term165 _69903 _69905 _69904).
Proof. exact (TRANS (@lem5406436 _69903 _69905 _69904) (@lem5406435 _69903 _69905 _69904)). Qed.
Lemma lem5406439 (_69904 : int) : (term163 _69904) = (term163 _69904).
Proof. exact (eq_refl (term163 _69904)). Qed.
Lemma lem5406440 (_69903 : int) (_69905 : int) (_69904 : int) : (term169 _69903 _69905 _69904) = (term170 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406439 _69904) (@lem5406437 _69903 _69905 _69904)). Qed.
Lemma lem5406441 (_69903 : int) (_69905 : int) (_69904 : int) : (term171 _69903 _69905 _69904) = (term169 _69903 _69905 _69904).
Proof. exact (@lem17362 (term167 _69904) (term172 _69903 _69905 _69904)). Qed.
Lemma lem5406442 (_69903 : int) (_69905 : int) (_69904 : int) : (term171 _69903 _69905 _69904) = (term170 _69903 _69905 _69904).
Proof. exact (TRANS (@lem5406441 _69903 _69905 _69904) (@lem5406440 _69903 _69905 _69904)). Qed.
Lemma lem5406444 (_69903 : int) : (term163 _69903) = (term163 _69903).
Proof. exact (eq_refl (term163 _69903)). Qed.
Lemma lem5406445 (_69903 : int) (_69905 : int) (_69904 : int) : (term173 _69903 _69905 _69904) = (term174 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406444 _69903) (@lem5406442 _69903 _69905 _69904)). Qed.
Lemma lem5406446 (_69903 : int) (_69905 : int) (_69904 : int) : (term175 _69903 _69905 _69904) = (term173 _69903 _69905 _69904).
Proof. exact (@lem17362 (term167 _69903) (term176 _69903 _69905 _69904)). Qed.
Lemma lem5406512 (_69903 : int) (_69905 : int) (_69904 : int) : (term175 _69903 _69905 _69904) = (term174 _69903 _69905 _69904).
Proof. exact (TRANS (@lem5406446 _69903 _69905 _69904) (@lem5406445 _69903 _69905 _69904)). Qed.
Lemma lem5406515 (x : int) (y : int) : (int_le x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5406516 (_69903 : int) : (term167 _69903) = (term178 _69903).
Proof. exact (@lem5406515 term179 _69903). Qed.
Lemma lem5406518 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5406519 : term181 = term182.
Proof. exact (@lem5406518 (NUMERAL 0)). Qed.
Lemma lem5406520 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5406521 : term183 = term184.
Proof. exact (MK_COMB (@lem5406520) (@lem5406519)). Qed.
Lemma lem5406522 (_69903 : int) : (real_of_int _69903) = (real_of_int _69903).
Proof. exact (eq_refl (real_of_int _69903)). Qed.
Lemma lem5406523 (_69903 : int) : (term178 _69903) = (term185 _69903).
Proof. exact (MK_COMB (@lem5406521) (@lem5406522 _69903)). Qed.
Lemma lem5406525 (_69903 : int) : (term167 _69903) = (term185 _69903).
Proof. exact (TRANS (@lem5406516 _69903) (@lem5406523 _69903)). Qed.
Lemma lem5406528 (x : int) (y : int) : (int_le x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5406529 (_69904 : int) : (term167 _69904) = (term178 _69904).
Proof. exact (@lem5406528 term179 _69904). Qed.
Lemma lem5406531 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5406532 : term181 = term182.
Proof. exact (@lem5406531 (NUMERAL 0)). Qed.
Lemma lem5406533 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5406534 : term183 = term184.
Proof. exact (MK_COMB (@lem5406533) (@lem5406532)). Qed.
Lemma lem5406535 (_69904 : int) : (real_of_int _69904) = (real_of_int _69904).
Proof. exact (eq_refl (real_of_int _69904)). Qed.
Lemma lem5406536 (_69904 : int) : (term178 _69904) = (term185 _69904).
Proof. exact (MK_COMB (@lem5406534) (@lem5406535 _69904)). Qed.
Lemma lem5406538 (_69904 : int) : (term167 _69904) = (term185 _69904).
Proof. exact (TRANS (@lem5406529 _69904) (@lem5406536 _69904)). Qed.
Lemma lem5406541 (x : int) (y : int) : (int_le x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5406542 (_69905 : int) : (term167 _69905) = (term178 _69905).
Proof. exact (@lem5406541 term179 _69905). Qed.
Lemma lem5406544 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5406545 : term181 = term182.
Proof. exact (@lem5406544 (NUMERAL 0)). Qed.
Lemma lem5406546 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5406547 : term183 = term184.
Proof. exact (MK_COMB (@lem5406546) (@lem5406545)). Qed.
Lemma lem5406548 (_69905 : int) : (real_of_int _69905) = (real_of_int _69905).
Proof. exact (eq_refl (real_of_int _69905)). Qed.
Lemma lem5406549 (_69905 : int) : (term178 _69905) = (term185 _69905).
Proof. exact (MK_COMB (@lem5406547) (@lem5406548 _69905)). Qed.
Lemma lem5406551 (_69905 : int) : (term167 _69905) = (term185 _69905).
Proof. exact (TRANS (@lem5406542 _69905) (@lem5406549 _69905)). Qed.
Lemma lem5406554 (x : int) (y : int) : (int_le x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5406555 (_69903 : int) (_69904 : int) : (term112 _69903 _69904) = (term186 _69903 _69904).
Proof. exact (@lem5406554 _69903 (term116 _69904)). Qed.
Lemma lem5406557 (x : int) (y : int) : (term187 x y) = (term188 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5406558 (_69904 : int) : (term189 _69904) = (term190 _69904).
Proof. exact (@lem5406557 _69904 term191). Qed.
Lemma lem5406560 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5406561 : term192 = term193.
Proof. exact (@lem5406560 term79). Qed.
Lemma lem5406562 (_69904 : int) : (term194 _69904) = (term194 _69904).
Proof. exact (eq_refl (term194 _69904)). Qed.
Lemma lem5406563 (_69904 : int) : (term190 _69904) = (term195 _69904).
Proof. exact (MK_COMB (@lem5406562 _69904) (@lem5406561)). Qed.
Lemma lem5406564 (_69904 : int) : (term189 _69904) = (term195 _69904).
Proof. exact (TRANS (@lem5406558 _69904) (@lem5406563 _69904)). Qed.
Lemma lem5406565 (_69903 : int) : (term196 _69903) = (term196 _69903).
Proof. exact (eq_refl (term196 _69903)). Qed.
Lemma lem5406566 (_69903 : int) (_69904 : int) : (term186 _69903 _69904) = (term197 _69903 _69904).
Proof. exact (MK_COMB (@lem5406565 _69903) (@lem5406564 _69904)). Qed.
Lemma lem5406568 (_69903 : int) (_69904 : int) : (term112 _69903 _69904) = (term197 _69903 _69904).
Proof. exact (TRANS (@lem5406555 _69903 _69904) (@lem5406566 _69903 _69904)). Qed.
Lemma lem5406570 (y : int) (x : int) : (term123 x y) = (term198 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5406571 (_69905 : int) (_69903 : int) : (term123 _69903 _69905) = (term198 _69905 _69903).
Proof. exact (@lem5406570 _69905 _69903). Qed.
Lemma lem5406573 (x : int) (y : int) : (int_le x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5406574 (_69905 : int) (_69903 : int) : (term198 _69905 _69903) = (term199 _69905 _69903).
Proof. exact (@lem5406573 (term116 _69905) _69903). Qed.
Lemma lem5406576 (x : int) (y : int) : (term187 x y) = (term188 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5406577 (_69905 : int) : (term189 _69905) = (term190 _69905).
Proof. exact (@lem5406576 _69905 term191). Qed.
Lemma lem5406579 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5406580 : term192 = term193.
Proof. exact (@lem5406579 term79). Qed.
Lemma lem5406581 (_69905 : int) : (term194 _69905) = (term194 _69905).
Proof. exact (eq_refl (term194 _69905)). Qed.
Lemma lem5406582 (_69905 : int) : (term190 _69905) = (term195 _69905).
Proof. exact (MK_COMB (@lem5406581 _69905) (@lem5406580)). Qed.
Lemma lem5406583 (_69905 : int) : (term189 _69905) = (term195 _69905).
Proof. exact (TRANS (@lem5406577 _69905) (@lem5406582 _69905)). Qed.
Lemma lem5406584 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5406585 (_69905 : int) : (term200 _69905) = (term201 _69905).
Proof. exact (MK_COMB (@lem5406584) (@lem5406583 _69905)). Qed.
Lemma lem5406586 (_69903 : int) : (real_of_int _69903) = (real_of_int _69903).
Proof. exact (eq_refl (real_of_int _69903)). Qed.
Lemma lem5406587 (_69905 : int) (_69903 : int) : (term199 _69905 _69903) = (term202 _69905 _69903).
Proof. exact (MK_COMB (@lem5406585 _69905) (@lem5406586 _69903)). Qed.
Lemma lem5406588 (_69905 : int) (_69903 : int) : (term198 _69905 _69903) = (term202 _69905 _69903).
Proof. exact (TRANS (@lem5406574 _69905 _69903) (@lem5406587 _69905 _69903)). Qed.
Lemma lem5406589 (_69905 : int) (_69903 : int) : (term123 _69903 _69905) = (term202 _69905 _69903).
Proof. exact (TRANS (@lem5406571 _69905 _69903) (@lem5406588 _69905 _69903)). Qed.
Lemma lem5406591 (y : int) (x : int) : (term123 x y) = (term198 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5406592 (_69904 : int) (_69905 : int) : (term140 _69905 _69904) = (term203 _69904 _69905).
Proof. exact (@lem5406591 (term116 _69904) _69905). Qed.
Lemma lem5406594 (x : int) (y : int) : (int_le x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5406595 (_69904 : int) (_69905 : int) : (term203 _69904 _69905) = (term204 _69904 _69905).
Proof. exact (@lem5406594 (term205 _69904) _69905). Qed.
Lemma lem5406597 (x : int) (y : int) : (term187 x y) = (term188 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5406598 (_69904 : int) : (term206 _69904) = (term207 _69904).
Proof. exact (@lem5406597 (term116 _69904) term191). Qed.
Lemma lem5406600 (x : int) (y : int) : (term187 x y) = (term188 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5406601 (_69904 : int) : (term189 _69904) = (term190 _69904).
Proof. exact (@lem5406600 _69904 term191). Qed.
Lemma lem5406603 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5406604 : term192 = term193.
Proof. exact (@lem5406603 term79). Qed.
Lemma lem5406605 (_69904 : int) : (term194 _69904) = (term194 _69904).
Proof. exact (eq_refl (term194 _69904)). Qed.
Lemma lem5406606 (_69904 : int) : (term190 _69904) = (term195 _69904).
Proof. exact (MK_COMB (@lem5406605 _69904) (@lem5406604)). Qed.
Lemma lem5406607 (_69904 : int) : (term189 _69904) = (term195 _69904).
Proof. exact (TRANS (@lem5406601 _69904) (@lem5406606 _69904)). Qed.
Lemma lem5406608 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5406609 (_69904 : int) : (term208 _69904) = (term209 _69904).
Proof. exact (MK_COMB (@lem5406608) (@lem5406607 _69904)). Qed.
Lemma lem5406611 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5406612 : term192 = term193.
Proof. exact (@lem5406611 term79). Qed.
Lemma lem5406613 (_69904 : int) : (term207 _69904) = (term210 _69904).
Proof. exact (MK_COMB (@lem5406609 _69904) (@lem5406612)). Qed.
Lemma lem5406614 (_69904 : int) : (term206 _69904) = (term210 _69904).
Proof. exact (TRANS (@lem5406598 _69904) (@lem5406613 _69904)). Qed.
Lemma lem5406615 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5406616 (_69904 : int) : (term211 _69904) = (term212 _69904).
Proof. exact (MK_COMB (@lem5406615) (@lem5406614 _69904)). Qed.
Lemma lem5406617 (_69905 : int) : (real_of_int _69905) = (real_of_int _69905).
Proof. exact (eq_refl (real_of_int _69905)). Qed.
Lemma lem5406618 (_69904 : int) (_69905 : int) : (term204 _69904 _69905) = (term213 _69904 _69905).
Proof. exact (MK_COMB (@lem5406616 _69904) (@lem5406617 _69905)). Qed.
Lemma lem5406619 (_69904 : int) (_69905 : int) : (term203 _69904 _69905) = (term213 _69904 _69905).
Proof. exact (TRANS (@lem5406595 _69904 _69905) (@lem5406618 _69904 _69905)). Qed.
Lemma lem5406620 (_69904 : int) (_69905 : int) : (term140 _69905 _69904) = (term213 _69904 _69905).
Proof. exact (TRANS (@lem5406592 _69904 _69905) (@lem5406619 _69904 _69905)). Qed.
Lemma lem5406621 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406622 (_69905 : int) (_69903 : int) : (term214 _69903 _69905) = (term215 _69905 _69903).
Proof. exact (MK_COMB (@lem5406621) (@lem5406589 _69905 _69903)). Qed.
Lemma lem5406623 (_69903 : int) (_69904 : int) (_69905 : int) : (term114 _69903 _69905 _69904) = (term216 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5406622 _69905 _69903) (@lem5406620 _69904 _69905)). Qed.
Lemma lem5406626 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5406627 (_69905 : int) (_69904 : int) : (_69905 = (term116 _69904)) = ((real_of_int _69905) = (term189 _69904)).
Proof. exact (@lem5406626 _69905 (term116 _69904)). Qed.
Lemma lem5406631 (x : int) (y : int) : (term187 x y) = (term188 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5406632 (_69904 : int) : (term189 _69904) = (term190 _69904).
Proof. exact (@lem5406631 _69904 term191). Qed.
Lemma lem5406634 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5406635 : term192 = term193.
Proof. exact (@lem5406634 term79). Qed.
Lemma lem5406636 (_69904 : int) : (term194 _69904) = (term194 _69904).
Proof. exact (eq_refl (term194 _69904)). Qed.
Lemma lem5406637 (_69904 : int) : (term190 _69904) = (term195 _69904).
Proof. exact (MK_COMB (@lem5406636 _69904) (@lem5406635)). Qed.
Lemma lem5406638 (_69904 : int) : (term189 _69904) = (term195 _69904).
Proof. exact (TRANS (@lem5406632 _69904) (@lem5406637 _69904)). Qed.
Lemma lem5406639 (_69905 : int) : (term217 _69905) = (term217 _69905).
Proof. exact (eq_refl (term217 _69905)). Qed.
Lemma lem5406640 (_69905 : int) (_69904 : int) : ((real_of_int _69905) = (term189 _69904)) = ((real_of_int _69905) = (term195 _69904)).
Proof. exact (MK_COMB (@lem5406639 _69905) (@lem5406638 _69904)). Qed.
Lemma lem5406642 (_69905 : int) (_69904 : int) : (_69905 = (term116 _69904)) = ((real_of_int _69905) = (term195 _69904)).
Proof. exact (TRANS (@lem5406627 _69905 _69904) (@lem5406640 _69905 _69904)). Qed.
Lemma lem5406645 (x : int) (y : int) : (int_le x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5406647 (_69903 : int) (_69905 : int) : (int_le _69903 _69905) = (term177 _69903 _69905).
Proof. exact (@lem5406645 _69903 _69905). Qed.
Lemma lem5406650 (x : int) (y : int) : (int_le x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5406652 (_69905 : int) (_69904 : int) : (int_le _69905 _69904) = (term177 _69905 _69904).
Proof. exact (@lem5406650 _69905 _69904). Qed.
Lemma lem5406653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406654 (_69903 : int) (_69905 : int) : (term119 _69903 _69905) = (term218 _69903 _69905).
Proof. exact (MK_COMB (@lem5406653) (@lem5406647 _69903 _69905)). Qed.
Lemma lem5406655 (_69903 : int) (_69905 : int) (_69904 : int) : (term121 _69903 _69905 _69904) = (term219 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406654 _69903 _69905) (@lem5406652 _69905 _69904)). Qed.
Lemma lem5406656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406657 (_69905 : int) (_69904 : int) : (term125 _69905 _69904) = (term220 _69905 _69904).
Proof. exact (MK_COMB (@lem5406656) (@lem5406642 _69905 _69904)). Qed.
Lemma lem5406658 (_69903 : int) (_69905 : int) (_69904 : int) : (term127 _69903 _69905 _69904) = (term221 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406657 _69905 _69904) (@lem5406655 _69903 _69905 _69904)). Qed.
Lemma lem5406659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406660 (_69903 : int) (_69904 : int) (_69905 : int) : (term132 _69903 _69905 _69904) = (term222 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5406659) (@lem5406623 _69903 _69904 _69905)). Qed.
Lemma lem5406661 (_69903 : int) (_69905 : int) (_69904 : int) : (term134 _69903 _69905 _69904) = (term223 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406660 _69903 _69904 _69905) (@lem5406658 _69903 _69905 _69904)). Qed.
Lemma lem5406664 (x : int) (y : int) : (int_le x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5406666 (_69903 : int) (_69905 : int) : (int_le _69903 _69905) = (term177 _69903 _69905).
Proof. exact (@lem5406664 _69903 _69905). Qed.
Lemma lem5406669 (x : int) (y : int) : (int_le x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5406670 (_69905 : int) (_69904 : int) : (term112 _69905 _69904) = (term186 _69905 _69904).
Proof. exact (@lem5406669 _69905 (term116 _69904)). Qed.
Lemma lem5406672 (x : int) (y : int) : (term187 x y) = (term188 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5406673 (_69904 : int) : (term189 _69904) = (term190 _69904).
Proof. exact (@lem5406672 _69904 term191). Qed.
Lemma lem5406675 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5406676 : term192 = term193.
Proof. exact (@lem5406675 term79). Qed.
Lemma lem5406677 (_69904 : int) : (term194 _69904) = (term194 _69904).
Proof. exact (eq_refl (term194 _69904)). Qed.
Lemma lem5406678 (_69904 : int) : (term190 _69904) = (term195 _69904).
Proof. exact (MK_COMB (@lem5406677 _69904) (@lem5406676)). Qed.
Lemma lem5406679 (_69904 : int) : (term189 _69904) = (term195 _69904).
Proof. exact (TRANS (@lem5406673 _69904) (@lem5406678 _69904)). Qed.
Lemma lem5406680 (_69905 : int) : (term196 _69905) = (term196 _69905).
Proof. exact (eq_refl (term196 _69905)). Qed.
Lemma lem5406681 (_69905 : int) (_69904 : int) : (term186 _69905 _69904) = (term197 _69905 _69904).
Proof. exact (MK_COMB (@lem5406680 _69905) (@lem5406679 _69904)). Qed.
Lemma lem5406683 (_69905 : int) (_69904 : int) : (term112 _69905 _69904) = (term197 _69905 _69904).
Proof. exact (TRANS (@lem5406670 _69905 _69904) (@lem5406681 _69905 _69904)). Qed.
Lemma lem5406684 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406685 (_69903 : int) (_69905 : int) : (term119 _69903 _69905) = (term218 _69903 _69905).
Proof. exact (MK_COMB (@lem5406684) (@lem5406666 _69903 _69905)). Qed.
Lemma lem5406686 (_69903 : int) (_69905 : int) (_69904 : int) : (term136 _69903 _69905 _69904) = (term224 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406685 _69903 _69905) (@lem5406683 _69905 _69904)). Qed.
Lemma lem5406688 (y : int) (x : int) : (term225 x y) = (term226 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem5406689 (_69904 : int) (_69905 : int) : (term129 _69905 _69904) = (term227 _69904 _69905).
Proof. exact (@lem5406688 (term116 _69904) _69905). Qed.
Lemma lem5406691 (x : int) (y : int) : (int_le x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5406692 (_69905 : int) (_69904 : int) : (term228 _69905 _69904) = (term229 _69905 _69904).
Proof. exact (@lem5406691 (term116 _69905) (term116 _69904)). Qed.
Lemma lem5406694 (x : int) (y : int) : (term187 x y) = (term188 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5406695 (_69905 : int) : (term189 _69905) = (term190 _69905).
Proof. exact (@lem5406694 _69905 term191). Qed.
Lemma lem5406697 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5406698 : term192 = term193.
Proof. exact (@lem5406697 term79). Qed.
Lemma lem5406699 (_69905 : int) : (term194 _69905) = (term194 _69905).
Proof. exact (eq_refl (term194 _69905)). Qed.
Lemma lem5406700 (_69905 : int) : (term190 _69905) = (term195 _69905).
Proof. exact (MK_COMB (@lem5406699 _69905) (@lem5406698)). Qed.
Lemma lem5406701 (_69905 : int) : (term189 _69905) = (term195 _69905).
Proof. exact (TRANS (@lem5406695 _69905) (@lem5406700 _69905)). Qed.
Lemma lem5406702 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5406703 (_69905 : int) : (term200 _69905) = (term201 _69905).
Proof. exact (MK_COMB (@lem5406702) (@lem5406701 _69905)). Qed.
Lemma lem5406705 (x : int) (y : int) : (term187 x y) = (term188 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5406706 (_69904 : int) : (term189 _69904) = (term190 _69904).
Proof. exact (@lem5406705 _69904 term191). Qed.
Lemma lem5406708 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5406709 : term192 = term193.
Proof. exact (@lem5406708 term79). Qed.
Lemma lem5406710 (_69904 : int) : (term194 _69904) = (term194 _69904).
Proof. exact (eq_refl (term194 _69904)). Qed.
Lemma lem5406711 (_69904 : int) : (term190 _69904) = (term195 _69904).
Proof. exact (MK_COMB (@lem5406710 _69904) (@lem5406709)). Qed.
Lemma lem5406712 (_69904 : int) : (term189 _69904) = (term195 _69904).
Proof. exact (TRANS (@lem5406706 _69904) (@lem5406711 _69904)). Qed.
Lemma lem5406713 (_69905 : int) (_69904 : int) : (term229 _69905 _69904) = (term230 _69905 _69904).
Proof. exact (MK_COMB (@lem5406703 _69905) (@lem5406712 _69904)). Qed.
Lemma lem5406714 (_69905 : int) (_69904 : int) : (term228 _69905 _69904) = (term230 _69905 _69904).
Proof. exact (TRANS (@lem5406692 _69905 _69904) (@lem5406713 _69905 _69904)). Qed.
Lemma lem5406715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406716 (_69905 : int) (_69904 : int) : (term231 _69905 _69904) = (term232 _69905 _69904).
Proof. exact (MK_COMB (@lem5406715) (@lem5406714 _69905 _69904)). Qed.
Lemma lem5406718 (x : int) (y : int) : (int_le x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5406719 (_69904 : int) (_69905 : int) : (term203 _69904 _69905) = (term204 _69904 _69905).
Proof. exact (@lem5406718 (term205 _69904) _69905). Qed.
Lemma lem5406721 (x : int) (y : int) : (term187 x y) = (term188 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5406722 (_69904 : int) : (term206 _69904) = (term207 _69904).
Proof. exact (@lem5406721 (term116 _69904) term191). Qed.
Lemma lem5406724 (x : int) (y : int) : (term187 x y) = (term188 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5406725 (_69904 : int) : (term189 _69904) = (term190 _69904).
Proof. exact (@lem5406724 _69904 term191). Qed.
Lemma lem5406727 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5406728 : term192 = term193.
Proof. exact (@lem5406727 term79). Qed.
Lemma lem5406729 (_69904 : int) : (term194 _69904) = (term194 _69904).
Proof. exact (eq_refl (term194 _69904)). Qed.
Lemma lem5406730 (_69904 : int) : (term190 _69904) = (term195 _69904).
Proof. exact (MK_COMB (@lem5406729 _69904) (@lem5406728)). Qed.
Lemma lem5406731 (_69904 : int) : (term189 _69904) = (term195 _69904).
Proof. exact (TRANS (@lem5406725 _69904) (@lem5406730 _69904)). Qed.
Lemma lem5406732 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5406733 (_69904 : int) : (term208 _69904) = (term209 _69904).
Proof. exact (MK_COMB (@lem5406732) (@lem5406731 _69904)). Qed.
Lemma lem5406735 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5406736 : term192 = term193.
Proof. exact (@lem5406735 term79). Qed.
Lemma lem5406737 (_69904 : int) : (term207 _69904) = (term210 _69904).
Proof. exact (MK_COMB (@lem5406733 _69904) (@lem5406736)). Qed.
Lemma lem5406738 (_69904 : int) : (term206 _69904) = (term210 _69904).
Proof. exact (TRANS (@lem5406722 _69904) (@lem5406737 _69904)). Qed.
Lemma lem5406739 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5406740 (_69904 : int) : (term211 _69904) = (term212 _69904).
Proof. exact (MK_COMB (@lem5406739) (@lem5406738 _69904)). Qed.
Lemma lem5406741 (_69905 : int) : (real_of_int _69905) = (real_of_int _69905).
Proof. exact (eq_refl (real_of_int _69905)). Qed.
Lemma lem5406742 (_69904 : int) (_69905 : int) : (term204 _69904 _69905) = (term213 _69904 _69905).
Proof. exact (MK_COMB (@lem5406740 _69904) (@lem5406741 _69905)). Qed.
Lemma lem5406743 (_69904 : int) (_69905 : int) : (term203 _69904 _69905) = (term213 _69904 _69905).
Proof. exact (TRANS (@lem5406719 _69904 _69905) (@lem5406742 _69904 _69905)). Qed.
Lemma lem5406744 (_69904 : int) (_69905 : int) : (term227 _69904 _69905) = (term233 _69904 _69905).
Proof. exact (MK_COMB (@lem5406716 _69905 _69904) (@lem5406743 _69904 _69905)). Qed.
Lemma lem5406745 (_69904 : int) (_69905 : int) : (term129 _69905 _69904) = (term233 _69904 _69905).
Proof. exact (TRANS (@lem5406689 _69904 _69905) (@lem5406744 _69904 _69905)). Qed.
Lemma lem5406747 (y : int) (x : int) : (term123 x y) = (term198 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5406748 (_69905 : int) (_69903 : int) : (term123 _69903 _69905) = (term198 _69905 _69903).
Proof. exact (@lem5406747 _69905 _69903). Qed.
Lemma lem5406750 (x : int) (y : int) : (int_le x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5406751 (_69905 : int) (_69903 : int) : (term198 _69905 _69903) = (term199 _69905 _69903).
Proof. exact (@lem5406750 (term116 _69905) _69903). Qed.
Lemma lem5406753 (x : int) (y : int) : (term187 x y) = (term188 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5406754 (_69905 : int) : (term189 _69905) = (term190 _69905).
Proof. exact (@lem5406753 _69905 term191). Qed.
Lemma lem5406756 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5406757 : term192 = term193.
Proof. exact (@lem5406756 term79). Qed.
Lemma lem5406758 (_69905 : int) : (term194 _69905) = (term194 _69905).
Proof. exact (eq_refl (term194 _69905)). Qed.
Lemma lem5406759 (_69905 : int) : (term190 _69905) = (term195 _69905).
Proof. exact (MK_COMB (@lem5406758 _69905) (@lem5406757)). Qed.
Lemma lem5406760 (_69905 : int) : (term189 _69905) = (term195 _69905).
Proof. exact (TRANS (@lem5406754 _69905) (@lem5406759 _69905)). Qed.
Lemma lem5406761 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5406762 (_69905 : int) : (term200 _69905) = (term201 _69905).
Proof. exact (MK_COMB (@lem5406761) (@lem5406760 _69905)). Qed.
Lemma lem5406763 (_69903 : int) : (real_of_int _69903) = (real_of_int _69903).
Proof. exact (eq_refl (real_of_int _69903)). Qed.
Lemma lem5406764 (_69905 : int) (_69903 : int) : (term199 _69905 _69903) = (term202 _69905 _69903).
Proof. exact (MK_COMB (@lem5406762 _69905) (@lem5406763 _69903)). Qed.
Lemma lem5406765 (_69905 : int) (_69903 : int) : (term198 _69905 _69903) = (term202 _69905 _69903).
Proof. exact (TRANS (@lem5406751 _69905 _69903) (@lem5406764 _69905 _69903)). Qed.
Lemma lem5406766 (_69905 : int) (_69903 : int) : (term123 _69903 _69905) = (term202 _69905 _69903).
Proof. exact (TRANS (@lem5406748 _69905 _69903) (@lem5406765 _69905 _69903)). Qed.
Lemma lem5406768 (y : int) (x : int) : (term123 x y) = (term198 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5406769 (_69904 : int) (_69905 : int) : (term123 _69905 _69904) = (term198 _69904 _69905).
Proof. exact (@lem5406768 _69904 _69905). Qed.
Lemma lem5406771 (x : int) (y : int) : (int_le x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5406772 (_69904 : int) (_69905 : int) : (term198 _69904 _69905) = (term199 _69904 _69905).
Proof. exact (@lem5406771 (term116 _69904) _69905). Qed.
Lemma lem5406774 (x : int) (y : int) : (term187 x y) = (term188 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5406775 (_69904 : int) : (term189 _69904) = (term190 _69904).
Proof. exact (@lem5406774 _69904 term191). Qed.
Lemma lem5406777 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5406778 : term192 = term193.
Proof. exact (@lem5406777 term79). Qed.
Lemma lem5406779 (_69904 : int) : (term194 _69904) = (term194 _69904).
Proof. exact (eq_refl (term194 _69904)). Qed.
Lemma lem5406780 (_69904 : int) : (term190 _69904) = (term195 _69904).
Proof. exact (MK_COMB (@lem5406779 _69904) (@lem5406778)). Qed.
Lemma lem5406781 (_69904 : int) : (term189 _69904) = (term195 _69904).
Proof. exact (TRANS (@lem5406775 _69904) (@lem5406780 _69904)). Qed.
Lemma lem5406782 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5406783 (_69904 : int) : (term200 _69904) = (term201 _69904).
Proof. exact (MK_COMB (@lem5406782) (@lem5406781 _69904)). Qed.
Lemma lem5406784 (_69905 : int) : (real_of_int _69905) = (real_of_int _69905).
Proof. exact (eq_refl (real_of_int _69905)). Qed.
Lemma lem5406785 (_69904 : int) (_69905 : int) : (term199 _69904 _69905) = (term202 _69904 _69905).
Proof. exact (MK_COMB (@lem5406783 _69904) (@lem5406784 _69905)). Qed.
Lemma lem5406786 (_69904 : int) (_69905 : int) : (term198 _69904 _69905) = (term202 _69904 _69905).
Proof. exact (TRANS (@lem5406772 _69904 _69905) (@lem5406785 _69904 _69905)). Qed.
Lemma lem5406787 (_69904 : int) (_69905 : int) : (term123 _69905 _69904) = (term202 _69904 _69905).
Proof. exact (TRANS (@lem5406769 _69904 _69905) (@lem5406786 _69904 _69905)). Qed.
Lemma lem5406788 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406789 (_69905 : int) (_69903 : int) : (term214 _69903 _69905) = (term215 _69905 _69903).
Proof. exact (MK_COMB (@lem5406788) (@lem5406766 _69905 _69903)). Qed.
Lemma lem5406790 (_69903 : int) (_69904 : int) (_69905 : int) : (term130 _69903 _69905 _69904) = (term234 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5406789 _69905 _69903) (@lem5406787 _69904 _69905)). Qed.
Lemma lem5406791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406792 (_69904 : int) (_69905 : int) : (term142 _69905 _69904) = (term235 _69904 _69905).
Proof. exact (MK_COMB (@lem5406791) (@lem5406745 _69904 _69905)). Qed.
Lemma lem5406793 (_69903 : int) (_69904 : int) (_69905 : int) : (term137 _69903 _69905 _69904) = (term236 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5406792 _69904 _69905) (@lem5406790 _69903 _69904 _69905)). Qed.
Lemma lem5406794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406795 (_69903 : int) (_69905 : int) (_69904 : int) : (term146 _69903 _69905 _69904) = (term237 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406794) (@lem5406686 _69903 _69905 _69904)). Qed.
Lemma lem5406796 (_69903 : int) (_69904 : int) (_69905 : int) : (term148 _69903 _69905 _69904) = (term238 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5406795 _69903 _69905 _69904) (@lem5406793 _69903 _69904 _69905)). Qed.
Lemma lem5406797 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5406798 (_69903 : int) (_69905 : int) (_69904 : int) : (term151 _69903 _69905 _69904) = (term239 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5406797) (@lem5406661 _69903 _69905 _69904)). Qed.
Lemma lem5406799 (_69903 : int) (_69904 : int) (_69905 : int) : (term153 _69903 _69905 _69904) = (term240 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5406798 _69903 _69905 _69904) (@lem5406796 _69903 _69904 _69905)). Qed.
Lemma lem5406800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406801 (_69903 : int) (_69904 : int) : (term158 _69903 _69904) = (term241 _69903 _69904).
Proof. exact (MK_COMB (@lem5406800) (@lem5406568 _69903 _69904)). Qed.
Lemma lem5406802 (_69903 : int) (_69904 : int) (_69905 : int) : (term160 _69903 _69905 _69904) = (term242 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5406801 _69903 _69904) (@lem5406799 _69903 _69904 _69905)). Qed.
Lemma lem5406803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406804 (_69905 : int) : (term163 _69905) = (term243 _69905).
Proof. exact (MK_COMB (@lem5406803) (@lem5406551 _69905)). Qed.
Lemma lem5406805 (_69903 : int) (_69904 : int) (_69905 : int) : (term165 _69903 _69905 _69904) = (term244 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5406804 _69905) (@lem5406802 _69903 _69904 _69905)). Qed.
Lemma lem5406806 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406807 (_69904 : int) : (term163 _69904) = (term243 _69904).
Proof. exact (MK_COMB (@lem5406806) (@lem5406538 _69904)). Qed.
Lemma lem5406808 (_69903 : int) (_69904 : int) (_69905 : int) : (term170 _69903 _69905 _69904) = (term245 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5406807 _69904) (@lem5406805 _69903 _69904 _69905)). Qed.
Lemma lem5406809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5406810 (_69903 : int) : (term163 _69903) = (term243 _69903).
Proof. exact (MK_COMB (@lem5406809) (@lem5406525 _69903)). Qed.
Lemma lem5406811 (_69903 : int) (_69904 : int) (_69905 : int) : (term174 _69903 _69905 _69904) = (term246 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5406810 _69903) (@lem5406808 _69903 _69904 _69905)). Qed.
Lemma lem5406812 (_69903 : int) (_69904 : int) (_69905 : int) : (term175 _69903 _69905 _69904) = (term246 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5406512 _69903 _69905 _69904) (@lem5406811 _69903 _69904 _69905)). Qed.
Lemma lem5406816 (t : Prop) : (term247 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5406962 (_69903 : int) (_69904 : int) (_69905 : int) : (term248 _69903 _69904 _69905) = (term246 _69903 _69904 _69905).
Proof. exact (@lem5406816 (term246 _69903 _69904 _69905)). Qed.
Lemma lem5406963 (_69903 : int) : (term185 _69903) = (term249 _69903).
Proof. exact (@lem1988287 (real_of_int _69903) term182). Qed.
Lemma lem5406969 (_69903 : int) : (term250 _69903) = (term251 _69903).
Proof. exact (@lem1982792 (real_of_int _69903) term182). Qed.
Lemma lem5406971 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5406972 : term182 = term253.
Proof. exact (@lem5406971 (NUMERAL 0)). Qed.
Lemma lem5406974 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5406975 : term256 = term257.
Proof. exact (@lem5406974 term79). Qed.
Lemma lem5406976 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5406977 : term258 = term259.
Proof. exact (MK_COMB (@lem5406976) (@lem5406975)). Qed.
Lemma lem5406978 : term260 = term261.
Proof. exact (MK_COMB (@lem5406977) (@lem5406972)). Qed.
Lemma lem5406979 : term261 = term262.
Proof. exact (@lem1981613 term256 term182 term193 term193). Qed.
Lemma lem5406981 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5406982 : term265 = term266.
Proof. exact (@lem5406981 term79 term79). Qed.
Lemma lem5406983 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5406984 : term268 = term79.
Proof. exact (EQ_MP (@lem5406983) (@lem940073)). Qed.
Lemma lem5406985 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5406986 : term266 = term193.
Proof. exact (MK_COMB (@lem5406985) (@lem5406984)). Qed.
Lemma lem5406987 : term265 = term193.
Proof. exact (TRANS (@lem5406982) (@lem5406986)). Qed.
Lemma lem5406989 (x : nat) : (term269 x) = term182.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5406990 : term260 = term182.
Proof. exact (@lem5406989 term79). Qed.
Lemma lem5406991 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5406992 : term270 = term271.
Proof. exact (MK_COMB (@lem5406991) (@lem5406990)). Qed.
Lemma lem5406993 : term262 = term253.
Proof. exact (MK_COMB (@lem5406992) (@lem5406987)). Qed.
Lemma lem5406994 : term261 = term253.
Proof. exact (TRANS (@lem5406979) (@lem5406993)). Qed.
Lemma lem5406995 : term260 = term253.
Proof. exact (TRANS (@lem5406978) (@lem5406994)). Qed.
Lemma lem5406997 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5406998 : term253 = term182.
Proof. exact (@lem5406997 term182). Qed.
Lemma lem5406999 : term260 = term182.
Proof. exact (TRANS (@lem5406995) (@lem5406998)). Qed.
Lemma lem5407000 (_69903 : int) : (term194 _69903) = (term194 _69903).
Proof. exact (eq_refl (term194 _69903)). Qed.
Lemma lem5407001 (_69903 : int) : (term251 _69903) = (term273 _69903).
Proof. exact (MK_COMB (@lem5407000 _69903) (@lem5406999)). Qed.
Lemma lem5407002 (_69903 : int) : (term273 _69903) = (real_of_int _69903).
Proof. exact (@lem1982723 (real_of_int _69903)). Qed.
Lemma lem5407003 (_69903 : int) : (term251 _69903) = (real_of_int _69903).
Proof. exact (TRANS (@lem5407001 _69903) (@lem5407002 _69903)). Qed.
Lemma lem5407005 (_69903 : int) : (term250 _69903) = (real_of_int _69903).
Proof. exact (TRANS (@lem5406969 _69903) (@lem5407003 _69903)). Qed.
Lemma lem5407006 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5407007 (_69903 : int) : (term274 _69903) = (term275 _69903).
Proof. exact (MK_COMB (@lem5407006) (@lem5407005 _69903)). Qed.
Lemma lem5407008 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5407009 (_69903 : int) : (term249 _69903) = (term276 _69903).
Proof. exact (MK_COMB (@lem5407007 _69903) (@lem5407008)). Qed.
Lemma lem5407010 (_69903 : int) : (term185 _69903) = (term276 _69903).
Proof. exact (TRANS (@lem5406963 _69903) (@lem5407009 _69903)). Qed.
Lemma lem5407011 (_69904 : int) : (term185 _69904) = (term249 _69904).
Proof. exact (@lem1988287 (real_of_int _69904) term182). Qed.
Lemma lem5407017 (_69904 : int) : (term250 _69904) = (term251 _69904).
Proof. exact (@lem1982792 (real_of_int _69904) term182). Qed.
Lemma lem5407019 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5407020 : term182 = term253.
Proof. exact (@lem5407019 (NUMERAL 0)). Qed.
Lemma lem5407022 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5407023 : term256 = term257.
Proof. exact (@lem5407022 term79). Qed.
Lemma lem5407024 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5407025 : term258 = term259.
Proof. exact (MK_COMB (@lem5407024) (@lem5407023)). Qed.
Lemma lem5407026 : term260 = term261.
Proof. exact (MK_COMB (@lem5407025) (@lem5407020)). Qed.
Lemma lem5407027 : term261 = term262.
Proof. exact (@lem1981613 term256 term182 term193 term193). Qed.
Lemma lem5407029 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407030 : term265 = term266.
Proof. exact (@lem5407029 term79 term79). Qed.
Lemma lem5407031 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407032 : term268 = term79.
Proof. exact (EQ_MP (@lem5407031) (@lem940073)). Qed.
Lemma lem5407033 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407034 : term266 = term193.
Proof. exact (MK_COMB (@lem5407033) (@lem5407032)). Qed.
Lemma lem5407035 : term265 = term193.
Proof. exact (TRANS (@lem5407030) (@lem5407034)). Qed.
Lemma lem5407037 (x : nat) : (term269 x) = term182.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5407038 : term260 = term182.
Proof. exact (@lem5407037 term79). Qed.
Lemma lem5407039 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5407040 : term270 = term271.
Proof. exact (MK_COMB (@lem5407039) (@lem5407038)). Qed.
Lemma lem5407041 : term262 = term253.
Proof. exact (MK_COMB (@lem5407040) (@lem5407035)). Qed.
Lemma lem5407042 : term261 = term253.
Proof. exact (TRANS (@lem5407027) (@lem5407041)). Qed.
Lemma lem5407043 : term260 = term253.
Proof. exact (TRANS (@lem5407026) (@lem5407042)). Qed.
Lemma lem5407045 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5407046 : term253 = term182.
Proof. exact (@lem5407045 term182). Qed.
Lemma lem5407047 : term260 = term182.
Proof. exact (TRANS (@lem5407043) (@lem5407046)). Qed.
Lemma lem5407048 (_69904 : int) : (term194 _69904) = (term194 _69904).
Proof. exact (eq_refl (term194 _69904)). Qed.
Lemma lem5407049 (_69904 : int) : (term251 _69904) = (term273 _69904).
Proof. exact (MK_COMB (@lem5407048 _69904) (@lem5407047)). Qed.
Lemma lem5407050 (_69904 : int) : (term273 _69904) = (real_of_int _69904).
Proof. exact (@lem1982723 (real_of_int _69904)). Qed.
Lemma lem5407051 (_69904 : int) : (term251 _69904) = (real_of_int _69904).
Proof. exact (TRANS (@lem5407049 _69904) (@lem5407050 _69904)). Qed.
Lemma lem5407053 (_69904 : int) : (term250 _69904) = (real_of_int _69904).
Proof. exact (TRANS (@lem5407017 _69904) (@lem5407051 _69904)). Qed.
Lemma lem5407054 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5407055 (_69904 : int) : (term274 _69904) = (term275 _69904).
Proof. exact (MK_COMB (@lem5407054) (@lem5407053 _69904)). Qed.
Lemma lem5407056 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5407057 (_69904 : int) : (term249 _69904) = (term276 _69904).
Proof. exact (MK_COMB (@lem5407055 _69904) (@lem5407056)). Qed.
Lemma lem5407058 (_69904 : int) : (term185 _69904) = (term276 _69904).
Proof. exact (TRANS (@lem5407011 _69904) (@lem5407057 _69904)). Qed.
Lemma lem5407059 (_69905 : int) : (term185 _69905) = (term249 _69905).
Proof. exact (@lem1988287 (real_of_int _69905) term182). Qed.
Lemma lem5407065 (_69905 : int) : (term250 _69905) = (term251 _69905).
Proof. exact (@lem1982792 (real_of_int _69905) term182). Qed.
Lemma lem5407067 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5407068 : term182 = term253.
Proof. exact (@lem5407067 (NUMERAL 0)). Qed.
Lemma lem5407070 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5407071 : term256 = term257.
Proof. exact (@lem5407070 term79). Qed.
Lemma lem5407072 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5407073 : term258 = term259.
Proof. exact (MK_COMB (@lem5407072) (@lem5407071)). Qed.
Lemma lem5407074 : term260 = term261.
Proof. exact (MK_COMB (@lem5407073) (@lem5407068)). Qed.
Lemma lem5407075 : term261 = term262.
Proof. exact (@lem1981613 term256 term182 term193 term193). Qed.
Lemma lem5407077 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407078 : term265 = term266.
Proof. exact (@lem5407077 term79 term79). Qed.
Lemma lem5407079 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407080 : term268 = term79.
Proof. exact (EQ_MP (@lem5407079) (@lem940073)). Qed.
Lemma lem5407081 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407082 : term266 = term193.
Proof. exact (MK_COMB (@lem5407081) (@lem5407080)). Qed.
Lemma lem5407083 : term265 = term193.
Proof. exact (TRANS (@lem5407078) (@lem5407082)). Qed.
Lemma lem5407085 (x : nat) : (term269 x) = term182.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5407086 : term260 = term182.
Proof. exact (@lem5407085 term79). Qed.
Lemma lem5407087 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5407088 : term270 = term271.
Proof. exact (MK_COMB (@lem5407087) (@lem5407086)). Qed.
Lemma lem5407089 : term262 = term253.
Proof. exact (MK_COMB (@lem5407088) (@lem5407083)). Qed.
Lemma lem5407090 : term261 = term253.
Proof. exact (TRANS (@lem5407075) (@lem5407089)). Qed.
Lemma lem5407091 : term260 = term253.
Proof. exact (TRANS (@lem5407074) (@lem5407090)). Qed.
Lemma lem5407093 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5407094 : term253 = term182.
Proof. exact (@lem5407093 term182). Qed.
Lemma lem5407095 : term260 = term182.
Proof. exact (TRANS (@lem5407091) (@lem5407094)). Qed.
Lemma lem5407096 (_69905 : int) : (term194 _69905) = (term194 _69905).
Proof. exact (eq_refl (term194 _69905)). Qed.
Lemma lem5407097 (_69905 : int) : (term251 _69905) = (term273 _69905).
Proof. exact (MK_COMB (@lem5407096 _69905) (@lem5407095)). Qed.
Lemma lem5407098 (_69905 : int) : (term273 _69905) = (real_of_int _69905).
Proof. exact (@lem1982723 (real_of_int _69905)). Qed.
Lemma lem5407099 (_69905 : int) : (term251 _69905) = (real_of_int _69905).
Proof. exact (TRANS (@lem5407097 _69905) (@lem5407098 _69905)). Qed.
Lemma lem5407101 (_69905 : int) : (term250 _69905) = (real_of_int _69905).
Proof. exact (TRANS (@lem5407065 _69905) (@lem5407099 _69905)). Qed.
Lemma lem5407102 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5407103 (_69905 : int) : (term274 _69905) = (term275 _69905).
Proof. exact (MK_COMB (@lem5407102) (@lem5407101 _69905)). Qed.
Lemma lem5407104 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5407105 (_69905 : int) : (term249 _69905) = (term276 _69905).
Proof. exact (MK_COMB (@lem5407103 _69905) (@lem5407104)). Qed.
Lemma lem5407106 (_69905 : int) : (term185 _69905) = (term276 _69905).
Proof. exact (TRANS (@lem5407059 _69905) (@lem5407105 _69905)). Qed.
Lemma lem5407107 (_69904 : int) (_69903 : int) : (term197 _69903 _69904) = (term277 _69904 _69903).
Proof. exact (@lem1988287 (term195 _69904) (real_of_int _69903)). Qed.
Lemma lem5407119 (_69904 : int) (_69903 : int) : (term278 _69904 _69903) = (term279 _69904 _69903).
Proof. exact (@lem1982792 (term195 _69904) (real_of_int _69903)). Qed.
Lemma lem5407124 (_69903 : int) (_69904 : int) : (term279 _69904 _69903) = (term280 _69903 _69904).
Proof. exact (@lem1982761 (term281 _69903) (term195 _69904)). Qed.
Lemma lem5407126 (_69903 : int) (_69904 : int) : (term278 _69904 _69903) = (term280 _69903 _69904).
Proof. exact (TRANS (@lem5407119 _69904 _69903) (@lem5407124 _69903 _69904)). Qed.
Lemma lem5407127 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5407128 (_69903 : int) (_69904 : int) : (term282 _69904 _69903) = (term283 _69903 _69904).
Proof. exact (MK_COMB (@lem5407127) (@lem5407126 _69903 _69904)). Qed.
Lemma lem5407129 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5407130 (_69903 : int) (_69904 : int) : (term277 _69904 _69903) = (term284 _69903 _69904).
Proof. exact (MK_COMB (@lem5407128 _69903 _69904) (@lem5407129)). Qed.
Lemma lem5407131 (_69903 : int) (_69904 : int) : (term197 _69903 _69904) = (term284 _69903 _69904).
Proof. exact (TRANS (@lem5407107 _69904 _69903) (@lem5407130 _69903 _69904)). Qed.
Lemma lem5407132 (_69903 : int) (_69905 : int) : (term202 _69905 _69903) = (term285 _69903 _69905).
Proof. exact (@lem1988287 (real_of_int _69903) (term195 _69905)). Qed.
Lemma lem5407144 (_69903 : int) (_69905 : int) : (term286 _69903 _69905) = (term287 _69903 _69905).
Proof. exact (@lem1982792 (real_of_int _69903) (term195 _69905)). Qed.
Lemma lem5407145 (_69905 : int) : (term288 _69905) = (term289 _69905).
Proof. exact (@lem1982781 (real_of_int _69905) term256 term193). Qed.
Lemma lem5407147 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5407148 : term193 = term290.
Proof. exact (@lem5407147 term79). Qed.
Lemma lem5407150 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5407151 : term256 = term257.
Proof. exact (@lem5407150 term79). Qed.
Lemma lem5407152 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5407153 : term258 = term259.
Proof. exact (MK_COMB (@lem5407152) (@lem5407151)). Qed.
Lemma lem5407154 : term291 = term292.
Proof. exact (MK_COMB (@lem5407153) (@lem5407148)). Qed.
Lemma lem5407155 : term292 = term293.
Proof. exact (@lem1981613 term256 term193 term193 term193). Qed.
Lemma lem5407157 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407158 : term265 = term266.
Proof. exact (@lem5407157 term79 term79). Qed.
Lemma lem5407159 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407160 : term268 = term79.
Proof. exact (EQ_MP (@lem5407159) (@lem940073)). Qed.
Lemma lem5407161 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407162 : term266 = term193.
Proof. exact (MK_COMB (@lem5407161) (@lem5407160)). Qed.
Lemma lem5407163 : term265 = term193.
Proof. exact (TRANS (@lem5407158) (@lem5407162)). Qed.
Lemma lem5407165 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5407166 : term291 = term296.
Proof. exact (@lem5407165 term79 term79). Qed.
Lemma lem5407167 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407168 : term268 = term79.
Proof. exact (EQ_MP (@lem5407167) (@lem940073)). Qed.
Lemma lem5407169 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407170 : term266 = term193.
Proof. exact (MK_COMB (@lem5407169) (@lem5407168)). Qed.
Lemma lem5407171 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5407172 : term296 = term256.
Proof. exact (MK_COMB (@lem5407171) (@lem5407170)). Qed.
Lemma lem5407173 : term291 = term256.
Proof. exact (TRANS (@lem5407166) (@lem5407172)). Qed.
Lemma lem5407174 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5407175 : term297 = term298.
Proof. exact (MK_COMB (@lem5407174) (@lem5407173)). Qed.
Lemma lem5407176 : term293 = term257.
Proof. exact (MK_COMB (@lem5407175) (@lem5407163)). Qed.
Lemma lem5407177 : term292 = term257.
Proof. exact (TRANS (@lem5407155) (@lem5407176)). Qed.
Lemma lem5407178 : term291 = term257.
Proof. exact (TRANS (@lem5407154) (@lem5407177)). Qed.
Lemma lem5407180 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5407181 : term257 = term256.
Proof. exact (@lem5407180 term256). Qed.
Lemma lem5407182 : term291 = term256.
Proof. exact (TRANS (@lem5407178) (@lem5407181)). Qed.
Lemma lem5407185 (_69905 : int) : (term299 _69905) = (term299 _69905).
Proof. exact (eq_refl (term299 _69905)). Qed.
Lemma lem5407186 (_69905 : int) : (term289 _69905) = (term300 _69905).
Proof. exact (MK_COMB (@lem5407185 _69905) (@lem5407182)). Qed.
Lemma lem5407187 (_69905 : int) : (term288 _69905) = (term300 _69905).
Proof. exact (TRANS (@lem5407145 _69905) (@lem5407186 _69905)). Qed.
Lemma lem5407188 (_69903 : int) : (term194 _69903) = (term194 _69903).
Proof. exact (eq_refl (term194 _69903)). Qed.
Lemma lem5407191 (_69903 : int) (_69905 : int) : (term287 _69903 _69905) = (term301 _69903 _69905).
Proof. exact (MK_COMB (@lem5407188 _69903) (@lem5407187 _69905)). Qed.
Lemma lem5407193 (_69903 : int) (_69905 : int) : (term286 _69903 _69905) = (term301 _69903 _69905).
Proof. exact (TRANS (@lem5407144 _69903 _69905) (@lem5407191 _69903 _69905)). Qed.
Lemma lem5407194 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5407195 (_69903 : int) (_69905 : int) : (term302 _69903 _69905) = (term303 _69903 _69905).
Proof. exact (MK_COMB (@lem5407194) (@lem5407193 _69903 _69905)). Qed.
Lemma lem5407196 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5407197 (_69903 : int) (_69905 : int) : (term285 _69903 _69905) = (term304 _69903 _69905).
Proof. exact (MK_COMB (@lem5407195 _69903 _69905) (@lem5407196)). Qed.
Lemma lem5407198 (_69903 : int) (_69905 : int) : (term202 _69905 _69903) = (term304 _69903 _69905).
Proof. exact (TRANS (@lem5407132 _69903 _69905) (@lem5407197 _69903 _69905)). Qed.
Lemma lem5407199 (_69905 : int) (_69904 : int) : (term213 _69904 _69905) = (term305 _69905 _69904).
Proof. exact (@lem1988287 (real_of_int _69905) (term210 _69904)). Qed.
Lemma lem5407211 (_69904 : int) : (term210 _69904) = (term306 _69904).
Proof. exact (@lem1982755 (real_of_int _69904) term193 term193). Qed.
Lemma lem5407213 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5407214 : term193 = term290.
Proof. exact (@lem5407213 term79). Qed.
Lemma lem5407216 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5407217 : term193 = term290.
Proof. exact (@lem5407216 term79). Qed.
Lemma lem5407218 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5407219 : term307 = term308.
Proof. exact (MK_COMB (@lem5407218) (@lem5407217)). Qed.
Lemma lem5407220 : term309 = term310.
Proof. exact (MK_COMB (@lem5407219) (@lem5407214)). Qed.
Lemma lem5407221 : term311.
Proof. exact (@lem1981473 term193 term193 term193 term193 term312 term193). Qed.
Lemma lem5407223 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5407224 : term314 = term315.
Proof. exact (@lem5407223 (NUMERAL 0) term79). Qed.
Lemma lem5407225 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5407226 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5407227 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5407226 h1) (fun h1 : term315 = True => @lem5407225)). Qed.
Lemma lem5407228 : term315 = True.
Proof. exact (EQ_MP (@lem5407227) (@lem5407225)). Qed.
Lemma lem5407229 : term314 = True.
Proof. exact (TRANS (@lem5407224) (@lem5407228)). Qed.
Lemma lem5407230 : True = term314.
Proof. exact (SYM (@lem5407229)). Qed.
Lemma lem5407231 : term314.
Proof. exact (EQ_MP (@lem5407230) (@lem0)). Qed.
Lemma lem5407232 : term317.
Proof. exact (@lem5407221 (@lem5407231)). Qed.
Lemma lem5407234 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5407235 : term314 = term315.
Proof. exact (@lem5407234 (NUMERAL 0) term79). Qed.
Lemma lem5407236 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5407237 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5407238 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5407237 h1) (fun h1 : term315 = True => @lem5407236)). Qed.
Lemma lem5407239 : term315 = True.
Proof. exact (EQ_MP (@lem5407238) (@lem5407236)). Qed.
Lemma lem5407240 : term314 = True.
Proof. exact (TRANS (@lem5407235) (@lem5407239)). Qed.
Lemma lem5407241 : True = term314.
Proof. exact (SYM (@lem5407240)). Qed.
Lemma lem5407242 : term314.
Proof. exact (EQ_MP (@lem5407241) (@lem0)). Qed.
Lemma lem5407243 : term318.
Proof. exact (@lem5407232 (@lem5407242)). Qed.
Lemma lem5407245 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5407246 : term314 = term315.
Proof. exact (@lem5407245 (NUMERAL 0) term79). Qed.
Lemma lem5407247 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5407248 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5407249 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5407248 h1) (fun h1 : term315 = True => @lem5407247)). Qed.
Lemma lem5407250 : term315 = True.
Proof. exact (EQ_MP (@lem5407249) (@lem5407247)). Qed.
Lemma lem5407251 : term314 = True.
Proof. exact (TRANS (@lem5407246) (@lem5407250)). Qed.
Lemma lem5407252 : True = term314.
Proof. exact (SYM (@lem5407251)). Qed.
Lemma lem5407253 : term314.
Proof. exact (EQ_MP (@lem5407252) (@lem0)). Qed.
Lemma lem5407254 : term319.
Proof. exact (@lem5407243 (@lem5407253)). Qed.
Lemma lem5407256 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407257 : term265 = term266.
Proof. exact (@lem5407256 term79 term79). Qed.
Lemma lem5407258 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407259 : term268 = term79.
Proof. exact (EQ_MP (@lem5407258) (@lem940073)). Qed.
Lemma lem5407260 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407261 : term266 = term193.
Proof. exact (MK_COMB (@lem5407260) (@lem5407259)). Qed.
Lemma lem5407262 : term265 = term193.
Proof. exact (TRANS (@lem5407257) (@lem5407261)). Qed.
Lemma lem5407264 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407265 : term265 = term266.
Proof. exact (@lem5407264 term79 term79). Qed.
Lemma lem5407266 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407267 : term268 = term79.
Proof. exact (EQ_MP (@lem5407266) (@lem940073)). Qed.
Lemma lem5407268 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407269 : term266 = term193.
Proof. exact (MK_COMB (@lem5407268) (@lem5407267)). Qed.
Lemma lem5407270 : term265 = term193.
Proof. exact (TRANS (@lem5407265) (@lem5407269)). Qed.
Lemma lem5407271 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5407272 : term320 = term307.
Proof. exact (MK_COMB (@lem5407271) (@lem5407270)). Qed.
Lemma lem5407273 : term321 = term309.
Proof. exact (MK_COMB (@lem5407272) (@lem5407262)). Qed.
Lemma lem5407274 : term309 = term322.
Proof. exact (@lem1367770 term79 term79). Qed.
Lemma lem5407275 : term323 = term324.
Proof. exact (@lem706885). Qed.
Lemma lem5407276 : (term323 = term324) = (term325 = term326).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term324). Qed.
Lemma lem5407277 : term325 = term326.
Proof. exact (EQ_MP (@lem5407276) (@lem5407275)). Qed.
Lemma lem5407278 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407279 : term322 = term312.
Proof. exact (MK_COMB (@lem5407278) (@lem5407277)). Qed.
Lemma lem5407280 : term309 = term312.
Proof. exact (TRANS (@lem5407274) (@lem5407279)). Qed.
Lemma lem5407281 : term321 = term312.
Proof. exact (TRANS (@lem5407273) (@lem5407280)). Qed.
Lemma lem5407282 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5407283 : term327 = term328.
Proof. exact (MK_COMB (@lem5407282) (@lem5407281)). Qed.
Lemma lem5407284 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5407285 : term329 = term330.
Proof. exact (MK_COMB (@lem5407283) (@lem5407284)). Qed.
Lemma lem5407287 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407288 : term330 = term331.
Proof. exact (@lem5407287 term326 term79). Qed.
Lemma lem5407289 : term332 = term324.
Proof. exact (@lem996237 term324). Qed.
Lemma lem5407290 : (term332 = term324) = (term333 = term326).
Proof. exact (@lem1007663 term324 (BIT1 0) term324). Qed.
Lemma lem5407291 : term333 = term326.
Proof. exact (EQ_MP (@lem5407290) (@lem5407289)). Qed.
Lemma lem5407292 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407293 : term331 = term312.
Proof. exact (MK_COMB (@lem5407292) (@lem5407291)). Qed.
Lemma lem5407294 : term330 = term312.
Proof. exact (TRANS (@lem5407288) (@lem5407293)). Qed.
Lemma lem5407295 : term329 = term312.
Proof. exact (TRANS (@lem5407285) (@lem5407294)). Qed.
Lemma lem5407297 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407298 : term265 = term266.
Proof. exact (@lem5407297 term79 term79). Qed.
Lemma lem5407299 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407300 : term268 = term79.
Proof. exact (EQ_MP (@lem5407299) (@lem940073)). Qed.
Lemma lem5407301 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407302 : term266 = term193.
Proof. exact (MK_COMB (@lem5407301) (@lem5407300)). Qed.
Lemma lem5407303 : term265 = term193.
Proof. exact (TRANS (@lem5407298) (@lem5407302)). Qed.
Lemma lem5407304 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem5407305 : term334 = term330.
Proof. exact (MK_COMB (@lem5407304) (@lem5407303)). Qed.
Lemma lem5407307 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407308 : term330 = term331.
Proof. exact (@lem5407307 term326 term79). Qed.
Lemma lem5407309 : term332 = term324.
Proof. exact (@lem996237 term324). Qed.
Lemma lem5407310 : (term332 = term324) = (term333 = term326).
Proof. exact (@lem1007663 term324 (BIT1 0) term324). Qed.
Lemma lem5407311 : term333 = term326.
Proof. exact (EQ_MP (@lem5407310) (@lem5407309)). Qed.
Lemma lem5407312 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407313 : term331 = term312.
Proof. exact (MK_COMB (@lem5407312) (@lem5407311)). Qed.
Lemma lem5407314 : term330 = term312.
Proof. exact (TRANS (@lem5407308) (@lem5407313)). Qed.
Lemma lem5407315 : term334 = term312.
Proof. exact (TRANS (@lem5407305) (@lem5407314)). Qed.
Lemma lem5407316 : term312 = term334.
Proof. exact (SYM (@lem5407315)). Qed.
Lemma lem5407317 : term329 = term334.
Proof. exact (TRANS (@lem5407295) (@lem5407316)). Qed.
Lemma lem5407318 : term310 = term335.
Proof. exact (@lem5407254 (@lem5407317)). Qed.
Lemma lem5407319 : term309 = term335.
Proof. exact (TRANS (@lem5407220) (@lem5407318)). Qed.
Lemma lem5407321 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5407322 : term335 = term312.
Proof. exact (@lem5407321 term312). Qed.
Lemma lem5407323 : term309 = term312.
Proof. exact (TRANS (@lem5407319) (@lem5407322)). Qed.
Lemma lem5407324 (_69904 : int) : (term194 _69904) = (term194 _69904).
Proof. exact (eq_refl (term194 _69904)). Qed.
Lemma lem5407325 (_69904 : int) : (term306 _69904) = (term336 _69904).
Proof. exact (MK_COMB (@lem5407324 _69904) (@lem5407323)). Qed.
Lemma lem5407327 (_69904 : int) : (term210 _69904) = (term336 _69904).
Proof. exact (TRANS (@lem5407211 _69904) (@lem5407325 _69904)). Qed.
Lemma lem5407330 (_69905 : int) : (term337 _69905) = (term337 _69905).
Proof. exact (eq_refl (term337 _69905)). Qed.
Lemma lem5407331 (_69905 : int) (_69904 : int) : (term338 _69905 _69904) = (term339 _69905 _69904).
Proof. exact (MK_COMB (@lem5407330 _69905) (@lem5407327 _69904)). Qed.
Lemma lem5407332 (_69905 : int) (_69904 : int) : (term339 _69905 _69904) = (term340 _69905 _69904).
Proof. exact (@lem1982792 (real_of_int _69905) (term336 _69904)). Qed.
Lemma lem5407333 (_69904 : int) : (term341 _69904) = (term342 _69904).
Proof. exact (@lem1982781 (real_of_int _69904) term256 term312). Qed.
Lemma lem5407335 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5407336 : term312 = term335.
Proof. exact (@lem5407335 term326). Qed.
Lemma lem5407338 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5407339 : term256 = term257.
Proof. exact (@lem5407338 term79). Qed.
Lemma lem5407340 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5407341 : term258 = term259.
Proof. exact (MK_COMB (@lem5407340) (@lem5407339)). Qed.
Lemma lem5407342 : term343 = term344.
Proof. exact (MK_COMB (@lem5407341) (@lem5407336)). Qed.
Lemma lem5407343 : term344 = term345.
Proof. exact (@lem1981613 term256 term312 term193 term193). Qed.
Lemma lem5407345 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407346 : term265 = term266.
Proof. exact (@lem5407345 term79 term79). Qed.
Lemma lem5407347 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407348 : term268 = term79.
Proof. exact (EQ_MP (@lem5407347) (@lem940073)). Qed.
Lemma lem5407349 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407350 : term266 = term193.
Proof. exact (MK_COMB (@lem5407349) (@lem5407348)). Qed.
Lemma lem5407351 : term265 = term193.
Proof. exact (TRANS (@lem5407346) (@lem5407350)). Qed.
Lemma lem5407353 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5407354 : term343 = term346.
Proof. exact (@lem5407353 term79 term326). Qed.
Lemma lem5407355 : term347 = term324.
Proof. exact (@lem996238 term324). Qed.
Lemma lem5407356 : (term347 = term324) = (term348 = term326).
Proof. exact (@lem1007663 (BIT1 0) term324 term324). Qed.
Lemma lem5407357 : term348 = term326.
Proof. exact (EQ_MP (@lem5407356) (@lem5407355)). Qed.
Lemma lem5407358 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407359 : term349 = term312.
Proof. exact (MK_COMB (@lem5407358) (@lem5407357)). Qed.
Lemma lem5407360 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5407361 : term346 = term350.
Proof. exact (MK_COMB (@lem5407360) (@lem5407359)). Qed.
Lemma lem5407362 : term343 = term350.
Proof. exact (TRANS (@lem5407354) (@lem5407361)). Qed.
Lemma lem5407363 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5407364 : term351 = term352.
Proof. exact (MK_COMB (@lem5407363) (@lem5407362)). Qed.
Lemma lem5407365 : term345 = term353.
Proof. exact (MK_COMB (@lem5407364) (@lem5407351)). Qed.
Lemma lem5407366 : term344 = term353.
Proof. exact (TRANS (@lem5407343) (@lem5407365)). Qed.
Lemma lem5407367 : term343 = term353.
Proof. exact (TRANS (@lem5407342) (@lem5407366)). Qed.
Lemma lem5407369 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5407370 : term353 = term350.
Proof. exact (@lem5407369 term350). Qed.
Lemma lem5407371 : term343 = term350.
Proof. exact (TRANS (@lem5407367) (@lem5407370)). Qed.
Lemma lem5407374 (_69904 : int) : (term299 _69904) = (term299 _69904).
Proof. exact (eq_refl (term299 _69904)). Qed.
Lemma lem5407375 (_69904 : int) : (term342 _69904) = (term354 _69904).
Proof. exact (MK_COMB (@lem5407374 _69904) (@lem5407371)). Qed.
Lemma lem5407376 (_69904 : int) : (term341 _69904) = (term354 _69904).
Proof. exact (TRANS (@lem5407333 _69904) (@lem5407375 _69904)). Qed.
Lemma lem5407377 (_69905 : int) : (term194 _69905) = (term194 _69905).
Proof. exact (eq_refl (term194 _69905)). Qed.
Lemma lem5407378 (_69905 : int) (_69904 : int) : (term340 _69905 _69904) = (term355 _69905 _69904).
Proof. exact (MK_COMB (@lem5407377 _69905) (@lem5407376 _69904)). Qed.
Lemma lem5407383 (_69904 : int) (_69905 : int) : (term355 _69905 _69904) = (term356 _69904 _69905).
Proof. exact (@lem1982757 (term281 _69904) (real_of_int _69905) term350). Qed.
Lemma lem5407384 (_69904 : int) (_69905 : int) : (term340 _69905 _69904) = (term356 _69904 _69905).
Proof. exact (TRANS (@lem5407378 _69905 _69904) (@lem5407383 _69904 _69905)). Qed.
Lemma lem5407385 (_69904 : int) (_69905 : int) : (term339 _69905 _69904) = (term356 _69904 _69905).
Proof. exact (TRANS (@lem5407332 _69905 _69904) (@lem5407384 _69904 _69905)). Qed.
Lemma lem5407386 (_69904 : int) (_69905 : int) : (term338 _69905 _69904) = (term356 _69904 _69905).
Proof. exact (TRANS (@lem5407331 _69905 _69904) (@lem5407385 _69904 _69905)). Qed.
Lemma lem5407387 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5407388 (_69904 : int) (_69905 : int) : (term357 _69905 _69904) = (term358 _69904 _69905).
Proof. exact (MK_COMB (@lem5407387) (@lem5407386 _69904 _69905)). Qed.
Lemma lem5407389 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5407390 (_69904 : int) (_69905 : int) : (term305 _69905 _69904) = (term359 _69904 _69905).
Proof. exact (MK_COMB (@lem5407388 _69904 _69905) (@lem5407389)). Qed.
Lemma lem5407391 (_69904 : int) (_69905 : int) : (term213 _69904 _69905) = (term359 _69904 _69905).
Proof. exact (TRANS (@lem5407199 _69905 _69904) (@lem5407390 _69904 _69905)). Qed.
Lemma lem5407392 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5407393 (_69903 : int) (_69905 : int) : (term215 _69905 _69903) = (term360 _69903 _69905).
Proof. exact (MK_COMB (@lem5407392) (@lem5407198 _69903 _69905)). Qed.
Lemma lem5407394 (_69903 : int) (_69904 : int) (_69905 : int) : (term216 _69903 _69904 _69905) = (term361 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5407393 _69903 _69905) (@lem5407391 _69904 _69905)). Qed.
Lemma lem5407395 (_69905 : int) (_69904 : int) : ((real_of_int _69905) = (term195 _69904)) = ((term286 _69905 _69904) = term182).
Proof. exact (@lem1988293 (real_of_int _69905) (term195 _69904)). Qed.
Lemma lem5407407 (_69905 : int) (_69904 : int) : (term286 _69905 _69904) = (term287 _69905 _69904).
Proof. exact (@lem1982792 (real_of_int _69905) (term195 _69904)). Qed.
Lemma lem5407408 (_69904 : int) : (term288 _69904) = (term289 _69904).
Proof. exact (@lem1982781 (real_of_int _69904) term256 term193). Qed.
Lemma lem5407410 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5407411 : term193 = term290.
Proof. exact (@lem5407410 term79). Qed.
Lemma lem5407413 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5407414 : term256 = term257.
Proof. exact (@lem5407413 term79). Qed.
Lemma lem5407415 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5407416 : term258 = term259.
Proof. exact (MK_COMB (@lem5407415) (@lem5407414)). Qed.
Lemma lem5407417 : term291 = term292.
Proof. exact (MK_COMB (@lem5407416) (@lem5407411)). Qed.
Lemma lem5407418 : term292 = term293.
Proof. exact (@lem1981613 term256 term193 term193 term193). Qed.
Lemma lem5407420 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407421 : term265 = term266.
Proof. exact (@lem5407420 term79 term79). Qed.
Lemma lem5407422 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407423 : term268 = term79.
Proof. exact (EQ_MP (@lem5407422) (@lem940073)). Qed.
Lemma lem5407424 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407425 : term266 = term193.
Proof. exact (MK_COMB (@lem5407424) (@lem5407423)). Qed.
Lemma lem5407426 : term265 = term193.
Proof. exact (TRANS (@lem5407421) (@lem5407425)). Qed.
Lemma lem5407428 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5407429 : term291 = term296.
Proof. exact (@lem5407428 term79 term79). Qed.
Lemma lem5407430 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407431 : term268 = term79.
Proof. exact (EQ_MP (@lem5407430) (@lem940073)). Qed.
Lemma lem5407432 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407433 : term266 = term193.
Proof. exact (MK_COMB (@lem5407432) (@lem5407431)). Qed.
Lemma lem5407434 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5407435 : term296 = term256.
Proof. exact (MK_COMB (@lem5407434) (@lem5407433)). Qed.
Lemma lem5407436 : term291 = term256.
Proof. exact (TRANS (@lem5407429) (@lem5407435)). Qed.
Lemma lem5407437 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5407438 : term297 = term298.
Proof. exact (MK_COMB (@lem5407437) (@lem5407436)). Qed.
Lemma lem5407439 : term293 = term257.
Proof. exact (MK_COMB (@lem5407438) (@lem5407426)). Qed.
Lemma lem5407440 : term292 = term257.
Proof. exact (TRANS (@lem5407418) (@lem5407439)). Qed.
Lemma lem5407441 : term291 = term257.
Proof. exact (TRANS (@lem5407417) (@lem5407440)). Qed.
Lemma lem5407443 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5407444 : term257 = term256.
Proof. exact (@lem5407443 term256). Qed.
Lemma lem5407445 : term291 = term256.
Proof. exact (TRANS (@lem5407441) (@lem5407444)). Qed.
Lemma lem5407448 (_69904 : int) : (term299 _69904) = (term299 _69904).
Proof. exact (eq_refl (term299 _69904)). Qed.
Lemma lem5407449 (_69904 : int) : (term289 _69904) = (term300 _69904).
Proof. exact (MK_COMB (@lem5407448 _69904) (@lem5407445)). Qed.
Lemma lem5407450 (_69904 : int) : (term288 _69904) = (term300 _69904).
Proof. exact (TRANS (@lem5407408 _69904) (@lem5407449 _69904)). Qed.
Lemma lem5407451 (_69905 : int) : (term194 _69905) = (term194 _69905).
Proof. exact (eq_refl (term194 _69905)). Qed.
Lemma lem5407452 (_69905 : int) (_69904 : int) : (term287 _69905 _69904) = (term301 _69905 _69904).
Proof. exact (MK_COMB (@lem5407451 _69905) (@lem5407450 _69904)). Qed.
Lemma lem5407457 (_69904 : int) (_69905 : int) : (term301 _69905 _69904) = (term362 _69904 _69905).
Proof. exact (@lem1982757 (term281 _69904) (real_of_int _69905) term256). Qed.
Lemma lem5407458 (_69904 : int) (_69905 : int) : (term287 _69905 _69904) = (term362 _69904 _69905).
Proof. exact (TRANS (@lem5407452 _69905 _69904) (@lem5407457 _69904 _69905)). Qed.
Lemma lem5407460 (_69904 : int) (_69905 : int) : (term286 _69905 _69904) = (term362 _69904 _69905).
Proof. exact (TRANS (@lem5407407 _69905 _69904) (@lem5407458 _69904 _69905)). Qed.
Lemma lem5407461 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5407462 (_69904 : int) (_69905 : int) : (term363 _69905 _69904) = (term364 _69904 _69905).
Proof. exact (MK_COMB (@lem5407461) (@lem5407460 _69904 _69905)). Qed.
Lemma lem5407463 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5407464 (_69904 : int) (_69905 : int) : ((term286 _69905 _69904) = term182) = ((term362 _69904 _69905) = term182).
Proof. exact (MK_COMB (@lem5407462 _69904 _69905) (@lem5407463)). Qed.
Lemma lem5407465 (_69904 : int) (_69905 : int) : ((real_of_int _69905) = (term195 _69904)) = ((term362 _69904 _69905) = term182).
Proof. exact (TRANS (@lem5407395 _69905 _69904) (@lem5407464 _69904 _69905)). Qed.
Lemma lem5407466 (_69905 : int) (_69903 : int) : (term177 _69903 _69905) = (term365 _69905 _69903).
Proof. exact (@lem1988287 (real_of_int _69905) (real_of_int _69903)). Qed.
Lemma lem5407472 (_69905 : int) (_69903 : int) : (term366 _69905 _69903) = (term367 _69905 _69903).
Proof. exact (@lem1982792 (real_of_int _69905) (real_of_int _69903)). Qed.
Lemma lem5407477 (_69903 : int) (_69905 : int) : (term367 _69905 _69903) = (term368 _69903 _69905).
Proof. exact (@lem1982761 (term281 _69903) (real_of_int _69905)). Qed.
Lemma lem5407479 (_69903 : int) (_69905 : int) : (term366 _69905 _69903) = (term368 _69903 _69905).
Proof. exact (TRANS (@lem5407472 _69905 _69903) (@lem5407477 _69903 _69905)). Qed.
Lemma lem5407480 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5407481 (_69903 : int) (_69905 : int) : (term369 _69905 _69903) = (term370 _69903 _69905).
Proof. exact (MK_COMB (@lem5407480) (@lem5407479 _69903 _69905)). Qed.
Lemma lem5407482 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5407483 (_69903 : int) (_69905 : int) : (term365 _69905 _69903) = (term371 _69903 _69905).
Proof. exact (MK_COMB (@lem5407481 _69903 _69905) (@lem5407482)). Qed.
Lemma lem5407484 (_69903 : int) (_69905 : int) : (term177 _69903 _69905) = (term371 _69903 _69905).
Proof. exact (TRANS (@lem5407466 _69905 _69903) (@lem5407483 _69903 _69905)). Qed.
Lemma lem5407485 (_69904 : int) (_69905 : int) : (term177 _69905 _69904) = (term365 _69904 _69905).
Proof. exact (@lem1988287 (real_of_int _69904) (real_of_int _69905)). Qed.
Lemma lem5407498 (_69904 : int) (_69905 : int) : (term366 _69904 _69905) = (term367 _69904 _69905).
Proof. exact (@lem1982792 (real_of_int _69904) (real_of_int _69905)). Qed.
Lemma lem5407499 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5407500 (_69904 : int) (_69905 : int) : (term369 _69904 _69905) = (term372 _69904 _69905).
Proof. exact (MK_COMB (@lem5407499) (@lem5407498 _69904 _69905)). Qed.
Lemma lem5407501 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5407502 (_69904 : int) (_69905 : int) : (term365 _69904 _69905) = (term373 _69904 _69905).
Proof. exact (MK_COMB (@lem5407500 _69904 _69905) (@lem5407501)). Qed.
Lemma lem5407503 (_69904 : int) (_69905 : int) : (term177 _69905 _69904) = (term373 _69904 _69905).
Proof. exact (TRANS (@lem5407485 _69904 _69905) (@lem5407502 _69904 _69905)). Qed.
Lemma lem5407504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5407505 (_69903 : int) (_69905 : int) : (term218 _69903 _69905) = (term374 _69903 _69905).
Proof. exact (MK_COMB (@lem5407504) (@lem5407484 _69903 _69905)). Qed.
Lemma lem5407506 (_69903 : int) (_69904 : int) (_69905 : int) : (term219 _69903 _69905 _69904) = (term375 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5407505 _69903 _69905) (@lem5407503 _69904 _69905)). Qed.
Lemma lem5407507 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5407508 (_69904 : int) (_69905 : int) : (term220 _69905 _69904) = (term376 _69904 _69905).
Proof. exact (MK_COMB (@lem5407507) (@lem5407465 _69904 _69905)). Qed.
Lemma lem5407509 (_69903 : int) (_69904 : int) (_69905 : int) : (term221 _69903 _69905 _69904) = (term377 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5407508 _69904 _69905) (@lem5407506 _69903 _69904 _69905)). Qed.
Lemma lem5407510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5407511 (_69903 : int) (_69904 : int) (_69905 : int) : (term222 _69903 _69904 _69905) = (term378 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5407510) (@lem5407394 _69903 _69904 _69905)). Qed.
Lemma lem5407512 (_69903 : int) (_69904 : int) (_69905 : int) : (term223 _69903 _69905 _69904) = (term379 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5407511 _69903 _69904 _69905) (@lem5407509 _69903 _69904 _69905)). Qed.
Lemma lem5407513 (_69905 : int) (_69903 : int) : (term177 _69903 _69905) = (term365 _69905 _69903).
Proof. exact (@lem1988287 (real_of_int _69905) (real_of_int _69903)). Qed.
Lemma lem5407519 (_69905 : int) (_69903 : int) : (term366 _69905 _69903) = (term367 _69905 _69903).
Proof. exact (@lem1982792 (real_of_int _69905) (real_of_int _69903)). Qed.
Lemma lem5407524 (_69903 : int) (_69905 : int) : (term367 _69905 _69903) = (term368 _69903 _69905).
Proof. exact (@lem1982761 (term281 _69903) (real_of_int _69905)). Qed.
Lemma lem5407526 (_69903 : int) (_69905 : int) : (term366 _69905 _69903) = (term368 _69903 _69905).
Proof. exact (TRANS (@lem5407519 _69905 _69903) (@lem5407524 _69903 _69905)). Qed.
Lemma lem5407527 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5407528 (_69903 : int) (_69905 : int) : (term369 _69905 _69903) = (term370 _69903 _69905).
Proof. exact (MK_COMB (@lem5407527) (@lem5407526 _69903 _69905)). Qed.
Lemma lem5407529 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5407530 (_69903 : int) (_69905 : int) : (term365 _69905 _69903) = (term371 _69903 _69905).
Proof. exact (MK_COMB (@lem5407528 _69903 _69905) (@lem5407529)). Qed.
Lemma lem5407531 (_69903 : int) (_69905 : int) : (term177 _69903 _69905) = (term371 _69903 _69905).
Proof. exact (TRANS (@lem5407513 _69905 _69903) (@lem5407530 _69903 _69905)). Qed.
Lemma lem5407532 (_69904 : int) (_69905 : int) : (term197 _69905 _69904) = (term277 _69904 _69905).
Proof. exact (@lem1988287 (term195 _69904) (real_of_int _69905)). Qed.
Lemma lem5407544 (_69904 : int) (_69905 : int) : (term278 _69904 _69905) = (term279 _69904 _69905).
Proof. exact (@lem1982792 (term195 _69904) (real_of_int _69905)). Qed.
Lemma lem5407548 (_69904 : int) (_69905 : int) : (term279 _69904 _69905) = (term380 _69904 _69905).
Proof. exact (@lem1982755 (real_of_int _69904) term193 (term281 _69905)). Qed.
Lemma lem5407549 (_69905 : int) : (term381 _69905) = (term382 _69905).
Proof. exact (@lem1982761 (term281 _69905) term193). Qed.
Lemma lem5407550 (_69904 : int) : (term194 _69904) = (term194 _69904).
Proof. exact (eq_refl (term194 _69904)). Qed.
Lemma lem5407551 (_69904 : int) (_69905 : int) : (term380 _69904 _69905) = (term383 _69904 _69905).
Proof. exact (MK_COMB (@lem5407550 _69904) (@lem5407549 _69905)). Qed.
Lemma lem5407553 (_69904 : int) (_69905 : int) : (term279 _69904 _69905) = (term383 _69904 _69905).
Proof. exact (TRANS (@lem5407548 _69904 _69905) (@lem5407551 _69904 _69905)). Qed.
Lemma lem5407555 (_69904 : int) (_69905 : int) : (term278 _69904 _69905) = (term383 _69904 _69905).
Proof. exact (TRANS (@lem5407544 _69904 _69905) (@lem5407553 _69904 _69905)). Qed.
Lemma lem5407556 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5407557 (_69904 : int) (_69905 : int) : (term282 _69904 _69905) = (term384 _69904 _69905).
Proof. exact (MK_COMB (@lem5407556) (@lem5407555 _69904 _69905)). Qed.
Lemma lem5407558 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5407559 (_69904 : int) (_69905 : int) : (term277 _69904 _69905) = (term385 _69904 _69905).
Proof. exact (MK_COMB (@lem5407557 _69904 _69905) (@lem5407558)). Qed.
Lemma lem5407560 (_69904 : int) (_69905 : int) : (term197 _69905 _69904) = (term385 _69904 _69905).
Proof. exact (TRANS (@lem5407532 _69904 _69905) (@lem5407559 _69904 _69905)). Qed.
Lemma lem5407561 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5407562 (_69903 : int) (_69905 : int) : (term218 _69903 _69905) = (term374 _69903 _69905).
Proof. exact (MK_COMB (@lem5407561) (@lem5407531 _69903 _69905)). Qed.
Lemma lem5407563 (_69903 : int) (_69904 : int) (_69905 : int) : (term224 _69903 _69905 _69904) = (term386 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5407562 _69903 _69905) (@lem5407560 _69904 _69905)). Qed.
Lemma lem5407564 (_69904 : int) (_69905 : int) : (term230 _69905 _69904) = (term387 _69904 _69905).
Proof. exact (@lem1988287 (term195 _69904) (term195 _69905)). Qed.
Lemma lem5407582 (_69904 : int) (_69905 : int) : (term388 _69904 _69905) = (term389 _69904 _69905).
Proof. exact (@lem1982792 (term195 _69904) (term195 _69905)). Qed.
Lemma lem5407583 (_69905 : int) : (term288 _69905) = (term289 _69905).
Proof. exact (@lem1982781 (real_of_int _69905) term256 term193). Qed.
Lemma lem5407585 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5407586 : term193 = term290.
Proof. exact (@lem5407585 term79). Qed.
Lemma lem5407588 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5407589 : term256 = term257.
Proof. exact (@lem5407588 term79). Qed.
Lemma lem5407590 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5407591 : term258 = term259.
Proof. exact (MK_COMB (@lem5407590) (@lem5407589)). Qed.
Lemma lem5407592 : term291 = term292.
Proof. exact (MK_COMB (@lem5407591) (@lem5407586)). Qed.
Lemma lem5407593 : term292 = term293.
Proof. exact (@lem1981613 term256 term193 term193 term193). Qed.
Lemma lem5407595 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407596 : term265 = term266.
Proof. exact (@lem5407595 term79 term79). Qed.
Lemma lem5407597 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407598 : term268 = term79.
Proof. exact (EQ_MP (@lem5407597) (@lem940073)). Qed.
Lemma lem5407599 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407600 : term266 = term193.
Proof. exact (MK_COMB (@lem5407599) (@lem5407598)). Qed.
Lemma lem5407601 : term265 = term193.
Proof. exact (TRANS (@lem5407596) (@lem5407600)). Qed.
Lemma lem5407603 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5407604 : term291 = term296.
Proof. exact (@lem5407603 term79 term79). Qed.
Lemma lem5407605 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407606 : term268 = term79.
Proof. exact (EQ_MP (@lem5407605) (@lem940073)). Qed.
Lemma lem5407607 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407608 : term266 = term193.
Proof. exact (MK_COMB (@lem5407607) (@lem5407606)). Qed.
Lemma lem5407609 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5407610 : term296 = term256.
Proof. exact (MK_COMB (@lem5407609) (@lem5407608)). Qed.
Lemma lem5407611 : term291 = term256.
Proof. exact (TRANS (@lem5407604) (@lem5407610)). Qed.
Lemma lem5407612 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5407613 : term297 = term298.
Proof. exact (MK_COMB (@lem5407612) (@lem5407611)). Qed.
Lemma lem5407614 : term293 = term257.
Proof. exact (MK_COMB (@lem5407613) (@lem5407601)). Qed.
Lemma lem5407615 : term292 = term257.
Proof. exact (TRANS (@lem5407593) (@lem5407614)). Qed.
Lemma lem5407616 : term291 = term257.
Proof. exact (TRANS (@lem5407592) (@lem5407615)). Qed.
Lemma lem5407618 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5407619 : term257 = term256.
Proof. exact (@lem5407618 term256). Qed.
Lemma lem5407620 : term291 = term256.
Proof. exact (TRANS (@lem5407616) (@lem5407619)). Qed.
Lemma lem5407623 (_69905 : int) : (term299 _69905) = (term299 _69905).
Proof. exact (eq_refl (term299 _69905)). Qed.
Lemma lem5407624 (_69905 : int) : (term289 _69905) = (term300 _69905).
Proof. exact (MK_COMB (@lem5407623 _69905) (@lem5407620)). Qed.
Lemma lem5407625 (_69905 : int) : (term288 _69905) = (term300 _69905).
Proof. exact (TRANS (@lem5407583 _69905) (@lem5407624 _69905)). Qed.
Lemma lem5407626 (_69904 : int) : (term209 _69904) = (term209 _69904).
Proof. exact (eq_refl (term209 _69904)). Qed.
Lemma lem5407627 (_69904 : int) (_69905 : int) : (term389 _69904 _69905) = (term390 _69904 _69905).
Proof. exact (MK_COMB (@lem5407626 _69904) (@lem5407625 _69905)). Qed.
Lemma lem5407628 (_69904 : int) (_69905 : int) : (term390 _69904 _69905) = (term391 _69904 _69905).
Proof. exact (@lem1982755 (real_of_int _69904) term193 (term300 _69905)). Qed.
Lemma lem5407629 (_69905 : int) : (term392 _69905) = (term393 _69905).
Proof. exact (@lem1982757 (term281 _69905) term193 term256). Qed.
Lemma lem5407631 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5407632 : term256 = term257.
Proof. exact (@lem5407631 term79). Qed.
Lemma lem5407634 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5407635 : term193 = term290.
Proof. exact (@lem5407634 term79). Qed.
Lemma lem5407636 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5407637 : term307 = term308.
Proof. exact (MK_COMB (@lem5407636) (@lem5407635)). Qed.
Lemma lem5407638 : term394 = term395.
Proof. exact (MK_COMB (@lem5407637) (@lem5407632)). Qed.
Lemma lem5407639 : term396.
Proof. exact (@lem1981473 term193 term193 term256 term193 term182 term193). Qed.
Lemma lem5407641 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5407642 : term314 = term315.
Proof. exact (@lem5407641 (NUMERAL 0) term79). Qed.
Lemma lem5407643 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5407644 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5407645 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5407644 h1) (fun h1 : term315 = True => @lem5407643)). Qed.
Lemma lem5407646 : term315 = True.
Proof. exact (EQ_MP (@lem5407645) (@lem5407643)). Qed.
Lemma lem5407647 : term314 = True.
Proof. exact (TRANS (@lem5407642) (@lem5407646)). Qed.
Lemma lem5407648 : True = term314.
Proof. exact (SYM (@lem5407647)). Qed.
Lemma lem5407649 : term314.
Proof. exact (EQ_MP (@lem5407648) (@lem0)). Qed.
Lemma lem5407650 : term397.
Proof. exact (@lem5407639 (@lem5407649)). Qed.
Lemma lem5407652 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5407653 : term314 = term315.
Proof. exact (@lem5407652 (NUMERAL 0) term79). Qed.
Lemma lem5407654 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5407655 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5407656 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5407655 h1) (fun h1 : term315 = True => @lem5407654)). Qed.
Lemma lem5407657 : term315 = True.
Proof. exact (EQ_MP (@lem5407656) (@lem5407654)). Qed.
Lemma lem5407658 : term314 = True.
Proof. exact (TRANS (@lem5407653) (@lem5407657)). Qed.
Lemma lem5407659 : True = term314.
Proof. exact (SYM (@lem5407658)). Qed.
Lemma lem5407660 : term314.
Proof. exact (EQ_MP (@lem5407659) (@lem0)). Qed.
Lemma lem5407661 : term398.
Proof. exact (@lem5407650 (@lem5407660)). Qed.
Lemma lem5407663 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5407664 : term314 = term315.
Proof. exact (@lem5407663 (NUMERAL 0) term79). Qed.
Lemma lem5407665 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5407666 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5407667 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5407666 h1) (fun h1 : term315 = True => @lem5407665)). Qed.
Lemma lem5407668 : term315 = True.
Proof. exact (EQ_MP (@lem5407667) (@lem5407665)). Qed.
Lemma lem5407669 : term314 = True.
Proof. exact (TRANS (@lem5407664) (@lem5407668)). Qed.
Lemma lem5407670 : True = term314.
Proof. exact (SYM (@lem5407669)). Qed.
Lemma lem5407671 : term314.
Proof. exact (EQ_MP (@lem5407670) (@lem0)). Qed.
Lemma lem5407672 : term399.
Proof. exact (@lem5407661 (@lem5407671)). Qed.
Lemma lem5407674 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5407675 : term291 = term296.
Proof. exact (@lem5407674 term79 term79). Qed.
Lemma lem5407676 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407677 : term268 = term79.
Proof. exact (EQ_MP (@lem5407676) (@lem940073)). Qed.
Lemma lem5407678 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407679 : term266 = term193.
Proof. exact (MK_COMB (@lem5407678) (@lem5407677)). Qed.
Lemma lem5407680 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5407681 : term296 = term256.
Proof. exact (MK_COMB (@lem5407680) (@lem5407679)). Qed.
Lemma lem5407682 : term291 = term256.
Proof. exact (TRANS (@lem5407675) (@lem5407681)). Qed.
Lemma lem5407684 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407685 : term265 = term266.
Proof. exact (@lem5407684 term79 term79). Qed.
Lemma lem5407686 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407687 : term268 = term79.
Proof. exact (EQ_MP (@lem5407686) (@lem940073)). Qed.
Lemma lem5407688 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407689 : term266 = term193.
Proof. exact (MK_COMB (@lem5407688) (@lem5407687)). Qed.
Lemma lem5407690 : term265 = term193.
Proof. exact (TRANS (@lem5407685) (@lem5407689)). Qed.
Lemma lem5407691 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5407692 : term320 = term307.
Proof. exact (MK_COMB (@lem5407691) (@lem5407690)). Qed.
Lemma lem5407693 : term400 = term394.
Proof. exact (MK_COMB (@lem5407692) (@lem5407682)). Qed.
Lemma lem5407695 (m : nat) : (term401 m) = term182.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5407696 : term394 = term182.
Proof. exact (@lem5407695 term79). Qed.
Lemma lem5407697 : term400 = term182.
Proof. exact (TRANS (@lem5407693) (@lem5407696)). Qed.
Lemma lem5407698 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5407699 : term402 = term403.
Proof. exact (MK_COMB (@lem5407698) (@lem5407697)). Qed.
Lemma lem5407700 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5407701 : term404 = term405.
Proof. exact (MK_COMB (@lem5407699) (@lem5407700)). Qed.
Lemma lem5407703 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5407704 : term405 = term182.
Proof. exact (@lem5407703 term79). Qed.
Lemma lem5407705 : term404 = term182.
Proof. exact (TRANS (@lem5407701) (@lem5407704)). Qed.
Lemma lem5407707 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407708 : term265 = term266.
Proof. exact (@lem5407707 term79 term79). Qed.
Lemma lem5407709 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407710 : term268 = term79.
Proof. exact (EQ_MP (@lem5407709) (@lem940073)). Qed.
Lemma lem5407711 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407712 : term266 = term193.
Proof. exact (MK_COMB (@lem5407711) (@lem5407710)). Qed.
Lemma lem5407713 : term265 = term193.
Proof. exact (TRANS (@lem5407708) (@lem5407712)). Qed.
Lemma lem5407714 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5407715 : term407 = term405.
Proof. exact (MK_COMB (@lem5407714) (@lem5407713)). Qed.
Lemma lem5407717 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5407718 : term405 = term182.
Proof. exact (@lem5407717 term79). Qed.
Lemma lem5407719 : term407 = term182.
Proof. exact (TRANS (@lem5407715) (@lem5407718)). Qed.
Lemma lem5407720 : term182 = term407.
Proof. exact (SYM (@lem5407719)). Qed.
Lemma lem5407721 : term404 = term407.
Proof. exact (TRANS (@lem5407705) (@lem5407720)). Qed.
Lemma lem5407722 : term395 = term253.
Proof. exact (@lem5407672 (@lem5407721)). Qed.
Lemma lem5407723 : term394 = term253.
Proof. exact (TRANS (@lem5407638) (@lem5407722)). Qed.
Lemma lem5407725 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5407726 : term253 = term182.
Proof. exact (@lem5407725 term182). Qed.
Lemma lem5407727 : term394 = term182.
Proof. exact (TRANS (@lem5407723) (@lem5407726)). Qed.
Lemma lem5407728 (_69905 : int) : (term299 _69905) = (term299 _69905).
Proof. exact (eq_refl (term299 _69905)). Qed.
Lemma lem5407729 (_69905 : int) : (term393 _69905) = (term408 _69905).
Proof. exact (MK_COMB (@lem5407728 _69905) (@lem5407727)). Qed.
Lemma lem5407730 (_69905 : int) : (term392 _69905) = (term408 _69905).
Proof. exact (TRANS (@lem5407629 _69905) (@lem5407729 _69905)). Qed.
Lemma lem5407731 (_69905 : int) : (term408 _69905) = (term281 _69905).
Proof. exact (@lem1982723 (term281 _69905)). Qed.
Lemma lem5407732 (_69905 : int) : (term392 _69905) = (term281 _69905).
Proof. exact (TRANS (@lem5407730 _69905) (@lem5407731 _69905)). Qed.
Lemma lem5407733 (_69904 : int) : (term194 _69904) = (term194 _69904).
Proof. exact (eq_refl (term194 _69904)). Qed.
Lemma lem5407734 (_69904 : int) (_69905 : int) : (term391 _69904 _69905) = (term367 _69904 _69905).
Proof. exact (MK_COMB (@lem5407733 _69904) (@lem5407732 _69905)). Qed.
Lemma lem5407735 (_69904 : int) (_69905 : int) : (term390 _69904 _69905) = (term367 _69904 _69905).
Proof. exact (TRANS (@lem5407628 _69904 _69905) (@lem5407734 _69904 _69905)). Qed.
Lemma lem5407736 (_69904 : int) (_69905 : int) : (term389 _69904 _69905) = (term367 _69904 _69905).
Proof. exact (TRANS (@lem5407627 _69904 _69905) (@lem5407735 _69904 _69905)). Qed.
Lemma lem5407738 (_69904 : int) (_69905 : int) : (term388 _69904 _69905) = (term367 _69904 _69905).
Proof. exact (TRANS (@lem5407582 _69904 _69905) (@lem5407736 _69904 _69905)). Qed.
Lemma lem5407739 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5407740 (_69904 : int) (_69905 : int) : (term409 _69904 _69905) = (term372 _69904 _69905).
Proof. exact (MK_COMB (@lem5407739) (@lem5407738 _69904 _69905)). Qed.
Lemma lem5407741 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5407742 (_69904 : int) (_69905 : int) : (term387 _69904 _69905) = (term373 _69904 _69905).
Proof. exact (MK_COMB (@lem5407740 _69904 _69905) (@lem5407741)). Qed.
Lemma lem5407743 (_69904 : int) (_69905 : int) : (term230 _69905 _69904) = (term373 _69904 _69905).
Proof. exact (TRANS (@lem5407564 _69904 _69905) (@lem5407742 _69904 _69905)). Qed.
Lemma lem5407744 (_69905 : int) (_69904 : int) : (term213 _69904 _69905) = (term305 _69905 _69904).
Proof. exact (@lem1988287 (real_of_int _69905) (term210 _69904)). Qed.
Lemma lem5407756 (_69904 : int) : (term210 _69904) = (term306 _69904).
Proof. exact (@lem1982755 (real_of_int _69904) term193 term193). Qed.
Lemma lem5407758 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5407759 : term193 = term290.
Proof. exact (@lem5407758 term79). Qed.
Lemma lem5407761 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5407762 : term193 = term290.
Proof. exact (@lem5407761 term79). Qed.
Lemma lem5407763 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5407764 : term307 = term308.
Proof. exact (MK_COMB (@lem5407763) (@lem5407762)). Qed.
Lemma lem5407765 : term309 = term310.
Proof. exact (MK_COMB (@lem5407764) (@lem5407759)). Qed.
Lemma lem5407766 : term311.
Proof. exact (@lem1981473 term193 term193 term193 term193 term312 term193). Qed.
Lemma lem5407768 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5407769 : term314 = term315.
Proof. exact (@lem5407768 (NUMERAL 0) term79). Qed.
Lemma lem5407770 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5407771 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5407772 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5407771 h1) (fun h1 : term315 = True => @lem5407770)). Qed.
Lemma lem5407773 : term315 = True.
Proof. exact (EQ_MP (@lem5407772) (@lem5407770)). Qed.
Lemma lem5407774 : term314 = True.
Proof. exact (TRANS (@lem5407769) (@lem5407773)). Qed.
Lemma lem5407775 : True = term314.
Proof. exact (SYM (@lem5407774)). Qed.
Lemma lem5407776 : term314.
Proof. exact (EQ_MP (@lem5407775) (@lem0)). Qed.
Lemma lem5407777 : term317.
Proof. exact (@lem5407766 (@lem5407776)). Qed.
Lemma lem5407779 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5407780 : term314 = term315.
Proof. exact (@lem5407779 (NUMERAL 0) term79). Qed.
Lemma lem5407781 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5407782 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5407783 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5407782 h1) (fun h1 : term315 = True => @lem5407781)). Qed.
Lemma lem5407784 : term315 = True.
Proof. exact (EQ_MP (@lem5407783) (@lem5407781)). Qed.
Lemma lem5407785 : term314 = True.
Proof. exact (TRANS (@lem5407780) (@lem5407784)). Qed.
Lemma lem5407786 : True = term314.
Proof. exact (SYM (@lem5407785)). Qed.
Lemma lem5407787 : term314.
Proof. exact (EQ_MP (@lem5407786) (@lem0)). Qed.
Lemma lem5407788 : term318.
Proof. exact (@lem5407777 (@lem5407787)). Qed.
Lemma lem5407790 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5407791 : term314 = term315.
Proof. exact (@lem5407790 (NUMERAL 0) term79). Qed.
Lemma lem5407792 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5407793 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5407794 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5407793 h1) (fun h1 : term315 = True => @lem5407792)). Qed.
Lemma lem5407795 : term315 = True.
Proof. exact (EQ_MP (@lem5407794) (@lem5407792)). Qed.
Lemma lem5407796 : term314 = True.
Proof. exact (TRANS (@lem5407791) (@lem5407795)). Qed.
Lemma lem5407797 : True = term314.
Proof. exact (SYM (@lem5407796)). Qed.
Lemma lem5407798 : term314.
Proof. exact (EQ_MP (@lem5407797) (@lem0)). Qed.
Lemma lem5407799 : term319.
Proof. exact (@lem5407788 (@lem5407798)). Qed.
Lemma lem5407801 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407802 : term265 = term266.
Proof. exact (@lem5407801 term79 term79). Qed.
Lemma lem5407803 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407804 : term268 = term79.
Proof. exact (EQ_MP (@lem5407803) (@lem940073)). Qed.
Lemma lem5407805 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407806 : term266 = term193.
Proof. exact (MK_COMB (@lem5407805) (@lem5407804)). Qed.
Lemma lem5407807 : term265 = term193.
Proof. exact (TRANS (@lem5407802) (@lem5407806)). Qed.
Lemma lem5407809 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407810 : term265 = term266.
Proof. exact (@lem5407809 term79 term79). Qed.
Lemma lem5407811 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407812 : term268 = term79.
Proof. exact (EQ_MP (@lem5407811) (@lem940073)). Qed.
Lemma lem5407813 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407814 : term266 = term193.
Proof. exact (MK_COMB (@lem5407813) (@lem5407812)). Qed.
Lemma lem5407815 : term265 = term193.
Proof. exact (TRANS (@lem5407810) (@lem5407814)). Qed.
Lemma lem5407816 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5407817 : term320 = term307.
Proof. exact (MK_COMB (@lem5407816) (@lem5407815)). Qed.
Lemma lem5407818 : term321 = term309.
Proof. exact (MK_COMB (@lem5407817) (@lem5407807)). Qed.
Lemma lem5407819 : term309 = term322.
Proof. exact (@lem1367770 term79 term79). Qed.
Lemma lem5407820 : term323 = term324.
Proof. exact (@lem706885). Qed.
Lemma lem5407821 : (term323 = term324) = (term325 = term326).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term324). Qed.
Lemma lem5407822 : term325 = term326.
Proof. exact (EQ_MP (@lem5407821) (@lem5407820)). Qed.
Lemma lem5407823 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407824 : term322 = term312.
Proof. exact (MK_COMB (@lem5407823) (@lem5407822)). Qed.
Lemma lem5407825 : term309 = term312.
Proof. exact (TRANS (@lem5407819) (@lem5407824)). Qed.
Lemma lem5407826 : term321 = term312.
Proof. exact (TRANS (@lem5407818) (@lem5407825)). Qed.
Lemma lem5407827 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5407828 : term327 = term328.
Proof. exact (MK_COMB (@lem5407827) (@lem5407826)). Qed.
Lemma lem5407829 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5407830 : term329 = term330.
Proof. exact (MK_COMB (@lem5407828) (@lem5407829)). Qed.
Lemma lem5407832 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407833 : term330 = term331.
Proof. exact (@lem5407832 term326 term79). Qed.
Lemma lem5407834 : term332 = term324.
Proof. exact (@lem996237 term324). Qed.
Lemma lem5407835 : (term332 = term324) = (term333 = term326).
Proof. exact (@lem1007663 term324 (BIT1 0) term324). Qed.
Lemma lem5407836 : term333 = term326.
Proof. exact (EQ_MP (@lem5407835) (@lem5407834)). Qed.
Lemma lem5407837 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407838 : term331 = term312.
Proof. exact (MK_COMB (@lem5407837) (@lem5407836)). Qed.
Lemma lem5407839 : term330 = term312.
Proof. exact (TRANS (@lem5407833) (@lem5407838)). Qed.
Lemma lem5407840 : term329 = term312.
Proof. exact (TRANS (@lem5407830) (@lem5407839)). Qed.
Lemma lem5407842 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407843 : term265 = term266.
Proof. exact (@lem5407842 term79 term79). Qed.
Lemma lem5407844 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407845 : term268 = term79.
Proof. exact (EQ_MP (@lem5407844) (@lem940073)). Qed.
Lemma lem5407846 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407847 : term266 = term193.
Proof. exact (MK_COMB (@lem5407846) (@lem5407845)). Qed.
Lemma lem5407848 : term265 = term193.
Proof. exact (TRANS (@lem5407843) (@lem5407847)). Qed.
Lemma lem5407849 : term328 = term328.
Proof. exact (eq_refl term328). Qed.
Lemma lem5407850 : term334 = term330.
Proof. exact (MK_COMB (@lem5407849) (@lem5407848)). Qed.
Lemma lem5407852 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407853 : term330 = term331.
Proof. exact (@lem5407852 term326 term79). Qed.
Lemma lem5407854 : term332 = term324.
Proof. exact (@lem996237 term324). Qed.
Lemma lem5407855 : (term332 = term324) = (term333 = term326).
Proof. exact (@lem1007663 term324 (BIT1 0) term324). Qed.
Lemma lem5407856 : term333 = term326.
Proof. exact (EQ_MP (@lem5407855) (@lem5407854)). Qed.
Lemma lem5407857 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407858 : term331 = term312.
Proof. exact (MK_COMB (@lem5407857) (@lem5407856)). Qed.
Lemma lem5407859 : term330 = term312.
Proof. exact (TRANS (@lem5407853) (@lem5407858)). Qed.
Lemma lem5407860 : term334 = term312.
Proof. exact (TRANS (@lem5407850) (@lem5407859)). Qed.
Lemma lem5407861 : term312 = term334.
Proof. exact (SYM (@lem5407860)). Qed.
Lemma lem5407862 : term329 = term334.
Proof. exact (TRANS (@lem5407840) (@lem5407861)). Qed.
Lemma lem5407863 : term310 = term335.
Proof. exact (@lem5407799 (@lem5407862)). Qed.
Lemma lem5407864 : term309 = term335.
Proof. exact (TRANS (@lem5407765) (@lem5407863)). Qed.
Lemma lem5407866 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5407867 : term335 = term312.
Proof. exact (@lem5407866 term312). Qed.
Lemma lem5407868 : term309 = term312.
Proof. exact (TRANS (@lem5407864) (@lem5407867)). Qed.
Lemma lem5407869 (_69904 : int) : (term194 _69904) = (term194 _69904).
Proof. exact (eq_refl (term194 _69904)). Qed.
Lemma lem5407870 (_69904 : int) : (term306 _69904) = (term336 _69904).
Proof. exact (MK_COMB (@lem5407869 _69904) (@lem5407868)). Qed.
Lemma lem5407872 (_69904 : int) : (term210 _69904) = (term336 _69904).
Proof. exact (TRANS (@lem5407756 _69904) (@lem5407870 _69904)). Qed.
Lemma lem5407875 (_69905 : int) : (term337 _69905) = (term337 _69905).
Proof. exact (eq_refl (term337 _69905)). Qed.
Lemma lem5407876 (_69905 : int) (_69904 : int) : (term338 _69905 _69904) = (term339 _69905 _69904).
Proof. exact (MK_COMB (@lem5407875 _69905) (@lem5407872 _69904)). Qed.
Lemma lem5407877 (_69905 : int) (_69904 : int) : (term339 _69905 _69904) = (term340 _69905 _69904).
Proof. exact (@lem1982792 (real_of_int _69905) (term336 _69904)). Qed.
Lemma lem5407878 (_69904 : int) : (term341 _69904) = (term342 _69904).
Proof. exact (@lem1982781 (real_of_int _69904) term256 term312). Qed.
Lemma lem5407880 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5407881 : term312 = term335.
Proof. exact (@lem5407880 term326). Qed.
Lemma lem5407883 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5407884 : term256 = term257.
Proof. exact (@lem5407883 term79). Qed.
Lemma lem5407885 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5407886 : term258 = term259.
Proof. exact (MK_COMB (@lem5407885) (@lem5407884)). Qed.
Lemma lem5407887 : term343 = term344.
Proof. exact (MK_COMB (@lem5407886) (@lem5407881)). Qed.
Lemma lem5407888 : term344 = term345.
Proof. exact (@lem1981613 term256 term312 term193 term193). Qed.
Lemma lem5407890 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407891 : term265 = term266.
Proof. exact (@lem5407890 term79 term79). Qed.
Lemma lem5407892 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407893 : term268 = term79.
Proof. exact (EQ_MP (@lem5407892) (@lem940073)). Qed.
Lemma lem5407894 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407895 : term266 = term193.
Proof. exact (MK_COMB (@lem5407894) (@lem5407893)). Qed.
Lemma lem5407896 : term265 = term193.
Proof. exact (TRANS (@lem5407891) (@lem5407895)). Qed.
Lemma lem5407898 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5407899 : term343 = term346.
Proof. exact (@lem5407898 term79 term326). Qed.
Lemma lem5407900 : term347 = term324.
Proof. exact (@lem996238 term324). Qed.
Lemma lem5407901 : (term347 = term324) = (term348 = term326).
Proof. exact (@lem1007663 (BIT1 0) term324 term324). Qed.
Lemma lem5407902 : term348 = term326.
Proof. exact (EQ_MP (@lem5407901) (@lem5407900)). Qed.
Lemma lem5407903 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407904 : term349 = term312.
Proof. exact (MK_COMB (@lem5407903) (@lem5407902)). Qed.
Lemma lem5407905 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5407906 : term346 = term350.
Proof. exact (MK_COMB (@lem5407905) (@lem5407904)). Qed.
Lemma lem5407907 : term343 = term350.
Proof. exact (TRANS (@lem5407899) (@lem5407906)). Qed.
Lemma lem5407908 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5407909 : term351 = term352.
Proof. exact (MK_COMB (@lem5407908) (@lem5407907)). Qed.
Lemma lem5407910 : term345 = term353.
Proof. exact (MK_COMB (@lem5407909) (@lem5407896)). Qed.
Lemma lem5407911 : term344 = term353.
Proof. exact (TRANS (@lem5407888) (@lem5407910)). Qed.
Lemma lem5407912 : term343 = term353.
Proof. exact (TRANS (@lem5407887) (@lem5407911)). Qed.
Lemma lem5407914 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5407915 : term353 = term350.
Proof. exact (@lem5407914 term350). Qed.
Lemma lem5407916 : term343 = term350.
Proof. exact (TRANS (@lem5407912) (@lem5407915)). Qed.
Lemma lem5407919 (_69904 : int) : (term299 _69904) = (term299 _69904).
Proof. exact (eq_refl (term299 _69904)). Qed.
Lemma lem5407920 (_69904 : int) : (term342 _69904) = (term354 _69904).
Proof. exact (MK_COMB (@lem5407919 _69904) (@lem5407916)). Qed.
Lemma lem5407921 (_69904 : int) : (term341 _69904) = (term354 _69904).
Proof. exact (TRANS (@lem5407878 _69904) (@lem5407920 _69904)). Qed.
Lemma lem5407922 (_69905 : int) : (term194 _69905) = (term194 _69905).
Proof. exact (eq_refl (term194 _69905)). Qed.
Lemma lem5407923 (_69905 : int) (_69904 : int) : (term340 _69905 _69904) = (term355 _69905 _69904).
Proof. exact (MK_COMB (@lem5407922 _69905) (@lem5407921 _69904)). Qed.
Lemma lem5407928 (_69904 : int) (_69905 : int) : (term355 _69905 _69904) = (term356 _69904 _69905).
Proof. exact (@lem1982757 (term281 _69904) (real_of_int _69905) term350). Qed.
Lemma lem5407929 (_69904 : int) (_69905 : int) : (term340 _69905 _69904) = (term356 _69904 _69905).
Proof. exact (TRANS (@lem5407923 _69905 _69904) (@lem5407928 _69904 _69905)). Qed.
Lemma lem5407930 (_69904 : int) (_69905 : int) : (term339 _69905 _69904) = (term356 _69904 _69905).
Proof. exact (TRANS (@lem5407877 _69905 _69904) (@lem5407929 _69904 _69905)). Qed.
Lemma lem5407931 (_69904 : int) (_69905 : int) : (term338 _69905 _69904) = (term356 _69904 _69905).
Proof. exact (TRANS (@lem5407876 _69905 _69904) (@lem5407930 _69904 _69905)). Qed.
Lemma lem5407932 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5407933 (_69904 : int) (_69905 : int) : (term357 _69905 _69904) = (term358 _69904 _69905).
Proof. exact (MK_COMB (@lem5407932) (@lem5407931 _69904 _69905)). Qed.
Lemma lem5407934 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5407935 (_69904 : int) (_69905 : int) : (term305 _69905 _69904) = (term359 _69904 _69905).
Proof. exact (MK_COMB (@lem5407933 _69904 _69905) (@lem5407934)). Qed.
Lemma lem5407936 (_69904 : int) (_69905 : int) : (term213 _69904 _69905) = (term359 _69904 _69905).
Proof. exact (TRANS (@lem5407744 _69905 _69904) (@lem5407935 _69904 _69905)). Qed.
Lemma lem5407937 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5407938 (_69904 : int) (_69905 : int) : (term232 _69905 _69904) = (term410 _69904 _69905).
Proof. exact (MK_COMB (@lem5407937) (@lem5407743 _69904 _69905)). Qed.
Lemma lem5407939 (_69904 : int) (_69905 : int) : (term233 _69904 _69905) = (term411 _69904 _69905).
Proof. exact (MK_COMB (@lem5407938 _69904 _69905) (@lem5407936 _69904 _69905)). Qed.
Lemma lem5407940 (_69903 : int) (_69905 : int) : (term202 _69905 _69903) = (term285 _69903 _69905).
Proof. exact (@lem1988287 (real_of_int _69903) (term195 _69905)). Qed.
Lemma lem5407952 (_69903 : int) (_69905 : int) : (term286 _69903 _69905) = (term287 _69903 _69905).
Proof. exact (@lem1982792 (real_of_int _69903) (term195 _69905)). Qed.
Lemma lem5407953 (_69905 : int) : (term288 _69905) = (term289 _69905).
Proof. exact (@lem1982781 (real_of_int _69905) term256 term193). Qed.
Lemma lem5407955 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5407956 : term193 = term290.
Proof. exact (@lem5407955 term79). Qed.
Lemma lem5407958 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5407959 : term256 = term257.
Proof. exact (@lem5407958 term79). Qed.
Lemma lem5407960 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5407961 : term258 = term259.
Proof. exact (MK_COMB (@lem5407960) (@lem5407959)). Qed.
Lemma lem5407962 : term291 = term292.
Proof. exact (MK_COMB (@lem5407961) (@lem5407956)). Qed.
Lemma lem5407963 : term292 = term293.
Proof. exact (@lem1981613 term256 term193 term193 term193). Qed.
Lemma lem5407965 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5407966 : term265 = term266.
Proof. exact (@lem5407965 term79 term79). Qed.
Lemma lem5407967 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407968 : term268 = term79.
Proof. exact (EQ_MP (@lem5407967) (@lem940073)). Qed.
Lemma lem5407969 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407970 : term266 = term193.
Proof. exact (MK_COMB (@lem5407969) (@lem5407968)). Qed.
Lemma lem5407971 : term265 = term193.
Proof. exact (TRANS (@lem5407966) (@lem5407970)). Qed.
Lemma lem5407973 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5407974 : term291 = term296.
Proof. exact (@lem5407973 term79 term79). Qed.
Lemma lem5407975 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5407976 : term268 = term79.
Proof. exact (EQ_MP (@lem5407975) (@lem940073)). Qed.
Lemma lem5407977 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5407978 : term266 = term193.
Proof. exact (MK_COMB (@lem5407977) (@lem5407976)). Qed.
Lemma lem5407979 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5407980 : term296 = term256.
Proof. exact (MK_COMB (@lem5407979) (@lem5407978)). Qed.
Lemma lem5407981 : term291 = term256.
Proof. exact (TRANS (@lem5407974) (@lem5407980)). Qed.
Lemma lem5407982 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5407983 : term297 = term298.
Proof. exact (MK_COMB (@lem5407982) (@lem5407981)). Qed.
Lemma lem5407984 : term293 = term257.
Proof. exact (MK_COMB (@lem5407983) (@lem5407971)). Qed.
Lemma lem5407985 : term292 = term257.
Proof. exact (TRANS (@lem5407963) (@lem5407984)). Qed.
Lemma lem5407986 : term291 = term257.
Proof. exact (TRANS (@lem5407962) (@lem5407985)). Qed.
Lemma lem5407988 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5407989 : term257 = term256.
Proof. exact (@lem5407988 term256). Qed.
Lemma lem5407990 : term291 = term256.
Proof. exact (TRANS (@lem5407986) (@lem5407989)). Qed.
Lemma lem5407993 (_69905 : int) : (term299 _69905) = (term299 _69905).
Proof. exact (eq_refl (term299 _69905)). Qed.
Lemma lem5407994 (_69905 : int) : (term289 _69905) = (term300 _69905).
Proof. exact (MK_COMB (@lem5407993 _69905) (@lem5407990)). Qed.
Lemma lem5407995 (_69905 : int) : (term288 _69905) = (term300 _69905).
Proof. exact (TRANS (@lem5407953 _69905) (@lem5407994 _69905)). Qed.
Lemma lem5407996 (_69903 : int) : (term194 _69903) = (term194 _69903).
Proof. exact (eq_refl (term194 _69903)). Qed.
Lemma lem5407999 (_69903 : int) (_69905 : int) : (term287 _69903 _69905) = (term301 _69903 _69905).
Proof. exact (MK_COMB (@lem5407996 _69903) (@lem5407995 _69905)). Qed.
Lemma lem5408001 (_69903 : int) (_69905 : int) : (term286 _69903 _69905) = (term301 _69903 _69905).
Proof. exact (TRANS (@lem5407952 _69903 _69905) (@lem5407999 _69903 _69905)). Qed.
Lemma lem5408002 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5408003 (_69903 : int) (_69905 : int) : (term302 _69903 _69905) = (term303 _69903 _69905).
Proof. exact (MK_COMB (@lem5408002) (@lem5408001 _69903 _69905)). Qed.
Lemma lem5408004 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5408005 (_69903 : int) (_69905 : int) : (term285 _69903 _69905) = (term304 _69903 _69905).
Proof. exact (MK_COMB (@lem5408003 _69903 _69905) (@lem5408004)). Qed.
Lemma lem5408006 (_69903 : int) (_69905 : int) : (term202 _69905 _69903) = (term304 _69903 _69905).
Proof. exact (TRANS (@lem5407940 _69903 _69905) (@lem5408005 _69903 _69905)). Qed.
Lemma lem5408007 (_69905 : int) (_69904 : int) : (term202 _69904 _69905) = (term285 _69905 _69904).
Proof. exact (@lem1988287 (real_of_int _69905) (term195 _69904)). Qed.
Lemma lem5408019 (_69905 : int) (_69904 : int) : (term286 _69905 _69904) = (term287 _69905 _69904).
Proof. exact (@lem1982792 (real_of_int _69905) (term195 _69904)). Qed.
Lemma lem5408020 (_69904 : int) : (term288 _69904) = (term289 _69904).
Proof. exact (@lem1982781 (real_of_int _69904) term256 term193). Qed.
Lemma lem5408022 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5408023 : term193 = term290.
Proof. exact (@lem5408022 term79). Qed.
Lemma lem5408025 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5408026 : term256 = term257.
Proof. exact (@lem5408025 term79). Qed.
Lemma lem5408027 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5408028 : term258 = term259.
Proof. exact (MK_COMB (@lem5408027) (@lem5408026)). Qed.
Lemma lem5408029 : term291 = term292.
Proof. exact (MK_COMB (@lem5408028) (@lem5408023)). Qed.
Lemma lem5408030 : term292 = term293.
Proof. exact (@lem1981613 term256 term193 term193 term193). Qed.
Lemma lem5408032 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5408033 : term265 = term266.
Proof. exact (@lem5408032 term79 term79). Qed.
Lemma lem5408034 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5408035 : term268 = term79.
Proof. exact (EQ_MP (@lem5408034) (@lem940073)). Qed.
Lemma lem5408036 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5408037 : term266 = term193.
Proof. exact (MK_COMB (@lem5408036) (@lem5408035)). Qed.
Lemma lem5408038 : term265 = term193.
Proof. exact (TRANS (@lem5408033) (@lem5408037)). Qed.
Lemma lem5408040 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5408041 : term291 = term296.
Proof. exact (@lem5408040 term79 term79). Qed.
Lemma lem5408042 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5408043 : term268 = term79.
Proof. exact (EQ_MP (@lem5408042) (@lem940073)). Qed.
Lemma lem5408044 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5408045 : term266 = term193.
Proof. exact (MK_COMB (@lem5408044) (@lem5408043)). Qed.
Lemma lem5408046 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5408047 : term296 = term256.
Proof. exact (MK_COMB (@lem5408046) (@lem5408045)). Qed.
Lemma lem5408048 : term291 = term256.
Proof. exact (TRANS (@lem5408041) (@lem5408047)). Qed.
Lemma lem5408049 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5408050 : term297 = term298.
Proof. exact (MK_COMB (@lem5408049) (@lem5408048)). Qed.
Lemma lem5408051 : term293 = term257.
Proof. exact (MK_COMB (@lem5408050) (@lem5408038)). Qed.
Lemma lem5408052 : term292 = term257.
Proof. exact (TRANS (@lem5408030) (@lem5408051)). Qed.
Lemma lem5408053 : term291 = term257.
Proof. exact (TRANS (@lem5408029) (@lem5408052)). Qed.
Lemma lem5408055 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5408056 : term257 = term256.
Proof. exact (@lem5408055 term256). Qed.
Lemma lem5408057 : term291 = term256.
Proof. exact (TRANS (@lem5408053) (@lem5408056)). Qed.
Lemma lem5408060 (_69904 : int) : (term299 _69904) = (term299 _69904).
Proof. exact (eq_refl (term299 _69904)). Qed.
Lemma lem5408061 (_69904 : int) : (term289 _69904) = (term300 _69904).
Proof. exact (MK_COMB (@lem5408060 _69904) (@lem5408057)). Qed.
Lemma lem5408062 (_69904 : int) : (term288 _69904) = (term300 _69904).
Proof. exact (TRANS (@lem5408020 _69904) (@lem5408061 _69904)). Qed.
Lemma lem5408063 (_69905 : int) : (term194 _69905) = (term194 _69905).
Proof. exact (eq_refl (term194 _69905)). Qed.
Lemma lem5408064 (_69905 : int) (_69904 : int) : (term287 _69905 _69904) = (term301 _69905 _69904).
Proof. exact (MK_COMB (@lem5408063 _69905) (@lem5408062 _69904)). Qed.
Lemma lem5408069 (_69904 : int) (_69905 : int) : (term301 _69905 _69904) = (term362 _69904 _69905).
Proof. exact (@lem1982757 (term281 _69904) (real_of_int _69905) term256). Qed.
Lemma lem5408070 (_69904 : int) (_69905 : int) : (term287 _69905 _69904) = (term362 _69904 _69905).
Proof. exact (TRANS (@lem5408064 _69905 _69904) (@lem5408069 _69904 _69905)). Qed.
Lemma lem5408072 (_69904 : int) (_69905 : int) : (term286 _69905 _69904) = (term362 _69904 _69905).
Proof. exact (TRANS (@lem5408019 _69905 _69904) (@lem5408070 _69904 _69905)). Qed.
Lemma lem5408073 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5408074 (_69904 : int) (_69905 : int) : (term302 _69905 _69904) = (term412 _69904 _69905).
Proof. exact (MK_COMB (@lem5408073) (@lem5408072 _69904 _69905)). Qed.
Lemma lem5408075 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5408076 (_69904 : int) (_69905 : int) : (term285 _69905 _69904) = (term413 _69904 _69905).
Proof. exact (MK_COMB (@lem5408074 _69904 _69905) (@lem5408075)). Qed.
Lemma lem5408077 (_69904 : int) (_69905 : int) : (term202 _69904 _69905) = (term413 _69904 _69905).
Proof. exact (TRANS (@lem5408007 _69905 _69904) (@lem5408076 _69904 _69905)). Qed.
Lemma lem5408078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408079 (_69903 : int) (_69905 : int) : (term215 _69905 _69903) = (term360 _69903 _69905).
Proof. exact (MK_COMB (@lem5408078) (@lem5408006 _69903 _69905)). Qed.
Lemma lem5408080 (_69903 : int) (_69904 : int) (_69905 : int) : (term234 _69903 _69904 _69905) = (term414 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408079 _69903 _69905) (@lem5408077 _69904 _69905)). Qed.
Lemma lem5408081 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5408082 (_69904 : int) (_69905 : int) : (term235 _69904 _69905) = (term415 _69904 _69905).
Proof. exact (MK_COMB (@lem5408081) (@lem5407939 _69904 _69905)). Qed.
Lemma lem5408083 (_69903 : int) (_69904 : int) (_69905 : int) : (term236 _69903 _69904 _69905) = (term416 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408082 _69904 _69905) (@lem5408080 _69903 _69904 _69905)). Qed.
Lemma lem5408084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5408085 (_69903 : int) (_69904 : int) (_69905 : int) : (term237 _69903 _69905 _69904) = (term417 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408084) (@lem5407563 _69903 _69904 _69905)). Qed.
Lemma lem5408086 (_69903 : int) (_69904 : int) (_69905 : int) : (term238 _69903 _69904 _69905) = (term418 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408085 _69903 _69904 _69905) (@lem5408083 _69903 _69904 _69905)). Qed.
Lemma lem5408087 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408088 (_69903 : int) (_69904 : int) (_69905 : int) : (term239 _69903 _69905 _69904) = (term419 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408087) (@lem5407512 _69903 _69904 _69905)). Qed.
Lemma lem5408089 (_69903 : int) (_69904 : int) (_69905 : int) : (term240 _69903 _69904 _69905) = (term420 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408088 _69903 _69904 _69905) (@lem5408086 _69903 _69904 _69905)). Qed.
Lemma lem5408090 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5408091 (_69903 : int) (_69904 : int) : (term241 _69903 _69904) = (term421 _69903 _69904).
Proof. exact (MK_COMB (@lem5408090) (@lem5407131 _69903 _69904)). Qed.
Lemma lem5408092 (_69903 : int) (_69904 : int) (_69905 : int) : (term242 _69903 _69904 _69905) = (term422 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408091 _69903 _69904) (@lem5408089 _69903 _69904 _69905)). Qed.
Lemma lem5408093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5408094 (_69905 : int) : (term243 _69905) = (term423 _69905).
Proof. exact (MK_COMB (@lem5408093) (@lem5407106 _69905)). Qed.
Lemma lem5408095 (_69903 : int) (_69904 : int) (_69905 : int) : (term244 _69903 _69904 _69905) = (term424 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408094 _69905) (@lem5408092 _69903 _69904 _69905)). Qed.
Lemma lem5408096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5408097 (_69904 : int) : (term243 _69904) = (term423 _69904).
Proof. exact (MK_COMB (@lem5408096) (@lem5407058 _69904)). Qed.
Lemma lem5408098 (_69903 : int) (_69904 : int) (_69905 : int) : (term245 _69903 _69904 _69905) = (term425 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408097 _69904) (@lem5408095 _69903 _69904 _69905)). Qed.
Lemma lem5408099 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5408100 (_69903 : int) : (term243 _69903) = (term423 _69903).
Proof. exact (MK_COMB (@lem5408099) (@lem5407010 _69903)). Qed.
Lemma lem5408101 (_69903 : int) (_69904 : int) (_69905 : int) : (term246 _69903 _69904 _69905) = (term426 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408100 _69903) (@lem5408098 _69903 _69904 _69905)). Qed.
Lemma lem5408108 (_69903 : int) (_69904 : int) (_69905 : int) : (term248 _69903 _69904 _69905) = (term426 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5406962 _69903 _69904 _69905) (@lem5408101 _69903 _69904 _69905)). Qed.
Lemma lem5408122 (_69903 : int) (_69904 : int) (_69905 : int) : (term416 _69903 _69904 _69905) = (term427 _69903 _69904 _69905).
Proof. exact (@lem19158 (term304 _69903 _69905) (term411 _69904 _69905) (term413 _69904 _69905)). Qed.
Lemma lem5408129 (_69904 : int) (_69905 : int) : (term428 _69904 _69905) = (term429 _69904 _69905).
Proof. exact (@lem19367 (term373 _69904 _69905) (term359 _69904 _69905) (term413 _69904 _69905)). Qed.
Lemma lem5408136 (_69904 : int) (_69903 : int) (_69905 : int) : (term430 _69904 _69903 _69905) = (term431 _69904 _69903 _69905).
Proof. exact (@lem19367 (term373 _69904 _69905) (term359 _69904 _69905) (term304 _69903 _69905)). Qed.
Lemma lem5408137 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408138 (_69904 : int) (_69903 : int) (_69905 : int) : (term432 _69904 _69903 _69905) = (term433 _69904 _69903 _69905).
Proof. exact (MK_COMB (@lem5408137) (@lem5408136 _69904 _69903 _69905)). Qed.
Lemma lem5408139 (_69903 : int) (_69904 : int) (_69905 : int) : (term427 _69903 _69904 _69905) = (term434 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408138 _69904 _69903 _69905) (@lem5408129 _69904 _69905)). Qed.
Lemma lem5408141 (_69903 : int) (_69904 : int) (_69905 : int) : (term416 _69903 _69904 _69905) = (term434 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408122 _69903 _69904 _69905) (@lem5408139 _69903 _69904 _69905)). Qed.
Lemma lem5408150 (_69903 : int) (_69904 : int) (_69905 : int) : (term417 _69903 _69904 _69905) = (term417 _69903 _69904 _69905).
Proof. exact (eq_refl (term417 _69903 _69904 _69905)). Qed.
Lemma lem5408151 (_69903 : int) (_69904 : int) (_69905 : int) : (term418 _69903 _69904 _69905) = (term435 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408150 _69903 _69904 _69905) (@lem5408141 _69903 _69904 _69905)). Qed.
Lemma lem5408152 (_69903 : int) (_69904 : int) (_69905 : int) : (term435 _69903 _69904 _69905) = (term436 _69903 _69904 _69905).
Proof. exact (@lem19158 (term431 _69904 _69903 _69905) (term386 _69903 _69904 _69905) (term429 _69904 _69905)). Qed.
Lemma lem5408159 (_69903 : int) (_69904 : int) (_69905 : int) : (term437 _69903 _69904 _69905) = (term438 _69903 _69904 _69905).
Proof. exact (@lem19158 (term439 _69904 _69905) (term386 _69903 _69904 _69905) (term440 _69904 _69905)). Qed.
Lemma lem5408166 (_69904 : int) (_69903 : int) (_69905 : int) : (term441 _69904 _69903 _69905) = (term442 _69904 _69903 _69905).
Proof. exact (@lem19158 (term443 _69904 _69903 _69905) (term386 _69903 _69904 _69905) (term444 _69904 _69903 _69905)). Qed.
Lemma lem5408167 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408168 (_69904 : int) (_69903 : int) (_69905 : int) : (term445 _69904 _69903 _69905) = (term446 _69904 _69903 _69905).
Proof. exact (MK_COMB (@lem5408167) (@lem5408166 _69904 _69903 _69905)). Qed.
Lemma lem5408169 (_69903 : int) (_69904 : int) (_69905 : int) : (term436 _69903 _69904 _69905) = (term447 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408168 _69904 _69903 _69905) (@lem5408159 _69903 _69904 _69905)). Qed.
Lemma lem5408170 (_69903 : int) (_69904 : int) (_69905 : int) : (term435 _69903 _69904 _69905) = (term447 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408152 _69903 _69904 _69905) (@lem5408169 _69903 _69904 _69905)). Qed.
Lemma lem5408171 (_69903 : int) (_69904 : int) (_69905 : int) : (term418 _69903 _69904 _69905) = (term447 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408151 _69903 _69904 _69905) (@lem5408170 _69903 _69904 _69905)). Qed.
Lemma lem5408191 (_69903 : int) (_69904 : int) (_69905 : int) : (term379 _69903 _69904 _69905) = (term448 _69903 _69904 _69905).
Proof. exact (@lem19158 ((term362 _69904 _69905) = term182) (term361 _69903 _69904 _69905) (term375 _69903 _69904 _69905)). Qed.
Lemma lem5408198 (_69903 : int) (_69904 : int) (_69905 : int) : (term449 _69903 _69904 _69905) = (term450 _69903 _69904 _69905).
Proof. exact (@lem19367 (term304 _69903 _69905) (term359 _69904 _69905) (term375 _69903 _69904 _69905)). Qed.
Lemma lem5408205 (_69903 : int) (_69904 : int) (_69905 : int) : (term451 _69903 _69904 _69905) = (term452 _69903 _69904 _69905).
Proof. exact (@lem19367 (term304 _69903 _69905) (term359 _69904 _69905) ((term362 _69904 _69905) = term182)). Qed.
Lemma lem5408206 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408207 (_69903 : int) (_69904 : int) (_69905 : int) : (term453 _69903 _69904 _69905) = (term454 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408206) (@lem5408205 _69903 _69904 _69905)). Qed.
Lemma lem5408208 (_69903 : int) (_69904 : int) (_69905 : int) : (term448 _69903 _69904 _69905) = (term455 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408207 _69903 _69904 _69905) (@lem5408198 _69903 _69904 _69905)). Qed.
Lemma lem5408210 (_69903 : int) (_69904 : int) (_69905 : int) : (term379 _69903 _69904 _69905) = (term455 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408191 _69903 _69904 _69905) (@lem5408208 _69903 _69904 _69905)). Qed.
Lemma lem5408211 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408212 (_69903 : int) (_69904 : int) (_69905 : int) : (term419 _69903 _69904 _69905) = (term456 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408211) (@lem5408210 _69903 _69904 _69905)). Qed.
Lemma lem5408213 (_69903 : int) (_69904 : int) (_69905 : int) : (term420 _69903 _69904 _69905) = (term457 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408212 _69903 _69904 _69905) (@lem5408171 _69903 _69904 _69905)). Qed.
Lemma lem5408216 (_69903 : int) (_69904 : int) : (term421 _69903 _69904) = (term421 _69903 _69904).
Proof. exact (eq_refl (term421 _69903 _69904)). Qed.
Lemma lem5408217 (_69903 : int) (_69904 : int) (_69905 : int) : (term422 _69903 _69904 _69905) = (term458 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408216 _69903 _69904) (@lem5408213 _69903 _69904 _69905)). Qed.
Lemma lem5408218 (_69903 : int) (_69904 : int) (_69905 : int) : (term458 _69903 _69904 _69905) = (term459 _69903 _69904 _69905).
Proof. exact (@lem19158 (term455 _69903 _69904 _69905) (term284 _69903 _69904) (term447 _69903 _69904 _69905)). Qed.
Lemma lem5408219 (_69903 : int) (_69904 : int) (_69905 : int) : (term460 _69903 _69904 _69905) = (term461 _69903 _69904 _69905).
Proof. exact (@lem19158 (term442 _69904 _69903 _69905) (term284 _69903 _69904) (term438 _69903 _69904 _69905)). Qed.
Lemma lem5408226 (_69903 : int) (_69904 : int) (_69905 : int) : (term462 _69903 _69904 _69905) = (term463 _69903 _69904 _69905).
Proof. exact (@lem19158 (term464 _69903 _69904 _69905) (term284 _69903 _69904) (term465 _69903 _69904 _69905)). Qed.
Lemma lem5408233 (_69904 : int) (_69903 : int) (_69905 : int) : (term466 _69904 _69903 _69905) = (term467 _69904 _69903 _69905).
Proof. exact (@lem19158 (term468 _69904 _69903 _69905) (term284 _69903 _69904) (term469 _69904 _69903 _69905)). Qed.
Lemma lem5408234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408235 (_69904 : int) (_69903 : int) (_69905 : int) : (term470 _69904 _69903 _69905) = (term471 _69904 _69903 _69905).
Proof. exact (MK_COMB (@lem5408234) (@lem5408233 _69904 _69903 _69905)). Qed.
Lemma lem5408236 (_69903 : int) (_69904 : int) (_69905 : int) : (term461 _69903 _69904 _69905) = (term472 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408235 _69904 _69903 _69905) (@lem5408226 _69903 _69904 _69905)). Qed.
Lemma lem5408237 (_69903 : int) (_69904 : int) (_69905 : int) : (term460 _69903 _69904 _69905) = (term472 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408219 _69903 _69904 _69905) (@lem5408236 _69903 _69904 _69905)). Qed.
Lemma lem5408238 (_69903 : int) (_69904 : int) (_69905 : int) : (term473 _69903 _69904 _69905) = (term474 _69903 _69904 _69905).
Proof. exact (@lem19158 (term452 _69903 _69904 _69905) (term284 _69903 _69904) (term450 _69903 _69904 _69905)). Qed.
Lemma lem5408245 (_69903 : int) (_69904 : int) (_69905 : int) : (term475 _69903 _69904 _69905) = (term476 _69903 _69904 _69905).
Proof. exact (@lem19158 (term477 _69903 _69904 _69905) (term284 _69903 _69904) (term478 _69903 _69904 _69905)). Qed.
Lemma lem5408252 (_69903 : int) (_69904 : int) (_69905 : int) : (term479 _69903 _69904 _69905) = (term480 _69903 _69904 _69905).
Proof. exact (@lem19158 (term481 _69903 _69904 _69905) (term284 _69903 _69904) (term482 _69904 _69905)). Qed.
Lemma lem5408253 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408254 (_69903 : int) (_69904 : int) (_69905 : int) : (term483 _69903 _69904 _69905) = (term484 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408253) (@lem5408252 _69903 _69904 _69905)). Qed.
Lemma lem5408255 (_69903 : int) (_69904 : int) (_69905 : int) : (term474 _69903 _69904 _69905) = (term485 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408254 _69903 _69904 _69905) (@lem5408245 _69903 _69904 _69905)). Qed.
Lemma lem5408256 (_69903 : int) (_69904 : int) (_69905 : int) : (term473 _69903 _69904 _69905) = (term485 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408238 _69903 _69904 _69905) (@lem5408255 _69903 _69904 _69905)). Qed.
Lemma lem5408257 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408258 (_69903 : int) (_69904 : int) (_69905 : int) : (term486 _69903 _69904 _69905) = (term487 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408257) (@lem5408256 _69903 _69904 _69905)). Qed.
Lemma lem5408259 (_69903 : int) (_69904 : int) (_69905 : int) : (term459 _69903 _69904 _69905) = (term488 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408258 _69903 _69904 _69905) (@lem5408237 _69903 _69904 _69905)). Qed.
Lemma lem5408260 (_69903 : int) (_69904 : int) (_69905 : int) : (term458 _69903 _69904 _69905) = (term488 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408218 _69903 _69904 _69905) (@lem5408259 _69903 _69904 _69905)). Qed.
Lemma lem5408261 (_69903 : int) (_69904 : int) (_69905 : int) : (term422 _69903 _69904 _69905) = (term488 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408217 _69903 _69904 _69905) (@lem5408260 _69903 _69904 _69905)). Qed.
Lemma lem5408264 (_69905 : int) : (term423 _69905) = (term423 _69905).
Proof. exact (eq_refl (term423 _69905)). Qed.
Lemma lem5408265 (_69903 : int) (_69904 : int) (_69905 : int) : (term424 _69903 _69904 _69905) = (term489 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408264 _69905) (@lem5408261 _69903 _69904 _69905)). Qed.
Lemma lem5408266 (_69903 : int) (_69904 : int) (_69905 : int) : (term489 _69903 _69904 _69905) = (term490 _69903 _69904 _69905).
Proof. exact (@lem19158 (term485 _69903 _69904 _69905) (term276 _69905) (term472 _69903 _69904 _69905)). Qed.
Lemma lem5408267 (_69903 : int) (_69904 : int) (_69905 : int) : (term491 _69903 _69904 _69905) = (term492 _69903 _69904 _69905).
Proof. exact (@lem19158 (term467 _69904 _69903 _69905) (term276 _69905) (term463 _69903 _69904 _69905)). Qed.
Lemma lem5408274 (_69903 : int) (_69904 : int) (_69905 : int) : (term493 _69903 _69904 _69905) = (term494 _69903 _69904 _69905).
Proof. exact (@lem19158 (term495 _69903 _69904 _69905) (term276 _69905) (term496 _69903 _69904 _69905)). Qed.
Lemma lem5408281 (_69904 : int) (_69903 : int) (_69905 : int) : (term497 _69904 _69903 _69905) = (term498 _69904 _69903 _69905).
Proof. exact (@lem19158 (term499 _69904 _69903 _69905) (term276 _69905) (term500 _69904 _69903 _69905)). Qed.
Lemma lem5408282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408283 (_69904 : int) (_69903 : int) (_69905 : int) : (term501 _69904 _69903 _69905) = (term502 _69904 _69903 _69905).
Proof. exact (MK_COMB (@lem5408282) (@lem5408281 _69904 _69903 _69905)). Qed.
Lemma lem5408284 (_69903 : int) (_69904 : int) (_69905 : int) : (term492 _69903 _69904 _69905) = (term503 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408283 _69904 _69903 _69905) (@lem5408274 _69903 _69904 _69905)). Qed.
Lemma lem5408285 (_69903 : int) (_69904 : int) (_69905 : int) : (term491 _69903 _69904 _69905) = (term503 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408267 _69903 _69904 _69905) (@lem5408284 _69903 _69904 _69905)). Qed.
Lemma lem5408286 (_69903 : int) (_69904 : int) (_69905 : int) : (term504 _69903 _69904 _69905) = (term505 _69903 _69904 _69905).
Proof. exact (@lem19158 (term480 _69903 _69904 _69905) (term276 _69905) (term476 _69903 _69904 _69905)). Qed.
Lemma lem5408293 (_69903 : int) (_69904 : int) (_69905 : int) : (term506 _69903 _69904 _69905) = (term507 _69903 _69904 _69905).
Proof. exact (@lem19158 (term508 _69903 _69904 _69905) (term276 _69905) (term509 _69903 _69904 _69905)). Qed.
Lemma lem5408300 (_69903 : int) (_69904 : int) (_69905 : int) : (term510 _69903 _69904 _69905) = (term511 _69903 _69904 _69905).
Proof. exact (@lem19158 (term512 _69903 _69904 _69905) (term276 _69905) (term513 _69903 _69904 _69905)). Qed.
Lemma lem5408301 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408302 (_69903 : int) (_69904 : int) (_69905 : int) : (term514 _69903 _69904 _69905) = (term515 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408301) (@lem5408300 _69903 _69904 _69905)). Qed.
Lemma lem5408303 (_69903 : int) (_69904 : int) (_69905 : int) : (term505 _69903 _69904 _69905) = (term516 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408302 _69903 _69904 _69905) (@lem5408293 _69903 _69904 _69905)). Qed.
Lemma lem5408304 (_69903 : int) (_69904 : int) (_69905 : int) : (term504 _69903 _69904 _69905) = (term516 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408286 _69903 _69904 _69905) (@lem5408303 _69903 _69904 _69905)). Qed.
Lemma lem5408305 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408306 (_69903 : int) (_69904 : int) (_69905 : int) : (term517 _69903 _69904 _69905) = (term518 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408305) (@lem5408304 _69903 _69904 _69905)). Qed.
Lemma lem5408307 (_69903 : int) (_69904 : int) (_69905 : int) : (term490 _69903 _69904 _69905) = (term519 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408306 _69903 _69904 _69905) (@lem5408285 _69903 _69904 _69905)). Qed.
Lemma lem5408308 (_69903 : int) (_69904 : int) (_69905 : int) : (term489 _69903 _69904 _69905) = (term519 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408266 _69903 _69904 _69905) (@lem5408307 _69903 _69904 _69905)). Qed.
Lemma lem5408309 (_69903 : int) (_69904 : int) (_69905 : int) : (term424 _69903 _69904 _69905) = (term519 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408265 _69903 _69904 _69905) (@lem5408308 _69903 _69904 _69905)). Qed.
Lemma lem5408312 (_69904 : int) : (term423 _69904) = (term423 _69904).
Proof. exact (eq_refl (term423 _69904)). Qed.
Lemma lem5408313 (_69903 : int) (_69904 : int) (_69905 : int) : (term425 _69903 _69904 _69905) = (term520 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408312 _69904) (@lem5408309 _69903 _69904 _69905)). Qed.
Lemma lem5408314 (_69903 : int) (_69904 : int) (_69905 : int) : (term520 _69903 _69904 _69905) = (term521 _69903 _69904 _69905).
Proof. exact (@lem19158 (term516 _69903 _69904 _69905) (term276 _69904) (term503 _69903 _69904 _69905)). Qed.
Lemma lem5408315 (_69903 : int) (_69904 : int) (_69905 : int) : (term522 _69903 _69904 _69905) = (term523 _69903 _69904 _69905).
Proof. exact (@lem19158 (term498 _69904 _69903 _69905) (term276 _69904) (term494 _69903 _69904 _69905)). Qed.
Lemma lem5408322 (_69903 : int) (_69904 : int) (_69905 : int) : (term524 _69903 _69904 _69905) = (term525 _69903 _69904 _69905).
Proof. exact (@lem19158 (term526 _69903 _69904 _69905) (term276 _69904) (term527 _69903 _69904 _69905)). Qed.
Lemma lem5408329 (_69904 : int) (_69903 : int) (_69905 : int) : (term528 _69904 _69903 _69905) = (term529 _69904 _69903 _69905).
Proof. exact (@lem19158 (term530 _69904 _69903 _69905) (term276 _69904) (term531 _69904 _69903 _69905)). Qed.
Lemma lem5408330 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408331 (_69904 : int) (_69903 : int) (_69905 : int) : (term532 _69904 _69903 _69905) = (term533 _69904 _69903 _69905).
Proof. exact (MK_COMB (@lem5408330) (@lem5408329 _69904 _69903 _69905)). Qed.
Lemma lem5408332 (_69903 : int) (_69904 : int) (_69905 : int) : (term523 _69903 _69904 _69905) = (term534 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408331 _69904 _69903 _69905) (@lem5408322 _69903 _69904 _69905)). Qed.
Lemma lem5408333 (_69903 : int) (_69904 : int) (_69905 : int) : (term522 _69903 _69904 _69905) = (term534 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408315 _69903 _69904 _69905) (@lem5408332 _69903 _69904 _69905)). Qed.
Lemma lem5408334 (_69903 : int) (_69904 : int) (_69905 : int) : (term535 _69903 _69904 _69905) = (term536 _69903 _69904 _69905).
Proof. exact (@lem19158 (term511 _69903 _69904 _69905) (term276 _69904) (term507 _69903 _69904 _69905)). Qed.
Lemma lem5408341 (_69903 : int) (_69904 : int) (_69905 : int) : (term537 _69903 _69904 _69905) = (term538 _69903 _69904 _69905).
Proof. exact (@lem19158 (term539 _69903 _69904 _69905) (term276 _69904) (term540 _69903 _69904 _69905)). Qed.
Lemma lem5408348 (_69903 : int) (_69904 : int) (_69905 : int) : (term541 _69903 _69904 _69905) = (term542 _69903 _69904 _69905).
Proof. exact (@lem19158 (term543 _69903 _69904 _69905) (term276 _69904) (term544 _69903 _69904 _69905)). Qed.
Lemma lem5408349 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408350 (_69903 : int) (_69904 : int) (_69905 : int) : (term545 _69903 _69904 _69905) = (term546 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408349) (@lem5408348 _69903 _69904 _69905)). Qed.
Lemma lem5408351 (_69903 : int) (_69904 : int) (_69905 : int) : (term536 _69903 _69904 _69905) = (term547 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408350 _69903 _69904 _69905) (@lem5408341 _69903 _69904 _69905)). Qed.
Lemma lem5408352 (_69903 : int) (_69904 : int) (_69905 : int) : (term535 _69903 _69904 _69905) = (term547 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408334 _69903 _69904 _69905) (@lem5408351 _69903 _69904 _69905)). Qed.
Lemma lem5408353 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408354 (_69903 : int) (_69904 : int) (_69905 : int) : (term548 _69903 _69904 _69905) = (term549 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408353) (@lem5408352 _69903 _69904 _69905)). Qed.
Lemma lem5408355 (_69903 : int) (_69904 : int) (_69905 : int) : (term521 _69903 _69904 _69905) = (term550 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408354 _69903 _69904 _69905) (@lem5408333 _69903 _69904 _69905)). Qed.
Lemma lem5408356 (_69903 : int) (_69904 : int) (_69905 : int) : (term520 _69903 _69904 _69905) = (term550 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408314 _69903 _69904 _69905) (@lem5408355 _69903 _69904 _69905)). Qed.
Lemma lem5408357 (_69903 : int) (_69904 : int) (_69905 : int) : (term425 _69903 _69904 _69905) = (term550 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408313 _69903 _69904 _69905) (@lem5408356 _69903 _69904 _69905)). Qed.
Lemma lem5408360 (_69903 : int) : (term423 _69903) = (term423 _69903).
Proof. exact (eq_refl (term423 _69903)). Qed.
Lemma lem5408361 (_69903 : int) (_69904 : int) (_69905 : int) : (term426 _69903 _69904 _69905) = (term551 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408360 _69903) (@lem5408357 _69903 _69904 _69905)). Qed.
Lemma lem5408362 (_69903 : int) (_69904 : int) (_69905 : int) : (term551 _69903 _69904 _69905) = (term552 _69903 _69904 _69905).
Proof. exact (@lem19158 (term547 _69903 _69904 _69905) (term276 _69903) (term534 _69903 _69904 _69905)). Qed.
Lemma lem5408363 (_69903 : int) (_69904 : int) (_69905 : int) : (term553 _69903 _69904 _69905) = (term554 _69903 _69904 _69905).
Proof. exact (@lem19158 (term529 _69904 _69903 _69905) (term276 _69903) (term525 _69903 _69904 _69905)). Qed.
Lemma lem5408370 (_69903 : int) (_69904 : int) (_69905 : int) : (term555 _69903 _69904 _69905) = (term556 _69903 _69904 _69905).
Proof. exact (@lem19158 (term557 _69903 _69904 _69905) (term276 _69903) (term558 _69903 _69904 _69905)). Qed.
Lemma lem5408377 (_69904 : int) (_69903 : int) (_69905 : int) : (term559 _69904 _69903 _69905) = (term560 _69904 _69903 _69905).
Proof. exact (@lem19158 (term561 _69904 _69903 _69905) (term276 _69903) (term562 _69904 _69903 _69905)). Qed.
Lemma lem5408378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408379 (_69904 : int) (_69903 : int) (_69905 : int) : (term563 _69904 _69903 _69905) = (term564 _69904 _69903 _69905).
Proof. exact (MK_COMB (@lem5408378) (@lem5408377 _69904 _69903 _69905)). Qed.
Lemma lem5408380 (_69903 : int) (_69904 : int) (_69905 : int) : (term554 _69903 _69904 _69905) = (term565 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408379 _69904 _69903 _69905) (@lem5408370 _69903 _69904 _69905)). Qed.
Lemma lem5408381 (_69903 : int) (_69904 : int) (_69905 : int) : (term553 _69903 _69904 _69905) = (term565 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408363 _69903 _69904 _69905) (@lem5408380 _69903 _69904 _69905)). Qed.
Lemma lem5408382 (_69903 : int) (_69904 : int) (_69905 : int) : (term566 _69903 _69904 _69905) = (term567 _69903 _69904 _69905).
Proof. exact (@lem19158 (term542 _69903 _69904 _69905) (term276 _69903) (term538 _69903 _69904 _69905)). Qed.
Lemma lem5408389 (_69903 : int) (_69904 : int) (_69905 : int) : (term568 _69903 _69904 _69905) = (term569 _69903 _69904 _69905).
Proof. exact (@lem19158 (term570 _69903 _69904 _69905) (term276 _69903) (term571 _69903 _69904 _69905)). Qed.
Lemma lem5408396 (_69903 : int) (_69904 : int) (_69905 : int) : (term572 _69903 _69904 _69905) = (term573 _69903 _69904 _69905).
Proof. exact (@lem19158 (term574 _69903 _69904 _69905) (term276 _69903) (term575 _69903 _69904 _69905)). Qed.
Lemma lem5408397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408398 (_69903 : int) (_69904 : int) (_69905 : int) : (term576 _69903 _69904 _69905) = (term577 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408397) (@lem5408396 _69903 _69904 _69905)). Qed.
Lemma lem5408399 (_69903 : int) (_69904 : int) (_69905 : int) : (term567 _69903 _69904 _69905) = (term578 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408398 _69903 _69904 _69905) (@lem5408389 _69903 _69904 _69905)). Qed.
Lemma lem5408400 (_69903 : int) (_69904 : int) (_69905 : int) : (term566 _69903 _69904 _69905) = (term578 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408382 _69903 _69904 _69905) (@lem5408399 _69903 _69904 _69905)). Qed.
Lemma lem5408401 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5408402 (_69903 : int) (_69904 : int) (_69905 : int) : (term579 _69903 _69904 _69905) = (term580 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408401) (@lem5408400 _69903 _69904 _69905)). Qed.
Lemma lem5408403 (_69903 : int) (_69904 : int) (_69905 : int) : (term552 _69903 _69904 _69905) = (term581 _69903 _69904 _69905).
Proof. exact (MK_COMB (@lem5408402 _69903 _69904 _69905) (@lem5408381 _69903 _69904 _69905)). Qed.
Lemma lem5408404 (_69903 : int) (_69904 : int) (_69905 : int) : (term551 _69903 _69904 _69905) = (term581 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408362 _69903 _69904 _69905) (@lem5408403 _69903 _69904 _69905)). Qed.
Lemma lem5408405 (_69903 : int) (_69904 : int) (_69905 : int) : (term426 _69903 _69904 _69905) = (term581 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408361 _69903 _69904 _69905) (@lem5408404 _69903 _69904 _69905)). Qed.
Lemma lem5408406 (_69903 : int) (_69904 : int) (_69905 : int) : (term248 _69903 _69904 _69905) = (term581 _69903 _69904 _69905).
Proof. exact (TRANS (@lem5408108 _69903 _69904 _69905) (@lem5408405 _69903 _69904 _69905)). Qed.
Lemma lem5408452 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term581 _69903 _69904 _69905) : term581 _69903 _69904 _69905.
Proof. exact (h1). Qed.
Lemma lem5408453 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term578 _69903 _69904 _69905) : term578 _69903 _69904 _69905.
Proof. exact (h1). Qed.
Lemma lem5408454 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term573 _69903 _69904 _69905) : term573 _69903 _69904 _69905.
Proof. exact (h1). Qed.
Lemma lem5408455 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term582 _69903 _69904 _69905.
Proof. exact (h1). Qed.
Lemma lem5408456 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term574 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5408455 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408458 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term543 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5408456 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408460 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term512 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5408458 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408462 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term481 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5408460 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408463 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term284 _69903 _69904.
Proof. exact (proj1 (@lem5408460 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408464 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : (term362 _69904 _69905) = term182.
Proof. exact (proj2 (@lem5408462 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408465 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term304 _69903 _69905.
Proof. exact (proj1 (@lem5408462 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408467 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5408468 : term583 = term314.
Proof. exact (@lem5408467 term182 term193). Qed.
Lemma lem5408470 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5408471 : term193 = term290.
Proof. exact (@lem5408470 term79). Qed.
Lemma lem5408473 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5408474 : term182 = term253.
Proof. exact (@lem5408473 (NUMERAL 0)). Qed.
Lemma lem5408475 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5408476 : term584 = term585.
Proof. exact (MK_COMB (@lem5408475) (@lem5408474)). Qed.
Lemma lem5408477 : term314 = term586.
Proof. exact (MK_COMB (@lem5408476) (@lem5408471)). Qed.
Lemma lem5408478 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5408480 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408481 : term314 = term315.
Proof. exact (@lem5408480 (NUMERAL 0) term79). Qed.
Lemma lem5408482 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408483 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408484 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408483 h1) (fun h1 : term315 = True => @lem5408482)). Qed.
Lemma lem5408485 : term315 = True.
Proof. exact (EQ_MP (@lem5408484) (@lem5408482)). Qed.
Lemma lem5408486 : term314 = True.
Proof. exact (TRANS (@lem5408481) (@lem5408485)). Qed.
Lemma lem5408487 : True = term314.
Proof. exact (SYM (@lem5408486)). Qed.
Lemma lem5408488 : term314.
Proof. exact (EQ_MP (@lem5408487) (@lem0)). Qed.
Lemma lem5408489 : term588.
Proof. exact (@lem5408478 (@lem5408488)). Qed.
Lemma lem5408491 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408492 : term314 = term315.
Proof. exact (@lem5408491 (NUMERAL 0) term79). Qed.
Lemma lem5408493 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408494 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408495 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408494 h1) (fun h1 : term315 = True => @lem5408493)). Qed.
Lemma lem5408496 : term315 = True.
Proof. exact (EQ_MP (@lem5408495) (@lem5408493)). Qed.
Lemma lem5408497 : term314 = True.
Proof. exact (TRANS (@lem5408492) (@lem5408496)). Qed.
Lemma lem5408498 : True = term314.
Proof. exact (SYM (@lem5408497)). Qed.
Lemma lem5408499 : term314.
Proof. exact (EQ_MP (@lem5408498) (@lem0)). Qed.
Lemma lem5408500 : term586 = term589.
Proof. exact (@lem5408489 (@lem5408499)). Qed.
Lemma lem5408502 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5408503 : term265 = term266.
Proof. exact (@lem5408502 term79 term79). Qed.
Lemma lem5408504 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5408505 : term268 = term79.
Proof. exact (EQ_MP (@lem5408504) (@lem940073)). Qed.
Lemma lem5408506 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5408507 : term266 = term193.
Proof. exact (MK_COMB (@lem5408506) (@lem5408505)). Qed.
Lemma lem5408508 : term265 = term193.
Proof. exact (TRANS (@lem5408503) (@lem5408507)). Qed.
Lemma lem5408510 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5408511 : term405 = term182.
Proof. exact (@lem5408510 term79). Qed.
Lemma lem5408512 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5408513 : term590 = term584.
Proof. exact (MK_COMB (@lem5408512) (@lem5408511)). Qed.
Lemma lem5408514 : term589 = term314.
Proof. exact (MK_COMB (@lem5408513) (@lem5408508)). Qed.
Lemma lem5408516 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408517 : term314 = term315.
Proof. exact (@lem5408516 (NUMERAL 0) term79). Qed.
Lemma lem5408518 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408519 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408520 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408519 h1) (fun h1 : term315 = True => @lem5408518)). Qed.
Lemma lem5408521 : term315 = True.
Proof. exact (EQ_MP (@lem5408520) (@lem5408518)). Qed.
Lemma lem5408522 : term314 = True.
Proof. exact (TRANS (@lem5408517) (@lem5408521)). Qed.
Lemma lem5408523 : term589 = True.
Proof. exact (TRANS (@lem5408514) (@lem5408522)). Qed.
Lemma lem5408524 : term586 = True.
Proof. exact (TRANS (@lem5408500) (@lem5408523)). Qed.
Lemma lem5408525 : term314 = True.
Proof. exact (TRANS (@lem5408477) (@lem5408524)). Qed.
Lemma lem5408526 : term583 = True.
Proof. exact (TRANS (@lem5408468) (@lem5408525)). Qed.
Lemma lem5408527 : True = term583.
Proof. exact (SYM (@lem5408526)). Qed.
Lemma lem5408528 : term583.
Proof. exact (EQ_MP (@lem5408527) (@lem0)). Qed.
Lemma lem5408529 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term591 _69903 _69905.
Proof. exact (conj (@lem5408528) (@lem5408465 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408531 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5408532 (_69903 : int) (_69905 : int) : term593 _69903 _69905.
Proof. exact (@lem5408531 term193 (term301 _69903 _69905)). Qed.
Lemma lem5408533 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term594 _69903 _69905.
Proof. exact (@lem5408532 _69903 _69905 (@lem5408529 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408534 (_69903 : int) (_69905 : int) : (term595 _69903 _69905) = (term301 _69903 _69905).
Proof. exact (@lem1982733 (term301 _69903 _69905)). Qed.
Lemma lem5408535 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5408536 (_69903 : int) (_69905 : int) : (term596 _69903 _69905) = (term303 _69903 _69905).
Proof. exact (MK_COMB (@lem5408535) (@lem5408534 _69903 _69905)). Qed.
Lemma lem5408537 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5408538 (_69903 : int) (_69905 : int) : (term594 _69903 _69905) = (term304 _69903 _69905).
Proof. exact (MK_COMB (@lem5408536 _69903 _69905) (@lem5408537)). Qed.
Lemma lem5408539 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term304 _69903 _69905.
Proof. exact (EQ_MP (@lem5408538 _69903 _69905) (@lem5408533 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408541 (y : real) : term597 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5408542 (_69904 : int) (_69905 : int) : term598 _69904 _69905.
Proof. exact (@lem5408541 (term362 _69904 _69905)). Qed.
Lemma lem5408543 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term599 _69904 _69905.
Proof. exact (@lem5408542 _69904 _69905 (@lem5408464 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408544 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term600 _69904 _69905.
Proof. exact (@lem5408543 _69903 _69904 _69905 h1 term193). Qed.
Lemma lem5408545 (_69904 : int) (_69905 : int) : (term600 _69904 _69905) = ((term601 _69904 _69905) = term182).
Proof. exact (eq_refl (term600 _69904 _69905)). Qed.
Lemma lem5408546 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : (term601 _69904 _69905) = term182.
Proof. exact (EQ_MP (@lem5408545 _69904 _69905) (@lem5408544 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408547 (_69904 : int) (_69905 : int) : (term601 _69904 _69905) = (term362 _69904 _69905).
Proof. exact (@lem1982733 (term362 _69904 _69905)). Qed.
Lemma lem5408548 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5408549 (_69904 : int) (_69905 : int) : (term602 _69904 _69905) = (term364 _69904 _69905).
Proof. exact (MK_COMB (@lem5408548) (@lem5408547 _69904 _69905)). Qed.
Lemma lem5408550 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5408551 (_69904 : int) (_69905 : int) : ((term601 _69904 _69905) = term182) = ((term362 _69904 _69905) = term182).
Proof. exact (MK_COMB (@lem5408549 _69904 _69905) (@lem5408550)). Qed.
Lemma lem5408552 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : (term362 _69904 _69905) = term182.
Proof. exact (EQ_MP (@lem5408551 _69904 _69905) (@lem5408546 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408553 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term603 _69904 _69903 _69905.
Proof. exact (conj (@lem5408552 _69903 _69904 _69905 h1) (@lem5408539 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408555 (x : real) (y : real) : term604 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5408556 (_69904 : int) (_69903 : int) (_69905 : int) : term605 _69904 _69903 _69905.
Proof. exact (@lem5408555 (term362 _69904 _69905) (term301 _69903 _69905)). Qed.
Lemma lem5408557 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term606 _69904 _69903 _69905.
Proof. exact (@lem5408556 _69904 _69903 _69905 (@lem5408553 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408558 (_69903 : int) (_69904 : int) (_69905 : int) : (term607 _69904 _69903 _69905) = (term608 _69903 _69904 _69905).
Proof. exact (@lem1982757 (real_of_int _69903) (term362 _69904 _69905) (term300 _69905)). Qed.
Lemma lem5408559 (_69904 : int) (_69905 : int) : (term609 _69904 _69905) = (term610 _69904 _69905).
Proof. exact (@lem1982755 (term281 _69904) (term611 _69905) (term300 _69905)). Qed.
Lemma lem5408560 (_69905 : int) : (term612 _69905) = (term613 _69905).
Proof. exact (@lem1982753 (real_of_int _69905) (term281 _69905) term256 term256). Qed.
Lemma lem5408561 (_69905 : int) : (term614 _69905) = (term615 _69905).
Proof. exact (@lem1982715 term256 (real_of_int _69905)). Qed.
Lemma lem5408563 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5408564 : term193 = term290.
Proof. exact (@lem5408563 term79). Qed.
Lemma lem5408566 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5408567 : term256 = term257.
Proof. exact (@lem5408566 term79). Qed.
Lemma lem5408568 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5408569 : term616 = term617.
Proof. exact (MK_COMB (@lem5408568) (@lem5408567)). Qed.
Lemma lem5408570 : term618 = term619.
Proof. exact (MK_COMB (@lem5408569) (@lem5408564)). Qed.
Lemma lem5408571 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5408573 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408574 : term314 = term315.
Proof. exact (@lem5408573 (NUMERAL 0) term79). Qed.
Lemma lem5408575 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408576 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408577 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408576 h1) (fun h1 : term315 = True => @lem5408575)). Qed.
Lemma lem5408578 : term315 = True.
Proof. exact (EQ_MP (@lem5408577) (@lem5408575)). Qed.
Lemma lem5408579 : term314 = True.
Proof. exact (TRANS (@lem5408574) (@lem5408578)). Qed.
Lemma lem5408580 : True = term314.
Proof. exact (SYM (@lem5408579)). Qed.
Lemma lem5408581 : term314.
Proof. exact (EQ_MP (@lem5408580) (@lem0)). Qed.
Lemma lem5408582 : term621.
Proof. exact (@lem5408571 (@lem5408581)). Qed.
Lemma lem5408584 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408585 : term314 = term315.
Proof. exact (@lem5408584 (NUMERAL 0) term79). Qed.
Lemma lem5408586 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408587 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408588 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408587 h1) (fun h1 : term315 = True => @lem5408586)). Qed.
Lemma lem5408589 : term315 = True.
Proof. exact (EQ_MP (@lem5408588) (@lem5408586)). Qed.
Lemma lem5408590 : term314 = True.
Proof. exact (TRANS (@lem5408585) (@lem5408589)). Qed.
Lemma lem5408591 : True = term314.
Proof. exact (SYM (@lem5408590)). Qed.
Lemma lem5408592 : term314.
Proof. exact (EQ_MP (@lem5408591) (@lem0)). Qed.
Lemma lem5408593 : term622.
Proof. exact (@lem5408582 (@lem5408592)). Qed.
Lemma lem5408595 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408596 : term314 = term315.
Proof. exact (@lem5408595 (NUMERAL 0) term79). Qed.
Lemma lem5408597 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408598 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408599 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408598 h1) (fun h1 : term315 = True => @lem5408597)). Qed.
Lemma lem5408600 : term315 = True.
Proof. exact (EQ_MP (@lem5408599) (@lem5408597)). Qed.
Lemma lem5408601 : term314 = True.
Proof. exact (TRANS (@lem5408596) (@lem5408600)). Qed.
Lemma lem5408602 : True = term314.
Proof. exact (SYM (@lem5408601)). Qed.
Lemma lem5408603 : term314.
Proof. exact (EQ_MP (@lem5408602) (@lem0)). Qed.
Lemma lem5408604 : term623.
Proof. exact (@lem5408593 (@lem5408603)). Qed.
Lemma lem5408606 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5408607 : term265 = term266.
Proof. exact (@lem5408606 term79 term79). Qed.
Lemma lem5408608 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5408609 : term268 = term79.
Proof. exact (EQ_MP (@lem5408608) (@lem940073)). Qed.
Lemma lem5408610 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5408611 : term266 = term193.
Proof. exact (MK_COMB (@lem5408610) (@lem5408609)). Qed.
Lemma lem5408612 : term265 = term193.
Proof. exact (TRANS (@lem5408607) (@lem5408611)). Qed.
Lemma lem5408614 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5408615 : term291 = term296.
Proof. exact (@lem5408614 term79 term79). Qed.
Lemma lem5408616 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5408617 : term268 = term79.
Proof. exact (EQ_MP (@lem5408616) (@lem940073)). Qed.
Lemma lem5408618 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5408619 : term266 = term193.
Proof. exact (MK_COMB (@lem5408618) (@lem5408617)). Qed.
Lemma lem5408620 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5408621 : term296 = term256.
Proof. exact (MK_COMB (@lem5408620) (@lem5408619)). Qed.
Lemma lem5408622 : term291 = term256.
Proof. exact (TRANS (@lem5408615) (@lem5408621)). Qed.
Lemma lem5408623 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5408624 : term624 = term616.
Proof. exact (MK_COMB (@lem5408623) (@lem5408622)). Qed.
Lemma lem5408625 : term625 = term618.
Proof. exact (MK_COMB (@lem5408624) (@lem5408612)). Qed.
Lemma lem5408627 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5408628 : term618 = term182.
Proof. exact (@lem5408627 term79). Qed.
Lemma lem5408629 : term625 = term182.
Proof. exact (TRANS (@lem5408625) (@lem5408628)). Qed.
Lemma lem5408630 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5408631 : term627 = term403.
Proof. exact (MK_COMB (@lem5408630) (@lem5408629)). Qed.
Lemma lem5408632 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5408633 : term628 = term405.
Proof. exact (MK_COMB (@lem5408631) (@lem5408632)). Qed.
Lemma lem5408635 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5408636 : term405 = term182.
Proof. exact (@lem5408635 term79). Qed.
Lemma lem5408637 : term628 = term182.
Proof. exact (TRANS (@lem5408633) (@lem5408636)). Qed.
Lemma lem5408639 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5408640 : term265 = term266.
Proof. exact (@lem5408639 term79 term79). Qed.
Lemma lem5408641 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5408642 : term268 = term79.
Proof. exact (EQ_MP (@lem5408641) (@lem940073)). Qed.
Lemma lem5408643 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5408644 : term266 = term193.
Proof. exact (MK_COMB (@lem5408643) (@lem5408642)). Qed.
Lemma lem5408645 : term265 = term193.
Proof. exact (TRANS (@lem5408640) (@lem5408644)). Qed.
Lemma lem5408646 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5408647 : term407 = term405.
Proof. exact (MK_COMB (@lem5408646) (@lem5408645)). Qed.
Lemma lem5408649 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5408650 : term405 = term182.
Proof. exact (@lem5408649 term79). Qed.
Lemma lem5408651 : term407 = term182.
Proof. exact (TRANS (@lem5408647) (@lem5408650)). Qed.
Lemma lem5408652 : term182 = term407.
Proof. exact (SYM (@lem5408651)). Qed.
Lemma lem5408653 : term628 = term407.
Proof. exact (TRANS (@lem5408637) (@lem5408652)). Qed.
Lemma lem5408654 : term619 = term253.
Proof. exact (@lem5408604 (@lem5408653)). Qed.
Lemma lem5408655 : term618 = term253.
Proof. exact (TRANS (@lem5408570) (@lem5408654)). Qed.
Lemma lem5408657 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5408658 : term253 = term182.
Proof. exact (@lem5408657 term182). Qed.
Lemma lem5408659 : term618 = term182.
Proof. exact (TRANS (@lem5408655) (@lem5408658)). Qed.
Lemma lem5408660 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5408661 : term629 = term403.
Proof. exact (MK_COMB (@lem5408660) (@lem5408659)). Qed.
Lemma lem5408662 (_69905 : int) : (real_of_int _69905) = (real_of_int _69905).
Proof. exact (eq_refl (real_of_int _69905)). Qed.
Lemma lem5408663 (_69905 : int) : (term615 _69905) = (term630 _69905).
Proof. exact (MK_COMB (@lem5408661) (@lem5408662 _69905)). Qed.
Lemma lem5408664 (_69905 : int) : (term614 _69905) = (term630 _69905).
Proof. exact (TRANS (@lem5408561 _69905) (@lem5408663 _69905)). Qed.
Lemma lem5408665 (_69905 : int) : (term630 _69905) = term182.
Proof. exact (@lem1982719 (real_of_int _69905)). Qed.
Lemma lem5408666 (_69905 : int) : (term614 _69905) = term182.
Proof. exact (TRANS (@lem5408664 _69905) (@lem5408665 _69905)). Qed.
Lemma lem5408667 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5408668 (_69905 : int) : (term631 _69905) = term632.
Proof. exact (MK_COMB (@lem5408667) (@lem5408666 _69905)). Qed.
Lemma lem5408670 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5408671 : term256 = term257.
Proof. exact (@lem5408670 term79). Qed.
Lemma lem5408673 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5408674 : term256 = term257.
Proof. exact (@lem5408673 term79). Qed.
Lemma lem5408675 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5408676 : term616 = term617.
Proof. exact (MK_COMB (@lem5408675) (@lem5408674)). Qed.
Lemma lem5408677 : term633 = term634.
Proof. exact (MK_COMB (@lem5408676) (@lem5408671)). Qed.
Lemma lem5408678 : term635.
Proof. exact (@lem1981473 term256 term193 term256 term193 term350 term193). Qed.
Lemma lem5408680 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408681 : term314 = term315.
Proof. exact (@lem5408680 (NUMERAL 0) term79). Qed.
Lemma lem5408682 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408683 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408684 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408683 h1) (fun h1 : term315 = True => @lem5408682)). Qed.
Lemma lem5408685 : term315 = True.
Proof. exact (EQ_MP (@lem5408684) (@lem5408682)). Qed.
Lemma lem5408686 : term314 = True.
Proof. exact (TRANS (@lem5408681) (@lem5408685)). Qed.
Lemma lem5408687 : True = term314.
Proof. exact (SYM (@lem5408686)). Qed.
Lemma lem5408688 : term314.
Proof. exact (EQ_MP (@lem5408687) (@lem0)). Qed.
Lemma lem5408689 : term636.
Proof. exact (@lem5408678 (@lem5408688)). Qed.
Lemma lem5408691 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408692 : term314 = term315.
Proof. exact (@lem5408691 (NUMERAL 0) term79). Qed.
Lemma lem5408693 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408694 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408695 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408694 h1) (fun h1 : term315 = True => @lem5408693)). Qed.
Lemma lem5408696 : term315 = True.
Proof. exact (EQ_MP (@lem5408695) (@lem5408693)). Qed.
Lemma lem5408697 : term314 = True.
Proof. exact (TRANS (@lem5408692) (@lem5408696)). Qed.
Lemma lem5408698 : True = term314.
Proof. exact (SYM (@lem5408697)). Qed.
Lemma lem5408699 : term314.
Proof. exact (EQ_MP (@lem5408698) (@lem0)). Qed.
Lemma lem5408700 : term637.
Proof. exact (@lem5408689 (@lem5408699)). Qed.
Lemma lem5408702 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408703 : term314 = term315.
Proof. exact (@lem5408702 (NUMERAL 0) term79). Qed.
Lemma lem5408704 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408705 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408706 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408705 h1) (fun h1 : term315 = True => @lem5408704)). Qed.
Lemma lem5408707 : term315 = True.
Proof. exact (EQ_MP (@lem5408706) (@lem5408704)). Qed.
Lemma lem5408708 : term314 = True.
Proof. exact (TRANS (@lem5408703) (@lem5408707)). Qed.
Lemma lem5408709 : True = term314.
Proof. exact (SYM (@lem5408708)). Qed.
Lemma lem5408710 : term314.
Proof. exact (EQ_MP (@lem5408709) (@lem0)). Qed.
Lemma lem5408711 : term638.
Proof. exact (@lem5408700 (@lem5408710)). Qed.
Lemma lem5408713 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5408714 : term291 = term296.
Proof. exact (@lem5408713 term79 term79). Qed.
Lemma lem5408715 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5408716 : term268 = term79.
Proof. exact (EQ_MP (@lem5408715) (@lem940073)). Qed.
Lemma lem5408717 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5408718 : term266 = term193.
Proof. exact (MK_COMB (@lem5408717) (@lem5408716)). Qed.
Lemma lem5408719 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5408720 : term296 = term256.
Proof. exact (MK_COMB (@lem5408719) (@lem5408718)). Qed.
Lemma lem5408721 : term291 = term256.
Proof. exact (TRANS (@lem5408714) (@lem5408720)). Qed.
Lemma lem5408723 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5408724 : term291 = term296.
Proof. exact (@lem5408723 term79 term79). Qed.
Lemma lem5408725 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5408726 : term268 = term79.
Proof. exact (EQ_MP (@lem5408725) (@lem940073)). Qed.
Lemma lem5408727 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5408728 : term266 = term193.
Proof. exact (MK_COMB (@lem5408727) (@lem5408726)). Qed.
Lemma lem5408729 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5408730 : term296 = term256.
Proof. exact (MK_COMB (@lem5408729) (@lem5408728)). Qed.
Lemma lem5408731 : term291 = term256.
Proof. exact (TRANS (@lem5408724) (@lem5408730)). Qed.
Lemma lem5408732 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5408733 : term624 = term616.
Proof. exact (MK_COMB (@lem5408732) (@lem5408731)). Qed.
Lemma lem5408734 : term639 = term633.
Proof. exact (MK_COMB (@lem5408733) (@lem5408721)). Qed.
Lemma lem5408735 : term633 = term640.
Proof. exact (@lem1367763 term79 term79). Qed.
Lemma lem5408736 : term323 = term324.
Proof. exact (@lem706885). Qed.
Lemma lem5408737 : (term323 = term324) = (term325 = term326).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term324). Qed.
Lemma lem5408738 : term325 = term326.
Proof. exact (EQ_MP (@lem5408737) (@lem5408736)). Qed.
Lemma lem5408739 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5408740 : term322 = term312.
Proof. exact (MK_COMB (@lem5408739) (@lem5408738)). Qed.
Lemma lem5408741 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5408742 : term640 = term350.
Proof. exact (MK_COMB (@lem5408741) (@lem5408740)). Qed.
Lemma lem5408743 : term633 = term350.
Proof. exact (TRANS (@lem5408735) (@lem5408742)). Qed.
Lemma lem5408744 : term639 = term350.
Proof. exact (TRANS (@lem5408734) (@lem5408743)). Qed.
Lemma lem5408745 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5408746 : term641 = term642.
Proof. exact (MK_COMB (@lem5408745) (@lem5408744)). Qed.
Lemma lem5408747 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5408748 : term643 = term644.
Proof. exact (MK_COMB (@lem5408746) (@lem5408747)). Qed.
Lemma lem5408750 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5408751 : term644 = term645.
Proof. exact (@lem5408750 term326 term79). Qed.
Lemma lem5408752 : term332 = term324.
Proof. exact (@lem996237 term324). Qed.
Lemma lem5408753 : (term332 = term324) = (term333 = term326).
Proof. exact (@lem1007663 term324 (BIT1 0) term324). Qed.
Lemma lem5408754 : term333 = term326.
Proof. exact (EQ_MP (@lem5408753) (@lem5408752)). Qed.
Lemma lem5408755 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5408756 : term331 = term312.
Proof. exact (MK_COMB (@lem5408755) (@lem5408754)). Qed.
Lemma lem5408757 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5408758 : term645 = term350.
Proof. exact (MK_COMB (@lem5408757) (@lem5408756)). Qed.
Lemma lem5408759 : term644 = term350.
Proof. exact (TRANS (@lem5408751) (@lem5408758)). Qed.
Lemma lem5408760 : term643 = term350.
Proof. exact (TRANS (@lem5408748) (@lem5408759)). Qed.
Lemma lem5408762 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5408763 : term265 = term266.
Proof. exact (@lem5408762 term79 term79). Qed.
Lemma lem5408764 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5408765 : term268 = term79.
Proof. exact (EQ_MP (@lem5408764) (@lem940073)). Qed.
Lemma lem5408766 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5408767 : term266 = term193.
Proof. exact (MK_COMB (@lem5408766) (@lem5408765)). Qed.
Lemma lem5408768 : term265 = term193.
Proof. exact (TRANS (@lem5408763) (@lem5408767)). Qed.
Lemma lem5408769 : term642 = term642.
Proof. exact (eq_refl term642). Qed.
Lemma lem5408770 : term646 = term644.
Proof. exact (MK_COMB (@lem5408769) (@lem5408768)). Qed.
Lemma lem5408772 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5408773 : term644 = term645.
Proof. exact (@lem5408772 term326 term79). Qed.
Lemma lem5408774 : term332 = term324.
Proof. exact (@lem996237 term324). Qed.
Lemma lem5408775 : (term332 = term324) = (term333 = term326).
Proof. exact (@lem1007663 term324 (BIT1 0) term324). Qed.
Lemma lem5408776 : term333 = term326.
Proof. exact (EQ_MP (@lem5408775) (@lem5408774)). Qed.
Lemma lem5408777 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5408778 : term331 = term312.
Proof. exact (MK_COMB (@lem5408777) (@lem5408776)). Qed.
Lemma lem5408779 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5408780 : term645 = term350.
Proof. exact (MK_COMB (@lem5408779) (@lem5408778)). Qed.
Lemma lem5408781 : term644 = term350.
Proof. exact (TRANS (@lem5408773) (@lem5408780)). Qed.
Lemma lem5408782 : term646 = term350.
Proof. exact (TRANS (@lem5408770) (@lem5408781)). Qed.
Lemma lem5408783 : term350 = term646.
Proof. exact (SYM (@lem5408782)). Qed.
Lemma lem5408784 : term643 = term646.
Proof. exact (TRANS (@lem5408760) (@lem5408783)). Qed.
Lemma lem5408785 : term634 = term353.
Proof. exact (@lem5408711 (@lem5408784)). Qed.
Lemma lem5408786 : term633 = term353.
Proof. exact (TRANS (@lem5408677) (@lem5408785)). Qed.
Lemma lem5408788 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5408789 : term353 = term350.
Proof. exact (@lem5408788 term350). Qed.
Lemma lem5408790 : term633 = term350.
Proof. exact (TRANS (@lem5408786) (@lem5408789)). Qed.
Lemma lem5408791 (_69905 : int) : (term613 _69905) = term647.
Proof. exact (MK_COMB (@lem5408668 _69905) (@lem5408790)). Qed.
Lemma lem5408792 (_69905 : int) : (term612 _69905) = term647.
Proof. exact (TRANS (@lem5408560 _69905) (@lem5408791 _69905)). Qed.
Lemma lem5408793 : term647 = term350.
Proof. exact (@lem1982721 term350). Qed.
Lemma lem5408794 (_69905 : int) : (term612 _69905) = term350.
Proof. exact (TRANS (@lem5408792 _69905) (@lem5408793)). Qed.
Lemma lem5408795 (_69904 : int) : (term299 _69904) = (term299 _69904).
Proof. exact (eq_refl (term299 _69904)). Qed.
Lemma lem5408796 (_69905 : int) (_69904 : int) : (term610 _69904 _69905) = (term354 _69904).
Proof. exact (MK_COMB (@lem5408795 _69904) (@lem5408794 _69905)). Qed.
Lemma lem5408797 (_69905 : int) (_69904 : int) : (term609 _69904 _69905) = (term354 _69904).
Proof. exact (TRANS (@lem5408559 _69904 _69905) (@lem5408796 _69905 _69904)). Qed.
Lemma lem5408798 (_69903 : int) : (term194 _69903) = (term194 _69903).
Proof. exact (eq_refl (term194 _69903)). Qed.
Lemma lem5408799 (_69905 : int) (_69903 : int) (_69904 : int) : (term608 _69903 _69904 _69905) = (term355 _69903 _69904).
Proof. exact (MK_COMB (@lem5408798 _69903) (@lem5408797 _69905 _69904)). Qed.
Lemma lem5408800 (_69905 : int) (_69903 : int) (_69904 : int) : (term607 _69904 _69903 _69905) = (term355 _69903 _69904).
Proof. exact (TRANS (@lem5408558 _69903 _69904 _69905) (@lem5408799 _69905 _69903 _69904)). Qed.
Lemma lem5408801 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5408802 (_69905 : int) (_69903 : int) (_69904 : int) : (term648 _69904 _69903 _69905) = (term649 _69903 _69904).
Proof. exact (MK_COMB (@lem5408801) (@lem5408800 _69905 _69903 _69904)). Qed.
Lemma lem5408803 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5408804 (_69905 : int) (_69903 : int) (_69904 : int) : (term606 _69904 _69903 _69905) = (term650 _69903 _69904).
Proof. exact (MK_COMB (@lem5408802 _69905 _69903 _69904) (@lem5408803)). Qed.
Lemma lem5408805 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term650 _69903 _69904.
Proof. exact (EQ_MP (@lem5408804 _69905 _69903 _69904) (@lem5408557 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408807 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5408808 : term583 = term314.
Proof. exact (@lem5408807 term182 term193). Qed.
Lemma lem5408810 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5408811 : term193 = term290.
Proof. exact (@lem5408810 term79). Qed.
Lemma lem5408813 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5408814 : term182 = term253.
Proof. exact (@lem5408813 (NUMERAL 0)). Qed.
Lemma lem5408815 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5408816 : term584 = term585.
Proof. exact (MK_COMB (@lem5408815) (@lem5408814)). Qed.
Lemma lem5408817 : term314 = term586.
Proof. exact (MK_COMB (@lem5408816) (@lem5408811)). Qed.
Lemma lem5408818 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5408820 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408821 : term314 = term315.
Proof. exact (@lem5408820 (NUMERAL 0) term79). Qed.
Lemma lem5408822 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408823 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408824 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408823 h1) (fun h1 : term315 = True => @lem5408822)). Qed.
Lemma lem5408825 : term315 = True.
Proof. exact (EQ_MP (@lem5408824) (@lem5408822)). Qed.
Lemma lem5408826 : term314 = True.
Proof. exact (TRANS (@lem5408821) (@lem5408825)). Qed.
Lemma lem5408827 : True = term314.
Proof. exact (SYM (@lem5408826)). Qed.
Lemma lem5408828 : term314.
Proof. exact (EQ_MP (@lem5408827) (@lem0)). Qed.
Lemma lem5408829 : term588.
Proof. exact (@lem5408818 (@lem5408828)). Qed.
Lemma lem5408831 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408832 : term314 = term315.
Proof. exact (@lem5408831 (NUMERAL 0) term79). Qed.
Lemma lem5408833 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408834 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408835 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408834 h1) (fun h1 : term315 = True => @lem5408833)). Qed.
Lemma lem5408836 : term315 = True.
Proof. exact (EQ_MP (@lem5408835) (@lem5408833)). Qed.
Lemma lem5408837 : term314 = True.
Proof. exact (TRANS (@lem5408832) (@lem5408836)). Qed.
Lemma lem5408838 : True = term314.
Proof. exact (SYM (@lem5408837)). Qed.
Lemma lem5408839 : term314.
Proof. exact (EQ_MP (@lem5408838) (@lem0)). Qed.
Lemma lem5408840 : term586 = term589.
Proof. exact (@lem5408829 (@lem5408839)). Qed.
Lemma lem5408842 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5408843 : term265 = term266.
Proof. exact (@lem5408842 term79 term79). Qed.
Lemma lem5408844 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5408845 : term268 = term79.
Proof. exact (EQ_MP (@lem5408844) (@lem940073)). Qed.
Lemma lem5408846 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5408847 : term266 = term193.
Proof. exact (MK_COMB (@lem5408846) (@lem5408845)). Qed.
Lemma lem5408848 : term265 = term193.
Proof. exact (TRANS (@lem5408843) (@lem5408847)). Qed.
Lemma lem5408850 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5408851 : term405 = term182.
Proof. exact (@lem5408850 term79). Qed.
Lemma lem5408852 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5408853 : term590 = term584.
Proof. exact (MK_COMB (@lem5408852) (@lem5408851)). Qed.
Lemma lem5408854 : term589 = term314.
Proof. exact (MK_COMB (@lem5408853) (@lem5408848)). Qed.
Lemma lem5408856 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408857 : term314 = term315.
Proof. exact (@lem5408856 (NUMERAL 0) term79). Qed.
Lemma lem5408858 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408859 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408860 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408859 h1) (fun h1 : term315 = True => @lem5408858)). Qed.
Lemma lem5408861 : term315 = True.
Proof. exact (EQ_MP (@lem5408860) (@lem5408858)). Qed.
Lemma lem5408862 : term314 = True.
Proof. exact (TRANS (@lem5408857) (@lem5408861)). Qed.
Lemma lem5408863 : term589 = True.
Proof. exact (TRANS (@lem5408854) (@lem5408862)). Qed.
Lemma lem5408864 : term586 = True.
Proof. exact (TRANS (@lem5408840) (@lem5408863)). Qed.
Lemma lem5408865 : term314 = True.
Proof. exact (TRANS (@lem5408817) (@lem5408864)). Qed.
Lemma lem5408866 : term583 = True.
Proof. exact (TRANS (@lem5408808) (@lem5408865)). Qed.
Lemma lem5408867 : True = term583.
Proof. exact (SYM (@lem5408866)). Qed.
Lemma lem5408868 : term583.
Proof. exact (EQ_MP (@lem5408867) (@lem0)). Qed.
Lemma lem5408869 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term651 _69903 _69904.
Proof. exact (conj (@lem5408868) (@lem5408805 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408871 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5408872 (_69903 : int) (_69904 : int) : term652 _69903 _69904.
Proof. exact (@lem5408871 term193 (term355 _69903 _69904)). Qed.
Lemma lem5408873 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term653 _69903 _69904.
Proof. exact (@lem5408872 _69903 _69904 (@lem5408869 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408874 (_69903 : int) (_69904 : int) : (term654 _69903 _69904) = (term355 _69903 _69904).
Proof. exact (@lem1982733 (term355 _69903 _69904)). Qed.
Lemma lem5408875 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5408876 (_69903 : int) (_69904 : int) : (term655 _69903 _69904) = (term649 _69903 _69904).
Proof. exact (MK_COMB (@lem5408875) (@lem5408874 _69903 _69904)). Qed.
Lemma lem5408877 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5408878 (_69903 : int) (_69904 : int) : (term653 _69903 _69904) = (term650 _69903 _69904).
Proof. exact (MK_COMB (@lem5408876 _69903 _69904) (@lem5408877)). Qed.
Lemma lem5408879 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term650 _69903 _69904.
Proof. exact (EQ_MP (@lem5408878 _69903 _69904) (@lem5408873 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408881 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5408882 : term583 = term314.
Proof. exact (@lem5408881 term182 term193). Qed.
Lemma lem5408884 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5408885 : term193 = term290.
Proof. exact (@lem5408884 term79). Qed.
Lemma lem5408887 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5408888 : term182 = term253.
Proof. exact (@lem5408887 (NUMERAL 0)). Qed.
Lemma lem5408889 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5408890 : term584 = term585.
Proof. exact (MK_COMB (@lem5408889) (@lem5408888)). Qed.
Lemma lem5408891 : term314 = term586.
Proof. exact (MK_COMB (@lem5408890) (@lem5408885)). Qed.
Lemma lem5408892 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5408894 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408895 : term314 = term315.
Proof. exact (@lem5408894 (NUMERAL 0) term79). Qed.
Lemma lem5408896 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408897 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408898 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408897 h1) (fun h1 : term315 = True => @lem5408896)). Qed.
Lemma lem5408899 : term315 = True.
Proof. exact (EQ_MP (@lem5408898) (@lem5408896)). Qed.
Lemma lem5408900 : term314 = True.
Proof. exact (TRANS (@lem5408895) (@lem5408899)). Qed.
Lemma lem5408901 : True = term314.
Proof. exact (SYM (@lem5408900)). Qed.
Lemma lem5408902 : term314.
Proof. exact (EQ_MP (@lem5408901) (@lem0)). Qed.
Lemma lem5408903 : term588.
Proof. exact (@lem5408892 (@lem5408902)). Qed.
Lemma lem5408905 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408906 : term314 = term315.
Proof. exact (@lem5408905 (NUMERAL 0) term79). Qed.
Lemma lem5408907 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408908 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408909 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408908 h1) (fun h1 : term315 = True => @lem5408907)). Qed.
Lemma lem5408910 : term315 = True.
Proof. exact (EQ_MP (@lem5408909) (@lem5408907)). Qed.
Lemma lem5408911 : term314 = True.
Proof. exact (TRANS (@lem5408906) (@lem5408910)). Qed.
Lemma lem5408912 : True = term314.
Proof. exact (SYM (@lem5408911)). Qed.
Lemma lem5408913 : term314.
Proof. exact (EQ_MP (@lem5408912) (@lem0)). Qed.
Lemma lem5408914 : term586 = term589.
Proof. exact (@lem5408903 (@lem5408913)). Qed.
Lemma lem5408916 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5408917 : term265 = term266.
Proof. exact (@lem5408916 term79 term79). Qed.
Lemma lem5408918 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5408919 : term268 = term79.
Proof. exact (EQ_MP (@lem5408918) (@lem940073)). Qed.
Lemma lem5408920 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5408921 : term266 = term193.
Proof. exact (MK_COMB (@lem5408920) (@lem5408919)). Qed.
Lemma lem5408922 : term265 = term193.
Proof. exact (TRANS (@lem5408917) (@lem5408921)). Qed.
Lemma lem5408924 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5408925 : term405 = term182.
Proof. exact (@lem5408924 term79). Qed.
Lemma lem5408926 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5408927 : term590 = term584.
Proof. exact (MK_COMB (@lem5408926) (@lem5408925)). Qed.
Lemma lem5408928 : term589 = term314.
Proof. exact (MK_COMB (@lem5408927) (@lem5408922)). Qed.
Lemma lem5408930 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408931 : term314 = term315.
Proof. exact (@lem5408930 (NUMERAL 0) term79). Qed.
Lemma lem5408932 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408933 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408934 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408933 h1) (fun h1 : term315 = True => @lem5408932)). Qed.
Lemma lem5408935 : term315 = True.
Proof. exact (EQ_MP (@lem5408934) (@lem5408932)). Qed.
Lemma lem5408936 : term314 = True.
Proof. exact (TRANS (@lem5408931) (@lem5408935)). Qed.
Lemma lem5408937 : term589 = True.
Proof. exact (TRANS (@lem5408928) (@lem5408936)). Qed.
Lemma lem5408938 : term586 = True.
Proof. exact (TRANS (@lem5408914) (@lem5408937)). Qed.
Lemma lem5408939 : term314 = True.
Proof. exact (TRANS (@lem5408891) (@lem5408938)). Qed.
Lemma lem5408940 : term583 = True.
Proof. exact (TRANS (@lem5408882) (@lem5408939)). Qed.
Lemma lem5408941 : True = term583.
Proof. exact (SYM (@lem5408940)). Qed.
Lemma lem5408942 : term583.
Proof. exact (EQ_MP (@lem5408941) (@lem0)). Qed.
Lemma lem5408943 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term656 _69903 _69904.
Proof. exact (conj (@lem5408942) (@lem5408463 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408945 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5408946 (_69903 : int) (_69904 : int) : term657 _69903 _69904.
Proof. exact (@lem5408945 term193 (term280 _69903 _69904)). Qed.
Lemma lem5408947 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term658 _69903 _69904.
Proof. exact (@lem5408946 _69903 _69904 (@lem5408943 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408948 (_69903 : int) (_69904 : int) : (term659 _69903 _69904) = (term280 _69903 _69904).
Proof. exact (@lem1982733 (term280 _69903 _69904)). Qed.
Lemma lem5408949 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5408950 (_69903 : int) (_69904 : int) : (term660 _69903 _69904) = (term283 _69903 _69904).
Proof. exact (MK_COMB (@lem5408949) (@lem5408948 _69903 _69904)). Qed.
Lemma lem5408951 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5408952 (_69903 : int) (_69904 : int) : (term658 _69903 _69904) = (term284 _69903 _69904).
Proof. exact (MK_COMB (@lem5408950 _69903 _69904) (@lem5408951)). Qed.
Lemma lem5408953 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term284 _69903 _69904.
Proof. exact (EQ_MP (@lem5408952 _69903 _69904) (@lem5408947 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408954 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term661 _69903 _69904.
Proof. exact (conj (@lem5408953 _69903 _69904 _69905 h1) (@lem5408879 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408956 (x : real) (y : real) : term662 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5408957 (_69903 : int) (_69904 : int) : term663 _69903 _69904.
Proof. exact (@lem5408956 (term280 _69903 _69904) (term355 _69903 _69904)). Qed.
Lemma lem5408958 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term664 _69903 _69904.
Proof. exact (@lem5408957 _69903 _69904 (@lem5408954 _69903 _69904 _69905 h1)). Qed.
Lemma lem5408959 (_69903 : int) (_69904 : int) : (term665 _69903 _69904) = (term666 _69903 _69904).
Proof. exact (@lem1982753 (term281 _69903) (real_of_int _69903) (term195 _69904) (term354 _69904)). Qed.
Lemma lem5408960 (_69903 : int) : (term667 _69903) = (term615 _69903).
Proof. exact (@lem1982713 term256 (real_of_int _69903)). Qed.
Lemma lem5408962 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5408963 : term193 = term290.
Proof. exact (@lem5408962 term79). Qed.
Lemma lem5408965 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5408966 : term256 = term257.
Proof. exact (@lem5408965 term79). Qed.
Lemma lem5408967 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5408968 : term616 = term617.
Proof. exact (MK_COMB (@lem5408967) (@lem5408966)). Qed.
Lemma lem5408969 : term618 = term619.
Proof. exact (MK_COMB (@lem5408968) (@lem5408963)). Qed.
Lemma lem5408970 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5408972 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408973 : term314 = term315.
Proof. exact (@lem5408972 (NUMERAL 0) term79). Qed.
Lemma lem5408974 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408975 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408976 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408975 h1) (fun h1 : term315 = True => @lem5408974)). Qed.
Lemma lem5408977 : term315 = True.
Proof. exact (EQ_MP (@lem5408976) (@lem5408974)). Qed.
Lemma lem5408978 : term314 = True.
Proof. exact (TRANS (@lem5408973) (@lem5408977)). Qed.
Lemma lem5408979 : True = term314.
Proof. exact (SYM (@lem5408978)). Qed.
Lemma lem5408980 : term314.
Proof. exact (EQ_MP (@lem5408979) (@lem0)). Qed.
Lemma lem5408981 : term621.
Proof. exact (@lem5408970 (@lem5408980)). Qed.
Lemma lem5408983 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408984 : term314 = term315.
Proof. exact (@lem5408983 (NUMERAL 0) term79). Qed.
Lemma lem5408985 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408986 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408987 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408986 h1) (fun h1 : term315 = True => @lem5408985)). Qed.
Lemma lem5408988 : term315 = True.
Proof. exact (EQ_MP (@lem5408987) (@lem5408985)). Qed.
Lemma lem5408989 : term314 = True.
Proof. exact (TRANS (@lem5408984) (@lem5408988)). Qed.
Lemma lem5408990 : True = term314.
Proof. exact (SYM (@lem5408989)). Qed.
Lemma lem5408991 : term314.
Proof. exact (EQ_MP (@lem5408990) (@lem0)). Qed.
Lemma lem5408992 : term622.
Proof. exact (@lem5408981 (@lem5408991)). Qed.
Lemma lem5408994 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5408995 : term314 = term315.
Proof. exact (@lem5408994 (NUMERAL 0) term79). Qed.
Lemma lem5408996 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5408997 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5408998 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5408997 h1) (fun h1 : term315 = True => @lem5408996)). Qed.
Lemma lem5408999 : term315 = True.
Proof. exact (EQ_MP (@lem5408998) (@lem5408996)). Qed.
Lemma lem5409000 : term314 = True.
Proof. exact (TRANS (@lem5408995) (@lem5408999)). Qed.
Lemma lem5409001 : True = term314.
Proof. exact (SYM (@lem5409000)). Qed.
Lemma lem5409002 : term314.
Proof. exact (EQ_MP (@lem5409001) (@lem0)). Qed.
Lemma lem5409003 : term623.
Proof. exact (@lem5408992 (@lem5409002)). Qed.
Lemma lem5409005 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5409006 : term265 = term266.
Proof. exact (@lem5409005 term79 term79). Qed.
Lemma lem5409007 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409008 : term268 = term79.
Proof. exact (EQ_MP (@lem5409007) (@lem940073)). Qed.
Lemma lem5409009 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409010 : term266 = term193.
Proof. exact (MK_COMB (@lem5409009) (@lem5409008)). Qed.
Lemma lem5409011 : term265 = term193.
Proof. exact (TRANS (@lem5409006) (@lem5409010)). Qed.
Lemma lem5409013 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5409014 : term291 = term296.
Proof. exact (@lem5409013 term79 term79). Qed.
Lemma lem5409015 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409016 : term268 = term79.
Proof. exact (EQ_MP (@lem5409015) (@lem940073)). Qed.
Lemma lem5409017 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409018 : term266 = term193.
Proof. exact (MK_COMB (@lem5409017) (@lem5409016)). Qed.
Lemma lem5409019 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5409020 : term296 = term256.
Proof. exact (MK_COMB (@lem5409019) (@lem5409018)). Qed.
Lemma lem5409021 : term291 = term256.
Proof. exact (TRANS (@lem5409014) (@lem5409020)). Qed.
Lemma lem5409022 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409023 : term624 = term616.
Proof. exact (MK_COMB (@lem5409022) (@lem5409021)). Qed.
Lemma lem5409024 : term625 = term618.
Proof. exact (MK_COMB (@lem5409023) (@lem5409011)). Qed.
Lemma lem5409026 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5409027 : term618 = term182.
Proof. exact (@lem5409026 term79). Qed.
Lemma lem5409028 : term625 = term182.
Proof. exact (TRANS (@lem5409024) (@lem5409027)). Qed.
Lemma lem5409029 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5409030 : term627 = term403.
Proof. exact (MK_COMB (@lem5409029) (@lem5409028)). Qed.
Lemma lem5409031 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5409032 : term628 = term405.
Proof. exact (MK_COMB (@lem5409030) (@lem5409031)). Qed.
Lemma lem5409034 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5409035 : term405 = term182.
Proof. exact (@lem5409034 term79). Qed.
Lemma lem5409036 : term628 = term182.
Proof. exact (TRANS (@lem5409032) (@lem5409035)). Qed.
Lemma lem5409038 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5409039 : term265 = term266.
Proof. exact (@lem5409038 term79 term79). Qed.
Lemma lem5409040 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409041 : term268 = term79.
Proof. exact (EQ_MP (@lem5409040) (@lem940073)). Qed.
Lemma lem5409042 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409043 : term266 = term193.
Proof. exact (MK_COMB (@lem5409042) (@lem5409041)). Qed.
Lemma lem5409044 : term265 = term193.
Proof. exact (TRANS (@lem5409039) (@lem5409043)). Qed.
Lemma lem5409045 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5409046 : term407 = term405.
Proof. exact (MK_COMB (@lem5409045) (@lem5409044)). Qed.
Lemma lem5409048 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5409049 : term405 = term182.
Proof. exact (@lem5409048 term79). Qed.
Lemma lem5409050 : term407 = term182.
Proof. exact (TRANS (@lem5409046) (@lem5409049)). Qed.
Lemma lem5409051 : term182 = term407.
Proof. exact (SYM (@lem5409050)). Qed.
Lemma lem5409052 : term628 = term407.
Proof. exact (TRANS (@lem5409036) (@lem5409051)). Qed.
Lemma lem5409053 : term619 = term253.
Proof. exact (@lem5409003 (@lem5409052)). Qed.
Lemma lem5409054 : term618 = term253.
Proof. exact (TRANS (@lem5408969) (@lem5409053)). Qed.
Lemma lem5409056 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5409057 : term253 = term182.
Proof. exact (@lem5409056 term182). Qed.
Lemma lem5409058 : term618 = term182.
Proof. exact (TRANS (@lem5409054) (@lem5409057)). Qed.
Lemma lem5409059 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5409060 : term629 = term403.
Proof. exact (MK_COMB (@lem5409059) (@lem5409058)). Qed.
Lemma lem5409061 (_69903 : int) : (real_of_int _69903) = (real_of_int _69903).
Proof. exact (eq_refl (real_of_int _69903)). Qed.
Lemma lem5409062 (_69903 : int) : (term615 _69903) = (term630 _69903).
Proof. exact (MK_COMB (@lem5409060) (@lem5409061 _69903)). Qed.
Lemma lem5409063 (_69903 : int) : (term667 _69903) = (term630 _69903).
Proof. exact (TRANS (@lem5408960 _69903) (@lem5409062 _69903)). Qed.
Lemma lem5409064 (_69903 : int) : (term630 _69903) = term182.
Proof. exact (@lem1982719 (real_of_int _69903)). Qed.
Lemma lem5409065 (_69903 : int) : (term667 _69903) = term182.
Proof. exact (TRANS (@lem5409063 _69903) (@lem5409064 _69903)). Qed.
Lemma lem5409066 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409067 (_69903 : int) : (term668 _69903) = term632.
Proof. exact (MK_COMB (@lem5409066) (@lem5409065 _69903)). Qed.
Lemma lem5409068 (_69904 : int) : (term669 _69904) = (term670 _69904).
Proof. exact (@lem1982753 (real_of_int _69904) (term281 _69904) term193 term350). Qed.
Lemma lem5409069 (_69904 : int) : (term614 _69904) = (term615 _69904).
Proof. exact (@lem1982715 term256 (real_of_int _69904)). Qed.
Lemma lem5409071 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5409072 : term193 = term290.
Proof. exact (@lem5409071 term79). Qed.
Lemma lem5409074 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5409075 : term256 = term257.
Proof. exact (@lem5409074 term79). Qed.
Lemma lem5409076 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409077 : term616 = term617.
Proof. exact (MK_COMB (@lem5409076) (@lem5409075)). Qed.
Lemma lem5409078 : term618 = term619.
Proof. exact (MK_COMB (@lem5409077) (@lem5409072)). Qed.
Lemma lem5409079 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5409081 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409082 : term314 = term315.
Proof. exact (@lem5409081 (NUMERAL 0) term79). Qed.
Lemma lem5409083 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409084 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409085 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409084 h1) (fun h1 : term315 = True => @lem5409083)). Qed.
Lemma lem5409086 : term315 = True.
Proof. exact (EQ_MP (@lem5409085) (@lem5409083)). Qed.
Lemma lem5409087 : term314 = True.
Proof. exact (TRANS (@lem5409082) (@lem5409086)). Qed.
Lemma lem5409088 : True = term314.
Proof. exact (SYM (@lem5409087)). Qed.
Lemma lem5409089 : term314.
Proof. exact (EQ_MP (@lem5409088) (@lem0)). Qed.
Lemma lem5409090 : term621.
Proof. exact (@lem5409079 (@lem5409089)). Qed.
Lemma lem5409092 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409093 : term314 = term315.
Proof. exact (@lem5409092 (NUMERAL 0) term79). Qed.
Lemma lem5409094 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409095 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409096 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409095 h1) (fun h1 : term315 = True => @lem5409094)). Qed.
Lemma lem5409097 : term315 = True.
Proof. exact (EQ_MP (@lem5409096) (@lem5409094)). Qed.
Lemma lem5409098 : term314 = True.
Proof. exact (TRANS (@lem5409093) (@lem5409097)). Qed.
Lemma lem5409099 : True = term314.
Proof. exact (SYM (@lem5409098)). Qed.
Lemma lem5409100 : term314.
Proof. exact (EQ_MP (@lem5409099) (@lem0)). Qed.
Lemma lem5409101 : term622.
Proof. exact (@lem5409090 (@lem5409100)). Qed.
Lemma lem5409103 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409104 : term314 = term315.
Proof. exact (@lem5409103 (NUMERAL 0) term79). Qed.
Lemma lem5409105 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409106 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409107 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409106 h1) (fun h1 : term315 = True => @lem5409105)). Qed.
Lemma lem5409108 : term315 = True.
Proof. exact (EQ_MP (@lem5409107) (@lem5409105)). Qed.
Lemma lem5409109 : term314 = True.
Proof. exact (TRANS (@lem5409104) (@lem5409108)). Qed.
Lemma lem5409110 : True = term314.
Proof. exact (SYM (@lem5409109)). Qed.
Lemma lem5409111 : term314.
Proof. exact (EQ_MP (@lem5409110) (@lem0)). Qed.
Lemma lem5409112 : term623.
Proof. exact (@lem5409101 (@lem5409111)). Qed.
Lemma lem5409114 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5409115 : term265 = term266.
Proof. exact (@lem5409114 term79 term79). Qed.
Lemma lem5409116 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409117 : term268 = term79.
Proof. exact (EQ_MP (@lem5409116) (@lem940073)). Qed.
Lemma lem5409118 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409119 : term266 = term193.
Proof. exact (MK_COMB (@lem5409118) (@lem5409117)). Qed.
Lemma lem5409120 : term265 = term193.
Proof. exact (TRANS (@lem5409115) (@lem5409119)). Qed.
Lemma lem5409122 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5409123 : term291 = term296.
Proof. exact (@lem5409122 term79 term79). Qed.
Lemma lem5409124 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409125 : term268 = term79.
Proof. exact (EQ_MP (@lem5409124) (@lem940073)). Qed.
Lemma lem5409126 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409127 : term266 = term193.
Proof. exact (MK_COMB (@lem5409126) (@lem5409125)). Qed.
Lemma lem5409128 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5409129 : term296 = term256.
Proof. exact (MK_COMB (@lem5409128) (@lem5409127)). Qed.
Lemma lem5409130 : term291 = term256.
Proof. exact (TRANS (@lem5409123) (@lem5409129)). Qed.
Lemma lem5409131 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409132 : term624 = term616.
Proof. exact (MK_COMB (@lem5409131) (@lem5409130)). Qed.
Lemma lem5409133 : term625 = term618.
Proof. exact (MK_COMB (@lem5409132) (@lem5409120)). Qed.
Lemma lem5409135 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5409136 : term618 = term182.
Proof. exact (@lem5409135 term79). Qed.
Lemma lem5409137 : term625 = term182.
Proof. exact (TRANS (@lem5409133) (@lem5409136)). Qed.
Lemma lem5409138 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5409139 : term627 = term403.
Proof. exact (MK_COMB (@lem5409138) (@lem5409137)). Qed.
Lemma lem5409140 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5409141 : term628 = term405.
Proof. exact (MK_COMB (@lem5409139) (@lem5409140)). Qed.
Lemma lem5409143 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5409144 : term405 = term182.
Proof. exact (@lem5409143 term79). Qed.
Lemma lem5409145 : term628 = term182.
Proof. exact (TRANS (@lem5409141) (@lem5409144)). Qed.
Lemma lem5409147 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5409148 : term265 = term266.
Proof. exact (@lem5409147 term79 term79). Qed.
Lemma lem5409149 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409150 : term268 = term79.
Proof. exact (EQ_MP (@lem5409149) (@lem940073)). Qed.
Lemma lem5409151 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409152 : term266 = term193.
Proof. exact (MK_COMB (@lem5409151) (@lem5409150)). Qed.
Lemma lem5409153 : term265 = term193.
Proof. exact (TRANS (@lem5409148) (@lem5409152)). Qed.
Lemma lem5409154 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5409155 : term407 = term405.
Proof. exact (MK_COMB (@lem5409154) (@lem5409153)). Qed.
Lemma lem5409157 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5409158 : term405 = term182.
Proof. exact (@lem5409157 term79). Qed.
Lemma lem5409159 : term407 = term182.
Proof. exact (TRANS (@lem5409155) (@lem5409158)). Qed.
Lemma lem5409160 : term182 = term407.
Proof. exact (SYM (@lem5409159)). Qed.
Lemma lem5409161 : term628 = term407.
Proof. exact (TRANS (@lem5409145) (@lem5409160)). Qed.
Lemma lem5409162 : term619 = term253.
Proof. exact (@lem5409112 (@lem5409161)). Qed.
Lemma lem5409163 : term618 = term253.
Proof. exact (TRANS (@lem5409078) (@lem5409162)). Qed.
Lemma lem5409165 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5409166 : term253 = term182.
Proof. exact (@lem5409165 term182). Qed.
Lemma lem5409167 : term618 = term182.
Proof. exact (TRANS (@lem5409163) (@lem5409166)). Qed.
Lemma lem5409168 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5409169 : term629 = term403.
Proof. exact (MK_COMB (@lem5409168) (@lem5409167)). Qed.
Lemma lem5409170 (_69904 : int) : (real_of_int _69904) = (real_of_int _69904).
Proof. exact (eq_refl (real_of_int _69904)). Qed.
Lemma lem5409171 (_69904 : int) : (term615 _69904) = (term630 _69904).
Proof. exact (MK_COMB (@lem5409169) (@lem5409170 _69904)). Qed.
Lemma lem5409172 (_69904 : int) : (term614 _69904) = (term630 _69904).
Proof. exact (TRANS (@lem5409069 _69904) (@lem5409171 _69904)). Qed.
Lemma lem5409173 (_69904 : int) : (term630 _69904) = term182.
Proof. exact (@lem1982719 (real_of_int _69904)). Qed.
Lemma lem5409174 (_69904 : int) : (term614 _69904) = term182.
Proof. exact (TRANS (@lem5409172 _69904) (@lem5409173 _69904)). Qed.
Lemma lem5409175 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409176 (_69904 : int) : (term631 _69904) = term632.
Proof. exact (MK_COMB (@lem5409175) (@lem5409174 _69904)). Qed.
Lemma lem5409178 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5409179 : term350 = term353.
Proof. exact (@lem5409178 term326). Qed.
Lemma lem5409181 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5409182 : term193 = term290.
Proof. exact (@lem5409181 term79). Qed.
Lemma lem5409183 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409184 : term307 = term308.
Proof. exact (MK_COMB (@lem5409183) (@lem5409182)). Qed.
Lemma lem5409185 : term671 = term672.
Proof. exact (MK_COMB (@lem5409184) (@lem5409179)). Qed.
Lemma lem5409186 : term673.
Proof. exact (@lem1981473 term193 term193 term350 term193 term256 term193). Qed.
Lemma lem5409188 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409189 : term314 = term315.
Proof. exact (@lem5409188 (NUMERAL 0) term79). Qed.
Lemma lem5409190 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409191 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409192 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409191 h1) (fun h1 : term315 = True => @lem5409190)). Qed.
Lemma lem5409193 : term315 = True.
Proof. exact (EQ_MP (@lem5409192) (@lem5409190)). Qed.
Lemma lem5409194 : term314 = True.
Proof. exact (TRANS (@lem5409189) (@lem5409193)). Qed.
Lemma lem5409195 : True = term314.
Proof. exact (SYM (@lem5409194)). Qed.
Lemma lem5409196 : term314.
Proof. exact (EQ_MP (@lem5409195) (@lem0)). Qed.
Lemma lem5409197 : term674.
Proof. exact (@lem5409186 (@lem5409196)). Qed.
Lemma lem5409199 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409200 : term314 = term315.
Proof. exact (@lem5409199 (NUMERAL 0) term79). Qed.
Lemma lem5409201 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409202 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409203 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409202 h1) (fun h1 : term315 = True => @lem5409201)). Qed.
Lemma lem5409204 : term315 = True.
Proof. exact (EQ_MP (@lem5409203) (@lem5409201)). Qed.
Lemma lem5409205 : term314 = True.
Proof. exact (TRANS (@lem5409200) (@lem5409204)). Qed.
Lemma lem5409206 : True = term314.
Proof. exact (SYM (@lem5409205)). Qed.
Lemma lem5409207 : term314.
Proof. exact (EQ_MP (@lem5409206) (@lem0)). Qed.
Lemma lem5409208 : term675.
Proof. exact (@lem5409197 (@lem5409207)). Qed.
Lemma lem5409210 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409211 : term314 = term315.
Proof. exact (@lem5409210 (NUMERAL 0) term79). Qed.
Lemma lem5409212 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409213 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409214 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409213 h1) (fun h1 : term315 = True => @lem5409212)). Qed.
Lemma lem5409215 : term315 = True.
Proof. exact (EQ_MP (@lem5409214) (@lem5409212)). Qed.
Lemma lem5409216 : term314 = True.
Proof. exact (TRANS (@lem5409211) (@lem5409215)). Qed.
Lemma lem5409217 : True = term314.
Proof. exact (SYM (@lem5409216)). Qed.
Lemma lem5409218 : term314.
Proof. exact (EQ_MP (@lem5409217) (@lem0)). Qed.
Lemma lem5409219 : term676.
Proof. exact (@lem5409208 (@lem5409218)). Qed.
Lemma lem5409221 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5409222 : term644 = term645.
Proof. exact (@lem5409221 term326 term79). Qed.
Lemma lem5409223 : term332 = term324.
Proof. exact (@lem996237 term324). Qed.
Lemma lem5409224 : (term332 = term324) = (term333 = term326).
Proof. exact (@lem1007663 term324 (BIT1 0) term324). Qed.
Lemma lem5409225 : term333 = term326.
Proof. exact (EQ_MP (@lem5409224) (@lem5409223)). Qed.
Lemma lem5409226 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409227 : term331 = term312.
Proof. exact (MK_COMB (@lem5409226) (@lem5409225)). Qed.
Lemma lem5409228 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5409229 : term645 = term350.
Proof. exact (MK_COMB (@lem5409228) (@lem5409227)). Qed.
Lemma lem5409230 : term644 = term350.
Proof. exact (TRANS (@lem5409222) (@lem5409229)). Qed.
Lemma lem5409232 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5409233 : term265 = term266.
Proof. exact (@lem5409232 term79 term79). Qed.
Lemma lem5409234 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409235 : term268 = term79.
Proof. exact (EQ_MP (@lem5409234) (@lem940073)). Qed.
Lemma lem5409236 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409237 : term266 = term193.
Proof. exact (MK_COMB (@lem5409236) (@lem5409235)). Qed.
Lemma lem5409238 : term265 = term193.
Proof. exact (TRANS (@lem5409233) (@lem5409237)). Qed.
Lemma lem5409239 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409240 : term320 = term307.
Proof. exact (MK_COMB (@lem5409239) (@lem5409238)). Qed.
Lemma lem5409241 : term677 = term671.
Proof. exact (MK_COMB (@lem5409240) (@lem5409230)). Qed.
Lemma lem5409244 : term678 = term256.
Proof. exact (@lem1367771 term79 term79). Qed.
Lemma lem5409245 : term323 = term324.
Proof. exact (@lem706885). Qed.
Lemma lem5409246 : (term323 = term324) = (term325 = term326).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term324). Qed.
Lemma lem5409247 : term325 = term326.
Proof. exact (EQ_MP (@lem5409246) (@lem5409245)). Qed.
Lemma lem5409248 : term326 = term325.
Proof. exact (SYM (@lem5409247)). Qed.
Lemma lem5409249 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409250 : term312 = term322.
Proof. exact (MK_COMB (@lem5409249) (@lem5409248)). Qed.
Lemma lem5409251 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5409252 : term350 = term640.
Proof. exact (MK_COMB (@lem5409251) (@lem5409250)). Qed.
Lemma lem5409253 : term307 = term307.
Proof. exact (eq_refl term307). Qed.
Lemma lem5409254 : term671 = term678.
Proof. exact (MK_COMB (@lem5409253) (@lem5409252)). Qed.
Lemma lem5409255 : term671 = term256.
Proof. exact (TRANS (@lem5409254) (@lem5409244)). Qed.
Lemma lem5409256 : term677 = term256.
Proof. exact (TRANS (@lem5409241) (@lem5409255)). Qed.
Lemma lem5409257 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5409258 : term679 = term258.
Proof. exact (MK_COMB (@lem5409257) (@lem5409256)). Qed.
Lemma lem5409259 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5409260 : term680 = term291.
Proof. exact (MK_COMB (@lem5409258) (@lem5409259)). Qed.
Lemma lem5409262 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5409263 : term291 = term296.
Proof. exact (@lem5409262 term79 term79). Qed.
Lemma lem5409264 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409265 : term268 = term79.
Proof. exact (EQ_MP (@lem5409264) (@lem940073)). Qed.
Lemma lem5409266 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409267 : term266 = term193.
Proof. exact (MK_COMB (@lem5409266) (@lem5409265)). Qed.
Lemma lem5409268 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5409269 : term296 = term256.
Proof. exact (MK_COMB (@lem5409268) (@lem5409267)). Qed.
Lemma lem5409270 : term291 = term256.
Proof. exact (TRANS (@lem5409263) (@lem5409269)). Qed.
Lemma lem5409271 : term680 = term256.
Proof. exact (TRANS (@lem5409260) (@lem5409270)). Qed.
Lemma lem5409273 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5409274 : term265 = term266.
Proof. exact (@lem5409273 term79 term79). Qed.
Lemma lem5409275 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409276 : term268 = term79.
Proof. exact (EQ_MP (@lem5409275) (@lem940073)). Qed.
Lemma lem5409277 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409278 : term266 = term193.
Proof. exact (MK_COMB (@lem5409277) (@lem5409276)). Qed.
Lemma lem5409279 : term265 = term193.
Proof. exact (TRANS (@lem5409274) (@lem5409278)). Qed.
Lemma lem5409280 : term258 = term258.
Proof. exact (eq_refl term258). Qed.
Lemma lem5409281 : term681 = term291.
Proof. exact (MK_COMB (@lem5409280) (@lem5409279)). Qed.
Lemma lem5409283 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5409284 : term291 = term296.
Proof. exact (@lem5409283 term79 term79). Qed.
Lemma lem5409285 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409286 : term268 = term79.
Proof. exact (EQ_MP (@lem5409285) (@lem940073)). Qed.
Lemma lem5409287 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409288 : term266 = term193.
Proof. exact (MK_COMB (@lem5409287) (@lem5409286)). Qed.
Lemma lem5409289 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5409290 : term296 = term256.
Proof. exact (MK_COMB (@lem5409289) (@lem5409288)). Qed.
Lemma lem5409291 : term291 = term256.
Proof. exact (TRANS (@lem5409284) (@lem5409290)). Qed.
Lemma lem5409292 : term681 = term256.
Proof. exact (TRANS (@lem5409281) (@lem5409291)). Qed.
Lemma lem5409293 : term256 = term681.
Proof. exact (SYM (@lem5409292)). Qed.
Lemma lem5409294 : term680 = term681.
Proof. exact (TRANS (@lem5409271) (@lem5409293)). Qed.
Lemma lem5409295 : term672 = term257.
Proof. exact (@lem5409219 (@lem5409294)). Qed.
Lemma lem5409296 : term671 = term257.
Proof. exact (TRANS (@lem5409185) (@lem5409295)). Qed.
Lemma lem5409298 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5409299 : term257 = term256.
Proof. exact (@lem5409298 term256). Qed.
Lemma lem5409300 : term671 = term256.
Proof. exact (TRANS (@lem5409296) (@lem5409299)). Qed.
Lemma lem5409301 (_69904 : int) : (term670 _69904) = term682.
Proof. exact (MK_COMB (@lem5409176 _69904) (@lem5409300)). Qed.
Lemma lem5409302 (_69904 : int) : (term669 _69904) = term682.
Proof. exact (TRANS (@lem5409068 _69904) (@lem5409301 _69904)). Qed.
Lemma lem5409303 : term682 = term256.
Proof. exact (@lem1982721 term256). Qed.
Lemma lem5409304 (_69904 : int) : (term669 _69904) = term256.
Proof. exact (TRANS (@lem5409302 _69904) (@lem5409303)). Qed.
Lemma lem5409305 (_69903 : int) (_69904 : int) : (term666 _69903 _69904) = term682.
Proof. exact (MK_COMB (@lem5409067 _69903) (@lem5409304 _69904)). Qed.
Lemma lem5409306 (_69903 : int) (_69904 : int) : (term665 _69903 _69904) = term682.
Proof. exact (TRANS (@lem5408959 _69903 _69904) (@lem5409305 _69903 _69904)). Qed.
Lemma lem5409307 : term682 = term256.
Proof. exact (@lem1982721 term256). Qed.
Lemma lem5409308 (_69903 : int) (_69904 : int) : (term665 _69903 _69904) = term256.
Proof. exact (TRANS (@lem5409306 _69903 _69904) (@lem5409307)). Qed.
Lemma lem5409309 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5409310 (_69903 : int) (_69904 : int) : (term683 _69903 _69904) = term684.
Proof. exact (MK_COMB (@lem5409309) (@lem5409308 _69903 _69904)). Qed.
Lemma lem5409311 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5409312 (_69903 : int) (_69904 : int) : (term664 _69903 _69904) = term685.
Proof. exact (MK_COMB (@lem5409310 _69903 _69904) (@lem5409311)). Qed.
Lemma lem5409313 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : term685.
Proof. exact (EQ_MP (@lem5409312 _69903 _69904) (@lem5408958 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409315 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5409316 : term685 = term686.
Proof. exact (@lem5409315 term182 term256). Qed.
Lemma lem5409318 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5409319 : term256 = term257.
Proof. exact (@lem5409318 term79). Qed.
Lemma lem5409321 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5409322 : term182 = term253.
Proof. exact (@lem5409321 (NUMERAL 0)). Qed.
Lemma lem5409323 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5409324 : term184 = term687.
Proof. exact (MK_COMB (@lem5409323) (@lem5409322)). Qed.
Lemma lem5409325 : term686 = term688.
Proof. exact (MK_COMB (@lem5409324) (@lem5409319)). Qed.
Lemma lem5409326 : term689.
Proof. exact (@lem1980026 term182 term193 term256 term193). Qed.
Lemma lem5409328 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409329 : term314 = term315.
Proof. exact (@lem5409328 (NUMERAL 0) term79). Qed.
Lemma lem5409330 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409331 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409332 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409331 h1) (fun h1 : term315 = True => @lem5409330)). Qed.
Lemma lem5409333 : term315 = True.
Proof. exact (EQ_MP (@lem5409332) (@lem5409330)). Qed.
Lemma lem5409334 : term314 = True.
Proof. exact (TRANS (@lem5409329) (@lem5409333)). Qed.
Lemma lem5409335 : True = term314.
Proof. exact (SYM (@lem5409334)). Qed.
Lemma lem5409336 : term314.
Proof. exact (EQ_MP (@lem5409335) (@lem0)). Qed.
Lemma lem5409337 : term690.
Proof. exact (@lem5409326 (@lem5409336)). Qed.
Lemma lem5409339 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409340 : term314 = term315.
Proof. exact (@lem5409339 (NUMERAL 0) term79). Qed.
Lemma lem5409341 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409342 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409343 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409342 h1) (fun h1 : term315 = True => @lem5409341)). Qed.
Lemma lem5409344 : term315 = True.
Proof. exact (EQ_MP (@lem5409343) (@lem5409341)). Qed.
Lemma lem5409345 : term314 = True.
Proof. exact (TRANS (@lem5409340) (@lem5409344)). Qed.
Lemma lem5409346 : True = term314.
Proof. exact (SYM (@lem5409345)). Qed.
Lemma lem5409347 : term314.
Proof. exact (EQ_MP (@lem5409346) (@lem0)). Qed.
Lemma lem5409348 : term688 = term691.
Proof. exact (@lem5409337 (@lem5409347)). Qed.
Lemma lem5409350 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5409351 : term291 = term296.
Proof. exact (@lem5409350 term79 term79). Qed.
Lemma lem5409352 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409353 : term268 = term79.
Proof. exact (EQ_MP (@lem5409352) (@lem940073)). Qed.
Lemma lem5409354 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409355 : term266 = term193.
Proof. exact (MK_COMB (@lem5409354) (@lem5409353)). Qed.
Lemma lem5409356 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5409357 : term296 = term256.
Proof. exact (MK_COMB (@lem5409356) (@lem5409355)). Qed.
Lemma lem5409358 : term291 = term256.
Proof. exact (TRANS (@lem5409351) (@lem5409357)). Qed.
Lemma lem5409360 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5409361 : term405 = term182.
Proof. exact (@lem5409360 term79). Qed.
Lemma lem5409362 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5409363 : term692 = term184.
Proof. exact (MK_COMB (@lem5409362) (@lem5409361)). Qed.
Lemma lem5409364 : term691 = term686.
Proof. exact (MK_COMB (@lem5409363) (@lem5409358)). Qed.
Lemma lem5409366 (m : nat) (n : nat) : (term693 m n) = (term694 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5409367 : term686 = term695.
Proof. exact (@lem5409366 (NUMERAL 0) term79). Qed.
Lemma lem5409368 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409369 (h1 : term316 = (BIT1 0)) : (term79 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5409370 : (term316 = (BIT1 0)) = ((term79 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409369 h1) (fun h1 : (term79 = (NUMERAL 0)) = False => @lem5409368)). Qed.
Lemma lem5409371 : (term79 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5409370) (@lem5409368)). Qed.
Lemma lem5409372 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5409373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5409374 : term696 = (and True).
Proof. exact (MK_COMB (@lem5409373) (@lem5409372)). Qed.
Lemma lem5409375 : term695 = (True /\ False).
Proof. exact (MK_COMB (@lem5409374) (@lem5409371)). Qed.
Lemma lem5409377 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5409378 : term695 = False.
Proof. exact (TRANS (@lem5409375) (@lem5409377)). Qed.
Lemma lem5409379 : term686 = False.
Proof. exact (TRANS (@lem5409367) (@lem5409378)). Qed.
Lemma lem5409380 : term691 = False.
Proof. exact (TRANS (@lem5409364) (@lem5409379)). Qed.
Lemma lem5409381 : term688 = False.
Proof. exact (TRANS (@lem5409348) (@lem5409380)). Qed.
Lemma lem5409382 : term686 = False.
Proof. exact (TRANS (@lem5409325) (@lem5409381)). Qed.
Lemma lem5409383 : term685 = False.
Proof. exact (TRANS (@lem5409316) (@lem5409382)). Qed.
Lemma lem5409384 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term582 _69903 _69904 _69905) : False.
Proof. exact (EQ_MP (@lem5409383) (@lem5409313 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409385 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : term697 _69903 _69904 _69905.
Proof. exact (h1). Qed.
Lemma lem5409386 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : term575 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5409385 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409388 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : term544 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5409386 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409390 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : term513 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5409388 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409392 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : term482 _69904 _69905.
Proof. exact (proj2 (@lem5409390 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409394 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : (term362 _69904 _69905) = term182.
Proof. exact (proj2 (@lem5409392 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409395 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : term359 _69904 _69905.
Proof. exact (proj1 (@lem5409392 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409397 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5409398 : term583 = term314.
Proof. exact (@lem5409397 term182 term193). Qed.
Lemma lem5409400 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5409401 : term193 = term290.
Proof. exact (@lem5409400 term79). Qed.
Lemma lem5409403 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5409404 : term182 = term253.
Proof. exact (@lem5409403 (NUMERAL 0)). Qed.
Lemma lem5409405 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5409406 : term584 = term585.
Proof. exact (MK_COMB (@lem5409405) (@lem5409404)). Qed.
Lemma lem5409407 : term314 = term586.
Proof. exact (MK_COMB (@lem5409406) (@lem5409401)). Qed.
Lemma lem5409408 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5409410 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409411 : term314 = term315.
Proof. exact (@lem5409410 (NUMERAL 0) term79). Qed.
Lemma lem5409412 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409413 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409414 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409413 h1) (fun h1 : term315 = True => @lem5409412)). Qed.
Lemma lem5409415 : term315 = True.
Proof. exact (EQ_MP (@lem5409414) (@lem5409412)). Qed.
Lemma lem5409416 : term314 = True.
Proof. exact (TRANS (@lem5409411) (@lem5409415)). Qed.
Lemma lem5409417 : True = term314.
Proof. exact (SYM (@lem5409416)). Qed.
Lemma lem5409418 : term314.
Proof. exact (EQ_MP (@lem5409417) (@lem0)). Qed.
Lemma lem5409419 : term588.
Proof. exact (@lem5409408 (@lem5409418)). Qed.
Lemma lem5409421 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409422 : term314 = term315.
Proof. exact (@lem5409421 (NUMERAL 0) term79). Qed.
Lemma lem5409423 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409424 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409425 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409424 h1) (fun h1 : term315 = True => @lem5409423)). Qed.
Lemma lem5409426 : term315 = True.
Proof. exact (EQ_MP (@lem5409425) (@lem5409423)). Qed.
Lemma lem5409427 : term314 = True.
Proof. exact (TRANS (@lem5409422) (@lem5409426)). Qed.
Lemma lem5409428 : True = term314.
Proof. exact (SYM (@lem5409427)). Qed.
Lemma lem5409429 : term314.
Proof. exact (EQ_MP (@lem5409428) (@lem0)). Qed.
Lemma lem5409430 : term586 = term589.
Proof. exact (@lem5409419 (@lem5409429)). Qed.
Lemma lem5409432 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5409433 : term265 = term266.
Proof. exact (@lem5409432 term79 term79). Qed.
Lemma lem5409434 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409435 : term268 = term79.
Proof. exact (EQ_MP (@lem5409434) (@lem940073)). Qed.
Lemma lem5409436 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409437 : term266 = term193.
Proof. exact (MK_COMB (@lem5409436) (@lem5409435)). Qed.
Lemma lem5409438 : term265 = term193.
Proof. exact (TRANS (@lem5409433) (@lem5409437)). Qed.
Lemma lem5409440 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5409441 : term405 = term182.
Proof. exact (@lem5409440 term79). Qed.
Lemma lem5409442 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5409443 : term590 = term584.
Proof. exact (MK_COMB (@lem5409442) (@lem5409441)). Qed.
Lemma lem5409444 : term589 = term314.
Proof. exact (MK_COMB (@lem5409443) (@lem5409438)). Qed.
Lemma lem5409446 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409447 : term314 = term315.
Proof. exact (@lem5409446 (NUMERAL 0) term79). Qed.
Lemma lem5409448 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409449 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409450 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409449 h1) (fun h1 : term315 = True => @lem5409448)). Qed.
Lemma lem5409451 : term315 = True.
Proof. exact (EQ_MP (@lem5409450) (@lem5409448)). Qed.
Lemma lem5409452 : term314 = True.
Proof. exact (TRANS (@lem5409447) (@lem5409451)). Qed.
Lemma lem5409453 : term589 = True.
Proof. exact (TRANS (@lem5409444) (@lem5409452)). Qed.
Lemma lem5409454 : term586 = True.
Proof. exact (TRANS (@lem5409430) (@lem5409453)). Qed.
Lemma lem5409455 : term314 = True.
Proof. exact (TRANS (@lem5409407) (@lem5409454)). Qed.
Lemma lem5409456 : term583 = True.
Proof. exact (TRANS (@lem5409398) (@lem5409455)). Qed.
Lemma lem5409457 : True = term583.
Proof. exact (SYM (@lem5409456)). Qed.
Lemma lem5409458 : term583.
Proof. exact (EQ_MP (@lem5409457) (@lem0)). Qed.
Lemma lem5409459 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : term698 _69904 _69905.
Proof. exact (conj (@lem5409458) (@lem5409395 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409461 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5409462 (_69904 : int) (_69905 : int) : term699 _69904 _69905.
Proof. exact (@lem5409461 term193 (term356 _69904 _69905)). Qed.
Lemma lem5409463 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : term700 _69904 _69905.
Proof. exact (@lem5409462 _69904 _69905 (@lem5409459 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409464 (_69904 : int) (_69905 : int) : (term701 _69904 _69905) = (term356 _69904 _69905).
Proof. exact (@lem1982733 (term356 _69904 _69905)). Qed.
Lemma lem5409465 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5409466 (_69904 : int) (_69905 : int) : (term702 _69904 _69905) = (term358 _69904 _69905).
Proof. exact (MK_COMB (@lem5409465) (@lem5409464 _69904 _69905)). Qed.
Lemma lem5409467 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5409468 (_69904 : int) (_69905 : int) : (term700 _69904 _69905) = (term359 _69904 _69905).
Proof. exact (MK_COMB (@lem5409466 _69904 _69905) (@lem5409467)). Qed.
Lemma lem5409469 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : term359 _69904 _69905.
Proof. exact (EQ_MP (@lem5409468 _69904 _69905) (@lem5409463 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409471 (y : real) : term597 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5409472 (_69904 : int) (_69905 : int) : term598 _69904 _69905.
Proof. exact (@lem5409471 (term362 _69904 _69905)). Qed.
Lemma lem5409473 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : term599 _69904 _69905.
Proof. exact (@lem5409472 _69904 _69905 (@lem5409394 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409474 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : term703 _69904 _69905.
Proof. exact (@lem5409473 _69903 _69904 _69905 h1 term256). Qed.
Lemma lem5409475 (_69904 : int) (_69905 : int) : (term703 _69904 _69905) = ((term704 _69904 _69905) = term182).
Proof. exact (eq_refl (term703 _69904 _69905)). Qed.
Lemma lem5409476 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : (term704 _69904 _69905) = term182.
Proof. exact (EQ_MP (@lem5409475 _69904 _69905) (@lem5409474 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409477 (_69904 : int) (_69905 : int) : (term704 _69904 _69905) = (term705 _69904 _69905).
Proof. exact (@lem1982781 (term281 _69904) term256 (term611 _69905)). Qed.
Lemma lem5409478 (_69905 : int) : (term706 _69905) = (term707 _69905).
Proof. exact (@lem1982781 (real_of_int _69905) term256 term256). Qed.
Lemma lem5409480 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5409481 : term256 = term257.
Proof. exact (@lem5409480 term79). Qed.
Lemma lem5409483 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5409484 : term256 = term257.
Proof. exact (@lem5409483 term79). Qed.
Lemma lem5409485 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5409486 : term258 = term259.
Proof. exact (MK_COMB (@lem5409485) (@lem5409484)). Qed.
Lemma lem5409487 : term708 = term709.
Proof. exact (MK_COMB (@lem5409486) (@lem5409481)). Qed.
Lemma lem5409488 : term709 = term710.
Proof. exact (@lem1981613 term256 term256 term193 term193). Qed.
Lemma lem5409490 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5409491 : term265 = term266.
Proof. exact (@lem5409490 term79 term79). Qed.
Lemma lem5409492 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409493 : term268 = term79.
Proof. exact (EQ_MP (@lem5409492) (@lem940073)). Qed.
Lemma lem5409494 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409495 : term266 = term193.
Proof. exact (MK_COMB (@lem5409494) (@lem5409493)). Qed.
Lemma lem5409496 : term265 = term193.
Proof. exact (TRANS (@lem5409491) (@lem5409495)). Qed.
Lemma lem5409498 (m : nat) (n : nat) : (term711 m n) = (term264 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5409499 : term708 = term266.
Proof. exact (@lem5409498 term79 term79). Qed.
Lemma lem5409500 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409501 : term268 = term79.
Proof. exact (EQ_MP (@lem5409500) (@lem940073)). Qed.
Lemma lem5409502 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409503 : term266 = term193.
Proof. exact (MK_COMB (@lem5409502) (@lem5409501)). Qed.
Lemma lem5409504 : term708 = term193.
Proof. exact (TRANS (@lem5409499) (@lem5409503)). Qed.
Lemma lem5409505 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5409506 : term712 = term713.
Proof. exact (MK_COMB (@lem5409505) (@lem5409504)). Qed.
Lemma lem5409507 : term710 = term290.
Proof. exact (MK_COMB (@lem5409506) (@lem5409496)). Qed.
Lemma lem5409508 : term709 = term290.
Proof. exact (TRANS (@lem5409488) (@lem5409507)). Qed.
Lemma lem5409509 : term708 = term290.
Proof. exact (TRANS (@lem5409487) (@lem5409508)). Qed.
Lemma lem5409511 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5409512 : term290 = term193.
Proof. exact (@lem5409511 term193). Qed.
Lemma lem5409513 : term708 = term193.
Proof. exact (TRANS (@lem5409509) (@lem5409512)). Qed.
Lemma lem5409516 (_69905 : int) : (term299 _69905) = (term299 _69905).
Proof. exact (eq_refl (term299 _69905)). Qed.
Lemma lem5409517 (_69905 : int) : (term707 _69905) = (term382 _69905).
Proof. exact (MK_COMB (@lem5409516 _69905) (@lem5409513)). Qed.
Lemma lem5409518 (_69905 : int) : (term706 _69905) = (term382 _69905).
Proof. exact (TRANS (@lem5409478 _69905) (@lem5409517 _69905)). Qed.
Lemma lem5409519 (_69904 : int) : (term714 _69904) = (term715 _69904).
Proof. exact (@lem1982749 term256 term256 (real_of_int _69904)). Qed.
Lemma lem5409521 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5409522 : term256 = term257.
Proof. exact (@lem5409521 term79). Qed.
Lemma lem5409524 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5409525 : term256 = term257.
Proof. exact (@lem5409524 term79). Qed.
Lemma lem5409526 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5409527 : term258 = term259.
Proof. exact (MK_COMB (@lem5409526) (@lem5409525)). Qed.
Lemma lem5409528 : term708 = term709.
Proof. exact (MK_COMB (@lem5409527) (@lem5409522)). Qed.
Lemma lem5409529 : term709 = term710.
Proof. exact (@lem1981613 term256 term256 term193 term193). Qed.
Lemma lem5409531 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5409532 : term265 = term266.
Proof. exact (@lem5409531 term79 term79). Qed.
Lemma lem5409533 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409534 : term268 = term79.
Proof. exact (EQ_MP (@lem5409533) (@lem940073)). Qed.
Lemma lem5409535 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409536 : term266 = term193.
Proof. exact (MK_COMB (@lem5409535) (@lem5409534)). Qed.
Lemma lem5409537 : term265 = term193.
Proof. exact (TRANS (@lem5409532) (@lem5409536)). Qed.
Lemma lem5409539 (m : nat) (n : nat) : (term711 m n) = (term264 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5409540 : term708 = term266.
Proof. exact (@lem5409539 term79 term79). Qed.
Lemma lem5409541 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409542 : term268 = term79.
Proof. exact (EQ_MP (@lem5409541) (@lem940073)). Qed.
Lemma lem5409543 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409544 : term266 = term193.
Proof. exact (MK_COMB (@lem5409543) (@lem5409542)). Qed.
Lemma lem5409545 : term708 = term193.
Proof. exact (TRANS (@lem5409540) (@lem5409544)). Qed.
Lemma lem5409546 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5409547 : term712 = term713.
Proof. exact (MK_COMB (@lem5409546) (@lem5409545)). Qed.
Lemma lem5409548 : term710 = term290.
Proof. exact (MK_COMB (@lem5409547) (@lem5409537)). Qed.
Lemma lem5409549 : term709 = term290.
Proof. exact (TRANS (@lem5409529) (@lem5409548)). Qed.
Lemma lem5409550 : term708 = term290.
Proof. exact (TRANS (@lem5409528) (@lem5409549)). Qed.
Lemma lem5409552 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5409553 : term290 = term193.
Proof. exact (@lem5409552 term193). Qed.
Lemma lem5409554 : term708 = term193.
Proof. exact (TRANS (@lem5409550) (@lem5409553)). Qed.
Lemma lem5409555 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5409556 : term716 = term717.
Proof. exact (MK_COMB (@lem5409555) (@lem5409554)). Qed.
Lemma lem5409557 (_69904 : int) : (real_of_int _69904) = (real_of_int _69904).
Proof. exact (eq_refl (real_of_int _69904)). Qed.
Lemma lem5409558 (_69904 : int) : (term715 _69904) = (term718 _69904).
Proof. exact (MK_COMB (@lem5409556) (@lem5409557 _69904)). Qed.
Lemma lem5409559 (_69904 : int) : (term714 _69904) = (term718 _69904).
Proof. exact (TRANS (@lem5409519 _69904) (@lem5409558 _69904)). Qed.
Lemma lem5409560 (_69904 : int) : (term718 _69904) = (real_of_int _69904).
Proof. exact (@lem1982709 (real_of_int _69904)). Qed.
Lemma lem5409561 (_69904 : int) : (term714 _69904) = (real_of_int _69904).
Proof. exact (TRANS (@lem5409559 _69904) (@lem5409560 _69904)). Qed.
Lemma lem5409562 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409563 (_69904 : int) : (term719 _69904) = (term194 _69904).
Proof. exact (MK_COMB (@lem5409562) (@lem5409561 _69904)). Qed.
Lemma lem5409564 (_69904 : int) (_69905 : int) : (term705 _69904 _69905) = (term383 _69904 _69905).
Proof. exact (MK_COMB (@lem5409563 _69904) (@lem5409518 _69905)). Qed.
Lemma lem5409565 (_69904 : int) (_69905 : int) : (term704 _69904 _69905) = (term383 _69904 _69905).
Proof. exact (TRANS (@lem5409477 _69904 _69905) (@lem5409564 _69904 _69905)). Qed.
Lemma lem5409566 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5409567 (_69904 : int) (_69905 : int) : (term720 _69904 _69905) = (term721 _69904 _69905).
Proof. exact (MK_COMB (@lem5409566) (@lem5409565 _69904 _69905)). Qed.
Lemma lem5409568 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5409569 (_69904 : int) (_69905 : int) : ((term704 _69904 _69905) = term182) = ((term383 _69904 _69905) = term182).
Proof. exact (MK_COMB (@lem5409567 _69904 _69905) (@lem5409568)). Qed.
Lemma lem5409570 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : (term383 _69904 _69905) = term182.
Proof. exact (EQ_MP (@lem5409569 _69904 _69905) (@lem5409476 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409571 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : term722 _69904 _69905.
Proof. exact (conj (@lem5409570 _69903 _69904 _69905 h1) (@lem5409469 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409573 (x : real) (y : real) : term604 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5409574 (_69904 : int) (_69905 : int) : term723 _69904 _69905.
Proof. exact (@lem5409573 (term383 _69904 _69905) (term356 _69904 _69905)). Qed.
Lemma lem5409575 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : term724 _69904 _69905.
Proof. exact (@lem5409574 _69904 _69905 (@lem5409571 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409576 (_69904 : int) (_69905 : int) : (term725 _69904 _69905) = (term726 _69904 _69905).
Proof. exact (@lem1982753 (real_of_int _69904) (term281 _69904) (term382 _69905) (term727 _69905)). Qed.
Lemma lem5409577 (_69904 : int) : (term614 _69904) = (term615 _69904).
Proof. exact (@lem1982715 term256 (real_of_int _69904)). Qed.
Lemma lem5409579 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5409580 : term193 = term290.
Proof. exact (@lem5409579 term79). Qed.
Lemma lem5409582 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5409583 : term256 = term257.
Proof. exact (@lem5409582 term79). Qed.
Lemma lem5409584 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409585 : term616 = term617.
Proof. exact (MK_COMB (@lem5409584) (@lem5409583)). Qed.
Lemma lem5409586 : term618 = term619.
Proof. exact (MK_COMB (@lem5409585) (@lem5409580)). Qed.
Lemma lem5409587 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5409589 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409590 : term314 = term315.
Proof. exact (@lem5409589 (NUMERAL 0) term79). Qed.
Lemma lem5409591 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409592 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409593 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409592 h1) (fun h1 : term315 = True => @lem5409591)). Qed.
Lemma lem5409594 : term315 = True.
Proof. exact (EQ_MP (@lem5409593) (@lem5409591)). Qed.
Lemma lem5409595 : term314 = True.
Proof. exact (TRANS (@lem5409590) (@lem5409594)). Qed.
Lemma lem5409596 : True = term314.
Proof. exact (SYM (@lem5409595)). Qed.
Lemma lem5409597 : term314.
Proof. exact (EQ_MP (@lem5409596) (@lem0)). Qed.
Lemma lem5409598 : term621.
Proof. exact (@lem5409587 (@lem5409597)). Qed.
Lemma lem5409600 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409601 : term314 = term315.
Proof. exact (@lem5409600 (NUMERAL 0) term79). Qed.
Lemma lem5409602 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409603 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409604 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409603 h1) (fun h1 : term315 = True => @lem5409602)). Qed.
Lemma lem5409605 : term315 = True.
Proof. exact (EQ_MP (@lem5409604) (@lem5409602)). Qed.
Lemma lem5409606 : term314 = True.
Proof. exact (TRANS (@lem5409601) (@lem5409605)). Qed.
Lemma lem5409607 : True = term314.
Proof. exact (SYM (@lem5409606)). Qed.
Lemma lem5409608 : term314.
Proof. exact (EQ_MP (@lem5409607) (@lem0)). Qed.
Lemma lem5409609 : term622.
Proof. exact (@lem5409598 (@lem5409608)). Qed.
Lemma lem5409611 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409612 : term314 = term315.
Proof. exact (@lem5409611 (NUMERAL 0) term79). Qed.
Lemma lem5409613 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409614 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409615 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409614 h1) (fun h1 : term315 = True => @lem5409613)). Qed.
Lemma lem5409616 : term315 = True.
Proof. exact (EQ_MP (@lem5409615) (@lem5409613)). Qed.
Lemma lem5409617 : term314 = True.
Proof. exact (TRANS (@lem5409612) (@lem5409616)). Qed.
Lemma lem5409618 : True = term314.
Proof. exact (SYM (@lem5409617)). Qed.
Lemma lem5409619 : term314.
Proof. exact (EQ_MP (@lem5409618) (@lem0)). Qed.
Lemma lem5409620 : term623.
Proof. exact (@lem5409609 (@lem5409619)). Qed.
Lemma lem5409622 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5409623 : term265 = term266.
Proof. exact (@lem5409622 term79 term79). Qed.
Lemma lem5409624 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409625 : term268 = term79.
Proof. exact (EQ_MP (@lem5409624) (@lem940073)). Qed.
Lemma lem5409626 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409627 : term266 = term193.
Proof. exact (MK_COMB (@lem5409626) (@lem5409625)). Qed.
Lemma lem5409628 : term265 = term193.
Proof. exact (TRANS (@lem5409623) (@lem5409627)). Qed.
Lemma lem5409630 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5409631 : term291 = term296.
Proof. exact (@lem5409630 term79 term79). Qed.
Lemma lem5409632 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409633 : term268 = term79.
Proof. exact (EQ_MP (@lem5409632) (@lem940073)). Qed.
Lemma lem5409634 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409635 : term266 = term193.
Proof. exact (MK_COMB (@lem5409634) (@lem5409633)). Qed.
Lemma lem5409636 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5409637 : term296 = term256.
Proof. exact (MK_COMB (@lem5409636) (@lem5409635)). Qed.
Lemma lem5409638 : term291 = term256.
Proof. exact (TRANS (@lem5409631) (@lem5409637)). Qed.
Lemma lem5409639 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409640 : term624 = term616.
Proof. exact (MK_COMB (@lem5409639) (@lem5409638)). Qed.
Lemma lem5409641 : term625 = term618.
Proof. exact (MK_COMB (@lem5409640) (@lem5409628)). Qed.
Lemma lem5409643 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5409644 : term618 = term182.
Proof. exact (@lem5409643 term79). Qed.
Lemma lem5409645 : term625 = term182.
Proof. exact (TRANS (@lem5409641) (@lem5409644)). Qed.
Lemma lem5409646 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5409647 : term627 = term403.
Proof. exact (MK_COMB (@lem5409646) (@lem5409645)). Qed.
Lemma lem5409648 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5409649 : term628 = term405.
Proof. exact (MK_COMB (@lem5409647) (@lem5409648)). Qed.
Lemma lem5409651 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5409652 : term405 = term182.
Proof. exact (@lem5409651 term79). Qed.
Lemma lem5409653 : term628 = term182.
Proof. exact (TRANS (@lem5409649) (@lem5409652)). Qed.
Lemma lem5409655 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5409656 : term265 = term266.
Proof. exact (@lem5409655 term79 term79). Qed.
Lemma lem5409657 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409658 : term268 = term79.
Proof. exact (EQ_MP (@lem5409657) (@lem940073)). Qed.
Lemma lem5409659 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409660 : term266 = term193.
Proof. exact (MK_COMB (@lem5409659) (@lem5409658)). Qed.
Lemma lem5409661 : term265 = term193.
Proof. exact (TRANS (@lem5409656) (@lem5409660)). Qed.
Lemma lem5409662 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5409663 : term407 = term405.
Proof. exact (MK_COMB (@lem5409662) (@lem5409661)). Qed.
Lemma lem5409665 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5409666 : term405 = term182.
Proof. exact (@lem5409665 term79). Qed.
Lemma lem5409667 : term407 = term182.
Proof. exact (TRANS (@lem5409663) (@lem5409666)). Qed.
Lemma lem5409668 : term182 = term407.
Proof. exact (SYM (@lem5409667)). Qed.
Lemma lem5409669 : term628 = term407.
Proof. exact (TRANS (@lem5409653) (@lem5409668)). Qed.
Lemma lem5409670 : term619 = term253.
Proof. exact (@lem5409620 (@lem5409669)). Qed.
Lemma lem5409671 : term618 = term253.
Proof. exact (TRANS (@lem5409586) (@lem5409670)). Qed.
Lemma lem5409673 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5409674 : term253 = term182.
Proof. exact (@lem5409673 term182). Qed.
Lemma lem5409675 : term618 = term182.
Proof. exact (TRANS (@lem5409671) (@lem5409674)). Qed.
Lemma lem5409676 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5409677 : term629 = term403.
Proof. exact (MK_COMB (@lem5409676) (@lem5409675)). Qed.
Lemma lem5409678 (_69904 : int) : (real_of_int _69904) = (real_of_int _69904).
Proof. exact (eq_refl (real_of_int _69904)). Qed.
Lemma lem5409679 (_69904 : int) : (term615 _69904) = (term630 _69904).
Proof. exact (MK_COMB (@lem5409677) (@lem5409678 _69904)). Qed.
Lemma lem5409680 (_69904 : int) : (term614 _69904) = (term630 _69904).
Proof. exact (TRANS (@lem5409577 _69904) (@lem5409679 _69904)). Qed.
Lemma lem5409681 (_69904 : int) : (term630 _69904) = term182.
Proof. exact (@lem1982719 (real_of_int _69904)). Qed.
Lemma lem5409682 (_69904 : int) : (term614 _69904) = term182.
Proof. exact (TRANS (@lem5409680 _69904) (@lem5409681 _69904)). Qed.
Lemma lem5409683 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409684 (_69904 : int) : (term631 _69904) = term632.
Proof. exact (MK_COMB (@lem5409683) (@lem5409682 _69904)). Qed.
Lemma lem5409685 (_69905 : int) : (term728 _69905) = (term729 _69905).
Proof. exact (@lem1982753 (term281 _69905) (real_of_int _69905) term193 term350). Qed.
Lemma lem5409686 (_69905 : int) : (term667 _69905) = (term615 _69905).
Proof. exact (@lem1982713 term256 (real_of_int _69905)). Qed.
Lemma lem5409688 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5409689 : term193 = term290.
Proof. exact (@lem5409688 term79). Qed.
Lemma lem5409691 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5409692 : term256 = term257.
Proof. exact (@lem5409691 term79). Qed.
Lemma lem5409693 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409694 : term616 = term617.
Proof. exact (MK_COMB (@lem5409693) (@lem5409692)). Qed.
Lemma lem5409695 : term618 = term619.
Proof. exact (MK_COMB (@lem5409694) (@lem5409689)). Qed.
Lemma lem5409696 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5409698 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409699 : term314 = term315.
Proof. exact (@lem5409698 (NUMERAL 0) term79). Qed.
Lemma lem5409700 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409701 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409702 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409701 h1) (fun h1 : term315 = True => @lem5409700)). Qed.
Lemma lem5409703 : term315 = True.
Proof. exact (EQ_MP (@lem5409702) (@lem5409700)). Qed.
Lemma lem5409704 : term314 = True.
Proof. exact (TRANS (@lem5409699) (@lem5409703)). Qed.
Lemma lem5409705 : True = term314.
Proof. exact (SYM (@lem5409704)). Qed.
Lemma lem5409706 : term314.
Proof. exact (EQ_MP (@lem5409705) (@lem0)). Qed.
Lemma lem5409707 : term621.
Proof. exact (@lem5409696 (@lem5409706)). Qed.
Lemma lem5409709 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409710 : term314 = term315.
Proof. exact (@lem5409709 (NUMERAL 0) term79). Qed.
Lemma lem5409711 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409712 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409713 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409712 h1) (fun h1 : term315 = True => @lem5409711)). Qed.
Lemma lem5409714 : term315 = True.
Proof. exact (EQ_MP (@lem5409713) (@lem5409711)). Qed.
Lemma lem5409715 : term314 = True.
Proof. exact (TRANS (@lem5409710) (@lem5409714)). Qed.
Lemma lem5409716 : True = term314.
Proof. exact (SYM (@lem5409715)). Qed.
Lemma lem5409717 : term314.
Proof. exact (EQ_MP (@lem5409716) (@lem0)). Qed.
Lemma lem5409718 : term622.
Proof. exact (@lem5409707 (@lem5409717)). Qed.
Lemma lem5409720 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409721 : term314 = term315.
Proof. exact (@lem5409720 (NUMERAL 0) term79). Qed.
Lemma lem5409722 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409723 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409724 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409723 h1) (fun h1 : term315 = True => @lem5409722)). Qed.
Lemma lem5409725 : term315 = True.
Proof. exact (EQ_MP (@lem5409724) (@lem5409722)). Qed.
Lemma lem5409726 : term314 = True.
Proof. exact (TRANS (@lem5409721) (@lem5409725)). Qed.
Lemma lem5409727 : True = term314.
Proof. exact (SYM (@lem5409726)). Qed.
Lemma lem5409728 : term314.
Proof. exact (EQ_MP (@lem5409727) (@lem0)). Qed.
Lemma lem5409729 : term623.
Proof. exact (@lem5409718 (@lem5409728)). Qed.
Lemma lem5409731 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5409732 : term265 = term266.
Proof. exact (@lem5409731 term79 term79). Qed.
Lemma lem5409733 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409734 : term268 = term79.
Proof. exact (EQ_MP (@lem5409733) (@lem940073)). Qed.
Lemma lem5409735 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409736 : term266 = term193.
Proof. exact (MK_COMB (@lem5409735) (@lem5409734)). Qed.
Lemma lem5409737 : term265 = term193.
Proof. exact (TRANS (@lem5409732) (@lem5409736)). Qed.
Lemma lem5409739 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5409740 : term291 = term296.
Proof. exact (@lem5409739 term79 term79). Qed.
Lemma lem5409741 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409742 : term268 = term79.
Proof. exact (EQ_MP (@lem5409741) (@lem940073)). Qed.
Lemma lem5409743 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409744 : term266 = term193.
Proof. exact (MK_COMB (@lem5409743) (@lem5409742)). Qed.
Lemma lem5409745 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5409746 : term296 = term256.
Proof. exact (MK_COMB (@lem5409745) (@lem5409744)). Qed.
Lemma lem5409747 : term291 = term256.
Proof. exact (TRANS (@lem5409740) (@lem5409746)). Qed.
Lemma lem5409748 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409749 : term624 = term616.
Proof. exact (MK_COMB (@lem5409748) (@lem5409747)). Qed.
Lemma lem5409750 : term625 = term618.
Proof. exact (MK_COMB (@lem5409749) (@lem5409737)). Qed.
Lemma lem5409752 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5409753 : term618 = term182.
Proof. exact (@lem5409752 term79). Qed.
Lemma lem5409754 : term625 = term182.
Proof. exact (TRANS (@lem5409750) (@lem5409753)). Qed.
Lemma lem5409755 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5409756 : term627 = term403.
Proof. exact (MK_COMB (@lem5409755) (@lem5409754)). Qed.
Lemma lem5409757 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5409758 : term628 = term405.
Proof. exact (MK_COMB (@lem5409756) (@lem5409757)). Qed.
Lemma lem5409760 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5409761 : term405 = term182.
Proof. exact (@lem5409760 term79). Qed.
Lemma lem5409762 : term628 = term182.
Proof. exact (TRANS (@lem5409758) (@lem5409761)). Qed.
Lemma lem5409764 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5409765 : term265 = term266.
Proof. exact (@lem5409764 term79 term79). Qed.
Lemma lem5409766 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409767 : term268 = term79.
Proof. exact (EQ_MP (@lem5409766) (@lem940073)). Qed.
Lemma lem5409768 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409769 : term266 = term193.
Proof. exact (MK_COMB (@lem5409768) (@lem5409767)). Qed.
Lemma lem5409770 : term265 = term193.
Proof. exact (TRANS (@lem5409765) (@lem5409769)). Qed.
Lemma lem5409771 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5409772 : term407 = term405.
Proof. exact (MK_COMB (@lem5409771) (@lem5409770)). Qed.
Lemma lem5409774 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5409775 : term405 = term182.
Proof. exact (@lem5409774 term79). Qed.
Lemma lem5409776 : term407 = term182.
Proof. exact (TRANS (@lem5409772) (@lem5409775)). Qed.
Lemma lem5409777 : term182 = term407.
Proof. exact (SYM (@lem5409776)). Qed.
Lemma lem5409778 : term628 = term407.
Proof. exact (TRANS (@lem5409762) (@lem5409777)). Qed.
Lemma lem5409779 : term619 = term253.
Proof. exact (@lem5409729 (@lem5409778)). Qed.
Lemma lem5409780 : term618 = term253.
Proof. exact (TRANS (@lem5409695) (@lem5409779)). Qed.
Lemma lem5409782 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5409783 : term253 = term182.
Proof. exact (@lem5409782 term182). Qed.
Lemma lem5409784 : term618 = term182.
Proof. exact (TRANS (@lem5409780) (@lem5409783)). Qed.
Lemma lem5409785 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5409786 : term629 = term403.
Proof. exact (MK_COMB (@lem5409785) (@lem5409784)). Qed.
Lemma lem5409787 (_69905 : int) : (real_of_int _69905) = (real_of_int _69905).
Proof. exact (eq_refl (real_of_int _69905)). Qed.
Lemma lem5409788 (_69905 : int) : (term615 _69905) = (term630 _69905).
Proof. exact (MK_COMB (@lem5409786) (@lem5409787 _69905)). Qed.
Lemma lem5409789 (_69905 : int) : (term667 _69905) = (term630 _69905).
Proof. exact (TRANS (@lem5409686 _69905) (@lem5409788 _69905)). Qed.
Lemma lem5409790 (_69905 : int) : (term630 _69905) = term182.
Proof. exact (@lem1982719 (real_of_int _69905)). Qed.
Lemma lem5409791 (_69905 : int) : (term667 _69905) = term182.
Proof. exact (TRANS (@lem5409789 _69905) (@lem5409790 _69905)). Qed.
Lemma lem5409792 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409793 (_69905 : int) : (term668 _69905) = term632.
Proof. exact (MK_COMB (@lem5409792) (@lem5409791 _69905)). Qed.
Lemma lem5409795 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5409796 : term350 = term353.
Proof. exact (@lem5409795 term326). Qed.
Lemma lem5409798 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5409799 : term193 = term290.
Proof. exact (@lem5409798 term79). Qed.
Lemma lem5409800 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409801 : term307 = term308.
Proof. exact (MK_COMB (@lem5409800) (@lem5409799)). Qed.
Lemma lem5409802 : term671 = term672.
Proof. exact (MK_COMB (@lem5409801) (@lem5409796)). Qed.
Lemma lem5409803 : term673.
Proof. exact (@lem1981473 term193 term193 term350 term193 term256 term193). Qed.
Lemma lem5409805 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409806 : term314 = term315.
Proof. exact (@lem5409805 (NUMERAL 0) term79). Qed.
Lemma lem5409807 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409808 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409809 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409808 h1) (fun h1 : term315 = True => @lem5409807)). Qed.
Lemma lem5409810 : term315 = True.
Proof. exact (EQ_MP (@lem5409809) (@lem5409807)). Qed.
Lemma lem5409811 : term314 = True.
Proof. exact (TRANS (@lem5409806) (@lem5409810)). Qed.
Lemma lem5409812 : True = term314.
Proof. exact (SYM (@lem5409811)). Qed.
Lemma lem5409813 : term314.
Proof. exact (EQ_MP (@lem5409812) (@lem0)). Qed.
Lemma lem5409814 : term674.
Proof. exact (@lem5409803 (@lem5409813)). Qed.
Lemma lem5409816 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409817 : term314 = term315.
Proof. exact (@lem5409816 (NUMERAL 0) term79). Qed.
Lemma lem5409818 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409819 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409820 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409819 h1) (fun h1 : term315 = True => @lem5409818)). Qed.
Lemma lem5409821 : term315 = True.
Proof. exact (EQ_MP (@lem5409820) (@lem5409818)). Qed.
Lemma lem5409822 : term314 = True.
Proof. exact (TRANS (@lem5409817) (@lem5409821)). Qed.
Lemma lem5409823 : True = term314.
Proof. exact (SYM (@lem5409822)). Qed.
Lemma lem5409824 : term314.
Proof. exact (EQ_MP (@lem5409823) (@lem0)). Qed.
Lemma lem5409825 : term675.
Proof. exact (@lem5409814 (@lem5409824)). Qed.
Lemma lem5409827 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409828 : term314 = term315.
Proof. exact (@lem5409827 (NUMERAL 0) term79). Qed.
Lemma lem5409829 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409830 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409831 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409830 h1) (fun h1 : term315 = True => @lem5409829)). Qed.
Lemma lem5409832 : term315 = True.
Proof. exact (EQ_MP (@lem5409831) (@lem5409829)). Qed.
Lemma lem5409833 : term314 = True.
Proof. exact (TRANS (@lem5409828) (@lem5409832)). Qed.
Lemma lem5409834 : True = term314.
Proof. exact (SYM (@lem5409833)). Qed.
Lemma lem5409835 : term314.
Proof. exact (EQ_MP (@lem5409834) (@lem0)). Qed.
Lemma lem5409836 : term676.
Proof. exact (@lem5409825 (@lem5409835)). Qed.
Lemma lem5409838 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5409839 : term644 = term645.
Proof. exact (@lem5409838 term326 term79). Qed.
Lemma lem5409840 : term332 = term324.
Proof. exact (@lem996237 term324). Qed.
Lemma lem5409841 : (term332 = term324) = (term333 = term326).
Proof. exact (@lem1007663 term324 (BIT1 0) term324). Qed.
Lemma lem5409842 : term333 = term326.
Proof. exact (EQ_MP (@lem5409841) (@lem5409840)). Qed.
Lemma lem5409843 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409844 : term331 = term312.
Proof. exact (MK_COMB (@lem5409843) (@lem5409842)). Qed.
Lemma lem5409845 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5409846 : term645 = term350.
Proof. exact (MK_COMB (@lem5409845) (@lem5409844)). Qed.
Lemma lem5409847 : term644 = term350.
Proof. exact (TRANS (@lem5409839) (@lem5409846)). Qed.
Lemma lem5409849 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5409850 : term265 = term266.
Proof. exact (@lem5409849 term79 term79). Qed.
Lemma lem5409851 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409852 : term268 = term79.
Proof. exact (EQ_MP (@lem5409851) (@lem940073)). Qed.
Lemma lem5409853 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409854 : term266 = term193.
Proof. exact (MK_COMB (@lem5409853) (@lem5409852)). Qed.
Lemma lem5409855 : term265 = term193.
Proof. exact (TRANS (@lem5409850) (@lem5409854)). Qed.
Lemma lem5409856 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5409857 : term320 = term307.
Proof. exact (MK_COMB (@lem5409856) (@lem5409855)). Qed.
Lemma lem5409858 : term677 = term671.
Proof. exact (MK_COMB (@lem5409857) (@lem5409847)). Qed.
Lemma lem5409861 : term678 = term256.
Proof. exact (@lem1367771 term79 term79). Qed.
Lemma lem5409862 : term323 = term324.
Proof. exact (@lem706885). Qed.
Lemma lem5409863 : (term323 = term324) = (term325 = term326).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term324). Qed.
Lemma lem5409864 : term325 = term326.
Proof. exact (EQ_MP (@lem5409863) (@lem5409862)). Qed.
Lemma lem5409865 : term326 = term325.
Proof. exact (SYM (@lem5409864)). Qed.
Lemma lem5409866 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409867 : term312 = term322.
Proof. exact (MK_COMB (@lem5409866) (@lem5409865)). Qed.
Lemma lem5409868 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5409869 : term350 = term640.
Proof. exact (MK_COMB (@lem5409868) (@lem5409867)). Qed.
Lemma lem5409870 : term307 = term307.
Proof. exact (eq_refl term307). Qed.
Lemma lem5409871 : term671 = term678.
Proof. exact (MK_COMB (@lem5409870) (@lem5409869)). Qed.
Lemma lem5409872 : term671 = term256.
Proof. exact (TRANS (@lem5409871) (@lem5409861)). Qed.
Lemma lem5409873 : term677 = term256.
Proof. exact (TRANS (@lem5409858) (@lem5409872)). Qed.
Lemma lem5409874 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5409875 : term679 = term258.
Proof. exact (MK_COMB (@lem5409874) (@lem5409873)). Qed.
Lemma lem5409876 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5409877 : term680 = term291.
Proof. exact (MK_COMB (@lem5409875) (@lem5409876)). Qed.
Lemma lem5409879 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5409880 : term291 = term296.
Proof. exact (@lem5409879 term79 term79). Qed.
Lemma lem5409881 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409882 : term268 = term79.
Proof. exact (EQ_MP (@lem5409881) (@lem940073)). Qed.
Lemma lem5409883 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409884 : term266 = term193.
Proof. exact (MK_COMB (@lem5409883) (@lem5409882)). Qed.
Lemma lem5409885 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5409886 : term296 = term256.
Proof. exact (MK_COMB (@lem5409885) (@lem5409884)). Qed.
Lemma lem5409887 : term291 = term256.
Proof. exact (TRANS (@lem5409880) (@lem5409886)). Qed.
Lemma lem5409888 : term680 = term256.
Proof. exact (TRANS (@lem5409877) (@lem5409887)). Qed.
Lemma lem5409890 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5409891 : term265 = term266.
Proof. exact (@lem5409890 term79 term79). Qed.
Lemma lem5409892 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409893 : term268 = term79.
Proof. exact (EQ_MP (@lem5409892) (@lem940073)). Qed.
Lemma lem5409894 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409895 : term266 = term193.
Proof. exact (MK_COMB (@lem5409894) (@lem5409893)). Qed.
Lemma lem5409896 : term265 = term193.
Proof. exact (TRANS (@lem5409891) (@lem5409895)). Qed.
Lemma lem5409897 : term258 = term258.
Proof. exact (eq_refl term258). Qed.
Lemma lem5409898 : term681 = term291.
Proof. exact (MK_COMB (@lem5409897) (@lem5409896)). Qed.
Lemma lem5409900 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5409901 : term291 = term296.
Proof. exact (@lem5409900 term79 term79). Qed.
Lemma lem5409902 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409903 : term268 = term79.
Proof. exact (EQ_MP (@lem5409902) (@lem940073)). Qed.
Lemma lem5409904 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409905 : term266 = term193.
Proof. exact (MK_COMB (@lem5409904) (@lem5409903)). Qed.
Lemma lem5409906 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5409907 : term296 = term256.
Proof. exact (MK_COMB (@lem5409906) (@lem5409905)). Qed.
Lemma lem5409908 : term291 = term256.
Proof. exact (TRANS (@lem5409901) (@lem5409907)). Qed.
Lemma lem5409909 : term681 = term256.
Proof. exact (TRANS (@lem5409898) (@lem5409908)). Qed.
Lemma lem5409910 : term256 = term681.
Proof. exact (SYM (@lem5409909)). Qed.
Lemma lem5409911 : term680 = term681.
Proof. exact (TRANS (@lem5409888) (@lem5409910)). Qed.
Lemma lem5409912 : term672 = term257.
Proof. exact (@lem5409836 (@lem5409911)). Qed.
Lemma lem5409913 : term671 = term257.
Proof. exact (TRANS (@lem5409802) (@lem5409912)). Qed.
Lemma lem5409915 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5409916 : term257 = term256.
Proof. exact (@lem5409915 term256). Qed.
Lemma lem5409917 : term671 = term256.
Proof. exact (TRANS (@lem5409913) (@lem5409916)). Qed.
Lemma lem5409918 (_69905 : int) : (term729 _69905) = term682.
Proof. exact (MK_COMB (@lem5409793 _69905) (@lem5409917)). Qed.
Lemma lem5409919 (_69905 : int) : (term728 _69905) = term682.
Proof. exact (TRANS (@lem5409685 _69905) (@lem5409918 _69905)). Qed.
Lemma lem5409920 : term682 = term256.
Proof. exact (@lem1982721 term256). Qed.
Lemma lem5409921 (_69905 : int) : (term728 _69905) = term256.
Proof. exact (TRANS (@lem5409919 _69905) (@lem5409920)). Qed.
Lemma lem5409922 (_69904 : int) (_69905 : int) : (term726 _69904 _69905) = term682.
Proof. exact (MK_COMB (@lem5409684 _69904) (@lem5409921 _69905)). Qed.
Lemma lem5409923 (_69904 : int) (_69905 : int) : (term725 _69904 _69905) = term682.
Proof. exact (TRANS (@lem5409576 _69904 _69905) (@lem5409922 _69904 _69905)). Qed.
Lemma lem5409924 : term682 = term256.
Proof. exact (@lem1982721 term256). Qed.
Lemma lem5409925 (_69904 : int) (_69905 : int) : (term725 _69904 _69905) = term256.
Proof. exact (TRANS (@lem5409923 _69904 _69905) (@lem5409924)). Qed.
Lemma lem5409926 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5409927 (_69904 : int) (_69905 : int) : (term730 _69904 _69905) = term684.
Proof. exact (MK_COMB (@lem5409926) (@lem5409925 _69904 _69905)). Qed.
Lemma lem5409928 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5409929 (_69904 : int) (_69905 : int) : (term724 _69904 _69905) = term685.
Proof. exact (MK_COMB (@lem5409927 _69904 _69905) (@lem5409928)). Qed.
Lemma lem5409930 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : term685.
Proof. exact (EQ_MP (@lem5409929 _69904 _69905) (@lem5409575 _69903 _69904 _69905 h1)). Qed.
Lemma lem5409932 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5409933 : term685 = term686.
Proof. exact (@lem5409932 term182 term256). Qed.
Lemma lem5409935 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5409936 : term256 = term257.
Proof. exact (@lem5409935 term79). Qed.
Lemma lem5409938 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5409939 : term182 = term253.
Proof. exact (@lem5409938 (NUMERAL 0)). Qed.
Lemma lem5409940 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5409941 : term184 = term687.
Proof. exact (MK_COMB (@lem5409940) (@lem5409939)). Qed.
Lemma lem5409942 : term686 = term688.
Proof. exact (MK_COMB (@lem5409941) (@lem5409936)). Qed.
Lemma lem5409943 : term689.
Proof. exact (@lem1980026 term182 term193 term256 term193). Qed.
Lemma lem5409945 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409946 : term314 = term315.
Proof. exact (@lem5409945 (NUMERAL 0) term79). Qed.
Lemma lem5409947 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409948 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409949 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409948 h1) (fun h1 : term315 = True => @lem5409947)). Qed.
Lemma lem5409950 : term315 = True.
Proof. exact (EQ_MP (@lem5409949) (@lem5409947)). Qed.
Lemma lem5409951 : term314 = True.
Proof. exact (TRANS (@lem5409946) (@lem5409950)). Qed.
Lemma lem5409952 : True = term314.
Proof. exact (SYM (@lem5409951)). Qed.
Lemma lem5409953 : term314.
Proof. exact (EQ_MP (@lem5409952) (@lem0)). Qed.
Lemma lem5409954 : term690.
Proof. exact (@lem5409943 (@lem5409953)). Qed.
Lemma lem5409956 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5409957 : term314 = term315.
Proof. exact (@lem5409956 (NUMERAL 0) term79). Qed.
Lemma lem5409958 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409959 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5409960 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409959 h1) (fun h1 : term315 = True => @lem5409958)). Qed.
Lemma lem5409961 : term315 = True.
Proof. exact (EQ_MP (@lem5409960) (@lem5409958)). Qed.
Lemma lem5409962 : term314 = True.
Proof. exact (TRANS (@lem5409957) (@lem5409961)). Qed.
Lemma lem5409963 : True = term314.
Proof. exact (SYM (@lem5409962)). Qed.
Lemma lem5409964 : term314.
Proof. exact (EQ_MP (@lem5409963) (@lem0)). Qed.
Lemma lem5409965 : term688 = term691.
Proof. exact (@lem5409954 (@lem5409964)). Qed.
Lemma lem5409967 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5409968 : term291 = term296.
Proof. exact (@lem5409967 term79 term79). Qed.
Lemma lem5409969 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5409970 : term268 = term79.
Proof. exact (EQ_MP (@lem5409969) (@lem940073)). Qed.
Lemma lem5409971 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5409972 : term266 = term193.
Proof. exact (MK_COMB (@lem5409971) (@lem5409970)). Qed.
Lemma lem5409973 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5409974 : term296 = term256.
Proof. exact (MK_COMB (@lem5409973) (@lem5409972)). Qed.
Lemma lem5409975 : term291 = term256.
Proof. exact (TRANS (@lem5409968) (@lem5409974)). Qed.
Lemma lem5409977 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5409978 : term405 = term182.
Proof. exact (@lem5409977 term79). Qed.
Lemma lem5409979 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5409980 : term692 = term184.
Proof. exact (MK_COMB (@lem5409979) (@lem5409978)). Qed.
Lemma lem5409981 : term691 = term686.
Proof. exact (MK_COMB (@lem5409980) (@lem5409975)). Qed.
Lemma lem5409983 (m : nat) (n : nat) : (term693 m n) = (term694 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5409984 : term686 = term695.
Proof. exact (@lem5409983 (NUMERAL 0) term79). Qed.
Lemma lem5409985 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5409986 (h1 : term316 = (BIT1 0)) : (term79 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5409987 : (term316 = (BIT1 0)) = ((term79 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5409986 h1) (fun h1 : (term79 = (NUMERAL 0)) = False => @lem5409985)). Qed.
Lemma lem5409988 : (term79 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5409987) (@lem5409985)). Qed.
Lemma lem5409989 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5409990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5409991 : term696 = (and True).
Proof. exact (MK_COMB (@lem5409990) (@lem5409989)). Qed.
Lemma lem5409992 : term695 = (True /\ False).
Proof. exact (MK_COMB (@lem5409991) (@lem5409988)). Qed.
Lemma lem5409994 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5409995 : term695 = False.
Proof. exact (TRANS (@lem5409992) (@lem5409994)). Qed.
Lemma lem5409996 : term686 = False.
Proof. exact (TRANS (@lem5409984) (@lem5409995)). Qed.
Lemma lem5409997 : term691 = False.
Proof. exact (TRANS (@lem5409981) (@lem5409996)). Qed.
Lemma lem5409998 : term688 = False.
Proof. exact (TRANS (@lem5409965) (@lem5409997)). Qed.
Lemma lem5409999 : term686 = False.
Proof. exact (TRANS (@lem5409942) (@lem5409998)). Qed.
Lemma lem5410000 : term685 = False.
Proof. exact (TRANS (@lem5409933) (@lem5409999)). Qed.
Lemma lem5410001 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term697 _69903 _69904 _69905) : False.
Proof. exact (EQ_MP (@lem5410000) (@lem5409930 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410002 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term573 _69903 _69904 _69905) : False.
Proof. exact (or_elim (@lem5408454 _69903 _69904 _69905 h1) (fun h0 : term582 _69903 _69904 _69905 => @lem5409384 _69903 _69904 _69905 h0) (fun h0 : term697 _69903 _69904 _69905 => @lem5410001 _69903 _69904 _69905 h0)). Qed.
Lemma lem5410003 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term569 _69903 _69904 _69905) : term569 _69903 _69904 _69905.
Proof. exact (h1). Qed.
Lemma lem5410004 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term731 _69903 _69904 _69905.
Proof. exact (h1). Qed.
Lemma lem5410005 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term570 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5410004 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410007 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term539 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5410005 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410009 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term508 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5410007 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410011 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term477 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5410009 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410013 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term375 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5410011 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410014 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term304 _69903 _69905.
Proof. exact (proj1 (@lem5410011 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410016 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term371 _69903 _69905.
Proof. exact (proj1 (@lem5410013 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410018 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5410019 : term583 = term314.
Proof. exact (@lem5410018 term182 term193). Qed.
Lemma lem5410021 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410022 : term193 = term290.
Proof. exact (@lem5410021 term79). Qed.
Lemma lem5410024 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410025 : term182 = term253.
Proof. exact (@lem5410024 (NUMERAL 0)). Qed.
Lemma lem5410026 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5410027 : term584 = term585.
Proof. exact (MK_COMB (@lem5410026) (@lem5410025)). Qed.
Lemma lem5410028 : term314 = term586.
Proof. exact (MK_COMB (@lem5410027) (@lem5410022)). Qed.
Lemma lem5410029 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5410031 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410032 : term314 = term315.
Proof. exact (@lem5410031 (NUMERAL 0) term79). Qed.
Lemma lem5410033 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410034 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410035 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410034 h1) (fun h1 : term315 = True => @lem5410033)). Qed.
Lemma lem5410036 : term315 = True.
Proof. exact (EQ_MP (@lem5410035) (@lem5410033)). Qed.
Lemma lem5410037 : term314 = True.
Proof. exact (TRANS (@lem5410032) (@lem5410036)). Qed.
Lemma lem5410038 : True = term314.
Proof. exact (SYM (@lem5410037)). Qed.
Lemma lem5410039 : term314.
Proof. exact (EQ_MP (@lem5410038) (@lem0)). Qed.
Lemma lem5410040 : term588.
Proof. exact (@lem5410029 (@lem5410039)). Qed.
Lemma lem5410042 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410043 : term314 = term315.
Proof. exact (@lem5410042 (NUMERAL 0) term79). Qed.
Lemma lem5410044 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410045 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410046 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410045 h1) (fun h1 : term315 = True => @lem5410044)). Qed.
Lemma lem5410047 : term315 = True.
Proof. exact (EQ_MP (@lem5410046) (@lem5410044)). Qed.
Lemma lem5410048 : term314 = True.
Proof. exact (TRANS (@lem5410043) (@lem5410047)). Qed.
Lemma lem5410049 : True = term314.
Proof. exact (SYM (@lem5410048)). Qed.
Lemma lem5410050 : term314.
Proof. exact (EQ_MP (@lem5410049) (@lem0)). Qed.
Lemma lem5410051 : term586 = term589.
Proof. exact (@lem5410040 (@lem5410050)). Qed.
Lemma lem5410053 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5410054 : term265 = term266.
Proof. exact (@lem5410053 term79 term79). Qed.
Lemma lem5410055 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410056 : term268 = term79.
Proof. exact (EQ_MP (@lem5410055) (@lem940073)). Qed.
Lemma lem5410057 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410058 : term266 = term193.
Proof. exact (MK_COMB (@lem5410057) (@lem5410056)). Qed.
Lemma lem5410059 : term265 = term193.
Proof. exact (TRANS (@lem5410054) (@lem5410058)). Qed.
Lemma lem5410061 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5410062 : term405 = term182.
Proof. exact (@lem5410061 term79). Qed.
Lemma lem5410063 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5410064 : term590 = term584.
Proof. exact (MK_COMB (@lem5410063) (@lem5410062)). Qed.
Lemma lem5410065 : term589 = term314.
Proof. exact (MK_COMB (@lem5410064) (@lem5410059)). Qed.
Lemma lem5410067 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410068 : term314 = term315.
Proof. exact (@lem5410067 (NUMERAL 0) term79). Qed.
Lemma lem5410069 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410070 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410071 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410070 h1) (fun h1 : term315 = True => @lem5410069)). Qed.
Lemma lem5410072 : term315 = True.
Proof. exact (EQ_MP (@lem5410071) (@lem5410069)). Qed.
Lemma lem5410073 : term314 = True.
Proof. exact (TRANS (@lem5410068) (@lem5410072)). Qed.
Lemma lem5410074 : term589 = True.
Proof. exact (TRANS (@lem5410065) (@lem5410073)). Qed.
Lemma lem5410075 : term586 = True.
Proof. exact (TRANS (@lem5410051) (@lem5410074)). Qed.
Lemma lem5410076 : term314 = True.
Proof. exact (TRANS (@lem5410028) (@lem5410075)). Qed.
Lemma lem5410077 : term583 = True.
Proof. exact (TRANS (@lem5410019) (@lem5410076)). Qed.
Lemma lem5410078 : True = term583.
Proof. exact (SYM (@lem5410077)). Qed.
Lemma lem5410079 : term583.
Proof. exact (EQ_MP (@lem5410078) (@lem0)). Qed.
Lemma lem5410080 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term591 _69903 _69905.
Proof. exact (conj (@lem5410079) (@lem5410014 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410082 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5410083 (_69903 : int) (_69905 : int) : term593 _69903 _69905.
Proof. exact (@lem5410082 term193 (term301 _69903 _69905)). Qed.
Lemma lem5410084 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term594 _69903 _69905.
Proof. exact (@lem5410083 _69903 _69905 (@lem5410080 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410085 (_69903 : int) (_69905 : int) : (term595 _69903 _69905) = (term301 _69903 _69905).
Proof. exact (@lem1982733 (term301 _69903 _69905)). Qed.
Lemma lem5410086 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5410087 (_69903 : int) (_69905 : int) : (term596 _69903 _69905) = (term303 _69903 _69905).
Proof. exact (MK_COMB (@lem5410086) (@lem5410085 _69903 _69905)). Qed.
Lemma lem5410088 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5410089 (_69903 : int) (_69905 : int) : (term594 _69903 _69905) = (term304 _69903 _69905).
Proof. exact (MK_COMB (@lem5410087 _69903 _69905) (@lem5410088)). Qed.
Lemma lem5410090 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term304 _69903 _69905.
Proof. exact (EQ_MP (@lem5410089 _69903 _69905) (@lem5410084 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410092 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5410093 : term583 = term314.
Proof. exact (@lem5410092 term182 term193). Qed.
Lemma lem5410095 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410096 : term193 = term290.
Proof. exact (@lem5410095 term79). Qed.
Lemma lem5410098 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410099 : term182 = term253.
Proof. exact (@lem5410098 (NUMERAL 0)). Qed.
Lemma lem5410100 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5410101 : term584 = term585.
Proof. exact (MK_COMB (@lem5410100) (@lem5410099)). Qed.
Lemma lem5410102 : term314 = term586.
Proof. exact (MK_COMB (@lem5410101) (@lem5410096)). Qed.
Lemma lem5410103 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5410105 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410106 : term314 = term315.
Proof. exact (@lem5410105 (NUMERAL 0) term79). Qed.
Lemma lem5410107 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410108 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410109 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410108 h1) (fun h1 : term315 = True => @lem5410107)). Qed.
Lemma lem5410110 : term315 = True.
Proof. exact (EQ_MP (@lem5410109) (@lem5410107)). Qed.
Lemma lem5410111 : term314 = True.
Proof. exact (TRANS (@lem5410106) (@lem5410110)). Qed.
Lemma lem5410112 : True = term314.
Proof. exact (SYM (@lem5410111)). Qed.
Lemma lem5410113 : term314.
Proof. exact (EQ_MP (@lem5410112) (@lem0)). Qed.
Lemma lem5410114 : term588.
Proof. exact (@lem5410103 (@lem5410113)). Qed.
Lemma lem5410116 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410117 : term314 = term315.
Proof. exact (@lem5410116 (NUMERAL 0) term79). Qed.
Lemma lem5410118 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410119 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410120 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410119 h1) (fun h1 : term315 = True => @lem5410118)). Qed.
Lemma lem5410121 : term315 = True.
Proof. exact (EQ_MP (@lem5410120) (@lem5410118)). Qed.
Lemma lem5410122 : term314 = True.
Proof. exact (TRANS (@lem5410117) (@lem5410121)). Qed.
Lemma lem5410123 : True = term314.
Proof. exact (SYM (@lem5410122)). Qed.
Lemma lem5410124 : term314.
Proof. exact (EQ_MP (@lem5410123) (@lem0)). Qed.
Lemma lem5410125 : term586 = term589.
Proof. exact (@lem5410114 (@lem5410124)). Qed.
Lemma lem5410127 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5410128 : term265 = term266.
Proof. exact (@lem5410127 term79 term79). Qed.
Lemma lem5410129 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410130 : term268 = term79.
Proof. exact (EQ_MP (@lem5410129) (@lem940073)). Qed.
Lemma lem5410131 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410132 : term266 = term193.
Proof. exact (MK_COMB (@lem5410131) (@lem5410130)). Qed.
Lemma lem5410133 : term265 = term193.
Proof. exact (TRANS (@lem5410128) (@lem5410132)). Qed.
Lemma lem5410135 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5410136 : term405 = term182.
Proof. exact (@lem5410135 term79). Qed.
Lemma lem5410137 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5410138 : term590 = term584.
Proof. exact (MK_COMB (@lem5410137) (@lem5410136)). Qed.
Lemma lem5410139 : term589 = term314.
Proof. exact (MK_COMB (@lem5410138) (@lem5410133)). Qed.
Lemma lem5410141 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410142 : term314 = term315.
Proof. exact (@lem5410141 (NUMERAL 0) term79). Qed.
Lemma lem5410143 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410144 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410145 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410144 h1) (fun h1 : term315 = True => @lem5410143)). Qed.
Lemma lem5410146 : term315 = True.
Proof. exact (EQ_MP (@lem5410145) (@lem5410143)). Qed.
Lemma lem5410147 : term314 = True.
Proof. exact (TRANS (@lem5410142) (@lem5410146)). Qed.
Lemma lem5410148 : term589 = True.
Proof. exact (TRANS (@lem5410139) (@lem5410147)). Qed.
Lemma lem5410149 : term586 = True.
Proof. exact (TRANS (@lem5410125) (@lem5410148)). Qed.
Lemma lem5410150 : term314 = True.
Proof. exact (TRANS (@lem5410102) (@lem5410149)). Qed.
Lemma lem5410151 : term583 = True.
Proof. exact (TRANS (@lem5410093) (@lem5410150)). Qed.
Lemma lem5410152 : True = term583.
Proof. exact (SYM (@lem5410151)). Qed.
Lemma lem5410153 : term583.
Proof. exact (EQ_MP (@lem5410152) (@lem0)). Qed.
Lemma lem5410154 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term732 _69903 _69905.
Proof. exact (conj (@lem5410153) (@lem5410016 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410156 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5410157 (_69903 : int) (_69905 : int) : term733 _69903 _69905.
Proof. exact (@lem5410156 term193 (term368 _69903 _69905)). Qed.
Lemma lem5410158 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term734 _69903 _69905.
Proof. exact (@lem5410157 _69903 _69905 (@lem5410154 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410159 (_69903 : int) (_69905 : int) : (term735 _69903 _69905) = (term368 _69903 _69905).
Proof. exact (@lem1982733 (term368 _69903 _69905)). Qed.
Lemma lem5410160 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5410161 (_69903 : int) (_69905 : int) : (term736 _69903 _69905) = (term370 _69903 _69905).
Proof. exact (MK_COMB (@lem5410160) (@lem5410159 _69903 _69905)). Qed.
Lemma lem5410162 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5410163 (_69903 : int) (_69905 : int) : (term734 _69903 _69905) = (term371 _69903 _69905).
Proof. exact (MK_COMB (@lem5410161 _69903 _69905) (@lem5410162)). Qed.
Lemma lem5410164 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term371 _69903 _69905.
Proof. exact (EQ_MP (@lem5410163 _69903 _69905) (@lem5410158 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410165 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term737 _69903 _69905.
Proof. exact (conj (@lem5410164 _69903 _69904 _69905 h1) (@lem5410090 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410167 (x : real) (y : real) : term662 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5410168 (_69903 : int) (_69905 : int) : term738 _69903 _69905.
Proof. exact (@lem5410167 (term368 _69903 _69905) (term301 _69903 _69905)). Qed.
Lemma lem5410169 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term739 _69903 _69905.
Proof. exact (@lem5410168 _69903 _69905 (@lem5410165 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410170 (_69903 : int) (_69905 : int) : (term740 _69903 _69905) = (term741 _69903 _69905).
Proof. exact (@lem1982753 (term281 _69903) (real_of_int _69903) (real_of_int _69905) (term300 _69905)). Qed.
Lemma lem5410171 (_69903 : int) : (term667 _69903) = (term615 _69903).
Proof. exact (@lem1982713 term256 (real_of_int _69903)). Qed.
Lemma lem5410173 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410174 : term193 = term290.
Proof. exact (@lem5410173 term79). Qed.
Lemma lem5410176 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5410177 : term256 = term257.
Proof. exact (@lem5410176 term79). Qed.
Lemma lem5410178 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5410179 : term616 = term617.
Proof. exact (MK_COMB (@lem5410178) (@lem5410177)). Qed.
Lemma lem5410180 : term618 = term619.
Proof. exact (MK_COMB (@lem5410179) (@lem5410174)). Qed.
Lemma lem5410181 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5410183 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410184 : term314 = term315.
Proof. exact (@lem5410183 (NUMERAL 0) term79). Qed.
Lemma lem5410185 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410186 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410187 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410186 h1) (fun h1 : term315 = True => @lem5410185)). Qed.
Lemma lem5410188 : term315 = True.
Proof. exact (EQ_MP (@lem5410187) (@lem5410185)). Qed.
Lemma lem5410189 : term314 = True.
Proof. exact (TRANS (@lem5410184) (@lem5410188)). Qed.
Lemma lem5410190 : True = term314.
Proof. exact (SYM (@lem5410189)). Qed.
Lemma lem5410191 : term314.
Proof. exact (EQ_MP (@lem5410190) (@lem0)). Qed.
Lemma lem5410192 : term621.
Proof. exact (@lem5410181 (@lem5410191)). Qed.
Lemma lem5410194 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410195 : term314 = term315.
Proof. exact (@lem5410194 (NUMERAL 0) term79). Qed.
Lemma lem5410196 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410197 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410198 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410197 h1) (fun h1 : term315 = True => @lem5410196)). Qed.
Lemma lem5410199 : term315 = True.
Proof. exact (EQ_MP (@lem5410198) (@lem5410196)). Qed.
Lemma lem5410200 : term314 = True.
Proof. exact (TRANS (@lem5410195) (@lem5410199)). Qed.
Lemma lem5410201 : True = term314.
Proof. exact (SYM (@lem5410200)). Qed.
Lemma lem5410202 : term314.
Proof. exact (EQ_MP (@lem5410201) (@lem0)). Qed.
Lemma lem5410203 : term622.
Proof. exact (@lem5410192 (@lem5410202)). Qed.
Lemma lem5410205 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410206 : term314 = term315.
Proof. exact (@lem5410205 (NUMERAL 0) term79). Qed.
Lemma lem5410207 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410208 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410209 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410208 h1) (fun h1 : term315 = True => @lem5410207)). Qed.
Lemma lem5410210 : term315 = True.
Proof. exact (EQ_MP (@lem5410209) (@lem5410207)). Qed.
Lemma lem5410211 : term314 = True.
Proof. exact (TRANS (@lem5410206) (@lem5410210)). Qed.
Lemma lem5410212 : True = term314.
Proof. exact (SYM (@lem5410211)). Qed.
Lemma lem5410213 : term314.
Proof. exact (EQ_MP (@lem5410212) (@lem0)). Qed.
Lemma lem5410214 : term623.
Proof. exact (@lem5410203 (@lem5410213)). Qed.
Lemma lem5410216 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5410217 : term265 = term266.
Proof. exact (@lem5410216 term79 term79). Qed.
Lemma lem5410218 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410219 : term268 = term79.
Proof. exact (EQ_MP (@lem5410218) (@lem940073)). Qed.
Lemma lem5410220 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410221 : term266 = term193.
Proof. exact (MK_COMB (@lem5410220) (@lem5410219)). Qed.
Lemma lem5410222 : term265 = term193.
Proof. exact (TRANS (@lem5410217) (@lem5410221)). Qed.
Lemma lem5410224 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5410225 : term291 = term296.
Proof. exact (@lem5410224 term79 term79). Qed.
Lemma lem5410226 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410227 : term268 = term79.
Proof. exact (EQ_MP (@lem5410226) (@lem940073)). Qed.
Lemma lem5410228 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410229 : term266 = term193.
Proof. exact (MK_COMB (@lem5410228) (@lem5410227)). Qed.
Lemma lem5410230 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5410231 : term296 = term256.
Proof. exact (MK_COMB (@lem5410230) (@lem5410229)). Qed.
Lemma lem5410232 : term291 = term256.
Proof. exact (TRANS (@lem5410225) (@lem5410231)). Qed.
Lemma lem5410233 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5410234 : term624 = term616.
Proof. exact (MK_COMB (@lem5410233) (@lem5410232)). Qed.
Lemma lem5410235 : term625 = term618.
Proof. exact (MK_COMB (@lem5410234) (@lem5410222)). Qed.
Lemma lem5410237 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5410238 : term618 = term182.
Proof. exact (@lem5410237 term79). Qed.
Lemma lem5410239 : term625 = term182.
Proof. exact (TRANS (@lem5410235) (@lem5410238)). Qed.
Lemma lem5410240 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5410241 : term627 = term403.
Proof. exact (MK_COMB (@lem5410240) (@lem5410239)). Qed.
Lemma lem5410242 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5410243 : term628 = term405.
Proof. exact (MK_COMB (@lem5410241) (@lem5410242)). Qed.
Lemma lem5410245 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5410246 : term405 = term182.
Proof. exact (@lem5410245 term79). Qed.
Lemma lem5410247 : term628 = term182.
Proof. exact (TRANS (@lem5410243) (@lem5410246)). Qed.
Lemma lem5410249 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5410250 : term265 = term266.
Proof. exact (@lem5410249 term79 term79). Qed.
Lemma lem5410251 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410252 : term268 = term79.
Proof. exact (EQ_MP (@lem5410251) (@lem940073)). Qed.
Lemma lem5410253 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410254 : term266 = term193.
Proof. exact (MK_COMB (@lem5410253) (@lem5410252)). Qed.
Lemma lem5410255 : term265 = term193.
Proof. exact (TRANS (@lem5410250) (@lem5410254)). Qed.
Lemma lem5410256 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5410257 : term407 = term405.
Proof. exact (MK_COMB (@lem5410256) (@lem5410255)). Qed.
Lemma lem5410259 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5410260 : term405 = term182.
Proof. exact (@lem5410259 term79). Qed.
Lemma lem5410261 : term407 = term182.
Proof. exact (TRANS (@lem5410257) (@lem5410260)). Qed.
Lemma lem5410262 : term182 = term407.
Proof. exact (SYM (@lem5410261)). Qed.
Lemma lem5410263 : term628 = term407.
Proof. exact (TRANS (@lem5410247) (@lem5410262)). Qed.
Lemma lem5410264 : term619 = term253.
Proof. exact (@lem5410214 (@lem5410263)). Qed.
Lemma lem5410265 : term618 = term253.
Proof. exact (TRANS (@lem5410180) (@lem5410264)). Qed.
Lemma lem5410267 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5410268 : term253 = term182.
Proof. exact (@lem5410267 term182). Qed.
Lemma lem5410269 : term618 = term182.
Proof. exact (TRANS (@lem5410265) (@lem5410268)). Qed.
Lemma lem5410270 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5410271 : term629 = term403.
Proof. exact (MK_COMB (@lem5410270) (@lem5410269)). Qed.
Lemma lem5410272 (_69903 : int) : (real_of_int _69903) = (real_of_int _69903).
Proof. exact (eq_refl (real_of_int _69903)). Qed.
Lemma lem5410273 (_69903 : int) : (term615 _69903) = (term630 _69903).
Proof. exact (MK_COMB (@lem5410271) (@lem5410272 _69903)). Qed.
Lemma lem5410274 (_69903 : int) : (term667 _69903) = (term630 _69903).
Proof. exact (TRANS (@lem5410171 _69903) (@lem5410273 _69903)). Qed.
Lemma lem5410275 (_69903 : int) : (term630 _69903) = term182.
Proof. exact (@lem1982719 (real_of_int _69903)). Qed.
Lemma lem5410276 (_69903 : int) : (term667 _69903) = term182.
Proof. exact (TRANS (@lem5410274 _69903) (@lem5410275 _69903)). Qed.
Lemma lem5410277 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5410278 (_69903 : int) : (term668 _69903) = term632.
Proof. exact (MK_COMB (@lem5410277) (@lem5410276 _69903)). Qed.
Lemma lem5410279 (_69905 : int) : (term742 _69905) = (term743 _69905).
Proof. exact (@lem1982763 (real_of_int _69905) (term281 _69905) term256). Qed.
Lemma lem5410280 (_69905 : int) : (term614 _69905) = (term615 _69905).
Proof. exact (@lem1982715 term256 (real_of_int _69905)). Qed.
Lemma lem5410282 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410283 : term193 = term290.
Proof. exact (@lem5410282 term79). Qed.
Lemma lem5410285 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5410286 : term256 = term257.
Proof. exact (@lem5410285 term79). Qed.
Lemma lem5410287 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5410288 : term616 = term617.
Proof. exact (MK_COMB (@lem5410287) (@lem5410286)). Qed.
Lemma lem5410289 : term618 = term619.
Proof. exact (MK_COMB (@lem5410288) (@lem5410283)). Qed.
Lemma lem5410290 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5410292 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410293 : term314 = term315.
Proof. exact (@lem5410292 (NUMERAL 0) term79). Qed.
Lemma lem5410294 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410295 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410296 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410295 h1) (fun h1 : term315 = True => @lem5410294)). Qed.
Lemma lem5410297 : term315 = True.
Proof. exact (EQ_MP (@lem5410296) (@lem5410294)). Qed.
Lemma lem5410298 : term314 = True.
Proof. exact (TRANS (@lem5410293) (@lem5410297)). Qed.
Lemma lem5410299 : True = term314.
Proof. exact (SYM (@lem5410298)). Qed.
Lemma lem5410300 : term314.
Proof. exact (EQ_MP (@lem5410299) (@lem0)). Qed.
Lemma lem5410301 : term621.
Proof. exact (@lem5410290 (@lem5410300)). Qed.
Lemma lem5410303 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410304 : term314 = term315.
Proof. exact (@lem5410303 (NUMERAL 0) term79). Qed.
Lemma lem5410305 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410306 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410307 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410306 h1) (fun h1 : term315 = True => @lem5410305)). Qed.
Lemma lem5410308 : term315 = True.
Proof. exact (EQ_MP (@lem5410307) (@lem5410305)). Qed.
Lemma lem5410309 : term314 = True.
Proof. exact (TRANS (@lem5410304) (@lem5410308)). Qed.
Lemma lem5410310 : True = term314.
Proof. exact (SYM (@lem5410309)). Qed.
Lemma lem5410311 : term314.
Proof. exact (EQ_MP (@lem5410310) (@lem0)). Qed.
Lemma lem5410312 : term622.
Proof. exact (@lem5410301 (@lem5410311)). Qed.
Lemma lem5410314 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410315 : term314 = term315.
Proof. exact (@lem5410314 (NUMERAL 0) term79). Qed.
Lemma lem5410316 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410317 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410318 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410317 h1) (fun h1 : term315 = True => @lem5410316)). Qed.
Lemma lem5410319 : term315 = True.
Proof. exact (EQ_MP (@lem5410318) (@lem5410316)). Qed.
Lemma lem5410320 : term314 = True.
Proof. exact (TRANS (@lem5410315) (@lem5410319)). Qed.
Lemma lem5410321 : True = term314.
Proof. exact (SYM (@lem5410320)). Qed.
Lemma lem5410322 : term314.
Proof. exact (EQ_MP (@lem5410321) (@lem0)). Qed.
Lemma lem5410323 : term623.
Proof. exact (@lem5410312 (@lem5410322)). Qed.
Lemma lem5410325 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5410326 : term265 = term266.
Proof. exact (@lem5410325 term79 term79). Qed.
Lemma lem5410327 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410328 : term268 = term79.
Proof. exact (EQ_MP (@lem5410327) (@lem940073)). Qed.
Lemma lem5410329 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410330 : term266 = term193.
Proof. exact (MK_COMB (@lem5410329) (@lem5410328)). Qed.
Lemma lem5410331 : term265 = term193.
Proof. exact (TRANS (@lem5410326) (@lem5410330)). Qed.
Lemma lem5410333 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5410334 : term291 = term296.
Proof. exact (@lem5410333 term79 term79). Qed.
Lemma lem5410335 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410336 : term268 = term79.
Proof. exact (EQ_MP (@lem5410335) (@lem940073)). Qed.
Lemma lem5410337 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410338 : term266 = term193.
Proof. exact (MK_COMB (@lem5410337) (@lem5410336)). Qed.
Lemma lem5410339 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5410340 : term296 = term256.
Proof. exact (MK_COMB (@lem5410339) (@lem5410338)). Qed.
Lemma lem5410341 : term291 = term256.
Proof. exact (TRANS (@lem5410334) (@lem5410340)). Qed.
Lemma lem5410342 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5410343 : term624 = term616.
Proof. exact (MK_COMB (@lem5410342) (@lem5410341)). Qed.
Lemma lem5410344 : term625 = term618.
Proof. exact (MK_COMB (@lem5410343) (@lem5410331)). Qed.
Lemma lem5410346 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5410347 : term618 = term182.
Proof. exact (@lem5410346 term79). Qed.
Lemma lem5410348 : term625 = term182.
Proof. exact (TRANS (@lem5410344) (@lem5410347)). Qed.
Lemma lem5410349 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5410350 : term627 = term403.
Proof. exact (MK_COMB (@lem5410349) (@lem5410348)). Qed.
Lemma lem5410351 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5410352 : term628 = term405.
Proof. exact (MK_COMB (@lem5410350) (@lem5410351)). Qed.
Lemma lem5410354 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5410355 : term405 = term182.
Proof. exact (@lem5410354 term79). Qed.
Lemma lem5410356 : term628 = term182.
Proof. exact (TRANS (@lem5410352) (@lem5410355)). Qed.
Lemma lem5410358 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5410359 : term265 = term266.
Proof. exact (@lem5410358 term79 term79). Qed.
Lemma lem5410360 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410361 : term268 = term79.
Proof. exact (EQ_MP (@lem5410360) (@lem940073)). Qed.
Lemma lem5410362 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410363 : term266 = term193.
Proof. exact (MK_COMB (@lem5410362) (@lem5410361)). Qed.
Lemma lem5410364 : term265 = term193.
Proof. exact (TRANS (@lem5410359) (@lem5410363)). Qed.
Lemma lem5410365 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5410366 : term407 = term405.
Proof. exact (MK_COMB (@lem5410365) (@lem5410364)). Qed.
Lemma lem5410368 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5410369 : term405 = term182.
Proof. exact (@lem5410368 term79). Qed.
Lemma lem5410370 : term407 = term182.
Proof. exact (TRANS (@lem5410366) (@lem5410369)). Qed.
Lemma lem5410371 : term182 = term407.
Proof. exact (SYM (@lem5410370)). Qed.
Lemma lem5410372 : term628 = term407.
Proof. exact (TRANS (@lem5410356) (@lem5410371)). Qed.
Lemma lem5410373 : term619 = term253.
Proof. exact (@lem5410323 (@lem5410372)). Qed.
Lemma lem5410374 : term618 = term253.
Proof. exact (TRANS (@lem5410289) (@lem5410373)). Qed.
Lemma lem5410376 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5410377 : term253 = term182.
Proof. exact (@lem5410376 term182). Qed.
Lemma lem5410378 : term618 = term182.
Proof. exact (TRANS (@lem5410374) (@lem5410377)). Qed.
Lemma lem5410379 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5410380 : term629 = term403.
Proof. exact (MK_COMB (@lem5410379) (@lem5410378)). Qed.
Lemma lem5410381 (_69905 : int) : (real_of_int _69905) = (real_of_int _69905).
Proof. exact (eq_refl (real_of_int _69905)). Qed.
Lemma lem5410382 (_69905 : int) : (term615 _69905) = (term630 _69905).
Proof. exact (MK_COMB (@lem5410380) (@lem5410381 _69905)). Qed.
Lemma lem5410383 (_69905 : int) : (term614 _69905) = (term630 _69905).
Proof. exact (TRANS (@lem5410280 _69905) (@lem5410382 _69905)). Qed.
Lemma lem5410384 (_69905 : int) : (term630 _69905) = term182.
Proof. exact (@lem1982719 (real_of_int _69905)). Qed.
Lemma lem5410385 (_69905 : int) : (term614 _69905) = term182.
Proof. exact (TRANS (@lem5410383 _69905) (@lem5410384 _69905)). Qed.
Lemma lem5410386 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5410387 (_69905 : int) : (term631 _69905) = term632.
Proof. exact (MK_COMB (@lem5410386) (@lem5410385 _69905)). Qed.
Lemma lem5410388 : term256 = term256.
Proof. exact (eq_refl term256). Qed.
Lemma lem5410389 (_69905 : int) : (term743 _69905) = term682.
Proof. exact (MK_COMB (@lem5410387 _69905) (@lem5410388)). Qed.
Lemma lem5410390 (_69905 : int) : (term742 _69905) = term682.
Proof. exact (TRANS (@lem5410279 _69905) (@lem5410389 _69905)). Qed.
Lemma lem5410391 : term682 = term256.
Proof. exact (@lem1982721 term256). Qed.
Lemma lem5410392 (_69905 : int) : (term742 _69905) = term256.
Proof. exact (TRANS (@lem5410390 _69905) (@lem5410391)). Qed.
Lemma lem5410393 (_69903 : int) (_69905 : int) : (term741 _69903 _69905) = term682.
Proof. exact (MK_COMB (@lem5410278 _69903) (@lem5410392 _69905)). Qed.
Lemma lem5410394 (_69903 : int) (_69905 : int) : (term740 _69903 _69905) = term682.
Proof. exact (TRANS (@lem5410170 _69903 _69905) (@lem5410393 _69903 _69905)). Qed.
Lemma lem5410395 : term682 = term256.
Proof. exact (@lem1982721 term256). Qed.
Lemma lem5410396 (_69903 : int) (_69905 : int) : (term740 _69903 _69905) = term256.
Proof. exact (TRANS (@lem5410394 _69903 _69905) (@lem5410395)). Qed.
Lemma lem5410397 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5410398 (_69903 : int) (_69905 : int) : (term744 _69903 _69905) = term684.
Proof. exact (MK_COMB (@lem5410397) (@lem5410396 _69903 _69905)). Qed.
Lemma lem5410399 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5410400 (_69903 : int) (_69905 : int) : (term739 _69903 _69905) = term685.
Proof. exact (MK_COMB (@lem5410398 _69903 _69905) (@lem5410399)). Qed.
Lemma lem5410401 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : term685.
Proof. exact (EQ_MP (@lem5410400 _69903 _69905) (@lem5410169 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410403 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5410404 : term685 = term686.
Proof. exact (@lem5410403 term182 term256). Qed.
Lemma lem5410406 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5410407 : term256 = term257.
Proof. exact (@lem5410406 term79). Qed.
Lemma lem5410409 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410410 : term182 = term253.
Proof. exact (@lem5410409 (NUMERAL 0)). Qed.
Lemma lem5410411 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5410412 : term184 = term687.
Proof. exact (MK_COMB (@lem5410411) (@lem5410410)). Qed.
Lemma lem5410413 : term686 = term688.
Proof. exact (MK_COMB (@lem5410412) (@lem5410407)). Qed.
Lemma lem5410414 : term689.
Proof. exact (@lem1980026 term182 term193 term256 term193). Qed.
Lemma lem5410416 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410417 : term314 = term315.
Proof. exact (@lem5410416 (NUMERAL 0) term79). Qed.
Lemma lem5410418 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410419 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410420 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410419 h1) (fun h1 : term315 = True => @lem5410418)). Qed.
Lemma lem5410421 : term315 = True.
Proof. exact (EQ_MP (@lem5410420) (@lem5410418)). Qed.
Lemma lem5410422 : term314 = True.
Proof. exact (TRANS (@lem5410417) (@lem5410421)). Qed.
Lemma lem5410423 : True = term314.
Proof. exact (SYM (@lem5410422)). Qed.
Lemma lem5410424 : term314.
Proof. exact (EQ_MP (@lem5410423) (@lem0)). Qed.
Lemma lem5410425 : term690.
Proof. exact (@lem5410414 (@lem5410424)). Qed.
Lemma lem5410427 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410428 : term314 = term315.
Proof. exact (@lem5410427 (NUMERAL 0) term79). Qed.
Lemma lem5410429 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410430 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410431 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410430 h1) (fun h1 : term315 = True => @lem5410429)). Qed.
Lemma lem5410432 : term315 = True.
Proof. exact (EQ_MP (@lem5410431) (@lem5410429)). Qed.
Lemma lem5410433 : term314 = True.
Proof. exact (TRANS (@lem5410428) (@lem5410432)). Qed.
Lemma lem5410434 : True = term314.
Proof. exact (SYM (@lem5410433)). Qed.
Lemma lem5410435 : term314.
Proof. exact (EQ_MP (@lem5410434) (@lem0)). Qed.
Lemma lem5410436 : term688 = term691.
Proof. exact (@lem5410425 (@lem5410435)). Qed.
Lemma lem5410438 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5410439 : term291 = term296.
Proof. exact (@lem5410438 term79 term79). Qed.
Lemma lem5410440 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410441 : term268 = term79.
Proof. exact (EQ_MP (@lem5410440) (@lem940073)). Qed.
Lemma lem5410442 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410443 : term266 = term193.
Proof. exact (MK_COMB (@lem5410442) (@lem5410441)). Qed.
Lemma lem5410444 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5410445 : term296 = term256.
Proof. exact (MK_COMB (@lem5410444) (@lem5410443)). Qed.
Lemma lem5410446 : term291 = term256.
Proof. exact (TRANS (@lem5410439) (@lem5410445)). Qed.
Lemma lem5410448 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5410449 : term405 = term182.
Proof. exact (@lem5410448 term79). Qed.
Lemma lem5410450 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5410451 : term692 = term184.
Proof. exact (MK_COMB (@lem5410450) (@lem5410449)). Qed.
Lemma lem5410452 : term691 = term686.
Proof. exact (MK_COMB (@lem5410451) (@lem5410446)). Qed.
Lemma lem5410454 (m : nat) (n : nat) : (term693 m n) = (term694 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5410455 : term686 = term695.
Proof. exact (@lem5410454 (NUMERAL 0) term79). Qed.
Lemma lem5410456 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410457 (h1 : term316 = (BIT1 0)) : (term79 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5410458 : (term316 = (BIT1 0)) = ((term79 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410457 h1) (fun h1 : (term79 = (NUMERAL 0)) = False => @lem5410456)). Qed.
Lemma lem5410459 : (term79 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5410458) (@lem5410456)). Qed.
Lemma lem5410460 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5410461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5410462 : term696 = (and True).
Proof. exact (MK_COMB (@lem5410461) (@lem5410460)). Qed.
Lemma lem5410463 : term695 = (True /\ False).
Proof. exact (MK_COMB (@lem5410462) (@lem5410459)). Qed.
Lemma lem5410465 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5410466 : term695 = False.
Proof. exact (TRANS (@lem5410463) (@lem5410465)). Qed.
Lemma lem5410467 : term686 = False.
Proof. exact (TRANS (@lem5410455) (@lem5410466)). Qed.
Lemma lem5410468 : term691 = False.
Proof. exact (TRANS (@lem5410452) (@lem5410467)). Qed.
Lemma lem5410469 : term688 = False.
Proof. exact (TRANS (@lem5410436) (@lem5410468)). Qed.
Lemma lem5410470 : term686 = False.
Proof. exact (TRANS (@lem5410413) (@lem5410469)). Qed.
Lemma lem5410471 : term685 = False.
Proof. exact (TRANS (@lem5410404) (@lem5410470)). Qed.
Lemma lem5410472 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term731 _69903 _69904 _69905) : False.
Proof. exact (EQ_MP (@lem5410471) (@lem5410401 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410473 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term745 _69903 _69904 _69905.
Proof. exact (h1). Qed.
Lemma lem5410474 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term571 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5410473 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410476 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term540 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5410474 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410478 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term509 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5410476 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410480 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term478 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5410478 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410482 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term375 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5410480 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410483 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term359 _69904 _69905.
Proof. exact (proj1 (@lem5410480 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410484 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term373 _69904 _69905.
Proof. exact (proj2 (@lem5410482 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410487 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5410488 : term583 = term314.
Proof. exact (@lem5410487 term182 term193). Qed.
Lemma lem5410490 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410491 : term193 = term290.
Proof. exact (@lem5410490 term79). Qed.
Lemma lem5410493 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410494 : term182 = term253.
Proof. exact (@lem5410493 (NUMERAL 0)). Qed.
Lemma lem5410495 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5410496 : term584 = term585.
Proof. exact (MK_COMB (@lem5410495) (@lem5410494)). Qed.
Lemma lem5410497 : term314 = term586.
Proof. exact (MK_COMB (@lem5410496) (@lem5410491)). Qed.
Lemma lem5410498 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5410500 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410501 : term314 = term315.
Proof. exact (@lem5410500 (NUMERAL 0) term79). Qed.
Lemma lem5410502 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410503 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410504 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410503 h1) (fun h1 : term315 = True => @lem5410502)). Qed.
Lemma lem5410505 : term315 = True.
Proof. exact (EQ_MP (@lem5410504) (@lem5410502)). Qed.
Lemma lem5410506 : term314 = True.
Proof. exact (TRANS (@lem5410501) (@lem5410505)). Qed.
Lemma lem5410507 : True = term314.
Proof. exact (SYM (@lem5410506)). Qed.
Lemma lem5410508 : term314.
Proof. exact (EQ_MP (@lem5410507) (@lem0)). Qed.
Lemma lem5410509 : term588.
Proof. exact (@lem5410498 (@lem5410508)). Qed.
Lemma lem5410511 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410512 : term314 = term315.
Proof. exact (@lem5410511 (NUMERAL 0) term79). Qed.
Lemma lem5410513 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410514 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410515 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410514 h1) (fun h1 : term315 = True => @lem5410513)). Qed.
Lemma lem5410516 : term315 = True.
Proof. exact (EQ_MP (@lem5410515) (@lem5410513)). Qed.
Lemma lem5410517 : term314 = True.
Proof. exact (TRANS (@lem5410512) (@lem5410516)). Qed.
Lemma lem5410518 : True = term314.
Proof. exact (SYM (@lem5410517)). Qed.
Lemma lem5410519 : term314.
Proof. exact (EQ_MP (@lem5410518) (@lem0)). Qed.
Lemma lem5410520 : term586 = term589.
Proof. exact (@lem5410509 (@lem5410519)). Qed.
Lemma lem5410522 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5410523 : term265 = term266.
Proof. exact (@lem5410522 term79 term79). Qed.
Lemma lem5410524 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410525 : term268 = term79.
Proof. exact (EQ_MP (@lem5410524) (@lem940073)). Qed.
Lemma lem5410526 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410527 : term266 = term193.
Proof. exact (MK_COMB (@lem5410526) (@lem5410525)). Qed.
Lemma lem5410528 : term265 = term193.
Proof. exact (TRANS (@lem5410523) (@lem5410527)). Qed.
Lemma lem5410530 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5410531 : term405 = term182.
Proof. exact (@lem5410530 term79). Qed.
Lemma lem5410532 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5410533 : term590 = term584.
Proof. exact (MK_COMB (@lem5410532) (@lem5410531)). Qed.
Lemma lem5410534 : term589 = term314.
Proof. exact (MK_COMB (@lem5410533) (@lem5410528)). Qed.
Lemma lem5410536 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410537 : term314 = term315.
Proof. exact (@lem5410536 (NUMERAL 0) term79). Qed.
Lemma lem5410538 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410539 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410540 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410539 h1) (fun h1 : term315 = True => @lem5410538)). Qed.
Lemma lem5410541 : term315 = True.
Proof. exact (EQ_MP (@lem5410540) (@lem5410538)). Qed.
Lemma lem5410542 : term314 = True.
Proof. exact (TRANS (@lem5410537) (@lem5410541)). Qed.
Lemma lem5410543 : term589 = True.
Proof. exact (TRANS (@lem5410534) (@lem5410542)). Qed.
Lemma lem5410544 : term586 = True.
Proof. exact (TRANS (@lem5410520) (@lem5410543)). Qed.
Lemma lem5410545 : term314 = True.
Proof. exact (TRANS (@lem5410497) (@lem5410544)). Qed.
Lemma lem5410546 : term583 = True.
Proof. exact (TRANS (@lem5410488) (@lem5410545)). Qed.
Lemma lem5410547 : True = term583.
Proof. exact (SYM (@lem5410546)). Qed.
Lemma lem5410548 : term583.
Proof. exact (EQ_MP (@lem5410547) (@lem0)). Qed.
Lemma lem5410549 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term746 _69904 _69905.
Proof. exact (conj (@lem5410548) (@lem5410484 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410551 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5410552 (_69904 : int) (_69905 : int) : term747 _69904 _69905.
Proof. exact (@lem5410551 term193 (term367 _69904 _69905)). Qed.
Lemma lem5410553 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term748 _69904 _69905.
Proof. exact (@lem5410552 _69904 _69905 (@lem5410549 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410554 (_69904 : int) (_69905 : int) : (term749 _69904 _69905) = (term367 _69904 _69905).
Proof. exact (@lem1982733 (term367 _69904 _69905)). Qed.
Lemma lem5410555 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5410556 (_69904 : int) (_69905 : int) : (term750 _69904 _69905) = (term372 _69904 _69905).
Proof. exact (MK_COMB (@lem5410555) (@lem5410554 _69904 _69905)). Qed.
Lemma lem5410557 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5410558 (_69904 : int) (_69905 : int) : (term748 _69904 _69905) = (term373 _69904 _69905).
Proof. exact (MK_COMB (@lem5410556 _69904 _69905) (@lem5410557)). Qed.
Lemma lem5410559 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term373 _69904 _69905.
Proof. exact (EQ_MP (@lem5410558 _69904 _69905) (@lem5410553 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410561 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5410562 : term583 = term314.
Proof. exact (@lem5410561 term182 term193). Qed.
Lemma lem5410564 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410565 : term193 = term290.
Proof. exact (@lem5410564 term79). Qed.
Lemma lem5410567 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410568 : term182 = term253.
Proof. exact (@lem5410567 (NUMERAL 0)). Qed.
Lemma lem5410569 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5410570 : term584 = term585.
Proof. exact (MK_COMB (@lem5410569) (@lem5410568)). Qed.
Lemma lem5410571 : term314 = term586.
Proof. exact (MK_COMB (@lem5410570) (@lem5410565)). Qed.
Lemma lem5410572 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5410574 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410575 : term314 = term315.
Proof. exact (@lem5410574 (NUMERAL 0) term79). Qed.
Lemma lem5410576 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410577 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410578 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410577 h1) (fun h1 : term315 = True => @lem5410576)). Qed.
Lemma lem5410579 : term315 = True.
Proof. exact (EQ_MP (@lem5410578) (@lem5410576)). Qed.
Lemma lem5410580 : term314 = True.
Proof. exact (TRANS (@lem5410575) (@lem5410579)). Qed.
Lemma lem5410581 : True = term314.
Proof. exact (SYM (@lem5410580)). Qed.
Lemma lem5410582 : term314.
Proof. exact (EQ_MP (@lem5410581) (@lem0)). Qed.
Lemma lem5410583 : term588.
Proof. exact (@lem5410572 (@lem5410582)). Qed.
Lemma lem5410585 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410586 : term314 = term315.
Proof. exact (@lem5410585 (NUMERAL 0) term79). Qed.
Lemma lem5410587 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410588 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410589 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410588 h1) (fun h1 : term315 = True => @lem5410587)). Qed.
Lemma lem5410590 : term315 = True.
Proof. exact (EQ_MP (@lem5410589) (@lem5410587)). Qed.
Lemma lem5410591 : term314 = True.
Proof. exact (TRANS (@lem5410586) (@lem5410590)). Qed.
Lemma lem5410592 : True = term314.
Proof. exact (SYM (@lem5410591)). Qed.
Lemma lem5410593 : term314.
Proof. exact (EQ_MP (@lem5410592) (@lem0)). Qed.
Lemma lem5410594 : term586 = term589.
Proof. exact (@lem5410583 (@lem5410593)). Qed.
Lemma lem5410596 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5410597 : term265 = term266.
Proof. exact (@lem5410596 term79 term79). Qed.
Lemma lem5410598 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410599 : term268 = term79.
Proof. exact (EQ_MP (@lem5410598) (@lem940073)). Qed.
Lemma lem5410600 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410601 : term266 = term193.
Proof. exact (MK_COMB (@lem5410600) (@lem5410599)). Qed.
Lemma lem5410602 : term265 = term193.
Proof. exact (TRANS (@lem5410597) (@lem5410601)). Qed.
Lemma lem5410604 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5410605 : term405 = term182.
Proof. exact (@lem5410604 term79). Qed.
Lemma lem5410606 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5410607 : term590 = term584.
Proof. exact (MK_COMB (@lem5410606) (@lem5410605)). Qed.
Lemma lem5410608 : term589 = term314.
Proof. exact (MK_COMB (@lem5410607) (@lem5410602)). Qed.
Lemma lem5410610 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410611 : term314 = term315.
Proof. exact (@lem5410610 (NUMERAL 0) term79). Qed.
Lemma lem5410612 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410613 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410614 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410613 h1) (fun h1 : term315 = True => @lem5410612)). Qed.
Lemma lem5410615 : term315 = True.
Proof. exact (EQ_MP (@lem5410614) (@lem5410612)). Qed.
Lemma lem5410616 : term314 = True.
Proof. exact (TRANS (@lem5410611) (@lem5410615)). Qed.
Lemma lem5410617 : term589 = True.
Proof. exact (TRANS (@lem5410608) (@lem5410616)). Qed.
Lemma lem5410618 : term586 = True.
Proof. exact (TRANS (@lem5410594) (@lem5410617)). Qed.
Lemma lem5410619 : term314 = True.
Proof. exact (TRANS (@lem5410571) (@lem5410618)). Qed.
Lemma lem5410620 : term583 = True.
Proof. exact (TRANS (@lem5410562) (@lem5410619)). Qed.
Lemma lem5410621 : True = term583.
Proof. exact (SYM (@lem5410620)). Qed.
Lemma lem5410622 : term583.
Proof. exact (EQ_MP (@lem5410621) (@lem0)). Qed.
Lemma lem5410623 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term698 _69904 _69905.
Proof. exact (conj (@lem5410622) (@lem5410483 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410625 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5410626 (_69904 : int) (_69905 : int) : term699 _69904 _69905.
Proof. exact (@lem5410625 term193 (term356 _69904 _69905)). Qed.
Lemma lem5410627 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term700 _69904 _69905.
Proof. exact (@lem5410626 _69904 _69905 (@lem5410623 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410628 (_69904 : int) (_69905 : int) : (term701 _69904 _69905) = (term356 _69904 _69905).
Proof. exact (@lem1982733 (term356 _69904 _69905)). Qed.
Lemma lem5410629 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5410630 (_69904 : int) (_69905 : int) : (term702 _69904 _69905) = (term358 _69904 _69905).
Proof. exact (MK_COMB (@lem5410629) (@lem5410628 _69904 _69905)). Qed.
Lemma lem5410631 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5410632 (_69904 : int) (_69905 : int) : (term700 _69904 _69905) = (term359 _69904 _69905).
Proof. exact (MK_COMB (@lem5410630 _69904 _69905) (@lem5410631)). Qed.
Lemma lem5410633 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term359 _69904 _69905.
Proof. exact (EQ_MP (@lem5410632 _69904 _69905) (@lem5410627 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410634 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term751 _69904 _69905.
Proof. exact (conj (@lem5410633 _69903 _69904 _69905 h1) (@lem5410559 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410636 (x : real) (y : real) : term662 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5410637 (_69904 : int) (_69905 : int) : term752 _69904 _69905.
Proof. exact (@lem5410636 (term356 _69904 _69905) (term367 _69904 _69905)). Qed.
Lemma lem5410638 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term753 _69904 _69905.
Proof. exact (@lem5410637 _69904 _69905 (@lem5410634 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410639 (_69904 : int) (_69905 : int) : (term754 _69904 _69905) = (term755 _69904 _69905).
Proof. exact (@lem1982753 (term281 _69904) (real_of_int _69904) (term727 _69905) (term281 _69905)). Qed.
Lemma lem5410640 (_69904 : int) : (term667 _69904) = (term615 _69904).
Proof. exact (@lem1982713 term256 (real_of_int _69904)). Qed.
Lemma lem5410642 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410643 : term193 = term290.
Proof. exact (@lem5410642 term79). Qed.
Lemma lem5410645 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5410646 : term256 = term257.
Proof. exact (@lem5410645 term79). Qed.
Lemma lem5410647 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5410648 : term616 = term617.
Proof. exact (MK_COMB (@lem5410647) (@lem5410646)). Qed.
Lemma lem5410649 : term618 = term619.
Proof. exact (MK_COMB (@lem5410648) (@lem5410643)). Qed.
Lemma lem5410650 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5410652 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410653 : term314 = term315.
Proof. exact (@lem5410652 (NUMERAL 0) term79). Qed.
Lemma lem5410654 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410655 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410656 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410655 h1) (fun h1 : term315 = True => @lem5410654)). Qed.
Lemma lem5410657 : term315 = True.
Proof. exact (EQ_MP (@lem5410656) (@lem5410654)). Qed.
Lemma lem5410658 : term314 = True.
Proof. exact (TRANS (@lem5410653) (@lem5410657)). Qed.
Lemma lem5410659 : True = term314.
Proof. exact (SYM (@lem5410658)). Qed.
Lemma lem5410660 : term314.
Proof. exact (EQ_MP (@lem5410659) (@lem0)). Qed.
Lemma lem5410661 : term621.
Proof. exact (@lem5410650 (@lem5410660)). Qed.
Lemma lem5410663 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410664 : term314 = term315.
Proof. exact (@lem5410663 (NUMERAL 0) term79). Qed.
Lemma lem5410665 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410666 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410667 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410666 h1) (fun h1 : term315 = True => @lem5410665)). Qed.
Lemma lem5410668 : term315 = True.
Proof. exact (EQ_MP (@lem5410667) (@lem5410665)). Qed.
Lemma lem5410669 : term314 = True.
Proof. exact (TRANS (@lem5410664) (@lem5410668)). Qed.
Lemma lem5410670 : True = term314.
Proof. exact (SYM (@lem5410669)). Qed.
Lemma lem5410671 : term314.
Proof. exact (EQ_MP (@lem5410670) (@lem0)). Qed.
Lemma lem5410672 : term622.
Proof. exact (@lem5410661 (@lem5410671)). Qed.
Lemma lem5410674 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410675 : term314 = term315.
Proof. exact (@lem5410674 (NUMERAL 0) term79). Qed.
Lemma lem5410676 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410677 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410678 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410677 h1) (fun h1 : term315 = True => @lem5410676)). Qed.
Lemma lem5410679 : term315 = True.
Proof. exact (EQ_MP (@lem5410678) (@lem5410676)). Qed.
Lemma lem5410680 : term314 = True.
Proof. exact (TRANS (@lem5410675) (@lem5410679)). Qed.
Lemma lem5410681 : True = term314.
Proof. exact (SYM (@lem5410680)). Qed.
Lemma lem5410682 : term314.
Proof. exact (EQ_MP (@lem5410681) (@lem0)). Qed.
Lemma lem5410683 : term623.
Proof. exact (@lem5410672 (@lem5410682)). Qed.
Lemma lem5410685 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5410686 : term265 = term266.
Proof. exact (@lem5410685 term79 term79). Qed.
Lemma lem5410687 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410688 : term268 = term79.
Proof. exact (EQ_MP (@lem5410687) (@lem940073)). Qed.
Lemma lem5410689 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410690 : term266 = term193.
Proof. exact (MK_COMB (@lem5410689) (@lem5410688)). Qed.
Lemma lem5410691 : term265 = term193.
Proof. exact (TRANS (@lem5410686) (@lem5410690)). Qed.
Lemma lem5410693 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5410694 : term291 = term296.
Proof. exact (@lem5410693 term79 term79). Qed.
Lemma lem5410695 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410696 : term268 = term79.
Proof. exact (EQ_MP (@lem5410695) (@lem940073)). Qed.
Lemma lem5410697 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410698 : term266 = term193.
Proof. exact (MK_COMB (@lem5410697) (@lem5410696)). Qed.
Lemma lem5410699 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5410700 : term296 = term256.
Proof. exact (MK_COMB (@lem5410699) (@lem5410698)). Qed.
Lemma lem5410701 : term291 = term256.
Proof. exact (TRANS (@lem5410694) (@lem5410700)). Qed.
Lemma lem5410702 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5410703 : term624 = term616.
Proof. exact (MK_COMB (@lem5410702) (@lem5410701)). Qed.
Lemma lem5410704 : term625 = term618.
Proof. exact (MK_COMB (@lem5410703) (@lem5410691)). Qed.
Lemma lem5410706 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5410707 : term618 = term182.
Proof. exact (@lem5410706 term79). Qed.
Lemma lem5410708 : term625 = term182.
Proof. exact (TRANS (@lem5410704) (@lem5410707)). Qed.
Lemma lem5410709 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5410710 : term627 = term403.
Proof. exact (MK_COMB (@lem5410709) (@lem5410708)). Qed.
Lemma lem5410711 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5410712 : term628 = term405.
Proof. exact (MK_COMB (@lem5410710) (@lem5410711)). Qed.
Lemma lem5410714 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5410715 : term405 = term182.
Proof. exact (@lem5410714 term79). Qed.
Lemma lem5410716 : term628 = term182.
Proof. exact (TRANS (@lem5410712) (@lem5410715)). Qed.
Lemma lem5410718 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5410719 : term265 = term266.
Proof. exact (@lem5410718 term79 term79). Qed.
Lemma lem5410720 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410721 : term268 = term79.
Proof. exact (EQ_MP (@lem5410720) (@lem940073)). Qed.
Lemma lem5410722 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410723 : term266 = term193.
Proof. exact (MK_COMB (@lem5410722) (@lem5410721)). Qed.
Lemma lem5410724 : term265 = term193.
Proof. exact (TRANS (@lem5410719) (@lem5410723)). Qed.
Lemma lem5410725 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5410726 : term407 = term405.
Proof. exact (MK_COMB (@lem5410725) (@lem5410724)). Qed.
Lemma lem5410728 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5410729 : term405 = term182.
Proof. exact (@lem5410728 term79). Qed.
Lemma lem5410730 : term407 = term182.
Proof. exact (TRANS (@lem5410726) (@lem5410729)). Qed.
Lemma lem5410731 : term182 = term407.
Proof. exact (SYM (@lem5410730)). Qed.
Lemma lem5410732 : term628 = term407.
Proof. exact (TRANS (@lem5410716) (@lem5410731)). Qed.
Lemma lem5410733 : term619 = term253.
Proof. exact (@lem5410683 (@lem5410732)). Qed.
Lemma lem5410734 : term618 = term253.
Proof. exact (TRANS (@lem5410649) (@lem5410733)). Qed.
Lemma lem5410736 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5410737 : term253 = term182.
Proof. exact (@lem5410736 term182). Qed.
Lemma lem5410738 : term618 = term182.
Proof. exact (TRANS (@lem5410734) (@lem5410737)). Qed.
Lemma lem5410739 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5410740 : term629 = term403.
Proof. exact (MK_COMB (@lem5410739) (@lem5410738)). Qed.
Lemma lem5410741 (_69904 : int) : (real_of_int _69904) = (real_of_int _69904).
Proof. exact (eq_refl (real_of_int _69904)). Qed.
Lemma lem5410742 (_69904 : int) : (term615 _69904) = (term630 _69904).
Proof. exact (MK_COMB (@lem5410740) (@lem5410741 _69904)). Qed.
Lemma lem5410743 (_69904 : int) : (term667 _69904) = (term630 _69904).
Proof. exact (TRANS (@lem5410640 _69904) (@lem5410742 _69904)). Qed.
Lemma lem5410744 (_69904 : int) : (term630 _69904) = term182.
Proof. exact (@lem1982719 (real_of_int _69904)). Qed.
Lemma lem5410745 (_69904 : int) : (term667 _69904) = term182.
Proof. exact (TRANS (@lem5410743 _69904) (@lem5410744 _69904)). Qed.
Lemma lem5410746 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5410747 (_69904 : int) : (term668 _69904) = term632.
Proof. exact (MK_COMB (@lem5410746) (@lem5410745 _69904)). Qed.
Lemma lem5410748 (_69905 : int) : (term756 _69905) = (term757 _69905).
Proof. exact (@lem1982759 (real_of_int _69905) (term281 _69905) term350). Qed.
Lemma lem5410749 (_69905 : int) : (term614 _69905) = (term615 _69905).
Proof. exact (@lem1982715 term256 (real_of_int _69905)). Qed.
Lemma lem5410751 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410752 : term193 = term290.
Proof. exact (@lem5410751 term79). Qed.
Lemma lem5410754 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5410755 : term256 = term257.
Proof. exact (@lem5410754 term79). Qed.
Lemma lem5410756 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5410757 : term616 = term617.
Proof. exact (MK_COMB (@lem5410756) (@lem5410755)). Qed.
Lemma lem5410758 : term618 = term619.
Proof. exact (MK_COMB (@lem5410757) (@lem5410752)). Qed.
Lemma lem5410759 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5410761 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410762 : term314 = term315.
Proof. exact (@lem5410761 (NUMERAL 0) term79). Qed.
Lemma lem5410763 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410764 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410765 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410764 h1) (fun h1 : term315 = True => @lem5410763)). Qed.
Lemma lem5410766 : term315 = True.
Proof. exact (EQ_MP (@lem5410765) (@lem5410763)). Qed.
Lemma lem5410767 : term314 = True.
Proof. exact (TRANS (@lem5410762) (@lem5410766)). Qed.
Lemma lem5410768 : True = term314.
Proof. exact (SYM (@lem5410767)). Qed.
Lemma lem5410769 : term314.
Proof. exact (EQ_MP (@lem5410768) (@lem0)). Qed.
Lemma lem5410770 : term621.
Proof. exact (@lem5410759 (@lem5410769)). Qed.
Lemma lem5410772 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410773 : term314 = term315.
Proof. exact (@lem5410772 (NUMERAL 0) term79). Qed.
Lemma lem5410774 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410775 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410776 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410775 h1) (fun h1 : term315 = True => @lem5410774)). Qed.
Lemma lem5410777 : term315 = True.
Proof. exact (EQ_MP (@lem5410776) (@lem5410774)). Qed.
Lemma lem5410778 : term314 = True.
Proof. exact (TRANS (@lem5410773) (@lem5410777)). Qed.
Lemma lem5410779 : True = term314.
Proof. exact (SYM (@lem5410778)). Qed.
Lemma lem5410780 : term314.
Proof. exact (EQ_MP (@lem5410779) (@lem0)). Qed.
Lemma lem5410781 : term622.
Proof. exact (@lem5410770 (@lem5410780)). Qed.
Lemma lem5410783 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410784 : term314 = term315.
Proof. exact (@lem5410783 (NUMERAL 0) term79). Qed.
Lemma lem5410785 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410786 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410787 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410786 h1) (fun h1 : term315 = True => @lem5410785)). Qed.
Lemma lem5410788 : term315 = True.
Proof. exact (EQ_MP (@lem5410787) (@lem5410785)). Qed.
Lemma lem5410789 : term314 = True.
Proof. exact (TRANS (@lem5410784) (@lem5410788)). Qed.
Lemma lem5410790 : True = term314.
Proof. exact (SYM (@lem5410789)). Qed.
Lemma lem5410791 : term314.
Proof. exact (EQ_MP (@lem5410790) (@lem0)). Qed.
Lemma lem5410792 : term623.
Proof. exact (@lem5410781 (@lem5410791)). Qed.
Lemma lem5410794 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5410795 : term265 = term266.
Proof. exact (@lem5410794 term79 term79). Qed.
Lemma lem5410796 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410797 : term268 = term79.
Proof. exact (EQ_MP (@lem5410796) (@lem940073)). Qed.
Lemma lem5410798 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410799 : term266 = term193.
Proof. exact (MK_COMB (@lem5410798) (@lem5410797)). Qed.
Lemma lem5410800 : term265 = term193.
Proof. exact (TRANS (@lem5410795) (@lem5410799)). Qed.
Lemma lem5410802 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5410803 : term291 = term296.
Proof. exact (@lem5410802 term79 term79). Qed.
Lemma lem5410804 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410805 : term268 = term79.
Proof. exact (EQ_MP (@lem5410804) (@lem940073)). Qed.
Lemma lem5410806 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410807 : term266 = term193.
Proof. exact (MK_COMB (@lem5410806) (@lem5410805)). Qed.
Lemma lem5410808 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5410809 : term296 = term256.
Proof. exact (MK_COMB (@lem5410808) (@lem5410807)). Qed.
Lemma lem5410810 : term291 = term256.
Proof. exact (TRANS (@lem5410803) (@lem5410809)). Qed.
Lemma lem5410811 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5410812 : term624 = term616.
Proof. exact (MK_COMB (@lem5410811) (@lem5410810)). Qed.
Lemma lem5410813 : term625 = term618.
Proof. exact (MK_COMB (@lem5410812) (@lem5410800)). Qed.
Lemma lem5410815 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5410816 : term618 = term182.
Proof. exact (@lem5410815 term79). Qed.
Lemma lem5410817 : term625 = term182.
Proof. exact (TRANS (@lem5410813) (@lem5410816)). Qed.
Lemma lem5410818 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5410819 : term627 = term403.
Proof. exact (MK_COMB (@lem5410818) (@lem5410817)). Qed.
Lemma lem5410820 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5410821 : term628 = term405.
Proof. exact (MK_COMB (@lem5410819) (@lem5410820)). Qed.
Lemma lem5410823 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5410824 : term405 = term182.
Proof. exact (@lem5410823 term79). Qed.
Lemma lem5410825 : term628 = term182.
Proof. exact (TRANS (@lem5410821) (@lem5410824)). Qed.
Lemma lem5410827 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5410828 : term265 = term266.
Proof. exact (@lem5410827 term79 term79). Qed.
Lemma lem5410829 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5410830 : term268 = term79.
Proof. exact (EQ_MP (@lem5410829) (@lem940073)). Qed.
Lemma lem5410831 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410832 : term266 = term193.
Proof. exact (MK_COMB (@lem5410831) (@lem5410830)). Qed.
Lemma lem5410833 : term265 = term193.
Proof. exact (TRANS (@lem5410828) (@lem5410832)). Qed.
Lemma lem5410834 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5410835 : term407 = term405.
Proof. exact (MK_COMB (@lem5410834) (@lem5410833)). Qed.
Lemma lem5410837 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5410838 : term405 = term182.
Proof. exact (@lem5410837 term79). Qed.
Lemma lem5410839 : term407 = term182.
Proof. exact (TRANS (@lem5410835) (@lem5410838)). Qed.
Lemma lem5410840 : term182 = term407.
Proof. exact (SYM (@lem5410839)). Qed.
Lemma lem5410841 : term628 = term407.
Proof. exact (TRANS (@lem5410825) (@lem5410840)). Qed.
Lemma lem5410842 : term619 = term253.
Proof. exact (@lem5410792 (@lem5410841)). Qed.
Lemma lem5410843 : term618 = term253.
Proof. exact (TRANS (@lem5410758) (@lem5410842)). Qed.
Lemma lem5410845 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5410846 : term253 = term182.
Proof. exact (@lem5410845 term182). Qed.
Lemma lem5410847 : term618 = term182.
Proof. exact (TRANS (@lem5410843) (@lem5410846)). Qed.
Lemma lem5410848 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5410849 : term629 = term403.
Proof. exact (MK_COMB (@lem5410848) (@lem5410847)). Qed.
Lemma lem5410850 (_69905 : int) : (real_of_int _69905) = (real_of_int _69905).
Proof. exact (eq_refl (real_of_int _69905)). Qed.
Lemma lem5410851 (_69905 : int) : (term615 _69905) = (term630 _69905).
Proof. exact (MK_COMB (@lem5410849) (@lem5410850 _69905)). Qed.
Lemma lem5410852 (_69905 : int) : (term614 _69905) = (term630 _69905).
Proof. exact (TRANS (@lem5410749 _69905) (@lem5410851 _69905)). Qed.
Lemma lem5410853 (_69905 : int) : (term630 _69905) = term182.
Proof. exact (@lem1982719 (real_of_int _69905)). Qed.
Lemma lem5410854 (_69905 : int) : (term614 _69905) = term182.
Proof. exact (TRANS (@lem5410852 _69905) (@lem5410853 _69905)). Qed.
Lemma lem5410855 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5410856 (_69905 : int) : (term631 _69905) = term632.
Proof. exact (MK_COMB (@lem5410855) (@lem5410854 _69905)). Qed.
Lemma lem5410857 : term350 = term350.
Proof. exact (eq_refl term350). Qed.
Lemma lem5410858 (_69905 : int) : (term757 _69905) = term647.
Proof. exact (MK_COMB (@lem5410856 _69905) (@lem5410857)). Qed.
Lemma lem5410859 (_69905 : int) : (term756 _69905) = term647.
Proof. exact (TRANS (@lem5410748 _69905) (@lem5410858 _69905)). Qed.
Lemma lem5410860 : term647 = term350.
Proof. exact (@lem1982721 term350). Qed.
Lemma lem5410861 (_69905 : int) : (term756 _69905) = term350.
Proof. exact (TRANS (@lem5410859 _69905) (@lem5410860)). Qed.
Lemma lem5410862 (_69904 : int) (_69905 : int) : (term755 _69904 _69905) = term647.
Proof. exact (MK_COMB (@lem5410747 _69904) (@lem5410861 _69905)). Qed.
Lemma lem5410863 (_69904 : int) (_69905 : int) : (term754 _69904 _69905) = term647.
Proof. exact (TRANS (@lem5410639 _69904 _69905) (@lem5410862 _69904 _69905)). Qed.
Lemma lem5410864 : term647 = term350.
Proof. exact (@lem1982721 term350). Qed.
Lemma lem5410865 (_69904 : int) (_69905 : int) : (term754 _69904 _69905) = term350.
Proof. exact (TRANS (@lem5410863 _69904 _69905) (@lem5410864)). Qed.
Lemma lem5410866 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5410867 (_69904 : int) (_69905 : int) : (term758 _69904 _69905) = term759.
Proof. exact (MK_COMB (@lem5410866) (@lem5410865 _69904 _69905)). Qed.
Lemma lem5410868 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5410869 (_69904 : int) (_69905 : int) : (term753 _69904 _69905) = term760.
Proof. exact (MK_COMB (@lem5410867 _69904 _69905) (@lem5410868)). Qed.
Lemma lem5410870 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : term760.
Proof. exact (EQ_MP (@lem5410869 _69904 _69905) (@lem5410638 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410872 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5410873 : term760 = term761.
Proof. exact (@lem5410872 term182 term350). Qed.
Lemma lem5410875 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5410876 : term350 = term353.
Proof. exact (@lem5410875 term326). Qed.
Lemma lem5410878 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410879 : term182 = term253.
Proof. exact (@lem5410878 (NUMERAL 0)). Qed.
Lemma lem5410880 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5410881 : term184 = term687.
Proof. exact (MK_COMB (@lem5410880) (@lem5410879)). Qed.
Lemma lem5410882 : term761 = term762.
Proof. exact (MK_COMB (@lem5410881) (@lem5410876)). Qed.
Lemma lem5410883 : term763.
Proof. exact (@lem1980026 term182 term193 term350 term193). Qed.
Lemma lem5410885 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410886 : term314 = term315.
Proof. exact (@lem5410885 (NUMERAL 0) term79). Qed.
Lemma lem5410887 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410888 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410889 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410888 h1) (fun h1 : term315 = True => @lem5410887)). Qed.
Lemma lem5410890 : term315 = True.
Proof. exact (EQ_MP (@lem5410889) (@lem5410887)). Qed.
Lemma lem5410891 : term314 = True.
Proof. exact (TRANS (@lem5410886) (@lem5410890)). Qed.
Lemma lem5410892 : True = term314.
Proof. exact (SYM (@lem5410891)). Qed.
Lemma lem5410893 : term314.
Proof. exact (EQ_MP (@lem5410892) (@lem0)). Qed.
Lemma lem5410894 : term764.
Proof. exact (@lem5410883 (@lem5410893)). Qed.
Lemma lem5410896 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410897 : term314 = term315.
Proof. exact (@lem5410896 (NUMERAL 0) term79). Qed.
Lemma lem5410898 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410899 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410900 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410899 h1) (fun h1 : term315 = True => @lem5410898)). Qed.
Lemma lem5410901 : term315 = True.
Proof. exact (EQ_MP (@lem5410900) (@lem5410898)). Qed.
Lemma lem5410902 : term314 = True.
Proof. exact (TRANS (@lem5410897) (@lem5410901)). Qed.
Lemma lem5410903 : True = term314.
Proof. exact (SYM (@lem5410902)). Qed.
Lemma lem5410904 : term314.
Proof. exact (EQ_MP (@lem5410903) (@lem0)). Qed.
Lemma lem5410905 : term762 = term765.
Proof. exact (@lem5410894 (@lem5410904)). Qed.
Lemma lem5410907 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5410908 : term644 = term645.
Proof. exact (@lem5410907 term326 term79). Qed.
Lemma lem5410909 : term332 = term324.
Proof. exact (@lem996237 term324). Qed.
Lemma lem5410910 : (term332 = term324) = (term333 = term326).
Proof. exact (@lem1007663 term324 (BIT1 0) term324). Qed.
Lemma lem5410911 : term333 = term326.
Proof. exact (EQ_MP (@lem5410910) (@lem5410909)). Qed.
Lemma lem5410912 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5410913 : term331 = term312.
Proof. exact (MK_COMB (@lem5410912) (@lem5410911)). Qed.
Lemma lem5410914 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5410915 : term645 = term350.
Proof. exact (MK_COMB (@lem5410914) (@lem5410913)). Qed.
Lemma lem5410916 : term644 = term350.
Proof. exact (TRANS (@lem5410908) (@lem5410915)). Qed.
Lemma lem5410918 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5410919 : term405 = term182.
Proof. exact (@lem5410918 term79). Qed.
Lemma lem5410920 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5410921 : term692 = term184.
Proof. exact (MK_COMB (@lem5410920) (@lem5410919)). Qed.
Lemma lem5410922 : term765 = term761.
Proof. exact (MK_COMB (@lem5410921) (@lem5410916)). Qed.
Lemma lem5410924 (m : nat) (n : nat) : (term693 m n) = (term694 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5410925 : term761 = term766.
Proof. exact (@lem5410924 (NUMERAL 0) term326). Qed.
Lemma lem5410926 : term767 = term324.
Proof. exact (@lem912803). Qed.
Lemma lem5410927 (h1 : term767 = term324) : (term326 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term324 h1). Qed.
Lemma lem5410928 : (term767 = term324) = ((term326 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term767 = term324 => @lem5410927 h1) (fun h1 : (term326 = (NUMERAL 0)) = False => @lem5410926)). Qed.
Lemma lem5410929 : (term326 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5410928) (@lem5410926)). Qed.
Lemma lem5410930 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5410931 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5410932 : term696 = (and True).
Proof. exact (MK_COMB (@lem5410931) (@lem5410930)). Qed.
Lemma lem5410933 : term766 = (True /\ False).
Proof. exact (MK_COMB (@lem5410932) (@lem5410929)). Qed.
Lemma lem5410935 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5410936 : term766 = False.
Proof. exact (TRANS (@lem5410933) (@lem5410935)). Qed.
Lemma lem5410937 : term761 = False.
Proof. exact (TRANS (@lem5410925) (@lem5410936)). Qed.
Lemma lem5410938 : term765 = False.
Proof. exact (TRANS (@lem5410922) (@lem5410937)). Qed.
Lemma lem5410939 : term762 = False.
Proof. exact (TRANS (@lem5410905) (@lem5410938)). Qed.
Lemma lem5410940 : term761 = False.
Proof. exact (TRANS (@lem5410882) (@lem5410939)). Qed.
Lemma lem5410941 : term760 = False.
Proof. exact (TRANS (@lem5410873) (@lem5410940)). Qed.
Lemma lem5410942 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term745 _69903 _69904 _69905) : False.
Proof. exact (EQ_MP (@lem5410941) (@lem5410870 _69903 _69904 _69905 h1)). Qed.
Lemma lem5410943 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term569 _69903 _69904 _69905) : False.
Proof. exact (or_elim (@lem5410003 _69903 _69904 _69905 h1) (fun h0 : term731 _69903 _69904 _69905 => @lem5410472 _69903 _69904 _69905 h0) (fun h0 : term745 _69903 _69904 _69905 => @lem5410942 _69903 _69904 _69905 h0)). Qed.
Lemma lem5410944 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term578 _69903 _69904 _69905) : False.
Proof. exact (or_elim (@lem5408453 _69903 _69904 _69905 h1) (fun h0 : term573 _69903 _69904 _69905 => @lem5410002 _69903 _69904 _69905 h0) (fun h0 : term569 _69903 _69904 _69905 => @lem5410943 _69903 _69904 _69905 h0)). Qed.
Lemma lem5410945 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term565 _69903 _69904 _69905) : term565 _69903 _69904 _69905.
Proof. exact (h1). Qed.
Lemma lem5410946 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term560 _69904 _69903 _69905) : term560 _69904 _69903 _69905.
Proof. exact (h1). Qed.
Lemma lem5410947 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term768 _69904 _69903 _69905.
Proof. exact (h1). Qed.
Lemma lem5410948 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term561 _69904 _69903 _69905.
Proof. exact (proj2 (@lem5410947 _69904 _69903 _69905 h1)). Qed.
Lemma lem5410950 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term530 _69904 _69903 _69905.
Proof. exact (proj2 (@lem5410948 _69904 _69903 _69905 h1)). Qed.
Lemma lem5410952 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term499 _69904 _69903 _69905.
Proof. exact (proj2 (@lem5410950 _69904 _69903 _69905 h1)). Qed.
Lemma lem5410954 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term468 _69904 _69903 _69905.
Proof. exact (proj2 (@lem5410952 _69904 _69903 _69905 h1)). Qed.
Lemma lem5410956 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term443 _69904 _69903 _69905.
Proof. exact (proj2 (@lem5410954 _69904 _69903 _69905 h1)). Qed.
Lemma lem5410957 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term386 _69903 _69904 _69905.
Proof. exact (proj1 (@lem5410954 _69904 _69903 _69905 h1)). Qed.
Lemma lem5410959 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term371 _69903 _69905.
Proof. exact (proj1 (@lem5410957 _69904 _69903 _69905 h1)). Qed.
Lemma lem5410960 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term304 _69903 _69905.
Proof. exact (proj2 (@lem5410956 _69904 _69903 _69905 h1)). Qed.
Lemma lem5410963 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5410964 : term583 = term314.
Proof. exact (@lem5410963 term182 term193). Qed.
Lemma lem5410966 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410967 : term193 = term290.
Proof. exact (@lem5410966 term79). Qed.
Lemma lem5410969 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5410970 : term182 = term253.
Proof. exact (@lem5410969 (NUMERAL 0)). Qed.
Lemma lem5410971 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5410972 : term584 = term585.
Proof. exact (MK_COMB (@lem5410971) (@lem5410970)). Qed.
Lemma lem5410973 : term314 = term586.
Proof. exact (MK_COMB (@lem5410972) (@lem5410967)). Qed.
Lemma lem5410974 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5410976 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410977 : term314 = term315.
Proof. exact (@lem5410976 (NUMERAL 0) term79). Qed.
Lemma lem5410978 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410979 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410980 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410979 h1) (fun h1 : term315 = True => @lem5410978)). Qed.
Lemma lem5410981 : term315 = True.
Proof. exact (EQ_MP (@lem5410980) (@lem5410978)). Qed.
Lemma lem5410982 : term314 = True.
Proof. exact (TRANS (@lem5410977) (@lem5410981)). Qed.
Lemma lem5410983 : True = term314.
Proof. exact (SYM (@lem5410982)). Qed.
Lemma lem5410984 : term314.
Proof. exact (EQ_MP (@lem5410983) (@lem0)). Qed.
Lemma lem5410985 : term588.
Proof. exact (@lem5410974 (@lem5410984)). Qed.
Lemma lem5410987 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5410988 : term314 = term315.
Proof. exact (@lem5410987 (NUMERAL 0) term79). Qed.
Lemma lem5410989 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5410990 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5410991 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5410990 h1) (fun h1 : term315 = True => @lem5410989)). Qed.
Lemma lem5410992 : term315 = True.
Proof. exact (EQ_MP (@lem5410991) (@lem5410989)). Qed.
Lemma lem5410993 : term314 = True.
Proof. exact (TRANS (@lem5410988) (@lem5410992)). Qed.
Lemma lem5410994 : True = term314.
Proof. exact (SYM (@lem5410993)). Qed.
Lemma lem5410995 : term314.
Proof. exact (EQ_MP (@lem5410994) (@lem0)). Qed.
Lemma lem5410996 : term586 = term589.
Proof. exact (@lem5410985 (@lem5410995)). Qed.
Lemma lem5410998 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5410999 : term265 = term266.
Proof. exact (@lem5410998 term79 term79). Qed.
Lemma lem5411000 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411001 : term268 = term79.
Proof. exact (EQ_MP (@lem5411000) (@lem940073)). Qed.
Lemma lem5411002 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411003 : term266 = term193.
Proof. exact (MK_COMB (@lem5411002) (@lem5411001)). Qed.
Lemma lem5411004 : term265 = term193.
Proof. exact (TRANS (@lem5410999) (@lem5411003)). Qed.
Lemma lem5411006 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5411007 : term405 = term182.
Proof. exact (@lem5411006 term79). Qed.
Lemma lem5411008 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5411009 : term590 = term584.
Proof. exact (MK_COMB (@lem5411008) (@lem5411007)). Qed.
Lemma lem5411010 : term589 = term314.
Proof. exact (MK_COMB (@lem5411009) (@lem5411004)). Qed.
Lemma lem5411012 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411013 : term314 = term315.
Proof. exact (@lem5411012 (NUMERAL 0) term79). Qed.
Lemma lem5411014 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411015 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411016 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411015 h1) (fun h1 : term315 = True => @lem5411014)). Qed.
Lemma lem5411017 : term315 = True.
Proof. exact (EQ_MP (@lem5411016) (@lem5411014)). Qed.
Lemma lem5411018 : term314 = True.
Proof. exact (TRANS (@lem5411013) (@lem5411017)). Qed.
Lemma lem5411019 : term589 = True.
Proof. exact (TRANS (@lem5411010) (@lem5411018)). Qed.
Lemma lem5411020 : term586 = True.
Proof. exact (TRANS (@lem5410996) (@lem5411019)). Qed.
Lemma lem5411021 : term314 = True.
Proof. exact (TRANS (@lem5410973) (@lem5411020)). Qed.
Lemma lem5411022 : term583 = True.
Proof. exact (TRANS (@lem5410964) (@lem5411021)). Qed.
Lemma lem5411023 : True = term583.
Proof. exact (SYM (@lem5411022)). Qed.
Lemma lem5411024 : term583.
Proof. exact (EQ_MP (@lem5411023) (@lem0)). Qed.
Lemma lem5411025 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term591 _69903 _69905.
Proof. exact (conj (@lem5411024) (@lem5410960 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411027 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5411028 (_69903 : int) (_69905 : int) : term593 _69903 _69905.
Proof. exact (@lem5411027 term193 (term301 _69903 _69905)). Qed.
Lemma lem5411029 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term594 _69903 _69905.
Proof. exact (@lem5411028 _69903 _69905 (@lem5411025 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411030 (_69903 : int) (_69905 : int) : (term595 _69903 _69905) = (term301 _69903 _69905).
Proof. exact (@lem1982733 (term301 _69903 _69905)). Qed.
Lemma lem5411031 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5411032 (_69903 : int) (_69905 : int) : (term596 _69903 _69905) = (term303 _69903 _69905).
Proof. exact (MK_COMB (@lem5411031) (@lem5411030 _69903 _69905)). Qed.
Lemma lem5411033 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5411034 (_69903 : int) (_69905 : int) : (term594 _69903 _69905) = (term304 _69903 _69905).
Proof. exact (MK_COMB (@lem5411032 _69903 _69905) (@lem5411033)). Qed.
Lemma lem5411035 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term304 _69903 _69905.
Proof. exact (EQ_MP (@lem5411034 _69903 _69905) (@lem5411029 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411037 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5411038 : term583 = term314.
Proof. exact (@lem5411037 term182 term193). Qed.
Lemma lem5411040 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5411041 : term193 = term290.
Proof. exact (@lem5411040 term79). Qed.
Lemma lem5411043 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5411044 : term182 = term253.
Proof. exact (@lem5411043 (NUMERAL 0)). Qed.
Lemma lem5411045 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5411046 : term584 = term585.
Proof. exact (MK_COMB (@lem5411045) (@lem5411044)). Qed.
Lemma lem5411047 : term314 = term586.
Proof. exact (MK_COMB (@lem5411046) (@lem5411041)). Qed.
Lemma lem5411048 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5411050 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411051 : term314 = term315.
Proof. exact (@lem5411050 (NUMERAL 0) term79). Qed.
Lemma lem5411052 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411053 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411054 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411053 h1) (fun h1 : term315 = True => @lem5411052)). Qed.
Lemma lem5411055 : term315 = True.
Proof. exact (EQ_MP (@lem5411054) (@lem5411052)). Qed.
Lemma lem5411056 : term314 = True.
Proof. exact (TRANS (@lem5411051) (@lem5411055)). Qed.
Lemma lem5411057 : True = term314.
Proof. exact (SYM (@lem5411056)). Qed.
Lemma lem5411058 : term314.
Proof. exact (EQ_MP (@lem5411057) (@lem0)). Qed.
Lemma lem5411059 : term588.
Proof. exact (@lem5411048 (@lem5411058)). Qed.
Lemma lem5411061 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411062 : term314 = term315.
Proof. exact (@lem5411061 (NUMERAL 0) term79). Qed.
Lemma lem5411063 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411064 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411065 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411064 h1) (fun h1 : term315 = True => @lem5411063)). Qed.
Lemma lem5411066 : term315 = True.
Proof. exact (EQ_MP (@lem5411065) (@lem5411063)). Qed.
Lemma lem5411067 : term314 = True.
Proof. exact (TRANS (@lem5411062) (@lem5411066)). Qed.
Lemma lem5411068 : True = term314.
Proof. exact (SYM (@lem5411067)). Qed.
Lemma lem5411069 : term314.
Proof. exact (EQ_MP (@lem5411068) (@lem0)). Qed.
Lemma lem5411070 : term586 = term589.
Proof. exact (@lem5411059 (@lem5411069)). Qed.
Lemma lem5411072 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5411073 : term265 = term266.
Proof. exact (@lem5411072 term79 term79). Qed.
Lemma lem5411074 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411075 : term268 = term79.
Proof. exact (EQ_MP (@lem5411074) (@lem940073)). Qed.
Lemma lem5411076 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411077 : term266 = term193.
Proof. exact (MK_COMB (@lem5411076) (@lem5411075)). Qed.
Lemma lem5411078 : term265 = term193.
Proof. exact (TRANS (@lem5411073) (@lem5411077)). Qed.
Lemma lem5411080 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5411081 : term405 = term182.
Proof. exact (@lem5411080 term79). Qed.
Lemma lem5411082 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5411083 : term590 = term584.
Proof. exact (MK_COMB (@lem5411082) (@lem5411081)). Qed.
Lemma lem5411084 : term589 = term314.
Proof. exact (MK_COMB (@lem5411083) (@lem5411078)). Qed.
Lemma lem5411086 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411087 : term314 = term315.
Proof. exact (@lem5411086 (NUMERAL 0) term79). Qed.
Lemma lem5411088 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411089 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411090 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411089 h1) (fun h1 : term315 = True => @lem5411088)). Qed.
Lemma lem5411091 : term315 = True.
Proof. exact (EQ_MP (@lem5411090) (@lem5411088)). Qed.
Lemma lem5411092 : term314 = True.
Proof. exact (TRANS (@lem5411087) (@lem5411091)). Qed.
Lemma lem5411093 : term589 = True.
Proof. exact (TRANS (@lem5411084) (@lem5411092)). Qed.
Lemma lem5411094 : term586 = True.
Proof. exact (TRANS (@lem5411070) (@lem5411093)). Qed.
Lemma lem5411095 : term314 = True.
Proof. exact (TRANS (@lem5411047) (@lem5411094)). Qed.
Lemma lem5411096 : term583 = True.
Proof. exact (TRANS (@lem5411038) (@lem5411095)). Qed.
Lemma lem5411097 : True = term583.
Proof. exact (SYM (@lem5411096)). Qed.
Lemma lem5411098 : term583.
Proof. exact (EQ_MP (@lem5411097) (@lem0)). Qed.
Lemma lem5411099 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term732 _69903 _69905.
Proof. exact (conj (@lem5411098) (@lem5410959 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411101 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5411102 (_69903 : int) (_69905 : int) : term733 _69903 _69905.
Proof. exact (@lem5411101 term193 (term368 _69903 _69905)). Qed.
Lemma lem5411103 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term734 _69903 _69905.
Proof. exact (@lem5411102 _69903 _69905 (@lem5411099 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411104 (_69903 : int) (_69905 : int) : (term735 _69903 _69905) = (term368 _69903 _69905).
Proof. exact (@lem1982733 (term368 _69903 _69905)). Qed.
Lemma lem5411105 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5411106 (_69903 : int) (_69905 : int) : (term736 _69903 _69905) = (term370 _69903 _69905).
Proof. exact (MK_COMB (@lem5411105) (@lem5411104 _69903 _69905)). Qed.
Lemma lem5411107 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5411108 (_69903 : int) (_69905 : int) : (term734 _69903 _69905) = (term371 _69903 _69905).
Proof. exact (MK_COMB (@lem5411106 _69903 _69905) (@lem5411107)). Qed.
Lemma lem5411109 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term371 _69903 _69905.
Proof. exact (EQ_MP (@lem5411108 _69903 _69905) (@lem5411103 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411110 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term737 _69903 _69905.
Proof. exact (conj (@lem5411109 _69904 _69903 _69905 h1) (@lem5411035 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411112 (x : real) (y : real) : term662 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5411113 (_69903 : int) (_69905 : int) : term738 _69903 _69905.
Proof. exact (@lem5411112 (term368 _69903 _69905) (term301 _69903 _69905)). Qed.
Lemma lem5411114 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term739 _69903 _69905.
Proof. exact (@lem5411113 _69903 _69905 (@lem5411110 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411115 (_69903 : int) (_69905 : int) : (term740 _69903 _69905) = (term741 _69903 _69905).
Proof. exact (@lem1982753 (term281 _69903) (real_of_int _69903) (real_of_int _69905) (term300 _69905)). Qed.
Lemma lem5411116 (_69903 : int) : (term667 _69903) = (term615 _69903).
Proof. exact (@lem1982713 term256 (real_of_int _69903)). Qed.
Lemma lem5411118 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5411119 : term193 = term290.
Proof. exact (@lem5411118 term79). Qed.
Lemma lem5411121 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5411122 : term256 = term257.
Proof. exact (@lem5411121 term79). Qed.
Lemma lem5411123 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5411124 : term616 = term617.
Proof. exact (MK_COMB (@lem5411123) (@lem5411122)). Qed.
Lemma lem5411125 : term618 = term619.
Proof. exact (MK_COMB (@lem5411124) (@lem5411119)). Qed.
Lemma lem5411126 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5411128 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411129 : term314 = term315.
Proof. exact (@lem5411128 (NUMERAL 0) term79). Qed.
Lemma lem5411130 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411131 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411132 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411131 h1) (fun h1 : term315 = True => @lem5411130)). Qed.
Lemma lem5411133 : term315 = True.
Proof. exact (EQ_MP (@lem5411132) (@lem5411130)). Qed.
Lemma lem5411134 : term314 = True.
Proof. exact (TRANS (@lem5411129) (@lem5411133)). Qed.
Lemma lem5411135 : True = term314.
Proof. exact (SYM (@lem5411134)). Qed.
Lemma lem5411136 : term314.
Proof. exact (EQ_MP (@lem5411135) (@lem0)). Qed.
Lemma lem5411137 : term621.
Proof. exact (@lem5411126 (@lem5411136)). Qed.
Lemma lem5411139 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411140 : term314 = term315.
Proof. exact (@lem5411139 (NUMERAL 0) term79). Qed.
Lemma lem5411141 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411142 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411143 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411142 h1) (fun h1 : term315 = True => @lem5411141)). Qed.
Lemma lem5411144 : term315 = True.
Proof. exact (EQ_MP (@lem5411143) (@lem5411141)). Qed.
Lemma lem5411145 : term314 = True.
Proof. exact (TRANS (@lem5411140) (@lem5411144)). Qed.
Lemma lem5411146 : True = term314.
Proof. exact (SYM (@lem5411145)). Qed.
Lemma lem5411147 : term314.
Proof. exact (EQ_MP (@lem5411146) (@lem0)). Qed.
Lemma lem5411148 : term622.
Proof. exact (@lem5411137 (@lem5411147)). Qed.
Lemma lem5411150 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411151 : term314 = term315.
Proof. exact (@lem5411150 (NUMERAL 0) term79). Qed.
Lemma lem5411152 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411153 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411154 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411153 h1) (fun h1 : term315 = True => @lem5411152)). Qed.
Lemma lem5411155 : term315 = True.
Proof. exact (EQ_MP (@lem5411154) (@lem5411152)). Qed.
Lemma lem5411156 : term314 = True.
Proof. exact (TRANS (@lem5411151) (@lem5411155)). Qed.
Lemma lem5411157 : True = term314.
Proof. exact (SYM (@lem5411156)). Qed.
Lemma lem5411158 : term314.
Proof. exact (EQ_MP (@lem5411157) (@lem0)). Qed.
Lemma lem5411159 : term623.
Proof. exact (@lem5411148 (@lem5411158)). Qed.
Lemma lem5411161 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5411162 : term265 = term266.
Proof. exact (@lem5411161 term79 term79). Qed.
Lemma lem5411163 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411164 : term268 = term79.
Proof. exact (EQ_MP (@lem5411163) (@lem940073)). Qed.
Lemma lem5411165 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411166 : term266 = term193.
Proof. exact (MK_COMB (@lem5411165) (@lem5411164)). Qed.
Lemma lem5411167 : term265 = term193.
Proof. exact (TRANS (@lem5411162) (@lem5411166)). Qed.
Lemma lem5411169 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5411170 : term291 = term296.
Proof. exact (@lem5411169 term79 term79). Qed.
Lemma lem5411171 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411172 : term268 = term79.
Proof. exact (EQ_MP (@lem5411171) (@lem940073)). Qed.
Lemma lem5411173 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411174 : term266 = term193.
Proof. exact (MK_COMB (@lem5411173) (@lem5411172)). Qed.
Lemma lem5411175 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5411176 : term296 = term256.
Proof. exact (MK_COMB (@lem5411175) (@lem5411174)). Qed.
Lemma lem5411177 : term291 = term256.
Proof. exact (TRANS (@lem5411170) (@lem5411176)). Qed.
Lemma lem5411178 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5411179 : term624 = term616.
Proof. exact (MK_COMB (@lem5411178) (@lem5411177)). Qed.
Lemma lem5411180 : term625 = term618.
Proof. exact (MK_COMB (@lem5411179) (@lem5411167)). Qed.
Lemma lem5411182 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5411183 : term618 = term182.
Proof. exact (@lem5411182 term79). Qed.
Lemma lem5411184 : term625 = term182.
Proof. exact (TRANS (@lem5411180) (@lem5411183)). Qed.
Lemma lem5411185 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5411186 : term627 = term403.
Proof. exact (MK_COMB (@lem5411185) (@lem5411184)). Qed.
Lemma lem5411187 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5411188 : term628 = term405.
Proof. exact (MK_COMB (@lem5411186) (@lem5411187)). Qed.
Lemma lem5411190 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5411191 : term405 = term182.
Proof. exact (@lem5411190 term79). Qed.
Lemma lem5411192 : term628 = term182.
Proof. exact (TRANS (@lem5411188) (@lem5411191)). Qed.
Lemma lem5411194 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5411195 : term265 = term266.
Proof. exact (@lem5411194 term79 term79). Qed.
Lemma lem5411196 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411197 : term268 = term79.
Proof. exact (EQ_MP (@lem5411196) (@lem940073)). Qed.
Lemma lem5411198 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411199 : term266 = term193.
Proof. exact (MK_COMB (@lem5411198) (@lem5411197)). Qed.
Lemma lem5411200 : term265 = term193.
Proof. exact (TRANS (@lem5411195) (@lem5411199)). Qed.
Lemma lem5411201 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5411202 : term407 = term405.
Proof. exact (MK_COMB (@lem5411201) (@lem5411200)). Qed.
Lemma lem5411204 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5411205 : term405 = term182.
Proof. exact (@lem5411204 term79). Qed.
Lemma lem5411206 : term407 = term182.
Proof. exact (TRANS (@lem5411202) (@lem5411205)). Qed.
Lemma lem5411207 : term182 = term407.
Proof. exact (SYM (@lem5411206)). Qed.
Lemma lem5411208 : term628 = term407.
Proof. exact (TRANS (@lem5411192) (@lem5411207)). Qed.
Lemma lem5411209 : term619 = term253.
Proof. exact (@lem5411159 (@lem5411208)). Qed.
Lemma lem5411210 : term618 = term253.
Proof. exact (TRANS (@lem5411125) (@lem5411209)). Qed.
Lemma lem5411212 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5411213 : term253 = term182.
Proof. exact (@lem5411212 term182). Qed.
Lemma lem5411214 : term618 = term182.
Proof. exact (TRANS (@lem5411210) (@lem5411213)). Qed.
Lemma lem5411215 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5411216 : term629 = term403.
Proof. exact (MK_COMB (@lem5411215) (@lem5411214)). Qed.
Lemma lem5411217 (_69903 : int) : (real_of_int _69903) = (real_of_int _69903).
Proof. exact (eq_refl (real_of_int _69903)). Qed.
Lemma lem5411218 (_69903 : int) : (term615 _69903) = (term630 _69903).
Proof. exact (MK_COMB (@lem5411216) (@lem5411217 _69903)). Qed.
Lemma lem5411219 (_69903 : int) : (term667 _69903) = (term630 _69903).
Proof. exact (TRANS (@lem5411116 _69903) (@lem5411218 _69903)). Qed.
Lemma lem5411220 (_69903 : int) : (term630 _69903) = term182.
Proof. exact (@lem1982719 (real_of_int _69903)). Qed.
Lemma lem5411221 (_69903 : int) : (term667 _69903) = term182.
Proof. exact (TRANS (@lem5411219 _69903) (@lem5411220 _69903)). Qed.
Lemma lem5411222 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5411223 (_69903 : int) : (term668 _69903) = term632.
Proof. exact (MK_COMB (@lem5411222) (@lem5411221 _69903)). Qed.
Lemma lem5411224 (_69905 : int) : (term742 _69905) = (term743 _69905).
Proof. exact (@lem1982763 (real_of_int _69905) (term281 _69905) term256). Qed.
Lemma lem5411225 (_69905 : int) : (term614 _69905) = (term615 _69905).
Proof. exact (@lem1982715 term256 (real_of_int _69905)). Qed.
Lemma lem5411227 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5411228 : term193 = term290.
Proof. exact (@lem5411227 term79). Qed.
Lemma lem5411230 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5411231 : term256 = term257.
Proof. exact (@lem5411230 term79). Qed.
Lemma lem5411232 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5411233 : term616 = term617.
Proof. exact (MK_COMB (@lem5411232) (@lem5411231)). Qed.
Lemma lem5411234 : term618 = term619.
Proof. exact (MK_COMB (@lem5411233) (@lem5411228)). Qed.
Lemma lem5411235 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5411237 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411238 : term314 = term315.
Proof. exact (@lem5411237 (NUMERAL 0) term79). Qed.
Lemma lem5411239 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411240 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411241 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411240 h1) (fun h1 : term315 = True => @lem5411239)). Qed.
Lemma lem5411242 : term315 = True.
Proof. exact (EQ_MP (@lem5411241) (@lem5411239)). Qed.
Lemma lem5411243 : term314 = True.
Proof. exact (TRANS (@lem5411238) (@lem5411242)). Qed.
Lemma lem5411244 : True = term314.
Proof. exact (SYM (@lem5411243)). Qed.
Lemma lem5411245 : term314.
Proof. exact (EQ_MP (@lem5411244) (@lem0)). Qed.
Lemma lem5411246 : term621.
Proof. exact (@lem5411235 (@lem5411245)). Qed.
Lemma lem5411248 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411249 : term314 = term315.
Proof. exact (@lem5411248 (NUMERAL 0) term79). Qed.
Lemma lem5411250 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411251 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411252 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411251 h1) (fun h1 : term315 = True => @lem5411250)). Qed.
Lemma lem5411253 : term315 = True.
Proof. exact (EQ_MP (@lem5411252) (@lem5411250)). Qed.
Lemma lem5411254 : term314 = True.
Proof. exact (TRANS (@lem5411249) (@lem5411253)). Qed.
Lemma lem5411255 : True = term314.
Proof. exact (SYM (@lem5411254)). Qed.
Lemma lem5411256 : term314.
Proof. exact (EQ_MP (@lem5411255) (@lem0)). Qed.
Lemma lem5411257 : term622.
Proof. exact (@lem5411246 (@lem5411256)). Qed.
Lemma lem5411259 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411260 : term314 = term315.
Proof. exact (@lem5411259 (NUMERAL 0) term79). Qed.
Lemma lem5411261 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411262 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411263 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411262 h1) (fun h1 : term315 = True => @lem5411261)). Qed.
Lemma lem5411264 : term315 = True.
Proof. exact (EQ_MP (@lem5411263) (@lem5411261)). Qed.
Lemma lem5411265 : term314 = True.
Proof. exact (TRANS (@lem5411260) (@lem5411264)). Qed.
Lemma lem5411266 : True = term314.
Proof. exact (SYM (@lem5411265)). Qed.
Lemma lem5411267 : term314.
Proof. exact (EQ_MP (@lem5411266) (@lem0)). Qed.
Lemma lem5411268 : term623.
Proof. exact (@lem5411257 (@lem5411267)). Qed.
Lemma lem5411270 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5411271 : term265 = term266.
Proof. exact (@lem5411270 term79 term79). Qed.
Lemma lem5411272 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411273 : term268 = term79.
Proof. exact (EQ_MP (@lem5411272) (@lem940073)). Qed.
Lemma lem5411274 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411275 : term266 = term193.
Proof. exact (MK_COMB (@lem5411274) (@lem5411273)). Qed.
Lemma lem5411276 : term265 = term193.
Proof. exact (TRANS (@lem5411271) (@lem5411275)). Qed.
Lemma lem5411278 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5411279 : term291 = term296.
Proof. exact (@lem5411278 term79 term79). Qed.
Lemma lem5411280 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411281 : term268 = term79.
Proof. exact (EQ_MP (@lem5411280) (@lem940073)). Qed.
Lemma lem5411282 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411283 : term266 = term193.
Proof. exact (MK_COMB (@lem5411282) (@lem5411281)). Qed.
Lemma lem5411284 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5411285 : term296 = term256.
Proof. exact (MK_COMB (@lem5411284) (@lem5411283)). Qed.
Lemma lem5411286 : term291 = term256.
Proof. exact (TRANS (@lem5411279) (@lem5411285)). Qed.
Lemma lem5411287 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5411288 : term624 = term616.
Proof. exact (MK_COMB (@lem5411287) (@lem5411286)). Qed.
Lemma lem5411289 : term625 = term618.
Proof. exact (MK_COMB (@lem5411288) (@lem5411276)). Qed.
Lemma lem5411291 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5411292 : term618 = term182.
Proof. exact (@lem5411291 term79). Qed.
Lemma lem5411293 : term625 = term182.
Proof. exact (TRANS (@lem5411289) (@lem5411292)). Qed.
Lemma lem5411294 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5411295 : term627 = term403.
Proof. exact (MK_COMB (@lem5411294) (@lem5411293)). Qed.
Lemma lem5411296 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5411297 : term628 = term405.
Proof. exact (MK_COMB (@lem5411295) (@lem5411296)). Qed.
Lemma lem5411299 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5411300 : term405 = term182.
Proof. exact (@lem5411299 term79). Qed.
Lemma lem5411301 : term628 = term182.
Proof. exact (TRANS (@lem5411297) (@lem5411300)). Qed.
Lemma lem5411303 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5411304 : term265 = term266.
Proof. exact (@lem5411303 term79 term79). Qed.
Lemma lem5411305 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411306 : term268 = term79.
Proof. exact (EQ_MP (@lem5411305) (@lem940073)). Qed.
Lemma lem5411307 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411308 : term266 = term193.
Proof. exact (MK_COMB (@lem5411307) (@lem5411306)). Qed.
Lemma lem5411309 : term265 = term193.
Proof. exact (TRANS (@lem5411304) (@lem5411308)). Qed.
Lemma lem5411310 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5411311 : term407 = term405.
Proof. exact (MK_COMB (@lem5411310) (@lem5411309)). Qed.
Lemma lem5411313 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5411314 : term405 = term182.
Proof. exact (@lem5411313 term79). Qed.
Lemma lem5411315 : term407 = term182.
Proof. exact (TRANS (@lem5411311) (@lem5411314)). Qed.
Lemma lem5411316 : term182 = term407.
Proof. exact (SYM (@lem5411315)). Qed.
Lemma lem5411317 : term628 = term407.
Proof. exact (TRANS (@lem5411301) (@lem5411316)). Qed.
Lemma lem5411318 : term619 = term253.
Proof. exact (@lem5411268 (@lem5411317)). Qed.
Lemma lem5411319 : term618 = term253.
Proof. exact (TRANS (@lem5411234) (@lem5411318)). Qed.
Lemma lem5411321 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5411322 : term253 = term182.
Proof. exact (@lem5411321 term182). Qed.
Lemma lem5411323 : term618 = term182.
Proof. exact (TRANS (@lem5411319) (@lem5411322)). Qed.
Lemma lem5411324 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5411325 : term629 = term403.
Proof. exact (MK_COMB (@lem5411324) (@lem5411323)). Qed.
Lemma lem5411326 (_69905 : int) : (real_of_int _69905) = (real_of_int _69905).
Proof. exact (eq_refl (real_of_int _69905)). Qed.
Lemma lem5411327 (_69905 : int) : (term615 _69905) = (term630 _69905).
Proof. exact (MK_COMB (@lem5411325) (@lem5411326 _69905)). Qed.
Lemma lem5411328 (_69905 : int) : (term614 _69905) = (term630 _69905).
Proof. exact (TRANS (@lem5411225 _69905) (@lem5411327 _69905)). Qed.
Lemma lem5411329 (_69905 : int) : (term630 _69905) = term182.
Proof. exact (@lem1982719 (real_of_int _69905)). Qed.
Lemma lem5411330 (_69905 : int) : (term614 _69905) = term182.
Proof. exact (TRANS (@lem5411328 _69905) (@lem5411329 _69905)). Qed.
Lemma lem5411331 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5411332 (_69905 : int) : (term631 _69905) = term632.
Proof. exact (MK_COMB (@lem5411331) (@lem5411330 _69905)). Qed.
Lemma lem5411333 : term256 = term256.
Proof. exact (eq_refl term256). Qed.
Lemma lem5411334 (_69905 : int) : (term743 _69905) = term682.
Proof. exact (MK_COMB (@lem5411332 _69905) (@lem5411333)). Qed.
Lemma lem5411335 (_69905 : int) : (term742 _69905) = term682.
Proof. exact (TRANS (@lem5411224 _69905) (@lem5411334 _69905)). Qed.
Lemma lem5411336 : term682 = term256.
Proof. exact (@lem1982721 term256). Qed.
Lemma lem5411337 (_69905 : int) : (term742 _69905) = term256.
Proof. exact (TRANS (@lem5411335 _69905) (@lem5411336)). Qed.
Lemma lem5411338 (_69903 : int) (_69905 : int) : (term741 _69903 _69905) = term682.
Proof. exact (MK_COMB (@lem5411223 _69903) (@lem5411337 _69905)). Qed.
Lemma lem5411339 (_69903 : int) (_69905 : int) : (term740 _69903 _69905) = term682.
Proof. exact (TRANS (@lem5411115 _69903 _69905) (@lem5411338 _69903 _69905)). Qed.
Lemma lem5411340 : term682 = term256.
Proof. exact (@lem1982721 term256). Qed.
Lemma lem5411341 (_69903 : int) (_69905 : int) : (term740 _69903 _69905) = term256.
Proof. exact (TRANS (@lem5411339 _69903 _69905) (@lem5411340)). Qed.
Lemma lem5411342 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5411343 (_69903 : int) (_69905 : int) : (term744 _69903 _69905) = term684.
Proof. exact (MK_COMB (@lem5411342) (@lem5411341 _69903 _69905)). Qed.
Lemma lem5411344 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5411345 (_69903 : int) (_69905 : int) : (term739 _69903 _69905) = term685.
Proof. exact (MK_COMB (@lem5411343 _69903 _69905) (@lem5411344)). Qed.
Lemma lem5411346 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : term685.
Proof. exact (EQ_MP (@lem5411345 _69903 _69905) (@lem5411114 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411348 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5411349 : term685 = term686.
Proof. exact (@lem5411348 term182 term256). Qed.
Lemma lem5411351 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5411352 : term256 = term257.
Proof. exact (@lem5411351 term79). Qed.
Lemma lem5411354 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5411355 : term182 = term253.
Proof. exact (@lem5411354 (NUMERAL 0)). Qed.
Lemma lem5411356 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5411357 : term184 = term687.
Proof. exact (MK_COMB (@lem5411356) (@lem5411355)). Qed.
Lemma lem5411358 : term686 = term688.
Proof. exact (MK_COMB (@lem5411357) (@lem5411352)). Qed.
Lemma lem5411359 : term689.
Proof. exact (@lem1980026 term182 term193 term256 term193). Qed.
Lemma lem5411361 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411362 : term314 = term315.
Proof. exact (@lem5411361 (NUMERAL 0) term79). Qed.
Lemma lem5411363 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411364 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411365 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411364 h1) (fun h1 : term315 = True => @lem5411363)). Qed.
Lemma lem5411366 : term315 = True.
Proof. exact (EQ_MP (@lem5411365) (@lem5411363)). Qed.
Lemma lem5411367 : term314 = True.
Proof. exact (TRANS (@lem5411362) (@lem5411366)). Qed.
Lemma lem5411368 : True = term314.
Proof. exact (SYM (@lem5411367)). Qed.
Lemma lem5411369 : term314.
Proof. exact (EQ_MP (@lem5411368) (@lem0)). Qed.
Lemma lem5411370 : term690.
Proof. exact (@lem5411359 (@lem5411369)). Qed.
Lemma lem5411372 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411373 : term314 = term315.
Proof. exact (@lem5411372 (NUMERAL 0) term79). Qed.
Lemma lem5411374 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411375 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411376 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411375 h1) (fun h1 : term315 = True => @lem5411374)). Qed.
Lemma lem5411377 : term315 = True.
Proof. exact (EQ_MP (@lem5411376) (@lem5411374)). Qed.
Lemma lem5411378 : term314 = True.
Proof. exact (TRANS (@lem5411373) (@lem5411377)). Qed.
Lemma lem5411379 : True = term314.
Proof. exact (SYM (@lem5411378)). Qed.
Lemma lem5411380 : term314.
Proof. exact (EQ_MP (@lem5411379) (@lem0)). Qed.
Lemma lem5411381 : term688 = term691.
Proof. exact (@lem5411370 (@lem5411380)). Qed.
Lemma lem5411383 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5411384 : term291 = term296.
Proof. exact (@lem5411383 term79 term79). Qed.
Lemma lem5411385 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411386 : term268 = term79.
Proof. exact (EQ_MP (@lem5411385) (@lem940073)). Qed.
Lemma lem5411387 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411388 : term266 = term193.
Proof. exact (MK_COMB (@lem5411387) (@lem5411386)). Qed.
Lemma lem5411389 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5411390 : term296 = term256.
Proof. exact (MK_COMB (@lem5411389) (@lem5411388)). Qed.
Lemma lem5411391 : term291 = term256.
Proof. exact (TRANS (@lem5411384) (@lem5411390)). Qed.
Lemma lem5411393 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5411394 : term405 = term182.
Proof. exact (@lem5411393 term79). Qed.
Lemma lem5411395 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5411396 : term692 = term184.
Proof. exact (MK_COMB (@lem5411395) (@lem5411394)). Qed.
Lemma lem5411397 : term691 = term686.
Proof. exact (MK_COMB (@lem5411396) (@lem5411391)). Qed.
Lemma lem5411399 (m : nat) (n : nat) : (term693 m n) = (term694 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5411400 : term686 = term695.
Proof. exact (@lem5411399 (NUMERAL 0) term79). Qed.
Lemma lem5411401 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411402 (h1 : term316 = (BIT1 0)) : (term79 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5411403 : (term316 = (BIT1 0)) = ((term79 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411402 h1) (fun h1 : (term79 = (NUMERAL 0)) = False => @lem5411401)). Qed.
Lemma lem5411404 : (term79 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5411403) (@lem5411401)). Qed.
Lemma lem5411405 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5411406 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5411407 : term696 = (and True).
Proof. exact (MK_COMB (@lem5411406) (@lem5411405)). Qed.
Lemma lem5411408 : term695 = (True /\ False).
Proof. exact (MK_COMB (@lem5411407) (@lem5411404)). Qed.
Lemma lem5411410 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5411411 : term695 = False.
Proof. exact (TRANS (@lem5411408) (@lem5411410)). Qed.
Lemma lem5411412 : term686 = False.
Proof. exact (TRANS (@lem5411400) (@lem5411411)). Qed.
Lemma lem5411413 : term691 = False.
Proof. exact (TRANS (@lem5411397) (@lem5411412)). Qed.
Lemma lem5411414 : term688 = False.
Proof. exact (TRANS (@lem5411381) (@lem5411413)). Qed.
Lemma lem5411415 : term686 = False.
Proof. exact (TRANS (@lem5411358) (@lem5411414)). Qed.
Lemma lem5411416 : term685 = False.
Proof. exact (TRANS (@lem5411349) (@lem5411415)). Qed.
Lemma lem5411417 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term768 _69904 _69903 _69905) : False.
Proof. exact (EQ_MP (@lem5411416) (@lem5411346 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411418 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term769 _69904 _69903 _69905.
Proof. exact (h1). Qed.
Lemma lem5411419 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term562 _69904 _69903 _69905.
Proof. exact (proj2 (@lem5411418 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411421 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term531 _69904 _69903 _69905.
Proof. exact (proj2 (@lem5411419 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411423 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term500 _69904 _69903 _69905.
Proof. exact (proj2 (@lem5411421 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411425 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term469 _69904 _69903 _69905.
Proof. exact (proj2 (@lem5411423 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411427 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term444 _69904 _69903 _69905.
Proof. exact (proj2 (@lem5411425 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411428 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term386 _69903 _69904 _69905.
Proof. exact (proj1 (@lem5411425 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411429 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term385 _69904 _69905.
Proof. exact (proj2 (@lem5411428 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411432 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term359 _69904 _69905.
Proof. exact (proj1 (@lem5411427 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411434 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5411435 : term583 = term314.
Proof. exact (@lem5411434 term182 term193). Qed.
Lemma lem5411437 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5411438 : term193 = term290.
Proof. exact (@lem5411437 term79). Qed.
Lemma lem5411440 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5411441 : term182 = term253.
Proof. exact (@lem5411440 (NUMERAL 0)). Qed.
Lemma lem5411442 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5411443 : term584 = term585.
Proof. exact (MK_COMB (@lem5411442) (@lem5411441)). Qed.
Lemma lem5411444 : term314 = term586.
Proof. exact (MK_COMB (@lem5411443) (@lem5411438)). Qed.
Lemma lem5411445 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5411447 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411448 : term314 = term315.
Proof. exact (@lem5411447 (NUMERAL 0) term79). Qed.
Lemma lem5411449 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411450 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411451 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411450 h1) (fun h1 : term315 = True => @lem5411449)). Qed.
Lemma lem5411452 : term315 = True.
Proof. exact (EQ_MP (@lem5411451) (@lem5411449)). Qed.
Lemma lem5411453 : term314 = True.
Proof. exact (TRANS (@lem5411448) (@lem5411452)). Qed.
Lemma lem5411454 : True = term314.
Proof. exact (SYM (@lem5411453)). Qed.
Lemma lem5411455 : term314.
Proof. exact (EQ_MP (@lem5411454) (@lem0)). Qed.
Lemma lem5411456 : term588.
Proof. exact (@lem5411445 (@lem5411455)). Qed.
Lemma lem5411458 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411459 : term314 = term315.
Proof. exact (@lem5411458 (NUMERAL 0) term79). Qed.
Lemma lem5411460 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411461 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411462 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411461 h1) (fun h1 : term315 = True => @lem5411460)). Qed.
Lemma lem5411463 : term315 = True.
Proof. exact (EQ_MP (@lem5411462) (@lem5411460)). Qed.
Lemma lem5411464 : term314 = True.
Proof. exact (TRANS (@lem5411459) (@lem5411463)). Qed.
Lemma lem5411465 : True = term314.
Proof. exact (SYM (@lem5411464)). Qed.
Lemma lem5411466 : term314.
Proof. exact (EQ_MP (@lem5411465) (@lem0)). Qed.
Lemma lem5411467 : term586 = term589.
Proof. exact (@lem5411456 (@lem5411466)). Qed.
Lemma lem5411469 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5411470 : term265 = term266.
Proof. exact (@lem5411469 term79 term79). Qed.
Lemma lem5411471 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411472 : term268 = term79.
Proof. exact (EQ_MP (@lem5411471) (@lem940073)). Qed.
Lemma lem5411473 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411474 : term266 = term193.
Proof. exact (MK_COMB (@lem5411473) (@lem5411472)). Qed.
Lemma lem5411475 : term265 = term193.
Proof. exact (TRANS (@lem5411470) (@lem5411474)). Qed.
Lemma lem5411477 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5411478 : term405 = term182.
Proof. exact (@lem5411477 term79). Qed.
Lemma lem5411479 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5411480 : term590 = term584.
Proof. exact (MK_COMB (@lem5411479) (@lem5411478)). Qed.
Lemma lem5411481 : term589 = term314.
Proof. exact (MK_COMB (@lem5411480) (@lem5411475)). Qed.
Lemma lem5411483 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411484 : term314 = term315.
Proof. exact (@lem5411483 (NUMERAL 0) term79). Qed.
Lemma lem5411485 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411486 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411487 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411486 h1) (fun h1 : term315 = True => @lem5411485)). Qed.
Lemma lem5411488 : term315 = True.
Proof. exact (EQ_MP (@lem5411487) (@lem5411485)). Qed.
Lemma lem5411489 : term314 = True.
Proof. exact (TRANS (@lem5411484) (@lem5411488)). Qed.
Lemma lem5411490 : term589 = True.
Proof. exact (TRANS (@lem5411481) (@lem5411489)). Qed.
Lemma lem5411491 : term586 = True.
Proof. exact (TRANS (@lem5411467) (@lem5411490)). Qed.
Lemma lem5411492 : term314 = True.
Proof. exact (TRANS (@lem5411444) (@lem5411491)). Qed.
Lemma lem5411493 : term583 = True.
Proof. exact (TRANS (@lem5411435) (@lem5411492)). Qed.
Lemma lem5411494 : True = term583.
Proof. exact (SYM (@lem5411493)). Qed.
Lemma lem5411495 : term583.
Proof. exact (EQ_MP (@lem5411494) (@lem0)). Qed.
Lemma lem5411496 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term770 _69904 _69905.
Proof. exact (conj (@lem5411495) (@lem5411429 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411498 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5411499 (_69904 : int) (_69905 : int) : term771 _69904 _69905.
Proof. exact (@lem5411498 term193 (term383 _69904 _69905)). Qed.
Lemma lem5411500 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term772 _69904 _69905.
Proof. exact (@lem5411499 _69904 _69905 (@lem5411496 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411501 (_69904 : int) (_69905 : int) : (term773 _69904 _69905) = (term383 _69904 _69905).
Proof. exact (@lem1982733 (term383 _69904 _69905)). Qed.
Lemma lem5411502 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5411503 (_69904 : int) (_69905 : int) : (term774 _69904 _69905) = (term384 _69904 _69905).
Proof. exact (MK_COMB (@lem5411502) (@lem5411501 _69904 _69905)). Qed.
Lemma lem5411504 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5411505 (_69904 : int) (_69905 : int) : (term772 _69904 _69905) = (term385 _69904 _69905).
Proof. exact (MK_COMB (@lem5411503 _69904 _69905) (@lem5411504)). Qed.
Lemma lem5411506 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term385 _69904 _69905.
Proof. exact (EQ_MP (@lem5411505 _69904 _69905) (@lem5411500 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411508 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5411509 : term583 = term314.
Proof. exact (@lem5411508 term182 term193). Qed.
Lemma lem5411511 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5411512 : term193 = term290.
Proof. exact (@lem5411511 term79). Qed.
Lemma lem5411514 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5411515 : term182 = term253.
Proof. exact (@lem5411514 (NUMERAL 0)). Qed.
Lemma lem5411516 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5411517 : term584 = term585.
Proof. exact (MK_COMB (@lem5411516) (@lem5411515)). Qed.
Lemma lem5411518 : term314 = term586.
Proof. exact (MK_COMB (@lem5411517) (@lem5411512)). Qed.
Lemma lem5411519 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5411521 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411522 : term314 = term315.
Proof. exact (@lem5411521 (NUMERAL 0) term79). Qed.
Lemma lem5411523 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411524 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411525 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411524 h1) (fun h1 : term315 = True => @lem5411523)). Qed.
Lemma lem5411526 : term315 = True.
Proof. exact (EQ_MP (@lem5411525) (@lem5411523)). Qed.
Lemma lem5411527 : term314 = True.
Proof. exact (TRANS (@lem5411522) (@lem5411526)). Qed.
Lemma lem5411528 : True = term314.
Proof. exact (SYM (@lem5411527)). Qed.
Lemma lem5411529 : term314.
Proof. exact (EQ_MP (@lem5411528) (@lem0)). Qed.
Lemma lem5411530 : term588.
Proof. exact (@lem5411519 (@lem5411529)). Qed.
Lemma lem5411532 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411533 : term314 = term315.
Proof. exact (@lem5411532 (NUMERAL 0) term79). Qed.
Lemma lem5411534 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411535 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411536 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411535 h1) (fun h1 : term315 = True => @lem5411534)). Qed.
Lemma lem5411537 : term315 = True.
Proof. exact (EQ_MP (@lem5411536) (@lem5411534)). Qed.
Lemma lem5411538 : term314 = True.
Proof. exact (TRANS (@lem5411533) (@lem5411537)). Qed.
Lemma lem5411539 : True = term314.
Proof. exact (SYM (@lem5411538)). Qed.
Lemma lem5411540 : term314.
Proof. exact (EQ_MP (@lem5411539) (@lem0)). Qed.
Lemma lem5411541 : term586 = term589.
Proof. exact (@lem5411530 (@lem5411540)). Qed.
Lemma lem5411543 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5411544 : term265 = term266.
Proof. exact (@lem5411543 term79 term79). Qed.
Lemma lem5411545 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411546 : term268 = term79.
Proof. exact (EQ_MP (@lem5411545) (@lem940073)). Qed.
Lemma lem5411547 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411548 : term266 = term193.
Proof. exact (MK_COMB (@lem5411547) (@lem5411546)). Qed.
Lemma lem5411549 : term265 = term193.
Proof. exact (TRANS (@lem5411544) (@lem5411548)). Qed.
Lemma lem5411551 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5411552 : term405 = term182.
Proof. exact (@lem5411551 term79). Qed.
Lemma lem5411553 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5411554 : term590 = term584.
Proof. exact (MK_COMB (@lem5411553) (@lem5411552)). Qed.
Lemma lem5411555 : term589 = term314.
Proof. exact (MK_COMB (@lem5411554) (@lem5411549)). Qed.
Lemma lem5411557 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411558 : term314 = term315.
Proof. exact (@lem5411557 (NUMERAL 0) term79). Qed.
Lemma lem5411559 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411560 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411561 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411560 h1) (fun h1 : term315 = True => @lem5411559)). Qed.
Lemma lem5411562 : term315 = True.
Proof. exact (EQ_MP (@lem5411561) (@lem5411559)). Qed.
Lemma lem5411563 : term314 = True.
Proof. exact (TRANS (@lem5411558) (@lem5411562)). Qed.
Lemma lem5411564 : term589 = True.
Proof. exact (TRANS (@lem5411555) (@lem5411563)). Qed.
Lemma lem5411565 : term586 = True.
Proof. exact (TRANS (@lem5411541) (@lem5411564)). Qed.
Lemma lem5411566 : term314 = True.
Proof. exact (TRANS (@lem5411518) (@lem5411565)). Qed.
Lemma lem5411567 : term583 = True.
Proof. exact (TRANS (@lem5411509) (@lem5411566)). Qed.
Lemma lem5411568 : True = term583.
Proof. exact (SYM (@lem5411567)). Qed.
Lemma lem5411569 : term583.
Proof. exact (EQ_MP (@lem5411568) (@lem0)). Qed.
Lemma lem5411570 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term698 _69904 _69905.
Proof. exact (conj (@lem5411569) (@lem5411432 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411572 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5411573 (_69904 : int) (_69905 : int) : term699 _69904 _69905.
Proof. exact (@lem5411572 term193 (term356 _69904 _69905)). Qed.
Lemma lem5411574 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term700 _69904 _69905.
Proof. exact (@lem5411573 _69904 _69905 (@lem5411570 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411575 (_69904 : int) (_69905 : int) : (term701 _69904 _69905) = (term356 _69904 _69905).
Proof. exact (@lem1982733 (term356 _69904 _69905)). Qed.
Lemma lem5411576 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5411577 (_69904 : int) (_69905 : int) : (term702 _69904 _69905) = (term358 _69904 _69905).
Proof. exact (MK_COMB (@lem5411576) (@lem5411575 _69904 _69905)). Qed.
Lemma lem5411578 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5411579 (_69904 : int) (_69905 : int) : (term700 _69904 _69905) = (term359 _69904 _69905).
Proof. exact (MK_COMB (@lem5411577 _69904 _69905) (@lem5411578)). Qed.
Lemma lem5411580 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term359 _69904 _69905.
Proof. exact (EQ_MP (@lem5411579 _69904 _69905) (@lem5411574 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411581 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term775 _69904 _69905.
Proof. exact (conj (@lem5411580 _69904 _69903 _69905 h1) (@lem5411506 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411583 (x : real) (y : real) : term662 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5411584 (_69904 : int) (_69905 : int) : term776 _69904 _69905.
Proof. exact (@lem5411583 (term356 _69904 _69905) (term383 _69904 _69905)). Qed.
Lemma lem5411585 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term777 _69904 _69905.
Proof. exact (@lem5411584 _69904 _69905 (@lem5411581 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411586 (_69904 : int) (_69905 : int) : (term778 _69904 _69905) = (term779 _69904 _69905).
Proof. exact (@lem1982753 (term281 _69904) (real_of_int _69904) (term727 _69905) (term382 _69905)). Qed.
Lemma lem5411587 (_69904 : int) : (term667 _69904) = (term615 _69904).
Proof. exact (@lem1982713 term256 (real_of_int _69904)). Qed.
Lemma lem5411589 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5411590 : term193 = term290.
Proof. exact (@lem5411589 term79). Qed.
Lemma lem5411592 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5411593 : term256 = term257.
Proof. exact (@lem5411592 term79). Qed.
Lemma lem5411594 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5411595 : term616 = term617.
Proof. exact (MK_COMB (@lem5411594) (@lem5411593)). Qed.
Lemma lem5411596 : term618 = term619.
Proof. exact (MK_COMB (@lem5411595) (@lem5411590)). Qed.
Lemma lem5411597 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5411599 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411600 : term314 = term315.
Proof. exact (@lem5411599 (NUMERAL 0) term79). Qed.
Lemma lem5411601 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411602 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411603 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411602 h1) (fun h1 : term315 = True => @lem5411601)). Qed.
Lemma lem5411604 : term315 = True.
Proof. exact (EQ_MP (@lem5411603) (@lem5411601)). Qed.
Lemma lem5411605 : term314 = True.
Proof. exact (TRANS (@lem5411600) (@lem5411604)). Qed.
Lemma lem5411606 : True = term314.
Proof. exact (SYM (@lem5411605)). Qed.
Lemma lem5411607 : term314.
Proof. exact (EQ_MP (@lem5411606) (@lem0)). Qed.
Lemma lem5411608 : term621.
Proof. exact (@lem5411597 (@lem5411607)). Qed.
Lemma lem5411610 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411611 : term314 = term315.
Proof. exact (@lem5411610 (NUMERAL 0) term79). Qed.
Lemma lem5411612 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411613 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411614 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411613 h1) (fun h1 : term315 = True => @lem5411612)). Qed.
Lemma lem5411615 : term315 = True.
Proof. exact (EQ_MP (@lem5411614) (@lem5411612)). Qed.
Lemma lem5411616 : term314 = True.
Proof. exact (TRANS (@lem5411611) (@lem5411615)). Qed.
Lemma lem5411617 : True = term314.
Proof. exact (SYM (@lem5411616)). Qed.
Lemma lem5411618 : term314.
Proof. exact (EQ_MP (@lem5411617) (@lem0)). Qed.
Lemma lem5411619 : term622.
Proof. exact (@lem5411608 (@lem5411618)). Qed.
Lemma lem5411621 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411622 : term314 = term315.
Proof. exact (@lem5411621 (NUMERAL 0) term79). Qed.
Lemma lem5411623 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411624 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411625 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411624 h1) (fun h1 : term315 = True => @lem5411623)). Qed.
Lemma lem5411626 : term315 = True.
Proof. exact (EQ_MP (@lem5411625) (@lem5411623)). Qed.
Lemma lem5411627 : term314 = True.
Proof. exact (TRANS (@lem5411622) (@lem5411626)). Qed.
Lemma lem5411628 : True = term314.
Proof. exact (SYM (@lem5411627)). Qed.
Lemma lem5411629 : term314.
Proof. exact (EQ_MP (@lem5411628) (@lem0)). Qed.
Lemma lem5411630 : term623.
Proof. exact (@lem5411619 (@lem5411629)). Qed.
Lemma lem5411632 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5411633 : term265 = term266.
Proof. exact (@lem5411632 term79 term79). Qed.
Lemma lem5411634 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411635 : term268 = term79.
Proof. exact (EQ_MP (@lem5411634) (@lem940073)). Qed.
Lemma lem5411636 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411637 : term266 = term193.
Proof. exact (MK_COMB (@lem5411636) (@lem5411635)). Qed.
Lemma lem5411638 : term265 = term193.
Proof. exact (TRANS (@lem5411633) (@lem5411637)). Qed.
Lemma lem5411640 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5411641 : term291 = term296.
Proof. exact (@lem5411640 term79 term79). Qed.
Lemma lem5411642 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411643 : term268 = term79.
Proof. exact (EQ_MP (@lem5411642) (@lem940073)). Qed.
Lemma lem5411644 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411645 : term266 = term193.
Proof. exact (MK_COMB (@lem5411644) (@lem5411643)). Qed.
Lemma lem5411646 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5411647 : term296 = term256.
Proof. exact (MK_COMB (@lem5411646) (@lem5411645)). Qed.
Lemma lem5411648 : term291 = term256.
Proof. exact (TRANS (@lem5411641) (@lem5411647)). Qed.
Lemma lem5411649 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5411650 : term624 = term616.
Proof. exact (MK_COMB (@lem5411649) (@lem5411648)). Qed.
Lemma lem5411651 : term625 = term618.
Proof. exact (MK_COMB (@lem5411650) (@lem5411638)). Qed.
Lemma lem5411653 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5411654 : term618 = term182.
Proof. exact (@lem5411653 term79). Qed.
Lemma lem5411655 : term625 = term182.
Proof. exact (TRANS (@lem5411651) (@lem5411654)). Qed.
Lemma lem5411656 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5411657 : term627 = term403.
Proof. exact (MK_COMB (@lem5411656) (@lem5411655)). Qed.
Lemma lem5411658 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5411659 : term628 = term405.
Proof. exact (MK_COMB (@lem5411657) (@lem5411658)). Qed.
Lemma lem5411661 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5411662 : term405 = term182.
Proof. exact (@lem5411661 term79). Qed.
Lemma lem5411663 : term628 = term182.
Proof. exact (TRANS (@lem5411659) (@lem5411662)). Qed.
Lemma lem5411665 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5411666 : term265 = term266.
Proof. exact (@lem5411665 term79 term79). Qed.
Lemma lem5411667 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411668 : term268 = term79.
Proof. exact (EQ_MP (@lem5411667) (@lem940073)). Qed.
Lemma lem5411669 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411670 : term266 = term193.
Proof. exact (MK_COMB (@lem5411669) (@lem5411668)). Qed.
Lemma lem5411671 : term265 = term193.
Proof. exact (TRANS (@lem5411666) (@lem5411670)). Qed.
Lemma lem5411672 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5411673 : term407 = term405.
Proof. exact (MK_COMB (@lem5411672) (@lem5411671)). Qed.
Lemma lem5411675 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5411676 : term405 = term182.
Proof. exact (@lem5411675 term79). Qed.
Lemma lem5411677 : term407 = term182.
Proof. exact (TRANS (@lem5411673) (@lem5411676)). Qed.
Lemma lem5411678 : term182 = term407.
Proof. exact (SYM (@lem5411677)). Qed.
Lemma lem5411679 : term628 = term407.
Proof. exact (TRANS (@lem5411663) (@lem5411678)). Qed.
Lemma lem5411680 : term619 = term253.
Proof. exact (@lem5411630 (@lem5411679)). Qed.
Lemma lem5411681 : term618 = term253.
Proof. exact (TRANS (@lem5411596) (@lem5411680)). Qed.
Lemma lem5411683 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5411684 : term253 = term182.
Proof. exact (@lem5411683 term182). Qed.
Lemma lem5411685 : term618 = term182.
Proof. exact (TRANS (@lem5411681) (@lem5411684)). Qed.
Lemma lem5411686 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5411687 : term629 = term403.
Proof. exact (MK_COMB (@lem5411686) (@lem5411685)). Qed.
Lemma lem5411688 (_69904 : int) : (real_of_int _69904) = (real_of_int _69904).
Proof. exact (eq_refl (real_of_int _69904)). Qed.
Lemma lem5411689 (_69904 : int) : (term615 _69904) = (term630 _69904).
Proof. exact (MK_COMB (@lem5411687) (@lem5411688 _69904)). Qed.
Lemma lem5411690 (_69904 : int) : (term667 _69904) = (term630 _69904).
Proof. exact (TRANS (@lem5411587 _69904) (@lem5411689 _69904)). Qed.
Lemma lem5411691 (_69904 : int) : (term630 _69904) = term182.
Proof. exact (@lem1982719 (real_of_int _69904)). Qed.
Lemma lem5411692 (_69904 : int) : (term667 _69904) = term182.
Proof. exact (TRANS (@lem5411690 _69904) (@lem5411691 _69904)). Qed.
Lemma lem5411693 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5411694 (_69904 : int) : (term668 _69904) = term632.
Proof. exact (MK_COMB (@lem5411693) (@lem5411692 _69904)). Qed.
Lemma lem5411695 (_69905 : int) : (term780 _69905) = (term781 _69905).
Proof. exact (@lem1982753 (real_of_int _69905) (term281 _69905) term350 term193). Qed.
Lemma lem5411696 (_69905 : int) : (term614 _69905) = (term615 _69905).
Proof. exact (@lem1982715 term256 (real_of_int _69905)). Qed.
Lemma lem5411698 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5411699 : term193 = term290.
Proof. exact (@lem5411698 term79). Qed.
Lemma lem5411701 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5411702 : term256 = term257.
Proof. exact (@lem5411701 term79). Qed.
Lemma lem5411703 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5411704 : term616 = term617.
Proof. exact (MK_COMB (@lem5411703) (@lem5411702)). Qed.
Lemma lem5411705 : term618 = term619.
Proof. exact (MK_COMB (@lem5411704) (@lem5411699)). Qed.
Lemma lem5411706 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5411708 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411709 : term314 = term315.
Proof. exact (@lem5411708 (NUMERAL 0) term79). Qed.
Lemma lem5411710 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411711 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411712 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411711 h1) (fun h1 : term315 = True => @lem5411710)). Qed.
Lemma lem5411713 : term315 = True.
Proof. exact (EQ_MP (@lem5411712) (@lem5411710)). Qed.
Lemma lem5411714 : term314 = True.
Proof. exact (TRANS (@lem5411709) (@lem5411713)). Qed.
Lemma lem5411715 : True = term314.
Proof. exact (SYM (@lem5411714)). Qed.
Lemma lem5411716 : term314.
Proof. exact (EQ_MP (@lem5411715) (@lem0)). Qed.
Lemma lem5411717 : term621.
Proof. exact (@lem5411706 (@lem5411716)). Qed.
Lemma lem5411719 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411720 : term314 = term315.
Proof. exact (@lem5411719 (NUMERAL 0) term79). Qed.
Lemma lem5411721 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411722 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411723 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411722 h1) (fun h1 : term315 = True => @lem5411721)). Qed.
Lemma lem5411724 : term315 = True.
Proof. exact (EQ_MP (@lem5411723) (@lem5411721)). Qed.
Lemma lem5411725 : term314 = True.
Proof. exact (TRANS (@lem5411720) (@lem5411724)). Qed.
Lemma lem5411726 : True = term314.
Proof. exact (SYM (@lem5411725)). Qed.
Lemma lem5411727 : term314.
Proof. exact (EQ_MP (@lem5411726) (@lem0)). Qed.
Lemma lem5411728 : term622.
Proof. exact (@lem5411717 (@lem5411727)). Qed.
Lemma lem5411730 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411731 : term314 = term315.
Proof. exact (@lem5411730 (NUMERAL 0) term79). Qed.
Lemma lem5411732 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411733 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411734 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411733 h1) (fun h1 : term315 = True => @lem5411732)). Qed.
Lemma lem5411735 : term315 = True.
Proof. exact (EQ_MP (@lem5411734) (@lem5411732)). Qed.
Lemma lem5411736 : term314 = True.
Proof. exact (TRANS (@lem5411731) (@lem5411735)). Qed.
Lemma lem5411737 : True = term314.
Proof. exact (SYM (@lem5411736)). Qed.
Lemma lem5411738 : term314.
Proof. exact (EQ_MP (@lem5411737) (@lem0)). Qed.
Lemma lem5411739 : term623.
Proof. exact (@lem5411728 (@lem5411738)). Qed.
Lemma lem5411741 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5411742 : term265 = term266.
Proof. exact (@lem5411741 term79 term79). Qed.
Lemma lem5411743 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411744 : term268 = term79.
Proof. exact (EQ_MP (@lem5411743) (@lem940073)). Qed.
Lemma lem5411745 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411746 : term266 = term193.
Proof. exact (MK_COMB (@lem5411745) (@lem5411744)). Qed.
Lemma lem5411747 : term265 = term193.
Proof. exact (TRANS (@lem5411742) (@lem5411746)). Qed.
Lemma lem5411749 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5411750 : term291 = term296.
Proof. exact (@lem5411749 term79 term79). Qed.
Lemma lem5411751 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411752 : term268 = term79.
Proof. exact (EQ_MP (@lem5411751) (@lem940073)). Qed.
Lemma lem5411753 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411754 : term266 = term193.
Proof. exact (MK_COMB (@lem5411753) (@lem5411752)). Qed.
Lemma lem5411755 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5411756 : term296 = term256.
Proof. exact (MK_COMB (@lem5411755) (@lem5411754)). Qed.
Lemma lem5411757 : term291 = term256.
Proof. exact (TRANS (@lem5411750) (@lem5411756)). Qed.
Lemma lem5411758 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5411759 : term624 = term616.
Proof. exact (MK_COMB (@lem5411758) (@lem5411757)). Qed.
Lemma lem5411760 : term625 = term618.
Proof. exact (MK_COMB (@lem5411759) (@lem5411747)). Qed.
Lemma lem5411762 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5411763 : term618 = term182.
Proof. exact (@lem5411762 term79). Qed.
Lemma lem5411764 : term625 = term182.
Proof. exact (TRANS (@lem5411760) (@lem5411763)). Qed.
Lemma lem5411765 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5411766 : term627 = term403.
Proof. exact (MK_COMB (@lem5411765) (@lem5411764)). Qed.
Lemma lem5411767 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5411768 : term628 = term405.
Proof. exact (MK_COMB (@lem5411766) (@lem5411767)). Qed.
Lemma lem5411770 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5411771 : term405 = term182.
Proof. exact (@lem5411770 term79). Qed.
Lemma lem5411772 : term628 = term182.
Proof. exact (TRANS (@lem5411768) (@lem5411771)). Qed.
Lemma lem5411774 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5411775 : term265 = term266.
Proof. exact (@lem5411774 term79 term79). Qed.
Lemma lem5411776 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411777 : term268 = term79.
Proof. exact (EQ_MP (@lem5411776) (@lem940073)). Qed.
Lemma lem5411778 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411779 : term266 = term193.
Proof. exact (MK_COMB (@lem5411778) (@lem5411777)). Qed.
Lemma lem5411780 : term265 = term193.
Proof. exact (TRANS (@lem5411775) (@lem5411779)). Qed.
Lemma lem5411781 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5411782 : term407 = term405.
Proof. exact (MK_COMB (@lem5411781) (@lem5411780)). Qed.
Lemma lem5411784 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5411785 : term405 = term182.
Proof. exact (@lem5411784 term79). Qed.
Lemma lem5411786 : term407 = term182.
Proof. exact (TRANS (@lem5411782) (@lem5411785)). Qed.
Lemma lem5411787 : term182 = term407.
Proof. exact (SYM (@lem5411786)). Qed.
Lemma lem5411788 : term628 = term407.
Proof. exact (TRANS (@lem5411772) (@lem5411787)). Qed.
Lemma lem5411789 : term619 = term253.
Proof. exact (@lem5411739 (@lem5411788)). Qed.
Lemma lem5411790 : term618 = term253.
Proof. exact (TRANS (@lem5411705) (@lem5411789)). Qed.
Lemma lem5411792 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5411793 : term253 = term182.
Proof. exact (@lem5411792 term182). Qed.
Lemma lem5411794 : term618 = term182.
Proof. exact (TRANS (@lem5411790) (@lem5411793)). Qed.
Lemma lem5411795 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5411796 : term629 = term403.
Proof. exact (MK_COMB (@lem5411795) (@lem5411794)). Qed.
Lemma lem5411797 (_69905 : int) : (real_of_int _69905) = (real_of_int _69905).
Proof. exact (eq_refl (real_of_int _69905)). Qed.
Lemma lem5411798 (_69905 : int) : (term615 _69905) = (term630 _69905).
Proof. exact (MK_COMB (@lem5411796) (@lem5411797 _69905)). Qed.
Lemma lem5411799 (_69905 : int) : (term614 _69905) = (term630 _69905).
Proof. exact (TRANS (@lem5411696 _69905) (@lem5411798 _69905)). Qed.
Lemma lem5411800 (_69905 : int) : (term630 _69905) = term182.
Proof. exact (@lem1982719 (real_of_int _69905)). Qed.
Lemma lem5411801 (_69905 : int) : (term614 _69905) = term182.
Proof. exact (TRANS (@lem5411799 _69905) (@lem5411800 _69905)). Qed.
Lemma lem5411802 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5411803 (_69905 : int) : (term631 _69905) = term632.
Proof. exact (MK_COMB (@lem5411802) (@lem5411801 _69905)). Qed.
Lemma lem5411805 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5411806 : term193 = term290.
Proof. exact (@lem5411805 term79). Qed.
Lemma lem5411808 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5411809 : term350 = term353.
Proof. exact (@lem5411808 term326). Qed.
Lemma lem5411810 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5411811 : term782 = term783.
Proof. exact (MK_COMB (@lem5411810) (@lem5411809)). Qed.
Lemma lem5411812 : term784 = term785.
Proof. exact (MK_COMB (@lem5411811) (@lem5411806)). Qed.
Lemma lem5411813 : term786.
Proof. exact (@lem1981473 term350 term193 term193 term193 term256 term193). Qed.
Lemma lem5411815 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411816 : term314 = term315.
Proof. exact (@lem5411815 (NUMERAL 0) term79). Qed.
Lemma lem5411817 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411818 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411819 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411818 h1) (fun h1 : term315 = True => @lem5411817)). Qed.
Lemma lem5411820 : term315 = True.
Proof. exact (EQ_MP (@lem5411819) (@lem5411817)). Qed.
Lemma lem5411821 : term314 = True.
Proof. exact (TRANS (@lem5411816) (@lem5411820)). Qed.
Lemma lem5411822 : True = term314.
Proof. exact (SYM (@lem5411821)). Qed.
Lemma lem5411823 : term314.
Proof. exact (EQ_MP (@lem5411822) (@lem0)). Qed.
Lemma lem5411824 : term787.
Proof. exact (@lem5411813 (@lem5411823)). Qed.
Lemma lem5411826 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411827 : term314 = term315.
Proof. exact (@lem5411826 (NUMERAL 0) term79). Qed.
Lemma lem5411828 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411829 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411830 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411829 h1) (fun h1 : term315 = True => @lem5411828)). Qed.
Lemma lem5411831 : term315 = True.
Proof. exact (EQ_MP (@lem5411830) (@lem5411828)). Qed.
Lemma lem5411832 : term314 = True.
Proof. exact (TRANS (@lem5411827) (@lem5411831)). Qed.
Lemma lem5411833 : True = term314.
Proof. exact (SYM (@lem5411832)). Qed.
Lemma lem5411834 : term314.
Proof. exact (EQ_MP (@lem5411833) (@lem0)). Qed.
Lemma lem5411835 : term788.
Proof. exact (@lem5411824 (@lem5411834)). Qed.
Lemma lem5411837 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411838 : term314 = term315.
Proof. exact (@lem5411837 (NUMERAL 0) term79). Qed.
Lemma lem5411839 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411840 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411841 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411840 h1) (fun h1 : term315 = True => @lem5411839)). Qed.
Lemma lem5411842 : term315 = True.
Proof. exact (EQ_MP (@lem5411841) (@lem5411839)). Qed.
Lemma lem5411843 : term314 = True.
Proof. exact (TRANS (@lem5411838) (@lem5411842)). Qed.
Lemma lem5411844 : True = term314.
Proof. exact (SYM (@lem5411843)). Qed.
Lemma lem5411845 : term314.
Proof. exact (EQ_MP (@lem5411844) (@lem0)). Qed.
Lemma lem5411846 : term789.
Proof. exact (@lem5411835 (@lem5411845)). Qed.
Lemma lem5411848 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5411849 : term265 = term266.
Proof. exact (@lem5411848 term79 term79). Qed.
Lemma lem5411850 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411851 : term268 = term79.
Proof. exact (EQ_MP (@lem5411850) (@lem940073)). Qed.
Lemma lem5411852 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411853 : term266 = term193.
Proof. exact (MK_COMB (@lem5411852) (@lem5411851)). Qed.
Lemma lem5411854 : term265 = term193.
Proof. exact (TRANS (@lem5411849) (@lem5411853)). Qed.
Lemma lem5411856 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5411857 : term644 = term645.
Proof. exact (@lem5411856 term326 term79). Qed.
Lemma lem5411858 : term332 = term324.
Proof. exact (@lem996237 term324). Qed.
Lemma lem5411859 : (term332 = term324) = (term333 = term326).
Proof. exact (@lem1007663 term324 (BIT1 0) term324). Qed.
Lemma lem5411860 : term333 = term326.
Proof. exact (EQ_MP (@lem5411859) (@lem5411858)). Qed.
Lemma lem5411861 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411862 : term331 = term312.
Proof. exact (MK_COMB (@lem5411861) (@lem5411860)). Qed.
Lemma lem5411863 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5411864 : term645 = term350.
Proof. exact (MK_COMB (@lem5411863) (@lem5411862)). Qed.
Lemma lem5411865 : term644 = term350.
Proof. exact (TRANS (@lem5411857) (@lem5411864)). Qed.
Lemma lem5411866 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5411867 : term790 = term782.
Proof. exact (MK_COMB (@lem5411866) (@lem5411865)). Qed.
Lemma lem5411868 : term791 = term784.
Proof. exact (MK_COMB (@lem5411867) (@lem5411854)). Qed.
Lemma lem5411871 : term792 = term256.
Proof. exact (@lem1367767 term79 term79). Qed.
Lemma lem5411872 : term323 = term324.
Proof. exact (@lem706885). Qed.
Lemma lem5411873 : (term323 = term324) = (term325 = term326).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term324). Qed.
Lemma lem5411874 : term325 = term326.
Proof. exact (EQ_MP (@lem5411873) (@lem5411872)). Qed.
Lemma lem5411875 : term326 = term325.
Proof. exact (SYM (@lem5411874)). Qed.
Lemma lem5411876 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411877 : term312 = term322.
Proof. exact (MK_COMB (@lem5411876) (@lem5411875)). Qed.
Lemma lem5411878 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5411879 : term350 = term640.
Proof. exact (MK_COMB (@lem5411878) (@lem5411877)). Qed.
Lemma lem5411880 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5411881 : term782 = term793.
Proof. exact (MK_COMB (@lem5411880) (@lem5411879)). Qed.
Lemma lem5411882 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5411883 : term784 = term792.
Proof. exact (MK_COMB (@lem5411881) (@lem5411882)). Qed.
Lemma lem5411884 : term784 = term256.
Proof. exact (TRANS (@lem5411883) (@lem5411871)). Qed.
Lemma lem5411885 : term791 = term256.
Proof. exact (TRANS (@lem5411868) (@lem5411884)). Qed.
Lemma lem5411886 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5411887 : term794 = term258.
Proof. exact (MK_COMB (@lem5411886) (@lem5411885)). Qed.
Lemma lem5411888 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5411889 : term795 = term291.
Proof. exact (MK_COMB (@lem5411887) (@lem5411888)). Qed.
Lemma lem5411891 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5411892 : term291 = term296.
Proof. exact (@lem5411891 term79 term79). Qed.
Lemma lem5411893 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411894 : term268 = term79.
Proof. exact (EQ_MP (@lem5411893) (@lem940073)). Qed.
Lemma lem5411895 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411896 : term266 = term193.
Proof. exact (MK_COMB (@lem5411895) (@lem5411894)). Qed.
Lemma lem5411897 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5411898 : term296 = term256.
Proof. exact (MK_COMB (@lem5411897) (@lem5411896)). Qed.
Lemma lem5411899 : term291 = term256.
Proof. exact (TRANS (@lem5411892) (@lem5411898)). Qed.
Lemma lem5411900 : term795 = term256.
Proof. exact (TRANS (@lem5411889) (@lem5411899)). Qed.
Lemma lem5411902 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5411903 : term265 = term266.
Proof. exact (@lem5411902 term79 term79). Qed.
Lemma lem5411904 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411905 : term268 = term79.
Proof. exact (EQ_MP (@lem5411904) (@lem940073)). Qed.
Lemma lem5411906 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411907 : term266 = term193.
Proof. exact (MK_COMB (@lem5411906) (@lem5411905)). Qed.
Lemma lem5411908 : term265 = term193.
Proof. exact (TRANS (@lem5411903) (@lem5411907)). Qed.
Lemma lem5411909 : term258 = term258.
Proof. exact (eq_refl term258). Qed.
Lemma lem5411910 : term681 = term291.
Proof. exact (MK_COMB (@lem5411909) (@lem5411908)). Qed.
Lemma lem5411912 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5411913 : term291 = term296.
Proof. exact (@lem5411912 term79 term79). Qed.
Lemma lem5411914 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411915 : term268 = term79.
Proof. exact (EQ_MP (@lem5411914) (@lem940073)). Qed.
Lemma lem5411916 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411917 : term266 = term193.
Proof. exact (MK_COMB (@lem5411916) (@lem5411915)). Qed.
Lemma lem5411918 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5411919 : term296 = term256.
Proof. exact (MK_COMB (@lem5411918) (@lem5411917)). Qed.
Lemma lem5411920 : term291 = term256.
Proof. exact (TRANS (@lem5411913) (@lem5411919)). Qed.
Lemma lem5411921 : term681 = term256.
Proof. exact (TRANS (@lem5411910) (@lem5411920)). Qed.
Lemma lem5411922 : term256 = term681.
Proof. exact (SYM (@lem5411921)). Qed.
Lemma lem5411923 : term795 = term681.
Proof. exact (TRANS (@lem5411900) (@lem5411922)). Qed.
Lemma lem5411924 : term785 = term257.
Proof. exact (@lem5411846 (@lem5411923)). Qed.
Lemma lem5411925 : term784 = term257.
Proof. exact (TRANS (@lem5411812) (@lem5411924)). Qed.
Lemma lem5411927 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5411928 : term257 = term256.
Proof. exact (@lem5411927 term256). Qed.
Lemma lem5411929 : term784 = term256.
Proof. exact (TRANS (@lem5411925) (@lem5411928)). Qed.
Lemma lem5411930 (_69905 : int) : (term781 _69905) = term682.
Proof. exact (MK_COMB (@lem5411803 _69905) (@lem5411929)). Qed.
Lemma lem5411931 (_69905 : int) : (term780 _69905) = term682.
Proof. exact (TRANS (@lem5411695 _69905) (@lem5411930 _69905)). Qed.
Lemma lem5411932 : term682 = term256.
Proof. exact (@lem1982721 term256). Qed.
Lemma lem5411933 (_69905 : int) : (term780 _69905) = term256.
Proof. exact (TRANS (@lem5411931 _69905) (@lem5411932)). Qed.
Lemma lem5411934 (_69904 : int) (_69905 : int) : (term779 _69904 _69905) = term682.
Proof. exact (MK_COMB (@lem5411694 _69904) (@lem5411933 _69905)). Qed.
Lemma lem5411935 (_69904 : int) (_69905 : int) : (term778 _69904 _69905) = term682.
Proof. exact (TRANS (@lem5411586 _69904 _69905) (@lem5411934 _69904 _69905)). Qed.
Lemma lem5411936 : term682 = term256.
Proof. exact (@lem1982721 term256). Qed.
Lemma lem5411937 (_69904 : int) (_69905 : int) : (term778 _69904 _69905) = term256.
Proof. exact (TRANS (@lem5411935 _69904 _69905) (@lem5411936)). Qed.
Lemma lem5411938 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5411939 (_69904 : int) (_69905 : int) : (term796 _69904 _69905) = term684.
Proof. exact (MK_COMB (@lem5411938) (@lem5411937 _69904 _69905)). Qed.
Lemma lem5411940 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5411941 (_69904 : int) (_69905 : int) : (term777 _69904 _69905) = term685.
Proof. exact (MK_COMB (@lem5411939 _69904 _69905) (@lem5411940)). Qed.
Lemma lem5411942 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : term685.
Proof. exact (EQ_MP (@lem5411941 _69904 _69905) (@lem5411585 _69904 _69903 _69905 h1)). Qed.
Lemma lem5411944 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5411945 : term685 = term686.
Proof. exact (@lem5411944 term182 term256). Qed.
Lemma lem5411947 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5411948 : term256 = term257.
Proof. exact (@lem5411947 term79). Qed.
Lemma lem5411950 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5411951 : term182 = term253.
Proof. exact (@lem5411950 (NUMERAL 0)). Qed.
Lemma lem5411952 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5411953 : term184 = term687.
Proof. exact (MK_COMB (@lem5411952) (@lem5411951)). Qed.
Lemma lem5411954 : term686 = term688.
Proof. exact (MK_COMB (@lem5411953) (@lem5411948)). Qed.
Lemma lem5411955 : term689.
Proof. exact (@lem1980026 term182 term193 term256 term193). Qed.
Lemma lem5411957 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411958 : term314 = term315.
Proof. exact (@lem5411957 (NUMERAL 0) term79). Qed.
Lemma lem5411959 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411960 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411961 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411960 h1) (fun h1 : term315 = True => @lem5411959)). Qed.
Lemma lem5411962 : term315 = True.
Proof. exact (EQ_MP (@lem5411961) (@lem5411959)). Qed.
Lemma lem5411963 : term314 = True.
Proof. exact (TRANS (@lem5411958) (@lem5411962)). Qed.
Lemma lem5411964 : True = term314.
Proof. exact (SYM (@lem5411963)). Qed.
Lemma lem5411965 : term314.
Proof. exact (EQ_MP (@lem5411964) (@lem0)). Qed.
Lemma lem5411966 : term690.
Proof. exact (@lem5411955 (@lem5411965)). Qed.
Lemma lem5411968 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5411969 : term314 = term315.
Proof. exact (@lem5411968 (NUMERAL 0) term79). Qed.
Lemma lem5411970 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411971 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5411972 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411971 h1) (fun h1 : term315 = True => @lem5411970)). Qed.
Lemma lem5411973 : term315 = True.
Proof. exact (EQ_MP (@lem5411972) (@lem5411970)). Qed.
Lemma lem5411974 : term314 = True.
Proof. exact (TRANS (@lem5411969) (@lem5411973)). Qed.
Lemma lem5411975 : True = term314.
Proof. exact (SYM (@lem5411974)). Qed.
Lemma lem5411976 : term314.
Proof. exact (EQ_MP (@lem5411975) (@lem0)). Qed.
Lemma lem5411977 : term688 = term691.
Proof. exact (@lem5411966 (@lem5411976)). Qed.
Lemma lem5411979 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5411980 : term291 = term296.
Proof. exact (@lem5411979 term79 term79). Qed.
Lemma lem5411981 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5411982 : term268 = term79.
Proof. exact (EQ_MP (@lem5411981) (@lem940073)). Qed.
Lemma lem5411983 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5411984 : term266 = term193.
Proof. exact (MK_COMB (@lem5411983) (@lem5411982)). Qed.
Lemma lem5411985 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5411986 : term296 = term256.
Proof. exact (MK_COMB (@lem5411985) (@lem5411984)). Qed.
Lemma lem5411987 : term291 = term256.
Proof. exact (TRANS (@lem5411980) (@lem5411986)). Qed.
Lemma lem5411989 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5411990 : term405 = term182.
Proof. exact (@lem5411989 term79). Qed.
Lemma lem5411991 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5411992 : term692 = term184.
Proof. exact (MK_COMB (@lem5411991) (@lem5411990)). Qed.
Lemma lem5411993 : term691 = term686.
Proof. exact (MK_COMB (@lem5411992) (@lem5411987)). Qed.
Lemma lem5411995 (m : nat) (n : nat) : (term693 m n) = (term694 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5411996 : term686 = term695.
Proof. exact (@lem5411995 (NUMERAL 0) term79). Qed.
Lemma lem5411997 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5411998 (h1 : term316 = (BIT1 0)) : (term79 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5411999 : (term316 = (BIT1 0)) = ((term79 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5411998 h1) (fun h1 : (term79 = (NUMERAL 0)) = False => @lem5411997)). Qed.
Lemma lem5412000 : (term79 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5411999) (@lem5411997)). Qed.
Lemma lem5412001 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5412002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5412003 : term696 = (and True).
Proof. exact (MK_COMB (@lem5412002) (@lem5412001)). Qed.
Lemma lem5412004 : term695 = (True /\ False).
Proof. exact (MK_COMB (@lem5412003) (@lem5412000)). Qed.
Lemma lem5412006 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5412007 : term695 = False.
Proof. exact (TRANS (@lem5412004) (@lem5412006)). Qed.
Lemma lem5412008 : term686 = False.
Proof. exact (TRANS (@lem5411996) (@lem5412007)). Qed.
Lemma lem5412009 : term691 = False.
Proof. exact (TRANS (@lem5411993) (@lem5412008)). Qed.
Lemma lem5412010 : term688 = False.
Proof. exact (TRANS (@lem5411977) (@lem5412009)). Qed.
Lemma lem5412011 : term686 = False.
Proof. exact (TRANS (@lem5411954) (@lem5412010)). Qed.
Lemma lem5412012 : term685 = False.
Proof. exact (TRANS (@lem5411945) (@lem5412011)). Qed.
Lemma lem5412013 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term769 _69904 _69903 _69905) : False.
Proof. exact (EQ_MP (@lem5412012) (@lem5411942 _69904 _69903 _69905 h1)). Qed.
Lemma lem5412014 (_69904 : int) (_69903 : int) (_69905 : int) (h1 : term560 _69904 _69903 _69905) : False.
Proof. exact (or_elim (@lem5410946 _69904 _69903 _69905 h1) (fun h0 : term768 _69904 _69903 _69905 => @lem5411417 _69904 _69903 _69905 h0) (fun h0 : term769 _69904 _69903 _69905 => @lem5412013 _69904 _69903 _69905 h0)). Qed.
Lemma lem5412015 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term556 _69903 _69904 _69905) : term556 _69903 _69904 _69905.
Proof. exact (h1). Qed.
Lemma lem5412016 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term797 _69903 _69904 _69905.
Proof. exact (h1). Qed.
Lemma lem5412017 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term557 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5412016 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412019 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term526 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5412017 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412021 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term495 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5412019 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412023 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term464 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5412021 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412025 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term439 _69904 _69905.
Proof. exact (proj2 (@lem5412023 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412029 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term413 _69904 _69905.
Proof. exact (proj2 (@lem5412025 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412030 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term373 _69904 _69905.
Proof. exact (proj1 (@lem5412025 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412032 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5412033 : term583 = term314.
Proof. exact (@lem5412032 term182 term193). Qed.
Lemma lem5412035 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5412036 : term193 = term290.
Proof. exact (@lem5412035 term79). Qed.
Lemma lem5412038 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5412039 : term182 = term253.
Proof. exact (@lem5412038 (NUMERAL 0)). Qed.
Lemma lem5412040 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5412041 : term584 = term585.
Proof. exact (MK_COMB (@lem5412040) (@lem5412039)). Qed.
Lemma lem5412042 : term314 = term586.
Proof. exact (MK_COMB (@lem5412041) (@lem5412036)). Qed.
Lemma lem5412043 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5412045 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412046 : term314 = term315.
Proof. exact (@lem5412045 (NUMERAL 0) term79). Qed.
Lemma lem5412047 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412048 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412049 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412048 h1) (fun h1 : term315 = True => @lem5412047)). Qed.
Lemma lem5412050 : term315 = True.
Proof. exact (EQ_MP (@lem5412049) (@lem5412047)). Qed.
Lemma lem5412051 : term314 = True.
Proof. exact (TRANS (@lem5412046) (@lem5412050)). Qed.
Lemma lem5412052 : True = term314.
Proof. exact (SYM (@lem5412051)). Qed.
Lemma lem5412053 : term314.
Proof. exact (EQ_MP (@lem5412052) (@lem0)). Qed.
Lemma lem5412054 : term588.
Proof. exact (@lem5412043 (@lem5412053)). Qed.
Lemma lem5412056 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412057 : term314 = term315.
Proof. exact (@lem5412056 (NUMERAL 0) term79). Qed.
Lemma lem5412058 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412059 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412060 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412059 h1) (fun h1 : term315 = True => @lem5412058)). Qed.
Lemma lem5412061 : term315 = True.
Proof. exact (EQ_MP (@lem5412060) (@lem5412058)). Qed.
Lemma lem5412062 : term314 = True.
Proof. exact (TRANS (@lem5412057) (@lem5412061)). Qed.
Lemma lem5412063 : True = term314.
Proof. exact (SYM (@lem5412062)). Qed.
Lemma lem5412064 : term314.
Proof. exact (EQ_MP (@lem5412063) (@lem0)). Qed.
Lemma lem5412065 : term586 = term589.
Proof. exact (@lem5412054 (@lem5412064)). Qed.
Lemma lem5412067 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5412068 : term265 = term266.
Proof. exact (@lem5412067 term79 term79). Qed.
Lemma lem5412069 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412070 : term268 = term79.
Proof. exact (EQ_MP (@lem5412069) (@lem940073)). Qed.
Lemma lem5412071 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412072 : term266 = term193.
Proof. exact (MK_COMB (@lem5412071) (@lem5412070)). Qed.
Lemma lem5412073 : term265 = term193.
Proof. exact (TRANS (@lem5412068) (@lem5412072)). Qed.
Lemma lem5412075 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5412076 : term405 = term182.
Proof. exact (@lem5412075 term79). Qed.
Lemma lem5412077 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5412078 : term590 = term584.
Proof. exact (MK_COMB (@lem5412077) (@lem5412076)). Qed.
Lemma lem5412079 : term589 = term314.
Proof. exact (MK_COMB (@lem5412078) (@lem5412073)). Qed.
Lemma lem5412081 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412082 : term314 = term315.
Proof. exact (@lem5412081 (NUMERAL 0) term79). Qed.
Lemma lem5412083 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412084 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412085 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412084 h1) (fun h1 : term315 = True => @lem5412083)). Qed.
Lemma lem5412086 : term315 = True.
Proof. exact (EQ_MP (@lem5412085) (@lem5412083)). Qed.
Lemma lem5412087 : term314 = True.
Proof. exact (TRANS (@lem5412082) (@lem5412086)). Qed.
Lemma lem5412088 : term589 = True.
Proof. exact (TRANS (@lem5412079) (@lem5412087)). Qed.
Lemma lem5412089 : term586 = True.
Proof. exact (TRANS (@lem5412065) (@lem5412088)). Qed.
Lemma lem5412090 : term314 = True.
Proof. exact (TRANS (@lem5412042) (@lem5412089)). Qed.
Lemma lem5412091 : term583 = True.
Proof. exact (TRANS (@lem5412033) (@lem5412090)). Qed.
Lemma lem5412092 : True = term583.
Proof. exact (SYM (@lem5412091)). Qed.
Lemma lem5412093 : term583.
Proof. exact (EQ_MP (@lem5412092) (@lem0)). Qed.
Lemma lem5412094 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term746 _69904 _69905.
Proof. exact (conj (@lem5412093) (@lem5412030 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412096 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5412097 (_69904 : int) (_69905 : int) : term747 _69904 _69905.
Proof. exact (@lem5412096 term193 (term367 _69904 _69905)). Qed.
Lemma lem5412098 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term748 _69904 _69905.
Proof. exact (@lem5412097 _69904 _69905 (@lem5412094 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412099 (_69904 : int) (_69905 : int) : (term749 _69904 _69905) = (term367 _69904 _69905).
Proof. exact (@lem1982733 (term367 _69904 _69905)). Qed.
Lemma lem5412100 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5412101 (_69904 : int) (_69905 : int) : (term750 _69904 _69905) = (term372 _69904 _69905).
Proof. exact (MK_COMB (@lem5412100) (@lem5412099 _69904 _69905)). Qed.
Lemma lem5412102 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5412103 (_69904 : int) (_69905 : int) : (term748 _69904 _69905) = (term373 _69904 _69905).
Proof. exact (MK_COMB (@lem5412101 _69904 _69905) (@lem5412102)). Qed.
Lemma lem5412104 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term373 _69904 _69905.
Proof. exact (EQ_MP (@lem5412103 _69904 _69905) (@lem5412098 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412106 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5412107 : term583 = term314.
Proof. exact (@lem5412106 term182 term193). Qed.
Lemma lem5412109 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5412110 : term193 = term290.
Proof. exact (@lem5412109 term79). Qed.
Lemma lem5412112 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5412113 : term182 = term253.
Proof. exact (@lem5412112 (NUMERAL 0)). Qed.
Lemma lem5412114 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5412115 : term584 = term585.
Proof. exact (MK_COMB (@lem5412114) (@lem5412113)). Qed.
Lemma lem5412116 : term314 = term586.
Proof. exact (MK_COMB (@lem5412115) (@lem5412110)). Qed.
Lemma lem5412117 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5412119 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412120 : term314 = term315.
Proof. exact (@lem5412119 (NUMERAL 0) term79). Qed.
Lemma lem5412121 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412122 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412123 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412122 h1) (fun h1 : term315 = True => @lem5412121)). Qed.
Lemma lem5412124 : term315 = True.
Proof. exact (EQ_MP (@lem5412123) (@lem5412121)). Qed.
Lemma lem5412125 : term314 = True.
Proof. exact (TRANS (@lem5412120) (@lem5412124)). Qed.
Lemma lem5412126 : True = term314.
Proof. exact (SYM (@lem5412125)). Qed.
Lemma lem5412127 : term314.
Proof. exact (EQ_MP (@lem5412126) (@lem0)). Qed.
Lemma lem5412128 : term588.
Proof. exact (@lem5412117 (@lem5412127)). Qed.
Lemma lem5412130 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412131 : term314 = term315.
Proof. exact (@lem5412130 (NUMERAL 0) term79). Qed.
Lemma lem5412132 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412133 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412134 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412133 h1) (fun h1 : term315 = True => @lem5412132)). Qed.
Lemma lem5412135 : term315 = True.
Proof. exact (EQ_MP (@lem5412134) (@lem5412132)). Qed.
Lemma lem5412136 : term314 = True.
Proof. exact (TRANS (@lem5412131) (@lem5412135)). Qed.
Lemma lem5412137 : True = term314.
Proof. exact (SYM (@lem5412136)). Qed.
Lemma lem5412138 : term314.
Proof. exact (EQ_MP (@lem5412137) (@lem0)). Qed.
Lemma lem5412139 : term586 = term589.
Proof. exact (@lem5412128 (@lem5412138)). Qed.
Lemma lem5412141 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5412142 : term265 = term266.
Proof. exact (@lem5412141 term79 term79). Qed.
Lemma lem5412143 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412144 : term268 = term79.
Proof. exact (EQ_MP (@lem5412143) (@lem940073)). Qed.
Lemma lem5412145 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412146 : term266 = term193.
Proof. exact (MK_COMB (@lem5412145) (@lem5412144)). Qed.
Lemma lem5412147 : term265 = term193.
Proof. exact (TRANS (@lem5412142) (@lem5412146)). Qed.
Lemma lem5412149 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5412150 : term405 = term182.
Proof. exact (@lem5412149 term79). Qed.
Lemma lem5412151 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5412152 : term590 = term584.
Proof. exact (MK_COMB (@lem5412151) (@lem5412150)). Qed.
Lemma lem5412153 : term589 = term314.
Proof. exact (MK_COMB (@lem5412152) (@lem5412147)). Qed.
Lemma lem5412155 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412156 : term314 = term315.
Proof. exact (@lem5412155 (NUMERAL 0) term79). Qed.
Lemma lem5412157 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412158 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412159 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412158 h1) (fun h1 : term315 = True => @lem5412157)). Qed.
Lemma lem5412160 : term315 = True.
Proof. exact (EQ_MP (@lem5412159) (@lem5412157)). Qed.
Lemma lem5412161 : term314 = True.
Proof. exact (TRANS (@lem5412156) (@lem5412160)). Qed.
Lemma lem5412162 : term589 = True.
Proof. exact (TRANS (@lem5412153) (@lem5412161)). Qed.
Lemma lem5412163 : term586 = True.
Proof. exact (TRANS (@lem5412139) (@lem5412162)). Qed.
Lemma lem5412164 : term314 = True.
Proof. exact (TRANS (@lem5412116) (@lem5412163)). Qed.
Lemma lem5412165 : term583 = True.
Proof. exact (TRANS (@lem5412107) (@lem5412164)). Qed.
Lemma lem5412166 : True = term583.
Proof. exact (SYM (@lem5412165)). Qed.
Lemma lem5412167 : term583.
Proof. exact (EQ_MP (@lem5412166) (@lem0)). Qed.
Lemma lem5412168 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term798 _69904 _69905.
Proof. exact (conj (@lem5412167) (@lem5412029 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412170 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5412171 (_69904 : int) (_69905 : int) : term799 _69904 _69905.
Proof. exact (@lem5412170 term193 (term362 _69904 _69905)). Qed.
Lemma lem5412172 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term800 _69904 _69905.
Proof. exact (@lem5412171 _69904 _69905 (@lem5412168 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412173 (_69904 : int) (_69905 : int) : (term601 _69904 _69905) = (term362 _69904 _69905).
Proof. exact (@lem1982733 (term362 _69904 _69905)). Qed.
Lemma lem5412174 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5412175 (_69904 : int) (_69905 : int) : (term801 _69904 _69905) = (term412 _69904 _69905).
Proof. exact (MK_COMB (@lem5412174) (@lem5412173 _69904 _69905)). Qed.
Lemma lem5412176 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5412177 (_69904 : int) (_69905 : int) : (term800 _69904 _69905) = (term413 _69904 _69905).
Proof. exact (MK_COMB (@lem5412175 _69904 _69905) (@lem5412176)). Qed.
Lemma lem5412178 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term413 _69904 _69905.
Proof. exact (EQ_MP (@lem5412177 _69904 _69905) (@lem5412172 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412179 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term802 _69904 _69905.
Proof. exact (conj (@lem5412178 _69903 _69904 _69905 h1) (@lem5412104 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412181 (x : real) (y : real) : term662 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5412182 (_69904 : int) (_69905 : int) : term803 _69904 _69905.
Proof. exact (@lem5412181 (term362 _69904 _69905) (term367 _69904 _69905)). Qed.
Lemma lem5412183 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term804 _69904 _69905.
Proof. exact (@lem5412182 _69904 _69905 (@lem5412179 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412184 (_69904 : int) (_69905 : int) : (term805 _69904 _69905) = (term806 _69904 _69905).
Proof. exact (@lem1982753 (term281 _69904) (real_of_int _69904) (term611 _69905) (term281 _69905)). Qed.
Lemma lem5412185 (_69904 : int) : (term667 _69904) = (term615 _69904).
Proof. exact (@lem1982713 term256 (real_of_int _69904)). Qed.
Lemma lem5412187 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5412188 : term193 = term290.
Proof. exact (@lem5412187 term79). Qed.
Lemma lem5412190 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5412191 : term256 = term257.
Proof. exact (@lem5412190 term79). Qed.
Lemma lem5412192 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5412193 : term616 = term617.
Proof. exact (MK_COMB (@lem5412192) (@lem5412191)). Qed.
Lemma lem5412194 : term618 = term619.
Proof. exact (MK_COMB (@lem5412193) (@lem5412188)). Qed.
Lemma lem5412195 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5412197 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412198 : term314 = term315.
Proof. exact (@lem5412197 (NUMERAL 0) term79). Qed.
Lemma lem5412199 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412200 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412201 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412200 h1) (fun h1 : term315 = True => @lem5412199)). Qed.
Lemma lem5412202 : term315 = True.
Proof. exact (EQ_MP (@lem5412201) (@lem5412199)). Qed.
Lemma lem5412203 : term314 = True.
Proof. exact (TRANS (@lem5412198) (@lem5412202)). Qed.
Lemma lem5412204 : True = term314.
Proof. exact (SYM (@lem5412203)). Qed.
Lemma lem5412205 : term314.
Proof. exact (EQ_MP (@lem5412204) (@lem0)). Qed.
Lemma lem5412206 : term621.
Proof. exact (@lem5412195 (@lem5412205)). Qed.
Lemma lem5412208 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412209 : term314 = term315.
Proof. exact (@lem5412208 (NUMERAL 0) term79). Qed.
Lemma lem5412210 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412211 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412212 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412211 h1) (fun h1 : term315 = True => @lem5412210)). Qed.
Lemma lem5412213 : term315 = True.
Proof. exact (EQ_MP (@lem5412212) (@lem5412210)). Qed.
Lemma lem5412214 : term314 = True.
Proof. exact (TRANS (@lem5412209) (@lem5412213)). Qed.
Lemma lem5412215 : True = term314.
Proof. exact (SYM (@lem5412214)). Qed.
Lemma lem5412216 : term314.
Proof. exact (EQ_MP (@lem5412215) (@lem0)). Qed.
Lemma lem5412217 : term622.
Proof. exact (@lem5412206 (@lem5412216)). Qed.
Lemma lem5412219 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412220 : term314 = term315.
Proof. exact (@lem5412219 (NUMERAL 0) term79). Qed.
Lemma lem5412221 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412222 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412223 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412222 h1) (fun h1 : term315 = True => @lem5412221)). Qed.
Lemma lem5412224 : term315 = True.
Proof. exact (EQ_MP (@lem5412223) (@lem5412221)). Qed.
Lemma lem5412225 : term314 = True.
Proof. exact (TRANS (@lem5412220) (@lem5412224)). Qed.
Lemma lem5412226 : True = term314.
Proof. exact (SYM (@lem5412225)). Qed.
Lemma lem5412227 : term314.
Proof. exact (EQ_MP (@lem5412226) (@lem0)). Qed.
Lemma lem5412228 : term623.
Proof. exact (@lem5412217 (@lem5412227)). Qed.
Lemma lem5412230 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5412231 : term265 = term266.
Proof. exact (@lem5412230 term79 term79). Qed.
Lemma lem5412232 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412233 : term268 = term79.
Proof. exact (EQ_MP (@lem5412232) (@lem940073)). Qed.
Lemma lem5412234 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412235 : term266 = term193.
Proof. exact (MK_COMB (@lem5412234) (@lem5412233)). Qed.
Lemma lem5412236 : term265 = term193.
Proof. exact (TRANS (@lem5412231) (@lem5412235)). Qed.
Lemma lem5412238 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5412239 : term291 = term296.
Proof. exact (@lem5412238 term79 term79). Qed.
Lemma lem5412240 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412241 : term268 = term79.
Proof. exact (EQ_MP (@lem5412240) (@lem940073)). Qed.
Lemma lem5412242 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412243 : term266 = term193.
Proof. exact (MK_COMB (@lem5412242) (@lem5412241)). Qed.
Lemma lem5412244 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5412245 : term296 = term256.
Proof. exact (MK_COMB (@lem5412244) (@lem5412243)). Qed.
Lemma lem5412246 : term291 = term256.
Proof. exact (TRANS (@lem5412239) (@lem5412245)). Qed.
Lemma lem5412247 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5412248 : term624 = term616.
Proof. exact (MK_COMB (@lem5412247) (@lem5412246)). Qed.
Lemma lem5412249 : term625 = term618.
Proof. exact (MK_COMB (@lem5412248) (@lem5412236)). Qed.
Lemma lem5412251 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5412252 : term618 = term182.
Proof. exact (@lem5412251 term79). Qed.
Lemma lem5412253 : term625 = term182.
Proof. exact (TRANS (@lem5412249) (@lem5412252)). Qed.
Lemma lem5412254 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5412255 : term627 = term403.
Proof. exact (MK_COMB (@lem5412254) (@lem5412253)). Qed.
Lemma lem5412256 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5412257 : term628 = term405.
Proof. exact (MK_COMB (@lem5412255) (@lem5412256)). Qed.
Lemma lem5412259 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5412260 : term405 = term182.
Proof. exact (@lem5412259 term79). Qed.
Lemma lem5412261 : term628 = term182.
Proof. exact (TRANS (@lem5412257) (@lem5412260)). Qed.
Lemma lem5412263 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5412264 : term265 = term266.
Proof. exact (@lem5412263 term79 term79). Qed.
Lemma lem5412265 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412266 : term268 = term79.
Proof. exact (EQ_MP (@lem5412265) (@lem940073)). Qed.
Lemma lem5412267 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412268 : term266 = term193.
Proof. exact (MK_COMB (@lem5412267) (@lem5412266)). Qed.
Lemma lem5412269 : term265 = term193.
Proof. exact (TRANS (@lem5412264) (@lem5412268)). Qed.
Lemma lem5412270 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5412271 : term407 = term405.
Proof. exact (MK_COMB (@lem5412270) (@lem5412269)). Qed.
Lemma lem5412273 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5412274 : term405 = term182.
Proof. exact (@lem5412273 term79). Qed.
Lemma lem5412275 : term407 = term182.
Proof. exact (TRANS (@lem5412271) (@lem5412274)). Qed.
Lemma lem5412276 : term182 = term407.
Proof. exact (SYM (@lem5412275)). Qed.
Lemma lem5412277 : term628 = term407.
Proof. exact (TRANS (@lem5412261) (@lem5412276)). Qed.
Lemma lem5412278 : term619 = term253.
Proof. exact (@lem5412228 (@lem5412277)). Qed.
Lemma lem5412279 : term618 = term253.
Proof. exact (TRANS (@lem5412194) (@lem5412278)). Qed.
Lemma lem5412281 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5412282 : term253 = term182.
Proof. exact (@lem5412281 term182). Qed.
Lemma lem5412283 : term618 = term182.
Proof. exact (TRANS (@lem5412279) (@lem5412282)). Qed.
Lemma lem5412284 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5412285 : term629 = term403.
Proof. exact (MK_COMB (@lem5412284) (@lem5412283)). Qed.
Lemma lem5412286 (_69904 : int) : (real_of_int _69904) = (real_of_int _69904).
Proof. exact (eq_refl (real_of_int _69904)). Qed.
Lemma lem5412287 (_69904 : int) : (term615 _69904) = (term630 _69904).
Proof. exact (MK_COMB (@lem5412285) (@lem5412286 _69904)). Qed.
Lemma lem5412288 (_69904 : int) : (term667 _69904) = (term630 _69904).
Proof. exact (TRANS (@lem5412185 _69904) (@lem5412287 _69904)). Qed.
Lemma lem5412289 (_69904 : int) : (term630 _69904) = term182.
Proof. exact (@lem1982719 (real_of_int _69904)). Qed.
Lemma lem5412290 (_69904 : int) : (term667 _69904) = term182.
Proof. exact (TRANS (@lem5412288 _69904) (@lem5412289 _69904)). Qed.
Lemma lem5412291 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5412292 (_69904 : int) : (term668 _69904) = term632.
Proof. exact (MK_COMB (@lem5412291) (@lem5412290 _69904)). Qed.
Lemma lem5412293 (_69905 : int) : (term807 _69905) = (term743 _69905).
Proof. exact (@lem1982759 (real_of_int _69905) (term281 _69905) term256). Qed.
Lemma lem5412294 (_69905 : int) : (term614 _69905) = (term615 _69905).
Proof. exact (@lem1982715 term256 (real_of_int _69905)). Qed.
Lemma lem5412296 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5412297 : term193 = term290.
Proof. exact (@lem5412296 term79). Qed.
Lemma lem5412299 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5412300 : term256 = term257.
Proof. exact (@lem5412299 term79). Qed.
Lemma lem5412301 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5412302 : term616 = term617.
Proof. exact (MK_COMB (@lem5412301) (@lem5412300)). Qed.
Lemma lem5412303 : term618 = term619.
Proof. exact (MK_COMB (@lem5412302) (@lem5412297)). Qed.
Lemma lem5412304 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5412306 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412307 : term314 = term315.
Proof. exact (@lem5412306 (NUMERAL 0) term79). Qed.
Lemma lem5412308 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412309 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412310 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412309 h1) (fun h1 : term315 = True => @lem5412308)). Qed.
Lemma lem5412311 : term315 = True.
Proof. exact (EQ_MP (@lem5412310) (@lem5412308)). Qed.
Lemma lem5412312 : term314 = True.
Proof. exact (TRANS (@lem5412307) (@lem5412311)). Qed.
Lemma lem5412313 : True = term314.
Proof. exact (SYM (@lem5412312)). Qed.
Lemma lem5412314 : term314.
Proof. exact (EQ_MP (@lem5412313) (@lem0)). Qed.
Lemma lem5412315 : term621.
Proof. exact (@lem5412304 (@lem5412314)). Qed.
Lemma lem5412317 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412318 : term314 = term315.
Proof. exact (@lem5412317 (NUMERAL 0) term79). Qed.
Lemma lem5412319 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412320 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412321 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412320 h1) (fun h1 : term315 = True => @lem5412319)). Qed.
Lemma lem5412322 : term315 = True.
Proof. exact (EQ_MP (@lem5412321) (@lem5412319)). Qed.
Lemma lem5412323 : term314 = True.
Proof. exact (TRANS (@lem5412318) (@lem5412322)). Qed.
Lemma lem5412324 : True = term314.
Proof. exact (SYM (@lem5412323)). Qed.
Lemma lem5412325 : term314.
Proof. exact (EQ_MP (@lem5412324) (@lem0)). Qed.
Lemma lem5412326 : term622.
Proof. exact (@lem5412315 (@lem5412325)). Qed.
Lemma lem5412328 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412329 : term314 = term315.
Proof. exact (@lem5412328 (NUMERAL 0) term79). Qed.
Lemma lem5412330 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412331 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412332 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412331 h1) (fun h1 : term315 = True => @lem5412330)). Qed.
Lemma lem5412333 : term315 = True.
Proof. exact (EQ_MP (@lem5412332) (@lem5412330)). Qed.
Lemma lem5412334 : term314 = True.
Proof. exact (TRANS (@lem5412329) (@lem5412333)). Qed.
Lemma lem5412335 : True = term314.
Proof. exact (SYM (@lem5412334)). Qed.
Lemma lem5412336 : term314.
Proof. exact (EQ_MP (@lem5412335) (@lem0)). Qed.
Lemma lem5412337 : term623.
Proof. exact (@lem5412326 (@lem5412336)). Qed.
Lemma lem5412339 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5412340 : term265 = term266.
Proof. exact (@lem5412339 term79 term79). Qed.
Lemma lem5412341 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412342 : term268 = term79.
Proof. exact (EQ_MP (@lem5412341) (@lem940073)). Qed.
Lemma lem5412343 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412344 : term266 = term193.
Proof. exact (MK_COMB (@lem5412343) (@lem5412342)). Qed.
Lemma lem5412345 : term265 = term193.
Proof. exact (TRANS (@lem5412340) (@lem5412344)). Qed.
Lemma lem5412347 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5412348 : term291 = term296.
Proof. exact (@lem5412347 term79 term79). Qed.
Lemma lem5412349 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412350 : term268 = term79.
Proof. exact (EQ_MP (@lem5412349) (@lem940073)). Qed.
Lemma lem5412351 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412352 : term266 = term193.
Proof. exact (MK_COMB (@lem5412351) (@lem5412350)). Qed.
Lemma lem5412353 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5412354 : term296 = term256.
Proof. exact (MK_COMB (@lem5412353) (@lem5412352)). Qed.
Lemma lem5412355 : term291 = term256.
Proof. exact (TRANS (@lem5412348) (@lem5412354)). Qed.
Lemma lem5412356 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5412357 : term624 = term616.
Proof. exact (MK_COMB (@lem5412356) (@lem5412355)). Qed.
Lemma lem5412358 : term625 = term618.
Proof. exact (MK_COMB (@lem5412357) (@lem5412345)). Qed.
Lemma lem5412360 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5412361 : term618 = term182.
Proof. exact (@lem5412360 term79). Qed.
Lemma lem5412362 : term625 = term182.
Proof. exact (TRANS (@lem5412358) (@lem5412361)). Qed.
Lemma lem5412363 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5412364 : term627 = term403.
Proof. exact (MK_COMB (@lem5412363) (@lem5412362)). Qed.
Lemma lem5412365 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5412366 : term628 = term405.
Proof. exact (MK_COMB (@lem5412364) (@lem5412365)). Qed.
Lemma lem5412368 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5412369 : term405 = term182.
Proof. exact (@lem5412368 term79). Qed.
Lemma lem5412370 : term628 = term182.
Proof. exact (TRANS (@lem5412366) (@lem5412369)). Qed.
Lemma lem5412372 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5412373 : term265 = term266.
Proof. exact (@lem5412372 term79 term79). Qed.
Lemma lem5412374 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412375 : term268 = term79.
Proof. exact (EQ_MP (@lem5412374) (@lem940073)). Qed.
Lemma lem5412376 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412377 : term266 = term193.
Proof. exact (MK_COMB (@lem5412376) (@lem5412375)). Qed.
Lemma lem5412378 : term265 = term193.
Proof. exact (TRANS (@lem5412373) (@lem5412377)). Qed.
Lemma lem5412379 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5412380 : term407 = term405.
Proof. exact (MK_COMB (@lem5412379) (@lem5412378)). Qed.
Lemma lem5412382 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5412383 : term405 = term182.
Proof. exact (@lem5412382 term79). Qed.
Lemma lem5412384 : term407 = term182.
Proof. exact (TRANS (@lem5412380) (@lem5412383)). Qed.
Lemma lem5412385 : term182 = term407.
Proof. exact (SYM (@lem5412384)). Qed.
Lemma lem5412386 : term628 = term407.
Proof. exact (TRANS (@lem5412370) (@lem5412385)). Qed.
Lemma lem5412387 : term619 = term253.
Proof. exact (@lem5412337 (@lem5412386)). Qed.
Lemma lem5412388 : term618 = term253.
Proof. exact (TRANS (@lem5412303) (@lem5412387)). Qed.
Lemma lem5412390 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5412391 : term253 = term182.
Proof. exact (@lem5412390 term182). Qed.
Lemma lem5412392 : term618 = term182.
Proof. exact (TRANS (@lem5412388) (@lem5412391)). Qed.
Lemma lem5412393 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5412394 : term629 = term403.
Proof. exact (MK_COMB (@lem5412393) (@lem5412392)). Qed.
Lemma lem5412395 (_69905 : int) : (real_of_int _69905) = (real_of_int _69905).
Proof. exact (eq_refl (real_of_int _69905)). Qed.
Lemma lem5412396 (_69905 : int) : (term615 _69905) = (term630 _69905).
Proof. exact (MK_COMB (@lem5412394) (@lem5412395 _69905)). Qed.
Lemma lem5412397 (_69905 : int) : (term614 _69905) = (term630 _69905).
Proof. exact (TRANS (@lem5412294 _69905) (@lem5412396 _69905)). Qed.
Lemma lem5412398 (_69905 : int) : (term630 _69905) = term182.
Proof. exact (@lem1982719 (real_of_int _69905)). Qed.
Lemma lem5412399 (_69905 : int) : (term614 _69905) = term182.
Proof. exact (TRANS (@lem5412397 _69905) (@lem5412398 _69905)). Qed.
Lemma lem5412400 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5412401 (_69905 : int) : (term631 _69905) = term632.
Proof. exact (MK_COMB (@lem5412400) (@lem5412399 _69905)). Qed.
Lemma lem5412402 : term256 = term256.
Proof. exact (eq_refl term256). Qed.
Lemma lem5412403 (_69905 : int) : (term743 _69905) = term682.
Proof. exact (MK_COMB (@lem5412401 _69905) (@lem5412402)). Qed.
Lemma lem5412404 (_69905 : int) : (term807 _69905) = term682.
Proof. exact (TRANS (@lem5412293 _69905) (@lem5412403 _69905)). Qed.
Lemma lem5412405 : term682 = term256.
Proof. exact (@lem1982721 term256). Qed.
Lemma lem5412406 (_69905 : int) : (term807 _69905) = term256.
Proof. exact (TRANS (@lem5412404 _69905) (@lem5412405)). Qed.
Lemma lem5412407 (_69904 : int) (_69905 : int) : (term806 _69904 _69905) = term682.
Proof. exact (MK_COMB (@lem5412292 _69904) (@lem5412406 _69905)). Qed.
Lemma lem5412408 (_69904 : int) (_69905 : int) : (term805 _69904 _69905) = term682.
Proof. exact (TRANS (@lem5412184 _69904 _69905) (@lem5412407 _69904 _69905)). Qed.
Lemma lem5412409 : term682 = term256.
Proof. exact (@lem1982721 term256). Qed.
Lemma lem5412410 (_69904 : int) (_69905 : int) : (term805 _69904 _69905) = term256.
Proof. exact (TRANS (@lem5412408 _69904 _69905) (@lem5412409)). Qed.
Lemma lem5412411 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5412412 (_69904 : int) (_69905 : int) : (term808 _69904 _69905) = term684.
Proof. exact (MK_COMB (@lem5412411) (@lem5412410 _69904 _69905)). Qed.
Lemma lem5412413 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5412414 (_69904 : int) (_69905 : int) : (term804 _69904 _69905) = term685.
Proof. exact (MK_COMB (@lem5412412 _69904 _69905) (@lem5412413)). Qed.
Lemma lem5412415 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : term685.
Proof. exact (EQ_MP (@lem5412414 _69904 _69905) (@lem5412183 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412417 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5412418 : term685 = term686.
Proof. exact (@lem5412417 term182 term256). Qed.
Lemma lem5412420 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5412421 : term256 = term257.
Proof. exact (@lem5412420 term79). Qed.
Lemma lem5412423 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5412424 : term182 = term253.
Proof. exact (@lem5412423 (NUMERAL 0)). Qed.
Lemma lem5412425 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5412426 : term184 = term687.
Proof. exact (MK_COMB (@lem5412425) (@lem5412424)). Qed.
Lemma lem5412427 : term686 = term688.
Proof. exact (MK_COMB (@lem5412426) (@lem5412421)). Qed.
Lemma lem5412428 : term689.
Proof. exact (@lem1980026 term182 term193 term256 term193). Qed.
Lemma lem5412430 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412431 : term314 = term315.
Proof. exact (@lem5412430 (NUMERAL 0) term79). Qed.
Lemma lem5412432 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412433 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412434 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412433 h1) (fun h1 : term315 = True => @lem5412432)). Qed.
Lemma lem5412435 : term315 = True.
Proof. exact (EQ_MP (@lem5412434) (@lem5412432)). Qed.
Lemma lem5412436 : term314 = True.
Proof. exact (TRANS (@lem5412431) (@lem5412435)). Qed.
Lemma lem5412437 : True = term314.
Proof. exact (SYM (@lem5412436)). Qed.
Lemma lem5412438 : term314.
Proof. exact (EQ_MP (@lem5412437) (@lem0)). Qed.
Lemma lem5412439 : term690.
Proof. exact (@lem5412428 (@lem5412438)). Qed.
Lemma lem5412441 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412442 : term314 = term315.
Proof. exact (@lem5412441 (NUMERAL 0) term79). Qed.
Lemma lem5412443 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412444 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412445 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412444 h1) (fun h1 : term315 = True => @lem5412443)). Qed.
Lemma lem5412446 : term315 = True.
Proof. exact (EQ_MP (@lem5412445) (@lem5412443)). Qed.
Lemma lem5412447 : term314 = True.
Proof. exact (TRANS (@lem5412442) (@lem5412446)). Qed.
Lemma lem5412448 : True = term314.
Proof. exact (SYM (@lem5412447)). Qed.
Lemma lem5412449 : term314.
Proof. exact (EQ_MP (@lem5412448) (@lem0)). Qed.
Lemma lem5412450 : term688 = term691.
Proof. exact (@lem5412439 (@lem5412449)). Qed.
Lemma lem5412452 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5412453 : term291 = term296.
Proof. exact (@lem5412452 term79 term79). Qed.
Lemma lem5412454 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412455 : term268 = term79.
Proof. exact (EQ_MP (@lem5412454) (@lem940073)). Qed.
Lemma lem5412456 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412457 : term266 = term193.
Proof. exact (MK_COMB (@lem5412456) (@lem5412455)). Qed.
Lemma lem5412458 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5412459 : term296 = term256.
Proof. exact (MK_COMB (@lem5412458) (@lem5412457)). Qed.
Lemma lem5412460 : term291 = term256.
Proof. exact (TRANS (@lem5412453) (@lem5412459)). Qed.
Lemma lem5412462 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5412463 : term405 = term182.
Proof. exact (@lem5412462 term79). Qed.
Lemma lem5412464 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5412465 : term692 = term184.
Proof. exact (MK_COMB (@lem5412464) (@lem5412463)). Qed.
Lemma lem5412466 : term691 = term686.
Proof. exact (MK_COMB (@lem5412465) (@lem5412460)). Qed.
Lemma lem5412468 (m : nat) (n : nat) : (term693 m n) = (term694 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5412469 : term686 = term695.
Proof. exact (@lem5412468 (NUMERAL 0) term79). Qed.
Lemma lem5412470 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412471 (h1 : term316 = (BIT1 0)) : (term79 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5412472 : (term316 = (BIT1 0)) = ((term79 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412471 h1) (fun h1 : (term79 = (NUMERAL 0)) = False => @lem5412470)). Qed.
Lemma lem5412473 : (term79 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5412472) (@lem5412470)). Qed.
Lemma lem5412474 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5412475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5412476 : term696 = (and True).
Proof. exact (MK_COMB (@lem5412475) (@lem5412474)). Qed.
Lemma lem5412477 : term695 = (True /\ False).
Proof. exact (MK_COMB (@lem5412476) (@lem5412473)). Qed.
Lemma lem5412479 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5412480 : term695 = False.
Proof. exact (TRANS (@lem5412477) (@lem5412479)). Qed.
Lemma lem5412481 : term686 = False.
Proof. exact (TRANS (@lem5412469) (@lem5412480)). Qed.
Lemma lem5412482 : term691 = False.
Proof. exact (TRANS (@lem5412466) (@lem5412481)). Qed.
Lemma lem5412483 : term688 = False.
Proof. exact (TRANS (@lem5412450) (@lem5412482)). Qed.
Lemma lem5412484 : term686 = False.
Proof. exact (TRANS (@lem5412427) (@lem5412483)). Qed.
Lemma lem5412485 : term685 = False.
Proof. exact (TRANS (@lem5412418) (@lem5412484)). Qed.
Lemma lem5412486 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term797 _69903 _69904 _69905) : False.
Proof. exact (EQ_MP (@lem5412485) (@lem5412415 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412487 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term809 _69903 _69904 _69905.
Proof. exact (h1). Qed.
Lemma lem5412488 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term558 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5412487 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412490 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term527 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5412488 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412492 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term496 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5412490 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412494 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term465 _69903 _69904 _69905.
Proof. exact (proj2 (@lem5412492 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412496 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term440 _69904 _69905.
Proof. exact (proj2 (@lem5412494 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412497 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term386 _69903 _69904 _69905.
Proof. exact (proj1 (@lem5412494 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412498 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term385 _69904 _69905.
Proof. exact (proj2 (@lem5412497 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412501 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term359 _69904 _69905.
Proof. exact (proj1 (@lem5412496 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412503 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5412504 : term583 = term314.
Proof. exact (@lem5412503 term182 term193). Qed.
Lemma lem5412506 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5412507 : term193 = term290.
Proof. exact (@lem5412506 term79). Qed.
Lemma lem5412509 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5412510 : term182 = term253.
Proof. exact (@lem5412509 (NUMERAL 0)). Qed.
Lemma lem5412511 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5412512 : term584 = term585.
Proof. exact (MK_COMB (@lem5412511) (@lem5412510)). Qed.
Lemma lem5412513 : term314 = term586.
Proof. exact (MK_COMB (@lem5412512) (@lem5412507)). Qed.
Lemma lem5412514 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5412516 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412517 : term314 = term315.
Proof. exact (@lem5412516 (NUMERAL 0) term79). Qed.
Lemma lem5412518 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412519 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412520 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412519 h1) (fun h1 : term315 = True => @lem5412518)). Qed.
Lemma lem5412521 : term315 = True.
Proof. exact (EQ_MP (@lem5412520) (@lem5412518)). Qed.
Lemma lem5412522 : term314 = True.
Proof. exact (TRANS (@lem5412517) (@lem5412521)). Qed.
Lemma lem5412523 : True = term314.
Proof. exact (SYM (@lem5412522)). Qed.
Lemma lem5412524 : term314.
Proof. exact (EQ_MP (@lem5412523) (@lem0)). Qed.
Lemma lem5412525 : term588.
Proof. exact (@lem5412514 (@lem5412524)). Qed.
Lemma lem5412527 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412528 : term314 = term315.
Proof. exact (@lem5412527 (NUMERAL 0) term79). Qed.
Lemma lem5412529 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412530 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412531 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412530 h1) (fun h1 : term315 = True => @lem5412529)). Qed.
Lemma lem5412532 : term315 = True.
Proof. exact (EQ_MP (@lem5412531) (@lem5412529)). Qed.
Lemma lem5412533 : term314 = True.
Proof. exact (TRANS (@lem5412528) (@lem5412532)). Qed.
Lemma lem5412534 : True = term314.
Proof. exact (SYM (@lem5412533)). Qed.
Lemma lem5412535 : term314.
Proof. exact (EQ_MP (@lem5412534) (@lem0)). Qed.
Lemma lem5412536 : term586 = term589.
Proof. exact (@lem5412525 (@lem5412535)). Qed.
Lemma lem5412538 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5412539 : term265 = term266.
Proof. exact (@lem5412538 term79 term79). Qed.
Lemma lem5412540 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412541 : term268 = term79.
Proof. exact (EQ_MP (@lem5412540) (@lem940073)). Qed.
Lemma lem5412542 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412543 : term266 = term193.
Proof. exact (MK_COMB (@lem5412542) (@lem5412541)). Qed.
Lemma lem5412544 : term265 = term193.
Proof. exact (TRANS (@lem5412539) (@lem5412543)). Qed.
Lemma lem5412546 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5412547 : term405 = term182.
Proof. exact (@lem5412546 term79). Qed.
Lemma lem5412548 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5412549 : term590 = term584.
Proof. exact (MK_COMB (@lem5412548) (@lem5412547)). Qed.
Lemma lem5412550 : term589 = term314.
Proof. exact (MK_COMB (@lem5412549) (@lem5412544)). Qed.
Lemma lem5412552 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412553 : term314 = term315.
Proof. exact (@lem5412552 (NUMERAL 0) term79). Qed.
Lemma lem5412554 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412555 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412556 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412555 h1) (fun h1 : term315 = True => @lem5412554)). Qed.
Lemma lem5412557 : term315 = True.
Proof. exact (EQ_MP (@lem5412556) (@lem5412554)). Qed.
Lemma lem5412558 : term314 = True.
Proof. exact (TRANS (@lem5412553) (@lem5412557)). Qed.
Lemma lem5412559 : term589 = True.
Proof. exact (TRANS (@lem5412550) (@lem5412558)). Qed.
Lemma lem5412560 : term586 = True.
Proof. exact (TRANS (@lem5412536) (@lem5412559)). Qed.
Lemma lem5412561 : term314 = True.
Proof. exact (TRANS (@lem5412513) (@lem5412560)). Qed.
Lemma lem5412562 : term583 = True.
Proof. exact (TRANS (@lem5412504) (@lem5412561)). Qed.
Lemma lem5412563 : True = term583.
Proof. exact (SYM (@lem5412562)). Qed.
Lemma lem5412564 : term583.
Proof. exact (EQ_MP (@lem5412563) (@lem0)). Qed.
Lemma lem5412565 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term698 _69904 _69905.
Proof. exact (conj (@lem5412564) (@lem5412501 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412567 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5412568 (_69904 : int) (_69905 : int) : term699 _69904 _69905.
Proof. exact (@lem5412567 term193 (term356 _69904 _69905)). Qed.
Lemma lem5412569 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term700 _69904 _69905.
Proof. exact (@lem5412568 _69904 _69905 (@lem5412565 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412570 (_69904 : int) (_69905 : int) : (term701 _69904 _69905) = (term356 _69904 _69905).
Proof. exact (@lem1982733 (term356 _69904 _69905)). Qed.
Lemma lem5412571 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5412572 (_69904 : int) (_69905 : int) : (term702 _69904 _69905) = (term358 _69904 _69905).
Proof. exact (MK_COMB (@lem5412571) (@lem5412570 _69904 _69905)). Qed.
Lemma lem5412573 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5412574 (_69904 : int) (_69905 : int) : (term700 _69904 _69905) = (term359 _69904 _69905).
Proof. exact (MK_COMB (@lem5412572 _69904 _69905) (@lem5412573)). Qed.
Lemma lem5412575 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term359 _69904 _69905.
Proof. exact (EQ_MP (@lem5412574 _69904 _69905) (@lem5412569 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412577 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5412578 : term583 = term314.
Proof. exact (@lem5412577 term182 term193). Qed.
Lemma lem5412580 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5412581 : term193 = term290.
Proof. exact (@lem5412580 term79). Qed.
Lemma lem5412583 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5412584 : term182 = term253.
Proof. exact (@lem5412583 (NUMERAL 0)). Qed.
Lemma lem5412585 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5412586 : term584 = term585.
Proof. exact (MK_COMB (@lem5412585) (@lem5412584)). Qed.
Lemma lem5412587 : term314 = term586.
Proof. exact (MK_COMB (@lem5412586) (@lem5412581)). Qed.
Lemma lem5412588 : term587.
Proof. exact (@lem1980255 term182 term193 term193 term193). Qed.
Lemma lem5412590 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412591 : term314 = term315.
Proof. exact (@lem5412590 (NUMERAL 0) term79). Qed.
Lemma lem5412592 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412593 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412594 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412593 h1) (fun h1 : term315 = True => @lem5412592)). Qed.
Lemma lem5412595 : term315 = True.
Proof. exact (EQ_MP (@lem5412594) (@lem5412592)). Qed.
Lemma lem5412596 : term314 = True.
Proof. exact (TRANS (@lem5412591) (@lem5412595)). Qed.
Lemma lem5412597 : True = term314.
Proof. exact (SYM (@lem5412596)). Qed.
Lemma lem5412598 : term314.
Proof. exact (EQ_MP (@lem5412597) (@lem0)). Qed.
Lemma lem5412599 : term588.
Proof. exact (@lem5412588 (@lem5412598)). Qed.
Lemma lem5412601 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412602 : term314 = term315.
Proof. exact (@lem5412601 (NUMERAL 0) term79). Qed.
Lemma lem5412603 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412604 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412605 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412604 h1) (fun h1 : term315 = True => @lem5412603)). Qed.
Lemma lem5412606 : term315 = True.
Proof. exact (EQ_MP (@lem5412605) (@lem5412603)). Qed.
Lemma lem5412607 : term314 = True.
Proof. exact (TRANS (@lem5412602) (@lem5412606)). Qed.
Lemma lem5412608 : True = term314.
Proof. exact (SYM (@lem5412607)). Qed.
Lemma lem5412609 : term314.
Proof. exact (EQ_MP (@lem5412608) (@lem0)). Qed.
Lemma lem5412610 : term586 = term589.
Proof. exact (@lem5412599 (@lem5412609)). Qed.
Lemma lem5412612 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5412613 : term265 = term266.
Proof. exact (@lem5412612 term79 term79). Qed.
Lemma lem5412614 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412615 : term268 = term79.
Proof. exact (EQ_MP (@lem5412614) (@lem940073)). Qed.
Lemma lem5412616 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412617 : term266 = term193.
Proof. exact (MK_COMB (@lem5412616) (@lem5412615)). Qed.
Lemma lem5412618 : term265 = term193.
Proof. exact (TRANS (@lem5412613) (@lem5412617)). Qed.
Lemma lem5412620 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5412621 : term405 = term182.
Proof. exact (@lem5412620 term79). Qed.
Lemma lem5412622 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5412623 : term590 = term584.
Proof. exact (MK_COMB (@lem5412622) (@lem5412621)). Qed.
Lemma lem5412624 : term589 = term314.
Proof. exact (MK_COMB (@lem5412623) (@lem5412618)). Qed.
Lemma lem5412626 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412627 : term314 = term315.
Proof. exact (@lem5412626 (NUMERAL 0) term79). Qed.
Lemma lem5412628 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412629 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412630 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412629 h1) (fun h1 : term315 = True => @lem5412628)). Qed.
Lemma lem5412631 : term315 = True.
Proof. exact (EQ_MP (@lem5412630) (@lem5412628)). Qed.
Lemma lem5412632 : term314 = True.
Proof. exact (TRANS (@lem5412627) (@lem5412631)). Qed.
Lemma lem5412633 : term589 = True.
Proof. exact (TRANS (@lem5412624) (@lem5412632)). Qed.
Lemma lem5412634 : term586 = True.
Proof. exact (TRANS (@lem5412610) (@lem5412633)). Qed.
Lemma lem5412635 : term314 = True.
Proof. exact (TRANS (@lem5412587) (@lem5412634)). Qed.
Lemma lem5412636 : term583 = True.
Proof. exact (TRANS (@lem5412578) (@lem5412635)). Qed.
Lemma lem5412637 : True = term583.
Proof. exact (SYM (@lem5412636)). Qed.
Lemma lem5412638 : term583.
Proof. exact (EQ_MP (@lem5412637) (@lem0)). Qed.
Lemma lem5412639 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term770 _69904 _69905.
Proof. exact (conj (@lem5412638) (@lem5412498 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412641 (x : real) (y : real) : term592 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5412642 (_69904 : int) (_69905 : int) : term771 _69904 _69905.
Proof. exact (@lem5412641 term193 (term383 _69904 _69905)). Qed.
Lemma lem5412643 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term772 _69904 _69905.
Proof. exact (@lem5412642 _69904 _69905 (@lem5412639 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412644 (_69904 : int) (_69905 : int) : (term773 _69904 _69905) = (term383 _69904 _69905).
Proof. exact (@lem1982733 (term383 _69904 _69905)). Qed.
Lemma lem5412645 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5412646 (_69904 : int) (_69905 : int) : (term774 _69904 _69905) = (term384 _69904 _69905).
Proof. exact (MK_COMB (@lem5412645) (@lem5412644 _69904 _69905)). Qed.
Lemma lem5412647 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5412648 (_69904 : int) (_69905 : int) : (term772 _69904 _69905) = (term385 _69904 _69905).
Proof. exact (MK_COMB (@lem5412646 _69904 _69905) (@lem5412647)). Qed.
Lemma lem5412649 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term385 _69904 _69905.
Proof. exact (EQ_MP (@lem5412648 _69904 _69905) (@lem5412643 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412650 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term810 _69904 _69905.
Proof. exact (conj (@lem5412649 _69903 _69904 _69905 h1) (@lem5412575 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412652 (x : real) (y : real) : term662 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5412653 (_69904 : int) (_69905 : int) : term811 _69904 _69905.
Proof. exact (@lem5412652 (term383 _69904 _69905) (term356 _69904 _69905)). Qed.
Lemma lem5412654 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term724 _69904 _69905.
Proof. exact (@lem5412653 _69904 _69905 (@lem5412650 _69903 _69904 _69905 h1)). Qed.
Lemma lem5412655 (_69904 : int) (_69905 : int) : (term725 _69904 _69905) = (term726 _69904 _69905).
Proof. exact (@lem1982753 (real_of_int _69904) (term281 _69904) (term382 _69905) (term727 _69905)). Qed.
Lemma lem5412656 (_69904 : int) : (term614 _69904) = (term615 _69904).
Proof. exact (@lem1982715 term256 (real_of_int _69904)). Qed.
Lemma lem5412658 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5412659 : term193 = term290.
Proof. exact (@lem5412658 term79). Qed.
Lemma lem5412661 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5412662 : term256 = term257.
Proof. exact (@lem5412661 term79). Qed.
Lemma lem5412663 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5412664 : term616 = term617.
Proof. exact (MK_COMB (@lem5412663) (@lem5412662)). Qed.
Lemma lem5412665 : term618 = term619.
Proof. exact (MK_COMB (@lem5412664) (@lem5412659)). Qed.
Lemma lem5412666 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5412668 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412669 : term314 = term315.
Proof. exact (@lem5412668 (NUMERAL 0) term79). Qed.
Lemma lem5412670 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412671 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412672 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412671 h1) (fun h1 : term315 = True => @lem5412670)). Qed.
Lemma lem5412673 : term315 = True.
Proof. exact (EQ_MP (@lem5412672) (@lem5412670)). Qed.
Lemma lem5412674 : term314 = True.
Proof. exact (TRANS (@lem5412669) (@lem5412673)). Qed.
Lemma lem5412675 : True = term314.
Proof. exact (SYM (@lem5412674)). Qed.
Lemma lem5412676 : term314.
Proof. exact (EQ_MP (@lem5412675) (@lem0)). Qed.
Lemma lem5412677 : term621.
Proof. exact (@lem5412666 (@lem5412676)). Qed.
Lemma lem5412679 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412680 : term314 = term315.
Proof. exact (@lem5412679 (NUMERAL 0) term79). Qed.
Lemma lem5412681 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412682 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412683 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412682 h1) (fun h1 : term315 = True => @lem5412681)). Qed.
Lemma lem5412684 : term315 = True.
Proof. exact (EQ_MP (@lem5412683) (@lem5412681)). Qed.
Lemma lem5412685 : term314 = True.
Proof. exact (TRANS (@lem5412680) (@lem5412684)). Qed.
Lemma lem5412686 : True = term314.
Proof. exact (SYM (@lem5412685)). Qed.
Lemma lem5412687 : term314.
Proof. exact (EQ_MP (@lem5412686) (@lem0)). Qed.
Lemma lem5412688 : term622.
Proof. exact (@lem5412677 (@lem5412687)). Qed.
Lemma lem5412690 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412691 : term314 = term315.
Proof. exact (@lem5412690 (NUMERAL 0) term79). Qed.
Lemma lem5412692 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412693 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412694 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412693 h1) (fun h1 : term315 = True => @lem5412692)). Qed.
Lemma lem5412695 : term315 = True.
Proof. exact (EQ_MP (@lem5412694) (@lem5412692)). Qed.
Lemma lem5412696 : term314 = True.
Proof. exact (TRANS (@lem5412691) (@lem5412695)). Qed.
Lemma lem5412697 : True = term314.
Proof. exact (SYM (@lem5412696)). Qed.
Lemma lem5412698 : term314.
Proof. exact (EQ_MP (@lem5412697) (@lem0)). Qed.
Lemma lem5412699 : term623.
Proof. exact (@lem5412688 (@lem5412698)). Qed.
Lemma lem5412701 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5412702 : term265 = term266.
Proof. exact (@lem5412701 term79 term79). Qed.
Lemma lem5412703 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412704 : term268 = term79.
Proof. exact (EQ_MP (@lem5412703) (@lem940073)). Qed.
Lemma lem5412705 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412706 : term266 = term193.
Proof. exact (MK_COMB (@lem5412705) (@lem5412704)). Qed.
Lemma lem5412707 : term265 = term193.
Proof. exact (TRANS (@lem5412702) (@lem5412706)). Qed.
Lemma lem5412709 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5412710 : term291 = term296.
Proof. exact (@lem5412709 term79 term79). Qed.
Lemma lem5412711 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412712 : term268 = term79.
Proof. exact (EQ_MP (@lem5412711) (@lem940073)). Qed.
Lemma lem5412713 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412714 : term266 = term193.
Proof. exact (MK_COMB (@lem5412713) (@lem5412712)). Qed.
Lemma lem5412715 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5412716 : term296 = term256.
Proof. exact (MK_COMB (@lem5412715) (@lem5412714)). Qed.
Lemma lem5412717 : term291 = term256.
Proof. exact (TRANS (@lem5412710) (@lem5412716)). Qed.
Lemma lem5412718 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5412719 : term624 = term616.
Proof. exact (MK_COMB (@lem5412718) (@lem5412717)). Qed.
Lemma lem5412720 : term625 = term618.
Proof. exact (MK_COMB (@lem5412719) (@lem5412707)). Qed.
Lemma lem5412722 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5412723 : term618 = term182.
Proof. exact (@lem5412722 term79). Qed.
Lemma lem5412724 : term625 = term182.
Proof. exact (TRANS (@lem5412720) (@lem5412723)). Qed.
Lemma lem5412725 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5412726 : term627 = term403.
Proof. exact (MK_COMB (@lem5412725) (@lem5412724)). Qed.
Lemma lem5412727 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5412728 : term628 = term405.
Proof. exact (MK_COMB (@lem5412726) (@lem5412727)). Qed.
Lemma lem5412730 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5412731 : term405 = term182.
Proof. exact (@lem5412730 term79). Qed.
Lemma lem5412732 : term628 = term182.
Proof. exact (TRANS (@lem5412728) (@lem5412731)). Qed.
Lemma lem5412734 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5412735 : term265 = term266.
Proof. exact (@lem5412734 term79 term79). Qed.
Lemma lem5412736 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412737 : term268 = term79.
Proof. exact (EQ_MP (@lem5412736) (@lem940073)). Qed.
Lemma lem5412738 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412739 : term266 = term193.
Proof. exact (MK_COMB (@lem5412738) (@lem5412737)). Qed.
Lemma lem5412740 : term265 = term193.
Proof. exact (TRANS (@lem5412735) (@lem5412739)). Qed.
Lemma lem5412741 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5412742 : term407 = term405.
Proof. exact (MK_COMB (@lem5412741) (@lem5412740)). Qed.
Lemma lem5412744 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5412745 : term405 = term182.
Proof. exact (@lem5412744 term79). Qed.
Lemma lem5412746 : term407 = term182.
Proof. exact (TRANS (@lem5412742) (@lem5412745)). Qed.
Lemma lem5412747 : term182 = term407.
Proof. exact (SYM (@lem5412746)). Qed.
Lemma lem5412748 : term628 = term407.
Proof. exact (TRANS (@lem5412732) (@lem5412747)). Qed.
Lemma lem5412749 : term619 = term253.
Proof. exact (@lem5412699 (@lem5412748)). Qed.
Lemma lem5412750 : term618 = term253.
Proof. exact (TRANS (@lem5412665) (@lem5412749)). Qed.
Lemma lem5412752 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5412753 : term253 = term182.
Proof. exact (@lem5412752 term182). Qed.
Lemma lem5412754 : term618 = term182.
Proof. exact (TRANS (@lem5412750) (@lem5412753)). Qed.
Lemma lem5412755 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5412756 : term629 = term403.
Proof. exact (MK_COMB (@lem5412755) (@lem5412754)). Qed.
Lemma lem5412757 (_69904 : int) : (real_of_int _69904) = (real_of_int _69904).
Proof. exact (eq_refl (real_of_int _69904)). Qed.
Lemma lem5412758 (_69904 : int) : (term615 _69904) = (term630 _69904).
Proof. exact (MK_COMB (@lem5412756) (@lem5412757 _69904)). Qed.
Lemma lem5412759 (_69904 : int) : (term614 _69904) = (term630 _69904).
Proof. exact (TRANS (@lem5412656 _69904) (@lem5412758 _69904)). Qed.
Lemma lem5412760 (_69904 : int) : (term630 _69904) = term182.
Proof. exact (@lem1982719 (real_of_int _69904)). Qed.
Lemma lem5412761 (_69904 : int) : (term614 _69904) = term182.
Proof. exact (TRANS (@lem5412759 _69904) (@lem5412760 _69904)). Qed.
Lemma lem5412762 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5412763 (_69904 : int) : (term631 _69904) = term632.
Proof. exact (MK_COMB (@lem5412762) (@lem5412761 _69904)). Qed.
Lemma lem5412764 (_69905 : int) : (term728 _69905) = (term729 _69905).
Proof. exact (@lem1982753 (term281 _69905) (real_of_int _69905) term193 term350). Qed.
Lemma lem5412765 (_69905 : int) : (term667 _69905) = (term615 _69905).
Proof. exact (@lem1982713 term256 (real_of_int _69905)). Qed.
Lemma lem5412767 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5412768 : term193 = term290.
Proof. exact (@lem5412767 term79). Qed.
Lemma lem5412770 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5412771 : term256 = term257.
Proof. exact (@lem5412770 term79). Qed.
Lemma lem5412772 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5412773 : term616 = term617.
Proof. exact (MK_COMB (@lem5412772) (@lem5412771)). Qed.
Lemma lem5412774 : term618 = term619.
Proof. exact (MK_COMB (@lem5412773) (@lem5412768)). Qed.
Lemma lem5412775 : term620.
Proof. exact (@lem1981473 term256 term193 term193 term193 term182 term193). Qed.
Lemma lem5412777 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412778 : term314 = term315.
Proof. exact (@lem5412777 (NUMERAL 0) term79). Qed.
Lemma lem5412779 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412780 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412781 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412780 h1) (fun h1 : term315 = True => @lem5412779)). Qed.
Lemma lem5412782 : term315 = True.
Proof. exact (EQ_MP (@lem5412781) (@lem5412779)). Qed.
Lemma lem5412783 : term314 = True.
Proof. exact (TRANS (@lem5412778) (@lem5412782)). Qed.
Lemma lem5412784 : True = term314.
Proof. exact (SYM (@lem5412783)). Qed.
Lemma lem5412785 : term314.
Proof. exact (EQ_MP (@lem5412784) (@lem0)). Qed.
Lemma lem5412786 : term621.
Proof. exact (@lem5412775 (@lem5412785)). Qed.
Lemma lem5412788 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412789 : term314 = term315.
Proof. exact (@lem5412788 (NUMERAL 0) term79). Qed.
Lemma lem5412790 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412791 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412792 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412791 h1) (fun h1 : term315 = True => @lem5412790)). Qed.
Lemma lem5412793 : term315 = True.
Proof. exact (EQ_MP (@lem5412792) (@lem5412790)). Qed.
Lemma lem5412794 : term314 = True.
Proof. exact (TRANS (@lem5412789) (@lem5412793)). Qed.
Lemma lem5412795 : True = term314.
Proof. exact (SYM (@lem5412794)). Qed.
Lemma lem5412796 : term314.
Proof. exact (EQ_MP (@lem5412795) (@lem0)). Qed.
Lemma lem5412797 : term622.
Proof. exact (@lem5412786 (@lem5412796)). Qed.
Lemma lem5412799 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412800 : term314 = term315.
Proof. exact (@lem5412799 (NUMERAL 0) term79). Qed.
Lemma lem5412801 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412802 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412803 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412802 h1) (fun h1 : term315 = True => @lem5412801)). Qed.
Lemma lem5412804 : term315 = True.
Proof. exact (EQ_MP (@lem5412803) (@lem5412801)). Qed.
Lemma lem5412805 : term314 = True.
Proof. exact (TRANS (@lem5412800) (@lem5412804)). Qed.
Lemma lem5412806 : True = term314.
Proof. exact (SYM (@lem5412805)). Qed.
Lemma lem5412807 : term314.
Proof. exact (EQ_MP (@lem5412806) (@lem0)). Qed.
Lemma lem5412808 : term623.
Proof. exact (@lem5412797 (@lem5412807)). Qed.
Lemma lem5412810 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5412811 : term265 = term266.
Proof. exact (@lem5412810 term79 term79). Qed.
Lemma lem5412812 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412813 : term268 = term79.
Proof. exact (EQ_MP (@lem5412812) (@lem940073)). Qed.
Lemma lem5412814 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412815 : term266 = term193.
Proof. exact (MK_COMB (@lem5412814) (@lem5412813)). Qed.
Lemma lem5412816 : term265 = term193.
Proof. exact (TRANS (@lem5412811) (@lem5412815)). Qed.
Lemma lem5412818 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5412819 : term291 = term296.
Proof. exact (@lem5412818 term79 term79). Qed.
Lemma lem5412820 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412821 : term268 = term79.
Proof. exact (EQ_MP (@lem5412820) (@lem940073)). Qed.
Lemma lem5412822 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412823 : term266 = term193.
Proof. exact (MK_COMB (@lem5412822) (@lem5412821)). Qed.
Lemma lem5412824 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5412825 : term296 = term256.
Proof. exact (MK_COMB (@lem5412824) (@lem5412823)). Qed.
Lemma lem5412826 : term291 = term256.
Proof. exact (TRANS (@lem5412819) (@lem5412825)). Qed.
Lemma lem5412827 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5412828 : term624 = term616.
Proof. exact (MK_COMB (@lem5412827) (@lem5412826)). Qed.
Lemma lem5412829 : term625 = term618.
Proof. exact (MK_COMB (@lem5412828) (@lem5412816)). Qed.
Lemma lem5412831 (m : nat) : (term626 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5412832 : term618 = term182.
Proof. exact (@lem5412831 term79). Qed.
Lemma lem5412833 : term625 = term182.
Proof. exact (TRANS (@lem5412829) (@lem5412832)). Qed.
Lemma lem5412834 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5412835 : term627 = term403.
Proof. exact (MK_COMB (@lem5412834) (@lem5412833)). Qed.
Lemma lem5412836 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5412837 : term628 = term405.
Proof. exact (MK_COMB (@lem5412835) (@lem5412836)). Qed.
Lemma lem5412839 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5412840 : term405 = term182.
Proof. exact (@lem5412839 term79). Qed.
Lemma lem5412841 : term628 = term182.
Proof. exact (TRANS (@lem5412837) (@lem5412840)). Qed.
Lemma lem5412843 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5412844 : term265 = term266.
Proof. exact (@lem5412843 term79 term79). Qed.
Lemma lem5412845 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412846 : term268 = term79.
Proof. exact (EQ_MP (@lem5412845) (@lem940073)). Qed.
Lemma lem5412847 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412848 : term266 = term193.
Proof. exact (MK_COMB (@lem5412847) (@lem5412846)). Qed.
Lemma lem5412849 : term265 = term193.
Proof. exact (TRANS (@lem5412844) (@lem5412848)). Qed.
Lemma lem5412850 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem5412851 : term407 = term405.
Proof. exact (MK_COMB (@lem5412850) (@lem5412849)). Qed.
Lemma lem5412853 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5412854 : term405 = term182.
Proof. exact (@lem5412853 term79). Qed.
Lemma lem5412855 : term407 = term182.
Proof. exact (TRANS (@lem5412851) (@lem5412854)). Qed.
Lemma lem5412856 : term182 = term407.
Proof. exact (SYM (@lem5412855)). Qed.
Lemma lem5412857 : term628 = term407.
Proof. exact (TRANS (@lem5412841) (@lem5412856)). Qed.
Lemma lem5412858 : term619 = term253.
Proof. exact (@lem5412808 (@lem5412857)). Qed.
Lemma lem5412859 : term618 = term253.
Proof. exact (TRANS (@lem5412774) (@lem5412858)). Qed.
Lemma lem5412861 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5412862 : term253 = term182.
Proof. exact (@lem5412861 term182). Qed.
Lemma lem5412863 : term618 = term182.
Proof. exact (TRANS (@lem5412859) (@lem5412862)). Qed.
Lemma lem5412864 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5412865 : term629 = term403.
Proof. exact (MK_COMB (@lem5412864) (@lem5412863)). Qed.
Lemma lem5412866 (_69905 : int) : (real_of_int _69905) = (real_of_int _69905).
Proof. exact (eq_refl (real_of_int _69905)). Qed.
Lemma lem5412867 (_69905 : int) : (term615 _69905) = (term630 _69905).
Proof. exact (MK_COMB (@lem5412865) (@lem5412866 _69905)). Qed.
Lemma lem5412868 (_69905 : int) : (term667 _69905) = (term630 _69905).
Proof. exact (TRANS (@lem5412765 _69905) (@lem5412867 _69905)). Qed.
Lemma lem5412869 (_69905 : int) : (term630 _69905) = term182.
Proof. exact (@lem1982719 (real_of_int _69905)). Qed.
Lemma lem5412870 (_69905 : int) : (term667 _69905) = term182.
Proof. exact (TRANS (@lem5412868 _69905) (@lem5412869 _69905)). Qed.
Lemma lem5412871 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5412872 (_69905 : int) : (term668 _69905) = term632.
Proof. exact (MK_COMB (@lem5412871) (@lem5412870 _69905)). Qed.
Lemma lem5412874 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5412875 : term350 = term353.
Proof. exact (@lem5412874 term326). Qed.
Lemma lem5412877 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5412878 : term193 = term290.
Proof. exact (@lem5412877 term79). Qed.
Lemma lem5412879 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5412880 : term307 = term308.
Proof. exact (MK_COMB (@lem5412879) (@lem5412878)). Qed.
Lemma lem5412881 : term671 = term672.
Proof. exact (MK_COMB (@lem5412880) (@lem5412875)). Qed.
Lemma lem5412882 : term673.
Proof. exact (@lem1981473 term193 term193 term350 term193 term256 term193). Qed.
Lemma lem5412884 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412885 : term314 = term315.
Proof. exact (@lem5412884 (NUMERAL 0) term79). Qed.
Lemma lem5412886 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412887 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412888 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412887 h1) (fun h1 : term315 = True => @lem5412886)). Qed.
Lemma lem5412889 : term315 = True.
Proof. exact (EQ_MP (@lem5412888) (@lem5412886)). Qed.
Lemma lem5412890 : term314 = True.
Proof. exact (TRANS (@lem5412885) (@lem5412889)). Qed.
Lemma lem5412891 : True = term314.
Proof. exact (SYM (@lem5412890)). Qed.
Lemma lem5412892 : term314.
Proof. exact (EQ_MP (@lem5412891) (@lem0)). Qed.
Lemma lem5412893 : term674.
Proof. exact (@lem5412882 (@lem5412892)). Qed.
Lemma lem5412895 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412896 : term314 = term315.
Proof. exact (@lem5412895 (NUMERAL 0) term79). Qed.
Lemma lem5412897 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412898 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412899 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412898 h1) (fun h1 : term315 = True => @lem5412897)). Qed.
Lemma lem5412900 : term315 = True.
Proof. exact (EQ_MP (@lem5412899) (@lem5412897)). Qed.
Lemma lem5412901 : term314 = True.
Proof. exact (TRANS (@lem5412896) (@lem5412900)). Qed.
Lemma lem5412902 : True = term314.
Proof. exact (SYM (@lem5412901)). Qed.
Lemma lem5412903 : term314.
Proof. exact (EQ_MP (@lem5412902) (@lem0)). Qed.
Lemma lem5412904 : term675.
Proof. exact (@lem5412893 (@lem5412903)). Qed.
Lemma lem5412906 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5412907 : term314 = term315.
Proof. exact (@lem5412906 (NUMERAL 0) term79). Qed.
Lemma lem5412908 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5412909 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5412910 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5412909 h1) (fun h1 : term315 = True => @lem5412908)). Qed.
Lemma lem5412911 : term315 = True.
Proof. exact (EQ_MP (@lem5412910) (@lem5412908)). Qed.
Lemma lem5412912 : term314 = True.
Proof. exact (TRANS (@lem5412907) (@lem5412911)). Qed.
Lemma lem5412913 : True = term314.
Proof. exact (SYM (@lem5412912)). Qed.
Lemma lem5412914 : term314.
Proof. exact (EQ_MP (@lem5412913) (@lem0)). Qed.
Lemma lem5412915 : term676.
Proof. exact (@lem5412904 (@lem5412914)). Qed.
Lemma lem5412917 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5412918 : term644 = term645.
Proof. exact (@lem5412917 term326 term79). Qed.
Lemma lem5412919 : term332 = term324.
Proof. exact (@lem996237 term324). Qed.
Lemma lem5412920 : (term332 = term324) = (term333 = term326).
Proof. exact (@lem1007663 term324 (BIT1 0) term324). Qed.
Lemma lem5412921 : term333 = term326.
Proof. exact (EQ_MP (@lem5412920) (@lem5412919)). Qed.
Lemma lem5412922 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412923 : term331 = term312.
Proof. exact (MK_COMB (@lem5412922) (@lem5412921)). Qed.
Lemma lem5412924 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5412925 : term645 = term350.
Proof. exact (MK_COMB (@lem5412924) (@lem5412923)). Qed.
Lemma lem5412926 : term644 = term350.
Proof. exact (TRANS (@lem5412918) (@lem5412925)). Qed.
Lemma lem5412928 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5412929 : term265 = term266.
Proof. exact (@lem5412928 term79 term79). Qed.
Lemma lem5412930 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412931 : term268 = term79.
Proof. exact (EQ_MP (@lem5412930) (@lem940073)). Qed.
Lemma lem5412932 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412933 : term266 = term193.
Proof. exact (MK_COMB (@lem5412932) (@lem5412931)). Qed.
Lemma lem5412934 : term265 = term193.
Proof. exact (TRANS (@lem5412929) (@lem5412933)). Qed.
Lemma lem5412935 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5412936 : term320 = term307.
Proof. exact (MK_COMB (@lem5412935) (@lem5412934)). Qed.
Lemma lem5412937 : term677 = term671.
Proof. exact (MK_COMB (@lem5412936) (@lem5412926)). Qed.
Lemma lem5412940 : term678 = term256.
Proof. exact (@lem1367771 term79 term79). Qed.
Lemma lem5412941 : term323 = term324.
Proof. exact (@lem706885). Qed.
Lemma lem5412942 : (term323 = term324) = (term325 = term326).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term324). Qed.
Lemma lem5412943 : term325 = term326.
Proof. exact (EQ_MP (@lem5412942) (@lem5412941)). Qed.
Lemma lem5412944 : term326 = term325.
Proof. exact (SYM (@lem5412943)). Qed.
Lemma lem5412945 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412946 : term312 = term322.
Proof. exact (MK_COMB (@lem5412945) (@lem5412944)). Qed.
Lemma lem5412947 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5412948 : term350 = term640.
Proof. exact (MK_COMB (@lem5412947) (@lem5412946)). Qed.
Lemma lem5412949 : term307 = term307.
Proof. exact (eq_refl term307). Qed.
Lemma lem5412950 : term671 = term678.
Proof. exact (MK_COMB (@lem5412949) (@lem5412948)). Qed.
Lemma lem5412951 : term671 = term256.
Proof. exact (TRANS (@lem5412950) (@lem5412940)). Qed.
Lemma lem5412952 : term677 = term256.
Proof. exact (TRANS (@lem5412937) (@lem5412951)). Qed.
Lemma lem5412953 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5412954 : term679 = term258.
Proof. exact (MK_COMB (@lem5412953) (@lem5412952)). Qed.
Lemma lem5412955 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem5412956 : term680 = term291.
Proof. exact (MK_COMB (@lem5412954) (@lem5412955)). Qed.
Lemma lem5412958 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5412959 : term291 = term296.
Proof. exact (@lem5412958 term79 term79). Qed.
Lemma lem5412960 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412961 : term268 = term79.
Proof. exact (EQ_MP (@lem5412960) (@lem940073)). Qed.
Lemma lem5412962 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412963 : term266 = term193.
Proof. exact (MK_COMB (@lem5412962) (@lem5412961)). Qed.
Lemma lem5412964 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5412965 : term296 = term256.
Proof. exact (MK_COMB (@lem5412964) (@lem5412963)). Qed.
Lemma lem5412966 : term291 = term256.
Proof. exact (TRANS (@lem5412959) (@lem5412965)). Qed.
Lemma lem5412967 : term680 = term256.
Proof. exact (TRANS (@lem5412956) (@lem5412966)). Qed.
Lemma lem5412969 (m : nat) (n : nat) : (term263 m n) = (term264 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5412970 : term265 = term266.
Proof. exact (@lem5412969 term79 term79). Qed.
Lemma lem5412971 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412972 : term268 = term79.
Proof. exact (EQ_MP (@lem5412971) (@lem940073)). Qed.
Lemma lem5412973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412974 : term266 = term193.
Proof. exact (MK_COMB (@lem5412973) (@lem5412972)). Qed.
Lemma lem5412975 : term265 = term193.
Proof. exact (TRANS (@lem5412970) (@lem5412974)). Qed.
Lemma lem5412976 : term258 = term258.
Proof. exact (eq_refl term258). Qed.
Lemma lem5412977 : term681 = term291.
Proof. exact (MK_COMB (@lem5412976) (@lem5412975)). Qed.
Lemma lem5412979 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5412980 : term291 = term296.
Proof. exact (@lem5412979 term79 term79). Qed.
Lemma lem5412981 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5412982 : term268 = term79.
Proof. exact (EQ_MP (@lem5412981) (@lem940073)). Qed.
Lemma lem5412983 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5412984 : term266 = term193.
Proof. exact (MK_COMB (@lem5412983) (@lem5412982)). Qed.
Lemma lem5412985 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5412986 : term296 = term256.
Proof. exact (MK_COMB (@lem5412985) (@lem5412984)). Qed.
Lemma lem5412987 : term291 = term256.
Proof. exact (TRANS (@lem5412980) (@lem5412986)). Qed.
Lemma lem5412988 : term681 = term256.
Proof. exact (TRANS (@lem5412977) (@lem5412987)). Qed.
Lemma lem5412989 : term256 = term681.
Proof. exact (SYM (@lem5412988)). Qed.
Lemma lem5412990 : term680 = term681.
Proof. exact (TRANS (@lem5412967) (@lem5412989)). Qed.
Lemma lem5412991 : term672 = term257.
Proof. exact (@lem5412915 (@lem5412990)). Qed.
Lemma lem5412992 : term671 = term257.
Proof. exact (TRANS (@lem5412881) (@lem5412991)). Qed.
Lemma lem5412994 (x : real) : (term272 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5412995 : term257 = term256.
Proof. exact (@lem5412994 term256). Qed.
Lemma lem5412996 : term671 = term256.
Proof. exact (TRANS (@lem5412992) (@lem5412995)). Qed.
Lemma lem5412997 (_69905 : int) : (term729 _69905) = term682.
Proof. exact (MK_COMB (@lem5412872 _69905) (@lem5412996)). Qed.
Lemma lem5412998 (_69905 : int) : (term728 _69905) = term682.
Proof. exact (TRANS (@lem5412764 _69905) (@lem5412997 _69905)). Qed.
Lemma lem5412999 : term682 = term256.
Proof. exact (@lem1982721 term256). Qed.
Lemma lem5413000 (_69905 : int) : (term728 _69905) = term256.
Proof. exact (TRANS (@lem5412998 _69905) (@lem5412999)). Qed.
Lemma lem5413001 (_69904 : int) (_69905 : int) : (term726 _69904 _69905) = term682.
Proof. exact (MK_COMB (@lem5412763 _69904) (@lem5413000 _69905)). Qed.
Lemma lem5413002 (_69904 : int) (_69905 : int) : (term725 _69904 _69905) = term682.
Proof. exact (TRANS (@lem5412655 _69904 _69905) (@lem5413001 _69904 _69905)). Qed.
Lemma lem5413003 : term682 = term256.
Proof. exact (@lem1982721 term256). Qed.
Lemma lem5413004 (_69904 : int) (_69905 : int) : (term725 _69904 _69905) = term256.
Proof. exact (TRANS (@lem5413002 _69904 _69905) (@lem5413003)). Qed.
Lemma lem5413005 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5413006 (_69904 : int) (_69905 : int) : (term730 _69904 _69905) = term684.
Proof. exact (MK_COMB (@lem5413005) (@lem5413004 _69904 _69905)). Qed.
Lemma lem5413007 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem5413008 (_69904 : int) (_69905 : int) : (term724 _69904 _69905) = term685.
Proof. exact (MK_COMB (@lem5413006 _69904 _69905) (@lem5413007)). Qed.
Lemma lem5413009 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : term685.
Proof. exact (EQ_MP (@lem5413008 _69904 _69905) (@lem5412654 _69903 _69904 _69905 h1)). Qed.
Lemma lem5413011 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5413012 : term685 = term686.
Proof. exact (@lem5413011 term182 term256). Qed.
Lemma lem5413014 (x : nat) : (term254 x) = (term255 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5413015 : term256 = term257.
Proof. exact (@lem5413014 term79). Qed.
Lemma lem5413017 (x : nat) : (real_of_num x) = (term252 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5413018 : term182 = term253.
Proof. exact (@lem5413017 (NUMERAL 0)). Qed.
Lemma lem5413019 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5413020 : term184 = term687.
Proof. exact (MK_COMB (@lem5413019) (@lem5413018)). Qed.
Lemma lem5413021 : term686 = term688.
Proof. exact (MK_COMB (@lem5413020) (@lem5413015)). Qed.
Lemma lem5413022 : term689.
Proof. exact (@lem1980026 term182 term193 term256 term193). Qed.
Lemma lem5413024 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5413025 : term314 = term315.
Proof. exact (@lem5413024 (NUMERAL 0) term79). Qed.
Lemma lem5413026 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5413027 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5413028 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5413027 h1) (fun h1 : term315 = True => @lem5413026)). Qed.
Lemma lem5413029 : term315 = True.
Proof. exact (EQ_MP (@lem5413028) (@lem5413026)). Qed.
Lemma lem5413030 : term314 = True.
Proof. exact (TRANS (@lem5413025) (@lem5413029)). Qed.
Lemma lem5413031 : True = term314.
Proof. exact (SYM (@lem5413030)). Qed.
Lemma lem5413032 : term314.
Proof. exact (EQ_MP (@lem5413031) (@lem0)). Qed.
Lemma lem5413033 : term690.
Proof. exact (@lem5413022 (@lem5413032)). Qed.
Lemma lem5413035 (m : nat) (n : nat) : (term313 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5413036 : term314 = term315.
Proof. exact (@lem5413035 (NUMERAL 0) term79). Qed.
Lemma lem5413037 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5413038 (h1 : term316 = (BIT1 0)) : term315 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5413039 : (term316 = (BIT1 0)) = (term315 = True).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5413038 h1) (fun h1 : term315 = True => @lem5413037)). Qed.
Lemma lem5413040 : term315 = True.
Proof. exact (EQ_MP (@lem5413039) (@lem5413037)). Qed.
Lemma lem5413041 : term314 = True.
Proof. exact (TRANS (@lem5413036) (@lem5413040)). Qed.
Lemma lem5413042 : True = term314.
Proof. exact (SYM (@lem5413041)). Qed.
Lemma lem5413043 : term314.
Proof. exact (EQ_MP (@lem5413042) (@lem0)). Qed.
Lemma lem5413044 : term688 = term691.
Proof. exact (@lem5413033 (@lem5413043)). Qed.
Lemma lem5413046 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5413047 : term291 = term296.
Proof. exact (@lem5413046 term79 term79). Qed.
Lemma lem5413048 : (term267 = (BIT1 0)) = (term268 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5413049 : term268 = term79.
Proof. exact (EQ_MP (@lem5413048) (@lem940073)). Qed.
Lemma lem5413050 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5413051 : term266 = term193.
Proof. exact (MK_COMB (@lem5413050) (@lem5413049)). Qed.
Lemma lem5413052 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5413053 : term296 = term256.
Proof. exact (MK_COMB (@lem5413052) (@lem5413051)). Qed.
Lemma lem5413054 : term291 = term256.
Proof. exact (TRANS (@lem5413047) (@lem5413053)). Qed.
Lemma lem5413056 (x : nat) : (term406 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5413057 : term405 = term182.
Proof. exact (@lem5413056 term79). Qed.
Lemma lem5413058 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5413059 : term692 = term184.
Proof. exact (MK_COMB (@lem5413058) (@lem5413057)). Qed.
Lemma lem5413060 : term691 = term686.
Proof. exact (MK_COMB (@lem5413059) (@lem5413054)). Qed.
Lemma lem5413062 (m : nat) (n : nat) : (term693 m n) = (term694 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5413063 : term686 = term695.
Proof. exact (@lem5413062 (NUMERAL 0) term79). Qed.
Lemma lem5413064 : term316 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5413065 (h1 : term316 = (BIT1 0)) : (term79 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5413066 : (term316 = (BIT1 0)) = ((term79 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term316 = (BIT1 0) => @lem5413065 h1) (fun h1 : (term79 = (NUMERAL 0)) = False => @lem5413064)). Qed.
Lemma lem5413067 : (term79 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5413066) (@lem5413064)). Qed.
Lemma lem5413068 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5413069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413070 : term696 = (and True).
Proof. exact (MK_COMB (@lem5413069) (@lem5413068)). Qed.
Lemma lem5413071 : term695 = (True /\ False).
Proof. exact (MK_COMB (@lem5413070) (@lem5413067)). Qed.
Lemma lem5413073 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5413074 : term695 = False.
Proof. exact (TRANS (@lem5413071) (@lem5413073)). Qed.
Lemma lem5413075 : term686 = False.
Proof. exact (TRANS (@lem5413063) (@lem5413074)). Qed.
Lemma lem5413076 : term691 = False.
Proof. exact (TRANS (@lem5413060) (@lem5413075)). Qed.
Lemma lem5413077 : term688 = False.
Proof. exact (TRANS (@lem5413044) (@lem5413076)). Qed.
Lemma lem5413078 : term686 = False.
Proof. exact (TRANS (@lem5413021) (@lem5413077)). Qed.
Lemma lem5413079 : term685 = False.
Proof. exact (TRANS (@lem5413012) (@lem5413078)). Qed.
Lemma lem5413080 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term809 _69903 _69904 _69905) : False.
Proof. exact (EQ_MP (@lem5413079) (@lem5413009 _69903 _69904 _69905 h1)). Qed.
Lemma lem5413081 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term556 _69903 _69904 _69905) : False.
Proof. exact (or_elim (@lem5412015 _69903 _69904 _69905 h1) (fun h0 : term797 _69903 _69904 _69905 => @lem5412486 _69903 _69904 _69905 h0) (fun h0 : term809 _69903 _69904 _69905 => @lem5413080 _69903 _69904 _69905 h0)). Qed.
Lemma lem5413082 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term565 _69903 _69904 _69905) : False.
Proof. exact (or_elim (@lem5410945 _69903 _69904 _69905 h1) (fun h0 : term560 _69904 _69903 _69905 => @lem5412014 _69904 _69903 _69905 h0) (fun h0 : term556 _69903 _69904 _69905 => @lem5413081 _69903 _69904 _69905 h0)). Qed.
Lemma lem5413083 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term581 _69903 _69904 _69905) : False.
Proof. exact (or_elim (@lem5408452 _69903 _69904 _69905 h1) (fun h0 : term578 _69903 _69904 _69905 => @lem5410944 _69903 _69904 _69905 h0) (fun h0 : term565 _69903 _69904 _69905 => @lem5413082 _69903 _69904 _69905 h0)). Qed.
Lemma lem5413085 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term581 _69903 _69904 _69905) : term581 _69903 _69904 _69905.
Proof. exact (h1). Qed.
Lemma lem5413086 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term581 _69903 _69904 _69905) : (term581 _69903 _69904 _69905) = False.
Proof. exact (prop_ext (fun h2 : term581 _69903 _69904 _69905 => @lem5413083 _69903 _69904 _69905 h1) (fun h2 : False => @lem5413085 _69903 _69904 _69905 h1)). Qed.
Lemma lem5413087 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term581 _69903 _69904 _69905) : False.
Proof. exact (EQ_MP (@lem5413086 _69903 _69904 _69905 h1) (@lem5413085 _69903 _69904 _69905 h1)). Qed.
Lemma lem5413088 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term248 _69903 _69904 _69905) : term248 _69903 _69904 _69905.
Proof. exact (h1). Qed.
Lemma lem5413089 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term248 _69903 _69904 _69905) : term581 _69903 _69904 _69905.
Proof. exact (EQ_MP (@lem5408406 _69903 _69904 _69905) (@lem5413088 _69903 _69904 _69905 h1)). Qed.
Lemma lem5413090 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term248 _69903 _69904 _69905) : (term581 _69903 _69904 _69905) = False.
Proof. exact (prop_ext (fun h2 : term581 _69903 _69904 _69905 => @lem5413087 _69903 _69904 _69905 h2) (fun h2 : False => @lem5413089 _69903 _69904 _69905 h1)). Qed.
Lemma lem5413091 (_69903 : int) (_69904 : int) (_69905 : int) (h1 : term248 _69903 _69904 _69905) : False.
Proof. exact (EQ_MP (@lem5413090 _69903 _69904 _69905 h1) (@lem5413089 _69903 _69904 _69905 h1)). Qed.
Lemma lem5413092 (_69903 : int) (_69904 : int) (_69905 : int) : term812 _69903 _69904 _69905.
Proof. exact (fun h0 : term248 _69903 _69904 _69905 => @lem5413091 _69903 _69904 _69905 h0). Qed.
Lemma lem5413093 (_69903 : int) (_69904 : int) (_69905 : int) : term813 _69903 _69904 _69905.
Proof. exact (@lem1386578 (term814 _69903 _69904 _69905)). Qed.
Lemma lem5413096 (_69903 : int) (_69904 : int) (_69905 : int) : term814 _69903 _69904 _69905.
Proof. exact (@lem5413093 _69903 _69904 _69905 (@lem5413092 _69903 _69904 _69905)). Qed.
Lemma lem5413097 (_69903 : int) (_69905 : int) (_69904 : int) : (term246 _69903 _69904 _69905) = (term175 _69903 _69905 _69904).
Proof. exact (SYM (@lem5406812 _69903 _69904 _69905)). Qed.
Lemma lem5413098 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5413099 (_69903 : int) (_69905 : int) (_69904 : int) : (term814 _69903 _69904 _69905) = (term109 _69903 _69905 _69904).
Proof. exact (MK_COMB (@lem5413098) (@lem5413097 _69903 _69905 _69904)). Qed.
Lemma lem5413100 (_69903 : int) (_69905 : int) (_69904 : int) : term109 _69903 _69905 _69904.
Proof. exact (EQ_MP (@lem5413099 _69903 _69905 _69904) (@lem5413096 _69903 _69904 _69905)). Qed.
Lemma lem5413101 (_69903 : int) (_69905 : int) (_69904 : int) : term110 _69903 _69905 _69904.
Proof. exact (EQ_MP (@lem5406325 _69903 _69905 _69904) (@lem5413100 _69903 _69905 _69904)). Qed.
Lemma lem5413102 (m : nat) (x : nat) (n : nat) : term815 m x n.
Proof. exact (@lem5413101 (int_of_num m) (int_of_num x) (int_of_num n)). Qed.
Lemma lem5413103 (m : nat) (x : nat) (n : nat) : term816 m x n.
Proof. exact (@lem5413102 m x n (@lem5406318 m)). Qed.
Lemma lem5413104 (m : nat) (x : nat) (n : nat) : term817 m x n.
Proof. exact (@lem5413103 m x n (@lem5406321 n)). Qed.
Lemma lem5413105 (m : nat) (x : nat) (n : nat) : term104 m x n.
Proof. exact (@lem5413104 m x n (@lem5406324 x)). Qed.
Lemma lem5413106 (m : nat) (n : nat) : term106 m n.
Proof. exact (fun x : nat => @lem5413105 m x n). Qed.
Lemma lem5413107 (m : nat) (n : nat) : (term106 m n) = (term5 m n).
Proof. exact (SYM (@lem5406315 m n)). Qed.
Lemma lem5413108 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem5413107 m n) (@lem5413106 m n)). Qed.
Lemma lem5413109 (m : nat) (n : nat) : (term5 m n) = ((term5 m n) = True).
Proof. exact (@lem7 (term5 m n)). Qed.
Lemma lem5413110 (m : nat) (n : nat) : (term5 m n) = True.
Proof. exact (EQ_MP (@lem5413109 m n) (@lem5413108 m n)). Qed.
Lemma lem5413111 (m : nat) (n : nat) : True = (term5 m n).
Proof. exact (SYM (@lem5413110 m n)). Qed.
Lemma lem5413112 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem5413111 m n) (@lem0)). Qed.
