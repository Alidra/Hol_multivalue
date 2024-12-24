Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INF_ASCLOSE_term_abbrevs.
Require Import REAL_INF_BOUNDS_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482680_spec.
Require Import thm1482981_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm19158_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
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
Require Import thm1982761_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988297_spec.
Require Import thm1988332_spec.
Require Import thm1988348_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem5243852 (s : real -> Prop) : term0 s.
Proof. exact (@lem5243750 s). Qed.
Lemma lem5243853 (s : real -> Prop) : (term0 s) = (term1 s).
Proof. exact (eq_refl (term0 s)). Qed.
Lemma lem5243854 (s : real -> Prop) : term1 s.
Proof. exact (EQ_MP (@lem5243853 s) (@lem5243852 s)). Qed.
Lemma lem5243855 (s : real -> Prop) (a : real) : term2 s a.
Proof. exact (@lem5243854 s a). Qed.
Lemma lem5243856 (a : real) (s : real -> Prop) : (term2 s a) = (term3 a s).
Proof. exact (eq_refl (term2 s a)). Qed.
Lemma lem5243857 (a : real) (s : real -> Prop) : term3 a s.
Proof. exact (EQ_MP (@lem5243856 a s) (@lem5243855 s a)). Qed.
Lemma lem5243858 (a : real) (s : real -> Prop) (b : real) : term4 a s b.
Proof. exact (@lem5243857 a s b). Qed.
Lemma lem5243859 (a : real) (s : real -> Prop) (b : real) : (term4 a s b) = (term5 a s b).
Proof. exact (eq_refl (term4 a s b)). Qed.
Lemma lem5243860 (a : real) (s : real -> Prop) (b : real) : term5 a s b.
Proof. exact (EQ_MP (@lem5243859 a s b) (@lem5243858 a s b)). Qed.
Lemma lem5243861 (a : real) (s : real -> Prop) (b : real) : (term5 a s b) = ((term5 a s b) = True).
Proof. exact (@lem7 (term5 a s b)). Qed.
Lemma lem5243879 (x : real) (l : real) (e : real) : (term6 x l e) = (term7 x l e).
Proof. exact (@lem17045 (term8 l e x) (term9 x l e)). Qed.
Lemma lem5243885 (x : real) (l : real) (e : real) : (term10 x l e) = (term10 x l e).
Proof. exact (eq_refl (term10 x l e)). Qed.
Lemma lem5243887 (x : real) (l : real) (e : real) : (term11 x l e) = (term11 x l e).
Proof. exact (eq_refl (term11 x l e)). Qed.
Lemma lem5243888 (x : real) (l : real) (e : real) : (term12 x l e) = (term13 x l e).
Proof. exact (MK_COMB (@lem5243887 x l e) (@lem5243879 x l e)). Qed.
Lemma lem5243889 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5243890 (x : real) (l : real) (e : real) : (term14 x l e) = (term15 x l e).
Proof. exact (MK_COMB (@lem5243889) (@lem5243888 x l e)). Qed.
Lemma lem5243891 (x : real) (l : real) (e : real) : (term16 x l e) = (term17 x l e).
Proof. exact (MK_COMB (@lem5243890 x l e) (@lem5243885 x l e)). Qed.
Lemma lem5243892 (x : real) (l : real) (e : real) : (term18 x l e) = (term16 x l e).
Proof. exact (@lem17646 (term19 x l e) (term20 x l e)). Qed.
Lemma lem5243922 (x : real) (l : real) (e : real) : (term18 x l e) = (term17 x l e).
Proof. exact (TRANS (@lem5243892 x l e) (@lem5243891 x l e)). Qed.
Lemma lem5243923 (e : real) (x : real) (l : real) : (term19 x l e) = (term21 e x l).
Proof. exact (@lem1988287 e (term22 x l)). Qed.
Lemma lem5243929 (x : real) (l : real) : (real_sub x l) = (term23 x l).
Proof. exact (@lem1982792 x l). Qed.
Lemma lem5243934 (l : real) (x : real) : (term23 x l) = (term24 l x).
Proof. exact (@lem1982761 (term25 l) x). Qed.
Lemma lem5243936 (l : real) (x : real) : (real_sub x l) = (term24 l x).
Proof. exact (TRANS (@lem5243929 x l) (@lem5243934 l x)). Qed.
Lemma lem5243937 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem5243938 (l : real) (x : real) : (term22 x l) = (term26 l x).
Proof. exact (MK_COMB (@lem5243937) (@lem5243936 l x)). Qed.
Lemma lem5243941 (e : real) : (real_sub e) = (real_sub e).
Proof. exact (eq_refl (real_sub e)). Qed.
Lemma lem5243942 (e : real) (l : real) (x : real) : (term27 e x l) = (term28 e l x).
Proof. exact (MK_COMB (@lem5243941 e) (@lem5243938 l x)). Qed.
Lemma lem5243949 (e : real) (l : real) (x : real) : (term28 e l x) = (term29 e l x).
Proof. exact (@lem1982792 e (term26 l x)). Qed.
Lemma lem5243950 (e : real) (l : real) (x : real) : (term27 e x l) = (term29 e l x).
Proof. exact (TRANS (@lem5243942 e l x) (@lem5243949 e l x)). Qed.
Lemma lem5243951 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5243952 (e : real) (l : real) (x : real) : (term30 e x l) = (term31 e l x).
Proof. exact (MK_COMB (@lem5243951) (@lem5243950 e l x)). Qed.
Lemma lem5243953 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5243954 (e : real) (l : real) (x : real) : (term21 e x l) = (term33 e l x).
Proof. exact (MK_COMB (@lem5243952 e l x) (@lem5243953)). Qed.
Lemma lem5243955 (e : real) (l : real) (x : real) : (term19 x l e) = (term33 e l x).
Proof. exact (TRANS (@lem5243923 e x l) (@lem5243954 e l x)). Qed.
Lemma lem5243956 (l : real) (e : real) (x : real) : (term34 l e x) = (term35 l e x).
Proof. exact (@lem1988297 (real_sub l e) x). Qed.
Lemma lem5243957 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5243963 (l : real) (e : real) : (real_sub l e) = (term23 l e).
Proof. exact (@lem1982792 l e). Qed.
Lemma lem5243968 (e : real) (l : real) : (term23 l e) = (term24 e l).
Proof. exact (@lem1982761 (term25 e) l). Qed.
Lemma lem5243970 (e : real) (l : real) : (real_sub l e) = (term24 e l).
Proof. exact (TRANS (@lem5243963 l e) (@lem5243968 e l)). Qed.
Lemma lem5243971 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5243972 (e : real) (l : real) : (term36 l e) = (term37 e l).
Proof. exact (MK_COMB (@lem5243971) (@lem5243970 e l)). Qed.
Lemma lem5243973 (e : real) (l : real) (x : real) : (term38 l e x) = (term39 e l x).
Proof. exact (MK_COMB (@lem5243972 e l) (@lem5243957 x)). Qed.
Lemma lem5243974 (e : real) (l : real) (x : real) : (term39 e l x) = (term40 e l x).
Proof. exact (@lem1982792 (term24 e l) x). Qed.
Lemma lem5243983 (e : real) (l : real) (x : real) : (term40 e l x) = (term41 e l x).
Proof. exact (@lem1982755 (term25 e) l (term25 x)). Qed.
Lemma lem5243984 (e : real) (l : real) (x : real) : (term39 e l x) = (term41 e l x).
Proof. exact (TRANS (@lem5243974 e l x) (@lem5243983 e l x)). Qed.
Lemma lem5243985 (e : real) (l : real) (x : real) : (term38 l e x) = (term41 e l x).
Proof. exact (TRANS (@lem5243973 e l x) (@lem5243984 e l x)). Qed.
Lemma lem5243986 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5243987 (e : real) (l : real) (x : real) : (term42 l e x) = (term43 e l x).
Proof. exact (MK_COMB (@lem5243986) (@lem5243985 e l x)). Qed.
Lemma lem5243988 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5243989 (e : real) (l : real) (x : real) : (term35 l e x) = (term44 e l x).
Proof. exact (MK_COMB (@lem5243987 e l x) (@lem5243988)). Qed.
Lemma lem5243990 (e : real) (l : real) (x : real) : (term34 l e x) = (term44 e l x).
Proof. exact (TRANS (@lem5243956 l e x) (@lem5243989 e l x)). Qed.
Lemma lem5243991 (x : real) (l : real) (e : real) : (term45 x l e) = (term46 x l e).
Proof. exact (@lem1988297 x (real_add l e)). Qed.
Lemma lem5243998 (e : real) (l : real) : (real_add l e) = (real_add e l).
Proof. exact (@lem1982761 e l). Qed.
Lemma lem5244001 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem5244002 (x : real) (e : real) (l : real) : (term47 x l e) = (term47 x e l).
Proof. exact (MK_COMB (@lem5244001 x) (@lem5243998 e l)). Qed.
Lemma lem5244003 (x : real) (e : real) (l : real) : (term47 x e l) = (term48 x e l).
Proof. exact (@lem1982792 x (real_add e l)). Qed.
Lemma lem5244010 (e : real) (l : real) : (term49 e l) = (term50 e l).
Proof. exact (@lem1982781 e term51 l). Qed.
Lemma lem5244011 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem5244012 (x : real) (e : real) (l : real) : (term48 x e l) = (term52 x e l).
Proof. exact (MK_COMB (@lem5244011 x) (@lem5244010 e l)). Qed.
Lemma lem5244013 (e : real) (x : real) (l : real) : (term52 x e l) = (term41 e x l).
Proof. exact (@lem1982757 (term25 e) x (term25 l)). Qed.
Lemma lem5244014 (l : real) (x : real) : (term23 x l) = (term24 l x).
Proof. exact (@lem1982761 (term25 l) x). Qed.
Lemma lem5244015 (e : real) : (term53 e) = (term53 e).
Proof. exact (eq_refl (term53 e)). Qed.
Lemma lem5244016 (e : real) (l : real) (x : real) : (term41 e x l) = (term54 e l x).
Proof. exact (MK_COMB (@lem5244015 e) (@lem5244014 l x)). Qed.
Lemma lem5244017 (e : real) (l : real) (x : real) : (term52 x e l) = (term54 e l x).
Proof. exact (TRANS (@lem5244013 e x l) (@lem5244016 e l x)). Qed.
Lemma lem5244018 (e : real) (l : real) (x : real) : (term48 x e l) = (term54 e l x).
Proof. exact (TRANS (@lem5244012 x e l) (@lem5244017 e l x)). Qed.
Lemma lem5244019 (e : real) (l : real) (x : real) : (term47 x e l) = (term54 e l x).
Proof. exact (TRANS (@lem5244003 x e l) (@lem5244018 e l x)). Qed.
Lemma lem5244020 (e : real) (l : real) (x : real) : (term47 x l e) = (term54 e l x).
Proof. exact (TRANS (@lem5244002 x e l) (@lem5244019 e l x)). Qed.
Lemma lem5244021 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5244022 (e : real) (l : real) (x : real) : (term55 x l e) = (term56 e l x).
Proof. exact (MK_COMB (@lem5244021) (@lem5244020 e l x)). Qed.
Lemma lem5244023 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5244024 (e : real) (l : real) (x : real) : (term46 x l e) = (term57 e l x).
Proof. exact (MK_COMB (@lem5244022 e l x) (@lem5244023)). Qed.
Lemma lem5244025 (e : real) (l : real) (x : real) : (term45 x l e) = (term57 e l x).
Proof. exact (TRANS (@lem5243991 x l e) (@lem5244024 e l x)). Qed.
Lemma lem5244026 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5244027 (e : real) (l : real) (x : real) : (term58 l e x) = (term59 e l x).
Proof. exact (MK_COMB (@lem5244026) (@lem5243990 e l x)). Qed.
Lemma lem5244028 (e : real) (l : real) (x : real) : (term7 x l e) = (term60 e l x).
Proof. exact (MK_COMB (@lem5244027 e l x) (@lem5244025 e l x)). Qed.
Lemma lem5244029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5244030 (e : real) (l : real) (x : real) : (term11 x l e) = (term61 e l x).
Proof. exact (MK_COMB (@lem5244029) (@lem5243955 e l x)). Qed.
Lemma lem5244031 (e : real) (l : real) (x : real) : (term13 x l e) = (term62 e l x).
Proof. exact (MK_COMB (@lem5244030 e l x) (@lem5244028 e l x)). Qed.
Lemma lem5244032 (x : real) (l : real) (e : real) : (term63 x l e) = (term64 x l e).
Proof. exact (@lem1988297 (term22 x l) e). Qed.
Lemma lem5244033 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem5244039 (x : real) (l : real) : (real_sub x l) = (term23 x l).
Proof. exact (@lem1982792 x l). Qed.
Lemma lem5244044 (l : real) (x : real) : (term23 x l) = (term24 l x).
Proof. exact (@lem1982761 (term25 l) x). Qed.
Lemma lem5244046 (l : real) (x : real) : (real_sub x l) = (term24 l x).
Proof. exact (TRANS (@lem5244039 x l) (@lem5244044 l x)). Qed.
Lemma lem5244047 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem5244048 (l : real) (x : real) : (term22 x l) = (term26 l x).
Proof. exact (MK_COMB (@lem5244047) (@lem5244046 l x)). Qed.
Lemma lem5244049 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5244050 (l : real) (x : real) : (term65 x l) = (term66 l x).
Proof. exact (MK_COMB (@lem5244049) (@lem5244048 l x)). Qed.
Lemma lem5244051 (l : real) (x : real) (e : real) : (term67 x l e) = (term68 l x e).
Proof. exact (MK_COMB (@lem5244050 l x) (@lem5244033 e)). Qed.
Lemma lem5244052 (l : real) (x : real) (e : real) : (term68 l x e) = (term69 l x e).
Proof. exact (@lem1982792 (term26 l x) e). Qed.
Lemma lem5244057 (e : real) (l : real) (x : real) : (term69 l x e) = (term70 e l x).
Proof. exact (@lem1982761 (term25 e) (term26 l x)). Qed.
Lemma lem5244058 (e : real) (l : real) (x : real) : (term68 l x e) = (term70 e l x).
Proof. exact (TRANS (@lem5244052 l x e) (@lem5244057 e l x)). Qed.
Lemma lem5244059 (e : real) (l : real) (x : real) : (term67 x l e) = (term70 e l x).
Proof. exact (TRANS (@lem5244051 l x e) (@lem5244058 e l x)). Qed.
Lemma lem5244060 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5244061 (e : real) (l : real) (x : real) : (term71 x l e) = (term72 e l x).
Proof. exact (MK_COMB (@lem5244060) (@lem5244059 e l x)). Qed.
Lemma lem5244062 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5244063 (e : real) (l : real) (x : real) : (term64 x l e) = (term73 e l x).
Proof. exact (MK_COMB (@lem5244061 e l x) (@lem5244062)). Qed.
Lemma lem5244064 (e : real) (l : real) (x : real) : (term63 x l e) = (term73 e l x).
Proof. exact (TRANS (@lem5244032 x l e) (@lem5244063 e l x)). Qed.
Lemma lem5244065 (x : real) (l : real) (e : real) : (term8 l e x) = (term74 x l e).
Proof. exact (@lem1988287 x (real_sub l e)). Qed.
Lemma lem5244071 (l : real) (e : real) : (real_sub l e) = (term23 l e).
Proof. exact (@lem1982792 l e). Qed.
Lemma lem5244076 (e : real) (l : real) : (term23 l e) = (term24 e l).
Proof. exact (@lem1982761 (term25 e) l). Qed.
Lemma lem5244078 (e : real) (l : real) : (real_sub l e) = (term24 e l).
Proof. exact (TRANS (@lem5244071 l e) (@lem5244076 e l)). Qed.
Lemma lem5244081 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem5244082 (x : real) (e : real) (l : real) : (term75 x l e) = (term76 x e l).
Proof. exact (MK_COMB (@lem5244081 x) (@lem5244078 e l)). Qed.
Lemma lem5244083 (x : real) (e : real) (l : real) : (term76 x e l) = (term77 x e l).
Proof. exact (@lem1982792 x (term24 e l)). Qed.
Lemma lem5244084 (e : real) (l : real) : (term78 e l) = (term79 e l).
Proof. exact (@lem1982781 (term25 e) term51 l). Qed.
Lemma lem5244085 (l : real) : (term25 l) = (term25 l).
Proof. exact (eq_refl (term25 l)). Qed.
Lemma lem5244086 (e : real) : (term80 e) = (term81 e).
Proof. exact (@lem1982749 term51 term51 e). Qed.
Lemma lem5244088 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5244089 : term51 = term84.
Proof. exact (@lem5244088 term85). Qed.
Lemma lem5244091 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5244092 : term51 = term84.
Proof. exact (@lem5244091 term85). Qed.
Lemma lem5244093 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5244094 : term86 = term87.
Proof. exact (MK_COMB (@lem5244093) (@lem5244092)). Qed.
Lemma lem5244095 : term88 = term89.
Proof. exact (MK_COMB (@lem5244094) (@lem5244089)). Qed.
Lemma lem5244096 : term89 = term90.
Proof. exact (@lem1981613 term51 term51 term91 term91). Qed.
Lemma lem5244098 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5244099 : term94 = term95.
Proof. exact (@lem5244098 term85 term85). Qed.
Lemma lem5244100 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5244101 : term97 = term85.
Proof. exact (EQ_MP (@lem5244100) (@lem940073)). Qed.
Lemma lem5244102 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5244103 : term95 = term91.
Proof. exact (MK_COMB (@lem5244102) (@lem5244101)). Qed.
Lemma lem5244104 : term94 = term91.
Proof. exact (TRANS (@lem5244099) (@lem5244103)). Qed.
Lemma lem5244106 (m : nat) (n : nat) : (term98 m n) = (term93 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5244107 : term88 = term95.
Proof. exact (@lem5244106 term85 term85). Qed.
Lemma lem5244108 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5244109 : term97 = term85.
Proof. exact (EQ_MP (@lem5244108) (@lem940073)). Qed.
Lemma lem5244110 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5244111 : term95 = term91.
Proof. exact (MK_COMB (@lem5244110) (@lem5244109)). Qed.
Lemma lem5244112 : term88 = term91.
Proof. exact (TRANS (@lem5244107) (@lem5244111)). Qed.
Lemma lem5244113 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5244114 : term99 = term100.
Proof. exact (MK_COMB (@lem5244113) (@lem5244112)). Qed.
Lemma lem5244115 : term90 = term101.
Proof. exact (MK_COMB (@lem5244114) (@lem5244104)). Qed.
Lemma lem5244116 : term89 = term101.
Proof. exact (TRANS (@lem5244096) (@lem5244115)). Qed.
Lemma lem5244117 : term88 = term101.
Proof. exact (TRANS (@lem5244095) (@lem5244116)). Qed.
Lemma lem5244119 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5244120 : term101 = term91.
Proof. exact (@lem5244119 term91). Qed.
Lemma lem5244121 : term88 = term91.
Proof. exact (TRANS (@lem5244117) (@lem5244120)). Qed.
Lemma lem5244122 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5244123 : term103 = term104.
Proof. exact (MK_COMB (@lem5244122) (@lem5244121)). Qed.
Lemma lem5244124 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem5244125 (e : real) : (term81 e) = (term105 e).
Proof. exact (MK_COMB (@lem5244123) (@lem5244124 e)). Qed.
Lemma lem5244126 (e : real) : (term80 e) = (term105 e).
Proof. exact (TRANS (@lem5244086 e) (@lem5244125 e)). Qed.
Lemma lem5244127 (e : real) : (term105 e) = e.
Proof. exact (@lem1982709 e). Qed.
Lemma lem5244128 (e : real) : (term80 e) = e.
Proof. exact (TRANS (@lem5244126 e) (@lem5244127 e)). Qed.
Lemma lem5244129 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5244130 (e : real) : (term106 e) = (real_add e).
Proof. exact (MK_COMB (@lem5244129) (@lem5244128 e)). Qed.
Lemma lem5244131 (e : real) (l : real) : (term79 e l) = (term23 e l).
Proof. exact (MK_COMB (@lem5244130 e) (@lem5244085 l)). Qed.
Lemma lem5244132 (e : real) (l : real) : (term78 e l) = (term23 e l).
Proof. exact (TRANS (@lem5244084 e l) (@lem5244131 e l)). Qed.
Lemma lem5244133 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem5244134 (x : real) (e : real) (l : real) : (term77 x e l) = (term107 x e l).
Proof. exact (MK_COMB (@lem5244133 x) (@lem5244132 e l)). Qed.
Lemma lem5244135 (e : real) (x : real) (l : real) : (term107 x e l) = (term107 e x l).
Proof. exact (@lem1982757 e x (term25 l)). Qed.
Lemma lem5244136 (l : real) (x : real) : (term23 x l) = (term24 l x).
Proof. exact (@lem1982761 (term25 l) x). Qed.
Lemma lem5244137 (e : real) : (real_add e) = (real_add e).
Proof. exact (eq_refl (real_add e)). Qed.
Lemma lem5244138 (e : real) (l : real) (x : real) : (term107 e x l) = (term108 e l x).
Proof. exact (MK_COMB (@lem5244137 e) (@lem5244136 l x)). Qed.
Lemma lem5244139 (e : real) (l : real) (x : real) : (term107 x e l) = (term108 e l x).
Proof. exact (TRANS (@lem5244135 e x l) (@lem5244138 e l x)). Qed.
Lemma lem5244140 (e : real) (l : real) (x : real) : (term77 x e l) = (term108 e l x).
Proof. exact (TRANS (@lem5244134 x e l) (@lem5244139 e l x)). Qed.
Lemma lem5244141 (e : real) (l : real) (x : real) : (term76 x e l) = (term108 e l x).
Proof. exact (TRANS (@lem5244083 x e l) (@lem5244140 e l x)). Qed.
Lemma lem5244142 (e : real) (l : real) (x : real) : (term75 x l e) = (term108 e l x).
Proof. exact (TRANS (@lem5244082 x e l) (@lem5244141 e l x)). Qed.
Lemma lem5244143 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5244144 (e : real) (l : real) (x : real) : (term109 x l e) = (term110 e l x).
Proof. exact (MK_COMB (@lem5244143) (@lem5244142 e l x)). Qed.
Lemma lem5244145 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5244146 (e : real) (l : real) (x : real) : (term74 x l e) = (term111 e l x).
Proof. exact (MK_COMB (@lem5244144 e l x) (@lem5244145)). Qed.
Lemma lem5244147 (e : real) (l : real) (x : real) : (term8 l e x) = (term111 e l x).
Proof. exact (TRANS (@lem5244065 x l e) (@lem5244146 e l x)). Qed.
Lemma lem5244148 (l : real) (e : real) (x : real) : (term9 x l e) = (term112 l e x).
Proof. exact (@lem1988287 (real_add l e) x). Qed.
Lemma lem5244149 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5244156 (e : real) (l : real) : (real_add l e) = (real_add e l).
Proof. exact (@lem1982761 e l). Qed.
Lemma lem5244157 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5244158 (e : real) (l : real) : (term113 l e) = (term113 e l).
Proof. exact (MK_COMB (@lem5244157) (@lem5244156 e l)). Qed.
Lemma lem5244159 (e : real) (l : real) (x : real) : (term114 l e x) = (term114 e l x).
Proof. exact (MK_COMB (@lem5244158 e l) (@lem5244149 x)). Qed.
Lemma lem5244160 (e : real) (l : real) (x : real) : (term114 e l x) = (term115 e l x).
Proof. exact (@lem1982792 (real_add e l) x). Qed.
Lemma lem5244169 (e : real) (l : real) (x : real) : (term115 e l x) = (term107 e l x).
Proof. exact (@lem1982755 e l (term25 x)). Qed.
Lemma lem5244170 (e : real) (l : real) (x : real) : (term114 e l x) = (term107 e l x).
Proof. exact (TRANS (@lem5244160 e l x) (@lem5244169 e l x)). Qed.
Lemma lem5244171 (e : real) (l : real) (x : real) : (term114 l e x) = (term107 e l x).
Proof. exact (TRANS (@lem5244159 e l x) (@lem5244170 e l x)). Qed.
Lemma lem5244172 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5244173 (e : real) (l : real) (x : real) : (term116 l e x) = (term117 e l x).
Proof. exact (MK_COMB (@lem5244172) (@lem5244171 e l x)). Qed.
Lemma lem5244174 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5244175 (e : real) (l : real) (x : real) : (term112 l e x) = (term118 e l x).
Proof. exact (MK_COMB (@lem5244173 e l x) (@lem5244174)). Qed.
Lemma lem5244176 (e : real) (l : real) (x : real) : (term9 x l e) = (term118 e l x).
Proof. exact (TRANS (@lem5244148 l e x) (@lem5244175 e l x)). Qed.
Lemma lem5244177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5244178 (e : real) (l : real) (x : real) : (term119 l e x) = (term120 e l x).
Proof. exact (MK_COMB (@lem5244177) (@lem5244147 e l x)). Qed.
Lemma lem5244179 (e : real) (l : real) (x : real) : (term20 x l e) = (term121 e l x).
Proof. exact (MK_COMB (@lem5244178 e l x) (@lem5244176 e l x)). Qed.
Lemma lem5244180 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5244181 (e : real) (l : real) (x : real) : (term122 x l e) = (term123 e l x).
Proof. exact (MK_COMB (@lem5244180) (@lem5244064 e l x)). Qed.
Lemma lem5244182 (e : real) (l : real) (x : real) : (term10 x l e) = (term124 e l x).
Proof. exact (MK_COMB (@lem5244181 e l x) (@lem5244179 e l x)). Qed.
Lemma lem5244183 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5244184 (e : real) (l : real) (x : real) : (term15 x l e) = (term125 e l x).
Proof. exact (MK_COMB (@lem5244183) (@lem5244031 e l x)). Qed.
Lemma lem5244185 (e : real) (l : real) (x : real) : (term17 x l e) = (term126 e l x).
Proof. exact (MK_COMB (@lem5244184 e l x) (@lem5244182 e l x)). Qed.
Lemma lem5244192 (e : real) (l : real) (x : real) : (term18 x l e) = (term126 e l x).
Proof. exact (TRANS (@lem5243922 x l e) (@lem5244185 e l x)). Qed.
Lemma lem5244205 (e : real) (l : real) (x : real) : (term124 e l x) = (term124 e l x).
Proof. exact (eq_refl (term124 e l x)). Qed.
Lemma lem5244222 (e : real) (l : real) (x : real) : (term62 e l x) = (term127 e l x).
Proof. exact (@lem19158 (term44 e l x) (term33 e l x) (term57 e l x)). Qed.
Lemma lem5244223 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5244224 (e : real) (l : real) (x : real) : (term125 e l x) = (term128 e l x).
Proof. exact (MK_COMB (@lem5244223) (@lem5244222 e l x)). Qed.
Lemma lem5244225 (e : real) (l : real) (x : real) : (term126 e l x) = (term129 e l x).
Proof. exact (MK_COMB (@lem5244224 e l x) (@lem5244205 e l x)). Qed.
Lemma lem5244226 (e : real) (l : real) (x : real) : (term18 x l e) = (term129 e l x).
Proof. exact (TRANS (@lem5244192 e l x) (@lem5244225 e l x)). Qed.
Lemma lem5244228 (a : real) (x : real) (r : real) : (term130 a x r) = (term131 a x r).
Proof. exact (proj1 (@lem1482680 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem5244229 (e : real) (l : real) (x : real) : (term33 e l x) = (term132 e l x).
Proof. exact (@lem5244228 e (term24 l x) term32). Qed.
Lemma lem5244248 (l : real) (x : real) : (term133 l x) = (term24 l x).
Proof. exact (@lem1982733 (term24 l x)). Qed.
Lemma lem5244251 (e : real) : (real_add e) = (real_add e).
Proof. exact (eq_refl (real_add e)). Qed.
Lemma lem5244254 (e : real) (l : real) (x : real) : (term134 e l x) = (term108 e l x).
Proof. exact (MK_COMB (@lem5244251 e) (@lem5244248 l x)). Qed.
Lemma lem5244255 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5244256 (e : real) (l : real) (x : real) : (term135 e l x) = (term110 e l x).
Proof. exact (MK_COMB (@lem5244255) (@lem5244254 e l x)). Qed.
Lemma lem5244257 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5244258 (e : real) (l : real) (x : real) : (term136 e l x) = (term111 e l x).
Proof. exact (MK_COMB (@lem5244256 e l x) (@lem5244257)). Qed.
Lemma lem5244276 (l : real) (x : real) : (term78 l x) = (term79 l x).
Proof. exact (@lem1982781 (term25 l) term51 x). Qed.
Lemma lem5244277 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem5244278 (l : real) : (term80 l) = (term81 l).
Proof. exact (@lem1982749 term51 term51 l). Qed.
Lemma lem5244280 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5244281 : term51 = term84.
Proof. exact (@lem5244280 term85). Qed.
Lemma lem5244283 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5244284 : term51 = term84.
Proof. exact (@lem5244283 term85). Qed.
Lemma lem5244285 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5244286 : term86 = term87.
Proof. exact (MK_COMB (@lem5244285) (@lem5244284)). Qed.
Lemma lem5244287 : term88 = term89.
Proof. exact (MK_COMB (@lem5244286) (@lem5244281)). Qed.
Lemma lem5244288 : term89 = term90.
Proof. exact (@lem1981613 term51 term51 term91 term91). Qed.
Lemma lem5244290 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5244291 : term94 = term95.
Proof. exact (@lem5244290 term85 term85). Qed.
Lemma lem5244292 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5244293 : term97 = term85.
Proof. exact (EQ_MP (@lem5244292) (@lem940073)). Qed.
Lemma lem5244294 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5244295 : term95 = term91.
Proof. exact (MK_COMB (@lem5244294) (@lem5244293)). Qed.
Lemma lem5244296 : term94 = term91.
Proof. exact (TRANS (@lem5244291) (@lem5244295)). Qed.
Lemma lem5244298 (m : nat) (n : nat) : (term98 m n) = (term93 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5244299 : term88 = term95.
Proof. exact (@lem5244298 term85 term85). Qed.
Lemma lem5244300 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5244301 : term97 = term85.
Proof. exact (EQ_MP (@lem5244300) (@lem940073)). Qed.
Lemma lem5244302 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5244303 : term95 = term91.
Proof. exact (MK_COMB (@lem5244302) (@lem5244301)). Qed.
Lemma lem5244304 : term88 = term91.
Proof. exact (TRANS (@lem5244299) (@lem5244303)). Qed.
Lemma lem5244305 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5244306 : term99 = term100.
Proof. exact (MK_COMB (@lem5244305) (@lem5244304)). Qed.
Lemma lem5244307 : term90 = term101.
Proof. exact (MK_COMB (@lem5244306) (@lem5244296)). Qed.
Lemma lem5244308 : term89 = term101.
Proof. exact (TRANS (@lem5244288) (@lem5244307)). Qed.
Lemma lem5244309 : term88 = term101.
Proof. exact (TRANS (@lem5244287) (@lem5244308)). Qed.
Lemma lem5244311 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5244312 : term101 = term91.
Proof. exact (@lem5244311 term91). Qed.
Lemma lem5244313 : term88 = term91.
Proof. exact (TRANS (@lem5244309) (@lem5244312)). Qed.
Lemma lem5244314 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5244315 : term103 = term104.
Proof. exact (MK_COMB (@lem5244314) (@lem5244313)). Qed.
Lemma lem5244316 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5244317 (l : real) : (term81 l) = (term105 l).
Proof. exact (MK_COMB (@lem5244315) (@lem5244316 l)). Qed.
Lemma lem5244318 (l : real) : (term80 l) = (term105 l).
Proof. exact (TRANS (@lem5244278 l) (@lem5244317 l)). Qed.
Lemma lem5244319 (l : real) : (term105 l) = l.
Proof. exact (@lem1982709 l). Qed.
Lemma lem5244320 (l : real) : (term80 l) = l.
Proof. exact (TRANS (@lem5244318 l) (@lem5244319 l)). Qed.
Lemma lem5244321 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5244322 (l : real) : (term106 l) = (real_add l).
Proof. exact (MK_COMB (@lem5244321) (@lem5244320 l)). Qed.
Lemma lem5244323 (l : real) (x : real) : (term79 l x) = (term23 l x).
Proof. exact (MK_COMB (@lem5244322 l) (@lem5244277 x)). Qed.
Lemma lem5244325 (l : real) (x : real) : (term78 l x) = (term23 l x).
Proof. exact (TRANS (@lem5244276 l x) (@lem5244323 l x)). Qed.
Lemma lem5244328 (e : real) : (real_add e) = (real_add e).
Proof. exact (eq_refl (real_add e)). Qed.
Lemma lem5244331 (e : real) (l : real) (x : real) : (term77 e l x) = (term107 e l x).
Proof. exact (MK_COMB (@lem5244328 e) (@lem5244325 l x)). Qed.
Lemma lem5244332 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5244333 (e : real) (l : real) (x : real) : (term137 e l x) = (term117 e l x).
Proof. exact (MK_COMB (@lem5244332) (@lem5244331 e l x)). Qed.
Lemma lem5244334 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5244335 (e : real) (l : real) (x : real) : (term138 e l x) = (term118 e l x).
Proof. exact (MK_COMB (@lem5244333 e l x) (@lem5244334)). Qed.
Lemma lem5244336 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5244337 (e : real) (l : real) (x : real) : (term139 e l x) = (term140 e l x).
Proof. exact (MK_COMB (@lem5244336) (@lem5244335 e l x)). Qed.
Lemma lem5244338 (e : real) (l : real) (x : real) : (term132 e l x) = (term141 e l x).
Proof. exact (MK_COMB (@lem5244337 e l x) (@lem5244258 e l x)). Qed.
Lemma lem5244339 (e : real) (l : real) (x : real) : (term33 e l x) = (term141 e l x).
Proof. exact (TRANS (@lem5244229 e l x) (@lem5244338 e l x)). Qed.
Lemma lem5244340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5244341 (e : real) (l : real) (x : real) : (term61 e l x) = (term142 e l x).
Proof. exact (MK_COMB (@lem5244340) (@lem5244339 e l x)). Qed.
Lemma lem5244342 (e : real) (l : real) (x : real) : (term44 e l x) = (term44 e l x).
Proof. exact (eq_refl (term44 e l x)). Qed.
Lemma lem5244345 (e : real) (l : real) (x : real) : (term143 e l x) = (term144 e l x).
Proof. exact (MK_COMB (@lem5244341 e l x) (@lem5244342 e l x)). Qed.
Lemma lem5244347 (a : real) (x : real) (r : real) : (term130 a x r) = (term131 a x r).
Proof. exact (proj1 (@lem1482680 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem5244348 (e : real) (l : real) (x : real) : (term33 e l x) = (term132 e l x).
Proof. exact (@lem5244347 e (term24 l x) term32). Qed.
Lemma lem5244367 (l : real) (x : real) : (term133 l x) = (term24 l x).
Proof. exact (@lem1982733 (term24 l x)). Qed.
Lemma lem5244370 (e : real) : (real_add e) = (real_add e).
Proof. exact (eq_refl (real_add e)). Qed.
Lemma lem5244373 (e : real) (l : real) (x : real) : (term134 e l x) = (term108 e l x).
Proof. exact (MK_COMB (@lem5244370 e) (@lem5244367 l x)). Qed.
Lemma lem5244374 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5244375 (e : real) (l : real) (x : real) : (term135 e l x) = (term110 e l x).
Proof. exact (MK_COMB (@lem5244374) (@lem5244373 e l x)). Qed.
Lemma lem5244376 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5244377 (e : real) (l : real) (x : real) : (term136 e l x) = (term111 e l x).
Proof. exact (MK_COMB (@lem5244375 e l x) (@lem5244376)). Qed.
Lemma lem5244395 (l : real) (x : real) : (term78 l x) = (term79 l x).
Proof. exact (@lem1982781 (term25 l) term51 x). Qed.
Lemma lem5244396 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem5244397 (l : real) : (term80 l) = (term81 l).
Proof. exact (@lem1982749 term51 term51 l). Qed.
Lemma lem5244399 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5244400 : term51 = term84.
Proof. exact (@lem5244399 term85). Qed.
Lemma lem5244402 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5244403 : term51 = term84.
Proof. exact (@lem5244402 term85). Qed.
Lemma lem5244404 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5244405 : term86 = term87.
Proof. exact (MK_COMB (@lem5244404) (@lem5244403)). Qed.
Lemma lem5244406 : term88 = term89.
Proof. exact (MK_COMB (@lem5244405) (@lem5244400)). Qed.
Lemma lem5244407 : term89 = term90.
Proof. exact (@lem1981613 term51 term51 term91 term91). Qed.
Lemma lem5244409 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5244410 : term94 = term95.
Proof. exact (@lem5244409 term85 term85). Qed.
Lemma lem5244411 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5244412 : term97 = term85.
Proof. exact (EQ_MP (@lem5244411) (@lem940073)). Qed.
Lemma lem5244413 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5244414 : term95 = term91.
Proof. exact (MK_COMB (@lem5244413) (@lem5244412)). Qed.
Lemma lem5244415 : term94 = term91.
Proof. exact (TRANS (@lem5244410) (@lem5244414)). Qed.
Lemma lem5244417 (m : nat) (n : nat) : (term98 m n) = (term93 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5244418 : term88 = term95.
Proof. exact (@lem5244417 term85 term85). Qed.
Lemma lem5244419 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5244420 : term97 = term85.
Proof. exact (EQ_MP (@lem5244419) (@lem940073)). Qed.
Lemma lem5244421 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5244422 : term95 = term91.
Proof. exact (MK_COMB (@lem5244421) (@lem5244420)). Qed.
Lemma lem5244423 : term88 = term91.
Proof. exact (TRANS (@lem5244418) (@lem5244422)). Qed.
Lemma lem5244424 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5244425 : term99 = term100.
Proof. exact (MK_COMB (@lem5244424) (@lem5244423)). Qed.
Lemma lem5244426 : term90 = term101.
Proof. exact (MK_COMB (@lem5244425) (@lem5244415)). Qed.
Lemma lem5244427 : term89 = term101.
Proof. exact (TRANS (@lem5244407) (@lem5244426)). Qed.
Lemma lem5244428 : term88 = term101.
Proof. exact (TRANS (@lem5244406) (@lem5244427)). Qed.
Lemma lem5244430 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5244431 : term101 = term91.
Proof. exact (@lem5244430 term91). Qed.
Lemma lem5244432 : term88 = term91.
Proof. exact (TRANS (@lem5244428) (@lem5244431)). Qed.
Lemma lem5244433 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5244434 : term103 = term104.
Proof. exact (MK_COMB (@lem5244433) (@lem5244432)). Qed.
Lemma lem5244435 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5244436 (l : real) : (term81 l) = (term105 l).
Proof. exact (MK_COMB (@lem5244434) (@lem5244435 l)). Qed.
Lemma lem5244437 (l : real) : (term80 l) = (term105 l).
Proof. exact (TRANS (@lem5244397 l) (@lem5244436 l)). Qed.
Lemma lem5244438 (l : real) : (term105 l) = l.
Proof. exact (@lem1982709 l). Qed.
Lemma lem5244439 (l : real) : (term80 l) = l.
Proof. exact (TRANS (@lem5244437 l) (@lem5244438 l)). Qed.
Lemma lem5244440 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5244441 (l : real) : (term106 l) = (real_add l).
Proof. exact (MK_COMB (@lem5244440) (@lem5244439 l)). Qed.
Lemma lem5244442 (l : real) (x : real) : (term79 l x) = (term23 l x).
Proof. exact (MK_COMB (@lem5244441 l) (@lem5244396 x)). Qed.
Lemma lem5244444 (l : real) (x : real) : (term78 l x) = (term23 l x).
Proof. exact (TRANS (@lem5244395 l x) (@lem5244442 l x)). Qed.
Lemma lem5244447 (e : real) : (real_add e) = (real_add e).
Proof. exact (eq_refl (real_add e)). Qed.
Lemma lem5244450 (e : real) (l : real) (x : real) : (term77 e l x) = (term107 e l x).
Proof. exact (MK_COMB (@lem5244447 e) (@lem5244444 l x)). Qed.
Lemma lem5244451 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5244452 (e : real) (l : real) (x : real) : (term137 e l x) = (term117 e l x).
Proof. exact (MK_COMB (@lem5244451) (@lem5244450 e l x)). Qed.
Lemma lem5244453 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5244454 (e : real) (l : real) (x : real) : (term138 e l x) = (term118 e l x).
Proof. exact (MK_COMB (@lem5244452 e l x) (@lem5244453)). Qed.
Lemma lem5244455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5244456 (e : real) (l : real) (x : real) : (term139 e l x) = (term140 e l x).
Proof. exact (MK_COMB (@lem5244455) (@lem5244454 e l x)). Qed.
Lemma lem5244457 (e : real) (l : real) (x : real) : (term132 e l x) = (term141 e l x).
Proof. exact (MK_COMB (@lem5244456 e l x) (@lem5244377 e l x)). Qed.
Lemma lem5244458 (e : real) (l : real) (x : real) : (term33 e l x) = (term141 e l x).
Proof. exact (TRANS (@lem5244348 e l x) (@lem5244457 e l x)). Qed.
Lemma lem5244459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5244460 (e : real) (l : real) (x : real) : (term61 e l x) = (term142 e l x).
Proof. exact (MK_COMB (@lem5244459) (@lem5244458 e l x)). Qed.
Lemma lem5244461 (e : real) (l : real) (x : real) : (term57 e l x) = (term57 e l x).
Proof. exact (eq_refl (term57 e l x)). Qed.
Lemma lem5244464 (e : real) (l : real) (x : real) : (term145 e l x) = (term146 e l x).
Proof. exact (MK_COMB (@lem5244460 e l x) (@lem5244461 e l x)). Qed.
Lemma lem5244465 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5244466 (e : real) (l : real) (x : real) : (term147 e l x) = (term148 e l x).
Proof. exact (MK_COMB (@lem5244465) (@lem5244345 e l x)). Qed.
Lemma lem5244467 (e : real) (l : real) (x : real) : (term127 e l x) = (term149 e l x).
Proof. exact (MK_COMB (@lem5244466 e l x) (@lem5244464 e l x)). Qed.
Lemma lem5244469 (e : real) (l : real) (x : real) : (term150 e l x) = (term124 e l x).
Proof. exact (eq_refl (term150 e l x)). Qed.
Lemma lem5244470 (e : real) (l : real) (x : real) : (term124 e l x) = (term150 e l x).
Proof. exact (SYM (@lem5244469 e l x)). Qed.
Lemma lem5244471 (e : real) (l : real) (x : real) : (term150 e l x) = (term151 e l x).
Proof. exact (@lem1482981 (term152 e l x) (term24 l x)). Qed.
Lemma lem5244472 (e : real) (l : real) (x : real) : (term124 e l x) = (term151 e l x).
Proof. exact (TRANS (@lem5244470 e l x) (@lem5244471 e l x)). Qed.
Lemma lem5244473 (e : real) (l : real) (x : real) : (term153 e l x) = (term154 e l x).
Proof. exact (eq_refl (term153 e l x)). Qed.
Lemma lem5244474 (l : real) (x : real) : (term155 l x) = (term155 l x).
Proof. exact (eq_refl (term155 l x)). Qed.
Lemma lem5244475 (e : real) (l : real) (x : real) : (term156 e l x) = (term157 e l x).
Proof. exact (MK_COMB (@lem5244474 l x) (@lem5244473 e l x)). Qed.
Lemma lem5244476 (e : real) (l : real) (x : real) : (term158 e l x) = (term159 e l x).
Proof. exact (eq_refl (term158 e l x)). Qed.
Lemma lem5244477 (l : real) (x : real) : (term160 l x) = (term160 l x).
Proof. exact (eq_refl (term160 l x)). Qed.
Lemma lem5244478 (e : real) (l : real) (x : real) : (term161 e l x) = (term162 e l x).
Proof. exact (MK_COMB (@lem5244477 l x) (@lem5244476 e l x)). Qed.
Lemma lem5244479 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5244480 (e : real) (l : real) (x : real) : (term163 e l x) = (term164 e l x).
Proof. exact (MK_COMB (@lem5244479) (@lem5244478 e l x)). Qed.
Lemma lem5244481 (e : real) (l : real) (x : real) : (term151 e l x) = (term165 e l x).
Proof. exact (MK_COMB (@lem5244480 e l x) (@lem5244475 e l x)). Qed.
Lemma lem5244482 (e : real) (l : real) (x : real) : (term166 e l x) = (term166 e l x).
Proof. exact (eq_refl (term166 e l x)). Qed.
Lemma lem5244483 (e : real) (l : real) (x : real) : ((term124 e l x) = (term151 e l x)) = ((term124 e l x) = (term165 e l x)).
Proof. exact (MK_COMB (@lem5244482 e l x) (@lem5244481 e l x)). Qed.
Lemma lem5244484 (e : real) (l : real) (x : real) : (term124 e l x) = (term165 e l x).
Proof. exact (EQ_MP (@lem5244483 e l x) (@lem5244472 e l x)). Qed.
Lemma lem5244485 (l : real) (x : real) : (term167 l x) = (term168 l x).
Proof. exact (@lem1988291 (term24 l x) term32). Qed.
Lemma lem5244503 (l : real) (x : real) : (term169 l x) = (term170 l x).
Proof. exact (@lem1982792 (term24 l x) term32). Qed.
Lemma lem5244505 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5244506 : term32 = term172.
Proof. exact (@lem5244505 (NUMERAL 0)). Qed.
Lemma lem5244508 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5244509 : term51 = term84.
Proof. exact (@lem5244508 term85). Qed.
Lemma lem5244510 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5244511 : term86 = term87.
Proof. exact (MK_COMB (@lem5244510) (@lem5244509)). Qed.
Lemma lem5244512 : term173 = term174.
Proof. exact (MK_COMB (@lem5244511) (@lem5244506)). Qed.
Lemma lem5244513 : term174 = term175.
Proof. exact (@lem1981613 term51 term32 term91 term91). Qed.
Lemma lem5244515 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5244516 : term94 = term95.
Proof. exact (@lem5244515 term85 term85). Qed.
Lemma lem5244517 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5244518 : term97 = term85.
Proof. exact (EQ_MP (@lem5244517) (@lem940073)). Qed.
Lemma lem5244519 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5244520 : term95 = term91.
Proof. exact (MK_COMB (@lem5244519) (@lem5244518)). Qed.
Lemma lem5244521 : term94 = term91.
Proof. exact (TRANS (@lem5244516) (@lem5244520)). Qed.
Lemma lem5244523 (x : nat) : (term176 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5244524 : term173 = term32.
Proof. exact (@lem5244523 term85). Qed.
Lemma lem5244525 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5244526 : term177 = term178.
Proof. exact (MK_COMB (@lem5244525) (@lem5244524)). Qed.
Lemma lem5244527 : term175 = term172.
Proof. exact (MK_COMB (@lem5244526) (@lem5244521)). Qed.
Lemma lem5244528 : term174 = term172.
Proof. exact (TRANS (@lem5244513) (@lem5244527)). Qed.
Lemma lem5244529 : term173 = term172.
Proof. exact (TRANS (@lem5244512) (@lem5244528)). Qed.
Lemma lem5244531 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5244532 : term172 = term32.
Proof. exact (@lem5244531 term32). Qed.
Lemma lem5244533 : term173 = term32.
Proof. exact (TRANS (@lem5244529) (@lem5244532)). Qed.
Lemma lem5244534 (l : real) (x : real) : (term179 l x) = (term179 l x).
Proof. exact (eq_refl (term179 l x)). Qed.
Lemma lem5244535 (l : real) (x : real) : (term170 l x) = (term180 l x).
Proof. exact (MK_COMB (@lem5244534 l x) (@lem5244533)). Qed.
Lemma lem5244536 (l : real) (x : real) : (term180 l x) = (term24 l x).
Proof. exact (@lem1982723 (term24 l x)). Qed.
Lemma lem5244537 (l : real) (x : real) : (term170 l x) = (term24 l x).
Proof. exact (TRANS (@lem5244535 l x) (@lem5244536 l x)). Qed.
Lemma lem5244539 (l : real) (x : real) : (term169 l x) = (term24 l x).
Proof. exact (TRANS (@lem5244503 l x) (@lem5244537 l x)). Qed.
Lemma lem5244540 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5244541 (l : real) (x : real) : (term181 l x) = (term182 l x).
Proof. exact (MK_COMB (@lem5244540) (@lem5244539 l x)). Qed.
Lemma lem5244542 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5244543 (l : real) (x : real) : (term168 l x) = (term167 l x).
Proof. exact (MK_COMB (@lem5244541 l x) (@lem5244542)). Qed.
Lemma lem5244544 (l : real) (x : real) : (term167 l x) = (term167 l x).
Proof. exact (TRANS (@lem5244485 l x) (@lem5244543 l x)). Qed.
Lemma lem5244545 (e : real) (l : real) (x : real) : (term57 e l x) = (term183 e l x).
Proof. exact (@lem1988289 (term54 e l x) term32). Qed.
Lemma lem5244575 (e : real) (l : real) (x : real) : (term184 e l x) = (term185 e l x).
Proof. exact (@lem1982792 (term54 e l x) term32). Qed.
Lemma lem5244577 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5244578 : term32 = term172.
Proof. exact (@lem5244577 (NUMERAL 0)). Qed.
Lemma lem5244580 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5244581 : term51 = term84.
Proof. exact (@lem5244580 term85). Qed.
Lemma lem5244582 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5244583 : term86 = term87.
Proof. exact (MK_COMB (@lem5244582) (@lem5244581)). Qed.
Lemma lem5244584 : term173 = term174.
Proof. exact (MK_COMB (@lem5244583) (@lem5244578)). Qed.
Lemma lem5244585 : term174 = term175.
Proof. exact (@lem1981613 term51 term32 term91 term91). Qed.
Lemma lem5244587 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5244588 : term94 = term95.
Proof. exact (@lem5244587 term85 term85). Qed.
Lemma lem5244589 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5244590 : term97 = term85.
Proof. exact (EQ_MP (@lem5244589) (@lem940073)). Qed.
Lemma lem5244591 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5244592 : term95 = term91.
Proof. exact (MK_COMB (@lem5244591) (@lem5244590)). Qed.
Lemma lem5244593 : term94 = term91.
Proof. exact (TRANS (@lem5244588) (@lem5244592)). Qed.
Lemma lem5244595 (x : nat) : (term176 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5244596 : term173 = term32.
Proof. exact (@lem5244595 term85). Qed.
Lemma lem5244597 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5244598 : term177 = term178.
Proof. exact (MK_COMB (@lem5244597) (@lem5244596)). Qed.
Lemma lem5244599 : term175 = term172.
Proof. exact (MK_COMB (@lem5244598) (@lem5244593)). Qed.
Lemma lem5244600 : term174 = term172.
Proof. exact (TRANS (@lem5244585) (@lem5244599)). Qed.
Lemma lem5244601 : term173 = term172.
Proof. exact (TRANS (@lem5244584) (@lem5244600)). Qed.
Lemma lem5244603 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5244604 : term172 = term32.
Proof. exact (@lem5244603 term32). Qed.
Lemma lem5244605 : term173 = term32.
Proof. exact (TRANS (@lem5244601) (@lem5244604)). Qed.
Lemma lem5244606 (e : real) (l : real) (x : real) : (term186 e l x) = (term186 e l x).
Proof. exact (eq_refl (term186 e l x)). Qed.
Lemma lem5244607 (e : real) (l : real) (x : real) : (term185 e l x) = (term187 e l x).
Proof. exact (MK_COMB (@lem5244606 e l x) (@lem5244605)). Qed.
Lemma lem5244608 (e : real) (l : real) (x : real) : (term187 e l x) = (term54 e l x).
Proof. exact (@lem1982723 (term54 e l x)). Qed.
Lemma lem5244609 (e : real) (l : real) (x : real) : (term185 e l x) = (term54 e l x).
Proof. exact (TRANS (@lem5244607 e l x) (@lem5244608 e l x)). Qed.
Lemma lem5244611 (e : real) (l : real) (x : real) : (term184 e l x) = (term54 e l x).
Proof. exact (TRANS (@lem5244575 e l x) (@lem5244609 e l x)). Qed.
Lemma lem5244612 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5244613 (e : real) (l : real) (x : real) : (term188 e l x) = (term56 e l x).
Proof. exact (MK_COMB (@lem5244612) (@lem5244611 e l x)). Qed.
Lemma lem5244614 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5244615 (e : real) (l : real) (x : real) : (term183 e l x) = (term57 e l x).
Proof. exact (MK_COMB (@lem5244613 e l x) (@lem5244614)). Qed.
Lemma lem5244616 (e : real) (l : real) (x : real) : (term57 e l x) = (term57 e l x).
Proof. exact (TRANS (@lem5244545 e l x) (@lem5244615 e l x)). Qed.
Lemma lem5244617 (e : real) (l : real) (x : real) : (term111 e l x) = (term189 e l x).
Proof. exact (@lem1988291 (term108 e l x) term32). Qed.
Lemma lem5244641 (e : real) (l : real) (x : real) : (term190 e l x) = (term191 e l x).
Proof. exact (@lem1982792 (term108 e l x) term32). Qed.
Lemma lem5244643 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5244644 : term32 = term172.
Proof. exact (@lem5244643 (NUMERAL 0)). Qed.
Lemma lem5244646 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5244647 : term51 = term84.
Proof. exact (@lem5244646 term85). Qed.
Lemma lem5244648 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5244649 : term86 = term87.
Proof. exact (MK_COMB (@lem5244648) (@lem5244647)). Qed.
Lemma lem5244650 : term173 = term174.
Proof. exact (MK_COMB (@lem5244649) (@lem5244644)). Qed.
Lemma lem5244651 : term174 = term175.
Proof. exact (@lem1981613 term51 term32 term91 term91). Qed.
Lemma lem5244653 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5244654 : term94 = term95.
Proof. exact (@lem5244653 term85 term85). Qed.
Lemma lem5244655 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5244656 : term97 = term85.
Proof. exact (EQ_MP (@lem5244655) (@lem940073)). Qed.
Lemma lem5244657 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5244658 : term95 = term91.
Proof. exact (MK_COMB (@lem5244657) (@lem5244656)). Qed.
Lemma lem5244659 : term94 = term91.
Proof. exact (TRANS (@lem5244654) (@lem5244658)). Qed.
Lemma lem5244661 (x : nat) : (term176 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5244662 : term173 = term32.
Proof. exact (@lem5244661 term85). Qed.
Lemma lem5244663 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5244664 : term177 = term178.
Proof. exact (MK_COMB (@lem5244663) (@lem5244662)). Qed.
Lemma lem5244665 : term175 = term172.
Proof. exact (MK_COMB (@lem5244664) (@lem5244659)). Qed.
Lemma lem5244666 : term174 = term172.
Proof. exact (TRANS (@lem5244651) (@lem5244665)). Qed.
Lemma lem5244667 : term173 = term172.
Proof. exact (TRANS (@lem5244650) (@lem5244666)). Qed.
Lemma lem5244669 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5244670 : term172 = term32.
Proof. exact (@lem5244669 term32). Qed.
Lemma lem5244671 : term173 = term32.
Proof. exact (TRANS (@lem5244667) (@lem5244670)). Qed.
Lemma lem5244672 (e : real) (l : real) (x : real) : (term192 e l x) = (term192 e l x).
Proof. exact (eq_refl (term192 e l x)). Qed.
Lemma lem5244673 (e : real) (l : real) (x : real) : (term191 e l x) = (term193 e l x).
Proof. exact (MK_COMB (@lem5244672 e l x) (@lem5244671)). Qed.
Lemma lem5244674 (e : real) (l : real) (x : real) : (term193 e l x) = (term108 e l x).
Proof. exact (@lem1982723 (term108 e l x)). Qed.
Lemma lem5244675 (e : real) (l : real) (x : real) : (term191 e l x) = (term108 e l x).
Proof. exact (TRANS (@lem5244673 e l x) (@lem5244674 e l x)). Qed.
Lemma lem5244677 (e : real) (l : real) (x : real) : (term190 e l x) = (term108 e l x).
Proof. exact (TRANS (@lem5244641 e l x) (@lem5244675 e l x)). Qed.
Lemma lem5244678 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5244679 (e : real) (l : real) (x : real) : (term194 e l x) = (term110 e l x).
Proof. exact (MK_COMB (@lem5244678) (@lem5244677 e l x)). Qed.
Lemma lem5244680 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5244681 (e : real) (l : real) (x : real) : (term189 e l x) = (term111 e l x).
Proof. exact (MK_COMB (@lem5244679 e l x) (@lem5244680)). Qed.
Lemma lem5244682 (e : real) (l : real) (x : real) : (term111 e l x) = (term111 e l x).
Proof. exact (TRANS (@lem5244617 e l x) (@lem5244681 e l x)). Qed.
Lemma lem5244683 (e : real) (l : real) (x : real) : (term118 e l x) = (term195 e l x).
Proof. exact (@lem1988291 (term107 e l x) term32). Qed.
Lemma lem5244707 (e : real) (l : real) (x : real) : (term196 e l x) = (term197 e l x).
Proof. exact (@lem1982792 (term107 e l x) term32). Qed.
Lemma lem5244709 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5244710 : term32 = term172.
Proof. exact (@lem5244709 (NUMERAL 0)). Qed.
Lemma lem5244712 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5244713 : term51 = term84.
Proof. exact (@lem5244712 term85). Qed.
Lemma lem5244714 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5244715 : term86 = term87.
Proof. exact (MK_COMB (@lem5244714) (@lem5244713)). Qed.
Lemma lem5244716 : term173 = term174.
Proof. exact (MK_COMB (@lem5244715) (@lem5244710)). Qed.
Lemma lem5244717 : term174 = term175.
Proof. exact (@lem1981613 term51 term32 term91 term91). Qed.
Lemma lem5244719 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5244720 : term94 = term95.
Proof. exact (@lem5244719 term85 term85). Qed.
Lemma lem5244721 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5244722 : term97 = term85.
Proof. exact (EQ_MP (@lem5244721) (@lem940073)). Qed.
Lemma lem5244723 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5244724 : term95 = term91.
Proof. exact (MK_COMB (@lem5244723) (@lem5244722)). Qed.
Lemma lem5244725 : term94 = term91.
Proof. exact (TRANS (@lem5244720) (@lem5244724)). Qed.
Lemma lem5244727 (x : nat) : (term176 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5244728 : term173 = term32.
Proof. exact (@lem5244727 term85). Qed.
Lemma lem5244729 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5244730 : term177 = term178.
Proof. exact (MK_COMB (@lem5244729) (@lem5244728)). Qed.
Lemma lem5244731 : term175 = term172.
Proof. exact (MK_COMB (@lem5244730) (@lem5244725)). Qed.
Lemma lem5244732 : term174 = term172.
Proof. exact (TRANS (@lem5244717) (@lem5244731)). Qed.
Lemma lem5244733 : term173 = term172.
Proof. exact (TRANS (@lem5244716) (@lem5244732)). Qed.
Lemma lem5244735 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5244736 : term172 = term32.
Proof. exact (@lem5244735 term32). Qed.
Lemma lem5244737 : term173 = term32.
Proof. exact (TRANS (@lem5244733) (@lem5244736)). Qed.
Lemma lem5244738 (e : real) (l : real) (x : real) : (term198 e l x) = (term198 e l x).
Proof. exact (eq_refl (term198 e l x)). Qed.
Lemma lem5244739 (e : real) (l : real) (x : real) : (term197 e l x) = (term199 e l x).
Proof. exact (MK_COMB (@lem5244738 e l x) (@lem5244737)). Qed.
Lemma lem5244740 (e : real) (l : real) (x : real) : (term199 e l x) = (term107 e l x).
Proof. exact (@lem1982723 (term107 e l x)). Qed.
Lemma lem5244741 (e : real) (l : real) (x : real) : (term197 e l x) = (term107 e l x).
Proof. exact (TRANS (@lem5244739 e l x) (@lem5244740 e l x)). Qed.
Lemma lem5244743 (e : real) (l : real) (x : real) : (term196 e l x) = (term107 e l x).
Proof. exact (TRANS (@lem5244707 e l x) (@lem5244741 e l x)). Qed.
Lemma lem5244744 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5244745 (e : real) (l : real) (x : real) : (term200 e l x) = (term117 e l x).
Proof. exact (MK_COMB (@lem5244744) (@lem5244743 e l x)). Qed.
Lemma lem5244746 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5244747 (e : real) (l : real) (x : real) : (term195 e l x) = (term118 e l x).
Proof. exact (MK_COMB (@lem5244745 e l x) (@lem5244746)). Qed.
Lemma lem5244748 (e : real) (l : real) (x : real) : (term118 e l x) = (term118 e l x).
Proof. exact (TRANS (@lem5244683 e l x) (@lem5244747 e l x)). Qed.
Lemma lem5244749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5244750 (e : real) (l : real) (x : real) : (term120 e l x) = (term120 e l x).
Proof. exact (MK_COMB (@lem5244749) (@lem5244682 e l x)). Qed.
Lemma lem5244751 (e : real) (l : real) (x : real) : (term121 e l x) = (term121 e l x).
Proof. exact (MK_COMB (@lem5244750 e l x) (@lem5244748 e l x)). Qed.
Lemma lem5244752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5244753 (e : real) (l : real) (x : real) : (term201 e l x) = (term201 e l x).
Proof. exact (MK_COMB (@lem5244752) (@lem5244616 e l x)). Qed.
Lemma lem5244754 (e : real) (l : real) (x : real) : (term159 e l x) = (term159 e l x).
Proof. exact (MK_COMB (@lem5244753 e l x) (@lem5244751 e l x)). Qed.
Lemma lem5244755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5244756 (l : real) (x : real) : (term160 l x) = (term160 l x).
Proof. exact (MK_COMB (@lem5244755) (@lem5244544 l x)). Qed.
Lemma lem5244757 (e : real) (l : real) (x : real) : (term162 e l x) = (term162 e l x).
Proof. exact (MK_COMB (@lem5244756 l x) (@lem5244754 e l x)). Qed.
Lemma lem5244758 (l : real) (x : real) : (term202 l x) = (term203 l x).
Proof. exact (@lem1988289 term32 (term24 l x)). Qed.
Lemma lem5244776 (l : real) (x : real) : (term204 l x) = (term205 l x).
Proof. exact (@lem1982792 term32 (term24 l x)). Qed.
Lemma lem5244777 (l : real) (x : real) : (term78 l x) = (term79 l x).
Proof. exact (@lem1982781 (term25 l) term51 x). Qed.
Lemma lem5244778 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem5244779 (l : real) : (term80 l) = (term81 l).
Proof. exact (@lem1982749 term51 term51 l). Qed.
Lemma lem5244781 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5244782 : term51 = term84.
Proof. exact (@lem5244781 term85). Qed.
Lemma lem5244784 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5244785 : term51 = term84.
Proof. exact (@lem5244784 term85). Qed.
Lemma lem5244786 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5244787 : term86 = term87.
Proof. exact (MK_COMB (@lem5244786) (@lem5244785)). Qed.
Lemma lem5244788 : term88 = term89.
Proof. exact (MK_COMB (@lem5244787) (@lem5244782)). Qed.
Lemma lem5244789 : term89 = term90.
Proof. exact (@lem1981613 term51 term51 term91 term91). Qed.
Lemma lem5244791 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5244792 : term94 = term95.
Proof. exact (@lem5244791 term85 term85). Qed.
Lemma lem5244793 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5244794 : term97 = term85.
Proof. exact (EQ_MP (@lem5244793) (@lem940073)). Qed.
Lemma lem5244795 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5244796 : term95 = term91.
Proof. exact (MK_COMB (@lem5244795) (@lem5244794)). Qed.
Lemma lem5244797 : term94 = term91.
Proof. exact (TRANS (@lem5244792) (@lem5244796)). Qed.
Lemma lem5244799 (m : nat) (n : nat) : (term98 m n) = (term93 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5244800 : term88 = term95.
Proof. exact (@lem5244799 term85 term85). Qed.
Lemma lem5244801 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5244802 : term97 = term85.
Proof. exact (EQ_MP (@lem5244801) (@lem940073)). Qed.
Lemma lem5244803 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5244804 : term95 = term91.
Proof. exact (MK_COMB (@lem5244803) (@lem5244802)). Qed.
Lemma lem5244805 : term88 = term91.
Proof. exact (TRANS (@lem5244800) (@lem5244804)). Qed.
Lemma lem5244806 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5244807 : term99 = term100.
Proof. exact (MK_COMB (@lem5244806) (@lem5244805)). Qed.
Lemma lem5244808 : term90 = term101.
Proof. exact (MK_COMB (@lem5244807) (@lem5244797)). Qed.
Lemma lem5244809 : term89 = term101.
Proof. exact (TRANS (@lem5244789) (@lem5244808)). Qed.
Lemma lem5244810 : term88 = term101.
Proof. exact (TRANS (@lem5244788) (@lem5244809)). Qed.
Lemma lem5244812 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5244813 : term101 = term91.
Proof. exact (@lem5244812 term91). Qed.
Lemma lem5244814 : term88 = term91.
Proof. exact (TRANS (@lem5244810) (@lem5244813)). Qed.
Lemma lem5244815 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5244816 : term103 = term104.
Proof. exact (MK_COMB (@lem5244815) (@lem5244814)). Qed.
Lemma lem5244817 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5244818 (l : real) : (term81 l) = (term105 l).
Proof. exact (MK_COMB (@lem5244816) (@lem5244817 l)). Qed.
Lemma lem5244819 (l : real) : (term80 l) = (term105 l).
Proof. exact (TRANS (@lem5244779 l) (@lem5244818 l)). Qed.
Lemma lem5244820 (l : real) : (term105 l) = l.
Proof. exact (@lem1982709 l). Qed.
Lemma lem5244821 (l : real) : (term80 l) = l.
Proof. exact (TRANS (@lem5244819 l) (@lem5244820 l)). Qed.
Lemma lem5244822 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5244823 (l : real) : (term106 l) = (real_add l).
Proof. exact (MK_COMB (@lem5244822) (@lem5244821 l)). Qed.
Lemma lem5244824 (l : real) (x : real) : (term79 l x) = (term23 l x).
Proof. exact (MK_COMB (@lem5244823 l) (@lem5244778 x)). Qed.
Lemma lem5244825 (l : real) (x : real) : (term78 l x) = (term23 l x).
Proof. exact (TRANS (@lem5244777 l x) (@lem5244824 l x)). Qed.
Lemma lem5244826 : term206 = term206.
Proof. exact (eq_refl term206). Qed.
Lemma lem5244827 (l : real) (x : real) : (term205 l x) = (term207 l x).
Proof. exact (MK_COMB (@lem5244826) (@lem5244825 l x)). Qed.
Lemma lem5244828 (l : real) (x : real) : (term207 l x) = (term23 l x).
Proof. exact (@lem1982721 (term23 l x)). Qed.
Lemma lem5244829 (l : real) (x : real) : (term205 l x) = (term23 l x).
Proof. exact (TRANS (@lem5244827 l x) (@lem5244828 l x)). Qed.
Lemma lem5244831 (l : real) (x : real) : (term204 l x) = (term23 l x).
Proof. exact (TRANS (@lem5244776 l x) (@lem5244829 l x)). Qed.
Lemma lem5244832 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5244833 (l : real) (x : real) : (term208 l x) = (term209 l x).
Proof. exact (MK_COMB (@lem5244832) (@lem5244831 l x)). Qed.
Lemma lem5244834 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5244835 (l : real) (x : real) : (term203 l x) = (term210 l x).
Proof. exact (MK_COMB (@lem5244833 l x) (@lem5244834)). Qed.
Lemma lem5244836 (l : real) (x : real) : (term202 l x) = (term210 l x).
Proof. exact (TRANS (@lem5244758 l x) (@lem5244835 l x)). Qed.
Lemma lem5244837 (e : real) (l : real) (x : real) : (term211 e l x) = (term212 e l x).
Proof. exact (@lem1988289 (term213 e l x) term32). Qed.
Lemma lem5244838 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5244854 (l : real) (x : real) : (term214 l x) = (term78 l x).
Proof. exact (@lem1982785 (term24 l x)). Qed.
Lemma lem5244855 (l : real) (x : real) : (term78 l x) = (term79 l x).
Proof. exact (@lem1982781 (term25 l) term51 x). Qed.
Lemma lem5244856 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem5244857 (l : real) : (term80 l) = (term81 l).
Proof. exact (@lem1982749 term51 term51 l). Qed.
Lemma lem5244859 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5244860 : term51 = term84.
Proof. exact (@lem5244859 term85). Qed.
Lemma lem5244862 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5244863 : term51 = term84.
Proof. exact (@lem5244862 term85). Qed.
Lemma lem5244864 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5244865 : term86 = term87.
Proof. exact (MK_COMB (@lem5244864) (@lem5244863)). Qed.
Lemma lem5244866 : term88 = term89.
Proof. exact (MK_COMB (@lem5244865) (@lem5244860)). Qed.
Lemma lem5244867 : term89 = term90.
Proof. exact (@lem1981613 term51 term51 term91 term91). Qed.
Lemma lem5244869 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5244870 : term94 = term95.
Proof. exact (@lem5244869 term85 term85). Qed.
Lemma lem5244871 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5244872 : term97 = term85.
Proof. exact (EQ_MP (@lem5244871) (@lem940073)). Qed.
Lemma lem5244873 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5244874 : term95 = term91.
Proof. exact (MK_COMB (@lem5244873) (@lem5244872)). Qed.
Lemma lem5244875 : term94 = term91.
Proof. exact (TRANS (@lem5244870) (@lem5244874)). Qed.
Lemma lem5244877 (m : nat) (n : nat) : (term98 m n) = (term93 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5244878 : term88 = term95.
Proof. exact (@lem5244877 term85 term85). Qed.
Lemma lem5244879 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5244880 : term97 = term85.
Proof. exact (EQ_MP (@lem5244879) (@lem940073)). Qed.
Lemma lem5244881 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5244882 : term95 = term91.
Proof. exact (MK_COMB (@lem5244881) (@lem5244880)). Qed.
Lemma lem5244883 : term88 = term91.
Proof. exact (TRANS (@lem5244878) (@lem5244882)). Qed.
Lemma lem5244884 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5244885 : term99 = term100.
Proof. exact (MK_COMB (@lem5244884) (@lem5244883)). Qed.
Lemma lem5244886 : term90 = term101.
Proof. exact (MK_COMB (@lem5244885) (@lem5244875)). Qed.
Lemma lem5244887 : term89 = term101.
Proof. exact (TRANS (@lem5244867) (@lem5244886)). Qed.
Lemma lem5244888 : term88 = term101.
Proof. exact (TRANS (@lem5244866) (@lem5244887)). Qed.
Lemma lem5244890 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5244891 : term101 = term91.
Proof. exact (@lem5244890 term91). Qed.
Lemma lem5244892 : term88 = term91.
Proof. exact (TRANS (@lem5244888) (@lem5244891)). Qed.
Lemma lem5244893 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5244894 : term103 = term104.
Proof. exact (MK_COMB (@lem5244893) (@lem5244892)). Qed.
Lemma lem5244895 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5244896 (l : real) : (term81 l) = (term105 l).
Proof. exact (MK_COMB (@lem5244894) (@lem5244895 l)). Qed.
Lemma lem5244897 (l : real) : (term80 l) = (term105 l).
Proof. exact (TRANS (@lem5244857 l) (@lem5244896 l)). Qed.
Lemma lem5244898 (l : real) : (term105 l) = l.
Proof. exact (@lem1982709 l). Qed.
Lemma lem5244899 (l : real) : (term80 l) = l.
Proof. exact (TRANS (@lem5244897 l) (@lem5244898 l)). Qed.
Lemma lem5244900 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5244901 (l : real) : (term106 l) = (real_add l).
Proof. exact (MK_COMB (@lem5244900) (@lem5244899 l)). Qed.
Lemma lem5244902 (l : real) (x : real) : (term79 l x) = (term23 l x).
Proof. exact (MK_COMB (@lem5244901 l) (@lem5244856 x)). Qed.
Lemma lem5244903 (l : real) (x : real) : (term78 l x) = (term23 l x).
Proof. exact (TRANS (@lem5244855 l x) (@lem5244902 l x)). Qed.
Lemma lem5244905 (l : real) (x : real) : (term214 l x) = (term23 l x).
Proof. exact (TRANS (@lem5244854 l x) (@lem5244903 l x)). Qed.
Lemma lem5244914 (e : real) : (term53 e) = (term53 e).
Proof. exact (eq_refl (term53 e)). Qed.
Lemma lem5244917 (e : real) (l : real) (x : real) : (term213 e l x) = (term41 e l x).
Proof. exact (MK_COMB (@lem5244914 e) (@lem5244905 l x)). Qed.
Lemma lem5244918 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5244919 (e : real) (l : real) (x : real) : (term215 e l x) = (term216 e l x).
Proof. exact (MK_COMB (@lem5244918) (@lem5244917 e l x)). Qed.
Lemma lem5244920 (e : real) (l : real) (x : real) : (term217 e l x) = (term218 e l x).
Proof. exact (MK_COMB (@lem5244919 e l x) (@lem5244838)). Qed.
Lemma lem5244921 (e : real) (l : real) (x : real) : (term218 e l x) = (term219 e l x).
Proof. exact (@lem1982792 (term41 e l x) term32). Qed.
Lemma lem5244923 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5244924 : term32 = term172.
Proof. exact (@lem5244923 (NUMERAL 0)). Qed.
Lemma lem5244926 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5244927 : term51 = term84.
Proof. exact (@lem5244926 term85). Qed.
Lemma lem5244928 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5244929 : term86 = term87.
Proof. exact (MK_COMB (@lem5244928) (@lem5244927)). Qed.
Lemma lem5244930 : term173 = term174.
Proof. exact (MK_COMB (@lem5244929) (@lem5244924)). Qed.
Lemma lem5244931 : term174 = term175.
Proof. exact (@lem1981613 term51 term32 term91 term91). Qed.
Lemma lem5244933 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5244934 : term94 = term95.
Proof. exact (@lem5244933 term85 term85). Qed.
Lemma lem5244935 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5244936 : term97 = term85.
Proof. exact (EQ_MP (@lem5244935) (@lem940073)). Qed.
Lemma lem5244937 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5244938 : term95 = term91.
Proof. exact (MK_COMB (@lem5244937) (@lem5244936)). Qed.
Lemma lem5244939 : term94 = term91.
Proof. exact (TRANS (@lem5244934) (@lem5244938)). Qed.
Lemma lem5244941 (x : nat) : (term176 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5244942 : term173 = term32.
Proof. exact (@lem5244941 term85). Qed.
Lemma lem5244943 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5244944 : term177 = term178.
Proof. exact (MK_COMB (@lem5244943) (@lem5244942)). Qed.
Lemma lem5244945 : term175 = term172.
Proof. exact (MK_COMB (@lem5244944) (@lem5244939)). Qed.
Lemma lem5244946 : term174 = term172.
Proof. exact (TRANS (@lem5244931) (@lem5244945)). Qed.
Lemma lem5244947 : term173 = term172.
Proof. exact (TRANS (@lem5244930) (@lem5244946)). Qed.
Lemma lem5244949 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5244950 : term172 = term32.
Proof. exact (@lem5244949 term32). Qed.
Lemma lem5244951 : term173 = term32.
Proof. exact (TRANS (@lem5244947) (@lem5244950)). Qed.
Lemma lem5244952 (e : real) (l : real) (x : real) : (term220 e l x) = (term220 e l x).
Proof. exact (eq_refl (term220 e l x)). Qed.
Lemma lem5244953 (e : real) (l : real) (x : real) : (term219 e l x) = (term221 e l x).
Proof. exact (MK_COMB (@lem5244952 e l x) (@lem5244951)). Qed.
Lemma lem5244954 (e : real) (l : real) (x : real) : (term221 e l x) = (term41 e l x).
Proof. exact (@lem1982723 (term41 e l x)). Qed.
Lemma lem5244955 (e : real) (l : real) (x : real) : (term219 e l x) = (term41 e l x).
Proof. exact (TRANS (@lem5244953 e l x) (@lem5244954 e l x)). Qed.
Lemma lem5244956 (e : real) (l : real) (x : real) : (term218 e l x) = (term41 e l x).
Proof. exact (TRANS (@lem5244921 e l x) (@lem5244955 e l x)). Qed.
Lemma lem5244957 (e : real) (l : real) (x : real) : (term217 e l x) = (term41 e l x).
Proof. exact (TRANS (@lem5244920 e l x) (@lem5244956 e l x)). Qed.
Lemma lem5244958 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5244959 (e : real) (l : real) (x : real) : (term222 e l x) = (term43 e l x).
Proof. exact (MK_COMB (@lem5244958) (@lem5244957 e l x)). Qed.
Lemma lem5244960 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5244961 (e : real) (l : real) (x : real) : (term212 e l x) = (term44 e l x).
Proof. exact (MK_COMB (@lem5244959 e l x) (@lem5244960)). Qed.
Lemma lem5244962 (e : real) (l : real) (x : real) : (term211 e l x) = (term44 e l x).
Proof. exact (TRANS (@lem5244837 e l x) (@lem5244961 e l x)). Qed.
Lemma lem5244963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5244964 (e : real) (l : real) (x : real) : (term120 e l x) = (term120 e l x).
Proof. exact (MK_COMB (@lem5244963) (@lem5244682 e l x)). Qed.
Lemma lem5244965 (e : real) (l : real) (x : real) : (term121 e l x) = (term121 e l x).
Proof. exact (MK_COMB (@lem5244964 e l x) (@lem5244748 e l x)). Qed.
Lemma lem5244966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5244967 (e : real) (l : real) (x : real) : (term223 e l x) = (term224 e l x).
Proof. exact (MK_COMB (@lem5244966) (@lem5244962 e l x)). Qed.
Lemma lem5244968 (e : real) (l : real) (x : real) : (term154 e l x) = (term225 e l x).
Proof. exact (MK_COMB (@lem5244967 e l x) (@lem5244965 e l x)). Qed.
Lemma lem5244969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5244970 (l : real) (x : real) : (term155 l x) = (term226 l x).
Proof. exact (MK_COMB (@lem5244969) (@lem5244836 l x)). Qed.
Lemma lem5244971 (e : real) (l : real) (x : real) : (term157 e l x) = (term227 e l x).
Proof. exact (MK_COMB (@lem5244970 l x) (@lem5244968 e l x)). Qed.
Lemma lem5244972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5244973 (e : real) (l : real) (x : real) : (term164 e l x) = (term164 e l x).
Proof. exact (MK_COMB (@lem5244972) (@lem5244757 e l x)). Qed.
Lemma lem5244974 (e : real) (l : real) (x : real) : (term165 e l x) = (term228 e l x).
Proof. exact (MK_COMB (@lem5244973 e l x) (@lem5244971 e l x)). Qed.
Lemma lem5244986 (e : real) (l : real) (x : real) : (term124 e l x) = (term228 e l x).
Proof. exact (TRANS (@lem5244484 e l x) (@lem5244974 e l x)). Qed.
Lemma lem5244987 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5244988 (e : real) (l : real) (x : real) : (term128 e l x) = (term229 e l x).
Proof. exact (MK_COMB (@lem5244987) (@lem5244467 e l x)). Qed.
Lemma lem5244989 (e : real) (l : real) (x : real) : (term129 e l x) = (term230 e l x).
Proof. exact (MK_COMB (@lem5244988 e l x) (@lem5244986 e l x)). Qed.
Lemma lem5244990 (e : real) (l : real) (x : real) (h1 : term230 e l x) : term230 e l x.
Proof. exact (h1). Qed.
Lemma lem5244991 (e : real) (l : real) (x : real) (h1 : term149 e l x) : term149 e l x.
Proof. exact (h1). Qed.
Lemma lem5244992 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term144 e l x.
Proof. exact (h1). Qed.
Lemma lem5244993 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term44 e l x.
Proof. exact (proj2 (@lem5244992 e l x h1)). Qed.
Lemma lem5244994 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term141 e l x.
Proof. exact (proj1 (@lem5244992 e l x h1)). Qed.
Lemma lem5244995 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term111 e l x.
Proof. exact (proj2 (@lem5244994 e l x h1)). Qed.
Lemma lem5244998 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5244999 : term231 = term232.
Proof. exact (@lem5244998 term32 term91). Qed.
Lemma lem5245001 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245002 : term91 = term101.
Proof. exact (@lem5245001 term85). Qed.
Lemma lem5245004 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245005 : term32 = term172.
Proof. exact (@lem5245004 (NUMERAL 0)). Qed.
Lemma lem5245006 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5245007 : term233 = term234.
Proof. exact (MK_COMB (@lem5245006) (@lem5245005)). Qed.
Lemma lem5245008 : term232 = term235.
Proof. exact (MK_COMB (@lem5245007) (@lem5245002)). Qed.
Lemma lem5245009 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5245011 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245012 : term232 = term238.
Proof. exact (@lem5245011 (NUMERAL 0) term85). Qed.
Lemma lem5245013 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245014 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245015 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245014 h1) (fun h1 : term238 = True => @lem5245013)). Qed.
Lemma lem5245016 : term238 = True.
Proof. exact (EQ_MP (@lem5245015) (@lem5245013)). Qed.
Lemma lem5245017 : term232 = True.
Proof. exact (TRANS (@lem5245012) (@lem5245016)). Qed.
Lemma lem5245018 : True = term232.
Proof. exact (SYM (@lem5245017)). Qed.
Lemma lem5245019 : term232.
Proof. exact (EQ_MP (@lem5245018) (@lem0)). Qed.
Lemma lem5245020 : term240.
Proof. exact (@lem5245009 (@lem5245019)). Qed.
Lemma lem5245022 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245023 : term232 = term238.
Proof. exact (@lem5245022 (NUMERAL 0) term85). Qed.
Lemma lem5245024 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245025 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245026 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245025 h1) (fun h1 : term238 = True => @lem5245024)). Qed.
Lemma lem5245027 : term238 = True.
Proof. exact (EQ_MP (@lem5245026) (@lem5245024)). Qed.
Lemma lem5245028 : term232 = True.
Proof. exact (TRANS (@lem5245023) (@lem5245027)). Qed.
Lemma lem5245029 : True = term232.
Proof. exact (SYM (@lem5245028)). Qed.
Lemma lem5245030 : term232.
Proof. exact (EQ_MP (@lem5245029) (@lem0)). Qed.
Lemma lem5245031 : term235 = term241.
Proof. exact (@lem5245020 (@lem5245030)). Qed.
Lemma lem5245033 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245034 : term94 = term95.
Proof. exact (@lem5245033 term85 term85). Qed.
Lemma lem5245035 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245036 : term97 = term85.
Proof. exact (EQ_MP (@lem5245035) (@lem940073)). Qed.
Lemma lem5245037 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245038 : term95 = term91.
Proof. exact (MK_COMB (@lem5245037) (@lem5245036)). Qed.
Lemma lem5245039 : term94 = term91.
Proof. exact (TRANS (@lem5245034) (@lem5245038)). Qed.
Lemma lem5245041 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245042 : term243 = term32.
Proof. exact (@lem5245041 term85). Qed.
Lemma lem5245043 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5245044 : term244 = term233.
Proof. exact (MK_COMB (@lem5245043) (@lem5245042)). Qed.
Lemma lem5245045 : term241 = term232.
Proof. exact (MK_COMB (@lem5245044) (@lem5245039)). Qed.
Lemma lem5245047 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245048 : term232 = term238.
Proof. exact (@lem5245047 (NUMERAL 0) term85). Qed.
Lemma lem5245049 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245050 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245051 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245050 h1) (fun h1 : term238 = True => @lem5245049)). Qed.
Lemma lem5245052 : term238 = True.
Proof. exact (EQ_MP (@lem5245051) (@lem5245049)). Qed.
Lemma lem5245053 : term232 = True.
Proof. exact (TRANS (@lem5245048) (@lem5245052)). Qed.
Lemma lem5245054 : term241 = True.
Proof. exact (TRANS (@lem5245045) (@lem5245053)). Qed.
Lemma lem5245055 : term235 = True.
Proof. exact (TRANS (@lem5245031) (@lem5245054)). Qed.
Lemma lem5245056 : term232 = True.
Proof. exact (TRANS (@lem5245008) (@lem5245055)). Qed.
Lemma lem5245057 : term231 = True.
Proof. exact (TRANS (@lem5244999) (@lem5245056)). Qed.
Lemma lem5245058 : True = term231.
Proof. exact (SYM (@lem5245057)). Qed.
Lemma lem5245059 : term231.
Proof. exact (EQ_MP (@lem5245058) (@lem0)). Qed.
Lemma lem5245060 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term245 e l x.
Proof. exact (conj (@lem5245059) (@lem5244995 e l x h1)). Qed.
Lemma lem5245062 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5245063 (e : real) (l : real) (x : real) : term247 e l x.
Proof. exact (@lem5245062 term91 (term108 e l x)). Qed.
Lemma lem5245064 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term248 e l x.
Proof. exact (@lem5245063 e l x (@lem5245060 e l x h1)). Qed.
Lemma lem5245065 (e : real) (l : real) (x : real) : (term249 e l x) = (term108 e l x).
Proof. exact (@lem1982733 (term108 e l x)). Qed.
Lemma lem5245066 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5245067 (e : real) (l : real) (x : real) : (term250 e l x) = (term110 e l x).
Proof. exact (MK_COMB (@lem5245066) (@lem5245065 e l x)). Qed.
Lemma lem5245068 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5245069 (e : real) (l : real) (x : real) : (term248 e l x) = (term111 e l x).
Proof. exact (MK_COMB (@lem5245067 e l x) (@lem5245068)). Qed.
Lemma lem5245070 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term111 e l x.
Proof. exact (EQ_MP (@lem5245069 e l x) (@lem5245064 e l x h1)). Qed.
Lemma lem5245072 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5245073 : term231 = term232.
Proof. exact (@lem5245072 term32 term91). Qed.
Lemma lem5245075 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245076 : term91 = term101.
Proof. exact (@lem5245075 term85). Qed.
Lemma lem5245078 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245079 : term32 = term172.
Proof. exact (@lem5245078 (NUMERAL 0)). Qed.
Lemma lem5245080 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5245081 : term233 = term234.
Proof. exact (MK_COMB (@lem5245080) (@lem5245079)). Qed.
Lemma lem5245082 : term232 = term235.
Proof. exact (MK_COMB (@lem5245081) (@lem5245076)). Qed.
Lemma lem5245083 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5245085 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245086 : term232 = term238.
Proof. exact (@lem5245085 (NUMERAL 0) term85). Qed.
Lemma lem5245087 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245088 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245089 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245088 h1) (fun h1 : term238 = True => @lem5245087)). Qed.
Lemma lem5245090 : term238 = True.
Proof. exact (EQ_MP (@lem5245089) (@lem5245087)). Qed.
Lemma lem5245091 : term232 = True.
Proof. exact (TRANS (@lem5245086) (@lem5245090)). Qed.
Lemma lem5245092 : True = term232.
Proof. exact (SYM (@lem5245091)). Qed.
Lemma lem5245093 : term232.
Proof. exact (EQ_MP (@lem5245092) (@lem0)). Qed.
Lemma lem5245094 : term240.
Proof. exact (@lem5245083 (@lem5245093)). Qed.
Lemma lem5245096 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245097 : term232 = term238.
Proof. exact (@lem5245096 (NUMERAL 0) term85). Qed.
Lemma lem5245098 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245099 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245100 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245099 h1) (fun h1 : term238 = True => @lem5245098)). Qed.
Lemma lem5245101 : term238 = True.
Proof. exact (EQ_MP (@lem5245100) (@lem5245098)). Qed.
Lemma lem5245102 : term232 = True.
Proof. exact (TRANS (@lem5245097) (@lem5245101)). Qed.
Lemma lem5245103 : True = term232.
Proof. exact (SYM (@lem5245102)). Qed.
Lemma lem5245104 : term232.
Proof. exact (EQ_MP (@lem5245103) (@lem0)). Qed.
Lemma lem5245105 : term235 = term241.
Proof. exact (@lem5245094 (@lem5245104)). Qed.
Lemma lem5245107 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245108 : term94 = term95.
Proof. exact (@lem5245107 term85 term85). Qed.
Lemma lem5245109 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245110 : term97 = term85.
Proof. exact (EQ_MP (@lem5245109) (@lem940073)). Qed.
Lemma lem5245111 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245112 : term95 = term91.
Proof. exact (MK_COMB (@lem5245111) (@lem5245110)). Qed.
Lemma lem5245113 : term94 = term91.
Proof. exact (TRANS (@lem5245108) (@lem5245112)). Qed.
Lemma lem5245115 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245116 : term243 = term32.
Proof. exact (@lem5245115 term85). Qed.
Lemma lem5245117 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5245118 : term244 = term233.
Proof. exact (MK_COMB (@lem5245117) (@lem5245116)). Qed.
Lemma lem5245119 : term241 = term232.
Proof. exact (MK_COMB (@lem5245118) (@lem5245113)). Qed.
Lemma lem5245121 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245122 : term232 = term238.
Proof. exact (@lem5245121 (NUMERAL 0) term85). Qed.
Lemma lem5245123 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245124 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245125 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245124 h1) (fun h1 : term238 = True => @lem5245123)). Qed.
Lemma lem5245126 : term238 = True.
Proof. exact (EQ_MP (@lem5245125) (@lem5245123)). Qed.
Lemma lem5245127 : term232 = True.
Proof. exact (TRANS (@lem5245122) (@lem5245126)). Qed.
Lemma lem5245128 : term241 = True.
Proof. exact (TRANS (@lem5245119) (@lem5245127)). Qed.
Lemma lem5245129 : term235 = True.
Proof. exact (TRANS (@lem5245105) (@lem5245128)). Qed.
Lemma lem5245130 : term232 = True.
Proof. exact (TRANS (@lem5245082) (@lem5245129)). Qed.
Lemma lem5245131 : term231 = True.
Proof. exact (TRANS (@lem5245073) (@lem5245130)). Qed.
Lemma lem5245132 : True = term231.
Proof. exact (SYM (@lem5245131)). Qed.
Lemma lem5245133 : term231.
Proof. exact (EQ_MP (@lem5245132) (@lem0)). Qed.
Lemma lem5245134 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term251 e l x.
Proof. exact (conj (@lem5245133) (@lem5244993 e l x h1)). Qed.
Lemma lem5245136 (x : real) (y : real) : term252 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5245137 (e : real) (l : real) (x : real) : term253 e l x.
Proof. exact (@lem5245136 term91 (term41 e l x)). Qed.
Lemma lem5245138 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term254 e l x.
Proof. exact (@lem5245137 e l x (@lem5245134 e l x h1)). Qed.
Lemma lem5245139 (e : real) (l : real) (x : real) : (term255 e l x) = (term41 e l x).
Proof. exact (@lem1982733 (term41 e l x)). Qed.
Lemma lem5245140 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5245141 (e : real) (l : real) (x : real) : (term256 e l x) = (term43 e l x).
Proof. exact (MK_COMB (@lem5245140) (@lem5245139 e l x)). Qed.
Lemma lem5245142 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5245143 (e : real) (l : real) (x : real) : (term254 e l x) = (term44 e l x).
Proof. exact (MK_COMB (@lem5245141 e l x) (@lem5245142)). Qed.
Lemma lem5245144 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term44 e l x.
Proof. exact (EQ_MP (@lem5245143 e l x) (@lem5245138 e l x h1)). Qed.
Lemma lem5245145 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term257 e l x.
Proof. exact (conj (@lem5245144 e l x h1) (@lem5245070 e l x h1)). Qed.
Lemma lem5245147 (x : real) (y : real) : term258 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5245148 (e : real) (l : real) (x : real) : term259 e l x.
Proof. exact (@lem5245147 (term41 e l x) (term108 e l x)). Qed.
Lemma lem5245149 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term260 e l x.
Proof. exact (@lem5245148 e l x (@lem5245145 e l x h1)). Qed.
Lemma lem5245150 (e : real) (l : real) (x : real) : (term261 e l x) = (term262 e l x).
Proof. exact (@lem1982753 (term25 e) e (term23 l x) (term24 l x)). Qed.
Lemma lem5245151 (e : real) : (term263 e) = (term264 e).
Proof. exact (@lem1982713 term51 e). Qed.
Lemma lem5245153 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245154 : term91 = term101.
Proof. exact (@lem5245153 term85). Qed.
Lemma lem5245156 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5245157 : term51 = term84.
Proof. exact (@lem5245156 term85). Qed.
Lemma lem5245158 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245159 : term265 = term266.
Proof. exact (MK_COMB (@lem5245158) (@lem5245157)). Qed.
Lemma lem5245160 : term267 = term268.
Proof. exact (MK_COMB (@lem5245159) (@lem5245154)). Qed.
Lemma lem5245161 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5245163 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245164 : term232 = term238.
Proof. exact (@lem5245163 (NUMERAL 0) term85). Qed.
Lemma lem5245165 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245166 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245167 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245166 h1) (fun h1 : term238 = True => @lem5245165)). Qed.
Lemma lem5245168 : term238 = True.
Proof. exact (EQ_MP (@lem5245167) (@lem5245165)). Qed.
Lemma lem5245169 : term232 = True.
Proof. exact (TRANS (@lem5245164) (@lem5245168)). Qed.
Lemma lem5245170 : True = term232.
Proof. exact (SYM (@lem5245169)). Qed.
Lemma lem5245171 : term232.
Proof. exact (EQ_MP (@lem5245170) (@lem0)). Qed.
Lemma lem5245172 : term270.
Proof. exact (@lem5245161 (@lem5245171)). Qed.
Lemma lem5245174 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245175 : term232 = term238.
Proof. exact (@lem5245174 (NUMERAL 0) term85). Qed.
Lemma lem5245176 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245177 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245178 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245177 h1) (fun h1 : term238 = True => @lem5245176)). Qed.
Lemma lem5245179 : term238 = True.
Proof. exact (EQ_MP (@lem5245178) (@lem5245176)). Qed.
Lemma lem5245180 : term232 = True.
Proof. exact (TRANS (@lem5245175) (@lem5245179)). Qed.
Lemma lem5245181 : True = term232.
Proof. exact (SYM (@lem5245180)). Qed.
Lemma lem5245182 : term232.
Proof. exact (EQ_MP (@lem5245181) (@lem0)). Qed.
Lemma lem5245183 : term271.
Proof. exact (@lem5245172 (@lem5245182)). Qed.
Lemma lem5245185 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245186 : term232 = term238.
Proof. exact (@lem5245185 (NUMERAL 0) term85). Qed.
Lemma lem5245187 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245188 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245189 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245188 h1) (fun h1 : term238 = True => @lem5245187)). Qed.
Lemma lem5245190 : term238 = True.
Proof. exact (EQ_MP (@lem5245189) (@lem5245187)). Qed.
Lemma lem5245191 : term232 = True.
Proof. exact (TRANS (@lem5245186) (@lem5245190)). Qed.
Lemma lem5245192 : True = term232.
Proof. exact (SYM (@lem5245191)). Qed.
Lemma lem5245193 : term232.
Proof. exact (EQ_MP (@lem5245192) (@lem0)). Qed.
Lemma lem5245194 : term272.
Proof. exact (@lem5245183 (@lem5245193)). Qed.
Lemma lem5245196 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245197 : term94 = term95.
Proof. exact (@lem5245196 term85 term85). Qed.
Lemma lem5245198 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245199 : term97 = term85.
Proof. exact (EQ_MP (@lem5245198) (@lem940073)). Qed.
Lemma lem5245200 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245201 : term95 = term91.
Proof. exact (MK_COMB (@lem5245200) (@lem5245199)). Qed.
Lemma lem5245202 : term94 = term91.
Proof. exact (TRANS (@lem5245197) (@lem5245201)). Qed.
Lemma lem5245204 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5245205 : term275 = term276.
Proof. exact (@lem5245204 term85 term85). Qed.
Lemma lem5245206 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245207 : term97 = term85.
Proof. exact (EQ_MP (@lem5245206) (@lem940073)). Qed.
Lemma lem5245208 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245209 : term95 = term91.
Proof. exact (MK_COMB (@lem5245208) (@lem5245207)). Qed.
Lemma lem5245210 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5245211 : term276 = term51.
Proof. exact (MK_COMB (@lem5245210) (@lem5245209)). Qed.
Lemma lem5245212 : term275 = term51.
Proof. exact (TRANS (@lem5245205) (@lem5245211)). Qed.
Lemma lem5245213 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245214 : term277 = term265.
Proof. exact (MK_COMB (@lem5245213) (@lem5245212)). Qed.
Lemma lem5245215 : term278 = term267.
Proof. exact (MK_COMB (@lem5245214) (@lem5245202)). Qed.
Lemma lem5245217 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5245218 : term267 = term32.
Proof. exact (@lem5245217 term85). Qed.
Lemma lem5245219 : term278 = term32.
Proof. exact (TRANS (@lem5245215) (@lem5245218)). Qed.
Lemma lem5245220 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5245221 : term280 = term281.
Proof. exact (MK_COMB (@lem5245220) (@lem5245219)). Qed.
Lemma lem5245222 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5245223 : term282 = term243.
Proof. exact (MK_COMB (@lem5245221) (@lem5245222)). Qed.
Lemma lem5245225 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245226 : term243 = term32.
Proof. exact (@lem5245225 term85). Qed.
Lemma lem5245227 : term282 = term32.
Proof. exact (TRANS (@lem5245223) (@lem5245226)). Qed.
Lemma lem5245229 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245230 : term94 = term95.
Proof. exact (@lem5245229 term85 term85). Qed.
Lemma lem5245231 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245232 : term97 = term85.
Proof. exact (EQ_MP (@lem5245231) (@lem940073)). Qed.
Lemma lem5245233 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245234 : term95 = term91.
Proof. exact (MK_COMB (@lem5245233) (@lem5245232)). Qed.
Lemma lem5245235 : term94 = term91.
Proof. exact (TRANS (@lem5245230) (@lem5245234)). Qed.
Lemma lem5245236 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5245237 : term283 = term243.
Proof. exact (MK_COMB (@lem5245236) (@lem5245235)). Qed.
Lemma lem5245239 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245240 : term243 = term32.
Proof. exact (@lem5245239 term85). Qed.
Lemma lem5245241 : term283 = term32.
Proof. exact (TRANS (@lem5245237) (@lem5245240)). Qed.
Lemma lem5245242 : term32 = term283.
Proof. exact (SYM (@lem5245241)). Qed.
Lemma lem5245243 : term282 = term283.
Proof. exact (TRANS (@lem5245227) (@lem5245242)). Qed.
Lemma lem5245244 : term268 = term172.
Proof. exact (@lem5245194 (@lem5245243)). Qed.
Lemma lem5245245 : term267 = term172.
Proof. exact (TRANS (@lem5245160) (@lem5245244)). Qed.
Lemma lem5245247 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5245248 : term172 = term32.
Proof. exact (@lem5245247 term32). Qed.
Lemma lem5245249 : term267 = term32.
Proof. exact (TRANS (@lem5245245) (@lem5245248)). Qed.
Lemma lem5245250 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5245251 : term284 = term281.
Proof. exact (MK_COMB (@lem5245250) (@lem5245249)). Qed.
Lemma lem5245252 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem5245253 (e : real) : (term264 e) = (term285 e).
Proof. exact (MK_COMB (@lem5245251) (@lem5245252 e)). Qed.
Lemma lem5245254 (e : real) : (term263 e) = (term285 e).
Proof. exact (TRANS (@lem5245151 e) (@lem5245253 e)). Qed.
Lemma lem5245255 (e : real) : (term285 e) = term32.
Proof. exact (@lem1982719 e). Qed.
Lemma lem5245256 (e : real) : (term263 e) = term32.
Proof. exact (TRANS (@lem5245254 e) (@lem5245255 e)). Qed.
Lemma lem5245257 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245258 (e : real) : (term286 e) = term206.
Proof. exact (MK_COMB (@lem5245257) (@lem5245256 e)). Qed.
Lemma lem5245259 (l : real) (x : real) : (term287 l x) = (term288 l x).
Proof. exact (@lem1982753 l (term25 l) (term25 x) x). Qed.
Lemma lem5245260 (l : real) : (term289 l) = (term264 l).
Proof. exact (@lem1982715 term51 l). Qed.
Lemma lem5245262 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245263 : term91 = term101.
Proof. exact (@lem5245262 term85). Qed.
Lemma lem5245265 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5245266 : term51 = term84.
Proof. exact (@lem5245265 term85). Qed.
Lemma lem5245267 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245268 : term265 = term266.
Proof. exact (MK_COMB (@lem5245267) (@lem5245266)). Qed.
Lemma lem5245269 : term267 = term268.
Proof. exact (MK_COMB (@lem5245268) (@lem5245263)). Qed.
Lemma lem5245270 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5245272 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245273 : term232 = term238.
Proof. exact (@lem5245272 (NUMERAL 0) term85). Qed.
Lemma lem5245274 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245275 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245276 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245275 h1) (fun h1 : term238 = True => @lem5245274)). Qed.
Lemma lem5245277 : term238 = True.
Proof. exact (EQ_MP (@lem5245276) (@lem5245274)). Qed.
Lemma lem5245278 : term232 = True.
Proof. exact (TRANS (@lem5245273) (@lem5245277)). Qed.
Lemma lem5245279 : True = term232.
Proof. exact (SYM (@lem5245278)). Qed.
Lemma lem5245280 : term232.
Proof. exact (EQ_MP (@lem5245279) (@lem0)). Qed.
Lemma lem5245281 : term270.
Proof. exact (@lem5245270 (@lem5245280)). Qed.
Lemma lem5245283 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245284 : term232 = term238.
Proof. exact (@lem5245283 (NUMERAL 0) term85). Qed.
Lemma lem5245285 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245286 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245287 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245286 h1) (fun h1 : term238 = True => @lem5245285)). Qed.
Lemma lem5245288 : term238 = True.
Proof. exact (EQ_MP (@lem5245287) (@lem5245285)). Qed.
Lemma lem5245289 : term232 = True.
Proof. exact (TRANS (@lem5245284) (@lem5245288)). Qed.
Lemma lem5245290 : True = term232.
Proof. exact (SYM (@lem5245289)). Qed.
Lemma lem5245291 : term232.
Proof. exact (EQ_MP (@lem5245290) (@lem0)). Qed.
Lemma lem5245292 : term271.
Proof. exact (@lem5245281 (@lem5245291)). Qed.
Lemma lem5245294 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245295 : term232 = term238.
Proof. exact (@lem5245294 (NUMERAL 0) term85). Qed.
Lemma lem5245296 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245297 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245298 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245297 h1) (fun h1 : term238 = True => @lem5245296)). Qed.
Lemma lem5245299 : term238 = True.
Proof. exact (EQ_MP (@lem5245298) (@lem5245296)). Qed.
Lemma lem5245300 : term232 = True.
Proof. exact (TRANS (@lem5245295) (@lem5245299)). Qed.
Lemma lem5245301 : True = term232.
Proof. exact (SYM (@lem5245300)). Qed.
Lemma lem5245302 : term232.
Proof. exact (EQ_MP (@lem5245301) (@lem0)). Qed.
Lemma lem5245303 : term272.
Proof. exact (@lem5245292 (@lem5245302)). Qed.
Lemma lem5245305 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245306 : term94 = term95.
Proof. exact (@lem5245305 term85 term85). Qed.
Lemma lem5245307 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245308 : term97 = term85.
Proof. exact (EQ_MP (@lem5245307) (@lem940073)). Qed.
Lemma lem5245309 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245310 : term95 = term91.
Proof. exact (MK_COMB (@lem5245309) (@lem5245308)). Qed.
Lemma lem5245311 : term94 = term91.
Proof. exact (TRANS (@lem5245306) (@lem5245310)). Qed.
Lemma lem5245313 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5245314 : term275 = term276.
Proof. exact (@lem5245313 term85 term85). Qed.
Lemma lem5245315 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245316 : term97 = term85.
Proof. exact (EQ_MP (@lem5245315) (@lem940073)). Qed.
Lemma lem5245317 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245318 : term95 = term91.
Proof. exact (MK_COMB (@lem5245317) (@lem5245316)). Qed.
Lemma lem5245319 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5245320 : term276 = term51.
Proof. exact (MK_COMB (@lem5245319) (@lem5245318)). Qed.
Lemma lem5245321 : term275 = term51.
Proof. exact (TRANS (@lem5245314) (@lem5245320)). Qed.
Lemma lem5245322 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245323 : term277 = term265.
Proof. exact (MK_COMB (@lem5245322) (@lem5245321)). Qed.
Lemma lem5245324 : term278 = term267.
Proof. exact (MK_COMB (@lem5245323) (@lem5245311)). Qed.
Lemma lem5245326 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5245327 : term267 = term32.
Proof. exact (@lem5245326 term85). Qed.
Lemma lem5245328 : term278 = term32.
Proof. exact (TRANS (@lem5245324) (@lem5245327)). Qed.
Lemma lem5245329 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5245330 : term280 = term281.
Proof. exact (MK_COMB (@lem5245329) (@lem5245328)). Qed.
Lemma lem5245331 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5245332 : term282 = term243.
Proof. exact (MK_COMB (@lem5245330) (@lem5245331)). Qed.
Lemma lem5245334 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245335 : term243 = term32.
Proof. exact (@lem5245334 term85). Qed.
Lemma lem5245336 : term282 = term32.
Proof. exact (TRANS (@lem5245332) (@lem5245335)). Qed.
Lemma lem5245338 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245339 : term94 = term95.
Proof. exact (@lem5245338 term85 term85). Qed.
Lemma lem5245340 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245341 : term97 = term85.
Proof. exact (EQ_MP (@lem5245340) (@lem940073)). Qed.
Lemma lem5245342 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245343 : term95 = term91.
Proof. exact (MK_COMB (@lem5245342) (@lem5245341)). Qed.
Lemma lem5245344 : term94 = term91.
Proof. exact (TRANS (@lem5245339) (@lem5245343)). Qed.
Lemma lem5245345 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5245346 : term283 = term243.
Proof. exact (MK_COMB (@lem5245345) (@lem5245344)). Qed.
Lemma lem5245348 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245349 : term243 = term32.
Proof. exact (@lem5245348 term85). Qed.
Lemma lem5245350 : term283 = term32.
Proof. exact (TRANS (@lem5245346) (@lem5245349)). Qed.
Lemma lem5245351 : term32 = term283.
Proof. exact (SYM (@lem5245350)). Qed.
Lemma lem5245352 : term282 = term283.
Proof. exact (TRANS (@lem5245336) (@lem5245351)). Qed.
Lemma lem5245353 : term268 = term172.
Proof. exact (@lem5245303 (@lem5245352)). Qed.
Lemma lem5245354 : term267 = term172.
Proof. exact (TRANS (@lem5245269) (@lem5245353)). Qed.
Lemma lem5245356 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5245357 : term172 = term32.
Proof. exact (@lem5245356 term32). Qed.
Lemma lem5245358 : term267 = term32.
Proof. exact (TRANS (@lem5245354) (@lem5245357)). Qed.
Lemma lem5245359 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5245360 : term284 = term281.
Proof. exact (MK_COMB (@lem5245359) (@lem5245358)). Qed.
Lemma lem5245361 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5245362 (l : real) : (term264 l) = (term285 l).
Proof. exact (MK_COMB (@lem5245360) (@lem5245361 l)). Qed.
Lemma lem5245363 (l : real) : (term289 l) = (term285 l).
Proof. exact (TRANS (@lem5245260 l) (@lem5245362 l)). Qed.
Lemma lem5245364 (l : real) : (term285 l) = term32.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5245365 (l : real) : (term289 l) = term32.
Proof. exact (TRANS (@lem5245363 l) (@lem5245364 l)). Qed.
Lemma lem5245366 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245367 (l : real) : (term290 l) = term206.
Proof. exact (MK_COMB (@lem5245366) (@lem5245365 l)). Qed.
Lemma lem5245368 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1982713 term51 x). Qed.
Lemma lem5245370 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245371 : term91 = term101.
Proof. exact (@lem5245370 term85). Qed.
Lemma lem5245373 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5245374 : term51 = term84.
Proof. exact (@lem5245373 term85). Qed.
Lemma lem5245375 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245376 : term265 = term266.
Proof. exact (MK_COMB (@lem5245375) (@lem5245374)). Qed.
Lemma lem5245377 : term267 = term268.
Proof. exact (MK_COMB (@lem5245376) (@lem5245371)). Qed.
Lemma lem5245378 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5245380 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245381 : term232 = term238.
Proof. exact (@lem5245380 (NUMERAL 0) term85). Qed.
Lemma lem5245382 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245383 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245384 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245383 h1) (fun h1 : term238 = True => @lem5245382)). Qed.
Lemma lem5245385 : term238 = True.
Proof. exact (EQ_MP (@lem5245384) (@lem5245382)). Qed.
Lemma lem5245386 : term232 = True.
Proof. exact (TRANS (@lem5245381) (@lem5245385)). Qed.
Lemma lem5245387 : True = term232.
Proof. exact (SYM (@lem5245386)). Qed.
Lemma lem5245388 : term232.
Proof. exact (EQ_MP (@lem5245387) (@lem0)). Qed.
Lemma lem5245389 : term270.
Proof. exact (@lem5245378 (@lem5245388)). Qed.
Lemma lem5245391 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245392 : term232 = term238.
Proof. exact (@lem5245391 (NUMERAL 0) term85). Qed.
Lemma lem5245393 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245394 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245395 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245394 h1) (fun h1 : term238 = True => @lem5245393)). Qed.
Lemma lem5245396 : term238 = True.
Proof. exact (EQ_MP (@lem5245395) (@lem5245393)). Qed.
Lemma lem5245397 : term232 = True.
Proof. exact (TRANS (@lem5245392) (@lem5245396)). Qed.
Lemma lem5245398 : True = term232.
Proof. exact (SYM (@lem5245397)). Qed.
Lemma lem5245399 : term232.
Proof. exact (EQ_MP (@lem5245398) (@lem0)). Qed.
Lemma lem5245400 : term271.
Proof. exact (@lem5245389 (@lem5245399)). Qed.
Lemma lem5245402 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245403 : term232 = term238.
Proof. exact (@lem5245402 (NUMERAL 0) term85). Qed.
Lemma lem5245404 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245405 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245406 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245405 h1) (fun h1 : term238 = True => @lem5245404)). Qed.
Lemma lem5245407 : term238 = True.
Proof. exact (EQ_MP (@lem5245406) (@lem5245404)). Qed.
Lemma lem5245408 : term232 = True.
Proof. exact (TRANS (@lem5245403) (@lem5245407)). Qed.
Lemma lem5245409 : True = term232.
Proof. exact (SYM (@lem5245408)). Qed.
Lemma lem5245410 : term232.
Proof. exact (EQ_MP (@lem5245409) (@lem0)). Qed.
Lemma lem5245411 : term272.
Proof. exact (@lem5245400 (@lem5245410)). Qed.
Lemma lem5245413 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245414 : term94 = term95.
Proof. exact (@lem5245413 term85 term85). Qed.
Lemma lem5245415 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245416 : term97 = term85.
Proof. exact (EQ_MP (@lem5245415) (@lem940073)). Qed.
Lemma lem5245417 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245418 : term95 = term91.
Proof. exact (MK_COMB (@lem5245417) (@lem5245416)). Qed.
Lemma lem5245419 : term94 = term91.
Proof. exact (TRANS (@lem5245414) (@lem5245418)). Qed.
Lemma lem5245421 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5245422 : term275 = term276.
Proof. exact (@lem5245421 term85 term85). Qed.
Lemma lem5245423 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245424 : term97 = term85.
Proof. exact (EQ_MP (@lem5245423) (@lem940073)). Qed.
Lemma lem5245425 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245426 : term95 = term91.
Proof. exact (MK_COMB (@lem5245425) (@lem5245424)). Qed.
Lemma lem5245427 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5245428 : term276 = term51.
Proof. exact (MK_COMB (@lem5245427) (@lem5245426)). Qed.
Lemma lem5245429 : term275 = term51.
Proof. exact (TRANS (@lem5245422) (@lem5245428)). Qed.
Lemma lem5245430 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245431 : term277 = term265.
Proof. exact (MK_COMB (@lem5245430) (@lem5245429)). Qed.
Lemma lem5245432 : term278 = term267.
Proof. exact (MK_COMB (@lem5245431) (@lem5245419)). Qed.
Lemma lem5245434 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5245435 : term267 = term32.
Proof. exact (@lem5245434 term85). Qed.
Lemma lem5245436 : term278 = term32.
Proof. exact (TRANS (@lem5245432) (@lem5245435)). Qed.
Lemma lem5245437 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5245438 : term280 = term281.
Proof. exact (MK_COMB (@lem5245437) (@lem5245436)). Qed.
Lemma lem5245439 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5245440 : term282 = term243.
Proof. exact (MK_COMB (@lem5245438) (@lem5245439)). Qed.
Lemma lem5245442 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245443 : term243 = term32.
Proof. exact (@lem5245442 term85). Qed.
Lemma lem5245444 : term282 = term32.
Proof. exact (TRANS (@lem5245440) (@lem5245443)). Qed.
Lemma lem5245446 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245447 : term94 = term95.
Proof. exact (@lem5245446 term85 term85). Qed.
Lemma lem5245448 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245449 : term97 = term85.
Proof. exact (EQ_MP (@lem5245448) (@lem940073)). Qed.
Lemma lem5245450 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245451 : term95 = term91.
Proof. exact (MK_COMB (@lem5245450) (@lem5245449)). Qed.
Lemma lem5245452 : term94 = term91.
Proof. exact (TRANS (@lem5245447) (@lem5245451)). Qed.
Lemma lem5245453 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5245454 : term283 = term243.
Proof. exact (MK_COMB (@lem5245453) (@lem5245452)). Qed.
Lemma lem5245456 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245457 : term243 = term32.
Proof. exact (@lem5245456 term85). Qed.
Lemma lem5245458 : term283 = term32.
Proof. exact (TRANS (@lem5245454) (@lem5245457)). Qed.
Lemma lem5245459 : term32 = term283.
Proof. exact (SYM (@lem5245458)). Qed.
Lemma lem5245460 : term282 = term283.
Proof. exact (TRANS (@lem5245444) (@lem5245459)). Qed.
Lemma lem5245461 : term268 = term172.
Proof. exact (@lem5245411 (@lem5245460)). Qed.
Lemma lem5245462 : term267 = term172.
Proof. exact (TRANS (@lem5245377) (@lem5245461)). Qed.
Lemma lem5245464 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5245465 : term172 = term32.
Proof. exact (@lem5245464 term32). Qed.
Lemma lem5245466 : term267 = term32.
Proof. exact (TRANS (@lem5245462) (@lem5245465)). Qed.
Lemma lem5245467 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5245468 : term284 = term281.
Proof. exact (MK_COMB (@lem5245467) (@lem5245466)). Qed.
Lemma lem5245469 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5245470 (x : real) : (term264 x) = (term285 x).
Proof. exact (MK_COMB (@lem5245468) (@lem5245469 x)). Qed.
Lemma lem5245471 (x : real) : (term263 x) = (term285 x).
Proof. exact (TRANS (@lem5245368 x) (@lem5245470 x)). Qed.
Lemma lem5245472 (x : real) : (term285 x) = term32.
Proof. exact (@lem1982719 x). Qed.
Lemma lem5245473 (x : real) : (term263 x) = term32.
Proof. exact (TRANS (@lem5245471 x) (@lem5245472 x)). Qed.
Lemma lem5245474 (l : real) (x : real) : (term288 l x) = term291.
Proof. exact (MK_COMB (@lem5245367 l) (@lem5245473 x)). Qed.
Lemma lem5245475 (l : real) (x : real) : (term287 l x) = term291.
Proof. exact (TRANS (@lem5245259 l x) (@lem5245474 l x)). Qed.
Lemma lem5245476 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5245477 (l : real) (x : real) : (term287 l x) = term32.
Proof. exact (TRANS (@lem5245475 l x) (@lem5245476)). Qed.
Lemma lem5245478 (e : real) (l : real) (x : real) : (term262 e l x) = term291.
Proof. exact (MK_COMB (@lem5245258 e) (@lem5245477 l x)). Qed.
Lemma lem5245479 (e : real) (l : real) (x : real) : (term261 e l x) = term291.
Proof. exact (TRANS (@lem5245150 e l x) (@lem5245478 e l x)). Qed.
Lemma lem5245480 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5245481 (e : real) (l : real) (x : real) : (term261 e l x) = term32.
Proof. exact (TRANS (@lem5245479 e l x) (@lem5245480)). Qed.
Lemma lem5245482 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5245483 (e : real) (l : real) (x : real) : (term292 e l x) = term293.
Proof. exact (MK_COMB (@lem5245482) (@lem5245481 e l x)). Qed.
Lemma lem5245484 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5245485 (e : real) (l : real) (x : real) : (term260 e l x) = term294.
Proof. exact (MK_COMB (@lem5245483 e l x) (@lem5245484)). Qed.
Lemma lem5245486 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term294.
Proof. exact (EQ_MP (@lem5245485 e l x) (@lem5245149 e l x h1)). Qed.
Lemma lem5245488 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5245489 : term294 = term295.
Proof. exact (@lem5245488 term32 term32). Qed.
Lemma lem5245491 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245492 : term32 = term172.
Proof. exact (@lem5245491 (NUMERAL 0)). Qed.
Lemma lem5245494 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245495 : term32 = term172.
Proof. exact (@lem5245494 (NUMERAL 0)). Qed.
Lemma lem5245496 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5245497 : term233 = term234.
Proof. exact (MK_COMB (@lem5245496) (@lem5245495)). Qed.
Lemma lem5245498 : term295 = term296.
Proof. exact (MK_COMB (@lem5245497) (@lem5245492)). Qed.
Lemma lem5245499 : term297.
Proof. exact (@lem1980255 term32 term91 term32 term91). Qed.
Lemma lem5245501 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245502 : term232 = term238.
Proof. exact (@lem5245501 (NUMERAL 0) term85). Qed.
Lemma lem5245503 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245504 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245505 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245504 h1) (fun h1 : term238 = True => @lem5245503)). Qed.
Lemma lem5245506 : term238 = True.
Proof. exact (EQ_MP (@lem5245505) (@lem5245503)). Qed.
Lemma lem5245507 : term232 = True.
Proof. exact (TRANS (@lem5245502) (@lem5245506)). Qed.
Lemma lem5245508 : True = term232.
Proof. exact (SYM (@lem5245507)). Qed.
Lemma lem5245509 : term232.
Proof. exact (EQ_MP (@lem5245508) (@lem0)). Qed.
Lemma lem5245510 : term298.
Proof. exact (@lem5245499 (@lem5245509)). Qed.
Lemma lem5245512 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245513 : term232 = term238.
Proof. exact (@lem5245512 (NUMERAL 0) term85). Qed.
Lemma lem5245514 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245515 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245516 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245515 h1) (fun h1 : term238 = True => @lem5245514)). Qed.
Lemma lem5245517 : term238 = True.
Proof. exact (EQ_MP (@lem5245516) (@lem5245514)). Qed.
Lemma lem5245518 : term232 = True.
Proof. exact (TRANS (@lem5245513) (@lem5245517)). Qed.
Lemma lem5245519 : True = term232.
Proof. exact (SYM (@lem5245518)). Qed.
Lemma lem5245520 : term232.
Proof. exact (EQ_MP (@lem5245519) (@lem0)). Qed.
Lemma lem5245521 : term296 = term299.
Proof. exact (@lem5245510 (@lem5245520)). Qed.
Lemma lem5245523 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245524 : term243 = term32.
Proof. exact (@lem5245523 term85). Qed.
Lemma lem5245526 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245527 : term243 = term32.
Proof. exact (@lem5245526 term85). Qed.
Lemma lem5245528 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5245529 : term244 = term233.
Proof. exact (MK_COMB (@lem5245528) (@lem5245527)). Qed.
Lemma lem5245530 : term299 = term295.
Proof. exact (MK_COMB (@lem5245529) (@lem5245524)). Qed.
Lemma lem5245532 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245533 : term295 = term300.
Proof. exact (@lem5245532 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5245534 : term300 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5245535 : term295 = False.
Proof. exact (TRANS (@lem5245533) (@lem5245534)). Qed.
Lemma lem5245536 : term299 = False.
Proof. exact (TRANS (@lem5245530) (@lem5245535)). Qed.
Lemma lem5245537 : term296 = False.
Proof. exact (TRANS (@lem5245521) (@lem5245536)). Qed.
Lemma lem5245538 : term295 = False.
Proof. exact (TRANS (@lem5245498) (@lem5245537)). Qed.
Lemma lem5245539 : term294 = False.
Proof. exact (TRANS (@lem5245489) (@lem5245538)). Qed.
Lemma lem5245540 (e : real) (l : real) (x : real) (h1 : term144 e l x) : False.
Proof. exact (EQ_MP (@lem5245539) (@lem5245486 e l x h1)). Qed.
Lemma lem5245541 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term146 e l x.
Proof. exact (h1). Qed.
Lemma lem5245542 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term57 e l x.
Proof. exact (proj2 (@lem5245541 e l x h1)). Qed.
Lemma lem5245543 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term141 e l x.
Proof. exact (proj1 (@lem5245541 e l x h1)). Qed.
Lemma lem5245545 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term118 e l x.
Proof. exact (proj1 (@lem5245543 e l x h1)). Qed.
Lemma lem5245547 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5245548 : term231 = term232.
Proof. exact (@lem5245547 term32 term91). Qed.
Lemma lem5245550 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245551 : term91 = term101.
Proof. exact (@lem5245550 term85). Qed.
Lemma lem5245553 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245554 : term32 = term172.
Proof. exact (@lem5245553 (NUMERAL 0)). Qed.
Lemma lem5245555 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5245556 : term233 = term234.
Proof. exact (MK_COMB (@lem5245555) (@lem5245554)). Qed.
Lemma lem5245557 : term232 = term235.
Proof. exact (MK_COMB (@lem5245556) (@lem5245551)). Qed.
Lemma lem5245558 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5245560 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245561 : term232 = term238.
Proof. exact (@lem5245560 (NUMERAL 0) term85). Qed.
Lemma lem5245562 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245563 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245564 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245563 h1) (fun h1 : term238 = True => @lem5245562)). Qed.
Lemma lem5245565 : term238 = True.
Proof. exact (EQ_MP (@lem5245564) (@lem5245562)). Qed.
Lemma lem5245566 : term232 = True.
Proof. exact (TRANS (@lem5245561) (@lem5245565)). Qed.
Lemma lem5245567 : True = term232.
Proof. exact (SYM (@lem5245566)). Qed.
Lemma lem5245568 : term232.
Proof. exact (EQ_MP (@lem5245567) (@lem0)). Qed.
Lemma lem5245569 : term240.
Proof. exact (@lem5245558 (@lem5245568)). Qed.
Lemma lem5245571 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245572 : term232 = term238.
Proof. exact (@lem5245571 (NUMERAL 0) term85). Qed.
Lemma lem5245573 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245574 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245575 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245574 h1) (fun h1 : term238 = True => @lem5245573)). Qed.
Lemma lem5245576 : term238 = True.
Proof. exact (EQ_MP (@lem5245575) (@lem5245573)). Qed.
Lemma lem5245577 : term232 = True.
Proof. exact (TRANS (@lem5245572) (@lem5245576)). Qed.
Lemma lem5245578 : True = term232.
Proof. exact (SYM (@lem5245577)). Qed.
Lemma lem5245579 : term232.
Proof. exact (EQ_MP (@lem5245578) (@lem0)). Qed.
Lemma lem5245580 : term235 = term241.
Proof. exact (@lem5245569 (@lem5245579)). Qed.
Lemma lem5245582 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245583 : term94 = term95.
Proof. exact (@lem5245582 term85 term85). Qed.
Lemma lem5245584 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245585 : term97 = term85.
Proof. exact (EQ_MP (@lem5245584) (@lem940073)). Qed.
Lemma lem5245586 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245587 : term95 = term91.
Proof. exact (MK_COMB (@lem5245586) (@lem5245585)). Qed.
Lemma lem5245588 : term94 = term91.
Proof. exact (TRANS (@lem5245583) (@lem5245587)). Qed.
Lemma lem5245590 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245591 : term243 = term32.
Proof. exact (@lem5245590 term85). Qed.
Lemma lem5245592 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5245593 : term244 = term233.
Proof. exact (MK_COMB (@lem5245592) (@lem5245591)). Qed.
Lemma lem5245594 : term241 = term232.
Proof. exact (MK_COMB (@lem5245593) (@lem5245588)). Qed.
Lemma lem5245596 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245597 : term232 = term238.
Proof. exact (@lem5245596 (NUMERAL 0) term85). Qed.
Lemma lem5245598 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245599 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245600 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245599 h1) (fun h1 : term238 = True => @lem5245598)). Qed.
Lemma lem5245601 : term238 = True.
Proof. exact (EQ_MP (@lem5245600) (@lem5245598)). Qed.
Lemma lem5245602 : term232 = True.
Proof. exact (TRANS (@lem5245597) (@lem5245601)). Qed.
Lemma lem5245603 : term241 = True.
Proof. exact (TRANS (@lem5245594) (@lem5245602)). Qed.
Lemma lem5245604 : term235 = True.
Proof. exact (TRANS (@lem5245580) (@lem5245603)). Qed.
Lemma lem5245605 : term232 = True.
Proof. exact (TRANS (@lem5245557) (@lem5245604)). Qed.
Lemma lem5245606 : term231 = True.
Proof. exact (TRANS (@lem5245548) (@lem5245605)). Qed.
Lemma lem5245607 : True = term231.
Proof. exact (SYM (@lem5245606)). Qed.
Lemma lem5245608 : term231.
Proof. exact (EQ_MP (@lem5245607) (@lem0)). Qed.
Lemma lem5245609 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term301 e l x.
Proof. exact (conj (@lem5245608) (@lem5245545 e l x h1)). Qed.
Lemma lem5245611 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5245612 (e : real) (l : real) (x : real) : term302 e l x.
Proof. exact (@lem5245611 term91 (term107 e l x)). Qed.
Lemma lem5245613 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term303 e l x.
Proof. exact (@lem5245612 e l x (@lem5245609 e l x h1)). Qed.
Lemma lem5245614 (e : real) (l : real) (x : real) : (term304 e l x) = (term107 e l x).
Proof. exact (@lem1982733 (term107 e l x)). Qed.
Lemma lem5245615 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5245616 (e : real) (l : real) (x : real) : (term305 e l x) = (term117 e l x).
Proof. exact (MK_COMB (@lem5245615) (@lem5245614 e l x)). Qed.
Lemma lem5245617 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5245618 (e : real) (l : real) (x : real) : (term303 e l x) = (term118 e l x).
Proof. exact (MK_COMB (@lem5245616 e l x) (@lem5245617)). Qed.
Lemma lem5245619 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term118 e l x.
Proof. exact (EQ_MP (@lem5245618 e l x) (@lem5245613 e l x h1)). Qed.
Lemma lem5245621 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5245622 : term231 = term232.
Proof. exact (@lem5245621 term32 term91). Qed.
Lemma lem5245624 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245625 : term91 = term101.
Proof. exact (@lem5245624 term85). Qed.
Lemma lem5245627 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245628 : term32 = term172.
Proof. exact (@lem5245627 (NUMERAL 0)). Qed.
Lemma lem5245629 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5245630 : term233 = term234.
Proof. exact (MK_COMB (@lem5245629) (@lem5245628)). Qed.
Lemma lem5245631 : term232 = term235.
Proof. exact (MK_COMB (@lem5245630) (@lem5245625)). Qed.
Lemma lem5245632 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5245634 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245635 : term232 = term238.
Proof. exact (@lem5245634 (NUMERAL 0) term85). Qed.
Lemma lem5245636 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245637 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245638 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245637 h1) (fun h1 : term238 = True => @lem5245636)). Qed.
Lemma lem5245639 : term238 = True.
Proof. exact (EQ_MP (@lem5245638) (@lem5245636)). Qed.
Lemma lem5245640 : term232 = True.
Proof. exact (TRANS (@lem5245635) (@lem5245639)). Qed.
Lemma lem5245641 : True = term232.
Proof. exact (SYM (@lem5245640)). Qed.
Lemma lem5245642 : term232.
Proof. exact (EQ_MP (@lem5245641) (@lem0)). Qed.
Lemma lem5245643 : term240.
Proof. exact (@lem5245632 (@lem5245642)). Qed.
Lemma lem5245645 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245646 : term232 = term238.
Proof. exact (@lem5245645 (NUMERAL 0) term85). Qed.
Lemma lem5245647 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245648 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245649 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245648 h1) (fun h1 : term238 = True => @lem5245647)). Qed.
Lemma lem5245650 : term238 = True.
Proof. exact (EQ_MP (@lem5245649) (@lem5245647)). Qed.
Lemma lem5245651 : term232 = True.
Proof. exact (TRANS (@lem5245646) (@lem5245650)). Qed.
Lemma lem5245652 : True = term232.
Proof. exact (SYM (@lem5245651)). Qed.
Lemma lem5245653 : term232.
Proof. exact (EQ_MP (@lem5245652) (@lem0)). Qed.
Lemma lem5245654 : term235 = term241.
Proof. exact (@lem5245643 (@lem5245653)). Qed.
Lemma lem5245656 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245657 : term94 = term95.
Proof. exact (@lem5245656 term85 term85). Qed.
Lemma lem5245658 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245659 : term97 = term85.
Proof. exact (EQ_MP (@lem5245658) (@lem940073)). Qed.
Lemma lem5245660 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245661 : term95 = term91.
Proof. exact (MK_COMB (@lem5245660) (@lem5245659)). Qed.
Lemma lem5245662 : term94 = term91.
Proof. exact (TRANS (@lem5245657) (@lem5245661)). Qed.
Lemma lem5245664 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245665 : term243 = term32.
Proof. exact (@lem5245664 term85). Qed.
Lemma lem5245666 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5245667 : term244 = term233.
Proof. exact (MK_COMB (@lem5245666) (@lem5245665)). Qed.
Lemma lem5245668 : term241 = term232.
Proof. exact (MK_COMB (@lem5245667) (@lem5245662)). Qed.
Lemma lem5245670 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245671 : term232 = term238.
Proof. exact (@lem5245670 (NUMERAL 0) term85). Qed.
Lemma lem5245672 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245673 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245674 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245673 h1) (fun h1 : term238 = True => @lem5245672)). Qed.
Lemma lem5245675 : term238 = True.
Proof. exact (EQ_MP (@lem5245674) (@lem5245672)). Qed.
Lemma lem5245676 : term232 = True.
Proof. exact (TRANS (@lem5245671) (@lem5245675)). Qed.
Lemma lem5245677 : term241 = True.
Proof. exact (TRANS (@lem5245668) (@lem5245676)). Qed.
Lemma lem5245678 : term235 = True.
Proof. exact (TRANS (@lem5245654) (@lem5245677)). Qed.
Lemma lem5245679 : term232 = True.
Proof. exact (TRANS (@lem5245631) (@lem5245678)). Qed.
Lemma lem5245680 : term231 = True.
Proof. exact (TRANS (@lem5245622) (@lem5245679)). Qed.
Lemma lem5245681 : True = term231.
Proof. exact (SYM (@lem5245680)). Qed.
Lemma lem5245682 : term231.
Proof. exact (EQ_MP (@lem5245681) (@lem0)). Qed.
Lemma lem5245683 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term306 e l x.
Proof. exact (conj (@lem5245682) (@lem5245542 e l x h1)). Qed.
Lemma lem5245685 (x : real) (y : real) : term252 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5245686 (e : real) (l : real) (x : real) : term307 e l x.
Proof. exact (@lem5245685 term91 (term54 e l x)). Qed.
Lemma lem5245687 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term308 e l x.
Proof. exact (@lem5245686 e l x (@lem5245683 e l x h1)). Qed.
Lemma lem5245688 (e : real) (l : real) (x : real) : (term309 e l x) = (term54 e l x).
Proof. exact (@lem1982733 (term54 e l x)). Qed.
Lemma lem5245689 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5245690 (e : real) (l : real) (x : real) : (term310 e l x) = (term56 e l x).
Proof. exact (MK_COMB (@lem5245689) (@lem5245688 e l x)). Qed.
Lemma lem5245691 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5245692 (e : real) (l : real) (x : real) : (term308 e l x) = (term57 e l x).
Proof. exact (MK_COMB (@lem5245690 e l x) (@lem5245691)). Qed.
Lemma lem5245693 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term57 e l x.
Proof. exact (EQ_MP (@lem5245692 e l x) (@lem5245687 e l x h1)). Qed.
Lemma lem5245694 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term311 e l x.
Proof. exact (conj (@lem5245693 e l x h1) (@lem5245619 e l x h1)). Qed.
Lemma lem5245696 (x : real) (y : real) : term258 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5245697 (e : real) (l : real) (x : real) : term312 e l x.
Proof. exact (@lem5245696 (term54 e l x) (term107 e l x)). Qed.
Lemma lem5245698 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term313 e l x.
Proof. exact (@lem5245697 e l x (@lem5245694 e l x h1)). Qed.
Lemma lem5245699 (e : real) (l : real) (x : real) : (term314 e l x) = (term315 e l x).
Proof. exact (@lem1982753 (term25 e) e (term24 l x) (term23 l x)). Qed.
Lemma lem5245700 (e : real) : (term263 e) = (term264 e).
Proof. exact (@lem1982713 term51 e). Qed.
Lemma lem5245702 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245703 : term91 = term101.
Proof. exact (@lem5245702 term85). Qed.
Lemma lem5245705 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5245706 : term51 = term84.
Proof. exact (@lem5245705 term85). Qed.
Lemma lem5245707 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245708 : term265 = term266.
Proof. exact (MK_COMB (@lem5245707) (@lem5245706)). Qed.
Lemma lem5245709 : term267 = term268.
Proof. exact (MK_COMB (@lem5245708) (@lem5245703)). Qed.
Lemma lem5245710 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5245712 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245713 : term232 = term238.
Proof. exact (@lem5245712 (NUMERAL 0) term85). Qed.
Lemma lem5245714 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245715 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245716 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245715 h1) (fun h1 : term238 = True => @lem5245714)). Qed.
Lemma lem5245717 : term238 = True.
Proof. exact (EQ_MP (@lem5245716) (@lem5245714)). Qed.
Lemma lem5245718 : term232 = True.
Proof. exact (TRANS (@lem5245713) (@lem5245717)). Qed.
Lemma lem5245719 : True = term232.
Proof. exact (SYM (@lem5245718)). Qed.
Lemma lem5245720 : term232.
Proof. exact (EQ_MP (@lem5245719) (@lem0)). Qed.
Lemma lem5245721 : term270.
Proof. exact (@lem5245710 (@lem5245720)). Qed.
Lemma lem5245723 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245724 : term232 = term238.
Proof. exact (@lem5245723 (NUMERAL 0) term85). Qed.
Lemma lem5245725 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245726 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245727 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245726 h1) (fun h1 : term238 = True => @lem5245725)). Qed.
Lemma lem5245728 : term238 = True.
Proof. exact (EQ_MP (@lem5245727) (@lem5245725)). Qed.
Lemma lem5245729 : term232 = True.
Proof. exact (TRANS (@lem5245724) (@lem5245728)). Qed.
Lemma lem5245730 : True = term232.
Proof. exact (SYM (@lem5245729)). Qed.
Lemma lem5245731 : term232.
Proof. exact (EQ_MP (@lem5245730) (@lem0)). Qed.
Lemma lem5245732 : term271.
Proof. exact (@lem5245721 (@lem5245731)). Qed.
Lemma lem5245734 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245735 : term232 = term238.
Proof. exact (@lem5245734 (NUMERAL 0) term85). Qed.
Lemma lem5245736 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245737 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245738 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245737 h1) (fun h1 : term238 = True => @lem5245736)). Qed.
Lemma lem5245739 : term238 = True.
Proof. exact (EQ_MP (@lem5245738) (@lem5245736)). Qed.
Lemma lem5245740 : term232 = True.
Proof. exact (TRANS (@lem5245735) (@lem5245739)). Qed.
Lemma lem5245741 : True = term232.
Proof. exact (SYM (@lem5245740)). Qed.
Lemma lem5245742 : term232.
Proof. exact (EQ_MP (@lem5245741) (@lem0)). Qed.
Lemma lem5245743 : term272.
Proof. exact (@lem5245732 (@lem5245742)). Qed.
Lemma lem5245745 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245746 : term94 = term95.
Proof. exact (@lem5245745 term85 term85). Qed.
Lemma lem5245747 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245748 : term97 = term85.
Proof. exact (EQ_MP (@lem5245747) (@lem940073)). Qed.
Lemma lem5245749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245750 : term95 = term91.
Proof. exact (MK_COMB (@lem5245749) (@lem5245748)). Qed.
Lemma lem5245751 : term94 = term91.
Proof. exact (TRANS (@lem5245746) (@lem5245750)). Qed.
Lemma lem5245753 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5245754 : term275 = term276.
Proof. exact (@lem5245753 term85 term85). Qed.
Lemma lem5245755 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245756 : term97 = term85.
Proof. exact (EQ_MP (@lem5245755) (@lem940073)). Qed.
Lemma lem5245757 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245758 : term95 = term91.
Proof. exact (MK_COMB (@lem5245757) (@lem5245756)). Qed.
Lemma lem5245759 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5245760 : term276 = term51.
Proof. exact (MK_COMB (@lem5245759) (@lem5245758)). Qed.
Lemma lem5245761 : term275 = term51.
Proof. exact (TRANS (@lem5245754) (@lem5245760)). Qed.
Lemma lem5245762 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245763 : term277 = term265.
Proof. exact (MK_COMB (@lem5245762) (@lem5245761)). Qed.
Lemma lem5245764 : term278 = term267.
Proof. exact (MK_COMB (@lem5245763) (@lem5245751)). Qed.
Lemma lem5245766 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5245767 : term267 = term32.
Proof. exact (@lem5245766 term85). Qed.
Lemma lem5245768 : term278 = term32.
Proof. exact (TRANS (@lem5245764) (@lem5245767)). Qed.
Lemma lem5245769 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5245770 : term280 = term281.
Proof. exact (MK_COMB (@lem5245769) (@lem5245768)). Qed.
Lemma lem5245771 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5245772 : term282 = term243.
Proof. exact (MK_COMB (@lem5245770) (@lem5245771)). Qed.
Lemma lem5245774 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245775 : term243 = term32.
Proof. exact (@lem5245774 term85). Qed.
Lemma lem5245776 : term282 = term32.
Proof. exact (TRANS (@lem5245772) (@lem5245775)). Qed.
Lemma lem5245778 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245779 : term94 = term95.
Proof. exact (@lem5245778 term85 term85). Qed.
Lemma lem5245780 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245781 : term97 = term85.
Proof. exact (EQ_MP (@lem5245780) (@lem940073)). Qed.
Lemma lem5245782 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245783 : term95 = term91.
Proof. exact (MK_COMB (@lem5245782) (@lem5245781)). Qed.
Lemma lem5245784 : term94 = term91.
Proof. exact (TRANS (@lem5245779) (@lem5245783)). Qed.
Lemma lem5245785 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5245786 : term283 = term243.
Proof. exact (MK_COMB (@lem5245785) (@lem5245784)). Qed.
Lemma lem5245788 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245789 : term243 = term32.
Proof. exact (@lem5245788 term85). Qed.
Lemma lem5245790 : term283 = term32.
Proof. exact (TRANS (@lem5245786) (@lem5245789)). Qed.
Lemma lem5245791 : term32 = term283.
Proof. exact (SYM (@lem5245790)). Qed.
Lemma lem5245792 : term282 = term283.
Proof. exact (TRANS (@lem5245776) (@lem5245791)). Qed.
Lemma lem5245793 : term268 = term172.
Proof. exact (@lem5245743 (@lem5245792)). Qed.
Lemma lem5245794 : term267 = term172.
Proof. exact (TRANS (@lem5245709) (@lem5245793)). Qed.
Lemma lem5245796 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5245797 : term172 = term32.
Proof. exact (@lem5245796 term32). Qed.
Lemma lem5245798 : term267 = term32.
Proof. exact (TRANS (@lem5245794) (@lem5245797)). Qed.
Lemma lem5245799 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5245800 : term284 = term281.
Proof. exact (MK_COMB (@lem5245799) (@lem5245798)). Qed.
Lemma lem5245801 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem5245802 (e : real) : (term264 e) = (term285 e).
Proof. exact (MK_COMB (@lem5245800) (@lem5245801 e)). Qed.
Lemma lem5245803 (e : real) : (term263 e) = (term285 e).
Proof. exact (TRANS (@lem5245700 e) (@lem5245802 e)). Qed.
Lemma lem5245804 (e : real) : (term285 e) = term32.
Proof. exact (@lem1982719 e). Qed.
Lemma lem5245805 (e : real) : (term263 e) = term32.
Proof. exact (TRANS (@lem5245803 e) (@lem5245804 e)). Qed.
Lemma lem5245806 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245807 (e : real) : (term286 e) = term206.
Proof. exact (MK_COMB (@lem5245806) (@lem5245805 e)). Qed.
Lemma lem5245808 (l : real) (x : real) : (term316 l x) = (term317 l x).
Proof. exact (@lem1982753 (term25 l) l x (term25 x)). Qed.
Lemma lem5245809 (l : real) : (term263 l) = (term264 l).
Proof. exact (@lem1982713 term51 l). Qed.
Lemma lem5245811 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245812 : term91 = term101.
Proof. exact (@lem5245811 term85). Qed.
Lemma lem5245814 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5245815 : term51 = term84.
Proof. exact (@lem5245814 term85). Qed.
Lemma lem5245816 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245817 : term265 = term266.
Proof. exact (MK_COMB (@lem5245816) (@lem5245815)). Qed.
Lemma lem5245818 : term267 = term268.
Proof. exact (MK_COMB (@lem5245817) (@lem5245812)). Qed.
Lemma lem5245819 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5245821 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245822 : term232 = term238.
Proof. exact (@lem5245821 (NUMERAL 0) term85). Qed.
Lemma lem5245823 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245824 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245825 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245824 h1) (fun h1 : term238 = True => @lem5245823)). Qed.
Lemma lem5245826 : term238 = True.
Proof. exact (EQ_MP (@lem5245825) (@lem5245823)). Qed.
Lemma lem5245827 : term232 = True.
Proof. exact (TRANS (@lem5245822) (@lem5245826)). Qed.
Lemma lem5245828 : True = term232.
Proof. exact (SYM (@lem5245827)). Qed.
Lemma lem5245829 : term232.
Proof. exact (EQ_MP (@lem5245828) (@lem0)). Qed.
Lemma lem5245830 : term270.
Proof. exact (@lem5245819 (@lem5245829)). Qed.
Lemma lem5245832 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245833 : term232 = term238.
Proof. exact (@lem5245832 (NUMERAL 0) term85). Qed.
Lemma lem5245834 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245835 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245836 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245835 h1) (fun h1 : term238 = True => @lem5245834)). Qed.
Lemma lem5245837 : term238 = True.
Proof. exact (EQ_MP (@lem5245836) (@lem5245834)). Qed.
Lemma lem5245838 : term232 = True.
Proof. exact (TRANS (@lem5245833) (@lem5245837)). Qed.
Lemma lem5245839 : True = term232.
Proof. exact (SYM (@lem5245838)). Qed.
Lemma lem5245840 : term232.
Proof. exact (EQ_MP (@lem5245839) (@lem0)). Qed.
Lemma lem5245841 : term271.
Proof. exact (@lem5245830 (@lem5245840)). Qed.
Lemma lem5245843 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245844 : term232 = term238.
Proof. exact (@lem5245843 (NUMERAL 0) term85). Qed.
Lemma lem5245845 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245846 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245847 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245846 h1) (fun h1 : term238 = True => @lem5245845)). Qed.
Lemma lem5245848 : term238 = True.
Proof. exact (EQ_MP (@lem5245847) (@lem5245845)). Qed.
Lemma lem5245849 : term232 = True.
Proof. exact (TRANS (@lem5245844) (@lem5245848)). Qed.
Lemma lem5245850 : True = term232.
Proof. exact (SYM (@lem5245849)). Qed.
Lemma lem5245851 : term232.
Proof. exact (EQ_MP (@lem5245850) (@lem0)). Qed.
Lemma lem5245852 : term272.
Proof. exact (@lem5245841 (@lem5245851)). Qed.
Lemma lem5245854 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245855 : term94 = term95.
Proof. exact (@lem5245854 term85 term85). Qed.
Lemma lem5245856 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245857 : term97 = term85.
Proof. exact (EQ_MP (@lem5245856) (@lem940073)). Qed.
Lemma lem5245858 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245859 : term95 = term91.
Proof. exact (MK_COMB (@lem5245858) (@lem5245857)). Qed.
Lemma lem5245860 : term94 = term91.
Proof. exact (TRANS (@lem5245855) (@lem5245859)). Qed.
Lemma lem5245862 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5245863 : term275 = term276.
Proof. exact (@lem5245862 term85 term85). Qed.
Lemma lem5245864 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245865 : term97 = term85.
Proof. exact (EQ_MP (@lem5245864) (@lem940073)). Qed.
Lemma lem5245866 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245867 : term95 = term91.
Proof. exact (MK_COMB (@lem5245866) (@lem5245865)). Qed.
Lemma lem5245868 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5245869 : term276 = term51.
Proof. exact (MK_COMB (@lem5245868) (@lem5245867)). Qed.
Lemma lem5245870 : term275 = term51.
Proof. exact (TRANS (@lem5245863) (@lem5245869)). Qed.
Lemma lem5245871 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245872 : term277 = term265.
Proof. exact (MK_COMB (@lem5245871) (@lem5245870)). Qed.
Lemma lem5245873 : term278 = term267.
Proof. exact (MK_COMB (@lem5245872) (@lem5245860)). Qed.
Lemma lem5245875 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5245876 : term267 = term32.
Proof. exact (@lem5245875 term85). Qed.
Lemma lem5245877 : term278 = term32.
Proof. exact (TRANS (@lem5245873) (@lem5245876)). Qed.
Lemma lem5245878 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5245879 : term280 = term281.
Proof. exact (MK_COMB (@lem5245878) (@lem5245877)). Qed.
Lemma lem5245880 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5245881 : term282 = term243.
Proof. exact (MK_COMB (@lem5245879) (@lem5245880)). Qed.
Lemma lem5245883 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245884 : term243 = term32.
Proof. exact (@lem5245883 term85). Qed.
Lemma lem5245885 : term282 = term32.
Proof. exact (TRANS (@lem5245881) (@lem5245884)). Qed.
Lemma lem5245887 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245888 : term94 = term95.
Proof. exact (@lem5245887 term85 term85). Qed.
Lemma lem5245889 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245890 : term97 = term85.
Proof. exact (EQ_MP (@lem5245889) (@lem940073)). Qed.
Lemma lem5245891 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245892 : term95 = term91.
Proof. exact (MK_COMB (@lem5245891) (@lem5245890)). Qed.
Lemma lem5245893 : term94 = term91.
Proof. exact (TRANS (@lem5245888) (@lem5245892)). Qed.
Lemma lem5245894 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5245895 : term283 = term243.
Proof. exact (MK_COMB (@lem5245894) (@lem5245893)). Qed.
Lemma lem5245897 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245898 : term243 = term32.
Proof. exact (@lem5245897 term85). Qed.
Lemma lem5245899 : term283 = term32.
Proof. exact (TRANS (@lem5245895) (@lem5245898)). Qed.
Lemma lem5245900 : term32 = term283.
Proof. exact (SYM (@lem5245899)). Qed.
Lemma lem5245901 : term282 = term283.
Proof. exact (TRANS (@lem5245885) (@lem5245900)). Qed.
Lemma lem5245902 : term268 = term172.
Proof. exact (@lem5245852 (@lem5245901)). Qed.
Lemma lem5245903 : term267 = term172.
Proof. exact (TRANS (@lem5245818) (@lem5245902)). Qed.
Lemma lem5245905 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5245906 : term172 = term32.
Proof. exact (@lem5245905 term32). Qed.
Lemma lem5245907 : term267 = term32.
Proof. exact (TRANS (@lem5245903) (@lem5245906)). Qed.
Lemma lem5245908 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5245909 : term284 = term281.
Proof. exact (MK_COMB (@lem5245908) (@lem5245907)). Qed.
Lemma lem5245910 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5245911 (l : real) : (term264 l) = (term285 l).
Proof. exact (MK_COMB (@lem5245909) (@lem5245910 l)). Qed.
Lemma lem5245912 (l : real) : (term263 l) = (term285 l).
Proof. exact (TRANS (@lem5245809 l) (@lem5245911 l)). Qed.
Lemma lem5245913 (l : real) : (term285 l) = term32.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5245914 (l : real) : (term263 l) = term32.
Proof. exact (TRANS (@lem5245912 l) (@lem5245913 l)). Qed.
Lemma lem5245915 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245916 (l : real) : (term286 l) = term206.
Proof. exact (MK_COMB (@lem5245915) (@lem5245914 l)). Qed.
Lemma lem5245917 (x : real) : (term289 x) = (term264 x).
Proof. exact (@lem1982715 term51 x). Qed.
Lemma lem5245919 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5245920 : term91 = term101.
Proof. exact (@lem5245919 term85). Qed.
Lemma lem5245922 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5245923 : term51 = term84.
Proof. exact (@lem5245922 term85). Qed.
Lemma lem5245924 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245925 : term265 = term266.
Proof. exact (MK_COMB (@lem5245924) (@lem5245923)). Qed.
Lemma lem5245926 : term267 = term268.
Proof. exact (MK_COMB (@lem5245925) (@lem5245920)). Qed.
Lemma lem5245927 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5245929 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245930 : term232 = term238.
Proof. exact (@lem5245929 (NUMERAL 0) term85). Qed.
Lemma lem5245931 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245932 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245933 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245932 h1) (fun h1 : term238 = True => @lem5245931)). Qed.
Lemma lem5245934 : term238 = True.
Proof. exact (EQ_MP (@lem5245933) (@lem5245931)). Qed.
Lemma lem5245935 : term232 = True.
Proof. exact (TRANS (@lem5245930) (@lem5245934)). Qed.
Lemma lem5245936 : True = term232.
Proof. exact (SYM (@lem5245935)). Qed.
Lemma lem5245937 : term232.
Proof. exact (EQ_MP (@lem5245936) (@lem0)). Qed.
Lemma lem5245938 : term270.
Proof. exact (@lem5245927 (@lem5245937)). Qed.
Lemma lem5245940 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245941 : term232 = term238.
Proof. exact (@lem5245940 (NUMERAL 0) term85). Qed.
Lemma lem5245942 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245943 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245944 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245943 h1) (fun h1 : term238 = True => @lem5245942)). Qed.
Lemma lem5245945 : term238 = True.
Proof. exact (EQ_MP (@lem5245944) (@lem5245942)). Qed.
Lemma lem5245946 : term232 = True.
Proof. exact (TRANS (@lem5245941) (@lem5245945)). Qed.
Lemma lem5245947 : True = term232.
Proof. exact (SYM (@lem5245946)). Qed.
Lemma lem5245948 : term232.
Proof. exact (EQ_MP (@lem5245947) (@lem0)). Qed.
Lemma lem5245949 : term271.
Proof. exact (@lem5245938 (@lem5245948)). Qed.
Lemma lem5245951 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5245952 : term232 = term238.
Proof. exact (@lem5245951 (NUMERAL 0) term85). Qed.
Lemma lem5245953 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5245954 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5245955 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5245954 h1) (fun h1 : term238 = True => @lem5245953)). Qed.
Lemma lem5245956 : term238 = True.
Proof. exact (EQ_MP (@lem5245955) (@lem5245953)). Qed.
Lemma lem5245957 : term232 = True.
Proof. exact (TRANS (@lem5245952) (@lem5245956)). Qed.
Lemma lem5245958 : True = term232.
Proof. exact (SYM (@lem5245957)). Qed.
Lemma lem5245959 : term232.
Proof. exact (EQ_MP (@lem5245958) (@lem0)). Qed.
Lemma lem5245960 : term272.
Proof. exact (@lem5245949 (@lem5245959)). Qed.
Lemma lem5245962 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245963 : term94 = term95.
Proof. exact (@lem5245962 term85 term85). Qed.
Lemma lem5245964 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245965 : term97 = term85.
Proof. exact (EQ_MP (@lem5245964) (@lem940073)). Qed.
Lemma lem5245966 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245967 : term95 = term91.
Proof. exact (MK_COMB (@lem5245966) (@lem5245965)). Qed.
Lemma lem5245968 : term94 = term91.
Proof. exact (TRANS (@lem5245963) (@lem5245967)). Qed.
Lemma lem5245970 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5245971 : term275 = term276.
Proof. exact (@lem5245970 term85 term85). Qed.
Lemma lem5245972 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245973 : term97 = term85.
Proof. exact (EQ_MP (@lem5245972) (@lem940073)). Qed.
Lemma lem5245974 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5245975 : term95 = term91.
Proof. exact (MK_COMB (@lem5245974) (@lem5245973)). Qed.
Lemma lem5245976 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5245977 : term276 = term51.
Proof. exact (MK_COMB (@lem5245976) (@lem5245975)). Qed.
Lemma lem5245978 : term275 = term51.
Proof. exact (TRANS (@lem5245971) (@lem5245977)). Qed.
Lemma lem5245979 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5245980 : term277 = term265.
Proof. exact (MK_COMB (@lem5245979) (@lem5245978)). Qed.
Lemma lem5245981 : term278 = term267.
Proof. exact (MK_COMB (@lem5245980) (@lem5245968)). Qed.
Lemma lem5245983 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5245984 : term267 = term32.
Proof. exact (@lem5245983 term85). Qed.
Lemma lem5245985 : term278 = term32.
Proof. exact (TRANS (@lem5245981) (@lem5245984)). Qed.
Lemma lem5245986 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5245987 : term280 = term281.
Proof. exact (MK_COMB (@lem5245986) (@lem5245985)). Qed.
Lemma lem5245988 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5245989 : term282 = term243.
Proof. exact (MK_COMB (@lem5245987) (@lem5245988)). Qed.
Lemma lem5245991 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5245992 : term243 = term32.
Proof. exact (@lem5245991 term85). Qed.
Lemma lem5245993 : term282 = term32.
Proof. exact (TRANS (@lem5245989) (@lem5245992)). Qed.
Lemma lem5245995 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5245996 : term94 = term95.
Proof. exact (@lem5245995 term85 term85). Qed.
Lemma lem5245997 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5245998 : term97 = term85.
Proof. exact (EQ_MP (@lem5245997) (@lem940073)). Qed.
Lemma lem5245999 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246000 : term95 = term91.
Proof. exact (MK_COMB (@lem5245999) (@lem5245998)). Qed.
Lemma lem5246001 : term94 = term91.
Proof. exact (TRANS (@lem5245996) (@lem5246000)). Qed.
Lemma lem5246002 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5246003 : term283 = term243.
Proof. exact (MK_COMB (@lem5246002) (@lem5246001)). Qed.
Lemma lem5246005 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246006 : term243 = term32.
Proof. exact (@lem5246005 term85). Qed.
Lemma lem5246007 : term283 = term32.
Proof. exact (TRANS (@lem5246003) (@lem5246006)). Qed.
Lemma lem5246008 : term32 = term283.
Proof. exact (SYM (@lem5246007)). Qed.
Lemma lem5246009 : term282 = term283.
Proof. exact (TRANS (@lem5245993) (@lem5246008)). Qed.
Lemma lem5246010 : term268 = term172.
Proof. exact (@lem5245960 (@lem5246009)). Qed.
Lemma lem5246011 : term267 = term172.
Proof. exact (TRANS (@lem5245926) (@lem5246010)). Qed.
Lemma lem5246013 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5246014 : term172 = term32.
Proof. exact (@lem5246013 term32). Qed.
Lemma lem5246015 : term267 = term32.
Proof. exact (TRANS (@lem5246011) (@lem5246014)). Qed.
Lemma lem5246016 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5246017 : term284 = term281.
Proof. exact (MK_COMB (@lem5246016) (@lem5246015)). Qed.
Lemma lem5246018 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5246019 (x : real) : (term264 x) = (term285 x).
Proof. exact (MK_COMB (@lem5246017) (@lem5246018 x)). Qed.
Lemma lem5246020 (x : real) : (term289 x) = (term285 x).
Proof. exact (TRANS (@lem5245917 x) (@lem5246019 x)). Qed.
Lemma lem5246021 (x : real) : (term285 x) = term32.
Proof. exact (@lem1982719 x). Qed.
Lemma lem5246022 (x : real) : (term289 x) = term32.
Proof. exact (TRANS (@lem5246020 x) (@lem5246021 x)). Qed.
Lemma lem5246023 (l : real) (x : real) : (term317 l x) = term291.
Proof. exact (MK_COMB (@lem5245916 l) (@lem5246022 x)). Qed.
Lemma lem5246024 (l : real) (x : real) : (term316 l x) = term291.
Proof. exact (TRANS (@lem5245808 l x) (@lem5246023 l x)). Qed.
Lemma lem5246025 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5246026 (l : real) (x : real) : (term316 l x) = term32.
Proof. exact (TRANS (@lem5246024 l x) (@lem5246025)). Qed.
Lemma lem5246027 (e : real) (l : real) (x : real) : (term315 e l x) = term291.
Proof. exact (MK_COMB (@lem5245807 e) (@lem5246026 l x)). Qed.
Lemma lem5246028 (e : real) (l : real) (x : real) : (term314 e l x) = term291.
Proof. exact (TRANS (@lem5245699 e l x) (@lem5246027 e l x)). Qed.
Lemma lem5246029 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5246030 (e : real) (l : real) (x : real) : (term314 e l x) = term32.
Proof. exact (TRANS (@lem5246028 e l x) (@lem5246029)). Qed.
Lemma lem5246031 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5246032 (e : real) (l : real) (x : real) : (term318 e l x) = term293.
Proof. exact (MK_COMB (@lem5246031) (@lem5246030 e l x)). Qed.
Lemma lem5246033 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5246034 (e : real) (l : real) (x : real) : (term313 e l x) = term294.
Proof. exact (MK_COMB (@lem5246032 e l x) (@lem5246033)). Qed.
Lemma lem5246035 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term294.
Proof. exact (EQ_MP (@lem5246034 e l x) (@lem5245698 e l x h1)). Qed.
Lemma lem5246037 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5246038 : term294 = term295.
Proof. exact (@lem5246037 term32 term32). Qed.
Lemma lem5246040 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246041 : term32 = term172.
Proof. exact (@lem5246040 (NUMERAL 0)). Qed.
Lemma lem5246043 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246044 : term32 = term172.
Proof. exact (@lem5246043 (NUMERAL 0)). Qed.
Lemma lem5246045 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5246046 : term233 = term234.
Proof. exact (MK_COMB (@lem5246045) (@lem5246044)). Qed.
Lemma lem5246047 : term295 = term296.
Proof. exact (MK_COMB (@lem5246046) (@lem5246041)). Qed.
Lemma lem5246048 : term297.
Proof. exact (@lem1980255 term32 term91 term32 term91). Qed.
Lemma lem5246050 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246051 : term232 = term238.
Proof. exact (@lem5246050 (NUMERAL 0) term85). Qed.
Lemma lem5246052 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246053 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246054 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246053 h1) (fun h1 : term238 = True => @lem5246052)). Qed.
Lemma lem5246055 : term238 = True.
Proof. exact (EQ_MP (@lem5246054) (@lem5246052)). Qed.
Lemma lem5246056 : term232 = True.
Proof. exact (TRANS (@lem5246051) (@lem5246055)). Qed.
Lemma lem5246057 : True = term232.
Proof. exact (SYM (@lem5246056)). Qed.
Lemma lem5246058 : term232.
Proof. exact (EQ_MP (@lem5246057) (@lem0)). Qed.
Lemma lem5246059 : term298.
Proof. exact (@lem5246048 (@lem5246058)). Qed.
Lemma lem5246061 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246062 : term232 = term238.
Proof. exact (@lem5246061 (NUMERAL 0) term85). Qed.
Lemma lem5246063 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246064 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246065 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246064 h1) (fun h1 : term238 = True => @lem5246063)). Qed.
Lemma lem5246066 : term238 = True.
Proof. exact (EQ_MP (@lem5246065) (@lem5246063)). Qed.
Lemma lem5246067 : term232 = True.
Proof. exact (TRANS (@lem5246062) (@lem5246066)). Qed.
Lemma lem5246068 : True = term232.
Proof. exact (SYM (@lem5246067)). Qed.
Lemma lem5246069 : term232.
Proof. exact (EQ_MP (@lem5246068) (@lem0)). Qed.
Lemma lem5246070 : term296 = term299.
Proof. exact (@lem5246059 (@lem5246069)). Qed.
Lemma lem5246072 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246073 : term243 = term32.
Proof. exact (@lem5246072 term85). Qed.
Lemma lem5246075 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246076 : term243 = term32.
Proof. exact (@lem5246075 term85). Qed.
Lemma lem5246077 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5246078 : term244 = term233.
Proof. exact (MK_COMB (@lem5246077) (@lem5246076)). Qed.
Lemma lem5246079 : term299 = term295.
Proof. exact (MK_COMB (@lem5246078) (@lem5246073)). Qed.
Lemma lem5246081 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246082 : term295 = term300.
Proof. exact (@lem5246081 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5246083 : term300 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5246084 : term295 = False.
Proof. exact (TRANS (@lem5246082) (@lem5246083)). Qed.
Lemma lem5246085 : term299 = False.
Proof. exact (TRANS (@lem5246079) (@lem5246084)). Qed.
Lemma lem5246086 : term296 = False.
Proof. exact (TRANS (@lem5246070) (@lem5246085)). Qed.
Lemma lem5246087 : term295 = False.
Proof. exact (TRANS (@lem5246047) (@lem5246086)). Qed.
Lemma lem5246088 : term294 = False.
Proof. exact (TRANS (@lem5246038) (@lem5246087)). Qed.
Lemma lem5246089 (e : real) (l : real) (x : real) (h1 : term146 e l x) : False.
Proof. exact (EQ_MP (@lem5246088) (@lem5246035 e l x h1)). Qed.
Lemma lem5246090 (e : real) (l : real) (x : real) (h1 : term149 e l x) : False.
Proof. exact (or_elim (@lem5244991 e l x h1) (fun h0 : term144 e l x => @lem5245540 e l x h0) (fun h0 : term146 e l x => @lem5246089 e l x h0)). Qed.
Lemma lem5246091 (e : real) (l : real) (x : real) (h1 : term228 e l x) : term228 e l x.
Proof. exact (h1). Qed.
Lemma lem5246092 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term162 e l x.
Proof. exact (h1). Qed.
Lemma lem5246093 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term159 e l x.
Proof. exact (proj2 (@lem5246092 e l x h1)). Qed.
Lemma lem5246095 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term121 e l x.
Proof. exact (proj2 (@lem5246093 e l x h1)). Qed.
Lemma lem5246096 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term57 e l x.
Proof. exact (proj1 (@lem5246093 e l x h1)). Qed.
Lemma lem5246097 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term118 e l x.
Proof. exact (proj2 (@lem5246095 e l x h1)). Qed.
Lemma lem5246100 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5246101 : term231 = term232.
Proof. exact (@lem5246100 term32 term91). Qed.
Lemma lem5246103 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246104 : term91 = term101.
Proof. exact (@lem5246103 term85). Qed.
Lemma lem5246106 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246107 : term32 = term172.
Proof. exact (@lem5246106 (NUMERAL 0)). Qed.
Lemma lem5246108 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5246109 : term233 = term234.
Proof. exact (MK_COMB (@lem5246108) (@lem5246107)). Qed.
Lemma lem5246110 : term232 = term235.
Proof. exact (MK_COMB (@lem5246109) (@lem5246104)). Qed.
Lemma lem5246111 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5246113 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246114 : term232 = term238.
Proof. exact (@lem5246113 (NUMERAL 0) term85). Qed.
Lemma lem5246115 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246116 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246117 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246116 h1) (fun h1 : term238 = True => @lem5246115)). Qed.
Lemma lem5246118 : term238 = True.
Proof. exact (EQ_MP (@lem5246117) (@lem5246115)). Qed.
Lemma lem5246119 : term232 = True.
Proof. exact (TRANS (@lem5246114) (@lem5246118)). Qed.
Lemma lem5246120 : True = term232.
Proof. exact (SYM (@lem5246119)). Qed.
Lemma lem5246121 : term232.
Proof. exact (EQ_MP (@lem5246120) (@lem0)). Qed.
Lemma lem5246122 : term240.
Proof. exact (@lem5246111 (@lem5246121)). Qed.
Lemma lem5246124 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246125 : term232 = term238.
Proof. exact (@lem5246124 (NUMERAL 0) term85). Qed.
Lemma lem5246126 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246127 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246128 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246127 h1) (fun h1 : term238 = True => @lem5246126)). Qed.
Lemma lem5246129 : term238 = True.
Proof. exact (EQ_MP (@lem5246128) (@lem5246126)). Qed.
Lemma lem5246130 : term232 = True.
Proof. exact (TRANS (@lem5246125) (@lem5246129)). Qed.
Lemma lem5246131 : True = term232.
Proof. exact (SYM (@lem5246130)). Qed.
Lemma lem5246132 : term232.
Proof. exact (EQ_MP (@lem5246131) (@lem0)). Qed.
Lemma lem5246133 : term235 = term241.
Proof. exact (@lem5246122 (@lem5246132)). Qed.
Lemma lem5246135 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5246136 : term94 = term95.
Proof. exact (@lem5246135 term85 term85). Qed.
Lemma lem5246137 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246138 : term97 = term85.
Proof. exact (EQ_MP (@lem5246137) (@lem940073)). Qed.
Lemma lem5246139 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246140 : term95 = term91.
Proof. exact (MK_COMB (@lem5246139) (@lem5246138)). Qed.
Lemma lem5246141 : term94 = term91.
Proof. exact (TRANS (@lem5246136) (@lem5246140)). Qed.
Lemma lem5246143 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246144 : term243 = term32.
Proof. exact (@lem5246143 term85). Qed.
Lemma lem5246145 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5246146 : term244 = term233.
Proof. exact (MK_COMB (@lem5246145) (@lem5246144)). Qed.
Lemma lem5246147 : term241 = term232.
Proof. exact (MK_COMB (@lem5246146) (@lem5246141)). Qed.
Lemma lem5246149 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246150 : term232 = term238.
Proof. exact (@lem5246149 (NUMERAL 0) term85). Qed.
Lemma lem5246151 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246152 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246153 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246152 h1) (fun h1 : term238 = True => @lem5246151)). Qed.
Lemma lem5246154 : term238 = True.
Proof. exact (EQ_MP (@lem5246153) (@lem5246151)). Qed.
Lemma lem5246155 : term232 = True.
Proof. exact (TRANS (@lem5246150) (@lem5246154)). Qed.
Lemma lem5246156 : term241 = True.
Proof. exact (TRANS (@lem5246147) (@lem5246155)). Qed.
Lemma lem5246157 : term235 = True.
Proof. exact (TRANS (@lem5246133) (@lem5246156)). Qed.
Lemma lem5246158 : term232 = True.
Proof. exact (TRANS (@lem5246110) (@lem5246157)). Qed.
Lemma lem5246159 : term231 = True.
Proof. exact (TRANS (@lem5246101) (@lem5246158)). Qed.
Lemma lem5246160 : True = term231.
Proof. exact (SYM (@lem5246159)). Qed.
Lemma lem5246161 : term231.
Proof. exact (EQ_MP (@lem5246160) (@lem0)). Qed.
Lemma lem5246162 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term301 e l x.
Proof. exact (conj (@lem5246161) (@lem5246097 e l x h1)). Qed.
Lemma lem5246164 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5246165 (e : real) (l : real) (x : real) : term302 e l x.
Proof. exact (@lem5246164 term91 (term107 e l x)). Qed.
Lemma lem5246166 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term303 e l x.
Proof. exact (@lem5246165 e l x (@lem5246162 e l x h1)). Qed.
Lemma lem5246167 (e : real) (l : real) (x : real) : (term304 e l x) = (term107 e l x).
Proof. exact (@lem1982733 (term107 e l x)). Qed.
Lemma lem5246168 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5246169 (e : real) (l : real) (x : real) : (term305 e l x) = (term117 e l x).
Proof. exact (MK_COMB (@lem5246168) (@lem5246167 e l x)). Qed.
Lemma lem5246170 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5246171 (e : real) (l : real) (x : real) : (term303 e l x) = (term118 e l x).
Proof. exact (MK_COMB (@lem5246169 e l x) (@lem5246170)). Qed.
Lemma lem5246172 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term118 e l x.
Proof. exact (EQ_MP (@lem5246171 e l x) (@lem5246166 e l x h1)). Qed.
Lemma lem5246174 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5246175 : term231 = term232.
Proof. exact (@lem5246174 term32 term91). Qed.
Lemma lem5246177 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246178 : term91 = term101.
Proof. exact (@lem5246177 term85). Qed.
Lemma lem5246180 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246181 : term32 = term172.
Proof. exact (@lem5246180 (NUMERAL 0)). Qed.
Lemma lem5246182 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5246183 : term233 = term234.
Proof. exact (MK_COMB (@lem5246182) (@lem5246181)). Qed.
Lemma lem5246184 : term232 = term235.
Proof. exact (MK_COMB (@lem5246183) (@lem5246178)). Qed.
Lemma lem5246185 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5246187 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246188 : term232 = term238.
Proof. exact (@lem5246187 (NUMERAL 0) term85). Qed.
Lemma lem5246189 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246190 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246191 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246190 h1) (fun h1 : term238 = True => @lem5246189)). Qed.
Lemma lem5246192 : term238 = True.
Proof. exact (EQ_MP (@lem5246191) (@lem5246189)). Qed.
Lemma lem5246193 : term232 = True.
Proof. exact (TRANS (@lem5246188) (@lem5246192)). Qed.
Lemma lem5246194 : True = term232.
Proof. exact (SYM (@lem5246193)). Qed.
Lemma lem5246195 : term232.
Proof. exact (EQ_MP (@lem5246194) (@lem0)). Qed.
Lemma lem5246196 : term240.
Proof. exact (@lem5246185 (@lem5246195)). Qed.
Lemma lem5246198 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246199 : term232 = term238.
Proof. exact (@lem5246198 (NUMERAL 0) term85). Qed.
Lemma lem5246200 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246201 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246202 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246201 h1) (fun h1 : term238 = True => @lem5246200)). Qed.
Lemma lem5246203 : term238 = True.
Proof. exact (EQ_MP (@lem5246202) (@lem5246200)). Qed.
Lemma lem5246204 : term232 = True.
Proof. exact (TRANS (@lem5246199) (@lem5246203)). Qed.
Lemma lem5246205 : True = term232.
Proof. exact (SYM (@lem5246204)). Qed.
Lemma lem5246206 : term232.
Proof. exact (EQ_MP (@lem5246205) (@lem0)). Qed.
Lemma lem5246207 : term235 = term241.
Proof. exact (@lem5246196 (@lem5246206)). Qed.
Lemma lem5246209 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5246210 : term94 = term95.
Proof. exact (@lem5246209 term85 term85). Qed.
Lemma lem5246211 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246212 : term97 = term85.
Proof. exact (EQ_MP (@lem5246211) (@lem940073)). Qed.
Lemma lem5246213 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246214 : term95 = term91.
Proof. exact (MK_COMB (@lem5246213) (@lem5246212)). Qed.
Lemma lem5246215 : term94 = term91.
Proof. exact (TRANS (@lem5246210) (@lem5246214)). Qed.
Lemma lem5246217 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246218 : term243 = term32.
Proof. exact (@lem5246217 term85). Qed.
Lemma lem5246219 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5246220 : term244 = term233.
Proof. exact (MK_COMB (@lem5246219) (@lem5246218)). Qed.
Lemma lem5246221 : term241 = term232.
Proof. exact (MK_COMB (@lem5246220) (@lem5246215)). Qed.
Lemma lem5246223 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246224 : term232 = term238.
Proof. exact (@lem5246223 (NUMERAL 0) term85). Qed.
Lemma lem5246225 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246226 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246227 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246226 h1) (fun h1 : term238 = True => @lem5246225)). Qed.
Lemma lem5246228 : term238 = True.
Proof. exact (EQ_MP (@lem5246227) (@lem5246225)). Qed.
Lemma lem5246229 : term232 = True.
Proof. exact (TRANS (@lem5246224) (@lem5246228)). Qed.
Lemma lem5246230 : term241 = True.
Proof. exact (TRANS (@lem5246221) (@lem5246229)). Qed.
Lemma lem5246231 : term235 = True.
Proof. exact (TRANS (@lem5246207) (@lem5246230)). Qed.
Lemma lem5246232 : term232 = True.
Proof. exact (TRANS (@lem5246184) (@lem5246231)). Qed.
Lemma lem5246233 : term231 = True.
Proof. exact (TRANS (@lem5246175) (@lem5246232)). Qed.
Lemma lem5246234 : True = term231.
Proof. exact (SYM (@lem5246233)). Qed.
Lemma lem5246235 : term231.
Proof. exact (EQ_MP (@lem5246234) (@lem0)). Qed.
Lemma lem5246236 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term306 e l x.
Proof. exact (conj (@lem5246235) (@lem5246096 e l x h1)). Qed.
Lemma lem5246238 (x : real) (y : real) : term252 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5246239 (e : real) (l : real) (x : real) : term307 e l x.
Proof. exact (@lem5246238 term91 (term54 e l x)). Qed.
Lemma lem5246240 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term308 e l x.
Proof. exact (@lem5246239 e l x (@lem5246236 e l x h1)). Qed.
Lemma lem5246241 (e : real) (l : real) (x : real) : (term309 e l x) = (term54 e l x).
Proof. exact (@lem1982733 (term54 e l x)). Qed.
Lemma lem5246242 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5246243 (e : real) (l : real) (x : real) : (term310 e l x) = (term56 e l x).
Proof. exact (MK_COMB (@lem5246242) (@lem5246241 e l x)). Qed.
Lemma lem5246244 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5246245 (e : real) (l : real) (x : real) : (term308 e l x) = (term57 e l x).
Proof. exact (MK_COMB (@lem5246243 e l x) (@lem5246244)). Qed.
Lemma lem5246246 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term57 e l x.
Proof. exact (EQ_MP (@lem5246245 e l x) (@lem5246240 e l x h1)). Qed.
Lemma lem5246247 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term311 e l x.
Proof. exact (conj (@lem5246246 e l x h1) (@lem5246172 e l x h1)). Qed.
Lemma lem5246249 (x : real) (y : real) : term258 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5246250 (e : real) (l : real) (x : real) : term312 e l x.
Proof. exact (@lem5246249 (term54 e l x) (term107 e l x)). Qed.
Lemma lem5246251 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term313 e l x.
Proof. exact (@lem5246250 e l x (@lem5246247 e l x h1)). Qed.
Lemma lem5246252 (e : real) (l : real) (x : real) : (term314 e l x) = (term315 e l x).
Proof. exact (@lem1982753 (term25 e) e (term24 l x) (term23 l x)). Qed.
Lemma lem5246253 (e : real) : (term263 e) = (term264 e).
Proof. exact (@lem1982713 term51 e). Qed.
Lemma lem5246255 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246256 : term91 = term101.
Proof. exact (@lem5246255 term85). Qed.
Lemma lem5246258 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5246259 : term51 = term84.
Proof. exact (@lem5246258 term85). Qed.
Lemma lem5246260 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5246261 : term265 = term266.
Proof. exact (MK_COMB (@lem5246260) (@lem5246259)). Qed.
Lemma lem5246262 : term267 = term268.
Proof. exact (MK_COMB (@lem5246261) (@lem5246256)). Qed.
Lemma lem5246263 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5246265 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246266 : term232 = term238.
Proof. exact (@lem5246265 (NUMERAL 0) term85). Qed.
Lemma lem5246267 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246268 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246269 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246268 h1) (fun h1 : term238 = True => @lem5246267)). Qed.
Lemma lem5246270 : term238 = True.
Proof. exact (EQ_MP (@lem5246269) (@lem5246267)). Qed.
Lemma lem5246271 : term232 = True.
Proof. exact (TRANS (@lem5246266) (@lem5246270)). Qed.
Lemma lem5246272 : True = term232.
Proof. exact (SYM (@lem5246271)). Qed.
Lemma lem5246273 : term232.
Proof. exact (EQ_MP (@lem5246272) (@lem0)). Qed.
Lemma lem5246274 : term270.
Proof. exact (@lem5246263 (@lem5246273)). Qed.
Lemma lem5246276 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246277 : term232 = term238.
Proof. exact (@lem5246276 (NUMERAL 0) term85). Qed.
Lemma lem5246278 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246279 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246280 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246279 h1) (fun h1 : term238 = True => @lem5246278)). Qed.
Lemma lem5246281 : term238 = True.
Proof. exact (EQ_MP (@lem5246280) (@lem5246278)). Qed.
Lemma lem5246282 : term232 = True.
Proof. exact (TRANS (@lem5246277) (@lem5246281)). Qed.
Lemma lem5246283 : True = term232.
Proof. exact (SYM (@lem5246282)). Qed.
Lemma lem5246284 : term232.
Proof. exact (EQ_MP (@lem5246283) (@lem0)). Qed.
Lemma lem5246285 : term271.
Proof. exact (@lem5246274 (@lem5246284)). Qed.
Lemma lem5246287 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246288 : term232 = term238.
Proof. exact (@lem5246287 (NUMERAL 0) term85). Qed.
Lemma lem5246289 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246290 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246291 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246290 h1) (fun h1 : term238 = True => @lem5246289)). Qed.
Lemma lem5246292 : term238 = True.
Proof. exact (EQ_MP (@lem5246291) (@lem5246289)). Qed.
Lemma lem5246293 : term232 = True.
Proof. exact (TRANS (@lem5246288) (@lem5246292)). Qed.
Lemma lem5246294 : True = term232.
Proof. exact (SYM (@lem5246293)). Qed.
Lemma lem5246295 : term232.
Proof. exact (EQ_MP (@lem5246294) (@lem0)). Qed.
Lemma lem5246296 : term272.
Proof. exact (@lem5246285 (@lem5246295)). Qed.
Lemma lem5246298 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5246299 : term94 = term95.
Proof. exact (@lem5246298 term85 term85). Qed.
Lemma lem5246300 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246301 : term97 = term85.
Proof. exact (EQ_MP (@lem5246300) (@lem940073)). Qed.
Lemma lem5246302 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246303 : term95 = term91.
Proof. exact (MK_COMB (@lem5246302) (@lem5246301)). Qed.
Lemma lem5246304 : term94 = term91.
Proof. exact (TRANS (@lem5246299) (@lem5246303)). Qed.
Lemma lem5246306 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5246307 : term275 = term276.
Proof. exact (@lem5246306 term85 term85). Qed.
Lemma lem5246308 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246309 : term97 = term85.
Proof. exact (EQ_MP (@lem5246308) (@lem940073)). Qed.
Lemma lem5246310 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246311 : term95 = term91.
Proof. exact (MK_COMB (@lem5246310) (@lem5246309)). Qed.
Lemma lem5246312 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5246313 : term276 = term51.
Proof. exact (MK_COMB (@lem5246312) (@lem5246311)). Qed.
Lemma lem5246314 : term275 = term51.
Proof. exact (TRANS (@lem5246307) (@lem5246313)). Qed.
Lemma lem5246315 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5246316 : term277 = term265.
Proof. exact (MK_COMB (@lem5246315) (@lem5246314)). Qed.
Lemma lem5246317 : term278 = term267.
Proof. exact (MK_COMB (@lem5246316) (@lem5246304)). Qed.
Lemma lem5246319 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5246320 : term267 = term32.
Proof. exact (@lem5246319 term85). Qed.
Lemma lem5246321 : term278 = term32.
Proof. exact (TRANS (@lem5246317) (@lem5246320)). Qed.
Lemma lem5246322 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5246323 : term280 = term281.
Proof. exact (MK_COMB (@lem5246322) (@lem5246321)). Qed.
Lemma lem5246324 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5246325 : term282 = term243.
Proof. exact (MK_COMB (@lem5246323) (@lem5246324)). Qed.
Lemma lem5246327 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246328 : term243 = term32.
Proof. exact (@lem5246327 term85). Qed.
Lemma lem5246329 : term282 = term32.
Proof. exact (TRANS (@lem5246325) (@lem5246328)). Qed.
Lemma lem5246331 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5246332 : term94 = term95.
Proof. exact (@lem5246331 term85 term85). Qed.
Lemma lem5246333 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246334 : term97 = term85.
Proof. exact (EQ_MP (@lem5246333) (@lem940073)). Qed.
Lemma lem5246335 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246336 : term95 = term91.
Proof. exact (MK_COMB (@lem5246335) (@lem5246334)). Qed.
Lemma lem5246337 : term94 = term91.
Proof. exact (TRANS (@lem5246332) (@lem5246336)). Qed.
Lemma lem5246338 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5246339 : term283 = term243.
Proof. exact (MK_COMB (@lem5246338) (@lem5246337)). Qed.
Lemma lem5246341 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246342 : term243 = term32.
Proof. exact (@lem5246341 term85). Qed.
Lemma lem5246343 : term283 = term32.
Proof. exact (TRANS (@lem5246339) (@lem5246342)). Qed.
Lemma lem5246344 : term32 = term283.
Proof. exact (SYM (@lem5246343)). Qed.
Lemma lem5246345 : term282 = term283.
Proof. exact (TRANS (@lem5246329) (@lem5246344)). Qed.
Lemma lem5246346 : term268 = term172.
Proof. exact (@lem5246296 (@lem5246345)). Qed.
Lemma lem5246347 : term267 = term172.
Proof. exact (TRANS (@lem5246262) (@lem5246346)). Qed.
Lemma lem5246349 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5246350 : term172 = term32.
Proof. exact (@lem5246349 term32). Qed.
Lemma lem5246351 : term267 = term32.
Proof. exact (TRANS (@lem5246347) (@lem5246350)). Qed.
Lemma lem5246352 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5246353 : term284 = term281.
Proof. exact (MK_COMB (@lem5246352) (@lem5246351)). Qed.
Lemma lem5246354 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem5246355 (e : real) : (term264 e) = (term285 e).
Proof. exact (MK_COMB (@lem5246353) (@lem5246354 e)). Qed.
Lemma lem5246356 (e : real) : (term263 e) = (term285 e).
Proof. exact (TRANS (@lem5246253 e) (@lem5246355 e)). Qed.
Lemma lem5246357 (e : real) : (term285 e) = term32.
Proof. exact (@lem1982719 e). Qed.
Lemma lem5246358 (e : real) : (term263 e) = term32.
Proof. exact (TRANS (@lem5246356 e) (@lem5246357 e)). Qed.
Lemma lem5246359 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5246360 (e : real) : (term286 e) = term206.
Proof. exact (MK_COMB (@lem5246359) (@lem5246358 e)). Qed.
Lemma lem5246361 (l : real) (x : real) : (term316 l x) = (term317 l x).
Proof. exact (@lem1982753 (term25 l) l x (term25 x)). Qed.
Lemma lem5246362 (l : real) : (term263 l) = (term264 l).
Proof. exact (@lem1982713 term51 l). Qed.
Lemma lem5246364 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246365 : term91 = term101.
Proof. exact (@lem5246364 term85). Qed.
Lemma lem5246367 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5246368 : term51 = term84.
Proof. exact (@lem5246367 term85). Qed.
Lemma lem5246369 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5246370 : term265 = term266.
Proof. exact (MK_COMB (@lem5246369) (@lem5246368)). Qed.
Lemma lem5246371 : term267 = term268.
Proof. exact (MK_COMB (@lem5246370) (@lem5246365)). Qed.
Lemma lem5246372 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5246374 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246375 : term232 = term238.
Proof. exact (@lem5246374 (NUMERAL 0) term85). Qed.
Lemma lem5246376 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246377 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246378 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246377 h1) (fun h1 : term238 = True => @lem5246376)). Qed.
Lemma lem5246379 : term238 = True.
Proof. exact (EQ_MP (@lem5246378) (@lem5246376)). Qed.
Lemma lem5246380 : term232 = True.
Proof. exact (TRANS (@lem5246375) (@lem5246379)). Qed.
Lemma lem5246381 : True = term232.
Proof. exact (SYM (@lem5246380)). Qed.
Lemma lem5246382 : term232.
Proof. exact (EQ_MP (@lem5246381) (@lem0)). Qed.
Lemma lem5246383 : term270.
Proof. exact (@lem5246372 (@lem5246382)). Qed.
Lemma lem5246385 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246386 : term232 = term238.
Proof. exact (@lem5246385 (NUMERAL 0) term85). Qed.
Lemma lem5246387 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246388 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246389 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246388 h1) (fun h1 : term238 = True => @lem5246387)). Qed.
Lemma lem5246390 : term238 = True.
Proof. exact (EQ_MP (@lem5246389) (@lem5246387)). Qed.
Lemma lem5246391 : term232 = True.
Proof. exact (TRANS (@lem5246386) (@lem5246390)). Qed.
Lemma lem5246392 : True = term232.
Proof. exact (SYM (@lem5246391)). Qed.
Lemma lem5246393 : term232.
Proof. exact (EQ_MP (@lem5246392) (@lem0)). Qed.
Lemma lem5246394 : term271.
Proof. exact (@lem5246383 (@lem5246393)). Qed.
Lemma lem5246396 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246397 : term232 = term238.
Proof. exact (@lem5246396 (NUMERAL 0) term85). Qed.
Lemma lem5246398 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246399 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246400 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246399 h1) (fun h1 : term238 = True => @lem5246398)). Qed.
Lemma lem5246401 : term238 = True.
Proof. exact (EQ_MP (@lem5246400) (@lem5246398)). Qed.
Lemma lem5246402 : term232 = True.
Proof. exact (TRANS (@lem5246397) (@lem5246401)). Qed.
Lemma lem5246403 : True = term232.
Proof. exact (SYM (@lem5246402)). Qed.
Lemma lem5246404 : term232.
Proof. exact (EQ_MP (@lem5246403) (@lem0)). Qed.
Lemma lem5246405 : term272.
Proof. exact (@lem5246394 (@lem5246404)). Qed.
Lemma lem5246407 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5246408 : term94 = term95.
Proof. exact (@lem5246407 term85 term85). Qed.
Lemma lem5246409 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246410 : term97 = term85.
Proof. exact (EQ_MP (@lem5246409) (@lem940073)). Qed.
Lemma lem5246411 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246412 : term95 = term91.
Proof. exact (MK_COMB (@lem5246411) (@lem5246410)). Qed.
Lemma lem5246413 : term94 = term91.
Proof. exact (TRANS (@lem5246408) (@lem5246412)). Qed.
Lemma lem5246415 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5246416 : term275 = term276.
Proof. exact (@lem5246415 term85 term85). Qed.
Lemma lem5246417 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246418 : term97 = term85.
Proof. exact (EQ_MP (@lem5246417) (@lem940073)). Qed.
Lemma lem5246419 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246420 : term95 = term91.
Proof. exact (MK_COMB (@lem5246419) (@lem5246418)). Qed.
Lemma lem5246421 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5246422 : term276 = term51.
Proof. exact (MK_COMB (@lem5246421) (@lem5246420)). Qed.
Lemma lem5246423 : term275 = term51.
Proof. exact (TRANS (@lem5246416) (@lem5246422)). Qed.
Lemma lem5246424 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5246425 : term277 = term265.
Proof. exact (MK_COMB (@lem5246424) (@lem5246423)). Qed.
Lemma lem5246426 : term278 = term267.
Proof. exact (MK_COMB (@lem5246425) (@lem5246413)). Qed.
Lemma lem5246428 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5246429 : term267 = term32.
Proof. exact (@lem5246428 term85). Qed.
Lemma lem5246430 : term278 = term32.
Proof. exact (TRANS (@lem5246426) (@lem5246429)). Qed.
Lemma lem5246431 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5246432 : term280 = term281.
Proof. exact (MK_COMB (@lem5246431) (@lem5246430)). Qed.
Lemma lem5246433 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5246434 : term282 = term243.
Proof. exact (MK_COMB (@lem5246432) (@lem5246433)). Qed.
Lemma lem5246436 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246437 : term243 = term32.
Proof. exact (@lem5246436 term85). Qed.
Lemma lem5246438 : term282 = term32.
Proof. exact (TRANS (@lem5246434) (@lem5246437)). Qed.
Lemma lem5246440 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5246441 : term94 = term95.
Proof. exact (@lem5246440 term85 term85). Qed.
Lemma lem5246442 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246443 : term97 = term85.
Proof. exact (EQ_MP (@lem5246442) (@lem940073)). Qed.
Lemma lem5246444 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246445 : term95 = term91.
Proof. exact (MK_COMB (@lem5246444) (@lem5246443)). Qed.
Lemma lem5246446 : term94 = term91.
Proof. exact (TRANS (@lem5246441) (@lem5246445)). Qed.
Lemma lem5246447 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5246448 : term283 = term243.
Proof. exact (MK_COMB (@lem5246447) (@lem5246446)). Qed.
Lemma lem5246450 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246451 : term243 = term32.
Proof. exact (@lem5246450 term85). Qed.
Lemma lem5246452 : term283 = term32.
Proof. exact (TRANS (@lem5246448) (@lem5246451)). Qed.
Lemma lem5246453 : term32 = term283.
Proof. exact (SYM (@lem5246452)). Qed.
Lemma lem5246454 : term282 = term283.
Proof. exact (TRANS (@lem5246438) (@lem5246453)). Qed.
Lemma lem5246455 : term268 = term172.
Proof. exact (@lem5246405 (@lem5246454)). Qed.
Lemma lem5246456 : term267 = term172.
Proof. exact (TRANS (@lem5246371) (@lem5246455)). Qed.
Lemma lem5246458 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5246459 : term172 = term32.
Proof. exact (@lem5246458 term32). Qed.
Lemma lem5246460 : term267 = term32.
Proof. exact (TRANS (@lem5246456) (@lem5246459)). Qed.
Lemma lem5246461 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5246462 : term284 = term281.
Proof. exact (MK_COMB (@lem5246461) (@lem5246460)). Qed.
Lemma lem5246463 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5246464 (l : real) : (term264 l) = (term285 l).
Proof. exact (MK_COMB (@lem5246462) (@lem5246463 l)). Qed.
Lemma lem5246465 (l : real) : (term263 l) = (term285 l).
Proof. exact (TRANS (@lem5246362 l) (@lem5246464 l)). Qed.
Lemma lem5246466 (l : real) : (term285 l) = term32.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5246467 (l : real) : (term263 l) = term32.
Proof. exact (TRANS (@lem5246465 l) (@lem5246466 l)). Qed.
Lemma lem5246468 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5246469 (l : real) : (term286 l) = term206.
Proof. exact (MK_COMB (@lem5246468) (@lem5246467 l)). Qed.
Lemma lem5246470 (x : real) : (term289 x) = (term264 x).
Proof. exact (@lem1982715 term51 x). Qed.
Lemma lem5246472 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246473 : term91 = term101.
Proof. exact (@lem5246472 term85). Qed.
Lemma lem5246475 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5246476 : term51 = term84.
Proof. exact (@lem5246475 term85). Qed.
Lemma lem5246477 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5246478 : term265 = term266.
Proof. exact (MK_COMB (@lem5246477) (@lem5246476)). Qed.
Lemma lem5246479 : term267 = term268.
Proof. exact (MK_COMB (@lem5246478) (@lem5246473)). Qed.
Lemma lem5246480 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5246482 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246483 : term232 = term238.
Proof. exact (@lem5246482 (NUMERAL 0) term85). Qed.
Lemma lem5246484 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246485 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246486 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246485 h1) (fun h1 : term238 = True => @lem5246484)). Qed.
Lemma lem5246487 : term238 = True.
Proof. exact (EQ_MP (@lem5246486) (@lem5246484)). Qed.
Lemma lem5246488 : term232 = True.
Proof. exact (TRANS (@lem5246483) (@lem5246487)). Qed.
Lemma lem5246489 : True = term232.
Proof. exact (SYM (@lem5246488)). Qed.
Lemma lem5246490 : term232.
Proof. exact (EQ_MP (@lem5246489) (@lem0)). Qed.
Lemma lem5246491 : term270.
Proof. exact (@lem5246480 (@lem5246490)). Qed.
Lemma lem5246493 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246494 : term232 = term238.
Proof. exact (@lem5246493 (NUMERAL 0) term85). Qed.
Lemma lem5246495 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246496 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246497 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246496 h1) (fun h1 : term238 = True => @lem5246495)). Qed.
Lemma lem5246498 : term238 = True.
Proof. exact (EQ_MP (@lem5246497) (@lem5246495)). Qed.
Lemma lem5246499 : term232 = True.
Proof. exact (TRANS (@lem5246494) (@lem5246498)). Qed.
Lemma lem5246500 : True = term232.
Proof. exact (SYM (@lem5246499)). Qed.
Lemma lem5246501 : term232.
Proof. exact (EQ_MP (@lem5246500) (@lem0)). Qed.
Lemma lem5246502 : term271.
Proof. exact (@lem5246491 (@lem5246501)). Qed.
Lemma lem5246504 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246505 : term232 = term238.
Proof. exact (@lem5246504 (NUMERAL 0) term85). Qed.
Lemma lem5246506 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246507 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246508 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246507 h1) (fun h1 : term238 = True => @lem5246506)). Qed.
Lemma lem5246509 : term238 = True.
Proof. exact (EQ_MP (@lem5246508) (@lem5246506)). Qed.
Lemma lem5246510 : term232 = True.
Proof. exact (TRANS (@lem5246505) (@lem5246509)). Qed.
Lemma lem5246511 : True = term232.
Proof. exact (SYM (@lem5246510)). Qed.
Lemma lem5246512 : term232.
Proof. exact (EQ_MP (@lem5246511) (@lem0)). Qed.
Lemma lem5246513 : term272.
Proof. exact (@lem5246502 (@lem5246512)). Qed.
Lemma lem5246515 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5246516 : term94 = term95.
Proof. exact (@lem5246515 term85 term85). Qed.
Lemma lem5246517 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246518 : term97 = term85.
Proof. exact (EQ_MP (@lem5246517) (@lem940073)). Qed.
Lemma lem5246519 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246520 : term95 = term91.
Proof. exact (MK_COMB (@lem5246519) (@lem5246518)). Qed.
Lemma lem5246521 : term94 = term91.
Proof. exact (TRANS (@lem5246516) (@lem5246520)). Qed.
Lemma lem5246523 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5246524 : term275 = term276.
Proof. exact (@lem5246523 term85 term85). Qed.
Lemma lem5246525 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246526 : term97 = term85.
Proof. exact (EQ_MP (@lem5246525) (@lem940073)). Qed.
Lemma lem5246527 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246528 : term95 = term91.
Proof. exact (MK_COMB (@lem5246527) (@lem5246526)). Qed.
Lemma lem5246529 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5246530 : term276 = term51.
Proof. exact (MK_COMB (@lem5246529) (@lem5246528)). Qed.
Lemma lem5246531 : term275 = term51.
Proof. exact (TRANS (@lem5246524) (@lem5246530)). Qed.
Lemma lem5246532 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5246533 : term277 = term265.
Proof. exact (MK_COMB (@lem5246532) (@lem5246531)). Qed.
Lemma lem5246534 : term278 = term267.
Proof. exact (MK_COMB (@lem5246533) (@lem5246521)). Qed.
Lemma lem5246536 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5246537 : term267 = term32.
Proof. exact (@lem5246536 term85). Qed.
Lemma lem5246538 : term278 = term32.
Proof. exact (TRANS (@lem5246534) (@lem5246537)). Qed.
Lemma lem5246539 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5246540 : term280 = term281.
Proof. exact (MK_COMB (@lem5246539) (@lem5246538)). Qed.
Lemma lem5246541 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5246542 : term282 = term243.
Proof. exact (MK_COMB (@lem5246540) (@lem5246541)). Qed.
Lemma lem5246544 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246545 : term243 = term32.
Proof. exact (@lem5246544 term85). Qed.
Lemma lem5246546 : term282 = term32.
Proof. exact (TRANS (@lem5246542) (@lem5246545)). Qed.
Lemma lem5246548 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5246549 : term94 = term95.
Proof. exact (@lem5246548 term85 term85). Qed.
Lemma lem5246550 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246551 : term97 = term85.
Proof. exact (EQ_MP (@lem5246550) (@lem940073)). Qed.
Lemma lem5246552 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246553 : term95 = term91.
Proof. exact (MK_COMB (@lem5246552) (@lem5246551)). Qed.
Lemma lem5246554 : term94 = term91.
Proof. exact (TRANS (@lem5246549) (@lem5246553)). Qed.
Lemma lem5246555 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5246556 : term283 = term243.
Proof. exact (MK_COMB (@lem5246555) (@lem5246554)). Qed.
Lemma lem5246558 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246559 : term243 = term32.
Proof. exact (@lem5246558 term85). Qed.
Lemma lem5246560 : term283 = term32.
Proof. exact (TRANS (@lem5246556) (@lem5246559)). Qed.
Lemma lem5246561 : term32 = term283.
Proof. exact (SYM (@lem5246560)). Qed.
Lemma lem5246562 : term282 = term283.
Proof. exact (TRANS (@lem5246546) (@lem5246561)). Qed.
Lemma lem5246563 : term268 = term172.
Proof. exact (@lem5246513 (@lem5246562)). Qed.
Lemma lem5246564 : term267 = term172.
Proof. exact (TRANS (@lem5246479) (@lem5246563)). Qed.
Lemma lem5246566 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5246567 : term172 = term32.
Proof. exact (@lem5246566 term32). Qed.
Lemma lem5246568 : term267 = term32.
Proof. exact (TRANS (@lem5246564) (@lem5246567)). Qed.
Lemma lem5246569 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5246570 : term284 = term281.
Proof. exact (MK_COMB (@lem5246569) (@lem5246568)). Qed.
Lemma lem5246571 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5246572 (x : real) : (term264 x) = (term285 x).
Proof. exact (MK_COMB (@lem5246570) (@lem5246571 x)). Qed.
Lemma lem5246573 (x : real) : (term289 x) = (term285 x).
Proof. exact (TRANS (@lem5246470 x) (@lem5246572 x)). Qed.
Lemma lem5246574 (x : real) : (term285 x) = term32.
Proof. exact (@lem1982719 x). Qed.
Lemma lem5246575 (x : real) : (term289 x) = term32.
Proof. exact (TRANS (@lem5246573 x) (@lem5246574 x)). Qed.
Lemma lem5246576 (l : real) (x : real) : (term317 l x) = term291.
Proof. exact (MK_COMB (@lem5246469 l) (@lem5246575 x)). Qed.
Lemma lem5246577 (l : real) (x : real) : (term316 l x) = term291.
Proof. exact (TRANS (@lem5246361 l x) (@lem5246576 l x)). Qed.
Lemma lem5246578 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5246579 (l : real) (x : real) : (term316 l x) = term32.
Proof. exact (TRANS (@lem5246577 l x) (@lem5246578)). Qed.
Lemma lem5246580 (e : real) (l : real) (x : real) : (term315 e l x) = term291.
Proof. exact (MK_COMB (@lem5246360 e) (@lem5246579 l x)). Qed.
Lemma lem5246581 (e : real) (l : real) (x : real) : (term314 e l x) = term291.
Proof. exact (TRANS (@lem5246252 e l x) (@lem5246580 e l x)). Qed.
Lemma lem5246582 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5246583 (e : real) (l : real) (x : real) : (term314 e l x) = term32.
Proof. exact (TRANS (@lem5246581 e l x) (@lem5246582)). Qed.
Lemma lem5246584 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5246585 (e : real) (l : real) (x : real) : (term318 e l x) = term293.
Proof. exact (MK_COMB (@lem5246584) (@lem5246583 e l x)). Qed.
Lemma lem5246586 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5246587 (e : real) (l : real) (x : real) : (term313 e l x) = term294.
Proof. exact (MK_COMB (@lem5246585 e l x) (@lem5246586)). Qed.
Lemma lem5246588 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term294.
Proof. exact (EQ_MP (@lem5246587 e l x) (@lem5246251 e l x h1)). Qed.
Lemma lem5246590 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5246591 : term294 = term295.
Proof. exact (@lem5246590 term32 term32). Qed.
Lemma lem5246593 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246594 : term32 = term172.
Proof. exact (@lem5246593 (NUMERAL 0)). Qed.
Lemma lem5246596 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246597 : term32 = term172.
Proof. exact (@lem5246596 (NUMERAL 0)). Qed.
Lemma lem5246598 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5246599 : term233 = term234.
Proof. exact (MK_COMB (@lem5246598) (@lem5246597)). Qed.
Lemma lem5246600 : term295 = term296.
Proof. exact (MK_COMB (@lem5246599) (@lem5246594)). Qed.
Lemma lem5246601 : term297.
Proof. exact (@lem1980255 term32 term91 term32 term91). Qed.
Lemma lem5246603 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246604 : term232 = term238.
Proof. exact (@lem5246603 (NUMERAL 0) term85). Qed.
Lemma lem5246605 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246606 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246607 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246606 h1) (fun h1 : term238 = True => @lem5246605)). Qed.
Lemma lem5246608 : term238 = True.
Proof. exact (EQ_MP (@lem5246607) (@lem5246605)). Qed.
Lemma lem5246609 : term232 = True.
Proof. exact (TRANS (@lem5246604) (@lem5246608)). Qed.
Lemma lem5246610 : True = term232.
Proof. exact (SYM (@lem5246609)). Qed.
Lemma lem5246611 : term232.
Proof. exact (EQ_MP (@lem5246610) (@lem0)). Qed.
Lemma lem5246612 : term298.
Proof. exact (@lem5246601 (@lem5246611)). Qed.
Lemma lem5246614 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246615 : term232 = term238.
Proof. exact (@lem5246614 (NUMERAL 0) term85). Qed.
Lemma lem5246616 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246617 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246618 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246617 h1) (fun h1 : term238 = True => @lem5246616)). Qed.
Lemma lem5246619 : term238 = True.
Proof. exact (EQ_MP (@lem5246618) (@lem5246616)). Qed.
Lemma lem5246620 : term232 = True.
Proof. exact (TRANS (@lem5246615) (@lem5246619)). Qed.
Lemma lem5246621 : True = term232.
Proof. exact (SYM (@lem5246620)). Qed.
Lemma lem5246622 : term232.
Proof. exact (EQ_MP (@lem5246621) (@lem0)). Qed.
Lemma lem5246623 : term296 = term299.
Proof. exact (@lem5246612 (@lem5246622)). Qed.
Lemma lem5246625 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246626 : term243 = term32.
Proof. exact (@lem5246625 term85). Qed.
Lemma lem5246628 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246629 : term243 = term32.
Proof. exact (@lem5246628 term85). Qed.
Lemma lem5246630 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5246631 : term244 = term233.
Proof. exact (MK_COMB (@lem5246630) (@lem5246629)). Qed.
Lemma lem5246632 : term299 = term295.
Proof. exact (MK_COMB (@lem5246631) (@lem5246626)). Qed.
Lemma lem5246634 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246635 : term295 = term300.
Proof. exact (@lem5246634 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5246636 : term300 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5246637 : term295 = False.
Proof. exact (TRANS (@lem5246635) (@lem5246636)). Qed.
Lemma lem5246638 : term299 = False.
Proof. exact (TRANS (@lem5246632) (@lem5246637)). Qed.
Lemma lem5246639 : term296 = False.
Proof. exact (TRANS (@lem5246623) (@lem5246638)). Qed.
Lemma lem5246640 : term295 = False.
Proof. exact (TRANS (@lem5246600) (@lem5246639)). Qed.
Lemma lem5246641 : term294 = False.
Proof. exact (TRANS (@lem5246591) (@lem5246640)). Qed.
Lemma lem5246642 (e : real) (l : real) (x : real) (h1 : term162 e l x) : False.
Proof. exact (EQ_MP (@lem5246641) (@lem5246588 e l x h1)). Qed.
Lemma lem5246643 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term227 e l x.
Proof. exact (h1). Qed.
Lemma lem5246644 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term225 e l x.
Proof. exact (proj2 (@lem5246643 e l x h1)). Qed.
Lemma lem5246646 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term121 e l x.
Proof. exact (proj2 (@lem5246644 e l x h1)). Qed.
Lemma lem5246647 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term44 e l x.
Proof. exact (proj1 (@lem5246644 e l x h1)). Qed.
Lemma lem5246649 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term111 e l x.
Proof. exact (proj1 (@lem5246646 e l x h1)). Qed.
Lemma lem5246651 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5246652 : term231 = term232.
Proof. exact (@lem5246651 term32 term91). Qed.
Lemma lem5246654 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246655 : term91 = term101.
Proof. exact (@lem5246654 term85). Qed.
Lemma lem5246657 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246658 : term32 = term172.
Proof. exact (@lem5246657 (NUMERAL 0)). Qed.
Lemma lem5246659 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5246660 : term233 = term234.
Proof. exact (MK_COMB (@lem5246659) (@lem5246658)). Qed.
Lemma lem5246661 : term232 = term235.
Proof. exact (MK_COMB (@lem5246660) (@lem5246655)). Qed.
Lemma lem5246662 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5246664 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246665 : term232 = term238.
Proof. exact (@lem5246664 (NUMERAL 0) term85). Qed.
Lemma lem5246666 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246667 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246668 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246667 h1) (fun h1 : term238 = True => @lem5246666)). Qed.
Lemma lem5246669 : term238 = True.
Proof. exact (EQ_MP (@lem5246668) (@lem5246666)). Qed.
Lemma lem5246670 : term232 = True.
Proof. exact (TRANS (@lem5246665) (@lem5246669)). Qed.
Lemma lem5246671 : True = term232.
Proof. exact (SYM (@lem5246670)). Qed.
Lemma lem5246672 : term232.
Proof. exact (EQ_MP (@lem5246671) (@lem0)). Qed.
Lemma lem5246673 : term240.
Proof. exact (@lem5246662 (@lem5246672)). Qed.
Lemma lem5246675 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246676 : term232 = term238.
Proof. exact (@lem5246675 (NUMERAL 0) term85). Qed.
Lemma lem5246677 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246678 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246679 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246678 h1) (fun h1 : term238 = True => @lem5246677)). Qed.
Lemma lem5246680 : term238 = True.
Proof. exact (EQ_MP (@lem5246679) (@lem5246677)). Qed.
Lemma lem5246681 : term232 = True.
Proof. exact (TRANS (@lem5246676) (@lem5246680)). Qed.
Lemma lem5246682 : True = term232.
Proof. exact (SYM (@lem5246681)). Qed.
Lemma lem5246683 : term232.
Proof. exact (EQ_MP (@lem5246682) (@lem0)). Qed.
Lemma lem5246684 : term235 = term241.
Proof. exact (@lem5246673 (@lem5246683)). Qed.
Lemma lem5246686 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5246687 : term94 = term95.
Proof. exact (@lem5246686 term85 term85). Qed.
Lemma lem5246688 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246689 : term97 = term85.
Proof. exact (EQ_MP (@lem5246688) (@lem940073)). Qed.
Lemma lem5246690 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246691 : term95 = term91.
Proof. exact (MK_COMB (@lem5246690) (@lem5246689)). Qed.
Lemma lem5246692 : term94 = term91.
Proof. exact (TRANS (@lem5246687) (@lem5246691)). Qed.
Lemma lem5246694 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246695 : term243 = term32.
Proof. exact (@lem5246694 term85). Qed.
Lemma lem5246696 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5246697 : term244 = term233.
Proof. exact (MK_COMB (@lem5246696) (@lem5246695)). Qed.
Lemma lem5246698 : term241 = term232.
Proof. exact (MK_COMB (@lem5246697) (@lem5246692)). Qed.
Lemma lem5246700 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246701 : term232 = term238.
Proof. exact (@lem5246700 (NUMERAL 0) term85). Qed.
Lemma lem5246702 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246703 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246704 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246703 h1) (fun h1 : term238 = True => @lem5246702)). Qed.
Lemma lem5246705 : term238 = True.
Proof. exact (EQ_MP (@lem5246704) (@lem5246702)). Qed.
Lemma lem5246706 : term232 = True.
Proof. exact (TRANS (@lem5246701) (@lem5246705)). Qed.
Lemma lem5246707 : term241 = True.
Proof. exact (TRANS (@lem5246698) (@lem5246706)). Qed.
Lemma lem5246708 : term235 = True.
Proof. exact (TRANS (@lem5246684) (@lem5246707)). Qed.
Lemma lem5246709 : term232 = True.
Proof. exact (TRANS (@lem5246661) (@lem5246708)). Qed.
Lemma lem5246710 : term231 = True.
Proof. exact (TRANS (@lem5246652) (@lem5246709)). Qed.
Lemma lem5246711 : True = term231.
Proof. exact (SYM (@lem5246710)). Qed.
Lemma lem5246712 : term231.
Proof. exact (EQ_MP (@lem5246711) (@lem0)). Qed.
Lemma lem5246713 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term245 e l x.
Proof. exact (conj (@lem5246712) (@lem5246649 e l x h1)). Qed.
Lemma lem5246715 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5246716 (e : real) (l : real) (x : real) : term247 e l x.
Proof. exact (@lem5246715 term91 (term108 e l x)). Qed.
Lemma lem5246717 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term248 e l x.
Proof. exact (@lem5246716 e l x (@lem5246713 e l x h1)). Qed.
Lemma lem5246718 (e : real) (l : real) (x : real) : (term249 e l x) = (term108 e l x).
Proof. exact (@lem1982733 (term108 e l x)). Qed.
Lemma lem5246719 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5246720 (e : real) (l : real) (x : real) : (term250 e l x) = (term110 e l x).
Proof. exact (MK_COMB (@lem5246719) (@lem5246718 e l x)). Qed.
Lemma lem5246721 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5246722 (e : real) (l : real) (x : real) : (term248 e l x) = (term111 e l x).
Proof. exact (MK_COMB (@lem5246720 e l x) (@lem5246721)). Qed.
Lemma lem5246723 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term111 e l x.
Proof. exact (EQ_MP (@lem5246722 e l x) (@lem5246717 e l x h1)). Qed.
Lemma lem5246725 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5246726 : term231 = term232.
Proof. exact (@lem5246725 term32 term91). Qed.
Lemma lem5246728 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246729 : term91 = term101.
Proof. exact (@lem5246728 term85). Qed.
Lemma lem5246731 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246732 : term32 = term172.
Proof. exact (@lem5246731 (NUMERAL 0)). Qed.
Lemma lem5246733 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5246734 : term233 = term234.
Proof. exact (MK_COMB (@lem5246733) (@lem5246732)). Qed.
Lemma lem5246735 : term232 = term235.
Proof. exact (MK_COMB (@lem5246734) (@lem5246729)). Qed.
Lemma lem5246736 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5246738 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246739 : term232 = term238.
Proof. exact (@lem5246738 (NUMERAL 0) term85). Qed.
Lemma lem5246740 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246741 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246742 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246741 h1) (fun h1 : term238 = True => @lem5246740)). Qed.
Lemma lem5246743 : term238 = True.
Proof. exact (EQ_MP (@lem5246742) (@lem5246740)). Qed.
Lemma lem5246744 : term232 = True.
Proof. exact (TRANS (@lem5246739) (@lem5246743)). Qed.
Lemma lem5246745 : True = term232.
Proof. exact (SYM (@lem5246744)). Qed.
Lemma lem5246746 : term232.
Proof. exact (EQ_MP (@lem5246745) (@lem0)). Qed.
Lemma lem5246747 : term240.
Proof. exact (@lem5246736 (@lem5246746)). Qed.
Lemma lem5246749 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246750 : term232 = term238.
Proof. exact (@lem5246749 (NUMERAL 0) term85). Qed.
Lemma lem5246751 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246752 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246753 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246752 h1) (fun h1 : term238 = True => @lem5246751)). Qed.
Lemma lem5246754 : term238 = True.
Proof. exact (EQ_MP (@lem5246753) (@lem5246751)). Qed.
Lemma lem5246755 : term232 = True.
Proof. exact (TRANS (@lem5246750) (@lem5246754)). Qed.
Lemma lem5246756 : True = term232.
Proof. exact (SYM (@lem5246755)). Qed.
Lemma lem5246757 : term232.
Proof. exact (EQ_MP (@lem5246756) (@lem0)). Qed.
Lemma lem5246758 : term235 = term241.
Proof. exact (@lem5246747 (@lem5246757)). Qed.
Lemma lem5246760 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5246761 : term94 = term95.
Proof. exact (@lem5246760 term85 term85). Qed.
Lemma lem5246762 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246763 : term97 = term85.
Proof. exact (EQ_MP (@lem5246762) (@lem940073)). Qed.
Lemma lem5246764 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246765 : term95 = term91.
Proof. exact (MK_COMB (@lem5246764) (@lem5246763)). Qed.
Lemma lem5246766 : term94 = term91.
Proof. exact (TRANS (@lem5246761) (@lem5246765)). Qed.
Lemma lem5246768 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246769 : term243 = term32.
Proof. exact (@lem5246768 term85). Qed.
Lemma lem5246770 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5246771 : term244 = term233.
Proof. exact (MK_COMB (@lem5246770) (@lem5246769)). Qed.
Lemma lem5246772 : term241 = term232.
Proof. exact (MK_COMB (@lem5246771) (@lem5246766)). Qed.
Lemma lem5246774 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246775 : term232 = term238.
Proof. exact (@lem5246774 (NUMERAL 0) term85). Qed.
Lemma lem5246776 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246777 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246778 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246777 h1) (fun h1 : term238 = True => @lem5246776)). Qed.
Lemma lem5246779 : term238 = True.
Proof. exact (EQ_MP (@lem5246778) (@lem5246776)). Qed.
Lemma lem5246780 : term232 = True.
Proof. exact (TRANS (@lem5246775) (@lem5246779)). Qed.
Lemma lem5246781 : term241 = True.
Proof. exact (TRANS (@lem5246772) (@lem5246780)). Qed.
Lemma lem5246782 : term235 = True.
Proof. exact (TRANS (@lem5246758) (@lem5246781)). Qed.
Lemma lem5246783 : term232 = True.
Proof. exact (TRANS (@lem5246735) (@lem5246782)). Qed.
Lemma lem5246784 : term231 = True.
Proof. exact (TRANS (@lem5246726) (@lem5246783)). Qed.
Lemma lem5246785 : True = term231.
Proof. exact (SYM (@lem5246784)). Qed.
Lemma lem5246786 : term231.
Proof. exact (EQ_MP (@lem5246785) (@lem0)). Qed.
Lemma lem5246787 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term251 e l x.
Proof. exact (conj (@lem5246786) (@lem5246647 e l x h1)). Qed.
Lemma lem5246789 (x : real) (y : real) : term252 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5246790 (e : real) (l : real) (x : real) : term253 e l x.
Proof. exact (@lem5246789 term91 (term41 e l x)). Qed.
Lemma lem5246791 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term254 e l x.
Proof. exact (@lem5246790 e l x (@lem5246787 e l x h1)). Qed.
Lemma lem5246792 (e : real) (l : real) (x : real) : (term255 e l x) = (term41 e l x).
Proof. exact (@lem1982733 (term41 e l x)). Qed.
Lemma lem5246793 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5246794 (e : real) (l : real) (x : real) : (term256 e l x) = (term43 e l x).
Proof. exact (MK_COMB (@lem5246793) (@lem5246792 e l x)). Qed.
Lemma lem5246795 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5246796 (e : real) (l : real) (x : real) : (term254 e l x) = (term44 e l x).
Proof. exact (MK_COMB (@lem5246794 e l x) (@lem5246795)). Qed.
Lemma lem5246797 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term44 e l x.
Proof. exact (EQ_MP (@lem5246796 e l x) (@lem5246791 e l x h1)). Qed.
Lemma lem5246798 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term257 e l x.
Proof. exact (conj (@lem5246797 e l x h1) (@lem5246723 e l x h1)). Qed.
Lemma lem5246800 (x : real) (y : real) : term258 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5246801 (e : real) (l : real) (x : real) : term259 e l x.
Proof. exact (@lem5246800 (term41 e l x) (term108 e l x)). Qed.
Lemma lem5246802 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term260 e l x.
Proof. exact (@lem5246801 e l x (@lem5246798 e l x h1)). Qed.
Lemma lem5246803 (e : real) (l : real) (x : real) : (term261 e l x) = (term262 e l x).
Proof. exact (@lem1982753 (term25 e) e (term23 l x) (term24 l x)). Qed.
Lemma lem5246804 (e : real) : (term263 e) = (term264 e).
Proof. exact (@lem1982713 term51 e). Qed.
Lemma lem5246806 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246807 : term91 = term101.
Proof. exact (@lem5246806 term85). Qed.
Lemma lem5246809 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5246810 : term51 = term84.
Proof. exact (@lem5246809 term85). Qed.
Lemma lem5246811 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5246812 : term265 = term266.
Proof. exact (MK_COMB (@lem5246811) (@lem5246810)). Qed.
Lemma lem5246813 : term267 = term268.
Proof. exact (MK_COMB (@lem5246812) (@lem5246807)). Qed.
Lemma lem5246814 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5246816 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246817 : term232 = term238.
Proof. exact (@lem5246816 (NUMERAL 0) term85). Qed.
Lemma lem5246818 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246819 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246820 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246819 h1) (fun h1 : term238 = True => @lem5246818)). Qed.
Lemma lem5246821 : term238 = True.
Proof. exact (EQ_MP (@lem5246820) (@lem5246818)). Qed.
Lemma lem5246822 : term232 = True.
Proof. exact (TRANS (@lem5246817) (@lem5246821)). Qed.
Lemma lem5246823 : True = term232.
Proof. exact (SYM (@lem5246822)). Qed.
Lemma lem5246824 : term232.
Proof. exact (EQ_MP (@lem5246823) (@lem0)). Qed.
Lemma lem5246825 : term270.
Proof. exact (@lem5246814 (@lem5246824)). Qed.
Lemma lem5246827 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246828 : term232 = term238.
Proof. exact (@lem5246827 (NUMERAL 0) term85). Qed.
Lemma lem5246829 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246830 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246831 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246830 h1) (fun h1 : term238 = True => @lem5246829)). Qed.
Lemma lem5246832 : term238 = True.
Proof. exact (EQ_MP (@lem5246831) (@lem5246829)). Qed.
Lemma lem5246833 : term232 = True.
Proof. exact (TRANS (@lem5246828) (@lem5246832)). Qed.
Lemma lem5246834 : True = term232.
Proof. exact (SYM (@lem5246833)). Qed.
Lemma lem5246835 : term232.
Proof. exact (EQ_MP (@lem5246834) (@lem0)). Qed.
Lemma lem5246836 : term271.
Proof. exact (@lem5246825 (@lem5246835)). Qed.
Lemma lem5246838 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246839 : term232 = term238.
Proof. exact (@lem5246838 (NUMERAL 0) term85). Qed.
Lemma lem5246840 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246841 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246842 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246841 h1) (fun h1 : term238 = True => @lem5246840)). Qed.
Lemma lem5246843 : term238 = True.
Proof. exact (EQ_MP (@lem5246842) (@lem5246840)). Qed.
Lemma lem5246844 : term232 = True.
Proof. exact (TRANS (@lem5246839) (@lem5246843)). Qed.
Lemma lem5246845 : True = term232.
Proof. exact (SYM (@lem5246844)). Qed.
Lemma lem5246846 : term232.
Proof. exact (EQ_MP (@lem5246845) (@lem0)). Qed.
Lemma lem5246847 : term272.
Proof. exact (@lem5246836 (@lem5246846)). Qed.
Lemma lem5246849 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5246850 : term94 = term95.
Proof. exact (@lem5246849 term85 term85). Qed.
Lemma lem5246851 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246852 : term97 = term85.
Proof. exact (EQ_MP (@lem5246851) (@lem940073)). Qed.
Lemma lem5246853 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246854 : term95 = term91.
Proof. exact (MK_COMB (@lem5246853) (@lem5246852)). Qed.
Lemma lem5246855 : term94 = term91.
Proof. exact (TRANS (@lem5246850) (@lem5246854)). Qed.
Lemma lem5246857 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5246858 : term275 = term276.
Proof. exact (@lem5246857 term85 term85). Qed.
Lemma lem5246859 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246860 : term97 = term85.
Proof. exact (EQ_MP (@lem5246859) (@lem940073)). Qed.
Lemma lem5246861 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246862 : term95 = term91.
Proof. exact (MK_COMB (@lem5246861) (@lem5246860)). Qed.
Lemma lem5246863 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5246864 : term276 = term51.
Proof. exact (MK_COMB (@lem5246863) (@lem5246862)). Qed.
Lemma lem5246865 : term275 = term51.
Proof. exact (TRANS (@lem5246858) (@lem5246864)). Qed.
Lemma lem5246866 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5246867 : term277 = term265.
Proof. exact (MK_COMB (@lem5246866) (@lem5246865)). Qed.
Lemma lem5246868 : term278 = term267.
Proof. exact (MK_COMB (@lem5246867) (@lem5246855)). Qed.
Lemma lem5246870 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5246871 : term267 = term32.
Proof. exact (@lem5246870 term85). Qed.
Lemma lem5246872 : term278 = term32.
Proof. exact (TRANS (@lem5246868) (@lem5246871)). Qed.
Lemma lem5246873 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5246874 : term280 = term281.
Proof. exact (MK_COMB (@lem5246873) (@lem5246872)). Qed.
Lemma lem5246875 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5246876 : term282 = term243.
Proof. exact (MK_COMB (@lem5246874) (@lem5246875)). Qed.
Lemma lem5246878 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246879 : term243 = term32.
Proof. exact (@lem5246878 term85). Qed.
Lemma lem5246880 : term282 = term32.
Proof. exact (TRANS (@lem5246876) (@lem5246879)). Qed.
Lemma lem5246882 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5246883 : term94 = term95.
Proof. exact (@lem5246882 term85 term85). Qed.
Lemma lem5246884 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246885 : term97 = term85.
Proof. exact (EQ_MP (@lem5246884) (@lem940073)). Qed.
Lemma lem5246886 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246887 : term95 = term91.
Proof. exact (MK_COMB (@lem5246886) (@lem5246885)). Qed.
Lemma lem5246888 : term94 = term91.
Proof. exact (TRANS (@lem5246883) (@lem5246887)). Qed.
Lemma lem5246889 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5246890 : term283 = term243.
Proof. exact (MK_COMB (@lem5246889) (@lem5246888)). Qed.
Lemma lem5246892 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246893 : term243 = term32.
Proof. exact (@lem5246892 term85). Qed.
Lemma lem5246894 : term283 = term32.
Proof. exact (TRANS (@lem5246890) (@lem5246893)). Qed.
Lemma lem5246895 : term32 = term283.
Proof. exact (SYM (@lem5246894)). Qed.
Lemma lem5246896 : term282 = term283.
Proof. exact (TRANS (@lem5246880) (@lem5246895)). Qed.
Lemma lem5246897 : term268 = term172.
Proof. exact (@lem5246847 (@lem5246896)). Qed.
Lemma lem5246898 : term267 = term172.
Proof. exact (TRANS (@lem5246813) (@lem5246897)). Qed.
Lemma lem5246900 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5246901 : term172 = term32.
Proof. exact (@lem5246900 term32). Qed.
Lemma lem5246902 : term267 = term32.
Proof. exact (TRANS (@lem5246898) (@lem5246901)). Qed.
Lemma lem5246903 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5246904 : term284 = term281.
Proof. exact (MK_COMB (@lem5246903) (@lem5246902)). Qed.
Lemma lem5246905 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem5246906 (e : real) : (term264 e) = (term285 e).
Proof. exact (MK_COMB (@lem5246904) (@lem5246905 e)). Qed.
Lemma lem5246907 (e : real) : (term263 e) = (term285 e).
Proof. exact (TRANS (@lem5246804 e) (@lem5246906 e)). Qed.
Lemma lem5246908 (e : real) : (term285 e) = term32.
Proof. exact (@lem1982719 e). Qed.
Lemma lem5246909 (e : real) : (term263 e) = term32.
Proof. exact (TRANS (@lem5246907 e) (@lem5246908 e)). Qed.
Lemma lem5246910 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5246911 (e : real) : (term286 e) = term206.
Proof. exact (MK_COMB (@lem5246910) (@lem5246909 e)). Qed.
Lemma lem5246912 (l : real) (x : real) : (term287 l x) = (term288 l x).
Proof. exact (@lem1982753 l (term25 l) (term25 x) x). Qed.
Lemma lem5246913 (l : real) : (term289 l) = (term264 l).
Proof. exact (@lem1982715 term51 l). Qed.
Lemma lem5246915 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5246916 : term91 = term101.
Proof. exact (@lem5246915 term85). Qed.
Lemma lem5246918 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5246919 : term51 = term84.
Proof. exact (@lem5246918 term85). Qed.
Lemma lem5246920 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5246921 : term265 = term266.
Proof. exact (MK_COMB (@lem5246920) (@lem5246919)). Qed.
Lemma lem5246922 : term267 = term268.
Proof. exact (MK_COMB (@lem5246921) (@lem5246916)). Qed.
Lemma lem5246923 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5246925 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246926 : term232 = term238.
Proof. exact (@lem5246925 (NUMERAL 0) term85). Qed.
Lemma lem5246927 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246928 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246929 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246928 h1) (fun h1 : term238 = True => @lem5246927)). Qed.
Lemma lem5246930 : term238 = True.
Proof. exact (EQ_MP (@lem5246929) (@lem5246927)). Qed.
Lemma lem5246931 : term232 = True.
Proof. exact (TRANS (@lem5246926) (@lem5246930)). Qed.
Lemma lem5246932 : True = term232.
Proof. exact (SYM (@lem5246931)). Qed.
Lemma lem5246933 : term232.
Proof. exact (EQ_MP (@lem5246932) (@lem0)). Qed.
Lemma lem5246934 : term270.
Proof. exact (@lem5246923 (@lem5246933)). Qed.
Lemma lem5246936 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246937 : term232 = term238.
Proof. exact (@lem5246936 (NUMERAL 0) term85). Qed.
Lemma lem5246938 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246939 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246940 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246939 h1) (fun h1 : term238 = True => @lem5246938)). Qed.
Lemma lem5246941 : term238 = True.
Proof. exact (EQ_MP (@lem5246940) (@lem5246938)). Qed.
Lemma lem5246942 : term232 = True.
Proof. exact (TRANS (@lem5246937) (@lem5246941)). Qed.
Lemma lem5246943 : True = term232.
Proof. exact (SYM (@lem5246942)). Qed.
Lemma lem5246944 : term232.
Proof. exact (EQ_MP (@lem5246943) (@lem0)). Qed.
Lemma lem5246945 : term271.
Proof. exact (@lem5246934 (@lem5246944)). Qed.
Lemma lem5246947 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5246948 : term232 = term238.
Proof. exact (@lem5246947 (NUMERAL 0) term85). Qed.
Lemma lem5246949 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5246950 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5246951 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5246950 h1) (fun h1 : term238 = True => @lem5246949)). Qed.
Lemma lem5246952 : term238 = True.
Proof. exact (EQ_MP (@lem5246951) (@lem5246949)). Qed.
Lemma lem5246953 : term232 = True.
Proof. exact (TRANS (@lem5246948) (@lem5246952)). Qed.
Lemma lem5246954 : True = term232.
Proof. exact (SYM (@lem5246953)). Qed.
Lemma lem5246955 : term232.
Proof. exact (EQ_MP (@lem5246954) (@lem0)). Qed.
Lemma lem5246956 : term272.
Proof. exact (@lem5246945 (@lem5246955)). Qed.
Lemma lem5246958 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5246959 : term94 = term95.
Proof. exact (@lem5246958 term85 term85). Qed.
Lemma lem5246960 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246961 : term97 = term85.
Proof. exact (EQ_MP (@lem5246960) (@lem940073)). Qed.
Lemma lem5246962 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246963 : term95 = term91.
Proof. exact (MK_COMB (@lem5246962) (@lem5246961)). Qed.
Lemma lem5246964 : term94 = term91.
Proof. exact (TRANS (@lem5246959) (@lem5246963)). Qed.
Lemma lem5246966 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5246967 : term275 = term276.
Proof. exact (@lem5246966 term85 term85). Qed.
Lemma lem5246968 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246969 : term97 = term85.
Proof. exact (EQ_MP (@lem5246968) (@lem940073)). Qed.
Lemma lem5246970 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246971 : term95 = term91.
Proof. exact (MK_COMB (@lem5246970) (@lem5246969)). Qed.
Lemma lem5246972 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5246973 : term276 = term51.
Proof. exact (MK_COMB (@lem5246972) (@lem5246971)). Qed.
Lemma lem5246974 : term275 = term51.
Proof. exact (TRANS (@lem5246967) (@lem5246973)). Qed.
Lemma lem5246975 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5246976 : term277 = term265.
Proof. exact (MK_COMB (@lem5246975) (@lem5246974)). Qed.
Lemma lem5246977 : term278 = term267.
Proof. exact (MK_COMB (@lem5246976) (@lem5246964)). Qed.
Lemma lem5246979 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5246980 : term267 = term32.
Proof. exact (@lem5246979 term85). Qed.
Lemma lem5246981 : term278 = term32.
Proof. exact (TRANS (@lem5246977) (@lem5246980)). Qed.
Lemma lem5246982 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5246983 : term280 = term281.
Proof. exact (MK_COMB (@lem5246982) (@lem5246981)). Qed.
Lemma lem5246984 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5246985 : term282 = term243.
Proof. exact (MK_COMB (@lem5246983) (@lem5246984)). Qed.
Lemma lem5246987 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5246988 : term243 = term32.
Proof. exact (@lem5246987 term85). Qed.
Lemma lem5246989 : term282 = term32.
Proof. exact (TRANS (@lem5246985) (@lem5246988)). Qed.
Lemma lem5246991 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5246992 : term94 = term95.
Proof. exact (@lem5246991 term85 term85). Qed.
Lemma lem5246993 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5246994 : term97 = term85.
Proof. exact (EQ_MP (@lem5246993) (@lem940073)). Qed.
Lemma lem5246995 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5246996 : term95 = term91.
Proof. exact (MK_COMB (@lem5246995) (@lem5246994)). Qed.
Lemma lem5246997 : term94 = term91.
Proof. exact (TRANS (@lem5246992) (@lem5246996)). Qed.
Lemma lem5246998 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5246999 : term283 = term243.
Proof. exact (MK_COMB (@lem5246998) (@lem5246997)). Qed.
Lemma lem5247001 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5247002 : term243 = term32.
Proof. exact (@lem5247001 term85). Qed.
Lemma lem5247003 : term283 = term32.
Proof. exact (TRANS (@lem5246999) (@lem5247002)). Qed.
Lemma lem5247004 : term32 = term283.
Proof. exact (SYM (@lem5247003)). Qed.
Lemma lem5247005 : term282 = term283.
Proof. exact (TRANS (@lem5246989) (@lem5247004)). Qed.
Lemma lem5247006 : term268 = term172.
Proof. exact (@lem5246956 (@lem5247005)). Qed.
Lemma lem5247007 : term267 = term172.
Proof. exact (TRANS (@lem5246922) (@lem5247006)). Qed.
Lemma lem5247009 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5247010 : term172 = term32.
Proof. exact (@lem5247009 term32). Qed.
Lemma lem5247011 : term267 = term32.
Proof. exact (TRANS (@lem5247007) (@lem5247010)). Qed.
Lemma lem5247012 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5247013 : term284 = term281.
Proof. exact (MK_COMB (@lem5247012) (@lem5247011)). Qed.
Lemma lem5247014 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5247015 (l : real) : (term264 l) = (term285 l).
Proof. exact (MK_COMB (@lem5247013) (@lem5247014 l)). Qed.
Lemma lem5247016 (l : real) : (term289 l) = (term285 l).
Proof. exact (TRANS (@lem5246913 l) (@lem5247015 l)). Qed.
Lemma lem5247017 (l : real) : (term285 l) = term32.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5247018 (l : real) : (term289 l) = term32.
Proof. exact (TRANS (@lem5247016 l) (@lem5247017 l)). Qed.
Lemma lem5247019 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5247020 (l : real) : (term290 l) = term206.
Proof. exact (MK_COMB (@lem5247019) (@lem5247018 l)). Qed.
Lemma lem5247021 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1982713 term51 x). Qed.
Lemma lem5247023 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5247024 : term91 = term101.
Proof. exact (@lem5247023 term85). Qed.
Lemma lem5247026 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5247027 : term51 = term84.
Proof. exact (@lem5247026 term85). Qed.
Lemma lem5247028 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5247029 : term265 = term266.
Proof. exact (MK_COMB (@lem5247028) (@lem5247027)). Qed.
Lemma lem5247030 : term267 = term268.
Proof. exact (MK_COMB (@lem5247029) (@lem5247024)). Qed.
Lemma lem5247031 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5247033 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5247034 : term232 = term238.
Proof. exact (@lem5247033 (NUMERAL 0) term85). Qed.
Lemma lem5247035 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5247036 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5247037 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5247036 h1) (fun h1 : term238 = True => @lem5247035)). Qed.
Lemma lem5247038 : term238 = True.
Proof. exact (EQ_MP (@lem5247037) (@lem5247035)). Qed.
Lemma lem5247039 : term232 = True.
Proof. exact (TRANS (@lem5247034) (@lem5247038)). Qed.
Lemma lem5247040 : True = term232.
Proof. exact (SYM (@lem5247039)). Qed.
Lemma lem5247041 : term232.
Proof. exact (EQ_MP (@lem5247040) (@lem0)). Qed.
Lemma lem5247042 : term270.
Proof. exact (@lem5247031 (@lem5247041)). Qed.
Lemma lem5247044 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5247045 : term232 = term238.
Proof. exact (@lem5247044 (NUMERAL 0) term85). Qed.
Lemma lem5247046 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5247047 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5247048 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5247047 h1) (fun h1 : term238 = True => @lem5247046)). Qed.
Lemma lem5247049 : term238 = True.
Proof. exact (EQ_MP (@lem5247048) (@lem5247046)). Qed.
Lemma lem5247050 : term232 = True.
Proof. exact (TRANS (@lem5247045) (@lem5247049)). Qed.
Lemma lem5247051 : True = term232.
Proof. exact (SYM (@lem5247050)). Qed.
Lemma lem5247052 : term232.
Proof. exact (EQ_MP (@lem5247051) (@lem0)). Qed.
Lemma lem5247053 : term271.
Proof. exact (@lem5247042 (@lem5247052)). Qed.
Lemma lem5247055 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5247056 : term232 = term238.
Proof. exact (@lem5247055 (NUMERAL 0) term85). Qed.
Lemma lem5247057 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5247058 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5247059 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5247058 h1) (fun h1 : term238 = True => @lem5247057)). Qed.
Lemma lem5247060 : term238 = True.
Proof. exact (EQ_MP (@lem5247059) (@lem5247057)). Qed.
Lemma lem5247061 : term232 = True.
Proof. exact (TRANS (@lem5247056) (@lem5247060)). Qed.
Lemma lem5247062 : True = term232.
Proof. exact (SYM (@lem5247061)). Qed.
Lemma lem5247063 : term232.
Proof. exact (EQ_MP (@lem5247062) (@lem0)). Qed.
Lemma lem5247064 : term272.
Proof. exact (@lem5247053 (@lem5247063)). Qed.
Lemma lem5247066 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5247067 : term94 = term95.
Proof. exact (@lem5247066 term85 term85). Qed.
Lemma lem5247068 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5247069 : term97 = term85.
Proof. exact (EQ_MP (@lem5247068) (@lem940073)). Qed.
Lemma lem5247070 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5247071 : term95 = term91.
Proof. exact (MK_COMB (@lem5247070) (@lem5247069)). Qed.
Lemma lem5247072 : term94 = term91.
Proof. exact (TRANS (@lem5247067) (@lem5247071)). Qed.
Lemma lem5247074 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5247075 : term275 = term276.
Proof. exact (@lem5247074 term85 term85). Qed.
Lemma lem5247076 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5247077 : term97 = term85.
Proof. exact (EQ_MP (@lem5247076) (@lem940073)). Qed.
Lemma lem5247078 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5247079 : term95 = term91.
Proof. exact (MK_COMB (@lem5247078) (@lem5247077)). Qed.
Lemma lem5247080 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5247081 : term276 = term51.
Proof. exact (MK_COMB (@lem5247080) (@lem5247079)). Qed.
Lemma lem5247082 : term275 = term51.
Proof. exact (TRANS (@lem5247075) (@lem5247081)). Qed.
Lemma lem5247083 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5247084 : term277 = term265.
Proof. exact (MK_COMB (@lem5247083) (@lem5247082)). Qed.
Lemma lem5247085 : term278 = term267.
Proof. exact (MK_COMB (@lem5247084) (@lem5247072)). Qed.
Lemma lem5247087 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5247088 : term267 = term32.
Proof. exact (@lem5247087 term85). Qed.
Lemma lem5247089 : term278 = term32.
Proof. exact (TRANS (@lem5247085) (@lem5247088)). Qed.
Lemma lem5247090 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5247091 : term280 = term281.
Proof. exact (MK_COMB (@lem5247090) (@lem5247089)). Qed.
Lemma lem5247092 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5247093 : term282 = term243.
Proof. exact (MK_COMB (@lem5247091) (@lem5247092)). Qed.
Lemma lem5247095 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5247096 : term243 = term32.
Proof. exact (@lem5247095 term85). Qed.
Lemma lem5247097 : term282 = term32.
Proof. exact (TRANS (@lem5247093) (@lem5247096)). Qed.
Lemma lem5247099 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5247100 : term94 = term95.
Proof. exact (@lem5247099 term85 term85). Qed.
Lemma lem5247101 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5247102 : term97 = term85.
Proof. exact (EQ_MP (@lem5247101) (@lem940073)). Qed.
Lemma lem5247103 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5247104 : term95 = term91.
Proof. exact (MK_COMB (@lem5247103) (@lem5247102)). Qed.
Lemma lem5247105 : term94 = term91.
Proof. exact (TRANS (@lem5247100) (@lem5247104)). Qed.
Lemma lem5247106 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5247107 : term283 = term243.
Proof. exact (MK_COMB (@lem5247106) (@lem5247105)). Qed.
Lemma lem5247109 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5247110 : term243 = term32.
Proof. exact (@lem5247109 term85). Qed.
Lemma lem5247111 : term283 = term32.
Proof. exact (TRANS (@lem5247107) (@lem5247110)). Qed.
Lemma lem5247112 : term32 = term283.
Proof. exact (SYM (@lem5247111)). Qed.
Lemma lem5247113 : term282 = term283.
Proof. exact (TRANS (@lem5247097) (@lem5247112)). Qed.
Lemma lem5247114 : term268 = term172.
Proof. exact (@lem5247064 (@lem5247113)). Qed.
Lemma lem5247115 : term267 = term172.
Proof. exact (TRANS (@lem5247030) (@lem5247114)). Qed.
Lemma lem5247117 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5247118 : term172 = term32.
Proof. exact (@lem5247117 term32). Qed.
Lemma lem5247119 : term267 = term32.
Proof. exact (TRANS (@lem5247115) (@lem5247118)). Qed.
Lemma lem5247120 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5247121 : term284 = term281.
Proof. exact (MK_COMB (@lem5247120) (@lem5247119)). Qed.
Lemma lem5247122 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5247123 (x : real) : (term264 x) = (term285 x).
Proof. exact (MK_COMB (@lem5247121) (@lem5247122 x)). Qed.
Lemma lem5247124 (x : real) : (term263 x) = (term285 x).
Proof. exact (TRANS (@lem5247021 x) (@lem5247123 x)). Qed.
Lemma lem5247125 (x : real) : (term285 x) = term32.
Proof. exact (@lem1982719 x). Qed.
Lemma lem5247126 (x : real) : (term263 x) = term32.
Proof. exact (TRANS (@lem5247124 x) (@lem5247125 x)). Qed.
Lemma lem5247127 (l : real) (x : real) : (term288 l x) = term291.
Proof. exact (MK_COMB (@lem5247020 l) (@lem5247126 x)). Qed.
Lemma lem5247128 (l : real) (x : real) : (term287 l x) = term291.
Proof. exact (TRANS (@lem5246912 l x) (@lem5247127 l x)). Qed.
Lemma lem5247129 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5247130 (l : real) (x : real) : (term287 l x) = term32.
Proof. exact (TRANS (@lem5247128 l x) (@lem5247129)). Qed.
Lemma lem5247131 (e : real) (l : real) (x : real) : (term262 e l x) = term291.
Proof. exact (MK_COMB (@lem5246911 e) (@lem5247130 l x)). Qed.
Lemma lem5247132 (e : real) (l : real) (x : real) : (term261 e l x) = term291.
Proof. exact (TRANS (@lem5246803 e l x) (@lem5247131 e l x)). Qed.
Lemma lem5247133 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5247134 (e : real) (l : real) (x : real) : (term261 e l x) = term32.
Proof. exact (TRANS (@lem5247132 e l x) (@lem5247133)). Qed.
Lemma lem5247135 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5247136 (e : real) (l : real) (x : real) : (term292 e l x) = term293.
Proof. exact (MK_COMB (@lem5247135) (@lem5247134 e l x)). Qed.
Lemma lem5247137 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5247138 (e : real) (l : real) (x : real) : (term260 e l x) = term294.
Proof. exact (MK_COMB (@lem5247136 e l x) (@lem5247137)). Qed.
Lemma lem5247139 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term294.
Proof. exact (EQ_MP (@lem5247138 e l x) (@lem5246802 e l x h1)). Qed.
Lemma lem5247141 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5247142 : term294 = term295.
Proof. exact (@lem5247141 term32 term32). Qed.
Lemma lem5247144 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5247145 : term32 = term172.
Proof. exact (@lem5247144 (NUMERAL 0)). Qed.
Lemma lem5247147 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5247148 : term32 = term172.
Proof. exact (@lem5247147 (NUMERAL 0)). Qed.
Lemma lem5247149 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5247150 : term233 = term234.
Proof. exact (MK_COMB (@lem5247149) (@lem5247148)). Qed.
Lemma lem5247151 : term295 = term296.
Proof. exact (MK_COMB (@lem5247150) (@lem5247145)). Qed.
Lemma lem5247152 : term297.
Proof. exact (@lem1980255 term32 term91 term32 term91). Qed.
Lemma lem5247154 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5247155 : term232 = term238.
Proof. exact (@lem5247154 (NUMERAL 0) term85). Qed.
Lemma lem5247156 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5247157 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5247158 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5247157 h1) (fun h1 : term238 = True => @lem5247156)). Qed.
Lemma lem5247159 : term238 = True.
Proof. exact (EQ_MP (@lem5247158) (@lem5247156)). Qed.
Lemma lem5247160 : term232 = True.
Proof. exact (TRANS (@lem5247155) (@lem5247159)). Qed.
Lemma lem5247161 : True = term232.
Proof. exact (SYM (@lem5247160)). Qed.
Lemma lem5247162 : term232.
Proof. exact (EQ_MP (@lem5247161) (@lem0)). Qed.
Lemma lem5247163 : term298.
Proof. exact (@lem5247152 (@lem5247162)). Qed.
Lemma lem5247165 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5247166 : term232 = term238.
Proof. exact (@lem5247165 (NUMERAL 0) term85). Qed.
Lemma lem5247167 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5247168 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5247169 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5247168 h1) (fun h1 : term238 = True => @lem5247167)). Qed.
Lemma lem5247170 : term238 = True.
Proof. exact (EQ_MP (@lem5247169) (@lem5247167)). Qed.
Lemma lem5247171 : term232 = True.
Proof. exact (TRANS (@lem5247166) (@lem5247170)). Qed.
Lemma lem5247172 : True = term232.
Proof. exact (SYM (@lem5247171)). Qed.
Lemma lem5247173 : term232.
Proof. exact (EQ_MP (@lem5247172) (@lem0)). Qed.
Lemma lem5247174 : term296 = term299.
Proof. exact (@lem5247163 (@lem5247173)). Qed.
Lemma lem5247176 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5247177 : term243 = term32.
Proof. exact (@lem5247176 term85). Qed.
Lemma lem5247179 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5247180 : term243 = term32.
Proof. exact (@lem5247179 term85). Qed.
Lemma lem5247181 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5247182 : term244 = term233.
Proof. exact (MK_COMB (@lem5247181) (@lem5247180)). Qed.
Lemma lem5247183 : term299 = term295.
Proof. exact (MK_COMB (@lem5247182) (@lem5247177)). Qed.
Lemma lem5247185 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5247186 : term295 = term300.
Proof. exact (@lem5247185 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5247187 : term300 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5247188 : term295 = False.
Proof. exact (TRANS (@lem5247186) (@lem5247187)). Qed.
Lemma lem5247189 : term299 = False.
Proof. exact (TRANS (@lem5247183) (@lem5247188)). Qed.
Lemma lem5247190 : term296 = False.
Proof. exact (TRANS (@lem5247174) (@lem5247189)). Qed.
Lemma lem5247191 : term295 = False.
Proof. exact (TRANS (@lem5247151) (@lem5247190)). Qed.
Lemma lem5247192 : term294 = False.
Proof. exact (TRANS (@lem5247142) (@lem5247191)). Qed.
Lemma lem5247193 (e : real) (l : real) (x : real) (h1 : term227 e l x) : False.
Proof. exact (EQ_MP (@lem5247192) (@lem5247139 e l x h1)). Qed.
Lemma lem5247194 (e : real) (l : real) (x : real) (h1 : term228 e l x) : False.
Proof. exact (or_elim (@lem5246091 e l x h1) (fun h0 : term162 e l x => @lem5246642 e l x h0) (fun h0 : term227 e l x => @lem5247193 e l x h0)). Qed.
Lemma lem5247195 (e : real) (l : real) (x : real) (h1 : term230 e l x) : False.
Proof. exact (or_elim (@lem5244990 e l x h1) (fun h0 : term149 e l x => @lem5246090 e l x h0) (fun h0 : term228 e l x => @lem5247194 e l x h0)). Qed.
Lemma lem5247196 (e : real) (l : real) (x : real) (h1 : term129 e l x) : term129 e l x.
Proof. exact (h1). Qed.
Lemma lem5247197 (e : real) (l : real) (x : real) (h1 : term129 e l x) : term230 e l x.
Proof. exact (EQ_MP (@lem5244989 e l x) (@lem5247196 e l x h1)). Qed.
Lemma lem5247198 (e : real) (l : real) (x : real) (h1 : term129 e l x) : (term230 e l x) = False.
Proof. exact (prop_ext (fun h2 : term230 e l x => @lem5247195 e l x h2) (fun h2 : False => @lem5247197 e l x h1)). Qed.
Lemma lem5247199 (e : real) (l : real) (x : real) (h1 : term129 e l x) : False.
Proof. exact (EQ_MP (@lem5247198 e l x h1) (@lem5247197 e l x h1)). Qed.
Lemma lem5247200 (x : real) (l : real) (e : real) (h1 : term18 x l e) : term18 x l e.
Proof. exact (h1). Qed.
Lemma lem5247201 (x : real) (l : real) (e : real) (h1 : term18 x l e) : term129 e l x.
Proof. exact (EQ_MP (@lem5244226 e l x) (@lem5247200 x l e h1)). Qed.
Lemma lem5247202 (x : real) (l : real) (e : real) (h1 : term18 x l e) : (term129 e l x) = False.
Proof. exact (prop_ext (fun h2 : term129 e l x => @lem5247199 e l x h2) (fun h2 : False => @lem5247201 x l e h1)). Qed.
Lemma lem5247203 (x : real) (l : real) (e : real) (h1 : term18 x l e) : False.
Proof. exact (EQ_MP (@lem5247202 x l e h1) (@lem5247201 x l e h1)). Qed.
Lemma lem5247204 (x : real) (l : real) (e : real) : term319 x l e.
Proof. exact (fun h0 : term18 x l e => @lem5247203 x l e h0). Qed.
Lemma lem5247205 (x : real) (l : real) (e : real) : term320 x l e.
Proof. exact (@lem1386578 ((term19 x l e) = (term20 x l e))). Qed.
Lemma lem5247224 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term321 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5247225 (p : Prop) (q : Prop) (p' : Prop) : term322 p q p'.
Proof. exact (fun q' : Prop => @lem5247224 p q p' q'). Qed.
Lemma lem5247226 (p : Prop) (q : Prop) : term323 p q.
Proof. exact (fun p' : Prop => @lem5247225 p q p'). Qed.
Lemma lem5247227 (s : real -> Prop) (l : real) (e : real) : term324 s l e.
Proof. exact (@lem5247226 (term325 s l e) (term326 s l e)). Qed.
Lemma lem5247228 (s : real -> Prop) (l : real) (e : real) (p' : Prop) : term327 s l e p'.
Proof. exact (@lem5247227 s l e p'). Qed.
Lemma lem5247229 (s : real -> Prop) (l : real) (e : real) (p' : Prop) : (term327 s l e p') = (term328 s l e p').
Proof. exact (eq_refl (term327 s l e p')). Qed.
Lemma lem5247230 (s : real -> Prop) (l : real) (e : real) (p' : Prop) : term328 s l e p'.
Proof. exact (EQ_MP (@lem5247229 s l e p') (@lem5247228 s l e p')). Qed.
Lemma lem5247231 (s : real -> Prop) (l : real) (e : real) (p' : Prop) (q' : Prop) : term329 s l e p' q'.
Proof. exact (@lem5247230 s l e p' q'). Qed.
Lemma lem5247232 (s : real -> Prop) (l : real) (e : real) (p' : Prop) (q' : Prop) : (term329 s l e p' q') = (term330 s l e p' q').
Proof. exact (eq_refl (term329 s l e p' q')). Qed.
Lemma lem5247233 (s : real -> Prop) (l : real) (e : real) (p' : Prop) (q' : Prop) : term330 s l e p' q'.
Proof. exact (EQ_MP (@lem5247232 s l e p' q') (@lem5247231 s l e p' q')). Qed.
Lemma lem5247245 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term321 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5247246 (p : Prop) (q : Prop) (p' : Prop) : term322 p q p'.
Proof. exact (fun q' : Prop => @lem5247245 p q p' q'). Qed.
Lemma lem5247247 (p : Prop) (q : Prop) : term323 p q.
Proof. exact (fun p' : Prop => @lem5247246 p q p'). Qed.
Lemma lem5247248 (s : real -> Prop) (x : real) (l : real) (e : real) : term331 s x l e.
Proof. exact (@lem5247247 (@IN real x s) (term19 x l e)). Qed.
Lemma lem5247249 (s : real -> Prop) (x : real) (l : real) (e : real) (p' : Prop) : term332 s x l e p'.
Proof. exact (@lem5247248 s x l e p'). Qed.
Lemma lem5247250 (s : real -> Prop) (x : real) (l : real) (e : real) (p' : Prop) : (term332 s x l e p') = (term333 s x l e p').
Proof. exact (eq_refl (term332 s x l e p')). Qed.
Lemma lem5247251 (s : real -> Prop) (x : real) (l : real) (e : real) (p' : Prop) : term333 s x l e p'.
Proof. exact (EQ_MP (@lem5247250 s x l e p') (@lem5247249 s x l e p')). Qed.
Lemma lem5247252 (s : real -> Prop) (x : real) (l : real) (e : real) (p' : Prop) (q' : Prop) : term334 s x l e p' q'.
Proof. exact (@lem5247251 s x l e p' q'). Qed.
Lemma lem5247253 (s : real -> Prop) (x : real) (l : real) (e : real) (p' : Prop) (q' : Prop) : (term334 s x l e p' q') = (term335 s x l e p' q').
Proof. exact (eq_refl (term334 s x l e p' q')). Qed.
Lemma lem5247254 (s : real -> Prop) (x : real) (l : real) (e : real) (p' : Prop) (q' : Prop) : term335 s x l e p' q'.
Proof. exact (EQ_MP (@lem5247253 s x l e p' q') (@lem5247252 s x l e p' q')). Qed.
Lemma lem5247255 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5247256 (l : real) (e : real) (x : real) (s : real -> Prop) (q' : Prop) : term336 l e x s q'.
Proof. exact (@lem5247254 s x l e (@IN real x s) q'). Qed.
Lemma lem5247257 (l : real) (e : real) (x : real) (s : real -> Prop) (q' : Prop) : term337 l e x s q'.
Proof. exact (@lem5247256 l e x s q' (@lem5247255 x s)). Qed.
Lemma lem5247262 (x : real) (l : real) (e : real) : (term19 x l e) = (term20 x l e).
Proof. exact (@lem5247205 x l e (@lem5247204 x l e)). Qed.
Lemma lem5247265 (s : real -> Prop) (x : real) (l : real) (e : real) : term338 s x l e.
Proof. exact (fun h0 : @IN real x s => @lem5247262 x l e). Qed.
Lemma lem5247266 (s : real -> Prop) (x : real) (l : real) (e : real) : term339 s x l e.
Proof. exact (@lem5247257 l e x s (term20 x l e)). Qed.
Lemma lem5247267 (s : real -> Prop) (x : real) (l : real) (e : real) : (term340 s x l e) = (term341 s x l e).
Proof. exact (@lem5247266 s x l e (@lem5247265 s x l e)). Qed.
Lemma lem5247295 (s : real -> Prop) (l : real) (e : real) : (term342 s l e) = (term343 s l e).
Proof. exact (fun_ext (fun x : real => @lem5247267 s x l e)). Qed.
Lemma lem5247323 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5247324 (s : real -> Prop) (l : real) (e : real) : (term344 s l e) = (term345 s l e).
Proof. exact (MK_COMB (@lem5247323) (@lem5247295 s l e)). Qed.
Lemma lem5247356 (s : real -> Prop) : (term346 s) = (term346 s).
Proof. exact (eq_refl (term346 s)). Qed.
Lemma lem5247357 (s : real -> Prop) (l : real) (e : real) : (term325 s l e) = (term347 s l e).
Proof. exact (MK_COMB (@lem5247356 s) (@lem5247324 s l e)). Qed.
Lemma lem5247393 (s : real -> Prop) (l : real) (e : real) (q' : Prop) : term348 s l e q'.
Proof. exact (@lem5247233 s l e (term347 s l e) q'). Qed.
Lemma lem5247394 (s : real -> Prop) (l : real) (e : real) (q' : Prop) : term349 s l e q'.
Proof. exact (@lem5247393 s l e q' (@lem5247357 s l e)). Qed.
Lemma lem5247433 (x : real) (l : real) (e : real) : (term19 x l e) = (term20 x l e).
Proof. exact (@lem5247205 x l e (@lem5247204 x l e)). Qed.
Lemma lem5247434 (s : real -> Prop) (l : real) (e : real) : (term326 s l e) = (term350 s l e).
Proof. exact (@lem5247433 (inf s) l e). Qed.
Lemma lem5247447 (s : real -> Prop) (l : real) (e : real) : term351 s l e.
Proof. exact (fun h0 : term347 s l e => @lem5247434 s l e). Qed.
Lemma lem5247448 (s : real -> Prop) (l : real) (e : real) : term352 s l e.
Proof. exact (@lem5247394 s l e (term350 s l e)). Qed.
Lemma lem5247449 (s : real -> Prop) (l : real) (e : real) : (term353 s l e) = (term354 s l e).
Proof. exact (@lem5247448 s l e (@lem5247447 s l e)). Qed.
Lemma lem5247591 (s : real -> Prop) (l : real) : (term355 s l) = (term356 s l).
Proof. exact (fun_ext (fun e : real => @lem5247449 s l e)). Qed.
Lemma lem5247733 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5247734 (s : real -> Prop) (l : real) : (term357 s l) = (term358 s l).
Proof. exact (MK_COMB (@lem5247733) (@lem5247591 s l)). Qed.
Lemma lem5247880 (s : real -> Prop) : (term359 s) = (term360 s).
Proof. exact (fun_ext (fun l : real => @lem5247734 s l)). Qed.
Lemma lem5248026 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5248027 (s : real -> Prop) : (term361 s) = (term362 s).
Proof. exact (MK_COMB (@lem5248026) (@lem5247880 s)). Qed.
Lemma lem5248177 : term363 = term364.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5248027 s)). Qed.
Lemma lem5248327 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5248328 : term365 = term366.
Proof. exact (MK_COMB (@lem5248327) (@lem5248177)). Qed.
Lemma lem5248482 : term366 = term365.
Proof. exact (SYM (@lem5248328)). Qed.
Lemma lem5248496 (a : real) (s : real -> Prop) (b : real) : (term5 a s b) = True.
Proof. exact (EQ_MP (@lem5243861 a s b) (@lem5243860 a s b)). Qed.
Lemma lem5248497 (s : real -> Prop) (l : real) (e : real) : (term354 s l e) = True.
Proof. exact (@lem5248496 (real_sub l e) s (real_add l e)). Qed.
Lemma lem5248498 (s : real -> Prop) (l : real) : (term356 s l) = term367.
Proof. exact (fun_ext (fun e : real => @lem5248497 s l e)). Qed.
Lemma lem5248499 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5248500 (s : real -> Prop) (l : real) : (term358 s l) = term368.
Proof. exact (MK_COMB (@lem5248499) (@lem5248498 s l)). Qed.
Lemma lem5248502 {A : Type'} (t : Prop) : (term369 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5248503 (t : Prop) : (term370 t) = t.
Proof. exact (@lem5248502 real t). Qed.
Lemma lem5248504 : term368 = True.
Proof. exact (@lem5248503 True). Qed.
Lemma lem5248505 (s : real -> Prop) (l : real) : (term358 s l) = True.
Proof. exact (TRANS (@lem5248500 s l) (@lem5248504)). Qed.
Lemma lem5248506 (s : real -> Prop) : (term360 s) = term367.
Proof. exact (fun_ext (fun l : real => @lem5248505 s l)). Qed.
Lemma lem5248507 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5248508 (s : real -> Prop) : (term362 s) = term368.
Proof. exact (MK_COMB (@lem5248507) (@lem5248506 s)). Qed.
Lemma lem5248510 {A : Type'} (t : Prop) : (term369 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5248511 (t : Prop) : (term370 t) = t.
Proof. exact (@lem5248510 real t). Qed.
Lemma lem5248512 : term368 = True.
Proof. exact (@lem5248511 True). Qed.
Lemma lem5248513 (s : real -> Prop) : (term362 s) = True.
Proof. exact (TRANS (@lem5248508 s) (@lem5248512)). Qed.
Lemma lem5248514 : term364 = term371.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5248513 s)). Qed.
Lemma lem5248515 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5248516 : term366 = term372.
Proof. exact (MK_COMB (@lem5248515) (@lem5248514)). Qed.
Lemma lem5248518 {A : Type'} (t : Prop) : (term369 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5248519 (t : Prop) : (term373 t) = t.
Proof. exact (@lem5248518 (real -> Prop) t). Qed.
Lemma lem5248520 : term372 = True.
Proof. exact (@lem5248519 True). Qed.
Lemma lem5248521 : term366 = True.
Proof. exact (TRANS (@lem5248516) (@lem5248520)). Qed.
Lemma lem5248522 : True = term366.
Proof. exact (SYM (@lem5248521)). Qed.
Lemma lem5248523 : term366.
Proof. exact (EQ_MP (@lem5248522) (@lem0)). Qed.
Lemma lem5248524 : term365.
Proof. exact (EQ_MP (@lem5248482) (@lem5248523)). Qed.
