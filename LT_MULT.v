Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_MULT_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import LT_0_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem101918 (n : nat) : term0 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem101919 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem101920 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem101919 n) (@lem101918 n)). Qed.
Lemma lem101921 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem101923 : term2.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem101924 : term3.
Proof. exact (proj2 (@lem101923)). Qed.
Lemma lem101925 : term4.
Proof. exact (proj2 (@lem101924)). Qed.
Lemma lem101926 (m : nat) : term5 m.
Proof. exact (@lem101925 m). Qed.
Lemma lem101927 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem101928 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem101927 m) (@lem101926 m)). Qed.
Lemma lem101929 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem101928 m n). Qed.
Lemma lem101930 (m : nat) (n : nat) : (term7 m n) = ((term8 m n) = (term9 m n)).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem101939 : term10.
Proof. exact (proj1 (@lem101923)). Qed.
Lemma lem101940 (m : nat) : term11 m.
Proof. exact (@lem101939 m). Qed.
Lemma lem101941 (m : nat) : (term11 m) = ((term12 m) = m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem101947 : term13.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem101948 : term14.
Proof. exact (proj2 (@lem101947)). Qed.
Lemma lem101949 : term15.
Proof. exact (proj2 (@lem101948)). Qed.
Lemma lem101950 : term16.
Proof. exact (proj2 (@lem101949)). Qed.
Lemma lem101951 : term17.
Proof. exact (proj2 (@lem101950)). Qed.
Lemma lem101952 (m : nat) : term18 m.
Proof. exact (@lem101951 m). Qed.
Lemma lem101953 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem101954 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem101953 m) (@lem101952 m)). Qed.
Lemma lem101955 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem101954 m n). Qed.
Lemma lem101956 (m : nat) (n : nat) : (term20 m n) = ((term21 m n) = (term22 m n)).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem101958 : term23.
Proof. exact (proj1 (@lem101950)). Qed.
Lemma lem101959 (m : nat) : term24 m.
Proof. exact (@lem101958 m). Qed.
Lemma lem101960 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem101961 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem101960 m) (@lem101959 m)). Qed.
Lemma lem101962 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem101961 m n). Qed.
Lemma lem101963 (m : nat) (n : nat) : (term26 m n) = ((term27 m n) = (term28 m n)).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem101973 : term29.
Proof. exact (proj1 (@lem101947)). Qed.
Lemma lem101974 (m : nat) : term30 m.
Proof. exact (@lem101973 m). Qed.
Lemma lem101975 (m : nat) : (term30 m) = ((term31 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem101977 : term32.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem101978 (n : nat) : term33 n.
Proof. exact (@lem101977 n). Qed.
Lemma lem101979 (n : nat) : (term33 n) = ((term34 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem101982 (P : nat -> Prop) : term35 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem101983 : term36.
Proof. exact (@lem101982 term37). Qed.
Lemma lem101984 : term38 = term39.
Proof. exact (eq_refl term38). Qed.
Lemma lem101985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem101986 : term40 = term41.
Proof. exact (MK_COMB (@lem101985) (@lem101984)). Qed.
Lemma lem101987 (m : nat) : (term42 m) = (term43 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem101988 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem101989 (m : nat) : (term44 m) = (term45 m).
Proof. exact (MK_COMB (@lem101988) (@lem101987 m)). Qed.
Lemma lem101990 (m : nat) : (term46 m) = (term47 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem101991 (m : nat) : (term48 m) = (term49 m).
Proof. exact (MK_COMB (@lem101989 m) (@lem101990 m)). Qed.
Lemma lem101992 : term50 = term51.
Proof. exact (fun_ext (fun m : nat => @lem101991 m)). Qed.
Lemma lem101993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem101994 : term52 = term53.
Proof. exact (MK_COMB (@lem101993) (@lem101992)). Qed.
Lemma lem101995 : term54 = term55.
Proof. exact (MK_COMB (@lem101986) (@lem101994)). Qed.
Lemma lem101996 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem101997 : term56 = term57.
Proof. exact (MK_COMB (@lem101996) (@lem101995)). Qed.
Lemma lem101998 (m : nat) : (term42 m) = (term43 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem101999 : term58 = term37.
Proof. exact (fun_ext (fun m : nat => @lem101998 m)). Qed.
Lemma lem102000 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102001 : term59 = term60.
Proof. exact (MK_COMB (@lem102000) (@lem101999)). Qed.
Lemma lem102002 : term36 = term61.
Proof. exact (MK_COMB (@lem101997) (@lem102001)). Qed.
Lemma lem102003 : term61.
Proof. exact (EQ_MP (@lem102002) (@lem101983)). Qed.
Lemma lem102006 (P : nat -> Prop) : term35 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem102007 : term62.
Proof. exact (@lem102006 term63). Qed.
Lemma lem102008 : term64 = (term65 = term66).
Proof. exact (eq_refl term64). Qed.
Lemma lem102009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem102010 : term67 = term68.
Proof. exact (MK_COMB (@lem102009) (@lem102008)). Qed.
Lemma lem102011 (n : nat) : (term69 n) = ((term70 n) = (term71 n)).
Proof. exact (eq_refl (term69 n)). Qed.
Lemma lem102012 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102013 (n : nat) : (term72 n) = (term73 n).
Proof. exact (MK_COMB (@lem102012) (@lem102011 n)). Qed.
Lemma lem102014 (n : nat) : (term74 n) = ((term75 n) = (term76 n)).
Proof. exact (eq_refl (term74 n)). Qed.
Lemma lem102015 (n : nat) : (term77 n) = (term78 n).
Proof. exact (MK_COMB (@lem102013 n) (@lem102014 n)). Qed.
Lemma lem102016 : term79 = term80.
Proof. exact (fun_ext (fun n : nat => @lem102015 n)). Qed.
Lemma lem102017 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102018 : term81 = term82.
Proof. exact (MK_COMB (@lem102017) (@lem102016)). Qed.
Lemma lem102019 : term83 = term84.
Proof. exact (MK_COMB (@lem102010) (@lem102018)). Qed.
Lemma lem102020 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102021 : term85 = term86.
Proof. exact (MK_COMB (@lem102020) (@lem102019)). Qed.
Lemma lem102022 (n : nat) : (term69 n) = ((term70 n) = (term71 n)).
Proof. exact (eq_refl (term69 n)). Qed.
Lemma lem102023 : term87 = term63.
Proof. exact (fun_ext (fun n : nat => @lem102022 n)). Qed.
Lemma lem102024 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102025 : term88 = term39.
Proof. exact (MK_COMB (@lem102024) (@lem102023)). Qed.
Lemma lem102026 : term62 = term89.
Proof. exact (MK_COMB (@lem102021) (@lem102025)). Qed.
Lemma lem102027 : term89.
Proof. exact (EQ_MP (@lem102026) (@lem102007)). Qed.
Lemma lem102034 (P : nat -> Prop) : term35 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem102035 (m : nat) : term90 m.
Proof. exact (@lem102034 (term91 m)). Qed.
Lemma lem102036 (m : nat) : (term92 m) = ((term93 m) = (term94 m)).
Proof. exact (eq_refl (term92 m)). Qed.
Lemma lem102037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem102038 (m : nat) : (term95 m) = (term96 m).
Proof. exact (MK_COMB (@lem102037) (@lem102036 m)). Qed.
Lemma lem102039 (m : nat) (n : nat) : (term97 m n) = ((term98 m n) = (term99 m n)).
Proof. exact (eq_refl (term97 m n)). Qed.
Lemma lem102040 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102041 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (MK_COMB (@lem102040) (@lem102039 m n)). Qed.
Lemma lem102042 (m : nat) (n : nat) : (term102 m n) = ((term103 m n) = (term104 m n)).
Proof. exact (eq_refl (term102 m n)). Qed.
Lemma lem102043 (m : nat) (n : nat) : (term105 m n) = (term106 m n).
Proof. exact (MK_COMB (@lem102041 m n) (@lem102042 m n)). Qed.
Lemma lem102044 (m : nat) : (term107 m) = (term108 m).
Proof. exact (fun_ext (fun n : nat => @lem102043 m n)). Qed.
Lemma lem102045 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102046 (m : nat) : (term109 m) = (term110 m).
Proof. exact (MK_COMB (@lem102045) (@lem102044 m)). Qed.
Lemma lem102047 (m : nat) : (term111 m) = (term112 m).
Proof. exact (MK_COMB (@lem102038 m) (@lem102046 m)). Qed.
Lemma lem102048 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102049 (m : nat) : (term113 m) = (term114 m).
Proof. exact (MK_COMB (@lem102048) (@lem102047 m)). Qed.
Lemma lem102050 (m : nat) (n : nat) : (term97 m n) = ((term98 m n) = (term99 m n)).
Proof. exact (eq_refl (term97 m n)). Qed.
Lemma lem102051 (m : nat) : (term115 m) = (term91 m).
Proof. exact (fun_ext (fun n : nat => @lem102050 m n)). Qed.
Lemma lem102052 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102053 (m : nat) : (term116 m) = (term47 m).
Proof. exact (MK_COMB (@lem102052) (@lem102051 m)). Qed.
Lemma lem102054 (m : nat) : (term90 m) = (term117 m).
Proof. exact (MK_COMB (@lem102049 m) (@lem102053 m)). Qed.
Lemma lem102055 (m : nat) : term117 m.
Proof. exact (EQ_MP (@lem102054 m) (@lem102035 m)). Qed.
Lemma lem102064 (n : nat) : (term34 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem101979 n) (@lem101978 n)). Qed.
Lemma lem102065 : term118 = (NUMERAL 0).
Proof. exact (@lem102064 (NUMERAL 0)). Qed.
Lemma lem102066 : term119 = term119.
Proof. exact (eq_refl term119). Qed.
Lemma lem102067 : term65 = term120.
Proof. exact (MK_COMB (@lem102066) (@lem102065)). Qed.
Lemma lem102068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem102069 : term121 = term122.
Proof. exact (MK_COMB (@lem102068) (@lem102067)). Qed.
Lemma lem102071 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem102072 : term66 = term120.
Proof. exact (@lem102071 term120). Qed.
Lemma lem102073 : (term65 = term66) = (term120 = term120).
Proof. exact (MK_COMB (@lem102069) (@lem102072)). Qed.
Lemma lem102075 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem102076 (x : Prop) : (x = x) = True.
Proof. exact (@lem102075 Prop x). Qed.
Lemma lem102077 : (term120 = term120) = True.
Proof. exact (@lem102076 term120). Qed.
Lemma lem102078 : (term65 = term66) = True.
Proof. exact (TRANS (@lem102073) (@lem102077)). Qed.
Lemma lem102079 : True = (term65 = term66).
Proof. exact (SYM (@lem102078)). Qed.
Lemma lem102080 : term65 = term66.
Proof. exact (EQ_MP (@lem102079) (@lem0)). Qed.
Lemma lem102084 (n : nat) : (term34 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem101979 n) (@lem101978 n)). Qed.
Lemma lem102085 (n : nat) : (term123 n) = (NUMERAL 0).
Proof. exact (@lem102084 (S n)). Qed.
Lemma lem102086 : term119 = term119.
Proof. exact (eq_refl term119). Qed.
Lemma lem102087 (n : nat) : (term75 n) = term120.
Proof. exact (MK_COMB (@lem102086) (@lem102085 n)). Qed.
Lemma lem102088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem102089 (n : nat) : (term124 n) = term122.
Proof. exact (MK_COMB (@lem102088) (@lem102087 n)). Qed.
Lemma lem102093 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem101921 n) (@lem101920 n)). Qed.
Lemma lem102094 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem102095 (n : nat) : (term76 n) = term126.
Proof. exact (MK_COMB (@lem102094) (@lem102093 n)). Qed.
Lemma lem102097 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem102098 : term126 = term120.
Proof. exact (@lem102097 term120). Qed.
Lemma lem102099 (n : nat) : (term76 n) = term120.
Proof. exact (TRANS (@lem102095 n) (@lem102098)). Qed.
Lemma lem102100 (n : nat) : ((term75 n) = (term76 n)) = (term120 = term120).
Proof. exact (MK_COMB (@lem102089 n) (@lem102099 n)). Qed.
Lemma lem102102 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem102103 (x : Prop) : (x = x) = True.
Proof. exact (@lem102102 Prop x). Qed.
Lemma lem102104 : (term120 = term120) = True.
Proof. exact (@lem102103 term120). Qed.
Lemma lem102105 (n : nat) : ((term75 n) = (term76 n)) = True.
Proof. exact (TRANS (@lem102100 n) (@lem102104)). Qed.
Lemma lem102106 (n : nat) : True = ((term75 n) = (term76 n)).
Proof. exact (SYM (@lem102105 n)). Qed.
Lemma lem102107 (n : nat) : (term75 n) = (term76 n).
Proof. exact (EQ_MP (@lem102106 n) (@lem0)). Qed.
Lemma lem102111 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (EQ_MP (@lem101963 m n) (@lem101962 m n)). Qed.
Lemma lem102112 (m : nat) : (term127 m) = (term128 m).
Proof. exact (@lem102111 m (NUMERAL 0)). Qed.
Lemma lem102114 (m : nat) : (term12 m) = m.
Proof. exact (EQ_MP (@lem101941 m) (@lem101940 m)). Qed.
Lemma lem102115 (m : nat) : (term128 m) = (term31 m).
Proof. exact (@lem102114 (term31 m)). Qed.
Lemma lem102117 (m : nat) : (term31 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem101975 m) (@lem101974 m)). Qed.
Lemma lem102118 (m : nat) : (term128 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem102115 m) (@lem102117 m)). Qed.
Lemma lem102119 (m : nat) : (term127 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem102112 m) (@lem102118 m)). Qed.
Lemma lem102120 : term119 = term119.
Proof. exact (eq_refl term119). Qed.
Lemma lem102121 (m : nat) : (term93 m) = term120.
Proof. exact (MK_COMB (@lem102120) (@lem102119 m)). Qed.
Lemma lem102122 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem102123 (m : nat) : (term129 m) = term122.
Proof. exact (MK_COMB (@lem102122) (@lem102121 m)). Qed.
Lemma lem102127 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem101921 n) (@lem101920 n)). Qed.
Lemma lem102128 (m : nat) : (term1 m) = True.
Proof. exact (@lem102127 m). Qed.
Lemma lem102129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem102130 (m : nat) : (term130 m) = (and True).
Proof. exact (MK_COMB (@lem102129) (@lem102128 m)). Qed.
Lemma lem102131 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem102132 (m : nat) : (term94 m) = term131.
Proof. exact (MK_COMB (@lem102130 m) (@lem102131)). Qed.
Lemma lem102134 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem102135 : term131 = term120.
Proof. exact (@lem102134 term120). Qed.
Lemma lem102136 (m : nat) : (term94 m) = term120.
Proof. exact (TRANS (@lem102132 m) (@lem102135)). Qed.
Lemma lem102137 (m : nat) : ((term93 m) = (term94 m)) = (term120 = term120).
Proof. exact (MK_COMB (@lem102123 m) (@lem102136 m)). Qed.
Lemma lem102139 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem102140 (x : Prop) : (x = x) = True.
Proof. exact (@lem102139 Prop x). Qed.
Lemma lem102141 : (term120 = term120) = True.
Proof. exact (@lem102140 term120). Qed.
Lemma lem102142 (m : nat) : ((term93 m) = (term94 m)) = True.
Proof. exact (TRANS (@lem102137 m) (@lem102141)). Qed.
Lemma lem102143 (m : nat) : True = ((term93 m) = (term94 m)).
Proof. exact (SYM (@lem102142 m)). Qed.
Lemma lem102144 (m : nat) : (term93 m) = (term94 m).
Proof. exact (EQ_MP (@lem102143 m) (@lem0)). Qed.
Lemma lem102148 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (EQ_MP (@lem101963 m n) (@lem101962 m n)). Qed.
Lemma lem102149 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (@lem102148 m (S n)). Qed.
Lemma lem102151 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (EQ_MP (@lem101930 m n) (@lem101929 m n)). Qed.
Lemma lem102152 (m : nat) (n : nat) : (term133 m n) = (term134 m n).
Proof. exact (@lem102151 (term21 m n) n). Qed.
Lemma lem102153 (m : nat) (n : nat) : (term132 m n) = (term134 m n).
Proof. exact (TRANS (@lem102149 m n) (@lem102152 m n)). Qed.
Lemma lem102155 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (EQ_MP (@lem101956 m n) (@lem101955 m n)). Qed.
Lemma lem102156 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem102157 (m : nat) (n : nat) : (term135 m n) = (term136 m n).
Proof. exact (MK_COMB (@lem102156) (@lem102155 m n)). Qed.
Lemma lem102158 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem102159 (m : nat) (n : nat) : (term137 m n) = (term138 m n).
Proof. exact (MK_COMB (@lem102157 m n) (@lem102158 n)). Qed.
Lemma lem102160 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem102161 (m : nat) (n : nat) : (term134 m n) = (term139 m n).
Proof. exact (MK_COMB (@lem102160) (@lem102159 m n)). Qed.
Lemma lem102162 (m : nat) (n : nat) : (term132 m n) = (term139 m n).
Proof. exact (TRANS (@lem102153 m n) (@lem102161 m n)). Qed.
Lemma lem102163 : term119 = term119.
Proof. exact (eq_refl term119). Qed.
Lemma lem102164 (m : nat) (n : nat) : (term103 m n) = (term140 m n).
Proof. exact (MK_COMB (@lem102163) (@lem102162 m n)). Qed.
Lemma lem102166 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem101921 n) (@lem101920 n)). Qed.
Lemma lem102167 (m : nat) (n : nat) : (term140 m n) = True.
Proof. exact (@lem102166 (term138 m n)). Qed.
Lemma lem102168 (m : nat) (n : nat) : (term103 m n) = True.
Proof. exact (TRANS (@lem102164 m n) (@lem102167 m n)). Qed.
Lemma lem102169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem102170 (m : nat) (n : nat) : (term141 m n) = (@eq Prop True).
Proof. exact (MK_COMB (@lem102169) (@lem102168 m n)). Qed.
Lemma lem102174 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem101921 n) (@lem101920 n)). Qed.
Lemma lem102175 (m : nat) : (term1 m) = True.
Proof. exact (@lem102174 m). Qed.
Lemma lem102176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem102177 (m : nat) : (term130 m) = (and True).
Proof. exact (MK_COMB (@lem102176) (@lem102175 m)). Qed.
Lemma lem102179 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem101921 n) (@lem101920 n)). Qed.
Lemma lem102180 (m : nat) (n : nat) : (term104 m n) = (True /\ True).
Proof. exact (MK_COMB (@lem102177 m) (@lem102179 n)). Qed.
Lemma lem102182 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem102183 : (True /\ True) = True.
Proof. exact (@lem102182 True). Qed.
Lemma lem102184 (m : nat) (n : nat) : (term104 m n) = True.
Proof. exact (TRANS (@lem102180 m n) (@lem102183)). Qed.
Lemma lem102185 (m : nat) (n : nat) : ((term103 m n) = (term104 m n)) = (True = True).
Proof. exact (MK_COMB (@lem102170 m n) (@lem102184 m n)). Qed.
Lemma lem102187 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem102188 : (True = True) = True.
Proof. exact (@lem102187 True). Qed.
Lemma lem102189 (m : nat) (n : nat) : ((term103 m n) = (term104 m n)) = True.
Proof. exact (TRANS (@lem102185 m n) (@lem102188)). Qed.
Lemma lem102190 (m : nat) (n : nat) : True = ((term103 m n) = (term104 m n)).
Proof. exact (SYM (@lem102189 m n)). Qed.
Lemma lem102191 (m : nat) (n : nat) : (term103 m n) = (term104 m n).
Proof. exact (EQ_MP (@lem102190 m n) (@lem0)). Qed.
Lemma lem102192 (m : nat) (n : nat) : term106 m n.
Proof. exact (fun h0 : (term98 m n) = (term99 m n) => @lem102191 m n). Qed.
Lemma lem102197 (m : nat) : term110 m.
Proof. exact (fun n : nat => @lem102192 m n). Qed.
Lemma lem102198 (m : nat) : term112 m.
Proof. exact (conj (@lem102144 m) (@lem102197 m)). Qed.
Lemma lem102199 (m : nat) : term47 m.
Proof. exact (@lem102055 m (@lem102198 m)). Qed.
Lemma lem102200 (n : nat) : term78 n.
Proof. exact (fun h0 : (term70 n) = (term71 n) => @lem102107 n). Qed.
Lemma lem102205 : term82.
Proof. exact (fun n : nat => @lem102200 n). Qed.
Lemma lem102206 : term84.
Proof. exact (conj (@lem102080) (@lem102205)). Qed.
Lemma lem102207 : term39.
Proof. exact (@lem102027 (@lem102206)). Qed.
Lemma lem102208 (m : nat) : term49 m.
Proof. exact (fun h0 : term43 m => @lem102199 m). Qed.
Lemma lem102213 : term53.
Proof. exact (fun m : nat => @lem102208 m). Qed.
Lemma lem102214 : term55.
Proof. exact (conj (@lem102207) (@lem102213)). Qed.
Lemma lem102215 : term60.
Proof. exact (@lem102003 (@lem102214)). Qed.
