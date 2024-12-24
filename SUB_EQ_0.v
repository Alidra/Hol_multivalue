Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUB_EQ_0_term_abbrevs.
Require Import LE_0_spec.
Require Import LE_SUC_spec.
Require Import SUB_0_spec.
Require Import SUB_SUC_spec.
Require Import thm0_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm89498_spec.
Lemma lem135940 (n : nat) : term0 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem135941 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem135942 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem135941 n) (@lem135940 n)). Qed.
Lemma lem135943 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem135952 : term2.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem135953 (m : nat) : term3 m.
Proof. exact (@lem135952 m). Qed.
Lemma lem135954 (m : nat) : (term3 m) = ((term4 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem135957 (P : nat -> Prop) : term5 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem135958 : term6.
Proof. exact (@lem135957 term7). Qed.
Lemma lem135959 : term8 = term9.
Proof. exact (eq_refl term8). Qed.
Lemma lem135960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem135961 : term10 = term11.
Proof. exact (MK_COMB (@lem135960) (@lem135959)). Qed.
Lemma lem135962 (m : nat) : (term12 m) = (term13 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem135963 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135964 (m : nat) : (term14 m) = (term15 m).
Proof. exact (MK_COMB (@lem135963) (@lem135962 m)). Qed.
Lemma lem135965 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem135966 (m : nat) : (term18 m) = (term19 m).
Proof. exact (MK_COMB (@lem135964 m) (@lem135965 m)). Qed.
Lemma lem135967 : term20 = term21.
Proof. exact (fun_ext (fun m : nat => @lem135966 m)). Qed.
Lemma lem135968 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135969 : term22 = term23.
Proof. exact (MK_COMB (@lem135968) (@lem135967)). Qed.
Lemma lem135970 : term24 = term25.
Proof. exact (MK_COMB (@lem135961) (@lem135969)). Qed.
Lemma lem135971 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135972 : term26 = term27.
Proof. exact (MK_COMB (@lem135971) (@lem135970)). Qed.
Lemma lem135973 (m : nat) : (term12 m) = (term13 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem135974 : term28 = term7.
Proof. exact (fun_ext (fun m : nat => @lem135973 m)). Qed.
Lemma lem135975 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135976 : term29 = term30.
Proof. exact (MK_COMB (@lem135975) (@lem135974)). Qed.
Lemma lem135977 : term6 = term31.
Proof. exact (MK_COMB (@lem135972) (@lem135976)). Qed.
Lemma lem135978 : term31.
Proof. exact (EQ_MP (@lem135977) (@lem135958)). Qed.
Lemma lem135979 (m : nat) (h1 : term13 m) : term13 m.
Proof. exact (h1). Qed.
Lemma lem135981 (P : nat -> Prop) : term5 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem135982 : term32.
Proof. exact (@lem135981 term33). Qed.
Lemma lem135983 : term34 = ((term35 = (NUMERAL 0)) = term36).
Proof. exact (eq_refl term34). Qed.
Lemma lem135984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem135985 : term37 = term38.
Proof. exact (MK_COMB (@lem135984) (@lem135983)). Qed.
Lemma lem135986 (n : nat) : (term39 n) = (((term40 n) = (NUMERAL 0)) = (term1 n)).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem135987 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135988 (n : nat) : (term41 n) = (term42 n).
Proof. exact (MK_COMB (@lem135987) (@lem135986 n)). Qed.
Lemma lem135989 (n : nat) : (term43 n) = (((term44 n) = (NUMERAL 0)) = (term45 n)).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem135990 (n : nat) : (term46 n) = (term47 n).
Proof. exact (MK_COMB (@lem135988 n) (@lem135989 n)). Qed.
Lemma lem135991 : term48 = term49.
Proof. exact (fun_ext (fun n : nat => @lem135990 n)). Qed.
Lemma lem135992 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135993 : term50 = term51.
Proof. exact (MK_COMB (@lem135992) (@lem135991)). Qed.
Lemma lem135994 : term52 = term53.
Proof. exact (MK_COMB (@lem135985) (@lem135993)). Qed.
Lemma lem135995 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135996 : term54 = term55.
Proof. exact (MK_COMB (@lem135995) (@lem135994)). Qed.
Lemma lem135997 (n : nat) : (term39 n) = (((term40 n) = (NUMERAL 0)) = (term1 n)).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem135998 : term56 = term33.
Proof. exact (fun_ext (fun n : nat => @lem135997 n)). Qed.
Lemma lem135999 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136000 : term57 = term9.
Proof. exact (MK_COMB (@lem135999) (@lem135998)). Qed.
Lemma lem136001 : term32 = term58.
Proof. exact (MK_COMB (@lem135996) (@lem136000)). Qed.
Lemma lem136002 : term58.
Proof. exact (EQ_MP (@lem136001) (@lem135982)). Qed.
Lemma lem136009 (P : nat -> Prop) : term5 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem136010 (m : nat) : term59 m.
Proof. exact (@lem136009 (term60 m)). Qed.
Lemma lem136011 (m : nat) : (term61 m) = (((term62 m) = (NUMERAL 0)) = (term63 m)).
Proof. exact (eq_refl (term61 m)). Qed.
Lemma lem136012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem136013 (m : nat) : (term64 m) = (term65 m).
Proof. exact (MK_COMB (@lem136012) (@lem136011 m)). Qed.
Lemma lem136014 (m : nat) (n : nat) : (term66 m n) = (((term67 m n) = (NUMERAL 0)) = (term68 m n)).
Proof. exact (eq_refl (term66 m n)). Qed.
Lemma lem136015 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem136016 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (MK_COMB (@lem136015) (@lem136014 m n)). Qed.
Lemma lem136017 (m : nat) (n : nat) : (term71 m n) = (((term72 m n) = (NUMERAL 0)) = (term73 m n)).
Proof. exact (eq_refl (term71 m n)). Qed.
Lemma lem136018 (m : nat) (n : nat) : (term74 m n) = (term75 m n).
Proof. exact (MK_COMB (@lem136016 m n) (@lem136017 m n)). Qed.
Lemma lem136019 (m : nat) : (term76 m) = (term77 m).
Proof. exact (fun_ext (fun n : nat => @lem136018 m n)). Qed.
Lemma lem136020 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136021 (m : nat) : (term78 m) = (term79 m).
Proof. exact (MK_COMB (@lem136020) (@lem136019 m)). Qed.
Lemma lem136022 (m : nat) : (term80 m) = (term81 m).
Proof. exact (MK_COMB (@lem136013 m) (@lem136021 m)). Qed.
Lemma lem136023 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem136024 (m : nat) : (term82 m) = (term83 m).
Proof. exact (MK_COMB (@lem136023) (@lem136022 m)). Qed.
Lemma lem136025 (m : nat) (n : nat) : (term66 m n) = (((term67 m n) = (NUMERAL 0)) = (term68 m n)).
Proof. exact (eq_refl (term66 m n)). Qed.
Lemma lem136026 (m : nat) : (term84 m) = (term60 m).
Proof. exact (fun_ext (fun n : nat => @lem136025 m n)). Qed.
Lemma lem136027 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136028 (m : nat) : (term85 m) = (term17 m).
Proof. exact (MK_COMB (@lem136027) (@lem136026 m)). Qed.
Lemma lem136029 (m : nat) : (term59 m) = (term86 m).
Proof. exact (MK_COMB (@lem136024 m) (@lem136028 m)). Qed.
Lemma lem136030 (m : nat) : term86 m.
Proof. exact (EQ_MP (@lem136029 m) (@lem136010 m)). Qed.
Lemma lem136036 (m : nat) : term87 m.
Proof. exact (@lem135231 m). Qed.
Lemma lem136037 (m : nat) : (term87 m) = (term88 m).
Proof. exact (eq_refl (term87 m)). Qed.
Lemma lem136038 (m : nat) : term88 m.
Proof. exact (EQ_MP (@lem136037 m) (@lem136036 m)). Qed.
Lemma lem136058 (m : nat) : (term40 m) = (NUMERAL 0).
Proof. exact (proj1 (@lem136038 m)). Qed.
Lemma lem136059 : term35 = (NUMERAL 0).
Proof. exact (@lem136058 (NUMERAL 0)). Qed.
Lemma lem136060 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem136061 : term89 = term90.
Proof. exact (MK_COMB (@lem136060) (@lem136059)). Qed.
Lemma lem136062 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem136063 : (term35 = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem136061) (@lem136062)). Qed.
Lemma lem136065 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem136066 (x : nat) : (x = x) = True.
Proof. exact (@lem136065 nat x). Qed.
Lemma lem136067 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem136066 (NUMERAL 0)). Qed.
Lemma lem136068 : (term35 = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem136063) (@lem136067)). Qed.
Lemma lem136069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem136070 : term91 = (@eq Prop True).
Proof. exact (MK_COMB (@lem136069) (@lem136068)). Qed.
Lemma lem136071 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem136072 : ((term35 = (NUMERAL 0)) = term36) = (True = term36).
Proof. exact (MK_COMB (@lem136070) (@lem136071)). Qed.
Lemma lem136074 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem136075 : (True = term36) = term36.
Proof. exact (@lem136074 term36). Qed.
Lemma lem136076 : ((term35 = (NUMERAL 0)) = term36) = term36.
Proof. exact (TRANS (@lem136072) (@lem136075)). Qed.
Lemma lem136077 : term36 = ((term35 = (NUMERAL 0)) = term36).
Proof. exact (SYM (@lem136076)). Qed.
Lemma lem136078 (m : nat) : term87 m.
Proof. exact (@lem135231 m). Qed.
Lemma lem136079 (m : nat) : (term87 m) = (term88 m).
Proof. exact (eq_refl (term87 m)). Qed.
Lemma lem136080 (m : nat) : term88 m.
Proof. exact (EQ_MP (@lem136079 m) (@lem136078 m)). Qed.
Lemma lem136100 (m : nat) : (term40 m) = (NUMERAL 0).
Proof. exact (proj1 (@lem136080 m)). Qed.
Lemma lem136101 (n : nat) : (term44 n) = (NUMERAL 0).
Proof. exact (@lem136100 (S n)). Qed.
Lemma lem136102 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem136103 (n : nat) : (term92 n) = term90.
Proof. exact (MK_COMB (@lem136102) (@lem136101 n)). Qed.
Lemma lem136104 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem136105 (n : nat) : ((term44 n) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem136103 n) (@lem136104)). Qed.
Lemma lem136107 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem136108 (x : nat) : (x = x) = True.
Proof. exact (@lem136107 nat x). Qed.
Lemma lem136109 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem136108 (NUMERAL 0)). Qed.
Lemma lem136110 (n : nat) : ((term44 n) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem136105 n) (@lem136109)). Qed.
Lemma lem136111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem136112 (n : nat) : (term93 n) = (@eq Prop True).
Proof. exact (MK_COMB (@lem136111) (@lem136110 n)). Qed.
Lemma lem136113 (n : nat) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem136114 (n : nat) : (((term44 n) = (NUMERAL 0)) = (term45 n)) = (True = (term45 n)).
Proof. exact (MK_COMB (@lem136112 n) (@lem136113 n)). Qed.
Lemma lem136116 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem136117 (n : nat) : (True = (term45 n)) = (term45 n).
Proof. exact (@lem136116 (term45 n)). Qed.
Lemma lem136118 (n : nat) : (((term44 n) = (NUMERAL 0)) = (term45 n)) = (term45 n).
Proof. exact (TRANS (@lem136114 n) (@lem136117 n)). Qed.
Lemma lem136119 (n : nat) : (term45 n) = (((term44 n) = (NUMERAL 0)) = (term45 n)).
Proof. exact (SYM (@lem136118 n)). Qed.
Lemma lem136120 (m : nat) : term87 m.
Proof. exact (@lem135231 m). Qed.
Lemma lem136121 (m : nat) : (term87 m) = (term88 m).
Proof. exact (eq_refl (term87 m)). Qed.
Lemma lem136122 (m : nat) : term88 m.
Proof. exact (EQ_MP (@lem136121 m) (@lem136120 m)). Qed.
Lemma lem136145 (m : nat) : (term94 m) = m.
Proof. exact (proj2 (@lem136122 m)). Qed.
Lemma lem136146 (m : nat) : (term62 m) = (S m).
Proof. exact (@lem136145 (S m)). Qed.
Lemma lem136147 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem136148 (m : nat) : (term95 m) = (term96 m).
Proof. exact (MK_COMB (@lem136147) (@lem136146 m)). Qed.
Lemma lem136149 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem136150 (m : nat) : ((term62 m) = (NUMERAL 0)) = ((S m) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem136148 m) (@lem136149)). Qed.
Lemma lem136153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem136154 (m : nat) : (term97 m) = (term98 m).
Proof. exact (MK_COMB (@lem136153) (@lem136150 m)). Qed.
Lemma lem136155 (m : nat) : (term63 m) = (term63 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem136156 (m : nat) : (((term62 m) = (NUMERAL 0)) = (term63 m)) = (((S m) = (NUMERAL 0)) = (term63 m)).
Proof. exact (MK_COMB (@lem136154 m) (@lem136155 m)). Qed.
Lemma lem136159 (m : nat) : (((S m) = (NUMERAL 0)) = (term63 m)) = (((term62 m) = (NUMERAL 0)) = (term63 m)).
Proof. exact (SYM (@lem136156 m)). Qed.
Lemma lem136165 (m : nat) : term99 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem136166 (m : nat) : (term99 m) = (term100 m).
Proof. exact (eq_refl (term99 m)). Qed.
Lemma lem136167 (m : nat) : term100 m.
Proof. exact (EQ_MP (@lem136166 m) (@lem136165 m)). Qed.
Lemma lem136168 (m : nat) (n : nat) : term101 m n.
Proof. exact (@lem136167 m n). Qed.
Lemma lem136169 (m : nat) (n : nat) : (term101 m n) = ((term73 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term101 m n)). Qed.
Lemma lem136171 (m : nat) : term102 m.
Proof. exact (@lem135645 m). Qed.
Lemma lem136172 (m : nat) : (term102 m) = (term103 m).
Proof. exact (eq_refl (term102 m)). Qed.
Lemma lem136173 (m : nat) : term103 m.
Proof. exact (EQ_MP (@lem136172 m) (@lem136171 m)). Qed.
Lemma lem136174 (m : nat) (n : nat) : term104 m n.
Proof. exact (@lem136173 m n). Qed.
Lemma lem136175 (m : nat) (n : nat) : (term104 m n) = ((term72 m n) = (Nat.sub m n)).
Proof. exact (eq_refl (term104 m n)). Qed.
Lemma lem136177 (n : nat) (m : nat) (h1 : term13 m) : term105 m n.
Proof. exact (@lem135979 m h1 n). Qed.
Lemma lem136178 (m : nat) (n : nat) : (term105 m n) = (((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n)).
Proof. exact (eq_refl (term105 m n)). Qed.
Lemma lem136185 (m : nat) (n : nat) : (term72 m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem136175 m n) (@lem136174 m n)). Qed.
Lemma lem136186 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem136187 (m : nat) (n : nat) : (term106 m n) = (term107 m n).
Proof. exact (MK_COMB (@lem136186) (@lem136185 m n)). Qed.
Lemma lem136188 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem136189 (m : nat) (n : nat) : ((term72 m n) = (NUMERAL 0)) = ((Nat.sub m n) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem136187 m n) (@lem136188)). Qed.
Lemma lem136191 (n : nat) (m : nat) (h1 : term13 m) : ((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n).
Proof. exact (EQ_MP (@lem136178 m n) (@lem136177 n m h1)). Qed.
Lemma lem136192 (n : nat) (m : nat) (h1 : term13 m) : ((term72 m n) = (NUMERAL 0)) = (Peano.le m n).
Proof. exact (TRANS (@lem136189 m n) (@lem136191 n m h1)). Qed.
Lemma lem136193 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem136194 (n : nat) (m : nat) (h1 : term13 m) : (term108 m n) = (term109 m n).
Proof. exact (MK_COMB (@lem136193) (@lem136192 n m h1)). Qed.
Lemma lem136196 (m : nat) (n : nat) : (term73 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem136169 m n) (@lem136168 m n)). Qed.
Lemma lem136197 (n : nat) (m : nat) (h1 : term13 m) : (((term72 m n) = (NUMERAL 0)) = (term73 m n)) = ((Peano.le m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem136194 n m h1) (@lem136196 m n)). Qed.
Lemma lem136199 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem136200 (x : Prop) : (x = x) = True.
Proof. exact (@lem136199 Prop x). Qed.
Lemma lem136201 (m : nat) (n : nat) : ((Peano.le m n) = (Peano.le m n)) = True.
Proof. exact (@lem136200 (Peano.le m n)). Qed.
Lemma lem136202 (n : nat) (m : nat) (h1 : term13 m) : (((term72 m n) = (NUMERAL 0)) = (term73 m n)) = True.
Proof. exact (TRANS (@lem136197 n m h1) (@lem136201 m n)). Qed.
Lemma lem136203 (n : nat) (m : nat) (h1 : term13 m) : True = (((term72 m n) = (NUMERAL 0)) = (term73 m n)).
Proof. exact (SYM (@lem136202 n m h1)). Qed.
Lemma lem136204 (n : nat) (m : nat) (h1 : term13 m) : ((term72 m n) = (NUMERAL 0)) = (term73 m n).
Proof. exact (EQ_MP (@lem136203 n m h1) (@lem0)). Qed.
Lemma lem136206 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem135943 n) (@lem135942 n)). Qed.
Lemma lem136207 : term36 = True.
Proof. exact (@lem136206 (NUMERAL 0)). Qed.
Lemma lem136208 : True = term36.
Proof. exact (SYM (@lem136207)). Qed.
Lemma lem136209 : term36.
Proof. exact (EQ_MP (@lem136208) (@lem0)). Qed.
Lemma lem136211 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem135943 n) (@lem135942 n)). Qed.
Lemma lem136212 (n : nat) : (term45 n) = True.
Proof. exact (@lem136211 (S n)). Qed.
Lemma lem136213 (n : nat) : True = (term45 n).
Proof. exact (SYM (@lem136212 n)). Qed.
Lemma lem136214 (n : nat) : term45 n.
Proof. exact (EQ_MP (@lem136213 n) (@lem0)). Qed.
Lemma lem136220 (m : nat) : (term4 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem135954 m) (@lem135953 m)). Qed.
Lemma lem136221 (m : nat) : (term63 m) = ((S m) = (NUMERAL 0)).
Proof. exact (@lem136220 (S m)). Qed.
Lemma lem136224 (m : nat) : (term98 m) = (term98 m).
Proof. exact (eq_refl (term98 m)). Qed.
Lemma lem136225 (m : nat) : (((S m) = (NUMERAL 0)) = (term63 m)) = (((S m) = (NUMERAL 0)) = ((S m) = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem136224 m) (@lem136221 m)). Qed.
Lemma lem136227 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem136228 (x : Prop) : (x = x) = True.
Proof. exact (@lem136227 Prop x). Qed.
Lemma lem136229 (m : nat) : (((S m) = (NUMERAL 0)) = ((S m) = (NUMERAL 0))) = True.
Proof. exact (@lem136228 ((S m) = (NUMERAL 0))). Qed.
Lemma lem136230 (m : nat) : (((S m) = (NUMERAL 0)) = (term63 m)) = True.
Proof. exact (TRANS (@lem136225 m) (@lem136229 m)). Qed.
Lemma lem136231 (m : nat) : True = (((S m) = (NUMERAL 0)) = (term63 m)).
Proof. exact (SYM (@lem136230 m)). Qed.
Lemma lem136232 (m : nat) : ((S m) = (NUMERAL 0)) = (term63 m).
Proof. exact (EQ_MP (@lem136231 m) (@lem0)). Qed.
Lemma lem136233 (m : nat) : ((term62 m) = (NUMERAL 0)) = (term63 m).
Proof. exact (EQ_MP (@lem136159 m) (@lem136232 m)). Qed.
Lemma lem136234 (n : nat) : ((term44 n) = (NUMERAL 0)) = (term45 n).
Proof. exact (EQ_MP (@lem136119 n) (@lem136214 n)). Qed.
Lemma lem136235 : (term35 = (NUMERAL 0)) = term36.
Proof. exact (EQ_MP (@lem136077) (@lem136209)). Qed.
Lemma lem136236 (n : nat) (m : nat) (h1 : term13 m) : term75 m n.
Proof. exact (fun h0 : ((term67 m n) = (NUMERAL 0)) = (term68 m n) => @lem136204 n m h1). Qed.
Lemma lem136241 (m : nat) (h1 : term13 m) : term79 m.
Proof. exact (fun n : nat => @lem136236 n m h1). Qed.
Lemma lem136242 (m : nat) (h1 : term13 m) : term81 m.
Proof. exact (conj (@lem136233 m) (@lem136241 m h1)). Qed.
Lemma lem136243 (m : nat) (h1 : term13 m) : term17 m.
Proof. exact (@lem136030 m (@lem136242 m h1)). Qed.
Lemma lem136244 (n : nat) : term47 n.
Proof. exact (fun h0 : ((term40 n) = (NUMERAL 0)) = (term1 n) => @lem136234 n). Qed.
Lemma lem136249 : term51.
Proof. exact (fun n : nat => @lem136244 n). Qed.
Lemma lem136250 : term53.
Proof. exact (conj (@lem136235) (@lem136249)). Qed.
Lemma lem136251 : term9.
Proof. exact (@lem136002 (@lem136250)). Qed.
Lemma lem136252 (m : nat) : term19 m.
Proof. exact (fun h0 : term13 m => @lem136243 m h0). Qed.
Lemma lem136257 : term23.
Proof. exact (fun m : nat => @lem136252 m). Qed.
Lemma lem136258 : term25.
Proof. exact (conj (@lem136251) (@lem136257)). Qed.
Lemma lem136259 : term30.
Proof. exact (@lem135978 (@lem136258)). Qed.
