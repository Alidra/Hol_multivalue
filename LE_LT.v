Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_LT_term_abbrevs.
Require Import LE_0_spec.
Require Import LE_SUC_spec.
Require Import LT_0_spec.
Require Import LT_SUC_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1833_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm89498_spec.
Require Import thm89994_spec.
Lemma lem96971 : term0.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem96972 (m : nat) : term1 m.
Proof. exact (@lem96971 m). Qed.
Lemma lem96973 (m : nat) : (term1 m) = ((term2 m) = False).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem96982 : term3.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem96983 (m : nat) : term4 m.
Proof. exact (@lem96982 m). Qed.
Lemma lem96984 (m : nat) : (term4 m) = ((term5 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem96987 (P : nat -> Prop) : term6 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem96988 : term7.
Proof. exact (@lem96987 term8). Qed.
Lemma lem96989 : term9 = term10.
Proof. exact (eq_refl term9). Qed.
Lemma lem96990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem96991 : term11 = term12.
Proof. exact (MK_COMB (@lem96990) (@lem96989)). Qed.
Lemma lem96992 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem96993 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96994 (m : nat) : (term15 m) = (term16 m).
Proof. exact (MK_COMB (@lem96993) (@lem96992 m)). Qed.
Lemma lem96995 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem96996 (m : nat) : (term19 m) = (term20 m).
Proof. exact (MK_COMB (@lem96994 m) (@lem96995 m)). Qed.
Lemma lem96997 : term21 = term22.
Proof. exact (fun_ext (fun m : nat => @lem96996 m)). Qed.
Lemma lem96998 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96999 : term23 = term24.
Proof. exact (MK_COMB (@lem96998) (@lem96997)). Qed.
Lemma lem97000 : term25 = term26.
Proof. exact (MK_COMB (@lem96991) (@lem96999)). Qed.
Lemma lem97001 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem97002 : term27 = term28.
Proof. exact (MK_COMB (@lem97001) (@lem97000)). Qed.
Lemma lem97003 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem97004 : term29 = term8.
Proof. exact (fun_ext (fun m : nat => @lem97003 m)). Qed.
Lemma lem97005 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97006 : term30 = term31.
Proof. exact (MK_COMB (@lem97005) (@lem97004)). Qed.
Lemma lem97007 : term7 = term32.
Proof. exact (MK_COMB (@lem97002) (@lem97006)). Qed.
Lemma lem97008 : term32.
Proof. exact (EQ_MP (@lem97007) (@lem96988)). Qed.
Lemma lem97009 (m : nat) (h1 : term14 m) : term14 m.
Proof. exact (h1). Qed.
Lemma lem97011 (P : nat -> Prop) : term6 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem97012 : term33.
Proof. exact (@lem97011 term34). Qed.
Lemma lem97013 : term35 = (term36 = term37).
Proof. exact (eq_refl term35). Qed.
Lemma lem97014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem97015 : term38 = term39.
Proof. exact (MK_COMB (@lem97014) (@lem97013)). Qed.
Lemma lem97016 (n : nat) : (term40 n) = ((term41 n) = (term42 n)).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem97017 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem97018 (n : nat) : (term43 n) = (term44 n).
Proof. exact (MK_COMB (@lem97017) (@lem97016 n)). Qed.
Lemma lem97019 (n : nat) : (term45 n) = ((term46 n) = (term47 n)).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem97020 (n : nat) : (term48 n) = (term49 n).
Proof. exact (MK_COMB (@lem97018 n) (@lem97019 n)). Qed.
Lemma lem97021 : term50 = term51.
Proof. exact (fun_ext (fun n : nat => @lem97020 n)). Qed.
Lemma lem97022 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97023 : term52 = term53.
Proof. exact (MK_COMB (@lem97022) (@lem97021)). Qed.
Lemma lem97024 : term54 = term55.
Proof. exact (MK_COMB (@lem97015) (@lem97023)). Qed.
Lemma lem97025 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem97026 : term56 = term57.
Proof. exact (MK_COMB (@lem97025) (@lem97024)). Qed.
Lemma lem97027 (n : nat) : (term40 n) = ((term41 n) = (term42 n)).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem97028 : term58 = term34.
Proof. exact (fun_ext (fun n : nat => @lem97027 n)). Qed.
Lemma lem97029 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97030 : term59 = term10.
Proof. exact (MK_COMB (@lem97029) (@lem97028)). Qed.
Lemma lem97031 : term33 = term60.
Proof. exact (MK_COMB (@lem97026) (@lem97030)). Qed.
Lemma lem97032 : term60.
Proof. exact (EQ_MP (@lem97031) (@lem97012)). Qed.
Lemma lem97039 (P : nat -> Prop) : term6 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem97040 (m : nat) : term61 m.
Proof. exact (@lem97039 (term62 m)). Qed.
Lemma lem97041 (m : nat) : (term63 m) = ((term64 m) = (term65 m)).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem97042 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem97043 (m : nat) : (term66 m) = (term67 m).
Proof. exact (MK_COMB (@lem97042) (@lem97041 m)). Qed.
Lemma lem97044 (m : nat) (n : nat) : (term68 m n) = ((term69 m n) = (term70 m n)).
Proof. exact (eq_refl (term68 m n)). Qed.
Lemma lem97045 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem97046 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (MK_COMB (@lem97045) (@lem97044 m n)). Qed.
Lemma lem97047 (m : nat) (n : nat) : (term73 m n) = ((term74 m n) = (term75 m n)).
Proof. exact (eq_refl (term73 m n)). Qed.
Lemma lem97048 (m : nat) (n : nat) : (term76 m n) = (term77 m n).
Proof. exact (MK_COMB (@lem97046 m n) (@lem97047 m n)). Qed.
Lemma lem97049 (m : nat) : (term78 m) = (term79 m).
Proof. exact (fun_ext (fun n : nat => @lem97048 m n)). Qed.
Lemma lem97050 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97051 (m : nat) : (term80 m) = (term81 m).
Proof. exact (MK_COMB (@lem97050) (@lem97049 m)). Qed.
Lemma lem97052 (m : nat) : (term82 m) = (term83 m).
Proof. exact (MK_COMB (@lem97043 m) (@lem97051 m)). Qed.
Lemma lem97053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem97054 (m : nat) : (term84 m) = (term85 m).
Proof. exact (MK_COMB (@lem97053) (@lem97052 m)). Qed.
Lemma lem97055 (m : nat) (n : nat) : (term68 m n) = ((term69 m n) = (term70 m n)).
Proof. exact (eq_refl (term68 m n)). Qed.
Lemma lem97056 (m : nat) : (term86 m) = (term62 m).
Proof. exact (fun_ext (fun n : nat => @lem97055 m n)). Qed.
Lemma lem97057 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97058 (m : nat) : (term87 m) = (term18 m).
Proof. exact (MK_COMB (@lem97057) (@lem97056 m)). Qed.
Lemma lem97059 (m : nat) : (term61 m) = (term88 m).
Proof. exact (MK_COMB (@lem97054 m) (@lem97058 m)). Qed.
Lemma lem97060 (m : nat) : term88 m.
Proof. exact (EQ_MP (@lem97059 m) (@lem97040 m)). Qed.
Lemma lem97071 (n : nat) : term89 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem97072 (n : nat) : (term89 n) = (term41 n).
Proof. exact (eq_refl (term89 n)). Qed.
Lemma lem97073 (n : nat) : term41 n.
Proof. exact (EQ_MP (@lem97072 n) (@lem97071 n)). Qed.
Lemma lem97074 (n : nat) : (term41 n) = ((term41 n) = True).
Proof. exact (@lem7 (term41 n)). Qed.
Lemma lem97097 (n : nat) : (term41 n) = True.
Proof. exact (EQ_MP (@lem97074 n) (@lem97073 n)). Qed.
Lemma lem97098 : term36 = True.
Proof. exact (@lem97097 (NUMERAL 0)). Qed.
Lemma lem97099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem97100 : term90 = (@eq Prop True).
Proof. exact (MK_COMB (@lem97099) (@lem97098)). Qed.
Lemma lem97104 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem97105 (x : nat) : (x = x) = True.
Proof. exact (@lem97104 nat x). Qed.
Lemma lem97106 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem97105 (NUMERAL 0)). Qed.
Lemma lem97107 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem97108 : term37 = term92.
Proof. exact (MK_COMB (@lem97107) (@lem97106)). Qed.
Lemma lem97110 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem97111 : term92 = True.
Proof. exact (@lem97110 term93). Qed.
Lemma lem97112 : term37 = True.
Proof. exact (TRANS (@lem97108) (@lem97111)). Qed.
Lemma lem97113 : (term36 = term37) = (True = True).
Proof. exact (MK_COMB (@lem97100) (@lem97112)). Qed.
Lemma lem97115 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem97116 : (True = True) = True.
Proof. exact (@lem97115 True). Qed.
Lemma lem97117 : (term36 = term37) = True.
Proof. exact (TRANS (@lem97113) (@lem97116)). Qed.
Lemma lem97118 : True = (term36 = term37).
Proof. exact (SYM (@lem97117)). Qed.
Lemma lem97119 : term36 = term37.
Proof. exact (EQ_MP (@lem97118) (@lem0)). Qed.
Lemma lem97120 (n : nat) : term94 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem97121 (n : nat) : (term94 n) = (term95 n).
Proof. exact (eq_refl (term94 n)). Qed.
Lemma lem97122 (n : nat) : term95 n.
Proof. exact (EQ_MP (@lem97121 n) (@lem97120 n)). Qed.
Lemma lem97123 (n : nat) : (term95 n) = ((term95 n) = True).
Proof. exact (@lem7 (term95 n)). Qed.
Lemma lem97125 (n : nat) : term89 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem97126 (n : nat) : (term89 n) = (term41 n).
Proof. exact (eq_refl (term89 n)). Qed.
Lemma lem97127 (n : nat) : term41 n.
Proof. exact (EQ_MP (@lem97126 n) (@lem97125 n)). Qed.
Lemma lem97128 (n : nat) : (term41 n) = ((term41 n) = True).
Proof. exact (@lem7 (term41 n)). Qed.
Lemma lem97151 (n : nat) : (term41 n) = True.
Proof. exact (EQ_MP (@lem97128 n) (@lem97127 n)). Qed.
Lemma lem97152 (n : nat) : (term46 n) = True.
Proof. exact (@lem97151 (S n)). Qed.
Lemma lem97153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem97154 (n : nat) : (term96 n) = (@eq Prop True).
Proof. exact (MK_COMB (@lem97153) (@lem97152 n)). Qed.
Lemma lem97158 (n : nat) : (term95 n) = True.
Proof. exact (EQ_MP (@lem97123 n) (@lem97122 n)). Qed.
Lemma lem97159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem97160 (n : nat) : (term97 n) = (or True).
Proof. exact (MK_COMB (@lem97159) (@lem97158 n)). Qed.
Lemma lem97163 (n : nat) : ((NUMERAL 0) = (S n)) = ((NUMERAL 0) = (S n)).
Proof. exact (eq_refl ((NUMERAL 0) = (S n))). Qed.
Lemma lem97164 (n : nat) : (term47 n) = (term98 n).
Proof. exact (MK_COMB (@lem97160 n) (@lem97163 n)). Qed.
Lemma lem97166 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem97167 (n : nat) : (term98 n) = True.
Proof. exact (@lem97166 ((NUMERAL 0) = (S n))). Qed.
Lemma lem97168 (n : nat) : (term47 n) = True.
Proof. exact (TRANS (@lem97164 n) (@lem97167 n)). Qed.
Lemma lem97169 (n : nat) : ((term46 n) = (term47 n)) = (True = True).
Proof. exact (MK_COMB (@lem97154 n) (@lem97168 n)). Qed.
Lemma lem97171 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem97172 : (True = True) = True.
Proof. exact (@lem97171 True). Qed.
Lemma lem97173 (n : nat) : ((term46 n) = (term47 n)) = True.
Proof. exact (TRANS (@lem97169 n) (@lem97172)). Qed.
Lemma lem97174 (n : nat) : True = ((term46 n) = (term47 n)).
Proof. exact (SYM (@lem97173 n)). Qed.
Lemma lem97175 (n : nat) : (term46 n) = (term47 n).
Proof. exact (EQ_MP (@lem97174 n) (@lem0)). Qed.
Lemma lem97225 (m : nat) : term99 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem97226 (m : nat) : (term99 m) = (term100 m).
Proof. exact (eq_refl (term99 m)). Qed.
Lemma lem97227 (m : nat) : term100 m.
Proof. exact (EQ_MP (@lem97226 m) (@lem97225 m)). Qed.
Lemma lem97228 (m : nat) (n : nat) : term101 m n.
Proof. exact (@lem97227 m n). Qed.
Lemma lem97229 (m : nat) (n : nat) : (term101 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term101 m n)). Qed.
Lemma lem97231 (m : nat) : term102 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem97232 (m : nat) : (term102 m) = (term103 m).
Proof. exact (eq_refl (term102 m)). Qed.
Lemma lem97233 (m : nat) : term103 m.
Proof. exact (EQ_MP (@lem97232 m) (@lem97231 m)). Qed.
Lemma lem97234 (m : nat) (n : nat) : term104 m n.
Proof. exact (@lem97233 m n). Qed.
Lemma lem97235 (m : nat) (n : nat) : (term104 m n) = ((term105 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term104 m n)). Qed.
Lemma lem97237 (m : nat) : term106 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem97238 (m : nat) : (term106 m) = (term107 m).
Proof. exact (eq_refl (term106 m)). Qed.
Lemma lem97239 (m : nat) : term107 m.
Proof. exact (EQ_MP (@lem97238 m) (@lem97237 m)). Qed.
Lemma lem97240 (m : nat) (n : nat) : term108 m n.
Proof. exact (@lem97239 m n). Qed.
Lemma lem97241 (m : nat) (n : nat) : (term108 m n) = ((term74 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term108 m n)). Qed.
Lemma lem97243 (n : nat) (m : nat) (h1 : term14 m) : term109 m n.
Proof. exact (@lem97009 m h1 n). Qed.
Lemma lem97244 (m : nat) (n : nat) : (term109 m n) = ((Peano.le m n) = (term110 m n)).
Proof. exact (eq_refl (term109 m n)). Qed.
Lemma lem97249 (m : nat) (n : nat) : (term74 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem97241 m n) (@lem97240 m n)). Qed.
Lemma lem97251 (n : nat) (m : nat) (h1 : term14 m) : (Peano.le m n) = (term110 m n).
Proof. exact (EQ_MP (@lem97244 m n) (@lem97243 n m h1)). Qed.
Lemma lem97254 (n : nat) (m : nat) (h1 : term14 m) : (term74 m n) = (term110 m n).
Proof. exact (TRANS (@lem97249 m n) (@lem97251 n m h1)). Qed.
Lemma lem97257 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem97258 (n : nat) (m : nat) (h1 : term14 m) : (term111 m n) = (term112 m n).
Proof. exact (MK_COMB (@lem97257) (@lem97254 n m h1)). Qed.
Lemma lem97262 (m : nat) (n : nat) : (term105 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem97235 m n) (@lem97234 m n)). Qed.
Lemma lem97263 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem97264 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (MK_COMB (@lem97263) (@lem97262 m n)). Qed.
Lemma lem97266 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem97229 m n) (@lem97228 m n)). Qed.
Lemma lem97269 (m : nat) (n : nat) : (term75 m n) = (term110 m n).
Proof. exact (MK_COMB (@lem97264 m n) (@lem97266 m n)). Qed.
Lemma lem97272 (n : nat) (m : nat) (h1 : term14 m) : ((term74 m n) = (term75 m n)) = ((term110 m n) = (term110 m n)).
Proof. exact (MK_COMB (@lem97258 n m h1) (@lem97269 m n)). Qed.
Lemma lem97274 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem97275 (x : Prop) : (x = x) = True.
Proof. exact (@lem97274 Prop x). Qed.
Lemma lem97276 (m : nat) (n : nat) : ((term110 m n) = (term110 m n)) = True.
Proof. exact (@lem97275 (term110 m n)). Qed.
Lemma lem97277 (n : nat) (m : nat) (h1 : term14 m) : ((term74 m n) = (term75 m n)) = True.
Proof. exact (TRANS (@lem97272 n m h1) (@lem97276 m n)). Qed.
Lemma lem97278 (n : nat) (m : nat) (h1 : term14 m) : True = ((term74 m n) = (term75 m n)).
Proof. exact (SYM (@lem97277 n m h1)). Qed.
Lemma lem97279 (n : nat) (m : nat) (h1 : term14 m) : (term74 m n) = (term75 m n).
Proof. exact (EQ_MP (@lem97278 n m h1) (@lem0)). Qed.
Lemma lem97283 (m : nat) : (term5 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem96984 m) (@lem96983 m)). Qed.
Lemma lem97284 (m : nat) : (term64 m) = ((S m) = (NUMERAL 0)).
Proof. exact (@lem97283 (S m)). Qed.
Lemma lem97287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem97288 (m : nat) : (term115 m) = (term116 m).
Proof. exact (MK_COMB (@lem97287) (@lem97284 m)). Qed.
Lemma lem97292 (m : nat) : (term2 m) = False.
Proof. exact (EQ_MP (@lem96973 m) (@lem96972 m)). Qed.
Lemma lem97293 (m : nat) : (term117 m) = False.
Proof. exact (@lem97292 (S m)). Qed.
Lemma lem97294 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem97295 (m : nat) : (term118 m) = (or False).
Proof. exact (MK_COMB (@lem97294) (@lem97293 m)). Qed.
Lemma lem97298 (m : nat) : ((S m) = (NUMERAL 0)) = ((S m) = (NUMERAL 0)).
Proof. exact (eq_refl ((S m) = (NUMERAL 0))). Qed.
Lemma lem97299 (m : nat) : (term65 m) = (term119 m).
Proof. exact (MK_COMB (@lem97295 m) (@lem97298 m)). Qed.
Lemma lem97301 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem97302 (m : nat) : (term119 m) = ((S m) = (NUMERAL 0)).
Proof. exact (@lem97301 ((S m) = (NUMERAL 0))). Qed.
Lemma lem97305 (m : nat) : (term65 m) = ((S m) = (NUMERAL 0)).
Proof. exact (TRANS (@lem97299 m) (@lem97302 m)). Qed.
Lemma lem97306 (m : nat) : ((term64 m) = (term65 m)) = (((S m) = (NUMERAL 0)) = ((S m) = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem97288 m) (@lem97305 m)). Qed.
Lemma lem97308 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem97309 (x : Prop) : (x = x) = True.
Proof. exact (@lem97308 Prop x). Qed.
Lemma lem97310 (m : nat) : (((S m) = (NUMERAL 0)) = ((S m) = (NUMERAL 0))) = True.
Proof. exact (@lem97309 ((S m) = (NUMERAL 0))). Qed.
Lemma lem97311 (m : nat) : ((term64 m) = (term65 m)) = True.
Proof. exact (TRANS (@lem97306 m) (@lem97310 m)). Qed.
Lemma lem97312 (m : nat) : True = ((term64 m) = (term65 m)).
Proof. exact (SYM (@lem97311 m)). Qed.
Lemma lem97314 (m : nat) : (term64 m) = (term65 m).
Proof. exact (EQ_MP (@lem97312 m) (@lem0)). Qed.
Lemma lem97315 (n : nat) (m : nat) (h1 : term14 m) : term77 m n.
Proof. exact (fun h0 : (term69 m n) = (term70 m n) => @lem97279 n m h1). Qed.
Lemma lem97320 (m : nat) (h1 : term14 m) : term81 m.
Proof. exact (fun n : nat => @lem97315 n m h1). Qed.
Lemma lem97321 (m : nat) (h1 : term14 m) : term83 m.
Proof. exact (conj (@lem97314 m) (@lem97320 m h1)). Qed.
Lemma lem97322 (m : nat) (h1 : term14 m) : term18 m.
Proof. exact (@lem97060 m (@lem97321 m h1)). Qed.
Lemma lem97323 (n : nat) : term49 n.
Proof. exact (fun h0 : (term41 n) = (term42 n) => @lem97175 n). Qed.
Lemma lem97328 : term53.
Proof. exact (fun n : nat => @lem97323 n). Qed.
Lemma lem97329 : term55.
Proof. exact (conj (@lem97119) (@lem97328)). Qed.
Lemma lem97330 : term10.
Proof. exact (@lem97032 (@lem97329)). Qed.
Lemma lem97331 (m : nat) : term20 m.
Proof. exact (fun h0 : term14 m => @lem97322 m h0). Qed.
Lemma lem97336 : term24.
Proof. exact (fun m : nat => @lem97331 m). Qed.
Lemma lem97337 : term26.
Proof. exact (conj (@lem97330) (@lem97336)). Qed.
Lemma lem97338 : term31.
Proof. exact (@lem97008 (@lem97337)). Qed.
