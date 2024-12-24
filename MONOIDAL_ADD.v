Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MONOIDAL_ADD_term_abbrevs.
Require Import INT_POS_spec.
Require Import monoidal_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032058_spec.
Require Import thm1032092_spec.
Require Import thm1032098_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16485_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19024_spec.
Require Import thm19025_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19158_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm6920431_spec.
Require Import thm6921992_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem6921994 {A : Type'} (op : type1400 A) : term0 A op.
Proof. exact (@lem5712802 A op). Qed.
Lemma lem6921995 {A : Type'} (op : type1400 A) : (term0 A op) = ((@monoidal A op) = (term1 A op)).
Proof. exact (eq_refl (term0 A op)). Qed.
Lemma lem6921998 {A : Type'} (op : type1400 A) : (@monoidal A op) = (term1 A op).
Proof. exact (EQ_MP (@lem6921995 A op) (@lem6921994 A op)). Qed.
Lemma lem6921999 (op : type1606) : (@monoidal nat op) = (term2 op).
Proof. exact (@lem6921998 nat op). Qed.
Lemma lem6922000 : (@monoidal nat Nat.add) = term3.
Proof. exact (@lem6921999 Nat.add). Qed.
Lemma lem6922036 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem6922037 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem6922038 : term4 = term5.
Proof. exact (MK_COMB (@lem6922037) (@lem6922036)). Qed.
Lemma lem6922039 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6922040 (x : nat) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem6922038) (@lem6922039 x)). Qed.
Lemma lem6922041 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6922042 (x : nat) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem6922041) (@lem6922040 x)). Qed.
Lemma lem6922043 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6922044 (x : nat) : ((term6 x) = x) = ((term7 x) = x).
Proof. exact (MK_COMB (@lem6922042 x) (@lem6922043 x)). Qed.
Lemma lem6922047 : term10 = term11.
Proof. exact (fun_ext (fun x : nat => @lem6922044 x)). Qed.
Lemma lem6922048 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922049 : term12 = term13.
Proof. exact (MK_COMB (@lem6922048) (@lem6922047)). Qed.
Lemma lem6922054 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem6922055 : term15 = term16.
Proof. exact (MK_COMB (@lem6922054) (@lem6922049)). Qed.
Lemma lem6922058 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem6922059 : term3 = term18.
Proof. exact (MK_COMB (@lem6922058) (@lem6922055)). Qed.
Lemma lem6922062 : (@monoidal nat Nat.add) = term18.
Proof. exact (TRANS (@lem6922000) (@lem6922059)). Qed.
Lemma lem6922063 : term18 = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem6922062)). Qed.
Lemma lem6922099 (x : nat) : ((term7 x) = x) = ((term7 x) = x).
Proof. exact (eq_refl ((term7 x) = x)). Qed.
Lemma lem6922100 : term11 = term11.
Proof. exact (fun_ext (fun x : nat => @lem6922099 x)). Qed.
Lemma lem6922101 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922102 : term13 = term13.
Proof. exact (MK_COMB (@lem6922101) (@lem6922100)). Qed.
Lemma lem6922103 (x : nat) (y : nat) (z : nat) : ((term19 x y z) = (term20 x y z)) = ((term19 x y z) = (term20 x y z)).
Proof. exact (eq_refl ((term19 x y z) = (term20 x y z))). Qed.
Lemma lem6922104 (x : nat) (y : nat) : (term21 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : nat => @lem6922103 x y z)). Qed.
Lemma lem6922105 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922106 (x : nat) (y : nat) : (term22 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem6922105) (@lem6922104 x y)). Qed.
Lemma lem6922107 (x : nat) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : nat => @lem6922106 x y)). Qed.
Lemma lem6922108 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922109 (x : nat) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem6922108) (@lem6922107 x)). Qed.
Lemma lem6922110 : term25 = term25.
Proof. exact (fun_ext (fun x : nat => @lem6922109 x)). Qed.
Lemma lem6922111 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922112 : term26 = term26.
Proof. exact (MK_COMB (@lem6922111) (@lem6922110)). Qed.
Lemma lem6922113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922114 : term14 = term14.
Proof. exact (MK_COMB (@lem6922113) (@lem6922112)). Qed.
Lemma lem6922115 : term16 = term16.
Proof. exact (MK_COMB (@lem6922114) (@lem6922102)). Qed.
Lemma lem6922116 (y : nat) (x : nat) : ((Nat.add x y) = (Nat.add y x)) = ((Nat.add x y) = (Nat.add y x)).
Proof. exact (eq_refl ((Nat.add x y) = (Nat.add y x))). Qed.
Lemma lem6922117 (x : nat) : (term27 x) = (term27 x).
Proof. exact (fun_ext (fun y : nat => @lem6922116 y x)). Qed.
Lemma lem6922118 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922119 (x : nat) : (term28 x) = (term28 x).
Proof. exact (MK_COMB (@lem6922118) (@lem6922117 x)). Qed.
Lemma lem6922120 : term29 = term29.
Proof. exact (fun_ext (fun x : nat => @lem6922119 x)). Qed.
Lemma lem6922121 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922122 : term30 = term30.
Proof. exact (MK_COMB (@lem6922121) (@lem6922120)). Qed.
Lemma lem6922123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922124 : term17 = term17.
Proof. exact (MK_COMB (@lem6922123) (@lem6922122)). Qed.
Lemma lem6922126 : term18 = term18.
Proof. exact (MK_COMB (@lem6922124) (@lem6922115)). Qed.
Lemma lem6922127 (y : nat) (x : nat) : ((Nat.add x y) = (Nat.add y x)) = ((Nat.add x y) = (Nat.add y x)).
Proof. exact (eq_refl ((Nat.add x y) = (Nat.add y x))). Qed.
Lemma lem6922128 (x : nat) : (term27 x) = (term27 x).
Proof. exact (fun_ext (fun y : nat => @lem6922127 y x)). Qed.
Lemma lem6922129 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922130 (x : nat) : (term28 x) = (term28 x).
Proof. exact (MK_COMB (@lem6922129) (@lem6922128 x)). Qed.
Lemma lem6922131 : term29 = term29.
Proof. exact (fun_ext (fun x : nat => @lem6922130 x)). Qed.
Lemma lem6922132 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922133 : term30 = term30.
Proof. exact (MK_COMB (@lem6922132) (@lem6922131)). Qed.
Lemma lem6922134 (x : nat) (y : nat) (z : nat) : ((term19 x y z) = (term20 x y z)) = ((term19 x y z) = (term20 x y z)).
Proof. exact (eq_refl ((term19 x y z) = (term20 x y z))). Qed.
Lemma lem6922135 (x : nat) (y : nat) : (term21 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : nat => @lem6922134 x y z)). Qed.
Lemma lem6922136 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922137 (x : nat) (y : nat) : (term22 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem6922136) (@lem6922135 x y)). Qed.
Lemma lem6922138 (x : nat) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : nat => @lem6922137 x y)). Qed.
Lemma lem6922139 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922140 (x : nat) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem6922139) (@lem6922138 x)). Qed.
Lemma lem6922141 : term25 = term25.
Proof. exact (fun_ext (fun x : nat => @lem6922140 x)). Qed.
Lemma lem6922142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922143 : term26 = term26.
Proof. exact (MK_COMB (@lem6922142) (@lem6922141)). Qed.
Lemma lem6922144 (x : nat) : ((term7 x) = x) = ((term7 x) = x).
Proof. exact (eq_refl ((term7 x) = x)). Qed.
Lemma lem6922145 : term11 = term11.
Proof. exact (fun_ext (fun x : nat => @lem6922144 x)). Qed.
Lemma lem6922146 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922147 : term13 = term13.
Proof. exact (MK_COMB (@lem6922146) (@lem6922145)). Qed.
Lemma lem6922148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922149 : term14 = term14.
Proof. exact (MK_COMB (@lem6922148) (@lem6922143)). Qed.
Lemma lem6922150 : term16 = term16.
Proof. exact (MK_COMB (@lem6922149) (@lem6922147)). Qed.
Lemma lem6922151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922152 : term17 = term17.
Proof. exact (MK_COMB (@lem6922151) (@lem6922133)). Qed.
Lemma lem6922153 : term18 = term18.
Proof. exact (MK_COMB (@lem6922152) (@lem6922150)). Qed.
Lemma lem6922154 : term18 = term18.
Proof. exact (TRANS (@lem6922126) (@lem6922153)). Qed.
Lemma lem6922155 (x : nat) : ((term7 x) = x) = ((term7 x) = x).
Proof. exact (eq_refl ((term7 x) = x)). Qed.
Lemma lem6922156 : term11 = term11.
Proof. exact (fun_ext (fun x : nat => @lem6922155 x)). Qed.
Lemma lem6922157 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922158 : term13 = term13.
Proof. exact (MK_COMB (@lem6922157) (@lem6922156)). Qed.
Lemma lem6922159 (x : nat) (y : nat) (z : nat) : ((term19 x y z) = (term20 x y z)) = ((term19 x y z) = (term20 x y z)).
Proof. exact (eq_refl ((term19 x y z) = (term20 x y z))). Qed.
Lemma lem6922160 (x : nat) (y : nat) : (term21 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : nat => @lem6922159 x y z)). Qed.
Lemma lem6922161 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922162 (x : nat) (y : nat) : (term22 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem6922161) (@lem6922160 x y)). Qed.
Lemma lem6922163 (x : nat) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : nat => @lem6922162 x y)). Qed.
Lemma lem6922164 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922165 (x : nat) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem6922164) (@lem6922163 x)). Qed.
Lemma lem6922166 : term25 = term25.
Proof. exact (fun_ext (fun x : nat => @lem6922165 x)). Qed.
Lemma lem6922167 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922168 : term26 = term26.
Proof. exact (MK_COMB (@lem6922167) (@lem6922166)). Qed.
Lemma lem6922169 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922170 : term14 = term14.
Proof. exact (MK_COMB (@lem6922169) (@lem6922168)). Qed.
Lemma lem6922171 : term16 = term16.
Proof. exact (MK_COMB (@lem6922170) (@lem6922158)). Qed.
Lemma lem6922172 (y : nat) (x : nat) : ((Nat.add x y) = (Nat.add y x)) = ((Nat.add x y) = (Nat.add y x)).
Proof. exact (eq_refl ((Nat.add x y) = (Nat.add y x))). Qed.
Lemma lem6922173 (x : nat) : (term27 x) = (term27 x).
Proof. exact (fun_ext (fun y : nat => @lem6922172 y x)). Qed.
Lemma lem6922174 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922175 (x : nat) : (term28 x) = (term28 x).
Proof. exact (MK_COMB (@lem6922174) (@lem6922173 x)). Qed.
Lemma lem6922176 : term29 = term29.
Proof. exact (fun_ext (fun x : nat => @lem6922175 x)). Qed.
Lemma lem6922177 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922178 : term30 = term30.
Proof. exact (MK_COMB (@lem6922177) (@lem6922176)). Qed.
Lemma lem6922179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922180 : term17 = term17.
Proof. exact (MK_COMB (@lem6922179) (@lem6922178)). Qed.
Lemma lem6922181 : term18 = term18.
Proof. exact (MK_COMB (@lem6922180) (@lem6922171)). Qed.
Lemma lem6922222 : term18 = term18.
Proof. exact (TRANS (@lem6922154) (@lem6922181)). Qed.
Lemma lem6922223 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6922230 (x : nat) : (term7 x) = x.
Proof. exact (@lem1032058 x). Qed.
Lemma lem6922231 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6922232 (x : nat) : (term9 x) = (@eq nat x).
Proof. exact (MK_COMB (@lem6922231) (@lem6922230 x)). Qed.
Lemma lem6922233 (x : nat) : ((term7 x) = x) = (x = x).
Proof. exact (MK_COMB (@lem6922232 x) (@lem6922223 x)). Qed.
Lemma lem6922234 : term11 = term31.
Proof. exact (fun_ext (fun x : nat => @lem6922233 x)). Qed.
Lemma lem6922235 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922236 : term13 = term32.
Proof. exact (MK_COMB (@lem6922235) (@lem6922234)). Qed.
Lemma lem6922253 (x : nat) (y : nat) (z : nat) : (term20 x y z) = (term19 x y z).
Proof. exact (@lem1032092 x y z). Qed.
Lemma lem6922268 (x : nat) (y : nat) (z : nat) : (term33 x y z) = (term33 x y z).
Proof. exact (eq_refl (term33 x y z)). Qed.
Lemma lem6922269 (x : nat) (y : nat) (z : nat) : ((term19 x y z) = (term20 x y z)) = ((term19 x y z) = (term19 x y z)).
Proof. exact (MK_COMB (@lem6922268 x y z) (@lem6922253 x y z)). Qed.
Lemma lem6922270 (x : nat) (y : nat) : (term21 x y) = (term34 x y).
Proof. exact (fun_ext (fun z : nat => @lem6922269 x y z)). Qed.
Lemma lem6922271 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922272 (x : nat) (y : nat) : (term22 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem6922271) (@lem6922270 x y)). Qed.
Lemma lem6922273 (x : nat) : (term23 x) = (term36 x).
Proof. exact (fun_ext (fun y : nat => @lem6922272 x y)). Qed.
Lemma lem6922274 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922275 (x : nat) : (term24 x) = (term37 x).
Proof. exact (MK_COMB (@lem6922274) (@lem6922273 x)). Qed.
Lemma lem6922276 : term25 = term38.
Proof. exact (fun_ext (fun x : nat => @lem6922275 x)). Qed.
Lemma lem6922277 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922278 : term26 = term39.
Proof. exact (MK_COMB (@lem6922277) (@lem6922276)). Qed.
Lemma lem6922279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922280 : term14 = term40.
Proof. exact (MK_COMB (@lem6922279) (@lem6922278)). Qed.
Lemma lem6922281 : term16 = term41.
Proof. exact (MK_COMB (@lem6922280) (@lem6922236)). Qed.
Lemma lem6922288 (x : nat) (y : nat) : (Nat.add y x) = (Nat.add x y).
Proof. exact (@lem1032098 x y). Qed.
Lemma lem6922297 (x : nat) (y : nat) : (term42 x y) = (term42 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem6922298 (x : nat) (y : nat) : ((Nat.add x y) = (Nat.add y x)) = ((Nat.add x y) = (Nat.add x y)).
Proof. exact (MK_COMB (@lem6922297 x y) (@lem6922288 x y)). Qed.
Lemma lem6922299 (x : nat) : (term27 x) = (term43 x).
Proof. exact (fun_ext (fun y : nat => @lem6922298 x y)). Qed.
Lemma lem6922300 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922301 (x : nat) : (term28 x) = (term44 x).
Proof. exact (MK_COMB (@lem6922300) (@lem6922299 x)). Qed.
Lemma lem6922302 : term29 = term45.
Proof. exact (fun_ext (fun x : nat => @lem6922301 x)). Qed.
Lemma lem6922303 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922304 : term30 = term46.
Proof. exact (MK_COMB (@lem6922303) (@lem6922302)). Qed.
Lemma lem6922305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922306 : term17 = term47.
Proof. exact (MK_COMB (@lem6922305) (@lem6922304)). Qed.
Lemma lem6922307 : term18 = term48.
Proof. exact (MK_COMB (@lem6922306) (@lem6922281)). Qed.
Lemma lem6922308 : term18 = term48.
Proof. exact (TRANS (@lem6922222) (@lem6922307)). Qed.
Lemma lem6922310 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term49 A P Q) = (term50 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6922311 (P : nat -> Prop) (Q : nat -> Prop) : (term51 P Q) = (term52 P Q).
Proof. exact (@lem6922310 nat P Q). Qed.
Lemma lem6922312 : term53 = term54.
Proof. exact (@lem6922311 term38 term31). Qed.
Lemma lem6922313 (x : nat) : (term55 x) = (term37 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem6922314 : term56 = term38.
Proof. exact (fun_ext (fun x : nat => @lem6922313 x)). Qed.
Lemma lem6922315 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922316 : term57 = term39.
Proof. exact (MK_COMB (@lem6922315) (@lem6922314)). Qed.
Lemma lem6922317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922318 : term58 = term40.
Proof. exact (MK_COMB (@lem6922317) (@lem6922316)). Qed.
Lemma lem6922319 (x : nat) : (term59 x) = (x = x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem6922320 : term60 = term31.
Proof. exact (fun_ext (fun x : nat => @lem6922319 x)). Qed.
Lemma lem6922321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922322 : term61 = term32.
Proof. exact (MK_COMB (@lem6922321) (@lem6922320)). Qed.
Lemma lem6922323 : term53 = term41.
Proof. exact (MK_COMB (@lem6922318) (@lem6922322)). Qed.
Lemma lem6922324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6922325 : term62 = term63.
Proof. exact (MK_COMB (@lem6922324) (@lem6922323)). Qed.
Lemma lem6922326 (x : nat) : (term55 x) = (term37 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem6922327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922328 (x : nat) : (term64 x) = (term65 x).
Proof. exact (MK_COMB (@lem6922327) (@lem6922326 x)). Qed.
Lemma lem6922329 (x : nat) : (term59 x) = (x = x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem6922330 (x : nat) : (term66 x) = (term67 x).
Proof. exact (MK_COMB (@lem6922328 x) (@lem6922329 x)). Qed.
Lemma lem6922331 : term68 = term69.
Proof. exact (fun_ext (fun x : nat => @lem6922330 x)). Qed.
Lemma lem6922332 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922333 : term54 = term70.
Proof. exact (MK_COMB (@lem6922332) (@lem6922331)). Qed.
Lemma lem6922334 : (term53 = term54) = (term41 = term70).
Proof. exact (MK_COMB (@lem6922325) (@lem6922333)). Qed.
Lemma lem6922335 : term41 = term70.
Proof. exact (EQ_MP (@lem6922334) (@lem6922312)). Qed.
Lemma lem6922337 {A : Type'} (P : A -> Prop) (Q : Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem6922338 (P : nat -> Prop) (Q : Prop) : (term73 P Q) = (term74 P Q).
Proof. exact (@lem6922337 nat P Q). Qed.
Lemma lem6922339 (x : nat) : (term75 x) = (term76 x).
Proof. exact (@lem6922338 (term36 x) (x = x)). Qed.
Lemma lem6922340 (x : nat) (y : nat) : (term77 x y) = (term35 x y).
Proof. exact (eq_refl (term77 x y)). Qed.
Lemma lem6922341 (x : nat) : (term78 x) = (term36 x).
Proof. exact (fun_ext (fun y : nat => @lem6922340 x y)). Qed.
Lemma lem6922342 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922343 (x : nat) : (term79 x) = (term37 x).
Proof. exact (MK_COMB (@lem6922342) (@lem6922341 x)). Qed.
Lemma lem6922344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922345 (x : nat) : (term80 x) = (term65 x).
Proof. exact (MK_COMB (@lem6922344) (@lem6922343 x)). Qed.
Lemma lem6922346 (x : nat) : (x = x) = (x = x).
Proof. exact (eq_refl (x = x)). Qed.
Lemma lem6922347 (x : nat) : (term75 x) = (term67 x).
Proof. exact (MK_COMB (@lem6922345 x) (@lem6922346 x)). Qed.
Lemma lem6922348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6922349 (x : nat) : (term81 x) = (term82 x).
Proof. exact (MK_COMB (@lem6922348) (@lem6922347 x)). Qed.
Lemma lem6922350 (x : nat) (y : nat) : (term77 x y) = (term35 x y).
Proof. exact (eq_refl (term77 x y)). Qed.
Lemma lem6922351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922352 (x : nat) (y : nat) : (term83 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem6922351) (@lem6922350 x y)). Qed.
Lemma lem6922353 (x : nat) : (x = x) = (x = x).
Proof. exact (eq_refl (x = x)). Qed.
Lemma lem6922354 (y : nat) (x : nat) : (term85 y x) = (term86 y x).
Proof. exact (MK_COMB (@lem6922352 x y) (@lem6922353 x)). Qed.
Lemma lem6922355 (x : nat) : (term87 x) = (term88 x).
Proof. exact (fun_ext (fun y : nat => @lem6922354 y x)). Qed.
Lemma lem6922356 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922357 (x : nat) : (term76 x) = (term89 x).
Proof. exact (MK_COMB (@lem6922356) (@lem6922355 x)). Qed.
Lemma lem6922358 (x : nat) : ((term75 x) = (term76 x)) = ((term67 x) = (term89 x)).
Proof. exact (MK_COMB (@lem6922349 x) (@lem6922357 x)). Qed.
Lemma lem6922359 (x : nat) : (term67 x) = (term89 x).
Proof. exact (EQ_MP (@lem6922358 x) (@lem6922339 x)). Qed.
Lemma lem6922361 {A : Type'} (P : A -> Prop) (Q : Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem6922362 (P : nat -> Prop) (Q : Prop) : (term73 P Q) = (term74 P Q).
Proof. exact (@lem6922361 nat P Q). Qed.
Lemma lem6922363 (y : nat) (x : nat) : (term90 y x) = (term91 y x).
Proof. exact (@lem6922362 (term34 x y) (x = x)). Qed.
Lemma lem6922364 (x : nat) (y : nat) (z : nat) : (term92 x y z) = ((term19 x y z) = (term19 x y z)).
Proof. exact (eq_refl (term92 x y z)). Qed.
Lemma lem6922365 (x : nat) (y : nat) : (term93 x y) = (term34 x y).
Proof. exact (fun_ext (fun z : nat => @lem6922364 x y z)). Qed.
Lemma lem6922366 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922367 (x : nat) (y : nat) : (term94 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem6922366) (@lem6922365 x y)). Qed.
Lemma lem6922368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922369 (x : nat) (y : nat) : (term95 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem6922368) (@lem6922367 x y)). Qed.
Lemma lem6922370 (x : nat) : (x = x) = (x = x).
Proof. exact (eq_refl (x = x)). Qed.
Lemma lem6922371 (y : nat) (x : nat) : (term90 y x) = (term86 y x).
Proof. exact (MK_COMB (@lem6922369 x y) (@lem6922370 x)). Qed.
Lemma lem6922372 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6922373 (y : nat) (x : nat) : (term96 y x) = (term97 y x).
Proof. exact (MK_COMB (@lem6922372) (@lem6922371 y x)). Qed.
Lemma lem6922374 (x : nat) (y : nat) (z : nat) : (term92 x y z) = ((term19 x y z) = (term19 x y z)).
Proof. exact (eq_refl (term92 x y z)). Qed.
Lemma lem6922375 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922376 (x : nat) (y : nat) (z : nat) : (term98 x y z) = (term99 x y z).
Proof. exact (MK_COMB (@lem6922375) (@lem6922374 x y z)). Qed.
Lemma lem6922377 (x : nat) : (x = x) = (x = x).
Proof. exact (eq_refl (x = x)). Qed.
Lemma lem6922378 (y : nat) (z : nat) (x : nat) : (term100 y z x) = (term101 y z x).
Proof. exact (MK_COMB (@lem6922376 x y z) (@lem6922377 x)). Qed.
Lemma lem6922379 (y : nat) (x : nat) : (term102 y x) = (term103 y x).
Proof. exact (fun_ext (fun z : nat => @lem6922378 y z x)). Qed.
Lemma lem6922380 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922381 (y : nat) (x : nat) : (term91 y x) = (term104 y x).
Proof. exact (MK_COMB (@lem6922380) (@lem6922379 y x)). Qed.
Lemma lem6922382 (y : nat) (x : nat) : ((term90 y x) = (term91 y x)) = ((term86 y x) = (term104 y x)).
Proof. exact (MK_COMB (@lem6922373 y x) (@lem6922381 y x)). Qed.
Lemma lem6922383 (y : nat) (x : nat) : (term86 y x) = (term104 y x).
Proof. exact (EQ_MP (@lem6922382 y x) (@lem6922363 y x)). Qed.
Lemma lem6922384 (x : nat) : (term88 x) = (term105 x).
Proof. exact (fun_ext (fun y : nat => @lem6922383 y x)). Qed.
Lemma lem6922385 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922386 (x : nat) : (term89 x) = (term106 x).
Proof. exact (MK_COMB (@lem6922385) (@lem6922384 x)). Qed.
Lemma lem6922387 (x : nat) : (term67 x) = (term106 x).
Proof. exact (TRANS (@lem6922359 x) (@lem6922386 x)). Qed.
Lemma lem6922388 : term69 = term107.
Proof. exact (fun_ext (fun x : nat => @lem6922387 x)). Qed.
Lemma lem6922389 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922390 : term70 = term108.
Proof. exact (MK_COMB (@lem6922389) (@lem6922388)). Qed.
Lemma lem6922391 : term41 = term108.
Proof. exact (TRANS (@lem6922335) (@lem6922390)). Qed.
Lemma lem6922392 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem6922393 : term48 = term109.
Proof. exact (MK_COMB (@lem6922392) (@lem6922391)). Qed.
Lemma lem6922395 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term49 A P Q) = (term50 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6922396 (P : nat -> Prop) (Q : nat -> Prop) : (term51 P Q) = (term52 P Q).
Proof. exact (@lem6922395 nat P Q). Qed.
Lemma lem6922397 : term110 = term111.
Proof. exact (@lem6922396 term45 term107). Qed.
Lemma lem6922398 (x : nat) : (term112 x) = (term44 x).
Proof. exact (eq_refl (term112 x)). Qed.
Lemma lem6922399 : term113 = term45.
Proof. exact (fun_ext (fun x : nat => @lem6922398 x)). Qed.
Lemma lem6922400 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922401 : term114 = term46.
Proof. exact (MK_COMB (@lem6922400) (@lem6922399)). Qed.
Lemma lem6922402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922403 : term115 = term47.
Proof. exact (MK_COMB (@lem6922402) (@lem6922401)). Qed.
Lemma lem6922404 (x : nat) : (term116 x) = (term106 x).
Proof. exact (eq_refl (term116 x)). Qed.
Lemma lem6922405 : term117 = term107.
Proof. exact (fun_ext (fun x : nat => @lem6922404 x)). Qed.
Lemma lem6922406 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922407 : term118 = term108.
Proof. exact (MK_COMB (@lem6922406) (@lem6922405)). Qed.
Lemma lem6922408 : term110 = term109.
Proof. exact (MK_COMB (@lem6922403) (@lem6922407)). Qed.
Lemma lem6922409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6922410 : term119 = term120.
Proof. exact (MK_COMB (@lem6922409) (@lem6922408)). Qed.
Lemma lem6922411 (x : nat) : (term112 x) = (term44 x).
Proof. exact (eq_refl (term112 x)). Qed.
Lemma lem6922412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922413 (x : nat) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem6922412) (@lem6922411 x)). Qed.
Lemma lem6922414 (x : nat) : (term116 x) = (term106 x).
Proof. exact (eq_refl (term116 x)). Qed.
Lemma lem6922415 (x : nat) : (term123 x) = (term124 x).
Proof. exact (MK_COMB (@lem6922413 x) (@lem6922414 x)). Qed.
Lemma lem6922416 : term125 = term126.
Proof. exact (fun_ext (fun x : nat => @lem6922415 x)). Qed.
Lemma lem6922417 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922418 : term111 = term127.
Proof. exact (MK_COMB (@lem6922417) (@lem6922416)). Qed.
Lemma lem6922419 : (term110 = term111) = (term109 = term127).
Proof. exact (MK_COMB (@lem6922410) (@lem6922418)). Qed.
Lemma lem6922420 : term109 = term127.
Proof. exact (EQ_MP (@lem6922419) (@lem6922397)). Qed.
Lemma lem6922422 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term49 A P Q) = (term50 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6922423 (P : nat -> Prop) (Q : nat -> Prop) : (term51 P Q) = (term52 P Q).
Proof. exact (@lem6922422 nat P Q). Qed.
Lemma lem6922424 (x : nat) : (term128 x) = (term129 x).
Proof. exact (@lem6922423 (term43 x) (term105 x)). Qed.
Lemma lem6922425 (x : nat) (y : nat) : (term130 x y) = ((Nat.add x y) = (Nat.add x y)).
Proof. exact (eq_refl (term130 x y)). Qed.
Lemma lem6922426 (x : nat) : (term131 x) = (term43 x).
Proof. exact (fun_ext (fun y : nat => @lem6922425 x y)). Qed.
Lemma lem6922427 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922428 (x : nat) : (term132 x) = (term44 x).
Proof. exact (MK_COMB (@lem6922427) (@lem6922426 x)). Qed.
Lemma lem6922429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922430 (x : nat) : (term133 x) = (term122 x).
Proof. exact (MK_COMB (@lem6922429) (@lem6922428 x)). Qed.
Lemma lem6922431 (y : nat) (x : nat) : (term134 x y) = (term104 y x).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem6922432 (x : nat) : (term135 x) = (term105 x).
Proof. exact (fun_ext (fun y : nat => @lem6922431 y x)). Qed.
Lemma lem6922433 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922434 (x : nat) : (term136 x) = (term106 x).
Proof. exact (MK_COMB (@lem6922433) (@lem6922432 x)). Qed.
Lemma lem6922435 (x : nat) : (term128 x) = (term124 x).
Proof. exact (MK_COMB (@lem6922430 x) (@lem6922434 x)). Qed.
Lemma lem6922436 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6922437 (x : nat) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem6922436) (@lem6922435 x)). Qed.
Lemma lem6922438 (x : nat) (y : nat) : (term130 x y) = ((Nat.add x y) = (Nat.add x y)).
Proof. exact (eq_refl (term130 x y)). Qed.
Lemma lem6922439 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922440 (x : nat) (y : nat) : (term139 x y) = (term140 x y).
Proof. exact (MK_COMB (@lem6922439) (@lem6922438 x y)). Qed.
Lemma lem6922441 (y : nat) (x : nat) : (term134 x y) = (term104 y x).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem6922442 (y : nat) (x : nat) : (term141 x y) = (term142 y x).
Proof. exact (MK_COMB (@lem6922440 x y) (@lem6922441 y x)). Qed.
Lemma lem6922443 (x : nat) : (term143 x) = (term144 x).
Proof. exact (fun_ext (fun y : nat => @lem6922442 y x)). Qed.
Lemma lem6922444 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922445 (x : nat) : (term129 x) = (term145 x).
Proof. exact (MK_COMB (@lem6922444) (@lem6922443 x)). Qed.
Lemma lem6922446 (x : nat) : ((term128 x) = (term129 x)) = ((term124 x) = (term145 x)).
Proof. exact (MK_COMB (@lem6922437 x) (@lem6922445 x)). Qed.
Lemma lem6922447 (x : nat) : (term124 x) = (term145 x).
Proof. exact (EQ_MP (@lem6922446 x) (@lem6922424 x)). Qed.
Lemma lem6922449 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6922450 (P : Prop) (Q : nat -> Prop) : (term148 P Q) = (term149 P Q).
Proof. exact (@lem6922449 nat P Q). Qed.
Lemma lem6922451 (y : nat) (x : nat) : (term150 y x) = (term151 y x).
Proof. exact (@lem6922450 ((Nat.add x y) = (Nat.add x y)) (term103 y x)). Qed.
Lemma lem6922452 (y : nat) (z : nat) (x : nat) : (term152 y x z) = (term101 y z x).
Proof. exact (eq_refl (term152 y x z)). Qed.
Lemma lem6922453 (y : nat) (x : nat) : (term153 y x) = (term103 y x).
Proof. exact (fun_ext (fun z : nat => @lem6922452 y z x)). Qed.
Lemma lem6922454 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922455 (y : nat) (x : nat) : (term154 y x) = (term104 y x).
Proof. exact (MK_COMB (@lem6922454) (@lem6922453 y x)). Qed.
Lemma lem6922456 (x : nat) (y : nat) : (term140 x y) = (term140 x y).
Proof. exact (eq_refl (term140 x y)). Qed.
Lemma lem6922457 (y : nat) (x : nat) : (term150 y x) = (term142 y x).
Proof. exact (MK_COMB (@lem6922456 x y) (@lem6922455 y x)). Qed.
Lemma lem6922458 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6922459 (y : nat) (x : nat) : (term155 y x) = (term156 y x).
Proof. exact (MK_COMB (@lem6922458) (@lem6922457 y x)). Qed.
Lemma lem6922460 (y : nat) (z : nat) (x : nat) : (term152 y x z) = (term101 y z x).
Proof. exact (eq_refl (term152 y x z)). Qed.
Lemma lem6922461 (x : nat) (y : nat) : (term140 x y) = (term140 x y).
Proof. exact (eq_refl (term140 x y)). Qed.
Lemma lem6922462 (y : nat) (z : nat) (x : nat) : (term157 y x z) = (term158 y z x).
Proof. exact (MK_COMB (@lem6922461 x y) (@lem6922460 y z x)). Qed.
Lemma lem6922463 (y : nat) (x : nat) : (term159 y x) = (term160 y x).
Proof. exact (fun_ext (fun z : nat => @lem6922462 y z x)). Qed.
Lemma lem6922464 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922465 (y : nat) (x : nat) : (term151 y x) = (term161 y x).
Proof. exact (MK_COMB (@lem6922464) (@lem6922463 y x)). Qed.
Lemma lem6922466 (y : nat) (x : nat) : ((term150 y x) = (term151 y x)) = ((term142 y x) = (term161 y x)).
Proof. exact (MK_COMB (@lem6922459 y x) (@lem6922465 y x)). Qed.
Lemma lem6922467 (y : nat) (x : nat) : (term142 y x) = (term161 y x).
Proof. exact (EQ_MP (@lem6922466 y x) (@lem6922451 y x)). Qed.
Lemma lem6922468 (x : nat) : (term144 x) = (term162 x).
Proof. exact (fun_ext (fun y : nat => @lem6922467 y x)). Qed.
Lemma lem6922469 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922470 (x : nat) : (term145 x) = (term163 x).
Proof. exact (MK_COMB (@lem6922469) (@lem6922468 x)). Qed.
Lemma lem6922471 (x : nat) : (term124 x) = (term163 x).
Proof. exact (TRANS (@lem6922447 x) (@lem6922470 x)). Qed.
Lemma lem6922472 : term126 = term164.
Proof. exact (fun_ext (fun x : nat => @lem6922471 x)). Qed.
Lemma lem6922473 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922474 : term127 = term165.
Proof. exact (MK_COMB (@lem6922473) (@lem6922472)). Qed.
Lemma lem6922475 : term109 = term165.
Proof. exact (TRANS (@lem6922420) (@lem6922474)). Qed.
Lemma lem6922476 : term48 = term165.
Proof. exact (TRANS (@lem6922393) (@lem6922475)). Qed.
Lemma lem6922477 : term18 = term165.
Proof. exact (TRANS (@lem6922308) (@lem6922476)). Qed.
Lemma lem6922479 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6922480 (x : nat) (y : nat) : ((Nat.add x y) = (Nat.add x y)) = ((term166 x y) = (term166 x y)).
Proof. exact (@lem6922479 (Nat.add x y) (Nat.add x y)). Qed.
Lemma lem6922484 (m : nat) (n : nat) : (term166 m n) = (term167 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6922485 (x : nat) (y : nat) : (term166 x y) = (term167 x y).
Proof. exact (@lem6922484 x y). Qed.
Lemma lem6922486 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem6922487 (x : nat) (y : nat) : (term168 x y) = (term169 x y).
Proof. exact (MK_COMB (@lem6922486) (@lem6922485 x y)). Qed.
Lemma lem6922489 (m : nat) (n : nat) : (term166 m n) = (term167 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6922490 (x : nat) (y : nat) : (term166 x y) = (term167 x y).
Proof. exact (@lem6922489 x y). Qed.
Lemma lem6922491 (x : nat) (y : nat) : ((term166 x y) = (term166 x y)) = ((term167 x y) = (term167 x y)).
Proof. exact (MK_COMB (@lem6922487 x y) (@lem6922490 x y)). Qed.
Lemma lem6922492 (x : nat) (y : nat) : ((Nat.add x y) = (Nat.add x y)) = ((term167 x y) = (term167 x y)).
Proof. exact (TRANS (@lem6922480 x y) (@lem6922491 x y)). Qed.
Lemma lem6922493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922494 (x : nat) (y : nat) : (term140 x y) = (term170 x y).
Proof. exact (MK_COMB (@lem6922493) (@lem6922492 x y)). Qed.
Lemma lem6922496 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6922497 (x : nat) (y : nat) (z : nat) : ((term19 x y z) = (term19 x y z)) = ((term171 x y z) = (term171 x y z)).
Proof. exact (@lem6922496 (term19 x y z) (term19 x y z)). Qed.
Lemma lem6922501 (m : nat) (n : nat) : (term166 m n) = (term167 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6922502 (x : nat) (y : nat) (z : nat) : (term171 x y z) = (term172 x y z).
Proof. exact (@lem6922501 x (Nat.add y z)). Qed.
Lemma lem6922504 (m : nat) (n : nat) : (term166 m n) = (term167 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6922505 (y : nat) (z : nat) : (term166 y z) = (term167 y z).
Proof. exact (@lem6922504 y z). Qed.
Lemma lem6922506 (x : nat) : (term173 x) = (term173 x).
Proof. exact (eq_refl (term173 x)). Qed.
Lemma lem6922507 (x : nat) (y : nat) (z : nat) : (term172 x y z) = (term174 x y z).
Proof. exact (MK_COMB (@lem6922506 x) (@lem6922505 y z)). Qed.
Lemma lem6922508 (x : nat) (y : nat) (z : nat) : (term171 x y z) = (term174 x y z).
Proof. exact (TRANS (@lem6922502 x y z) (@lem6922507 x y z)). Qed.
Lemma lem6922509 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem6922510 (x : nat) (y : nat) (z : nat) : (term175 x y z) = (term176 x y z).
Proof. exact (MK_COMB (@lem6922509) (@lem6922508 x y z)). Qed.
Lemma lem6922512 (m : nat) (n : nat) : (term166 m n) = (term167 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6922513 (x : nat) (y : nat) (z : nat) : (term171 x y z) = (term172 x y z).
Proof. exact (@lem6922512 x (Nat.add y z)). Qed.
Lemma lem6922515 (m : nat) (n : nat) : (term166 m n) = (term167 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6922516 (y : nat) (z : nat) : (term166 y z) = (term167 y z).
Proof. exact (@lem6922515 y z). Qed.
Lemma lem6922517 (x : nat) : (term173 x) = (term173 x).
Proof. exact (eq_refl (term173 x)). Qed.
Lemma lem6922518 (x : nat) (y : nat) (z : nat) : (term172 x y z) = (term174 x y z).
Proof. exact (MK_COMB (@lem6922517 x) (@lem6922516 y z)). Qed.
Lemma lem6922519 (x : nat) (y : nat) (z : nat) : (term171 x y z) = (term174 x y z).
Proof. exact (TRANS (@lem6922513 x y z) (@lem6922518 x y z)). Qed.
Lemma lem6922520 (x : nat) (y : nat) (z : nat) : ((term171 x y z) = (term171 x y z)) = ((term174 x y z) = (term174 x y z)).
Proof. exact (MK_COMB (@lem6922510 x y z) (@lem6922519 x y z)). Qed.
Lemma lem6922521 (x : nat) (y : nat) (z : nat) : ((term19 x y z) = (term19 x y z)) = ((term174 x y z) = (term174 x y z)).
Proof. exact (TRANS (@lem6922497 x y z) (@lem6922520 x y z)). Qed.
Lemma lem6922522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922523 (x : nat) (y : nat) (z : nat) : (term99 x y z) = (term177 x y z).
Proof. exact (MK_COMB (@lem6922522) (@lem6922521 x y z)). Qed.
Lemma lem6922525 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6922526 (x : nat) : (x = x) = ((int_of_num x) = (int_of_num x)).
Proof. exact (@lem6922525 x x). Qed.
Lemma lem6922529 (y : nat) (z : nat) (x : nat) : (term101 y z x) = (term178 y z x).
Proof. exact (MK_COMB (@lem6922523 x y z) (@lem6922526 x)). Qed.
Lemma lem6922530 (y : nat) (z : nat) (x : nat) : (term158 y z x) = (term179 y z x).
Proof. exact (MK_COMB (@lem6922494 x y) (@lem6922529 y z x)). Qed.
Lemma lem6922531 (y : nat) (x : nat) : (term160 y x) = (term180 y x).
Proof. exact (fun_ext (fun z : nat => @lem6922530 y z x)). Qed.
Lemma lem6922532 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922533 (y : nat) (x : nat) : (term161 y x) = (term181 y x).
Proof. exact (MK_COMB (@lem6922532) (@lem6922531 y x)). Qed.
Lemma lem6922534 (x : nat) : (term162 x) = (term182 x).
Proof. exact (fun_ext (fun y : nat => @lem6922533 y x)). Qed.
Lemma lem6922535 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922536 (x : nat) : (term163 x) = (term183 x).
Proof. exact (MK_COMB (@lem6922535) (@lem6922534 x)). Qed.
Lemma lem6922537 : term164 = term184.
Proof. exact (fun_ext (fun x : nat => @lem6922536 x)). Qed.
Lemma lem6922538 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6922539 : term165 = term185.
Proof. exact (MK_COMB (@lem6922538) (@lem6922537)). Qed.
Lemma lem6922540 : term18 = term185.
Proof. exact (TRANS (@lem6922477) (@lem6922539)). Qed.
Lemma lem6922541 (x : nat) : term186 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem6922542 (x : nat) : (term186 x) = (term187 x).
Proof. exact (eq_refl (term186 x)). Qed.
Lemma lem6922543 (x : nat) : term187 x.
Proof. exact (EQ_MP (@lem6922542 x) (@lem6922541 x)). Qed.
Lemma lem6922544 (y : nat) : term186 y.
Proof. exact (@lem2307535 y). Qed.
Lemma lem6922545 (y : nat) : (term186 y) = (term187 y).
Proof. exact (eq_refl (term186 y)). Qed.
Lemma lem6922546 (y : nat) : term187 y.
Proof. exact (EQ_MP (@lem6922545 y) (@lem6922544 y)). Qed.
Lemma lem6922547 (z : nat) : term186 z.
Proof. exact (@lem2307535 z). Qed.
Lemma lem6922548 (z : nat) : (term186 z) = (term187 z).
Proof. exact (eq_refl (term186 z)). Qed.
Lemma lem6922549 (z : nat) : term187 z.
Proof. exact (EQ_MP (@lem6922548 z) (@lem6922547 z)). Qed.
Lemma lem6922550 (_92393 : int) (_92394 : int) (_92392 : int) : (term188 _92393 _92394 _92392) = (term189 _92393 _92394 _92392).
Proof. exact (@lem2318604 (term189 _92393 _92394 _92392)). Qed.
Lemma lem6922576 (_92393 : int) (_92394 : int) (_92392 : int) : (term190 _92393 _92394 _92392) = (term191 _92393 _92394 _92392).
Proof. exact (@lem17045 ((term192 _92392 _92393 _92394) = (term192 _92392 _92393 _92394)) (_92392 = _92392)). Qed.
Lemma lem6922578 (_92392 : int) (_92393 : int) : (term193 _92392 _92393) = (term193 _92392 _92393).
Proof. exact (eq_refl (term193 _92392 _92393)). Qed.
Lemma lem6922579 (_92393 : int) (_92394 : int) (_92392 : int) : (term194 _92393 _92394 _92392) = (term195 _92393 _92394 _92392).
Proof. exact (MK_COMB (@lem6922578 _92392 _92393) (@lem6922576 _92393 _92394 _92392)). Qed.
Lemma lem6922580 (_92393 : int) (_92394 : int) (_92392 : int) : (term196 _92393 _92394 _92392) = (term194 _92393 _92394 _92392).
Proof. exact (@lem17045 ((int_add _92392 _92393) = (int_add _92392 _92393)) (term197 _92393 _92394 _92392)). Qed.
Lemma lem6922581 (_92393 : int) (_92394 : int) (_92392 : int) : (term196 _92393 _92394 _92392) = (term195 _92393 _92394 _92392).
Proof. exact (TRANS (@lem6922580 _92393 _92394 _92392) (@lem6922579 _92393 _92394 _92392)). Qed.
Lemma lem6922583 (_92394 : int) : (term198 _92394) = (term198 _92394).
Proof. exact (eq_refl (term198 _92394)). Qed.
Lemma lem6922584 (_92393 : int) (_92394 : int) (_92392 : int) : (term199 _92393 _92394 _92392) = (term200 _92393 _92394 _92392).
Proof. exact (MK_COMB (@lem6922583 _92394) (@lem6922581 _92393 _92394 _92392)). Qed.
Lemma lem6922585 (_92393 : int) (_92394 : int) (_92392 : int) : (term201 _92393 _92394 _92392) = (term199 _92393 _92394 _92392).
Proof. exact (@lem17362 (term202 _92394) (term203 _92393 _92394 _92392)). Qed.
Lemma lem6922586 (_92393 : int) (_92394 : int) (_92392 : int) : (term201 _92393 _92394 _92392) = (term200 _92393 _92394 _92392).
Proof. exact (TRANS (@lem6922585 _92393 _92394 _92392) (@lem6922584 _92393 _92394 _92392)). Qed.
Lemma lem6922588 (_92393 : int) : (term198 _92393) = (term198 _92393).
Proof. exact (eq_refl (term198 _92393)). Qed.
Lemma lem6922589 (_92393 : int) (_92394 : int) (_92392 : int) : (term204 _92393 _92394 _92392) = (term205 _92393 _92394 _92392).
Proof. exact (MK_COMB (@lem6922588 _92393) (@lem6922586 _92393 _92394 _92392)). Qed.
Lemma lem6922590 (_92393 : int) (_92394 : int) (_92392 : int) : (term206 _92393 _92394 _92392) = (term204 _92393 _92394 _92392).
Proof. exact (@lem17362 (term202 _92393) (term207 _92393 _92394 _92392)). Qed.
Lemma lem6922591 (_92393 : int) (_92394 : int) (_92392 : int) : (term206 _92393 _92394 _92392) = (term205 _92393 _92394 _92392).
Proof. exact (TRANS (@lem6922590 _92393 _92394 _92392) (@lem6922589 _92393 _92394 _92392)). Qed.
Lemma lem6922593 (_92392 : int) : (term198 _92392) = (term198 _92392).
Proof. exact (eq_refl (term198 _92392)). Qed.
Lemma lem6922594 (_92393 : int) (_92394 : int) (_92392 : int) : (term208 _92393 _92394 _92392) = (term209 _92393 _92394 _92392).
Proof. exact (MK_COMB (@lem6922593 _92392) (@lem6922591 _92393 _92394 _92392)). Qed.
Lemma lem6922595 (_92393 : int) (_92394 : int) (_92392 : int) : (term210 _92393 _92394 _92392) = (term208 _92393 _92394 _92392).
Proof. exact (@lem17362 (term202 _92392) (term211 _92393 _92394 _92392)). Qed.
Lemma lem6922625 (_92393 : int) (_92394 : int) (_92392 : int) : (term210 _92393 _92394 _92392) = (term209 _92393 _92394 _92392).
Proof. exact (TRANS (@lem6922595 _92393 _92394 _92392) (@lem6922594 _92393 _92394 _92392)). Qed.
Lemma lem6922628 (x : int) (y : int) : (int_le x y) = (term212 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6922629 (_92392 : int) : (term202 _92392) = (term213 _92392).
Proof. exact (@lem6922628 term214 _92392). Qed.
Lemma lem6922631 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6922632 : term216 = term217.
Proof. exact (@lem6922631 (NUMERAL 0)). Qed.
Lemma lem6922633 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6922634 : term218 = term219.
Proof. exact (MK_COMB (@lem6922633) (@lem6922632)). Qed.
Lemma lem6922635 (_92392 : int) : (real_of_int _92392) = (real_of_int _92392).
Proof. exact (eq_refl (real_of_int _92392)). Qed.
Lemma lem6922636 (_92392 : int) : (term213 _92392) = (term220 _92392).
Proof. exact (MK_COMB (@lem6922634) (@lem6922635 _92392)). Qed.
Lemma lem6922638 (_92392 : int) : (term202 _92392) = (term220 _92392).
Proof. exact (TRANS (@lem6922629 _92392) (@lem6922636 _92392)). Qed.
Lemma lem6922641 (x : int) (y : int) : (int_le x y) = (term212 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6922642 (_92393 : int) : (term202 _92393) = (term213 _92393).
Proof. exact (@lem6922641 term214 _92393). Qed.
Lemma lem6922644 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6922645 : term216 = term217.
Proof. exact (@lem6922644 (NUMERAL 0)). Qed.
Lemma lem6922646 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6922647 : term218 = term219.
Proof. exact (MK_COMB (@lem6922646) (@lem6922645)). Qed.
Lemma lem6922648 (_92393 : int) : (real_of_int _92393) = (real_of_int _92393).
Proof. exact (eq_refl (real_of_int _92393)). Qed.
Lemma lem6922649 (_92393 : int) : (term213 _92393) = (term220 _92393).
Proof. exact (MK_COMB (@lem6922647) (@lem6922648 _92393)). Qed.
Lemma lem6922651 (_92393 : int) : (term202 _92393) = (term220 _92393).
Proof. exact (TRANS (@lem6922642 _92393) (@lem6922649 _92393)). Qed.
Lemma lem6922654 (x : int) (y : int) : (int_le x y) = (term212 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6922655 (_92394 : int) : (term202 _92394) = (term213 _92394).
Proof. exact (@lem6922654 term214 _92394). Qed.
Lemma lem6922657 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6922658 : term216 = term217.
Proof. exact (@lem6922657 (NUMERAL 0)). Qed.
Lemma lem6922659 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6922660 : term218 = term219.
Proof. exact (MK_COMB (@lem6922659) (@lem6922658)). Qed.
Lemma lem6922661 (_92394 : int) : (real_of_int _92394) = (real_of_int _92394).
Proof. exact (eq_refl (real_of_int _92394)). Qed.
Lemma lem6922662 (_92394 : int) : (term213 _92394) = (term220 _92394).
Proof. exact (MK_COMB (@lem6922660) (@lem6922661 _92394)). Qed.
Lemma lem6922664 (_92394 : int) : (term202 _92394) = (term220 _92394).
Proof. exact (TRANS (@lem6922655 _92394) (@lem6922662 _92394)). Qed.
Lemma lem6922666 (y : int) (x : int) : (term221 x y) = (term222 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem6922667 (_92392 : int) (_92393 : int) : (term223 _92392 _92393) = (term224 _92392 _92393).
Proof. exact (@lem6922666 (int_add _92392 _92393) (int_add _92392 _92393)). Qed.
Lemma lem6922669 (x : int) (y : int) : (int_le x y) = (term212 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6922670 (_92392 : int) (_92393 : int) : (term225 _92392 _92393) = (term226 _92392 _92393).
Proof. exact (@lem6922669 (term227 _92392 _92393) (int_add _92392 _92393)). Qed.
Lemma lem6922672 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922673 (_92392 : int) (_92393 : int) : (term230 _92392 _92393) = (term231 _92392 _92393).
Proof. exact (@lem6922672 (int_add _92392 _92393) term232). Qed.
Lemma lem6922675 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922676 (_92392 : int) (_92393 : int) : (term228 _92392 _92393) = (term229 _92392 _92393).
Proof. exact (@lem6922675 _92392 _92393). Qed.
Lemma lem6922677 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6922678 (_92392 : int) (_92393 : int) : (term233 _92392 _92393) = (term234 _92392 _92393).
Proof. exact (MK_COMB (@lem6922677) (@lem6922676 _92392 _92393)). Qed.
Lemma lem6922680 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6922681 : term235 = term236.
Proof. exact (@lem6922680 term237). Qed.
Lemma lem6922682 (_92392 : int) (_92393 : int) : (term231 _92392 _92393) = (term238 _92392 _92393).
Proof. exact (MK_COMB (@lem6922678 _92392 _92393) (@lem6922681)). Qed.
Lemma lem6922683 (_92392 : int) (_92393 : int) : (term230 _92392 _92393) = (term238 _92392 _92393).
Proof. exact (TRANS (@lem6922673 _92392 _92393) (@lem6922682 _92392 _92393)). Qed.
Lemma lem6922684 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6922685 (_92392 : int) (_92393 : int) : (term239 _92392 _92393) = (term240 _92392 _92393).
Proof. exact (MK_COMB (@lem6922684) (@lem6922683 _92392 _92393)). Qed.
Lemma lem6922687 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922688 (_92392 : int) (_92393 : int) : (term228 _92392 _92393) = (term229 _92392 _92393).
Proof. exact (@lem6922687 _92392 _92393). Qed.
Lemma lem6922689 (_92392 : int) (_92393 : int) : (term226 _92392 _92393) = (term241 _92392 _92393).
Proof. exact (MK_COMB (@lem6922685 _92392 _92393) (@lem6922688 _92392 _92393)). Qed.
Lemma lem6922690 (_92392 : int) (_92393 : int) : (term225 _92392 _92393) = (term241 _92392 _92393).
Proof. exact (TRANS (@lem6922670 _92392 _92393) (@lem6922689 _92392 _92393)). Qed.
Lemma lem6922691 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6922692 (_92392 : int) (_92393 : int) : (term242 _92392 _92393) = (term243 _92392 _92393).
Proof. exact (MK_COMB (@lem6922691) (@lem6922690 _92392 _92393)). Qed.
Lemma lem6922694 (x : int) (y : int) : (int_le x y) = (term212 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6922695 (_92392 : int) (_92393 : int) : (term225 _92392 _92393) = (term226 _92392 _92393).
Proof. exact (@lem6922694 (term227 _92392 _92393) (int_add _92392 _92393)). Qed.
Lemma lem6922697 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922698 (_92392 : int) (_92393 : int) : (term230 _92392 _92393) = (term231 _92392 _92393).
Proof. exact (@lem6922697 (int_add _92392 _92393) term232). Qed.
Lemma lem6922700 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922701 (_92392 : int) (_92393 : int) : (term228 _92392 _92393) = (term229 _92392 _92393).
Proof. exact (@lem6922700 _92392 _92393). Qed.
Lemma lem6922702 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6922703 (_92392 : int) (_92393 : int) : (term233 _92392 _92393) = (term234 _92392 _92393).
Proof. exact (MK_COMB (@lem6922702) (@lem6922701 _92392 _92393)). Qed.
Lemma lem6922705 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6922706 : term235 = term236.
Proof. exact (@lem6922705 term237). Qed.
Lemma lem6922707 (_92392 : int) (_92393 : int) : (term231 _92392 _92393) = (term238 _92392 _92393).
Proof. exact (MK_COMB (@lem6922703 _92392 _92393) (@lem6922706)). Qed.
Lemma lem6922708 (_92392 : int) (_92393 : int) : (term230 _92392 _92393) = (term238 _92392 _92393).
Proof. exact (TRANS (@lem6922698 _92392 _92393) (@lem6922707 _92392 _92393)). Qed.
Lemma lem6922709 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6922710 (_92392 : int) (_92393 : int) : (term239 _92392 _92393) = (term240 _92392 _92393).
Proof. exact (MK_COMB (@lem6922709) (@lem6922708 _92392 _92393)). Qed.
Lemma lem6922712 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922713 (_92392 : int) (_92393 : int) : (term228 _92392 _92393) = (term229 _92392 _92393).
Proof. exact (@lem6922712 _92392 _92393). Qed.
Lemma lem6922714 (_92392 : int) (_92393 : int) : (term226 _92392 _92393) = (term241 _92392 _92393).
Proof. exact (MK_COMB (@lem6922710 _92392 _92393) (@lem6922713 _92392 _92393)). Qed.
Lemma lem6922715 (_92392 : int) (_92393 : int) : (term225 _92392 _92393) = (term241 _92392 _92393).
Proof. exact (TRANS (@lem6922695 _92392 _92393) (@lem6922714 _92392 _92393)). Qed.
Lemma lem6922716 (_92392 : int) (_92393 : int) : (term224 _92392 _92393) = (term244 _92392 _92393).
Proof. exact (MK_COMB (@lem6922692 _92392 _92393) (@lem6922715 _92392 _92393)). Qed.
Lemma lem6922717 (_92392 : int) (_92393 : int) : (term223 _92392 _92393) = (term244 _92392 _92393).
Proof. exact (TRANS (@lem6922667 _92392 _92393) (@lem6922716 _92392 _92393)). Qed.
Lemma lem6922719 (y : int) (x : int) : (term221 x y) = (term222 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem6922720 (_92392 : int) (_92393 : int) (_92394 : int) : (term245 _92392 _92393 _92394) = (term246 _92392 _92393 _92394).
Proof. exact (@lem6922719 (term192 _92392 _92393 _92394) (term192 _92392 _92393 _92394)). Qed.
Lemma lem6922722 (x : int) (y : int) : (int_le x y) = (term212 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6922723 (_92392 : int) (_92393 : int) (_92394 : int) : (term247 _92392 _92393 _92394) = (term248 _92392 _92393 _92394).
Proof. exact (@lem6922722 (term249 _92392 _92393 _92394) (term192 _92392 _92393 _92394)). Qed.
Lemma lem6922725 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922726 (_92392 : int) (_92393 : int) (_92394 : int) : (term250 _92392 _92393 _92394) = (term251 _92392 _92393 _92394).
Proof. exact (@lem6922725 (term192 _92392 _92393 _92394) term232). Qed.
Lemma lem6922728 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922729 (_92392 : int) (_92393 : int) (_92394 : int) : (term252 _92392 _92393 _92394) = (term253 _92392 _92393 _92394).
Proof. exact (@lem6922728 _92392 (int_add _92393 _92394)). Qed.
Lemma lem6922731 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922732 (_92393 : int) (_92394 : int) : (term228 _92393 _92394) = (term229 _92393 _92394).
Proof. exact (@lem6922731 _92393 _92394). Qed.
Lemma lem6922733 (_92392 : int) : (term254 _92392) = (term254 _92392).
Proof. exact (eq_refl (term254 _92392)). Qed.
Lemma lem6922734 (_92392 : int) (_92393 : int) (_92394 : int) : (term253 _92392 _92393 _92394) = (term255 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922733 _92392) (@lem6922732 _92393 _92394)). Qed.
Lemma lem6922735 (_92392 : int) (_92393 : int) (_92394 : int) : (term252 _92392 _92393 _92394) = (term255 _92392 _92393 _92394).
Proof. exact (TRANS (@lem6922729 _92392 _92393 _92394) (@lem6922734 _92392 _92393 _92394)). Qed.
Lemma lem6922736 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6922737 (_92392 : int) (_92393 : int) (_92394 : int) : (term256 _92392 _92393 _92394) = (term257 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922736) (@lem6922735 _92392 _92393 _92394)). Qed.
Lemma lem6922739 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6922740 : term235 = term236.
Proof. exact (@lem6922739 term237). Qed.
Lemma lem6922741 (_92392 : int) (_92393 : int) (_92394 : int) : (term251 _92392 _92393 _92394) = (term258 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922737 _92392 _92393 _92394) (@lem6922740)). Qed.
Lemma lem6922742 (_92392 : int) (_92393 : int) (_92394 : int) : (term250 _92392 _92393 _92394) = (term258 _92392 _92393 _92394).
Proof. exact (TRANS (@lem6922726 _92392 _92393 _92394) (@lem6922741 _92392 _92393 _92394)). Qed.
Lemma lem6922743 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6922744 (_92392 : int) (_92393 : int) (_92394 : int) : (term259 _92392 _92393 _92394) = (term260 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922743) (@lem6922742 _92392 _92393 _92394)). Qed.
Lemma lem6922746 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922747 (_92392 : int) (_92393 : int) (_92394 : int) : (term252 _92392 _92393 _92394) = (term253 _92392 _92393 _92394).
Proof. exact (@lem6922746 _92392 (int_add _92393 _92394)). Qed.
Lemma lem6922749 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922750 (_92393 : int) (_92394 : int) : (term228 _92393 _92394) = (term229 _92393 _92394).
Proof. exact (@lem6922749 _92393 _92394). Qed.
Lemma lem6922751 (_92392 : int) : (term254 _92392) = (term254 _92392).
Proof. exact (eq_refl (term254 _92392)). Qed.
Lemma lem6922752 (_92392 : int) (_92393 : int) (_92394 : int) : (term253 _92392 _92393 _92394) = (term255 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922751 _92392) (@lem6922750 _92393 _92394)). Qed.
Lemma lem6922753 (_92392 : int) (_92393 : int) (_92394 : int) : (term252 _92392 _92393 _92394) = (term255 _92392 _92393 _92394).
Proof. exact (TRANS (@lem6922747 _92392 _92393 _92394) (@lem6922752 _92392 _92393 _92394)). Qed.
Lemma lem6922754 (_92392 : int) (_92393 : int) (_92394 : int) : (term248 _92392 _92393 _92394) = (term261 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922744 _92392 _92393 _92394) (@lem6922753 _92392 _92393 _92394)). Qed.
Lemma lem6922755 (_92392 : int) (_92393 : int) (_92394 : int) : (term247 _92392 _92393 _92394) = (term261 _92392 _92393 _92394).
Proof. exact (TRANS (@lem6922723 _92392 _92393 _92394) (@lem6922754 _92392 _92393 _92394)). Qed.
Lemma lem6922756 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6922757 (_92392 : int) (_92393 : int) (_92394 : int) : (term262 _92392 _92393 _92394) = (term263 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922756) (@lem6922755 _92392 _92393 _92394)). Qed.
Lemma lem6922759 (x : int) (y : int) : (int_le x y) = (term212 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6922760 (_92392 : int) (_92393 : int) (_92394 : int) : (term247 _92392 _92393 _92394) = (term248 _92392 _92393 _92394).
Proof. exact (@lem6922759 (term249 _92392 _92393 _92394) (term192 _92392 _92393 _92394)). Qed.
Lemma lem6922762 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922763 (_92392 : int) (_92393 : int) (_92394 : int) : (term250 _92392 _92393 _92394) = (term251 _92392 _92393 _92394).
Proof. exact (@lem6922762 (term192 _92392 _92393 _92394) term232). Qed.
Lemma lem6922765 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922766 (_92392 : int) (_92393 : int) (_92394 : int) : (term252 _92392 _92393 _92394) = (term253 _92392 _92393 _92394).
Proof. exact (@lem6922765 _92392 (int_add _92393 _92394)). Qed.
Lemma lem6922768 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922769 (_92393 : int) (_92394 : int) : (term228 _92393 _92394) = (term229 _92393 _92394).
Proof. exact (@lem6922768 _92393 _92394). Qed.
Lemma lem6922770 (_92392 : int) : (term254 _92392) = (term254 _92392).
Proof. exact (eq_refl (term254 _92392)). Qed.
Lemma lem6922771 (_92392 : int) (_92393 : int) (_92394 : int) : (term253 _92392 _92393 _92394) = (term255 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922770 _92392) (@lem6922769 _92393 _92394)). Qed.
Lemma lem6922772 (_92392 : int) (_92393 : int) (_92394 : int) : (term252 _92392 _92393 _92394) = (term255 _92392 _92393 _92394).
Proof. exact (TRANS (@lem6922766 _92392 _92393 _92394) (@lem6922771 _92392 _92393 _92394)). Qed.
Lemma lem6922773 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6922774 (_92392 : int) (_92393 : int) (_92394 : int) : (term256 _92392 _92393 _92394) = (term257 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922773) (@lem6922772 _92392 _92393 _92394)). Qed.
Lemma lem6922776 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6922777 : term235 = term236.
Proof. exact (@lem6922776 term237). Qed.
Lemma lem6922778 (_92392 : int) (_92393 : int) (_92394 : int) : (term251 _92392 _92393 _92394) = (term258 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922774 _92392 _92393 _92394) (@lem6922777)). Qed.
Lemma lem6922779 (_92392 : int) (_92393 : int) (_92394 : int) : (term250 _92392 _92393 _92394) = (term258 _92392 _92393 _92394).
Proof. exact (TRANS (@lem6922763 _92392 _92393 _92394) (@lem6922778 _92392 _92393 _92394)). Qed.
Lemma lem6922780 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6922781 (_92392 : int) (_92393 : int) (_92394 : int) : (term259 _92392 _92393 _92394) = (term260 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922780) (@lem6922779 _92392 _92393 _92394)). Qed.
Lemma lem6922783 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922784 (_92392 : int) (_92393 : int) (_92394 : int) : (term252 _92392 _92393 _92394) = (term253 _92392 _92393 _92394).
Proof. exact (@lem6922783 _92392 (int_add _92393 _92394)). Qed.
Lemma lem6922786 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922787 (_92393 : int) (_92394 : int) : (term228 _92393 _92394) = (term229 _92393 _92394).
Proof. exact (@lem6922786 _92393 _92394). Qed.
Lemma lem6922788 (_92392 : int) : (term254 _92392) = (term254 _92392).
Proof. exact (eq_refl (term254 _92392)). Qed.
Lemma lem6922789 (_92392 : int) (_92393 : int) (_92394 : int) : (term253 _92392 _92393 _92394) = (term255 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922788 _92392) (@lem6922787 _92393 _92394)). Qed.
Lemma lem6922790 (_92392 : int) (_92393 : int) (_92394 : int) : (term252 _92392 _92393 _92394) = (term255 _92392 _92393 _92394).
Proof. exact (TRANS (@lem6922784 _92392 _92393 _92394) (@lem6922789 _92392 _92393 _92394)). Qed.
Lemma lem6922791 (_92392 : int) (_92393 : int) (_92394 : int) : (term248 _92392 _92393 _92394) = (term261 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922781 _92392 _92393 _92394) (@lem6922790 _92392 _92393 _92394)). Qed.
Lemma lem6922792 (_92392 : int) (_92393 : int) (_92394 : int) : (term247 _92392 _92393 _92394) = (term261 _92392 _92393 _92394).
Proof. exact (TRANS (@lem6922760 _92392 _92393 _92394) (@lem6922791 _92392 _92393 _92394)). Qed.
Lemma lem6922793 (_92392 : int) (_92393 : int) (_92394 : int) : (term246 _92392 _92393 _92394) = (term264 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922757 _92392 _92393 _92394) (@lem6922792 _92392 _92393 _92394)). Qed.
Lemma lem6922794 (_92392 : int) (_92393 : int) (_92394 : int) : (term245 _92392 _92393 _92394) = (term264 _92392 _92393 _92394).
Proof. exact (TRANS (@lem6922720 _92392 _92393 _92394) (@lem6922793 _92392 _92393 _92394)). Qed.
Lemma lem6922796 (y : int) (x : int) : (term221 x y) = (term222 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem6922797 (_92392 : int) : (term265 _92392) = (term266 _92392).
Proof. exact (@lem6922796 _92392 _92392). Qed.
Lemma lem6922799 (x : int) (y : int) : (int_le x y) = (term212 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6922800 (_92392 : int) : (term267 _92392) = (term268 _92392).
Proof. exact (@lem6922799 (term269 _92392) _92392). Qed.
Lemma lem6922802 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922803 (_92392 : int) : (term270 _92392) = (term271 _92392).
Proof. exact (@lem6922802 _92392 term232). Qed.
Lemma lem6922805 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6922806 : term235 = term236.
Proof. exact (@lem6922805 term237). Qed.
Lemma lem6922807 (_92392 : int) : (term254 _92392) = (term254 _92392).
Proof. exact (eq_refl (term254 _92392)). Qed.
Lemma lem6922808 (_92392 : int) : (term271 _92392) = (term272 _92392).
Proof. exact (MK_COMB (@lem6922807 _92392) (@lem6922806)). Qed.
Lemma lem6922809 (_92392 : int) : (term270 _92392) = (term272 _92392).
Proof. exact (TRANS (@lem6922803 _92392) (@lem6922808 _92392)). Qed.
Lemma lem6922810 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6922811 (_92392 : int) : (term273 _92392) = (term274 _92392).
Proof. exact (MK_COMB (@lem6922810) (@lem6922809 _92392)). Qed.
Lemma lem6922812 (_92392 : int) : (real_of_int _92392) = (real_of_int _92392).
Proof. exact (eq_refl (real_of_int _92392)). Qed.
Lemma lem6922813 (_92392 : int) : (term268 _92392) = (term275 _92392).
Proof. exact (MK_COMB (@lem6922811 _92392) (@lem6922812 _92392)). Qed.
Lemma lem6922814 (_92392 : int) : (term267 _92392) = (term275 _92392).
Proof. exact (TRANS (@lem6922800 _92392) (@lem6922813 _92392)). Qed.
Lemma lem6922815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6922816 (_92392 : int) : (term276 _92392) = (term277 _92392).
Proof. exact (MK_COMB (@lem6922815) (@lem6922814 _92392)). Qed.
Lemma lem6922818 (x : int) (y : int) : (int_le x y) = (term212 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6922819 (_92392 : int) : (term267 _92392) = (term268 _92392).
Proof. exact (@lem6922818 (term269 _92392) _92392). Qed.
Lemma lem6922821 (x : int) (y : int) : (term228 x y) = (term229 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6922822 (_92392 : int) : (term270 _92392) = (term271 _92392).
Proof. exact (@lem6922821 _92392 term232). Qed.
Lemma lem6922824 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6922825 : term235 = term236.
Proof. exact (@lem6922824 term237). Qed.
Lemma lem6922826 (_92392 : int) : (term254 _92392) = (term254 _92392).
Proof. exact (eq_refl (term254 _92392)). Qed.
Lemma lem6922827 (_92392 : int) : (term271 _92392) = (term272 _92392).
Proof. exact (MK_COMB (@lem6922826 _92392) (@lem6922825)). Qed.
Lemma lem6922828 (_92392 : int) : (term270 _92392) = (term272 _92392).
Proof. exact (TRANS (@lem6922822 _92392) (@lem6922827 _92392)). Qed.
Lemma lem6922829 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6922830 (_92392 : int) : (term273 _92392) = (term274 _92392).
Proof. exact (MK_COMB (@lem6922829) (@lem6922828 _92392)). Qed.
Lemma lem6922831 (_92392 : int) : (real_of_int _92392) = (real_of_int _92392).
Proof. exact (eq_refl (real_of_int _92392)). Qed.
Lemma lem6922832 (_92392 : int) : (term268 _92392) = (term275 _92392).
Proof. exact (MK_COMB (@lem6922830 _92392) (@lem6922831 _92392)). Qed.
Lemma lem6922833 (_92392 : int) : (term267 _92392) = (term275 _92392).
Proof. exact (TRANS (@lem6922819 _92392) (@lem6922832 _92392)). Qed.
Lemma lem6922834 (_92392 : int) : (term266 _92392) = (term278 _92392).
Proof. exact (MK_COMB (@lem6922816 _92392) (@lem6922833 _92392)). Qed.
Lemma lem6922835 (_92392 : int) : (term265 _92392) = (term278 _92392).
Proof. exact (TRANS (@lem6922797 _92392) (@lem6922834 _92392)). Qed.
Lemma lem6922836 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6922837 (_92392 : int) (_92393 : int) (_92394 : int) : (term279 _92392 _92393 _92394) = (term280 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922836) (@lem6922794 _92392 _92393 _92394)). Qed.
Lemma lem6922838 (_92393 : int) (_92394 : int) (_92392 : int) : (term191 _92393 _92394 _92392) = (term281 _92393 _92394 _92392).
Proof. exact (MK_COMB (@lem6922837 _92392 _92393 _92394) (@lem6922835 _92392)). Qed.
Lemma lem6922839 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6922840 (_92392 : int) (_92393 : int) : (term193 _92392 _92393) = (term282 _92392 _92393).
Proof. exact (MK_COMB (@lem6922839) (@lem6922717 _92392 _92393)). Qed.
Lemma lem6922841 (_92393 : int) (_92394 : int) (_92392 : int) : (term195 _92393 _92394 _92392) = (term283 _92393 _92394 _92392).
Proof. exact (MK_COMB (@lem6922840 _92392 _92393) (@lem6922838 _92393 _92394 _92392)). Qed.
Lemma lem6922842 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922843 (_92394 : int) : (term198 _92394) = (term284 _92394).
Proof. exact (MK_COMB (@lem6922842) (@lem6922664 _92394)). Qed.
Lemma lem6922844 (_92393 : int) (_92394 : int) (_92392 : int) : (term200 _92393 _92394 _92392) = (term285 _92393 _92394 _92392).
Proof. exact (MK_COMB (@lem6922843 _92394) (@lem6922841 _92393 _92394 _92392)). Qed.
Lemma lem6922845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922846 (_92393 : int) : (term198 _92393) = (term284 _92393).
Proof. exact (MK_COMB (@lem6922845) (@lem6922651 _92393)). Qed.
Lemma lem6922847 (_92393 : int) (_92394 : int) (_92392 : int) : (term205 _92393 _92394 _92392) = (term286 _92393 _92394 _92392).
Proof. exact (MK_COMB (@lem6922846 _92393) (@lem6922844 _92393 _92394 _92392)). Qed.
Lemma lem6922848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6922849 (_92392 : int) : (term198 _92392) = (term284 _92392).
Proof. exact (MK_COMB (@lem6922848) (@lem6922638 _92392)). Qed.
Lemma lem6922850 (_92393 : int) (_92394 : int) (_92392 : int) : (term209 _92393 _92394 _92392) = (term287 _92393 _92394 _92392).
Proof. exact (MK_COMB (@lem6922849 _92392) (@lem6922847 _92393 _92394 _92392)). Qed.
Lemma lem6922851 (_92393 : int) (_92394 : int) (_92392 : int) : (term210 _92393 _92394 _92392) = (term287 _92393 _92394 _92392).
Proof. exact (TRANS (@lem6922625 _92393 _92394 _92392) (@lem6922850 _92393 _92394 _92392)). Qed.
Lemma lem6922855 (t : Prop) : (term288 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6922856 (_92393 : int) (_92394 : int) (_92392 : int) : (term289 _92393 _92394 _92392) = (term287 _92393 _92394 _92392).
Proof. exact (@lem6922855 (term287 _92393 _92394 _92392)). Qed.
Lemma lem6922866 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem16485 t)). Qed.
Lemma lem6922867 (_92392 : int) (_92393 : int) : (term244 _92392 _92393) = (term241 _92392 _92393).
Proof. exact (@lem6922866 (term241 _92392 _92393)). Qed.
Lemma lem6922868 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6922869 (_92392 : int) (_92393 : int) : (term282 _92392 _92393) = (term243 _92392 _92393).
Proof. exact (MK_COMB (@lem6922868) (@lem6922867 _92392 _92393)). Qed.
Lemma lem6922873 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem16485 t)). Qed.
Lemma lem6922874 (_92392 : int) (_92393 : int) (_92394 : int) : (term264 _92392 _92393 _92394) = (term261 _92392 _92393 _92394).
Proof. exact (@lem6922873 (term261 _92392 _92393 _92394)). Qed.
Lemma lem6922875 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6922876 (_92392 : int) (_92393 : int) (_92394 : int) : (term280 _92392 _92393 _92394) = (term263 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6922875) (@lem6922874 _92392 _92393 _92394)). Qed.
Lemma lem6922878 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem16485 t)). Qed.
Lemma lem6922879 (_92392 : int) : (term278 _92392) = (term275 _92392).
Proof. exact (@lem6922878 (term275 _92392)). Qed.
Lemma lem6922880 (_92393 : int) (_92394 : int) (_92392 : int) : (term281 _92393 _92394 _92392) = (term290 _92393 _92394 _92392).
Proof. exact (MK_COMB (@lem6922876 _92392 _92393 _92394) (@lem6922879 _92392)). Qed.
Lemma lem6922883 (_92393 : int) (_92394 : int) (_92392 : int) : (term283 _92393 _92394 _92392) = (term291 _92393 _92394 _92392).
Proof. exact (MK_COMB (@lem6922869 _92392 _92393) (@lem6922880 _92393 _92394 _92392)). Qed.
Lemma lem6922886 (_92394 : int) : (term284 _92394) = (term284 _92394).
Proof. exact (eq_refl (term284 _92394)). Qed.
Lemma lem6922887 (_92393 : int) (_92394 : int) (_92392 : int) : (term285 _92393 _92394 _92392) = (term292 _92393 _92394 _92392).
Proof. exact (MK_COMB (@lem6922886 _92394) (@lem6922883 _92393 _92394 _92392)). Qed.
Lemma lem6922890 (_92393 : int) : (term284 _92393) = (term284 _92393).
Proof. exact (eq_refl (term284 _92393)). Qed.
Lemma lem6922891 (_92393 : int) (_92394 : int) (_92392 : int) : (term286 _92393 _92394 _92392) = (term293 _92393 _92394 _92392).
Proof. exact (MK_COMB (@lem6922890 _92393) (@lem6922887 _92393 _92394 _92392)). Qed.
Lemma lem6922894 (_92392 : int) : (term284 _92392) = (term284 _92392).
Proof. exact (eq_refl (term284 _92392)). Qed.
Lemma lem6922895 (_92393 : int) (_92394 : int) (_92392 : int) : (term287 _92393 _92394 _92392) = (term294 _92393 _92394 _92392).
Proof. exact (MK_COMB (@lem6922894 _92392) (@lem6922891 _92393 _92394 _92392)). Qed.
Lemma lem6922943 (_92393 : int) (_92394 : int) (_92392 : int) : (term289 _92393 _92394 _92392) = (term294 _92393 _92394 _92392).
Proof. exact (TRANS (@lem6922856 _92393 _92394 _92392) (@lem6922895 _92393 _92394 _92392)). Qed.
Lemma lem6922944 (_92392 : int) : (term220 _92392) = (term295 _92392).
Proof. exact (@lem1988287 (real_of_int _92392) term217). Qed.
Lemma lem6922950 (_92392 : int) : (term296 _92392) = (term297 _92392).
Proof. exact (@lem1982792 (real_of_int _92392) term217). Qed.
Lemma lem6922952 (x : nat) : (real_of_num x) = (term298 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6922953 : term217 = term299.
Proof. exact (@lem6922952 (NUMERAL 0)). Qed.
Lemma lem6922955 (x : nat) : (term300 x) = (term301 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6922956 : term302 = term303.
Proof. exact (@lem6922955 term237). Qed.
Lemma lem6922957 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6922958 : term304 = term305.
Proof. exact (MK_COMB (@lem6922957) (@lem6922956)). Qed.
Lemma lem6922959 : term306 = term307.
Proof. exact (MK_COMB (@lem6922958) (@lem6922953)). Qed.
Lemma lem6922960 : term307 = term308.
Proof. exact (@lem1981613 term302 term217 term236 term236). Qed.
Lemma lem6922962 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6922963 : term311 = term312.
Proof. exact (@lem6922962 term237 term237). Qed.
Lemma lem6922964 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6922965 : term314 = term237.
Proof. exact (EQ_MP (@lem6922964) (@lem940073)). Qed.
Lemma lem6922966 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6922967 : term312 = term236.
Proof. exact (MK_COMB (@lem6922966) (@lem6922965)). Qed.
Lemma lem6922968 : term311 = term236.
Proof. exact (TRANS (@lem6922963) (@lem6922967)). Qed.
Lemma lem6922970 (x : nat) : (term315 x) = term217.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6922971 : term306 = term217.
Proof. exact (@lem6922970 term237). Qed.
Lemma lem6922972 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6922973 : term316 = term317.
Proof. exact (MK_COMB (@lem6922972) (@lem6922971)). Qed.
Lemma lem6922974 : term308 = term299.
Proof. exact (MK_COMB (@lem6922973) (@lem6922968)). Qed.
Lemma lem6922975 : term307 = term299.
Proof. exact (TRANS (@lem6922960) (@lem6922974)). Qed.
Lemma lem6922976 : term306 = term299.
Proof. exact (TRANS (@lem6922959) (@lem6922975)). Qed.
Lemma lem6922978 (x : real) : (term318 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6922979 : term299 = term217.
Proof. exact (@lem6922978 term217). Qed.
Lemma lem6922980 : term306 = term217.
Proof. exact (TRANS (@lem6922976) (@lem6922979)). Qed.
Lemma lem6922981 (_92392 : int) : (term254 _92392) = (term254 _92392).
Proof. exact (eq_refl (term254 _92392)). Qed.
Lemma lem6922982 (_92392 : int) : (term297 _92392) = (term319 _92392).
Proof. exact (MK_COMB (@lem6922981 _92392) (@lem6922980)). Qed.
Lemma lem6922983 (_92392 : int) : (term319 _92392) = (real_of_int _92392).
Proof. exact (@lem1982723 (real_of_int _92392)). Qed.
Lemma lem6922984 (_92392 : int) : (term297 _92392) = (real_of_int _92392).
Proof. exact (TRANS (@lem6922982 _92392) (@lem6922983 _92392)). Qed.
Lemma lem6922986 (_92392 : int) : (term296 _92392) = (real_of_int _92392).
Proof. exact (TRANS (@lem6922950 _92392) (@lem6922984 _92392)). Qed.
Lemma lem6922987 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6922988 (_92392 : int) : (term320 _92392) = (term321 _92392).
Proof. exact (MK_COMB (@lem6922987) (@lem6922986 _92392)). Qed.
Lemma lem6922989 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem6922990 (_92392 : int) : (term295 _92392) = (term322 _92392).
Proof. exact (MK_COMB (@lem6922988 _92392) (@lem6922989)). Qed.
Lemma lem6922991 (_92392 : int) : (term220 _92392) = (term322 _92392).
Proof. exact (TRANS (@lem6922944 _92392) (@lem6922990 _92392)). Qed.
Lemma lem6922992 (_92393 : int) : (term220 _92393) = (term295 _92393).
Proof. exact (@lem1988287 (real_of_int _92393) term217). Qed.
Lemma lem6922998 (_92393 : int) : (term296 _92393) = (term297 _92393).
Proof. exact (@lem1982792 (real_of_int _92393) term217). Qed.
Lemma lem6923000 (x : nat) : (real_of_num x) = (term298 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6923001 : term217 = term299.
Proof. exact (@lem6923000 (NUMERAL 0)). Qed.
Lemma lem6923003 (x : nat) : (term300 x) = (term301 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6923004 : term302 = term303.
Proof. exact (@lem6923003 term237). Qed.
Lemma lem6923005 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923006 : term304 = term305.
Proof. exact (MK_COMB (@lem6923005) (@lem6923004)). Qed.
Lemma lem6923007 : term306 = term307.
Proof. exact (MK_COMB (@lem6923006) (@lem6923001)). Qed.
Lemma lem6923008 : term307 = term308.
Proof. exact (@lem1981613 term302 term217 term236 term236). Qed.
Lemma lem6923010 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923011 : term311 = term312.
Proof. exact (@lem6923010 term237 term237). Qed.
Lemma lem6923012 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923013 : term314 = term237.
Proof. exact (EQ_MP (@lem6923012) (@lem940073)). Qed.
Lemma lem6923014 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923015 : term312 = term236.
Proof. exact (MK_COMB (@lem6923014) (@lem6923013)). Qed.
Lemma lem6923016 : term311 = term236.
Proof. exact (TRANS (@lem6923011) (@lem6923015)). Qed.
Lemma lem6923018 (x : nat) : (term315 x) = term217.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6923019 : term306 = term217.
Proof. exact (@lem6923018 term237). Qed.
Lemma lem6923020 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6923021 : term316 = term317.
Proof. exact (MK_COMB (@lem6923020) (@lem6923019)). Qed.
Lemma lem6923022 : term308 = term299.
Proof. exact (MK_COMB (@lem6923021) (@lem6923016)). Qed.
Lemma lem6923023 : term307 = term299.
Proof. exact (TRANS (@lem6923008) (@lem6923022)). Qed.
Lemma lem6923024 : term306 = term299.
Proof. exact (TRANS (@lem6923007) (@lem6923023)). Qed.
Lemma lem6923026 (x : real) : (term318 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6923027 : term299 = term217.
Proof. exact (@lem6923026 term217). Qed.
Lemma lem6923028 : term306 = term217.
Proof. exact (TRANS (@lem6923024) (@lem6923027)). Qed.
Lemma lem6923029 (_92393 : int) : (term254 _92393) = (term254 _92393).
Proof. exact (eq_refl (term254 _92393)). Qed.
Lemma lem6923030 (_92393 : int) : (term297 _92393) = (term319 _92393).
Proof. exact (MK_COMB (@lem6923029 _92393) (@lem6923028)). Qed.
Lemma lem6923031 (_92393 : int) : (term319 _92393) = (real_of_int _92393).
Proof. exact (@lem1982723 (real_of_int _92393)). Qed.
Lemma lem6923032 (_92393 : int) : (term297 _92393) = (real_of_int _92393).
Proof. exact (TRANS (@lem6923030 _92393) (@lem6923031 _92393)). Qed.
Lemma lem6923034 (_92393 : int) : (term296 _92393) = (real_of_int _92393).
Proof. exact (TRANS (@lem6922998 _92393) (@lem6923032 _92393)). Qed.
Lemma lem6923035 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6923036 (_92393 : int) : (term320 _92393) = (term321 _92393).
Proof. exact (MK_COMB (@lem6923035) (@lem6923034 _92393)). Qed.
Lemma lem6923037 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem6923038 (_92393 : int) : (term295 _92393) = (term322 _92393).
Proof. exact (MK_COMB (@lem6923036 _92393) (@lem6923037)). Qed.
Lemma lem6923039 (_92393 : int) : (term220 _92393) = (term322 _92393).
Proof. exact (TRANS (@lem6922992 _92393) (@lem6923038 _92393)). Qed.
Lemma lem6923040 (_92394 : int) : (term220 _92394) = (term295 _92394).
Proof. exact (@lem1988287 (real_of_int _92394) term217). Qed.
Lemma lem6923046 (_92394 : int) : (term296 _92394) = (term297 _92394).
Proof. exact (@lem1982792 (real_of_int _92394) term217). Qed.
Lemma lem6923048 (x : nat) : (real_of_num x) = (term298 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6923049 : term217 = term299.
Proof. exact (@lem6923048 (NUMERAL 0)). Qed.
Lemma lem6923051 (x : nat) : (term300 x) = (term301 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6923052 : term302 = term303.
Proof. exact (@lem6923051 term237). Qed.
Lemma lem6923053 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923054 : term304 = term305.
Proof. exact (MK_COMB (@lem6923053) (@lem6923052)). Qed.
Lemma lem6923055 : term306 = term307.
Proof. exact (MK_COMB (@lem6923054) (@lem6923049)). Qed.
Lemma lem6923056 : term307 = term308.
Proof. exact (@lem1981613 term302 term217 term236 term236). Qed.
Lemma lem6923058 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923059 : term311 = term312.
Proof. exact (@lem6923058 term237 term237). Qed.
Lemma lem6923060 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923061 : term314 = term237.
Proof. exact (EQ_MP (@lem6923060) (@lem940073)). Qed.
Lemma lem6923062 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923063 : term312 = term236.
Proof. exact (MK_COMB (@lem6923062) (@lem6923061)). Qed.
Lemma lem6923064 : term311 = term236.
Proof. exact (TRANS (@lem6923059) (@lem6923063)). Qed.
Lemma lem6923066 (x : nat) : (term315 x) = term217.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6923067 : term306 = term217.
Proof. exact (@lem6923066 term237). Qed.
Lemma lem6923068 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6923069 : term316 = term317.
Proof. exact (MK_COMB (@lem6923068) (@lem6923067)). Qed.
Lemma lem6923070 : term308 = term299.
Proof. exact (MK_COMB (@lem6923069) (@lem6923064)). Qed.
Lemma lem6923071 : term307 = term299.
Proof. exact (TRANS (@lem6923056) (@lem6923070)). Qed.
Lemma lem6923072 : term306 = term299.
Proof. exact (TRANS (@lem6923055) (@lem6923071)). Qed.
Lemma lem6923074 (x : real) : (term318 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6923075 : term299 = term217.
Proof. exact (@lem6923074 term217). Qed.
Lemma lem6923076 : term306 = term217.
Proof. exact (TRANS (@lem6923072) (@lem6923075)). Qed.
Lemma lem6923077 (_92394 : int) : (term254 _92394) = (term254 _92394).
Proof. exact (eq_refl (term254 _92394)). Qed.
Lemma lem6923078 (_92394 : int) : (term297 _92394) = (term319 _92394).
Proof. exact (MK_COMB (@lem6923077 _92394) (@lem6923076)). Qed.
Lemma lem6923079 (_92394 : int) : (term319 _92394) = (real_of_int _92394).
Proof. exact (@lem1982723 (real_of_int _92394)). Qed.
Lemma lem6923080 (_92394 : int) : (term297 _92394) = (real_of_int _92394).
Proof. exact (TRANS (@lem6923078 _92394) (@lem6923079 _92394)). Qed.
Lemma lem6923082 (_92394 : int) : (term296 _92394) = (real_of_int _92394).
Proof. exact (TRANS (@lem6923046 _92394) (@lem6923080 _92394)). Qed.
Lemma lem6923083 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6923084 (_92394 : int) : (term320 _92394) = (term321 _92394).
Proof. exact (MK_COMB (@lem6923083) (@lem6923082 _92394)). Qed.
Lemma lem6923085 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem6923086 (_92394 : int) : (term295 _92394) = (term322 _92394).
Proof. exact (MK_COMB (@lem6923084 _92394) (@lem6923085)). Qed.
Lemma lem6923087 (_92394 : int) : (term220 _92394) = (term322 _92394).
Proof. exact (TRANS (@lem6923040 _92394) (@lem6923086 _92394)). Qed.
Lemma lem6923088 (_92392 : int) (_92393 : int) : (term241 _92392 _92393) = (term323 _92392 _92393).
Proof. exact (@lem1988287 (term229 _92392 _92393) (term238 _92392 _92393)). Qed.
Lemma lem6923105 (_92392 : int) (_92393 : int) : (term238 _92392 _92393) = (term324 _92392 _92393).
Proof. exact (@lem1982755 (real_of_int _92392) (real_of_int _92393) term236). Qed.
Lemma lem6923114 (_92392 : int) (_92393 : int) : (term325 _92392 _92393) = (term325 _92392 _92393).
Proof. exact (eq_refl (term325 _92392 _92393)). Qed.
Lemma lem6923115 (_92392 : int) (_92393 : int) : (term326 _92392 _92393) = (term327 _92392 _92393).
Proof. exact (MK_COMB (@lem6923114 _92392 _92393) (@lem6923105 _92392 _92393)). Qed.
Lemma lem6923116 (_92392 : int) (_92393 : int) : (term327 _92392 _92393) = (term328 _92392 _92393).
Proof. exact (@lem1982792 (term229 _92392 _92393) (term324 _92392 _92393)). Qed.
Lemma lem6923117 (_92392 : int) (_92393 : int) : (term329 _92392 _92393) = (term330 _92392 _92393).
Proof. exact (@lem1982781 (real_of_int _92392) term302 (term272 _92393)). Qed.
Lemma lem6923118 (_92393 : int) : (term331 _92393) = (term332 _92393).
Proof. exact (@lem1982781 (real_of_int _92393) term302 term236). Qed.
Lemma lem6923120 (x : nat) : (real_of_num x) = (term298 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6923121 : term236 = term333.
Proof. exact (@lem6923120 term237). Qed.
Lemma lem6923123 (x : nat) : (term300 x) = (term301 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6923124 : term302 = term303.
Proof. exact (@lem6923123 term237). Qed.
Lemma lem6923125 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923126 : term304 = term305.
Proof. exact (MK_COMB (@lem6923125) (@lem6923124)). Qed.
Lemma lem6923127 : term334 = term335.
Proof. exact (MK_COMB (@lem6923126) (@lem6923121)). Qed.
Lemma lem6923128 : term335 = term336.
Proof. exact (@lem1981613 term302 term236 term236 term236). Qed.
Lemma lem6923130 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923131 : term311 = term312.
Proof. exact (@lem6923130 term237 term237). Qed.
Lemma lem6923132 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923133 : term314 = term237.
Proof. exact (EQ_MP (@lem6923132) (@lem940073)). Qed.
Lemma lem6923134 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923135 : term312 = term236.
Proof. exact (MK_COMB (@lem6923134) (@lem6923133)). Qed.
Lemma lem6923136 : term311 = term236.
Proof. exact (TRANS (@lem6923131) (@lem6923135)). Qed.
Lemma lem6923138 (m : nat) (n : nat) : (term337 m n) = (term338 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6923139 : term334 = term339.
Proof. exact (@lem6923138 term237 term237). Qed.
Lemma lem6923140 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923141 : term314 = term237.
Proof. exact (EQ_MP (@lem6923140) (@lem940073)). Qed.
Lemma lem6923142 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923143 : term312 = term236.
Proof. exact (MK_COMB (@lem6923142) (@lem6923141)). Qed.
Lemma lem6923144 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6923145 : term339 = term302.
Proof. exact (MK_COMB (@lem6923144) (@lem6923143)). Qed.
Lemma lem6923146 : term334 = term302.
Proof. exact (TRANS (@lem6923139) (@lem6923145)). Qed.
Lemma lem6923147 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6923148 : term340 = term341.
Proof. exact (MK_COMB (@lem6923147) (@lem6923146)). Qed.
Lemma lem6923149 : term336 = term303.
Proof. exact (MK_COMB (@lem6923148) (@lem6923136)). Qed.
Lemma lem6923150 : term335 = term303.
Proof. exact (TRANS (@lem6923128) (@lem6923149)). Qed.
Lemma lem6923151 : term334 = term303.
Proof. exact (TRANS (@lem6923127) (@lem6923150)). Qed.
Lemma lem6923153 (x : real) : (term318 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6923154 : term303 = term302.
Proof. exact (@lem6923153 term302). Qed.
Lemma lem6923155 : term334 = term302.
Proof. exact (TRANS (@lem6923151) (@lem6923154)). Qed.
Lemma lem6923158 (_92393 : int) : (term342 _92393) = (term342 _92393).
Proof. exact (eq_refl (term342 _92393)). Qed.
Lemma lem6923159 (_92393 : int) : (term332 _92393) = (term343 _92393).
Proof. exact (MK_COMB (@lem6923158 _92393) (@lem6923155)). Qed.
Lemma lem6923160 (_92393 : int) : (term331 _92393) = (term343 _92393).
Proof. exact (TRANS (@lem6923118 _92393) (@lem6923159 _92393)). Qed.
Lemma lem6923163 (_92392 : int) : (term342 _92392) = (term342 _92392).
Proof. exact (eq_refl (term342 _92392)). Qed.
Lemma lem6923164 (_92392 : int) (_92393 : int) : (term330 _92392 _92393) = (term344 _92392 _92393).
Proof. exact (MK_COMB (@lem6923163 _92392) (@lem6923160 _92393)). Qed.
Lemma lem6923165 (_92392 : int) (_92393 : int) : (term329 _92392 _92393) = (term344 _92392 _92393).
Proof. exact (TRANS (@lem6923117 _92392 _92393) (@lem6923164 _92392 _92393)). Qed.
Lemma lem6923166 (_92392 : int) (_92393 : int) : (term234 _92392 _92393) = (term234 _92392 _92393).
Proof. exact (eq_refl (term234 _92392 _92393)). Qed.
Lemma lem6923167 (_92392 : int) (_92393 : int) : (term328 _92392 _92393) = (term345 _92392 _92393).
Proof. exact (MK_COMB (@lem6923166 _92392 _92393) (@lem6923165 _92392 _92393)). Qed.
Lemma lem6923168 (_92392 : int) (_92393 : int) : (term345 _92392 _92393) = (term346 _92392 _92393).
Proof. exact (@lem1982753 (real_of_int _92392) (term347 _92392) (real_of_int _92393) (term343 _92393)). Qed.
Lemma lem6923169 (_92392 : int) : (term348 _92392) = (term349 _92392).
Proof. exact (@lem1982715 term302 (real_of_int _92392)). Qed.
Lemma lem6923171 (x : nat) : (real_of_num x) = (term298 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6923172 : term236 = term333.
Proof. exact (@lem6923171 term237). Qed.
Lemma lem6923174 (x : nat) : (term300 x) = (term301 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6923175 : term302 = term303.
Proof. exact (@lem6923174 term237). Qed.
Lemma lem6923176 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923177 : term350 = term351.
Proof. exact (MK_COMB (@lem6923176) (@lem6923175)). Qed.
Lemma lem6923178 : term352 = term353.
Proof. exact (MK_COMB (@lem6923177) (@lem6923172)). Qed.
Lemma lem6923179 : term354.
Proof. exact (@lem1981473 term302 term236 term236 term236 term217 term236). Qed.
Lemma lem6923181 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923182 : term356 = term357.
Proof. exact (@lem6923181 (NUMERAL 0) term237). Qed.
Lemma lem6923183 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923184 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923185 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923184 h1) (fun h1 : term357 = True => @lem6923183)). Qed.
Lemma lem6923186 : term357 = True.
Proof. exact (EQ_MP (@lem6923185) (@lem6923183)). Qed.
Lemma lem6923187 : term356 = True.
Proof. exact (TRANS (@lem6923182) (@lem6923186)). Qed.
Lemma lem6923188 : True = term356.
Proof. exact (SYM (@lem6923187)). Qed.
Lemma lem6923189 : term356.
Proof. exact (EQ_MP (@lem6923188) (@lem0)). Qed.
Lemma lem6923190 : term359.
Proof. exact (@lem6923179 (@lem6923189)). Qed.
Lemma lem6923192 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923193 : term356 = term357.
Proof. exact (@lem6923192 (NUMERAL 0) term237). Qed.
Lemma lem6923194 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923195 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923196 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923195 h1) (fun h1 : term357 = True => @lem6923194)). Qed.
Lemma lem6923197 : term357 = True.
Proof. exact (EQ_MP (@lem6923196) (@lem6923194)). Qed.
Lemma lem6923198 : term356 = True.
Proof. exact (TRANS (@lem6923193) (@lem6923197)). Qed.
Lemma lem6923199 : True = term356.
Proof. exact (SYM (@lem6923198)). Qed.
Lemma lem6923200 : term356.
Proof. exact (EQ_MP (@lem6923199) (@lem0)). Qed.
Lemma lem6923201 : term360.
Proof. exact (@lem6923190 (@lem6923200)). Qed.
Lemma lem6923203 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923204 : term356 = term357.
Proof. exact (@lem6923203 (NUMERAL 0) term237). Qed.
Lemma lem6923205 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923206 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923207 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923206 h1) (fun h1 : term357 = True => @lem6923205)). Qed.
Lemma lem6923208 : term357 = True.
Proof. exact (EQ_MP (@lem6923207) (@lem6923205)). Qed.
Lemma lem6923209 : term356 = True.
Proof. exact (TRANS (@lem6923204) (@lem6923208)). Qed.
Lemma lem6923210 : True = term356.
Proof. exact (SYM (@lem6923209)). Qed.
Lemma lem6923211 : term356.
Proof. exact (EQ_MP (@lem6923210) (@lem0)). Qed.
Lemma lem6923212 : term361.
Proof. exact (@lem6923201 (@lem6923211)). Qed.
Lemma lem6923214 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923215 : term311 = term312.
Proof. exact (@lem6923214 term237 term237). Qed.
Lemma lem6923216 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923217 : term314 = term237.
Proof. exact (EQ_MP (@lem6923216) (@lem940073)). Qed.
Lemma lem6923218 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923219 : term312 = term236.
Proof. exact (MK_COMB (@lem6923218) (@lem6923217)). Qed.
Lemma lem6923220 : term311 = term236.
Proof. exact (TRANS (@lem6923215) (@lem6923219)). Qed.
Lemma lem6923222 (m : nat) (n : nat) : (term337 m n) = (term338 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6923223 : term334 = term339.
Proof. exact (@lem6923222 term237 term237). Qed.
Lemma lem6923224 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923225 : term314 = term237.
Proof. exact (EQ_MP (@lem6923224) (@lem940073)). Qed.
Lemma lem6923226 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923227 : term312 = term236.
Proof. exact (MK_COMB (@lem6923226) (@lem6923225)). Qed.
Lemma lem6923228 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6923229 : term339 = term302.
Proof. exact (MK_COMB (@lem6923228) (@lem6923227)). Qed.
Lemma lem6923230 : term334 = term302.
Proof. exact (TRANS (@lem6923223) (@lem6923229)). Qed.
Lemma lem6923231 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923232 : term362 = term350.
Proof. exact (MK_COMB (@lem6923231) (@lem6923230)). Qed.
Lemma lem6923233 : term363 = term352.
Proof. exact (MK_COMB (@lem6923232) (@lem6923220)). Qed.
Lemma lem6923235 (m : nat) : (term364 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6923236 : term352 = term217.
Proof. exact (@lem6923235 term237). Qed.
Lemma lem6923237 : term363 = term217.
Proof. exact (TRANS (@lem6923233) (@lem6923236)). Qed.
Lemma lem6923238 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923239 : term365 = term366.
Proof. exact (MK_COMB (@lem6923238) (@lem6923237)). Qed.
Lemma lem6923240 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem6923241 : term367 = term368.
Proof. exact (MK_COMB (@lem6923239) (@lem6923240)). Qed.
Lemma lem6923243 (x : nat) : (term369 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6923244 : term368 = term217.
Proof. exact (@lem6923243 term237). Qed.
Lemma lem6923245 : term367 = term217.
Proof. exact (TRANS (@lem6923241) (@lem6923244)). Qed.
Lemma lem6923247 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923248 : term311 = term312.
Proof. exact (@lem6923247 term237 term237). Qed.
Lemma lem6923249 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923250 : term314 = term237.
Proof. exact (EQ_MP (@lem6923249) (@lem940073)). Qed.
Lemma lem6923251 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923252 : term312 = term236.
Proof. exact (MK_COMB (@lem6923251) (@lem6923250)). Qed.
Lemma lem6923253 : term311 = term236.
Proof. exact (TRANS (@lem6923248) (@lem6923252)). Qed.
Lemma lem6923254 : term366 = term366.
Proof. exact (eq_refl term366). Qed.
Lemma lem6923255 : term370 = term368.
Proof. exact (MK_COMB (@lem6923254) (@lem6923253)). Qed.
Lemma lem6923257 (x : nat) : (term369 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6923258 : term368 = term217.
Proof. exact (@lem6923257 term237). Qed.
Lemma lem6923259 : term370 = term217.
Proof. exact (TRANS (@lem6923255) (@lem6923258)). Qed.
Lemma lem6923260 : term217 = term370.
Proof. exact (SYM (@lem6923259)). Qed.
Lemma lem6923261 : term367 = term370.
Proof. exact (TRANS (@lem6923245) (@lem6923260)). Qed.
Lemma lem6923262 : term353 = term299.
Proof. exact (@lem6923212 (@lem6923261)). Qed.
Lemma lem6923263 : term352 = term299.
Proof. exact (TRANS (@lem6923178) (@lem6923262)). Qed.
Lemma lem6923265 (x : real) : (term318 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6923266 : term299 = term217.
Proof. exact (@lem6923265 term217). Qed.
Lemma lem6923267 : term352 = term217.
Proof. exact (TRANS (@lem6923263) (@lem6923266)). Qed.
Lemma lem6923268 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923269 : term371 = term366.
Proof. exact (MK_COMB (@lem6923268) (@lem6923267)). Qed.
Lemma lem6923270 (_92392 : int) : (real_of_int _92392) = (real_of_int _92392).
Proof. exact (eq_refl (real_of_int _92392)). Qed.
Lemma lem6923271 (_92392 : int) : (term349 _92392) = (term372 _92392).
Proof. exact (MK_COMB (@lem6923269) (@lem6923270 _92392)). Qed.
Lemma lem6923272 (_92392 : int) : (term348 _92392) = (term372 _92392).
Proof. exact (TRANS (@lem6923169 _92392) (@lem6923271 _92392)). Qed.
Lemma lem6923273 (_92392 : int) : (term372 _92392) = term217.
Proof. exact (@lem1982719 (real_of_int _92392)). Qed.
Lemma lem6923274 (_92392 : int) : (term348 _92392) = term217.
Proof. exact (TRANS (@lem6923272 _92392) (@lem6923273 _92392)). Qed.
Lemma lem6923275 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923276 (_92392 : int) : (term373 _92392) = term374.
Proof. exact (MK_COMB (@lem6923275) (@lem6923274 _92392)). Qed.
Lemma lem6923277 (_92393 : int) : (term375 _92393) = (term376 _92393).
Proof. exact (@lem1982763 (real_of_int _92393) (term347 _92393) term302). Qed.
Lemma lem6923278 (_92393 : int) : (term348 _92393) = (term349 _92393).
Proof. exact (@lem1982715 term302 (real_of_int _92393)). Qed.
Lemma lem6923280 (x : nat) : (real_of_num x) = (term298 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6923281 : term236 = term333.
Proof. exact (@lem6923280 term237). Qed.
Lemma lem6923283 (x : nat) : (term300 x) = (term301 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6923284 : term302 = term303.
Proof. exact (@lem6923283 term237). Qed.
Lemma lem6923285 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923286 : term350 = term351.
Proof. exact (MK_COMB (@lem6923285) (@lem6923284)). Qed.
Lemma lem6923287 : term352 = term353.
Proof. exact (MK_COMB (@lem6923286) (@lem6923281)). Qed.
Lemma lem6923288 : term354.
Proof. exact (@lem1981473 term302 term236 term236 term236 term217 term236). Qed.
Lemma lem6923290 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923291 : term356 = term357.
Proof. exact (@lem6923290 (NUMERAL 0) term237). Qed.
Lemma lem6923292 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923293 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923294 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923293 h1) (fun h1 : term357 = True => @lem6923292)). Qed.
Lemma lem6923295 : term357 = True.
Proof. exact (EQ_MP (@lem6923294) (@lem6923292)). Qed.
Lemma lem6923296 : term356 = True.
Proof. exact (TRANS (@lem6923291) (@lem6923295)). Qed.
Lemma lem6923297 : True = term356.
Proof. exact (SYM (@lem6923296)). Qed.
Lemma lem6923298 : term356.
Proof. exact (EQ_MP (@lem6923297) (@lem0)). Qed.
Lemma lem6923299 : term359.
Proof. exact (@lem6923288 (@lem6923298)). Qed.
Lemma lem6923301 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923302 : term356 = term357.
Proof. exact (@lem6923301 (NUMERAL 0) term237). Qed.
Lemma lem6923303 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923304 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923305 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923304 h1) (fun h1 : term357 = True => @lem6923303)). Qed.
Lemma lem6923306 : term357 = True.
Proof. exact (EQ_MP (@lem6923305) (@lem6923303)). Qed.
Lemma lem6923307 : term356 = True.
Proof. exact (TRANS (@lem6923302) (@lem6923306)). Qed.
Lemma lem6923308 : True = term356.
Proof. exact (SYM (@lem6923307)). Qed.
Lemma lem6923309 : term356.
Proof. exact (EQ_MP (@lem6923308) (@lem0)). Qed.
Lemma lem6923310 : term360.
Proof. exact (@lem6923299 (@lem6923309)). Qed.
Lemma lem6923312 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923313 : term356 = term357.
Proof. exact (@lem6923312 (NUMERAL 0) term237). Qed.
Lemma lem6923314 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923315 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923316 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923315 h1) (fun h1 : term357 = True => @lem6923314)). Qed.
Lemma lem6923317 : term357 = True.
Proof. exact (EQ_MP (@lem6923316) (@lem6923314)). Qed.
Lemma lem6923318 : term356 = True.
Proof. exact (TRANS (@lem6923313) (@lem6923317)). Qed.
Lemma lem6923319 : True = term356.
Proof. exact (SYM (@lem6923318)). Qed.
Lemma lem6923320 : term356.
Proof. exact (EQ_MP (@lem6923319) (@lem0)). Qed.
Lemma lem6923321 : term361.
Proof. exact (@lem6923310 (@lem6923320)). Qed.
Lemma lem6923323 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923324 : term311 = term312.
Proof. exact (@lem6923323 term237 term237). Qed.
Lemma lem6923325 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923326 : term314 = term237.
Proof. exact (EQ_MP (@lem6923325) (@lem940073)). Qed.
Lemma lem6923327 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923328 : term312 = term236.
Proof. exact (MK_COMB (@lem6923327) (@lem6923326)). Qed.
Lemma lem6923329 : term311 = term236.
Proof. exact (TRANS (@lem6923324) (@lem6923328)). Qed.
Lemma lem6923331 (m : nat) (n : nat) : (term337 m n) = (term338 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6923332 : term334 = term339.
Proof. exact (@lem6923331 term237 term237). Qed.
Lemma lem6923333 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923334 : term314 = term237.
Proof. exact (EQ_MP (@lem6923333) (@lem940073)). Qed.
Lemma lem6923335 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923336 : term312 = term236.
Proof. exact (MK_COMB (@lem6923335) (@lem6923334)). Qed.
Lemma lem6923337 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6923338 : term339 = term302.
Proof. exact (MK_COMB (@lem6923337) (@lem6923336)). Qed.
Lemma lem6923339 : term334 = term302.
Proof. exact (TRANS (@lem6923332) (@lem6923338)). Qed.
Lemma lem6923340 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923341 : term362 = term350.
Proof. exact (MK_COMB (@lem6923340) (@lem6923339)). Qed.
Lemma lem6923342 : term363 = term352.
Proof. exact (MK_COMB (@lem6923341) (@lem6923329)). Qed.
Lemma lem6923344 (m : nat) : (term364 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6923345 : term352 = term217.
Proof. exact (@lem6923344 term237). Qed.
Lemma lem6923346 : term363 = term217.
Proof. exact (TRANS (@lem6923342) (@lem6923345)). Qed.
Lemma lem6923347 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923348 : term365 = term366.
Proof. exact (MK_COMB (@lem6923347) (@lem6923346)). Qed.
Lemma lem6923349 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem6923350 : term367 = term368.
Proof. exact (MK_COMB (@lem6923348) (@lem6923349)). Qed.
Lemma lem6923352 (x : nat) : (term369 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6923353 : term368 = term217.
Proof. exact (@lem6923352 term237). Qed.
Lemma lem6923354 : term367 = term217.
Proof. exact (TRANS (@lem6923350) (@lem6923353)). Qed.
Lemma lem6923356 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923357 : term311 = term312.
Proof. exact (@lem6923356 term237 term237). Qed.
Lemma lem6923358 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923359 : term314 = term237.
Proof. exact (EQ_MP (@lem6923358) (@lem940073)). Qed.
Lemma lem6923360 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923361 : term312 = term236.
Proof. exact (MK_COMB (@lem6923360) (@lem6923359)). Qed.
Lemma lem6923362 : term311 = term236.
Proof. exact (TRANS (@lem6923357) (@lem6923361)). Qed.
Lemma lem6923363 : term366 = term366.
Proof. exact (eq_refl term366). Qed.
Lemma lem6923364 : term370 = term368.
Proof. exact (MK_COMB (@lem6923363) (@lem6923362)). Qed.
Lemma lem6923366 (x : nat) : (term369 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6923367 : term368 = term217.
Proof. exact (@lem6923366 term237). Qed.
Lemma lem6923368 : term370 = term217.
Proof. exact (TRANS (@lem6923364) (@lem6923367)). Qed.
Lemma lem6923369 : term217 = term370.
Proof. exact (SYM (@lem6923368)). Qed.
Lemma lem6923370 : term367 = term370.
Proof. exact (TRANS (@lem6923354) (@lem6923369)). Qed.
Lemma lem6923371 : term353 = term299.
Proof. exact (@lem6923321 (@lem6923370)). Qed.
Lemma lem6923372 : term352 = term299.
Proof. exact (TRANS (@lem6923287) (@lem6923371)). Qed.
Lemma lem6923374 (x : real) : (term318 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6923375 : term299 = term217.
Proof. exact (@lem6923374 term217). Qed.
Lemma lem6923376 : term352 = term217.
Proof. exact (TRANS (@lem6923372) (@lem6923375)). Qed.
Lemma lem6923377 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923378 : term371 = term366.
Proof. exact (MK_COMB (@lem6923377) (@lem6923376)). Qed.
Lemma lem6923379 (_92393 : int) : (real_of_int _92393) = (real_of_int _92393).
Proof. exact (eq_refl (real_of_int _92393)). Qed.
Lemma lem6923380 (_92393 : int) : (term349 _92393) = (term372 _92393).
Proof. exact (MK_COMB (@lem6923378) (@lem6923379 _92393)). Qed.
Lemma lem6923381 (_92393 : int) : (term348 _92393) = (term372 _92393).
Proof. exact (TRANS (@lem6923278 _92393) (@lem6923380 _92393)). Qed.
Lemma lem6923382 (_92393 : int) : (term372 _92393) = term217.
Proof. exact (@lem1982719 (real_of_int _92393)). Qed.
Lemma lem6923383 (_92393 : int) : (term348 _92393) = term217.
Proof. exact (TRANS (@lem6923381 _92393) (@lem6923382 _92393)). Qed.
Lemma lem6923384 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923385 (_92393 : int) : (term373 _92393) = term374.
Proof. exact (MK_COMB (@lem6923384) (@lem6923383 _92393)). Qed.
Lemma lem6923386 : term302 = term302.
Proof. exact (eq_refl term302). Qed.
Lemma lem6923387 (_92393 : int) : (term376 _92393) = term377.
Proof. exact (MK_COMB (@lem6923385 _92393) (@lem6923386)). Qed.
Lemma lem6923388 (_92393 : int) : (term375 _92393) = term377.
Proof. exact (TRANS (@lem6923277 _92393) (@lem6923387 _92393)). Qed.
Lemma lem6923389 : term377 = term302.
Proof. exact (@lem1982721 term302). Qed.
Lemma lem6923390 (_92393 : int) : (term375 _92393) = term302.
Proof. exact (TRANS (@lem6923388 _92393) (@lem6923389)). Qed.
Lemma lem6923391 (_92392 : int) (_92393 : int) : (term346 _92392 _92393) = term377.
Proof. exact (MK_COMB (@lem6923276 _92392) (@lem6923390 _92393)). Qed.
Lemma lem6923392 (_92392 : int) (_92393 : int) : (term345 _92392 _92393) = term377.
Proof. exact (TRANS (@lem6923168 _92392 _92393) (@lem6923391 _92392 _92393)). Qed.
Lemma lem6923393 : term377 = term302.
Proof. exact (@lem1982721 term302). Qed.
Lemma lem6923394 (_92392 : int) (_92393 : int) : (term345 _92392 _92393) = term302.
Proof. exact (TRANS (@lem6923392 _92392 _92393) (@lem6923393)). Qed.
Lemma lem6923395 (_92392 : int) (_92393 : int) : (term328 _92392 _92393) = term302.
Proof. exact (TRANS (@lem6923167 _92392 _92393) (@lem6923394 _92392 _92393)). Qed.
Lemma lem6923396 (_92392 : int) (_92393 : int) : (term327 _92392 _92393) = term302.
Proof. exact (TRANS (@lem6923116 _92392 _92393) (@lem6923395 _92392 _92393)). Qed.
Lemma lem6923397 (_92392 : int) (_92393 : int) : (term326 _92392 _92393) = term302.
Proof. exact (TRANS (@lem6923115 _92392 _92393) (@lem6923396 _92392 _92393)). Qed.
Lemma lem6923398 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6923399 (_92392 : int) (_92393 : int) : (term378 _92392 _92393) = term379.
Proof. exact (MK_COMB (@lem6923398) (@lem6923397 _92392 _92393)). Qed.
Lemma lem6923400 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem6923401 (_92392 : int) (_92393 : int) : (term323 _92392 _92393) = term380.
Proof. exact (MK_COMB (@lem6923399 _92392 _92393) (@lem6923400)). Qed.
Lemma lem6923402 (_92392 : int) (_92393 : int) : (term241 _92392 _92393) = term380.
Proof. exact (TRANS (@lem6923088 _92392 _92393) (@lem6923401 _92392 _92393)). Qed.
Lemma lem6923403 (_92392 : int) (_92393 : int) (_92394 : int) : (term261 _92392 _92393 _92394) = (term381 _92392 _92393 _92394).
Proof. exact (@lem1988287 (term255 _92392 _92393 _92394) (term258 _92392 _92393 _92394)). Qed.
Lemma lem6923421 (_92392 : int) (_92393 : int) (_92394 : int) : (term258 _92392 _92393 _92394) = (term382 _92392 _92393 _92394).
Proof. exact (@lem1982755 (real_of_int _92392) (term229 _92393 _92394) term236). Qed.
Lemma lem6923426 (_92393 : int) (_92394 : int) : (term238 _92393 _92394) = (term324 _92393 _92394).
Proof. exact (@lem1982755 (real_of_int _92393) (real_of_int _92394) term236). Qed.
Lemma lem6923427 (_92392 : int) : (term254 _92392) = (term254 _92392).
Proof. exact (eq_refl (term254 _92392)). Qed.
Lemma lem6923428 (_92392 : int) (_92393 : int) (_92394 : int) : (term382 _92392 _92393 _92394) = (term383 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6923427 _92392) (@lem6923426 _92393 _92394)). Qed.
Lemma lem6923430 (_92392 : int) (_92393 : int) (_92394 : int) : (term258 _92392 _92393 _92394) = (term383 _92392 _92393 _92394).
Proof. exact (TRANS (@lem6923421 _92392 _92393 _92394) (@lem6923428 _92392 _92393 _92394)). Qed.
Lemma lem6923445 (_92392 : int) (_92393 : int) (_92394 : int) : (term384 _92392 _92393 _92394) = (term384 _92392 _92393 _92394).
Proof. exact (eq_refl (term384 _92392 _92393 _92394)). Qed.
Lemma lem6923446 (_92392 : int) (_92393 : int) (_92394 : int) : (term385 _92392 _92393 _92394) = (term386 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6923445 _92392 _92393 _92394) (@lem6923430 _92392 _92393 _92394)). Qed.
Lemma lem6923447 (_92392 : int) (_92393 : int) (_92394 : int) : (term386 _92392 _92393 _92394) = (term387 _92392 _92393 _92394).
Proof. exact (@lem1982792 (term255 _92392 _92393 _92394) (term383 _92392 _92393 _92394)). Qed.
Lemma lem6923448 (_92392 : int) (_92393 : int) (_92394 : int) : (term388 _92392 _92393 _92394) = (term389 _92392 _92393 _92394).
Proof. exact (@lem1982781 (real_of_int _92392) term302 (term324 _92393 _92394)). Qed.
Lemma lem6923449 (_92393 : int) (_92394 : int) : (term329 _92393 _92394) = (term330 _92393 _92394).
Proof. exact (@lem1982781 (real_of_int _92393) term302 (term272 _92394)). Qed.
Lemma lem6923450 (_92394 : int) : (term331 _92394) = (term332 _92394).
Proof. exact (@lem1982781 (real_of_int _92394) term302 term236). Qed.
Lemma lem6923452 (x : nat) : (real_of_num x) = (term298 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6923453 : term236 = term333.
Proof. exact (@lem6923452 term237). Qed.
Lemma lem6923455 (x : nat) : (term300 x) = (term301 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6923456 : term302 = term303.
Proof. exact (@lem6923455 term237). Qed.
Lemma lem6923457 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923458 : term304 = term305.
Proof. exact (MK_COMB (@lem6923457) (@lem6923456)). Qed.
Lemma lem6923459 : term334 = term335.
Proof. exact (MK_COMB (@lem6923458) (@lem6923453)). Qed.
Lemma lem6923460 : term335 = term336.
Proof. exact (@lem1981613 term302 term236 term236 term236). Qed.
Lemma lem6923462 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923463 : term311 = term312.
Proof. exact (@lem6923462 term237 term237). Qed.
Lemma lem6923464 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923465 : term314 = term237.
Proof. exact (EQ_MP (@lem6923464) (@lem940073)). Qed.
Lemma lem6923466 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923467 : term312 = term236.
Proof. exact (MK_COMB (@lem6923466) (@lem6923465)). Qed.
Lemma lem6923468 : term311 = term236.
Proof. exact (TRANS (@lem6923463) (@lem6923467)). Qed.
Lemma lem6923470 (m : nat) (n : nat) : (term337 m n) = (term338 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6923471 : term334 = term339.
Proof. exact (@lem6923470 term237 term237). Qed.
Lemma lem6923472 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923473 : term314 = term237.
Proof. exact (EQ_MP (@lem6923472) (@lem940073)). Qed.
Lemma lem6923474 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923475 : term312 = term236.
Proof. exact (MK_COMB (@lem6923474) (@lem6923473)). Qed.
Lemma lem6923476 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6923477 : term339 = term302.
Proof. exact (MK_COMB (@lem6923476) (@lem6923475)). Qed.
Lemma lem6923478 : term334 = term302.
Proof. exact (TRANS (@lem6923471) (@lem6923477)). Qed.
Lemma lem6923479 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6923480 : term340 = term341.
Proof. exact (MK_COMB (@lem6923479) (@lem6923478)). Qed.
Lemma lem6923481 : term336 = term303.
Proof. exact (MK_COMB (@lem6923480) (@lem6923468)). Qed.
Lemma lem6923482 : term335 = term303.
Proof. exact (TRANS (@lem6923460) (@lem6923481)). Qed.
Lemma lem6923483 : term334 = term303.
Proof. exact (TRANS (@lem6923459) (@lem6923482)). Qed.
Lemma lem6923485 (x : real) : (term318 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6923486 : term303 = term302.
Proof. exact (@lem6923485 term302). Qed.
Lemma lem6923487 : term334 = term302.
Proof. exact (TRANS (@lem6923483) (@lem6923486)). Qed.
Lemma lem6923490 (_92394 : int) : (term342 _92394) = (term342 _92394).
Proof. exact (eq_refl (term342 _92394)). Qed.
Lemma lem6923491 (_92394 : int) : (term332 _92394) = (term343 _92394).
Proof. exact (MK_COMB (@lem6923490 _92394) (@lem6923487)). Qed.
Lemma lem6923492 (_92394 : int) : (term331 _92394) = (term343 _92394).
Proof. exact (TRANS (@lem6923450 _92394) (@lem6923491 _92394)). Qed.
Lemma lem6923495 (_92393 : int) : (term342 _92393) = (term342 _92393).
Proof. exact (eq_refl (term342 _92393)). Qed.
Lemma lem6923496 (_92393 : int) (_92394 : int) : (term330 _92393 _92394) = (term344 _92393 _92394).
Proof. exact (MK_COMB (@lem6923495 _92393) (@lem6923492 _92394)). Qed.
Lemma lem6923497 (_92393 : int) (_92394 : int) : (term329 _92393 _92394) = (term344 _92393 _92394).
Proof. exact (TRANS (@lem6923449 _92393 _92394) (@lem6923496 _92393 _92394)). Qed.
Lemma lem6923500 (_92392 : int) : (term342 _92392) = (term342 _92392).
Proof. exact (eq_refl (term342 _92392)). Qed.
Lemma lem6923501 (_92392 : int) (_92393 : int) (_92394 : int) : (term389 _92392 _92393 _92394) = (term390 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6923500 _92392) (@lem6923497 _92393 _92394)). Qed.
Lemma lem6923502 (_92392 : int) (_92393 : int) (_92394 : int) : (term388 _92392 _92393 _92394) = (term390 _92392 _92393 _92394).
Proof. exact (TRANS (@lem6923448 _92392 _92393 _92394) (@lem6923501 _92392 _92393 _92394)). Qed.
Lemma lem6923503 (_92392 : int) (_92393 : int) (_92394 : int) : (term257 _92392 _92393 _92394) = (term257 _92392 _92393 _92394).
Proof. exact (eq_refl (term257 _92392 _92393 _92394)). Qed.
Lemma lem6923504 (_92392 : int) (_92393 : int) (_92394 : int) : (term387 _92392 _92393 _92394) = (term391 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6923503 _92392 _92393 _92394) (@lem6923502 _92392 _92393 _92394)). Qed.
Lemma lem6923505 (_92392 : int) (_92393 : int) (_92394 : int) : (term391 _92392 _92393 _92394) = (term392 _92392 _92393 _92394).
Proof. exact (@lem1982753 (real_of_int _92392) (term347 _92392) (term229 _92393 _92394) (term344 _92393 _92394)). Qed.
Lemma lem6923506 (_92392 : int) : (term348 _92392) = (term349 _92392).
Proof. exact (@lem1982715 term302 (real_of_int _92392)). Qed.
Lemma lem6923508 (x : nat) : (real_of_num x) = (term298 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6923509 : term236 = term333.
Proof. exact (@lem6923508 term237). Qed.
Lemma lem6923511 (x : nat) : (term300 x) = (term301 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6923512 : term302 = term303.
Proof. exact (@lem6923511 term237). Qed.
Lemma lem6923513 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923514 : term350 = term351.
Proof. exact (MK_COMB (@lem6923513) (@lem6923512)). Qed.
Lemma lem6923515 : term352 = term353.
Proof. exact (MK_COMB (@lem6923514) (@lem6923509)). Qed.
Lemma lem6923516 : term354.
Proof. exact (@lem1981473 term302 term236 term236 term236 term217 term236). Qed.
Lemma lem6923518 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923519 : term356 = term357.
Proof. exact (@lem6923518 (NUMERAL 0) term237). Qed.
Lemma lem6923520 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923521 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923522 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923521 h1) (fun h1 : term357 = True => @lem6923520)). Qed.
Lemma lem6923523 : term357 = True.
Proof. exact (EQ_MP (@lem6923522) (@lem6923520)). Qed.
Lemma lem6923524 : term356 = True.
Proof. exact (TRANS (@lem6923519) (@lem6923523)). Qed.
Lemma lem6923525 : True = term356.
Proof. exact (SYM (@lem6923524)). Qed.
Lemma lem6923526 : term356.
Proof. exact (EQ_MP (@lem6923525) (@lem0)). Qed.
Lemma lem6923527 : term359.
Proof. exact (@lem6923516 (@lem6923526)). Qed.
Lemma lem6923529 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923530 : term356 = term357.
Proof. exact (@lem6923529 (NUMERAL 0) term237). Qed.
Lemma lem6923531 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923532 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923533 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923532 h1) (fun h1 : term357 = True => @lem6923531)). Qed.
Lemma lem6923534 : term357 = True.
Proof. exact (EQ_MP (@lem6923533) (@lem6923531)). Qed.
Lemma lem6923535 : term356 = True.
Proof. exact (TRANS (@lem6923530) (@lem6923534)). Qed.
Lemma lem6923536 : True = term356.
Proof. exact (SYM (@lem6923535)). Qed.
Lemma lem6923537 : term356.
Proof. exact (EQ_MP (@lem6923536) (@lem0)). Qed.
Lemma lem6923538 : term360.
Proof. exact (@lem6923527 (@lem6923537)). Qed.
Lemma lem6923540 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923541 : term356 = term357.
Proof. exact (@lem6923540 (NUMERAL 0) term237). Qed.
Lemma lem6923542 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923543 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923544 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923543 h1) (fun h1 : term357 = True => @lem6923542)). Qed.
Lemma lem6923545 : term357 = True.
Proof. exact (EQ_MP (@lem6923544) (@lem6923542)). Qed.
Lemma lem6923546 : term356 = True.
Proof. exact (TRANS (@lem6923541) (@lem6923545)). Qed.
Lemma lem6923547 : True = term356.
Proof. exact (SYM (@lem6923546)). Qed.
Lemma lem6923548 : term356.
Proof. exact (EQ_MP (@lem6923547) (@lem0)). Qed.
Lemma lem6923549 : term361.
Proof. exact (@lem6923538 (@lem6923548)). Qed.
Lemma lem6923551 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923552 : term311 = term312.
Proof. exact (@lem6923551 term237 term237). Qed.
Lemma lem6923553 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923554 : term314 = term237.
Proof. exact (EQ_MP (@lem6923553) (@lem940073)). Qed.
Lemma lem6923555 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923556 : term312 = term236.
Proof. exact (MK_COMB (@lem6923555) (@lem6923554)). Qed.
Lemma lem6923557 : term311 = term236.
Proof. exact (TRANS (@lem6923552) (@lem6923556)). Qed.
Lemma lem6923559 (m : nat) (n : nat) : (term337 m n) = (term338 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6923560 : term334 = term339.
Proof. exact (@lem6923559 term237 term237). Qed.
Lemma lem6923561 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923562 : term314 = term237.
Proof. exact (EQ_MP (@lem6923561) (@lem940073)). Qed.
Lemma lem6923563 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923564 : term312 = term236.
Proof. exact (MK_COMB (@lem6923563) (@lem6923562)). Qed.
Lemma lem6923565 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6923566 : term339 = term302.
Proof. exact (MK_COMB (@lem6923565) (@lem6923564)). Qed.
Lemma lem6923567 : term334 = term302.
Proof. exact (TRANS (@lem6923560) (@lem6923566)). Qed.
Lemma lem6923568 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923569 : term362 = term350.
Proof. exact (MK_COMB (@lem6923568) (@lem6923567)). Qed.
Lemma lem6923570 : term363 = term352.
Proof. exact (MK_COMB (@lem6923569) (@lem6923557)). Qed.
Lemma lem6923572 (m : nat) : (term364 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6923573 : term352 = term217.
Proof. exact (@lem6923572 term237). Qed.
Lemma lem6923574 : term363 = term217.
Proof. exact (TRANS (@lem6923570) (@lem6923573)). Qed.
Lemma lem6923575 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923576 : term365 = term366.
Proof. exact (MK_COMB (@lem6923575) (@lem6923574)). Qed.
Lemma lem6923577 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem6923578 : term367 = term368.
Proof. exact (MK_COMB (@lem6923576) (@lem6923577)). Qed.
Lemma lem6923580 (x : nat) : (term369 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6923581 : term368 = term217.
Proof. exact (@lem6923580 term237). Qed.
Lemma lem6923582 : term367 = term217.
Proof. exact (TRANS (@lem6923578) (@lem6923581)). Qed.
Lemma lem6923584 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923585 : term311 = term312.
Proof. exact (@lem6923584 term237 term237). Qed.
Lemma lem6923586 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923587 : term314 = term237.
Proof. exact (EQ_MP (@lem6923586) (@lem940073)). Qed.
Lemma lem6923588 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923589 : term312 = term236.
Proof. exact (MK_COMB (@lem6923588) (@lem6923587)). Qed.
Lemma lem6923590 : term311 = term236.
Proof. exact (TRANS (@lem6923585) (@lem6923589)). Qed.
Lemma lem6923591 : term366 = term366.
Proof. exact (eq_refl term366). Qed.
Lemma lem6923592 : term370 = term368.
Proof. exact (MK_COMB (@lem6923591) (@lem6923590)). Qed.
Lemma lem6923594 (x : nat) : (term369 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6923595 : term368 = term217.
Proof. exact (@lem6923594 term237). Qed.
Lemma lem6923596 : term370 = term217.
Proof. exact (TRANS (@lem6923592) (@lem6923595)). Qed.
Lemma lem6923597 : term217 = term370.
Proof. exact (SYM (@lem6923596)). Qed.
Lemma lem6923598 : term367 = term370.
Proof. exact (TRANS (@lem6923582) (@lem6923597)). Qed.
Lemma lem6923599 : term353 = term299.
Proof. exact (@lem6923549 (@lem6923598)). Qed.
Lemma lem6923600 : term352 = term299.
Proof. exact (TRANS (@lem6923515) (@lem6923599)). Qed.
Lemma lem6923602 (x : real) : (term318 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6923603 : term299 = term217.
Proof. exact (@lem6923602 term217). Qed.
Lemma lem6923604 : term352 = term217.
Proof. exact (TRANS (@lem6923600) (@lem6923603)). Qed.
Lemma lem6923605 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923606 : term371 = term366.
Proof. exact (MK_COMB (@lem6923605) (@lem6923604)). Qed.
Lemma lem6923607 (_92392 : int) : (real_of_int _92392) = (real_of_int _92392).
Proof. exact (eq_refl (real_of_int _92392)). Qed.
Lemma lem6923608 (_92392 : int) : (term349 _92392) = (term372 _92392).
Proof. exact (MK_COMB (@lem6923606) (@lem6923607 _92392)). Qed.
Lemma lem6923609 (_92392 : int) : (term348 _92392) = (term372 _92392).
Proof. exact (TRANS (@lem6923506 _92392) (@lem6923608 _92392)). Qed.
Lemma lem6923610 (_92392 : int) : (term372 _92392) = term217.
Proof. exact (@lem1982719 (real_of_int _92392)). Qed.
Lemma lem6923611 (_92392 : int) : (term348 _92392) = term217.
Proof. exact (TRANS (@lem6923609 _92392) (@lem6923610 _92392)). Qed.
Lemma lem6923612 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923613 (_92392 : int) : (term373 _92392) = term374.
Proof. exact (MK_COMB (@lem6923612) (@lem6923611 _92392)). Qed.
Lemma lem6923614 (_92393 : int) (_92394 : int) : (term345 _92393 _92394) = (term346 _92393 _92394).
Proof. exact (@lem1982753 (real_of_int _92393) (term347 _92393) (real_of_int _92394) (term343 _92394)). Qed.
Lemma lem6923615 (_92393 : int) : (term348 _92393) = (term349 _92393).
Proof. exact (@lem1982715 term302 (real_of_int _92393)). Qed.
Lemma lem6923617 (x : nat) : (real_of_num x) = (term298 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6923618 : term236 = term333.
Proof. exact (@lem6923617 term237). Qed.
Lemma lem6923620 (x : nat) : (term300 x) = (term301 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6923621 : term302 = term303.
Proof. exact (@lem6923620 term237). Qed.
Lemma lem6923622 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923623 : term350 = term351.
Proof. exact (MK_COMB (@lem6923622) (@lem6923621)). Qed.
Lemma lem6923624 : term352 = term353.
Proof. exact (MK_COMB (@lem6923623) (@lem6923618)). Qed.
Lemma lem6923625 : term354.
Proof. exact (@lem1981473 term302 term236 term236 term236 term217 term236). Qed.
Lemma lem6923627 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923628 : term356 = term357.
Proof. exact (@lem6923627 (NUMERAL 0) term237). Qed.
Lemma lem6923629 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923630 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923631 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923630 h1) (fun h1 : term357 = True => @lem6923629)). Qed.
Lemma lem6923632 : term357 = True.
Proof. exact (EQ_MP (@lem6923631) (@lem6923629)). Qed.
Lemma lem6923633 : term356 = True.
Proof. exact (TRANS (@lem6923628) (@lem6923632)). Qed.
Lemma lem6923634 : True = term356.
Proof. exact (SYM (@lem6923633)). Qed.
Lemma lem6923635 : term356.
Proof. exact (EQ_MP (@lem6923634) (@lem0)). Qed.
Lemma lem6923636 : term359.
Proof. exact (@lem6923625 (@lem6923635)). Qed.
Lemma lem6923638 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923639 : term356 = term357.
Proof. exact (@lem6923638 (NUMERAL 0) term237). Qed.
Lemma lem6923640 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923641 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923642 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923641 h1) (fun h1 : term357 = True => @lem6923640)). Qed.
Lemma lem6923643 : term357 = True.
Proof. exact (EQ_MP (@lem6923642) (@lem6923640)). Qed.
Lemma lem6923644 : term356 = True.
Proof. exact (TRANS (@lem6923639) (@lem6923643)). Qed.
Lemma lem6923645 : True = term356.
Proof. exact (SYM (@lem6923644)). Qed.
Lemma lem6923646 : term356.
Proof. exact (EQ_MP (@lem6923645) (@lem0)). Qed.
Lemma lem6923647 : term360.
Proof. exact (@lem6923636 (@lem6923646)). Qed.
Lemma lem6923649 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923650 : term356 = term357.
Proof. exact (@lem6923649 (NUMERAL 0) term237). Qed.
Lemma lem6923651 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923652 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923653 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923652 h1) (fun h1 : term357 = True => @lem6923651)). Qed.
Lemma lem6923654 : term357 = True.
Proof. exact (EQ_MP (@lem6923653) (@lem6923651)). Qed.
Lemma lem6923655 : term356 = True.
Proof. exact (TRANS (@lem6923650) (@lem6923654)). Qed.
Lemma lem6923656 : True = term356.
Proof. exact (SYM (@lem6923655)). Qed.
Lemma lem6923657 : term356.
Proof. exact (EQ_MP (@lem6923656) (@lem0)). Qed.
Lemma lem6923658 : term361.
Proof. exact (@lem6923647 (@lem6923657)). Qed.
Lemma lem6923660 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923661 : term311 = term312.
Proof. exact (@lem6923660 term237 term237). Qed.
Lemma lem6923662 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923663 : term314 = term237.
Proof. exact (EQ_MP (@lem6923662) (@lem940073)). Qed.
Lemma lem6923664 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923665 : term312 = term236.
Proof. exact (MK_COMB (@lem6923664) (@lem6923663)). Qed.
Lemma lem6923666 : term311 = term236.
Proof. exact (TRANS (@lem6923661) (@lem6923665)). Qed.
Lemma lem6923668 (m : nat) (n : nat) : (term337 m n) = (term338 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6923669 : term334 = term339.
Proof. exact (@lem6923668 term237 term237). Qed.
Lemma lem6923670 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923671 : term314 = term237.
Proof. exact (EQ_MP (@lem6923670) (@lem940073)). Qed.
Lemma lem6923672 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923673 : term312 = term236.
Proof. exact (MK_COMB (@lem6923672) (@lem6923671)). Qed.
Lemma lem6923674 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6923675 : term339 = term302.
Proof. exact (MK_COMB (@lem6923674) (@lem6923673)). Qed.
Lemma lem6923676 : term334 = term302.
Proof. exact (TRANS (@lem6923669) (@lem6923675)). Qed.
Lemma lem6923677 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923678 : term362 = term350.
Proof. exact (MK_COMB (@lem6923677) (@lem6923676)). Qed.
Lemma lem6923679 : term363 = term352.
Proof. exact (MK_COMB (@lem6923678) (@lem6923666)). Qed.
Lemma lem6923681 (m : nat) : (term364 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6923682 : term352 = term217.
Proof. exact (@lem6923681 term237). Qed.
Lemma lem6923683 : term363 = term217.
Proof. exact (TRANS (@lem6923679) (@lem6923682)). Qed.
Lemma lem6923684 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923685 : term365 = term366.
Proof. exact (MK_COMB (@lem6923684) (@lem6923683)). Qed.
Lemma lem6923686 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem6923687 : term367 = term368.
Proof. exact (MK_COMB (@lem6923685) (@lem6923686)). Qed.
Lemma lem6923689 (x : nat) : (term369 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6923690 : term368 = term217.
Proof. exact (@lem6923689 term237). Qed.
Lemma lem6923691 : term367 = term217.
Proof. exact (TRANS (@lem6923687) (@lem6923690)). Qed.
Lemma lem6923693 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923694 : term311 = term312.
Proof. exact (@lem6923693 term237 term237). Qed.
Lemma lem6923695 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923696 : term314 = term237.
Proof. exact (EQ_MP (@lem6923695) (@lem940073)). Qed.
Lemma lem6923697 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923698 : term312 = term236.
Proof. exact (MK_COMB (@lem6923697) (@lem6923696)). Qed.
Lemma lem6923699 : term311 = term236.
Proof. exact (TRANS (@lem6923694) (@lem6923698)). Qed.
Lemma lem6923700 : term366 = term366.
Proof. exact (eq_refl term366). Qed.
Lemma lem6923701 : term370 = term368.
Proof. exact (MK_COMB (@lem6923700) (@lem6923699)). Qed.
Lemma lem6923703 (x : nat) : (term369 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6923704 : term368 = term217.
Proof. exact (@lem6923703 term237). Qed.
Lemma lem6923705 : term370 = term217.
Proof. exact (TRANS (@lem6923701) (@lem6923704)). Qed.
Lemma lem6923706 : term217 = term370.
Proof. exact (SYM (@lem6923705)). Qed.
Lemma lem6923707 : term367 = term370.
Proof. exact (TRANS (@lem6923691) (@lem6923706)). Qed.
Lemma lem6923708 : term353 = term299.
Proof. exact (@lem6923658 (@lem6923707)). Qed.
Lemma lem6923709 : term352 = term299.
Proof. exact (TRANS (@lem6923624) (@lem6923708)). Qed.
Lemma lem6923711 (x : real) : (term318 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6923712 : term299 = term217.
Proof. exact (@lem6923711 term217). Qed.
Lemma lem6923713 : term352 = term217.
Proof. exact (TRANS (@lem6923709) (@lem6923712)). Qed.
Lemma lem6923714 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923715 : term371 = term366.
Proof. exact (MK_COMB (@lem6923714) (@lem6923713)). Qed.
Lemma lem6923716 (_92393 : int) : (real_of_int _92393) = (real_of_int _92393).
Proof. exact (eq_refl (real_of_int _92393)). Qed.
Lemma lem6923717 (_92393 : int) : (term349 _92393) = (term372 _92393).
Proof. exact (MK_COMB (@lem6923715) (@lem6923716 _92393)). Qed.
Lemma lem6923718 (_92393 : int) : (term348 _92393) = (term372 _92393).
Proof. exact (TRANS (@lem6923615 _92393) (@lem6923717 _92393)). Qed.
Lemma lem6923719 (_92393 : int) : (term372 _92393) = term217.
Proof. exact (@lem1982719 (real_of_int _92393)). Qed.
Lemma lem6923720 (_92393 : int) : (term348 _92393) = term217.
Proof. exact (TRANS (@lem6923718 _92393) (@lem6923719 _92393)). Qed.
Lemma lem6923721 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923722 (_92393 : int) : (term373 _92393) = term374.
Proof. exact (MK_COMB (@lem6923721) (@lem6923720 _92393)). Qed.
Lemma lem6923723 (_92394 : int) : (term375 _92394) = (term376 _92394).
Proof. exact (@lem1982763 (real_of_int _92394) (term347 _92394) term302). Qed.
Lemma lem6923724 (_92394 : int) : (term348 _92394) = (term349 _92394).
Proof. exact (@lem1982715 term302 (real_of_int _92394)). Qed.
Lemma lem6923726 (x : nat) : (real_of_num x) = (term298 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6923727 : term236 = term333.
Proof. exact (@lem6923726 term237). Qed.
Lemma lem6923729 (x : nat) : (term300 x) = (term301 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6923730 : term302 = term303.
Proof. exact (@lem6923729 term237). Qed.
Lemma lem6923731 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923732 : term350 = term351.
Proof. exact (MK_COMB (@lem6923731) (@lem6923730)). Qed.
Lemma lem6923733 : term352 = term353.
Proof. exact (MK_COMB (@lem6923732) (@lem6923727)). Qed.
Lemma lem6923734 : term354.
Proof. exact (@lem1981473 term302 term236 term236 term236 term217 term236). Qed.
Lemma lem6923736 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923737 : term356 = term357.
Proof. exact (@lem6923736 (NUMERAL 0) term237). Qed.
Lemma lem6923738 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923739 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923740 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923739 h1) (fun h1 : term357 = True => @lem6923738)). Qed.
Lemma lem6923741 : term357 = True.
Proof. exact (EQ_MP (@lem6923740) (@lem6923738)). Qed.
Lemma lem6923742 : term356 = True.
Proof. exact (TRANS (@lem6923737) (@lem6923741)). Qed.
Lemma lem6923743 : True = term356.
Proof. exact (SYM (@lem6923742)). Qed.
Lemma lem6923744 : term356.
Proof. exact (EQ_MP (@lem6923743) (@lem0)). Qed.
Lemma lem6923745 : term359.
Proof. exact (@lem6923734 (@lem6923744)). Qed.
Lemma lem6923747 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923748 : term356 = term357.
Proof. exact (@lem6923747 (NUMERAL 0) term237). Qed.
Lemma lem6923749 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923750 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923751 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923750 h1) (fun h1 : term357 = True => @lem6923749)). Qed.
Lemma lem6923752 : term357 = True.
Proof. exact (EQ_MP (@lem6923751) (@lem6923749)). Qed.
Lemma lem6923753 : term356 = True.
Proof. exact (TRANS (@lem6923748) (@lem6923752)). Qed.
Lemma lem6923754 : True = term356.
Proof. exact (SYM (@lem6923753)). Qed.
Lemma lem6923755 : term356.
Proof. exact (EQ_MP (@lem6923754) (@lem0)). Qed.
Lemma lem6923756 : term360.
Proof. exact (@lem6923745 (@lem6923755)). Qed.
Lemma lem6923758 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923759 : term356 = term357.
Proof. exact (@lem6923758 (NUMERAL 0) term237). Qed.
Lemma lem6923760 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923761 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923762 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923761 h1) (fun h1 : term357 = True => @lem6923760)). Qed.
Lemma lem6923763 : term357 = True.
Proof. exact (EQ_MP (@lem6923762) (@lem6923760)). Qed.
Lemma lem6923764 : term356 = True.
Proof. exact (TRANS (@lem6923759) (@lem6923763)). Qed.
Lemma lem6923765 : True = term356.
Proof. exact (SYM (@lem6923764)). Qed.
Lemma lem6923766 : term356.
Proof. exact (EQ_MP (@lem6923765) (@lem0)). Qed.
Lemma lem6923767 : term361.
Proof. exact (@lem6923756 (@lem6923766)). Qed.
Lemma lem6923769 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923770 : term311 = term312.
Proof. exact (@lem6923769 term237 term237). Qed.
Lemma lem6923771 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923772 : term314 = term237.
Proof. exact (EQ_MP (@lem6923771) (@lem940073)). Qed.
Lemma lem6923773 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923774 : term312 = term236.
Proof. exact (MK_COMB (@lem6923773) (@lem6923772)). Qed.
Lemma lem6923775 : term311 = term236.
Proof. exact (TRANS (@lem6923770) (@lem6923774)). Qed.
Lemma lem6923777 (m : nat) (n : nat) : (term337 m n) = (term338 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6923778 : term334 = term339.
Proof. exact (@lem6923777 term237 term237). Qed.
Lemma lem6923779 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923780 : term314 = term237.
Proof. exact (EQ_MP (@lem6923779) (@lem940073)). Qed.
Lemma lem6923781 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923782 : term312 = term236.
Proof. exact (MK_COMB (@lem6923781) (@lem6923780)). Qed.
Lemma lem6923783 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6923784 : term339 = term302.
Proof. exact (MK_COMB (@lem6923783) (@lem6923782)). Qed.
Lemma lem6923785 : term334 = term302.
Proof. exact (TRANS (@lem6923778) (@lem6923784)). Qed.
Lemma lem6923786 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923787 : term362 = term350.
Proof. exact (MK_COMB (@lem6923786) (@lem6923785)). Qed.
Lemma lem6923788 : term363 = term352.
Proof. exact (MK_COMB (@lem6923787) (@lem6923775)). Qed.
Lemma lem6923790 (m : nat) : (term364 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6923791 : term352 = term217.
Proof. exact (@lem6923790 term237). Qed.
Lemma lem6923792 : term363 = term217.
Proof. exact (TRANS (@lem6923788) (@lem6923791)). Qed.
Lemma lem6923793 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923794 : term365 = term366.
Proof. exact (MK_COMB (@lem6923793) (@lem6923792)). Qed.
Lemma lem6923795 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem6923796 : term367 = term368.
Proof. exact (MK_COMB (@lem6923794) (@lem6923795)). Qed.
Lemma lem6923798 (x : nat) : (term369 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6923799 : term368 = term217.
Proof. exact (@lem6923798 term237). Qed.
Lemma lem6923800 : term367 = term217.
Proof. exact (TRANS (@lem6923796) (@lem6923799)). Qed.
Lemma lem6923802 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923803 : term311 = term312.
Proof. exact (@lem6923802 term237 term237). Qed.
Lemma lem6923804 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923805 : term314 = term237.
Proof. exact (EQ_MP (@lem6923804) (@lem940073)). Qed.
Lemma lem6923806 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923807 : term312 = term236.
Proof. exact (MK_COMB (@lem6923806) (@lem6923805)). Qed.
Lemma lem6923808 : term311 = term236.
Proof. exact (TRANS (@lem6923803) (@lem6923807)). Qed.
Lemma lem6923809 : term366 = term366.
Proof. exact (eq_refl term366). Qed.
Lemma lem6923810 : term370 = term368.
Proof. exact (MK_COMB (@lem6923809) (@lem6923808)). Qed.
Lemma lem6923812 (x : nat) : (term369 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6923813 : term368 = term217.
Proof. exact (@lem6923812 term237). Qed.
Lemma lem6923814 : term370 = term217.
Proof. exact (TRANS (@lem6923810) (@lem6923813)). Qed.
Lemma lem6923815 : term217 = term370.
Proof. exact (SYM (@lem6923814)). Qed.
Lemma lem6923816 : term367 = term370.
Proof. exact (TRANS (@lem6923800) (@lem6923815)). Qed.
Lemma lem6923817 : term353 = term299.
Proof. exact (@lem6923767 (@lem6923816)). Qed.
Lemma lem6923818 : term352 = term299.
Proof. exact (TRANS (@lem6923733) (@lem6923817)). Qed.
Lemma lem6923820 (x : real) : (term318 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6923821 : term299 = term217.
Proof. exact (@lem6923820 term217). Qed.
Lemma lem6923822 : term352 = term217.
Proof. exact (TRANS (@lem6923818) (@lem6923821)). Qed.
Lemma lem6923823 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923824 : term371 = term366.
Proof. exact (MK_COMB (@lem6923823) (@lem6923822)). Qed.
Lemma lem6923825 (_92394 : int) : (real_of_int _92394) = (real_of_int _92394).
Proof. exact (eq_refl (real_of_int _92394)). Qed.
Lemma lem6923826 (_92394 : int) : (term349 _92394) = (term372 _92394).
Proof. exact (MK_COMB (@lem6923824) (@lem6923825 _92394)). Qed.
Lemma lem6923827 (_92394 : int) : (term348 _92394) = (term372 _92394).
Proof. exact (TRANS (@lem6923724 _92394) (@lem6923826 _92394)). Qed.
Lemma lem6923828 (_92394 : int) : (term372 _92394) = term217.
Proof. exact (@lem1982719 (real_of_int _92394)). Qed.
Lemma lem6923829 (_92394 : int) : (term348 _92394) = term217.
Proof. exact (TRANS (@lem6923827 _92394) (@lem6923828 _92394)). Qed.
Lemma lem6923830 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923831 (_92394 : int) : (term373 _92394) = term374.
Proof. exact (MK_COMB (@lem6923830) (@lem6923829 _92394)). Qed.
Lemma lem6923832 : term302 = term302.
Proof. exact (eq_refl term302). Qed.
Lemma lem6923833 (_92394 : int) : (term376 _92394) = term377.
Proof. exact (MK_COMB (@lem6923831 _92394) (@lem6923832)). Qed.
Lemma lem6923834 (_92394 : int) : (term375 _92394) = term377.
Proof. exact (TRANS (@lem6923723 _92394) (@lem6923833 _92394)). Qed.
Lemma lem6923835 : term377 = term302.
Proof. exact (@lem1982721 term302). Qed.
Lemma lem6923836 (_92394 : int) : (term375 _92394) = term302.
Proof. exact (TRANS (@lem6923834 _92394) (@lem6923835)). Qed.
Lemma lem6923837 (_92393 : int) (_92394 : int) : (term346 _92393 _92394) = term377.
Proof. exact (MK_COMB (@lem6923722 _92393) (@lem6923836 _92394)). Qed.
Lemma lem6923838 (_92393 : int) (_92394 : int) : (term345 _92393 _92394) = term377.
Proof. exact (TRANS (@lem6923614 _92393 _92394) (@lem6923837 _92393 _92394)). Qed.
Lemma lem6923839 : term377 = term302.
Proof. exact (@lem1982721 term302). Qed.
Lemma lem6923840 (_92393 : int) (_92394 : int) : (term345 _92393 _92394) = term302.
Proof. exact (TRANS (@lem6923838 _92393 _92394) (@lem6923839)). Qed.
Lemma lem6923841 (_92392 : int) (_92393 : int) (_92394 : int) : (term392 _92392 _92393 _92394) = term377.
Proof. exact (MK_COMB (@lem6923613 _92392) (@lem6923840 _92393 _92394)). Qed.
Lemma lem6923842 (_92392 : int) (_92393 : int) (_92394 : int) : (term391 _92392 _92393 _92394) = term377.
Proof. exact (TRANS (@lem6923505 _92392 _92393 _92394) (@lem6923841 _92392 _92393 _92394)). Qed.
Lemma lem6923843 : term377 = term302.
Proof. exact (@lem1982721 term302). Qed.
Lemma lem6923844 (_92392 : int) (_92393 : int) (_92394 : int) : (term391 _92392 _92393 _92394) = term302.
Proof. exact (TRANS (@lem6923842 _92392 _92393 _92394) (@lem6923843)). Qed.
Lemma lem6923845 (_92392 : int) (_92393 : int) (_92394 : int) : (term387 _92392 _92393 _92394) = term302.
Proof. exact (TRANS (@lem6923504 _92392 _92393 _92394) (@lem6923844 _92392 _92393 _92394)). Qed.
Lemma lem6923846 (_92392 : int) (_92393 : int) (_92394 : int) : (term386 _92392 _92393 _92394) = term302.
Proof. exact (TRANS (@lem6923447 _92392 _92393 _92394) (@lem6923845 _92392 _92393 _92394)). Qed.
Lemma lem6923847 (_92392 : int) (_92393 : int) (_92394 : int) : (term385 _92392 _92393 _92394) = term302.
Proof. exact (TRANS (@lem6923446 _92392 _92393 _92394) (@lem6923846 _92392 _92393 _92394)). Qed.
Lemma lem6923848 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6923849 (_92392 : int) (_92393 : int) (_92394 : int) : (term393 _92392 _92393 _92394) = term379.
Proof. exact (MK_COMB (@lem6923848) (@lem6923847 _92392 _92393 _92394)). Qed.
Lemma lem6923850 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem6923851 (_92392 : int) (_92393 : int) (_92394 : int) : (term381 _92392 _92393 _92394) = term380.
Proof. exact (MK_COMB (@lem6923849 _92392 _92393 _92394) (@lem6923850)). Qed.
Lemma lem6923852 (_92392 : int) (_92393 : int) (_92394 : int) : (term261 _92392 _92393 _92394) = term380.
Proof. exact (TRANS (@lem6923403 _92392 _92393 _92394) (@lem6923851 _92392 _92393 _92394)). Qed.
Lemma lem6923853 (_92392 : int) : (term275 _92392) = (term394 _92392).
Proof. exact (@lem1988287 (real_of_int _92392) (term272 _92392)). Qed.
Lemma lem6923865 (_92392 : int) : (term395 _92392) = (term396 _92392).
Proof. exact (@lem1982792 (real_of_int _92392) (term272 _92392)). Qed.
Lemma lem6923866 (_92392 : int) : (term331 _92392) = (term332 _92392).
Proof. exact (@lem1982781 (real_of_int _92392) term302 term236). Qed.
Lemma lem6923868 (x : nat) : (real_of_num x) = (term298 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6923869 : term236 = term333.
Proof. exact (@lem6923868 term237). Qed.
Lemma lem6923871 (x : nat) : (term300 x) = (term301 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6923872 : term302 = term303.
Proof. exact (@lem6923871 term237). Qed.
Lemma lem6923873 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923874 : term304 = term305.
Proof. exact (MK_COMB (@lem6923873) (@lem6923872)). Qed.
Lemma lem6923875 : term334 = term335.
Proof. exact (MK_COMB (@lem6923874) (@lem6923869)). Qed.
Lemma lem6923876 : term335 = term336.
Proof. exact (@lem1981613 term302 term236 term236 term236). Qed.
Lemma lem6923878 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923879 : term311 = term312.
Proof. exact (@lem6923878 term237 term237). Qed.
Lemma lem6923880 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923881 : term314 = term237.
Proof. exact (EQ_MP (@lem6923880) (@lem940073)). Qed.
Lemma lem6923882 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923883 : term312 = term236.
Proof. exact (MK_COMB (@lem6923882) (@lem6923881)). Qed.
Lemma lem6923884 : term311 = term236.
Proof. exact (TRANS (@lem6923879) (@lem6923883)). Qed.
Lemma lem6923886 (m : nat) (n : nat) : (term337 m n) = (term338 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6923887 : term334 = term339.
Proof. exact (@lem6923886 term237 term237). Qed.
Lemma lem6923888 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923889 : term314 = term237.
Proof. exact (EQ_MP (@lem6923888) (@lem940073)). Qed.
Lemma lem6923890 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923891 : term312 = term236.
Proof. exact (MK_COMB (@lem6923890) (@lem6923889)). Qed.
Lemma lem6923892 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6923893 : term339 = term302.
Proof. exact (MK_COMB (@lem6923892) (@lem6923891)). Qed.
Lemma lem6923894 : term334 = term302.
Proof. exact (TRANS (@lem6923887) (@lem6923893)). Qed.
Lemma lem6923895 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6923896 : term340 = term341.
Proof. exact (MK_COMB (@lem6923895) (@lem6923894)). Qed.
Lemma lem6923897 : term336 = term303.
Proof. exact (MK_COMB (@lem6923896) (@lem6923884)). Qed.
Lemma lem6923898 : term335 = term303.
Proof. exact (TRANS (@lem6923876) (@lem6923897)). Qed.
Lemma lem6923899 : term334 = term303.
Proof. exact (TRANS (@lem6923875) (@lem6923898)). Qed.
Lemma lem6923901 (x : real) : (term318 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6923902 : term303 = term302.
Proof. exact (@lem6923901 term302). Qed.
Lemma lem6923903 : term334 = term302.
Proof. exact (TRANS (@lem6923899) (@lem6923902)). Qed.
Lemma lem6923906 (_92392 : int) : (term342 _92392) = (term342 _92392).
Proof. exact (eq_refl (term342 _92392)). Qed.
Lemma lem6923907 (_92392 : int) : (term332 _92392) = (term343 _92392).
Proof. exact (MK_COMB (@lem6923906 _92392) (@lem6923903)). Qed.
Lemma lem6923908 (_92392 : int) : (term331 _92392) = (term343 _92392).
Proof. exact (TRANS (@lem6923866 _92392) (@lem6923907 _92392)). Qed.
Lemma lem6923909 (_92392 : int) : (term254 _92392) = (term254 _92392).
Proof. exact (eq_refl (term254 _92392)). Qed.
Lemma lem6923910 (_92392 : int) : (term396 _92392) = (term375 _92392).
Proof. exact (MK_COMB (@lem6923909 _92392) (@lem6923908 _92392)). Qed.
Lemma lem6923911 (_92392 : int) : (term375 _92392) = (term376 _92392).
Proof. exact (@lem1982763 (real_of_int _92392) (term347 _92392) term302). Qed.
Lemma lem6923912 (_92392 : int) : (term348 _92392) = (term349 _92392).
Proof. exact (@lem1982715 term302 (real_of_int _92392)). Qed.
Lemma lem6923914 (x : nat) : (real_of_num x) = (term298 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6923915 : term236 = term333.
Proof. exact (@lem6923914 term237). Qed.
Lemma lem6923917 (x : nat) : (term300 x) = (term301 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6923918 : term302 = term303.
Proof. exact (@lem6923917 term237). Qed.
Lemma lem6923919 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923920 : term350 = term351.
Proof. exact (MK_COMB (@lem6923919) (@lem6923918)). Qed.
Lemma lem6923921 : term352 = term353.
Proof. exact (MK_COMB (@lem6923920) (@lem6923915)). Qed.
Lemma lem6923922 : term354.
Proof. exact (@lem1981473 term302 term236 term236 term236 term217 term236). Qed.
Lemma lem6923924 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923925 : term356 = term357.
Proof. exact (@lem6923924 (NUMERAL 0) term237). Qed.
Lemma lem6923926 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923927 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923928 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923927 h1) (fun h1 : term357 = True => @lem6923926)). Qed.
Lemma lem6923929 : term357 = True.
Proof. exact (EQ_MP (@lem6923928) (@lem6923926)). Qed.
Lemma lem6923930 : term356 = True.
Proof. exact (TRANS (@lem6923925) (@lem6923929)). Qed.
Lemma lem6923931 : True = term356.
Proof. exact (SYM (@lem6923930)). Qed.
Lemma lem6923932 : term356.
Proof. exact (EQ_MP (@lem6923931) (@lem0)). Qed.
Lemma lem6923933 : term359.
Proof. exact (@lem6923922 (@lem6923932)). Qed.
Lemma lem6923935 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923936 : term356 = term357.
Proof. exact (@lem6923935 (NUMERAL 0) term237). Qed.
Lemma lem6923937 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923938 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923939 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923938 h1) (fun h1 : term357 = True => @lem6923937)). Qed.
Lemma lem6923940 : term357 = True.
Proof. exact (EQ_MP (@lem6923939) (@lem6923937)). Qed.
Lemma lem6923941 : term356 = True.
Proof. exact (TRANS (@lem6923936) (@lem6923940)). Qed.
Lemma lem6923942 : True = term356.
Proof. exact (SYM (@lem6923941)). Qed.
Lemma lem6923943 : term356.
Proof. exact (EQ_MP (@lem6923942) (@lem0)). Qed.
Lemma lem6923944 : term360.
Proof. exact (@lem6923933 (@lem6923943)). Qed.
Lemma lem6923946 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6923947 : term356 = term357.
Proof. exact (@lem6923946 (NUMERAL 0) term237). Qed.
Lemma lem6923948 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6923949 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6923950 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6923949 h1) (fun h1 : term357 = True => @lem6923948)). Qed.
Lemma lem6923951 : term357 = True.
Proof. exact (EQ_MP (@lem6923950) (@lem6923948)). Qed.
Lemma lem6923952 : term356 = True.
Proof. exact (TRANS (@lem6923947) (@lem6923951)). Qed.
Lemma lem6923953 : True = term356.
Proof. exact (SYM (@lem6923952)). Qed.
Lemma lem6923954 : term356.
Proof. exact (EQ_MP (@lem6923953) (@lem0)). Qed.
Lemma lem6923955 : term361.
Proof. exact (@lem6923944 (@lem6923954)). Qed.
Lemma lem6923957 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923958 : term311 = term312.
Proof. exact (@lem6923957 term237 term237). Qed.
Lemma lem6923959 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923960 : term314 = term237.
Proof. exact (EQ_MP (@lem6923959) (@lem940073)). Qed.
Lemma lem6923961 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923962 : term312 = term236.
Proof. exact (MK_COMB (@lem6923961) (@lem6923960)). Qed.
Lemma lem6923963 : term311 = term236.
Proof. exact (TRANS (@lem6923958) (@lem6923962)). Qed.
Lemma lem6923965 (m : nat) (n : nat) : (term337 m n) = (term338 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6923966 : term334 = term339.
Proof. exact (@lem6923965 term237 term237). Qed.
Lemma lem6923967 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923968 : term314 = term237.
Proof. exact (EQ_MP (@lem6923967) (@lem940073)). Qed.
Lemma lem6923969 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923970 : term312 = term236.
Proof. exact (MK_COMB (@lem6923969) (@lem6923968)). Qed.
Lemma lem6923971 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6923972 : term339 = term302.
Proof. exact (MK_COMB (@lem6923971) (@lem6923970)). Qed.
Lemma lem6923973 : term334 = term302.
Proof. exact (TRANS (@lem6923966) (@lem6923972)). Qed.
Lemma lem6923974 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6923975 : term362 = term350.
Proof. exact (MK_COMB (@lem6923974) (@lem6923973)). Qed.
Lemma lem6923976 : term363 = term352.
Proof. exact (MK_COMB (@lem6923975) (@lem6923963)). Qed.
Lemma lem6923978 (m : nat) : (term364 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6923979 : term352 = term217.
Proof. exact (@lem6923978 term237). Qed.
Lemma lem6923980 : term363 = term217.
Proof. exact (TRANS (@lem6923976) (@lem6923979)). Qed.
Lemma lem6923981 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6923982 : term365 = term366.
Proof. exact (MK_COMB (@lem6923981) (@lem6923980)). Qed.
Lemma lem6923983 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem6923984 : term367 = term368.
Proof. exact (MK_COMB (@lem6923982) (@lem6923983)). Qed.
Lemma lem6923986 (x : nat) : (term369 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6923987 : term368 = term217.
Proof. exact (@lem6923986 term237). Qed.
Lemma lem6923988 : term367 = term217.
Proof. exact (TRANS (@lem6923984) (@lem6923987)). Qed.
Lemma lem6923990 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6923991 : term311 = term312.
Proof. exact (@lem6923990 term237 term237). Qed.
Lemma lem6923992 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6923993 : term314 = term237.
Proof. exact (EQ_MP (@lem6923992) (@lem940073)). Qed.
Lemma lem6923994 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6923995 : term312 = term236.
Proof. exact (MK_COMB (@lem6923994) (@lem6923993)). Qed.
Lemma lem6923996 : term311 = term236.
Proof. exact (TRANS (@lem6923991) (@lem6923995)). Qed.
Lemma lem6923997 : term366 = term366.
Proof. exact (eq_refl term366). Qed.
Lemma lem6923998 : term370 = term368.
Proof. exact (MK_COMB (@lem6923997) (@lem6923996)). Qed.
Lemma lem6924000 (x : nat) : (term369 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6924001 : term368 = term217.
Proof. exact (@lem6924000 term237). Qed.
Lemma lem6924002 : term370 = term217.
Proof. exact (TRANS (@lem6923998) (@lem6924001)). Qed.
Lemma lem6924003 : term217 = term370.
Proof. exact (SYM (@lem6924002)). Qed.
Lemma lem6924004 : term367 = term370.
Proof. exact (TRANS (@lem6923988) (@lem6924003)). Qed.
Lemma lem6924005 : term353 = term299.
Proof. exact (@lem6923955 (@lem6924004)). Qed.
Lemma lem6924006 : term352 = term299.
Proof. exact (TRANS (@lem6923921) (@lem6924005)). Qed.
Lemma lem6924008 (x : real) : (term318 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6924009 : term299 = term217.
Proof. exact (@lem6924008 term217). Qed.
Lemma lem6924010 : term352 = term217.
Proof. exact (TRANS (@lem6924006) (@lem6924009)). Qed.
Lemma lem6924011 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6924012 : term371 = term366.
Proof. exact (MK_COMB (@lem6924011) (@lem6924010)). Qed.
Lemma lem6924013 (_92392 : int) : (real_of_int _92392) = (real_of_int _92392).
Proof. exact (eq_refl (real_of_int _92392)). Qed.
Lemma lem6924014 (_92392 : int) : (term349 _92392) = (term372 _92392).
Proof. exact (MK_COMB (@lem6924012) (@lem6924013 _92392)). Qed.
Lemma lem6924015 (_92392 : int) : (term348 _92392) = (term372 _92392).
Proof. exact (TRANS (@lem6923912 _92392) (@lem6924014 _92392)). Qed.
Lemma lem6924016 (_92392 : int) : (term372 _92392) = term217.
Proof. exact (@lem1982719 (real_of_int _92392)). Qed.
Lemma lem6924017 (_92392 : int) : (term348 _92392) = term217.
Proof. exact (TRANS (@lem6924015 _92392) (@lem6924016 _92392)). Qed.
Lemma lem6924018 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6924019 (_92392 : int) : (term373 _92392) = term374.
Proof. exact (MK_COMB (@lem6924018) (@lem6924017 _92392)). Qed.
Lemma lem6924020 : term302 = term302.
Proof. exact (eq_refl term302). Qed.
Lemma lem6924021 (_92392 : int) : (term376 _92392) = term377.
Proof. exact (MK_COMB (@lem6924019 _92392) (@lem6924020)). Qed.
Lemma lem6924022 (_92392 : int) : (term375 _92392) = term377.
Proof. exact (TRANS (@lem6923911 _92392) (@lem6924021 _92392)). Qed.
Lemma lem6924023 : term377 = term302.
Proof. exact (@lem1982721 term302). Qed.
Lemma lem6924024 (_92392 : int) : (term375 _92392) = term302.
Proof. exact (TRANS (@lem6924022 _92392) (@lem6924023)). Qed.
Lemma lem6924025 (_92392 : int) : (term396 _92392) = term302.
Proof. exact (TRANS (@lem6923910 _92392) (@lem6924024 _92392)). Qed.
Lemma lem6924027 (_92392 : int) : (term395 _92392) = term302.
Proof. exact (TRANS (@lem6923865 _92392) (@lem6924025 _92392)). Qed.
Lemma lem6924028 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6924029 (_92392 : int) : (term397 _92392) = term379.
Proof. exact (MK_COMB (@lem6924028) (@lem6924027 _92392)). Qed.
Lemma lem6924030 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem6924031 (_92392 : int) : (term394 _92392) = term380.
Proof. exact (MK_COMB (@lem6924029 _92392) (@lem6924030)). Qed.
Lemma lem6924032 (_92392 : int) : (term275 _92392) = term380.
Proof. exact (TRANS (@lem6923853 _92392) (@lem6924031 _92392)). Qed.
Lemma lem6924033 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6924034 (_92392 : int) (_92393 : int) (_92394 : int) : (term263 _92392 _92393 _92394) = term398.
Proof. exact (MK_COMB (@lem6924033) (@lem6923852 _92392 _92393 _92394)). Qed.
Lemma lem6924035 (_92393 : int) (_92394 : int) (_92392 : int) : (term290 _92393 _92394 _92392) = term399.
Proof. exact (MK_COMB (@lem6924034 _92392 _92393 _92394) (@lem6924032 _92392)). Qed.
Lemma lem6924036 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6924037 (_92392 : int) (_92393 : int) : (term243 _92392 _92393) = term398.
Proof. exact (MK_COMB (@lem6924036) (@lem6923402 _92392 _92393)). Qed.
Lemma lem6924038 (_92393 : int) (_92394 : int) (_92392 : int) : (term291 _92393 _92394 _92392) = term400.
Proof. exact (MK_COMB (@lem6924037 _92392 _92393) (@lem6924035 _92393 _92394 _92392)). Qed.
Lemma lem6924039 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6924040 (_92394 : int) : (term284 _92394) = (term401 _92394).
Proof. exact (MK_COMB (@lem6924039) (@lem6923087 _92394)). Qed.
Lemma lem6924041 (_92393 : int) (_92392 : int) (_92394 : int) : (term292 _92393 _92394 _92392) = (term402 _92394).
Proof. exact (MK_COMB (@lem6924040 _92394) (@lem6924038 _92393 _92394 _92392)). Qed.
Lemma lem6924042 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6924043 (_92393 : int) : (term284 _92393) = (term401 _92393).
Proof. exact (MK_COMB (@lem6924042) (@lem6923039 _92393)). Qed.
Lemma lem6924044 (_92392 : int) (_92393 : int) (_92394 : int) : (term293 _92393 _92394 _92392) = (term403 _92393 _92394).
Proof. exact (MK_COMB (@lem6924043 _92393) (@lem6924041 _92393 _92392 _92394)). Qed.
Lemma lem6924045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6924046 (_92392 : int) : (term284 _92392) = (term401 _92392).
Proof. exact (MK_COMB (@lem6924045) (@lem6922991 _92392)). Qed.
Lemma lem6924047 (_92392 : int) (_92393 : int) (_92394 : int) : (term294 _92393 _92394 _92392) = (term404 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6924046 _92392) (@lem6924044 _92392 _92393 _92394)). Qed.
Lemma lem6924054 (_92392 : int) (_92393 : int) (_92394 : int) : (term289 _92393 _92394 _92392) = (term404 _92392 _92393 _92394).
Proof. exact (TRANS (@lem6922943 _92393 _92394 _92392) (@lem6924047 _92392 _92393 _92394)). Qed.
Lemma lem6924068 (_92394 : int) : (term402 _92394) = (term405 _92394).
Proof. exact (@lem19158 term380 (term322 _92394) term399). Qed.
Lemma lem6924075 (_92394 : int) : (term406 _92394) = (term407 _92394).
Proof. exact (@lem19158 term380 (term322 _92394) term380). Qed.
Lemma lem6924078 (_92394 : int) : (term408 _92394) = (term408 _92394).
Proof. exact (eq_refl (term408 _92394)). Qed.
Lemma lem6924079 (_92394 : int) : (term405 _92394) = (term409 _92394).
Proof. exact (MK_COMB (@lem6924078 _92394) (@lem6924075 _92394)). Qed.
Lemma lem6924081 (_92394 : int) : (term402 _92394) = (term409 _92394).
Proof. exact (TRANS (@lem6924068 _92394) (@lem6924079 _92394)). Qed.
Lemma lem6924084 (_92393 : int) : (term401 _92393) = (term401 _92393).
Proof. exact (eq_refl (term401 _92393)). Qed.
Lemma lem6924085 (_92393 : int) (_92394 : int) : (term403 _92393 _92394) = (term410 _92393 _92394).
Proof. exact (MK_COMB (@lem6924084 _92393) (@lem6924081 _92394)). Qed.
Lemma lem6924086 (_92393 : int) (_92394 : int) : (term410 _92393 _92394) = (term411 _92393 _92394).
Proof. exact (@lem19158 (term412 _92394) (term322 _92393) (term407 _92394)). Qed.
Lemma lem6924093 (_92393 : int) (_92394 : int) : (term413 _92393 _92394) = (term414 _92393 _92394).
Proof. exact (@lem19158 (term412 _92394) (term322 _92393) (term412 _92394)). Qed.
Lemma lem6924096 (_92393 : int) (_92394 : int) : (term415 _92393 _92394) = (term415 _92393 _92394).
Proof. exact (eq_refl (term415 _92393 _92394)). Qed.
Lemma lem6924097 (_92393 : int) (_92394 : int) : (term411 _92393 _92394) = (term416 _92393 _92394).
Proof. exact (MK_COMB (@lem6924096 _92393 _92394) (@lem6924093 _92393 _92394)). Qed.
Lemma lem6924098 (_92393 : int) (_92394 : int) : (term410 _92393 _92394) = (term416 _92393 _92394).
Proof. exact (TRANS (@lem6924086 _92393 _92394) (@lem6924097 _92393 _92394)). Qed.
Lemma lem6924099 (_92393 : int) (_92394 : int) : (term403 _92393 _92394) = (term416 _92393 _92394).
Proof. exact (TRANS (@lem6924085 _92393 _92394) (@lem6924098 _92393 _92394)). Qed.
Lemma lem6924102 (_92392 : int) : (term401 _92392) = (term401 _92392).
Proof. exact (eq_refl (term401 _92392)). Qed.
Lemma lem6924103 (_92392 : int) (_92393 : int) (_92394 : int) : (term404 _92392 _92393 _92394) = (term417 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6924102 _92392) (@lem6924099 _92393 _92394)). Qed.
Lemma lem6924104 (_92392 : int) (_92393 : int) (_92394 : int) : (term417 _92392 _92393 _92394) = (term418 _92392 _92393 _92394).
Proof. exact (@lem19158 (term419 _92393 _92394) (term322 _92392) (term414 _92393 _92394)). Qed.
Lemma lem6924111 (_92392 : int) (_92393 : int) (_92394 : int) : (term420 _92392 _92393 _92394) = (term421 _92392 _92393 _92394).
Proof. exact (@lem19158 (term419 _92393 _92394) (term322 _92392) (term419 _92393 _92394)). Qed.
Lemma lem6924114 (_92392 : int) (_92393 : int) (_92394 : int) : (term422 _92392 _92393 _92394) = (term422 _92392 _92393 _92394).
Proof. exact (eq_refl (term422 _92392 _92393 _92394)). Qed.
Lemma lem6924115 (_92392 : int) (_92393 : int) (_92394 : int) : (term418 _92392 _92393 _92394) = (term423 _92392 _92393 _92394).
Proof. exact (MK_COMB (@lem6924114 _92392 _92393 _92394) (@lem6924111 _92392 _92393 _92394)). Qed.
Lemma lem6924116 (_92392 : int) (_92393 : int) (_92394 : int) : (term417 _92392 _92393 _92394) = (term423 _92392 _92393 _92394).
Proof. exact (TRANS (@lem6924104 _92392 _92393 _92394) (@lem6924115 _92392 _92393 _92394)). Qed.
Lemma lem6924117 (_92392 : int) (_92393 : int) (_92394 : int) : (term404 _92392 _92393 _92394) = (term423 _92392 _92393 _92394).
Proof. exact (TRANS (@lem6924103 _92392 _92393 _92394) (@lem6924116 _92392 _92393 _92394)). Qed.
Lemma lem6924118 (_92392 : int) (_92393 : int) (_92394 : int) : (term289 _92393 _92394 _92392) = (term423 _92392 _92393 _92394).
Proof. exact (TRANS (@lem6924054 _92392 _92393 _92394) (@lem6924117 _92392 _92393 _92394)). Qed.
Lemma lem6924134 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term423 _92392 _92393 _92394) : term423 _92392 _92393 _92394.
Proof. exact (h1). Qed.
Lemma lem6924135 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term424 _92392 _92393 _92394) : term424 _92392 _92393 _92394.
Proof. exact (h1). Qed.
Lemma lem6924136 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term424 _92392 _92393 _92394) : term419 _92393 _92394.
Proof. exact (proj2 (@lem6924135 _92392 _92393 _92394 h1)). Qed.
Lemma lem6924138 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term424 _92392 _92393 _92394) : term412 _92394.
Proof. exact (proj2 (@lem6924136 _92392 _92393 _92394 h1)). Qed.
Lemma lem6924140 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term424 _92392 _92393 _92394) : term380.
Proof. exact (proj2 (@lem6924138 _92392 _92393 _92394 h1)). Qed.
Lemma lem6924143 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6924144 : term380 = term425.
Proof. exact (@lem6924143 term217 term302). Qed.
Lemma lem6924146 (x : nat) : (term300 x) = (term301 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6924147 : term302 = term303.
Proof. exact (@lem6924146 term237). Qed.
Lemma lem6924149 (x : nat) : (real_of_num x) = (term298 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6924150 : term217 = term299.
Proof. exact (@lem6924149 (NUMERAL 0)). Qed.
Lemma lem6924151 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6924152 : term219 = term426.
Proof. exact (MK_COMB (@lem6924151) (@lem6924150)). Qed.
Lemma lem6924153 : term425 = term427.
Proof. exact (MK_COMB (@lem6924152) (@lem6924147)). Qed.
Lemma lem6924154 : term428.
Proof. exact (@lem1980026 term217 term236 term302 term236). Qed.
Lemma lem6924156 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6924157 : term356 = term357.
Proof. exact (@lem6924156 (NUMERAL 0) term237). Qed.
Lemma lem6924158 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6924159 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6924160 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6924159 h1) (fun h1 : term357 = True => @lem6924158)). Qed.
Lemma lem6924161 : term357 = True.
Proof. exact (EQ_MP (@lem6924160) (@lem6924158)). Qed.
Lemma lem6924162 : term356 = True.
Proof. exact (TRANS (@lem6924157) (@lem6924161)). Qed.
Lemma lem6924163 : True = term356.
Proof. exact (SYM (@lem6924162)). Qed.
Lemma lem6924164 : term356.
Proof. exact (EQ_MP (@lem6924163) (@lem0)). Qed.
Lemma lem6924165 : term429.
Proof. exact (@lem6924154 (@lem6924164)). Qed.
Lemma lem6924167 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6924168 : term356 = term357.
Proof. exact (@lem6924167 (NUMERAL 0) term237). Qed.
Lemma lem6924169 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6924170 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6924171 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6924170 h1) (fun h1 : term357 = True => @lem6924169)). Qed.
Lemma lem6924172 : term357 = True.
Proof. exact (EQ_MP (@lem6924171) (@lem6924169)). Qed.
Lemma lem6924173 : term356 = True.
Proof. exact (TRANS (@lem6924168) (@lem6924172)). Qed.
Lemma lem6924174 : True = term356.
Proof. exact (SYM (@lem6924173)). Qed.
Lemma lem6924175 : term356.
Proof. exact (EQ_MP (@lem6924174) (@lem0)). Qed.
Lemma lem6924176 : term427 = term430.
Proof. exact (@lem6924165 (@lem6924175)). Qed.
Lemma lem6924178 (m : nat) (n : nat) : (term337 m n) = (term338 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6924179 : term334 = term339.
Proof. exact (@lem6924178 term237 term237). Qed.
Lemma lem6924180 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6924181 : term314 = term237.
Proof. exact (EQ_MP (@lem6924180) (@lem940073)). Qed.
Lemma lem6924182 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6924183 : term312 = term236.
Proof. exact (MK_COMB (@lem6924182) (@lem6924181)). Qed.
Lemma lem6924184 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6924185 : term339 = term302.
Proof. exact (MK_COMB (@lem6924184) (@lem6924183)). Qed.
Lemma lem6924186 : term334 = term302.
Proof. exact (TRANS (@lem6924179) (@lem6924185)). Qed.
Lemma lem6924188 (x : nat) : (term369 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6924189 : term368 = term217.
Proof. exact (@lem6924188 term237). Qed.
Lemma lem6924190 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6924191 : term431 = term219.
Proof. exact (MK_COMB (@lem6924190) (@lem6924189)). Qed.
Lemma lem6924192 : term430 = term425.
Proof. exact (MK_COMB (@lem6924191) (@lem6924186)). Qed.
Lemma lem6924194 (m : nat) (n : nat) : (term432 m n) = (term433 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6924195 : term425 = term434.
Proof. exact (@lem6924194 (NUMERAL 0) term237). Qed.
Lemma lem6924196 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6924197 (h1 : term358 = (BIT1 0)) : (term237 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6924198 : (term358 = (BIT1 0)) = ((term237 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6924197 h1) (fun h1 : (term237 = (NUMERAL 0)) = False => @lem6924196)). Qed.
Lemma lem6924199 : (term237 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6924198) (@lem6924196)). Qed.
Lemma lem6924200 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6924201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6924202 : term435 = (and True).
Proof. exact (MK_COMB (@lem6924201) (@lem6924200)). Qed.
Lemma lem6924203 : term434 = (True /\ False).
Proof. exact (MK_COMB (@lem6924202) (@lem6924199)). Qed.
Lemma lem6924205 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6924206 : term434 = False.
Proof. exact (TRANS (@lem6924203) (@lem6924205)). Qed.
Lemma lem6924207 : term425 = False.
Proof. exact (TRANS (@lem6924195) (@lem6924206)). Qed.
Lemma lem6924208 : term430 = False.
Proof. exact (TRANS (@lem6924192) (@lem6924207)). Qed.
Lemma lem6924209 : term427 = False.
Proof. exact (TRANS (@lem6924176) (@lem6924208)). Qed.
Lemma lem6924210 : term425 = False.
Proof. exact (TRANS (@lem6924153) (@lem6924209)). Qed.
Lemma lem6924211 : term380 = False.
Proof. exact (TRANS (@lem6924144) (@lem6924210)). Qed.
Lemma lem6924212 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term424 _92392 _92393 _92394) : False.
Proof. exact (EQ_MP (@lem6924211) (@lem6924140 _92392 _92393 _92394 h1)). Qed.
Lemma lem6924213 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term421 _92392 _92393 _92394) : term421 _92392 _92393 _92394.
Proof. exact (h1). Qed.
Lemma lem6924214 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term424 _92392 _92393 _92394) : term424 _92392 _92393 _92394.
Proof. exact (h1). Qed.
Lemma lem6924215 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term424 _92392 _92393 _92394) : term419 _92393 _92394.
Proof. exact (proj2 (@lem6924214 _92392 _92393 _92394 h1)). Qed.
Lemma lem6924217 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term424 _92392 _92393 _92394) : term412 _92394.
Proof. exact (proj2 (@lem6924215 _92392 _92393 _92394 h1)). Qed.
Lemma lem6924219 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term424 _92392 _92393 _92394) : term380.
Proof. exact (proj2 (@lem6924217 _92392 _92393 _92394 h1)). Qed.
Lemma lem6924222 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6924223 : term380 = term425.
Proof. exact (@lem6924222 term217 term302). Qed.
Lemma lem6924225 (x : nat) : (term300 x) = (term301 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6924226 : term302 = term303.
Proof. exact (@lem6924225 term237). Qed.
Lemma lem6924228 (x : nat) : (real_of_num x) = (term298 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6924229 : term217 = term299.
Proof. exact (@lem6924228 (NUMERAL 0)). Qed.
Lemma lem6924230 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6924231 : term219 = term426.
Proof. exact (MK_COMB (@lem6924230) (@lem6924229)). Qed.
Lemma lem6924232 : term425 = term427.
Proof. exact (MK_COMB (@lem6924231) (@lem6924226)). Qed.
Lemma lem6924233 : term428.
Proof. exact (@lem1980026 term217 term236 term302 term236). Qed.
Lemma lem6924235 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6924236 : term356 = term357.
Proof. exact (@lem6924235 (NUMERAL 0) term237). Qed.
Lemma lem6924237 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6924238 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6924239 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6924238 h1) (fun h1 : term357 = True => @lem6924237)). Qed.
Lemma lem6924240 : term357 = True.
Proof. exact (EQ_MP (@lem6924239) (@lem6924237)). Qed.
Lemma lem6924241 : term356 = True.
Proof. exact (TRANS (@lem6924236) (@lem6924240)). Qed.
Lemma lem6924242 : True = term356.
Proof. exact (SYM (@lem6924241)). Qed.
Lemma lem6924243 : term356.
Proof. exact (EQ_MP (@lem6924242) (@lem0)). Qed.
Lemma lem6924244 : term429.
Proof. exact (@lem6924233 (@lem6924243)). Qed.
Lemma lem6924246 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6924247 : term356 = term357.
Proof. exact (@lem6924246 (NUMERAL 0) term237). Qed.
Lemma lem6924248 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6924249 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6924250 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6924249 h1) (fun h1 : term357 = True => @lem6924248)). Qed.
Lemma lem6924251 : term357 = True.
Proof. exact (EQ_MP (@lem6924250) (@lem6924248)). Qed.
Lemma lem6924252 : term356 = True.
Proof. exact (TRANS (@lem6924247) (@lem6924251)). Qed.
Lemma lem6924253 : True = term356.
Proof. exact (SYM (@lem6924252)). Qed.
Lemma lem6924254 : term356.
Proof. exact (EQ_MP (@lem6924253) (@lem0)). Qed.
Lemma lem6924255 : term427 = term430.
Proof. exact (@lem6924244 (@lem6924254)). Qed.
Lemma lem6924257 (m : nat) (n : nat) : (term337 m n) = (term338 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6924258 : term334 = term339.
Proof. exact (@lem6924257 term237 term237). Qed.
Lemma lem6924259 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6924260 : term314 = term237.
Proof. exact (EQ_MP (@lem6924259) (@lem940073)). Qed.
Lemma lem6924261 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6924262 : term312 = term236.
Proof. exact (MK_COMB (@lem6924261) (@lem6924260)). Qed.
Lemma lem6924263 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6924264 : term339 = term302.
Proof. exact (MK_COMB (@lem6924263) (@lem6924262)). Qed.
Lemma lem6924265 : term334 = term302.
Proof. exact (TRANS (@lem6924258) (@lem6924264)). Qed.
Lemma lem6924267 (x : nat) : (term369 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6924268 : term368 = term217.
Proof. exact (@lem6924267 term237). Qed.
Lemma lem6924269 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6924270 : term431 = term219.
Proof. exact (MK_COMB (@lem6924269) (@lem6924268)). Qed.
Lemma lem6924271 : term430 = term425.
Proof. exact (MK_COMB (@lem6924270) (@lem6924265)). Qed.
Lemma lem6924273 (m : nat) (n : nat) : (term432 m n) = (term433 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6924274 : term425 = term434.
Proof. exact (@lem6924273 (NUMERAL 0) term237). Qed.
Lemma lem6924275 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6924276 (h1 : term358 = (BIT1 0)) : (term237 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6924277 : (term358 = (BIT1 0)) = ((term237 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6924276 h1) (fun h1 : (term237 = (NUMERAL 0)) = False => @lem6924275)). Qed.
Lemma lem6924278 : (term237 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6924277) (@lem6924275)). Qed.
Lemma lem6924279 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6924280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6924281 : term435 = (and True).
Proof. exact (MK_COMB (@lem6924280) (@lem6924279)). Qed.
Lemma lem6924282 : term434 = (True /\ False).
Proof. exact (MK_COMB (@lem6924281) (@lem6924278)). Qed.
Lemma lem6924284 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6924285 : term434 = False.
Proof. exact (TRANS (@lem6924282) (@lem6924284)). Qed.
Lemma lem6924286 : term425 = False.
Proof. exact (TRANS (@lem6924274) (@lem6924285)). Qed.
Lemma lem6924287 : term430 = False.
Proof. exact (TRANS (@lem6924271) (@lem6924286)). Qed.
Lemma lem6924288 : term427 = False.
Proof. exact (TRANS (@lem6924255) (@lem6924287)). Qed.
Lemma lem6924289 : term425 = False.
Proof. exact (TRANS (@lem6924232) (@lem6924288)). Qed.
Lemma lem6924290 : term380 = False.
Proof. exact (TRANS (@lem6924223) (@lem6924289)). Qed.
Lemma lem6924291 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term424 _92392 _92393 _92394) : False.
Proof. exact (EQ_MP (@lem6924290) (@lem6924219 _92392 _92393 _92394 h1)). Qed.
Lemma lem6924292 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term424 _92392 _92393 _92394) : term424 _92392 _92393 _92394.
Proof. exact (h1). Qed.
Lemma lem6924293 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term424 _92392 _92393 _92394) : term419 _92393 _92394.
Proof. exact (proj2 (@lem6924292 _92392 _92393 _92394 h1)). Qed.
Lemma lem6924295 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term424 _92392 _92393 _92394) : term412 _92394.
Proof. exact (proj2 (@lem6924293 _92392 _92393 _92394 h1)). Qed.
Lemma lem6924297 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term424 _92392 _92393 _92394) : term380.
Proof. exact (proj2 (@lem6924295 _92392 _92393 _92394 h1)). Qed.
Lemma lem6924300 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6924301 : term380 = term425.
Proof. exact (@lem6924300 term217 term302). Qed.
Lemma lem6924303 (x : nat) : (term300 x) = (term301 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6924304 : term302 = term303.
Proof. exact (@lem6924303 term237). Qed.
Lemma lem6924306 (x : nat) : (real_of_num x) = (term298 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6924307 : term217 = term299.
Proof. exact (@lem6924306 (NUMERAL 0)). Qed.
Lemma lem6924308 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6924309 : term219 = term426.
Proof. exact (MK_COMB (@lem6924308) (@lem6924307)). Qed.
Lemma lem6924310 : term425 = term427.
Proof. exact (MK_COMB (@lem6924309) (@lem6924304)). Qed.
Lemma lem6924311 : term428.
Proof. exact (@lem1980026 term217 term236 term302 term236). Qed.
Lemma lem6924313 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6924314 : term356 = term357.
Proof. exact (@lem6924313 (NUMERAL 0) term237). Qed.
Lemma lem6924315 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6924316 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6924317 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6924316 h1) (fun h1 : term357 = True => @lem6924315)). Qed.
Lemma lem6924318 : term357 = True.
Proof. exact (EQ_MP (@lem6924317) (@lem6924315)). Qed.
Lemma lem6924319 : term356 = True.
Proof. exact (TRANS (@lem6924314) (@lem6924318)). Qed.
Lemma lem6924320 : True = term356.
Proof. exact (SYM (@lem6924319)). Qed.
Lemma lem6924321 : term356.
Proof. exact (EQ_MP (@lem6924320) (@lem0)). Qed.
Lemma lem6924322 : term429.
Proof. exact (@lem6924311 (@lem6924321)). Qed.
Lemma lem6924324 (m : nat) (n : nat) : (term355 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6924325 : term356 = term357.
Proof. exact (@lem6924324 (NUMERAL 0) term237). Qed.
Lemma lem6924326 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6924327 (h1 : term358 = (BIT1 0)) : term357 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6924328 : (term358 = (BIT1 0)) = (term357 = True).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6924327 h1) (fun h1 : term357 = True => @lem6924326)). Qed.
Lemma lem6924329 : term357 = True.
Proof. exact (EQ_MP (@lem6924328) (@lem6924326)). Qed.
Lemma lem6924330 : term356 = True.
Proof. exact (TRANS (@lem6924325) (@lem6924329)). Qed.
Lemma lem6924331 : True = term356.
Proof. exact (SYM (@lem6924330)). Qed.
Lemma lem6924332 : term356.
Proof. exact (EQ_MP (@lem6924331) (@lem0)). Qed.
Lemma lem6924333 : term427 = term430.
Proof. exact (@lem6924322 (@lem6924332)). Qed.
Lemma lem6924335 (m : nat) (n : nat) : (term337 m n) = (term338 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6924336 : term334 = term339.
Proof. exact (@lem6924335 term237 term237). Qed.
Lemma lem6924337 : (term313 = (BIT1 0)) = (term314 = term237).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6924338 : term314 = term237.
Proof. exact (EQ_MP (@lem6924337) (@lem940073)). Qed.
Lemma lem6924339 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6924340 : term312 = term236.
Proof. exact (MK_COMB (@lem6924339) (@lem6924338)). Qed.
Lemma lem6924341 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6924342 : term339 = term302.
Proof. exact (MK_COMB (@lem6924341) (@lem6924340)). Qed.
Lemma lem6924343 : term334 = term302.
Proof. exact (TRANS (@lem6924336) (@lem6924342)). Qed.
Lemma lem6924345 (x : nat) : (term369 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6924346 : term368 = term217.
Proof. exact (@lem6924345 term237). Qed.
Lemma lem6924347 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6924348 : term431 = term219.
Proof. exact (MK_COMB (@lem6924347) (@lem6924346)). Qed.
Lemma lem6924349 : term430 = term425.
Proof. exact (MK_COMB (@lem6924348) (@lem6924343)). Qed.
Lemma lem6924351 (m : nat) (n : nat) : (term432 m n) = (term433 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6924352 : term425 = term434.
Proof. exact (@lem6924351 (NUMERAL 0) term237). Qed.
Lemma lem6924353 : term358 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6924354 (h1 : term358 = (BIT1 0)) : (term237 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6924355 : (term358 = (BIT1 0)) = ((term237 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term358 = (BIT1 0) => @lem6924354 h1) (fun h1 : (term237 = (NUMERAL 0)) = False => @lem6924353)). Qed.
Lemma lem6924356 : (term237 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6924355) (@lem6924353)). Qed.
Lemma lem6924357 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6924358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6924359 : term435 = (and True).
Proof. exact (MK_COMB (@lem6924358) (@lem6924357)). Qed.
Lemma lem6924360 : term434 = (True /\ False).
Proof. exact (MK_COMB (@lem6924359) (@lem6924356)). Qed.
Lemma lem6924362 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6924363 : term434 = False.
Proof. exact (TRANS (@lem6924360) (@lem6924362)). Qed.
Lemma lem6924364 : term425 = False.
Proof. exact (TRANS (@lem6924352) (@lem6924363)). Qed.
Lemma lem6924365 : term430 = False.
Proof. exact (TRANS (@lem6924349) (@lem6924364)). Qed.
Lemma lem6924366 : term427 = False.
Proof. exact (TRANS (@lem6924333) (@lem6924365)). Qed.
Lemma lem6924367 : term425 = False.
Proof. exact (TRANS (@lem6924310) (@lem6924366)). Qed.
Lemma lem6924368 : term380 = False.
Proof. exact (TRANS (@lem6924301) (@lem6924367)). Qed.
Lemma lem6924369 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term424 _92392 _92393 _92394) : False.
Proof. exact (EQ_MP (@lem6924368) (@lem6924297 _92392 _92393 _92394 h1)). Qed.
Lemma lem6924370 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term421 _92392 _92393 _92394) : False.
Proof. exact (or_elim (@lem6924213 _92392 _92393 _92394 h1) (fun h0 : term424 _92392 _92393 _92394 => @lem6924291 _92392 _92393 _92394 h0) (fun h0 : term424 _92392 _92393 _92394 => @lem6924369 _92392 _92393 _92394 h0)). Qed.
Lemma lem6924371 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term423 _92392 _92393 _92394) : False.
Proof. exact (or_elim (@lem6924134 _92392 _92393 _92394 h1) (fun h0 : term424 _92392 _92393 _92394 => @lem6924212 _92392 _92393 _92394 h0) (fun h0 : term421 _92392 _92393 _92394 => @lem6924370 _92392 _92393 _92394 h0)). Qed.
Lemma lem6924373 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term423 _92392 _92393 _92394) : term423 _92392 _92393 _92394.
Proof. exact (h1). Qed.
Lemma lem6924374 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term423 _92392 _92393 _92394) : (term423 _92392 _92393 _92394) = False.
Proof. exact (prop_ext (fun h2 : term423 _92392 _92393 _92394 => @lem6924371 _92392 _92393 _92394 h1) (fun h2 : False => @lem6924373 _92392 _92393 _92394 h1)). Qed.
Lemma lem6924375 (_92392 : int) (_92393 : int) (_92394 : int) (h1 : term423 _92392 _92393 _92394) : False.
Proof. exact (EQ_MP (@lem6924374 _92392 _92393 _92394 h1) (@lem6924373 _92392 _92393 _92394 h1)). Qed.
Lemma lem6924376 (_92393 : int) (_92394 : int) (_92392 : int) (h1 : term289 _92393 _92394 _92392) : term289 _92393 _92394 _92392.
Proof. exact (h1). Qed.
Lemma lem6924377 (_92393 : int) (_92394 : int) (_92392 : int) (h1 : term289 _92393 _92394 _92392) : term423 _92392 _92393 _92394.
Proof. exact (EQ_MP (@lem6924118 _92392 _92393 _92394) (@lem6924376 _92393 _92394 _92392 h1)). Qed.
Lemma lem6924378 (_92393 : int) (_92394 : int) (_92392 : int) (h1 : term289 _92393 _92394 _92392) : (term423 _92392 _92393 _92394) = False.
Proof. exact (prop_ext (fun h2 : term423 _92392 _92393 _92394 => @lem6924375 _92392 _92393 _92394 h2) (fun h2 : False => @lem6924377 _92393 _92394 _92392 h1)). Qed.
Lemma lem6924379 (_92393 : int) (_92394 : int) (_92392 : int) (h1 : term289 _92393 _92394 _92392) : False.
Proof. exact (EQ_MP (@lem6924378 _92393 _92394 _92392 h1) (@lem6924377 _92393 _92394 _92392 h1)). Qed.
Lemma lem6924380 (_92393 : int) (_92394 : int) (_92392 : int) : term436 _92393 _92394 _92392.
Proof. exact (fun h0 : term289 _92393 _92394 _92392 => @lem6924379 _92393 _92394 _92392 h0). Qed.
Lemma lem6924381 (_92393 : int) (_92394 : int) (_92392 : int) : term437 _92393 _92394 _92392.
Proof. exact (@lem1386578 (term438 _92393 _92394 _92392)). Qed.
Lemma lem6924384 (_92393 : int) (_92394 : int) (_92392 : int) : term438 _92393 _92394 _92392.
Proof. exact (@lem6924381 _92393 _92394 _92392 (@lem6924380 _92393 _92394 _92392)). Qed.
Lemma lem6924385 (_92393 : int) (_92394 : int) (_92392 : int) : (term287 _92393 _92394 _92392) = (term210 _92393 _92394 _92392).
Proof. exact (SYM (@lem6922851 _92393 _92394 _92392)). Qed.
Lemma lem6924386 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6924387 (_92393 : int) (_92394 : int) (_92392 : int) : (term438 _92393 _92394 _92392) = (term188 _92393 _92394 _92392).
Proof. exact (MK_COMB (@lem6924386) (@lem6924385 _92393 _92394 _92392)). Qed.
Lemma lem6924388 (_92393 : int) (_92394 : int) (_92392 : int) : term188 _92393 _92394 _92392.
Proof. exact (EQ_MP (@lem6924387 _92393 _92394 _92392) (@lem6924384 _92393 _92394 _92392)). Qed.
Lemma lem6924389 (_92393 : int) (_92394 : int) (_92392 : int) : term189 _92393 _92394 _92392.
Proof. exact (EQ_MP (@lem6922550 _92393 _92394 _92392) (@lem6924388 _92393 _92394 _92392)). Qed.
Lemma lem6924390 (y : nat) (z : nat) (x : nat) : term439 y z x.
Proof. exact (@lem6924389 (int_of_num y) (int_of_num z) (int_of_num x)). Qed.
Lemma lem6924391 (y : nat) (z : nat) (x : nat) : term440 y z x.
Proof. exact (@lem6924390 y z x (@lem6922543 x)). Qed.
Lemma lem6924392 (y : nat) (z : nat) (x : nat) : term441 y z x.
Proof. exact (@lem6924391 y z x (@lem6922546 y)). Qed.
Lemma lem6924393 (y : nat) (z : nat) (x : nat) : term179 y z x.
Proof. exact (@lem6924392 y z x (@lem6922549 z)). Qed.
Lemma lem6924394 (y : nat) (x : nat) : term181 y x.
Proof. exact (fun z : nat => @lem6924393 y z x). Qed.
Lemma lem6924395 (x : nat) : term183 x.
Proof. exact (fun y : nat => @lem6924394 y x). Qed.
Lemma lem6924396 : term185.
Proof. exact (fun x : nat => @lem6924395 x). Qed.
Lemma lem6924397 : term185 = term18.
Proof. exact (SYM (@lem6922540)). Qed.
Lemma lem6924398 : term18.
Proof. exact (EQ_MP (@lem6924397) (@lem6924396)). Qed.
Lemma lem6924399 : term18 = (term18 = True).
Proof. exact (@lem7 term18). Qed.
Lemma lem6924400 : term18 = True.
Proof. exact (EQ_MP (@lem6924399) (@lem6924398)). Qed.
Lemma lem6924401 : True = term18.
Proof. exact (SYM (@lem6924400)). Qed.
Lemma lem6924402 : term18.
Proof. exact (EQ_MP (@lem6924401) (@lem0)). Qed.
Lemma lem6924403 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem6922063) (@lem6924402)). Qed.
