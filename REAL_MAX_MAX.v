Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MAX_MAX_term_abbrevs.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482710_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483488_spec.
Require Import thm1483519_spec.
Require Import thm1483533_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm17045_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Lemma lem1557034 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term0 A P Q) = (term1 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1557035 (P : real -> Prop) (Q : real -> Prop) : (term2 P Q) = (term3 P Q).
Proof. exact (@lem1557034 real P Q). Qed.
Lemma lem1557036 (x : real) : (term4 x) = (term5 x).
Proof. exact (@lem1557035 (term6 x) (term7 x)). Qed.
Lemma lem1557037 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1557038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1557039 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem1557038) (@lem1557037 x y)). Qed.
Lemma lem1557040 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1557041 (x : real) (y : real) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1557039 x y) (@lem1557040 x y)). Qed.
Lemma lem1557042 (x : real) : (term16 x) = (term17 x).
Proof. exact (fun_ext (fun y : real => @lem1557041 x y)). Qed.
Lemma lem1557043 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1557044 (x : real) : (term4 x) = (term18 x).
Proof. exact (MK_COMB (@lem1557043) (@lem1557042 x)). Qed.
Lemma lem1557045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1557046 (x : real) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem1557045) (@lem1557044 x)). Qed.
Lemma lem1557047 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1557048 (x : real) : (term21 x) = (term6 x).
Proof. exact (fun_ext (fun y : real => @lem1557047 x y)). Qed.
Lemma lem1557049 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1557050 (x : real) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem1557049) (@lem1557048 x)). Qed.
Lemma lem1557051 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1557052 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1557051) (@lem1557050 x)). Qed.
Lemma lem1557053 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1557054 (x : real) : (term26 x) = (term7 x).
Proof. exact (fun_ext (fun y : real => @lem1557053 x y)). Qed.
Lemma lem1557055 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1557056 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1557055) (@lem1557054 x)). Qed.
Lemma lem1557057 (x : real) : (term5 x) = (term29 x).
Proof. exact (MK_COMB (@lem1557052 x) (@lem1557056 x)). Qed.
Lemma lem1557058 (x : real) : ((term4 x) = (term5 x)) = ((term18 x) = (term29 x)).
Proof. exact (MK_COMB (@lem1557046 x) (@lem1557057 x)). Qed.
Lemma lem1557059 (x : real) : (term18 x) = (term29 x).
Proof. exact (EQ_MP (@lem1557058 x) (@lem1557036 x)). Qed.
Lemma lem1557070 : term30 = term31.
Proof. exact (fun_ext (fun x : real => @lem1557059 x)). Qed.
Lemma lem1557071 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1557072 : term32 = term33.
Proof. exact (MK_COMB (@lem1557071) (@lem1557070)). Qed.
Lemma lem1557074 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term0 A P Q) = (term1 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1557075 (P : real -> Prop) (Q : real -> Prop) : (term2 P Q) = (term3 P Q).
Proof. exact (@lem1557074 real P Q). Qed.
Lemma lem1557076 : term34 = term35.
Proof. exact (@lem1557075 term36 term37). Qed.
Lemma lem1557077 (x : real) : (term38 x) = (term23 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1557078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1557079 (x : real) : (term39 x) = (term25 x).
Proof. exact (MK_COMB (@lem1557078) (@lem1557077 x)). Qed.
Lemma lem1557080 (x : real) : (term40 x) = (term28 x).
Proof. exact (eq_refl (term40 x)). Qed.
Lemma lem1557081 (x : real) : (term41 x) = (term29 x).
Proof. exact (MK_COMB (@lem1557079 x) (@lem1557080 x)). Qed.
Lemma lem1557082 : term42 = term31.
Proof. exact (fun_ext (fun x : real => @lem1557081 x)). Qed.
Lemma lem1557083 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1557084 : term34 = term33.
Proof. exact (MK_COMB (@lem1557083) (@lem1557082)). Qed.
Lemma lem1557085 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1557086 : term43 = term44.
Proof. exact (MK_COMB (@lem1557085) (@lem1557084)). Qed.
Lemma lem1557087 (x : real) : (term38 x) = (term23 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1557088 : term45 = term36.
Proof. exact (fun_ext (fun x : real => @lem1557087 x)). Qed.
Lemma lem1557089 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1557090 : term46 = term47.
Proof. exact (MK_COMB (@lem1557089) (@lem1557088)). Qed.
Lemma lem1557091 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1557092 : term48 = term49.
Proof. exact (MK_COMB (@lem1557091) (@lem1557090)). Qed.
Lemma lem1557093 (x : real) : (term40 x) = (term28 x).
Proof. exact (eq_refl (term40 x)). Qed.
Lemma lem1557094 : term50 = term37.
Proof. exact (fun_ext (fun x : real => @lem1557093 x)). Qed.
Lemma lem1557095 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1557096 : term51 = term52.
Proof. exact (MK_COMB (@lem1557095) (@lem1557094)). Qed.
Lemma lem1557097 : term35 = term53.
Proof. exact (MK_COMB (@lem1557092) (@lem1557096)). Qed.
Lemma lem1557098 : (term34 = term35) = (term33 = term53).
Proof. exact (MK_COMB (@lem1557086) (@lem1557097)). Qed.
Lemma lem1557099 : term33 = term53.
Proof. exact (EQ_MP (@lem1557098) (@lem1557076)). Qed.
Lemma lem1557118 : term32 = term53.
Proof. exact (TRANS (@lem1557072) (@lem1557099)). Qed.
Lemma lem1557119 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1557121 : term54 = term55.
Proof. exact (MK_COMB (@lem1557119) (@lem1557118)). Qed.
Lemma lem1557123 (P : real -> Prop) : (term56 P) = (term57 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1557124 (x : real) : (term58 x) = (term59 x).
Proof. exact (@lem1557123 (term6 x)). Qed.
Lemma lem1557125 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1557126 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1557128 (x : real) (y : real) : (term60 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1557126) (@lem1557125 x y)). Qed.
Lemma lem1557129 (x : real) : (term62 x) = (term63 x).
Proof. exact (fun_ext (fun y : real => @lem1557128 x y)). Qed.
Lemma lem1557130 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557131 (x : real) : (term59 x) = (term64 x).
Proof. exact (MK_COMB (@lem1557130) (@lem1557129 x)). Qed.
Lemma lem1557132 (x : real) : (term58 x) = (term64 x).
Proof. exact (TRANS (@lem1557124 x) (@lem1557131 x)). Qed.
Lemma lem1557133 (P : real -> Prop) : (term56 P) = (term57 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1557134 : term65 = term66.
Proof. exact (@lem1557133 term36). Qed.
Lemma lem1557135 (x : real) : (term38 x) = (term23 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1557136 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1557137 (x : real) : (term67 x) = (term58 x).
Proof. exact (MK_COMB (@lem1557136) (@lem1557135 x)). Qed.
Lemma lem1557138 (x : real) : (term67 x) = (term64 x).
Proof. exact (TRANS (@lem1557137 x) (@lem1557132 x)). Qed.
Lemma lem1557139 : term68 = term69.
Proof. exact (fun_ext (fun x : real => @lem1557138 x)). Qed.
Lemma lem1557140 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557141 : term66 = term70.
Proof. exact (MK_COMB (@lem1557140) (@lem1557139)). Qed.
Lemma lem1557142 : term65 = term70.
Proof. exact (TRANS (@lem1557134) (@lem1557141)). Qed.
Lemma lem1557144 (P : real -> Prop) : (term56 P) = (term57 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1557145 (x : real) : (term71 x) = (term72 x).
Proof. exact (@lem1557144 (term7 x)). Qed.
Lemma lem1557146 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1557147 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1557149 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1557147) (@lem1557146 x y)). Qed.
Lemma lem1557150 (x : real) : (term75 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1557149 x y)). Qed.
Lemma lem1557151 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557152 (x : real) : (term72 x) = (term77 x).
Proof. exact (MK_COMB (@lem1557151) (@lem1557150 x)). Qed.
Lemma lem1557153 (x : real) : (term71 x) = (term77 x).
Proof. exact (TRANS (@lem1557145 x) (@lem1557152 x)). Qed.
Lemma lem1557154 (P : real -> Prop) : (term56 P) = (term57 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1557155 : term78 = term79.
Proof. exact (@lem1557154 term37). Qed.
Lemma lem1557156 (x : real) : (term40 x) = (term28 x).
Proof. exact (eq_refl (term40 x)). Qed.
Lemma lem1557157 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1557158 (x : real) : (term80 x) = (term71 x).
Proof. exact (MK_COMB (@lem1557157) (@lem1557156 x)). Qed.
Lemma lem1557159 (x : real) : (term80 x) = (term77 x).
Proof. exact (TRANS (@lem1557158 x) (@lem1557153 x)). Qed.
Lemma lem1557160 : term81 = term82.
Proof. exact (fun_ext (fun x : real => @lem1557159 x)). Qed.
Lemma lem1557161 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557162 : term79 = term83.
Proof. exact (MK_COMB (@lem1557161) (@lem1557160)). Qed.
Lemma lem1557163 : term78 = term83.
Proof. exact (TRANS (@lem1557155) (@lem1557162)). Qed.
Lemma lem1557164 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557165 : term84 = term85.
Proof. exact (MK_COMB (@lem1557164) (@lem1557142)). Qed.
Lemma lem1557166 : term86 = term87.
Proof. exact (MK_COMB (@lem1557165) (@lem1557163)). Qed.
Lemma lem1557167 : term55 = term86.
Proof. exact (@lem17045 term47 term52). Qed.
Lemma lem1557168 : term55 = term87.
Proof. exact (TRANS (@lem1557167) (@lem1557166)). Qed.
Lemma lem1557169 : term54 = term87.
Proof. exact (TRANS (@lem1557121) (@lem1557168)). Qed.
Lemma lem1557172 (x : real) (y : real) : (term61 x y) = (term61 x y).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem1557173 (x : real) : (term63 x) = (term63 x).
Proof. exact (fun_ext (fun y : real => @lem1557172 x y)). Qed.
Lemma lem1557174 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557175 (x : real) : (term64 x) = (term64 x).
Proof. exact (MK_COMB (@lem1557174) (@lem1557173 x)). Qed.
Lemma lem1557176 : term69 = term69.
Proof. exact (fun_ext (fun x : real => @lem1557175 x)). Qed.
Lemma lem1557177 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557178 : term70 = term70.
Proof. exact (MK_COMB (@lem1557177) (@lem1557176)). Qed.
Lemma lem1557181 (x : real) (y : real) : (term74 x y) = (term74 x y).
Proof. exact (eq_refl (term74 x y)). Qed.
Lemma lem1557182 (x : real) : (term76 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1557181 x y)). Qed.
Lemma lem1557183 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557184 (x : real) : (term77 x) = (term77 x).
Proof. exact (MK_COMB (@lem1557183) (@lem1557182 x)). Qed.
Lemma lem1557185 : term82 = term82.
Proof. exact (fun_ext (fun x : real => @lem1557184 x)). Qed.
Lemma lem1557186 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557187 : term83 = term83.
Proof. exact (MK_COMB (@lem1557186) (@lem1557185)). Qed.
Lemma lem1557188 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557189 : term85 = term85.
Proof. exact (MK_COMB (@lem1557188) (@lem1557178)). Qed.
Lemma lem1557190 : term87 = term87.
Proof. exact (MK_COMB (@lem1557189) (@lem1557187)). Qed.
Lemma lem1557191 : term54 = term87.
Proof. exact (TRANS (@lem1557169) (@lem1557190)). Qed.
Lemma lem1557192 (x : real) (y : real) : (term61 x y) = (term88 x y).
Proof. exact (@lem1483533 x (real_max x y)). Qed.
Lemma lem1557205 (x : real) (y : real) : (term89 x y) = (term90 x y).
Proof. exact (@lem1483519 x (real_max x y)). Qed.
Lemma lem1557206 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1557207 (x : real) (y : real) : (term91 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1557206) (@lem1557205 x y)). Qed.
Lemma lem1557208 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem1557209 (x : real) (y : real) : (term88 x y) = (term94 x y).
Proof. exact (MK_COMB (@lem1557207 x y) (@lem1557208)). Qed.
Lemma lem1557210 (x : real) (y : real) : (term61 x y) = (term94 x y).
Proof. exact (TRANS (@lem1557192 x y) (@lem1557209 x y)). Qed.
Lemma lem1557211 (x : real) : (term63 x) = (term95 x).
Proof. exact (fun_ext (fun y : real => @lem1557210 x y)). Qed.
Lemma lem1557212 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557213 (x : real) : (term64 x) = (term96 x).
Proof. exact (MK_COMB (@lem1557212) (@lem1557211 x)). Qed.
Lemma lem1557214 : term69 = term97.
Proof. exact (fun_ext (fun x : real => @lem1557213 x)). Qed.
Lemma lem1557215 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557216 : term70 = term98.
Proof. exact (MK_COMB (@lem1557215) (@lem1557214)). Qed.
Lemma lem1557217 (x : real) (y : real) : (term74 x y) = (term99 x y).
Proof. exact (@lem1483533 y (real_max x y)). Qed.
Lemma lem1557230 (x : real) (y : real) : (term100 x y) = (term101 x y).
Proof. exact (@lem1483519 y (real_max x y)). Qed.
Lemma lem1557231 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1557232 (x : real) (y : real) : (term102 x y) = (term103 x y).
Proof. exact (MK_COMB (@lem1557231) (@lem1557230 x y)). Qed.
Lemma lem1557233 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem1557234 (x : real) (y : real) : (term99 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1557232 x y) (@lem1557233)). Qed.
Lemma lem1557235 (x : real) (y : real) : (term74 x y) = (term104 x y).
Proof. exact (TRANS (@lem1557217 x y) (@lem1557234 x y)). Qed.
Lemma lem1557236 (x : real) : (term76 x) = (term105 x).
Proof. exact (fun_ext (fun y : real => @lem1557235 x y)). Qed.
Lemma lem1557237 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557238 (x : real) : (term77 x) = (term106 x).
Proof. exact (MK_COMB (@lem1557237) (@lem1557236 x)). Qed.
Lemma lem1557239 : term82 = term107.
Proof. exact (fun_ext (fun x : real => @lem1557238 x)). Qed.
Lemma lem1557240 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557241 : term83 = term108.
Proof. exact (MK_COMB (@lem1557240) (@lem1557239)). Qed.
Lemma lem1557242 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557243 : term85 = term109.
Proof. exact (MK_COMB (@lem1557242) (@lem1557216)). Qed.
Lemma lem1557244 : term87 = term110.
Proof. exact (MK_COMB (@lem1557243) (@lem1557241)). Qed.
Lemma lem1557245 : term54 = term110.
Proof. exact (TRANS (@lem1557191) (@lem1557244)). Qed.
Lemma lem1557264 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term111 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1557265 (P : real -> Prop) (Q : real -> Prop) : (term113 P Q) = (term114 P Q).
Proof. exact (@lem1557264 real P Q). Qed.
Lemma lem1557266 : term115 = term116.
Proof. exact (@lem1557265 term97 term107). Qed.
Lemma lem1557267 (x : real) : (term117 x) = (term96 x).
Proof. exact (eq_refl (term117 x)). Qed.
Lemma lem1557268 : term118 = term97.
Proof. exact (fun_ext (fun x : real => @lem1557267 x)). Qed.
Lemma lem1557269 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557270 : term119 = term98.
Proof. exact (MK_COMB (@lem1557269) (@lem1557268)). Qed.
Lemma lem1557271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557272 : term120 = term109.
Proof. exact (MK_COMB (@lem1557271) (@lem1557270)). Qed.
Lemma lem1557273 (x : real) : (term121 x) = (term106 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1557274 : term122 = term107.
Proof. exact (fun_ext (fun x : real => @lem1557273 x)). Qed.
Lemma lem1557275 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557276 : term123 = term108.
Proof. exact (MK_COMB (@lem1557275) (@lem1557274)). Qed.
Lemma lem1557277 : term115 = term110.
Proof. exact (MK_COMB (@lem1557272) (@lem1557276)). Qed.
Lemma lem1557278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1557279 : term124 = term125.
Proof. exact (MK_COMB (@lem1557278) (@lem1557277)). Qed.
Lemma lem1557280 (x : real) : (term117 x) = (term96 x).
Proof. exact (eq_refl (term117 x)). Qed.
Lemma lem1557281 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557282 (x : real) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1557281) (@lem1557280 x)). Qed.
Lemma lem1557283 (x : real) : (term121 x) = (term106 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1557284 (x : real) : (term128 x) = (term129 x).
Proof. exact (MK_COMB (@lem1557282 x) (@lem1557283 x)). Qed.
Lemma lem1557285 : term130 = term131.
Proof. exact (fun_ext (fun x : real => @lem1557284 x)). Qed.
Lemma lem1557286 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557287 : term116 = term132.
Proof. exact (MK_COMB (@lem1557286) (@lem1557285)). Qed.
Lemma lem1557288 : (term115 = term116) = (term110 = term132).
Proof. exact (MK_COMB (@lem1557279) (@lem1557287)). Qed.
Lemma lem1557289 : term110 = term132.
Proof. exact (EQ_MP (@lem1557288) (@lem1557266)). Qed.
Lemma lem1557291 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term111 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1557292 (P : real -> Prop) (Q : real -> Prop) : (term113 P Q) = (term114 P Q).
Proof. exact (@lem1557291 real P Q). Qed.
Lemma lem1557293 (x : real) : (term133 x) = (term134 x).
Proof. exact (@lem1557292 (term95 x) (term105 x)). Qed.
Lemma lem1557294 (x : real) (y : real) : (term135 x y) = (term94 x y).
Proof. exact (eq_refl (term135 x y)). Qed.
Lemma lem1557295 (x : real) : (term136 x) = (term95 x).
Proof. exact (fun_ext (fun y : real => @lem1557294 x y)). Qed.
Lemma lem1557296 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557297 (x : real) : (term137 x) = (term96 x).
Proof. exact (MK_COMB (@lem1557296) (@lem1557295 x)). Qed.
Lemma lem1557298 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557299 (x : real) : (term138 x) = (term127 x).
Proof. exact (MK_COMB (@lem1557298) (@lem1557297 x)). Qed.
Lemma lem1557300 (x : real) (y : real) : (term139 x y) = (term104 x y).
Proof. exact (eq_refl (term139 x y)). Qed.
Lemma lem1557301 (x : real) : (term140 x) = (term105 x).
Proof. exact (fun_ext (fun y : real => @lem1557300 x y)). Qed.
Lemma lem1557302 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557303 (x : real) : (term141 x) = (term106 x).
Proof. exact (MK_COMB (@lem1557302) (@lem1557301 x)). Qed.
Lemma lem1557304 (x : real) : (term133 x) = (term129 x).
Proof. exact (MK_COMB (@lem1557299 x) (@lem1557303 x)). Qed.
Lemma lem1557305 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1557306 (x : real) : (term142 x) = (term143 x).
Proof. exact (MK_COMB (@lem1557305) (@lem1557304 x)). Qed.
Lemma lem1557307 (x : real) (y : real) : (term135 x y) = (term94 x y).
Proof. exact (eq_refl (term135 x y)). Qed.
Lemma lem1557308 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557309 (x : real) (y : real) : (term144 x y) = (term145 x y).
Proof. exact (MK_COMB (@lem1557308) (@lem1557307 x y)). Qed.
Lemma lem1557310 (x : real) (y : real) : (term139 x y) = (term104 x y).
Proof. exact (eq_refl (term139 x y)). Qed.
Lemma lem1557311 (x : real) (y : real) : (term146 x y) = (term147 x y).
Proof. exact (MK_COMB (@lem1557309 x y) (@lem1557310 x y)). Qed.
Lemma lem1557312 (x : real) : (term148 x) = (term149 x).
Proof. exact (fun_ext (fun y : real => @lem1557311 x y)). Qed.
Lemma lem1557313 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557314 (x : real) : (term134 x) = (term150 x).
Proof. exact (MK_COMB (@lem1557313) (@lem1557312 x)). Qed.
Lemma lem1557315 (x : real) : ((term133 x) = (term134 x)) = ((term129 x) = (term150 x)).
Proof. exact (MK_COMB (@lem1557306 x) (@lem1557314 x)). Qed.
Lemma lem1557316 (x : real) : (term129 x) = (term150 x).
Proof. exact (EQ_MP (@lem1557315 x) (@lem1557293 x)). Qed.
Lemma lem1557317 : term131 = term151.
Proof. exact (fun_ext (fun x : real => @lem1557316 x)). Qed.
Lemma lem1557318 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557319 : term132 = term152.
Proof. exact (MK_COMB (@lem1557318) (@lem1557317)). Qed.
Lemma lem1557321 : term110 = term152.
Proof. exact (TRANS (@lem1557289) (@lem1557319)). Qed.
Lemma lem1557324 : term54 = term152.
Proof. exact (TRANS (@lem1557245) (@lem1557321)). Qed.
Lemma lem1557329 (x : real) (y : real) : (term147 x y) = (term147 x y).
Proof. exact (eq_refl (term147 x y)). Qed.
Lemma lem1557330 (x : real) : (term149 x) = (term149 x).
Proof. exact (fun_ext (fun y : real => @lem1557329 x y)). Qed.
Lemma lem1557331 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557332 (x : real) : (term150 x) = (term150 x).
Proof. exact (MK_COMB (@lem1557331) (@lem1557330 x)). Qed.
Lemma lem1557333 : term151 = term151.
Proof. exact (fun_ext (fun x : real => @lem1557332 x)). Qed.
Lemma lem1557334 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557335 : term152 = term152.
Proof. exact (MK_COMB (@lem1557334) (@lem1557333)). Qed.
Lemma lem1557336 : term54 = term152.
Proof. exact (TRANS (@lem1557324) (@lem1557335)). Qed.
Lemma lem1557338 (x : real) (a : real) (y : real) (r : real) : (term153 a x y r) = (term154 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1557339 (x : real) (y : real) : (term94 x y) = (term155 x y).
Proof. exact (@lem1557338 x x y term93). Qed.
Lemma lem1557356 (x : real) (y : real) : (term156 x y) = (term156 x y).
Proof. exact (eq_refl (term156 x y)). Qed.
Lemma lem1557368 (x : real) : (term157 x) = (term158 x).
Proof. exact (@lem1483442 term159 x). Qed.
Lemma lem1557370 (m : nat) : (term160 m) = term93.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1557371 : term161 = term93.
Proof. exact (@lem1557370 term162). Qed.
Lemma lem1557372 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1557373 : term163 = term164.
Proof. exact (MK_COMB (@lem1557372) (@lem1557371)). Qed.
Lemma lem1557374 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1557375 (x : real) : (term158 x) = (term165 x).
Proof. exact (MK_COMB (@lem1557373) (@lem1557374 x)). Qed.
Lemma lem1557376 (x : real) : (term157 x) = (term165 x).
Proof. exact (TRANS (@lem1557368 x) (@lem1557375 x)). Qed.
Lemma lem1557377 (x : real) : (term165 x) = term93.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1557379 (x : real) : (term157 x) = term93.
Proof. exact (TRANS (@lem1557376 x) (@lem1557377 x)). Qed.
Lemma lem1557380 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1557381 (x : real) : (term166 x) = term167.
Proof. exact (MK_COMB (@lem1557380) (@lem1557379 x)). Qed.
Lemma lem1557382 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem1557383 (x : real) : (term168 x) = term169.
Proof. exact (MK_COMB (@lem1557381 x) (@lem1557382)). Qed.
Lemma lem1557384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1557385 (x : real) : (term170 x) = term171.
Proof. exact (MK_COMB (@lem1557384) (@lem1557383 x)). Qed.
Lemma lem1557386 (x : real) (y : real) : (term155 x y) = (term172 x y).
Proof. exact (MK_COMB (@lem1557385 x) (@lem1557356 x y)). Qed.
Lemma lem1557389 (x : real) (y : real) : (term94 x y) = (term172 x y).
Proof. exact (TRANS (@lem1557339 x y) (@lem1557386 x y)). Qed.
Lemma lem1557391 (x : real) (a : real) (y : real) (r : real) : (term153 a x y r) = (term154 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1557392 (x : real) (y : real) : (term104 x y) = (term173 x y).
Proof. exact (@lem1557391 x y y term93). Qed.
Lemma lem1557404 (y : real) : (term157 y) = (term158 y).
Proof. exact (@lem1483442 term159 y). Qed.
Lemma lem1557406 (m : nat) : (term160 m) = term93.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1557407 : term161 = term93.
Proof. exact (@lem1557406 term162). Qed.
Lemma lem1557408 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1557409 : term163 = term164.
Proof. exact (MK_COMB (@lem1557408) (@lem1557407)). Qed.
Lemma lem1557410 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1557411 (y : real) : (term158 y) = (term165 y).
Proof. exact (MK_COMB (@lem1557409) (@lem1557410 y)). Qed.
Lemma lem1557412 (y : real) : (term157 y) = (term165 y).
Proof. exact (TRANS (@lem1557404 y) (@lem1557411 y)). Qed.
Lemma lem1557413 (y : real) : (term165 y) = term93.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1557415 (y : real) : (term157 y) = term93.
Proof. exact (TRANS (@lem1557412 y) (@lem1557413 y)). Qed.
Lemma lem1557416 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1557417 (y : real) : (term166 y) = term167.
Proof. exact (MK_COMB (@lem1557416) (@lem1557415 y)). Qed.
Lemma lem1557418 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem1557419 (y : real) : (term168 y) = term169.
Proof. exact (MK_COMB (@lem1557417 y) (@lem1557418)). Qed.
Lemma lem1557432 (x : real) (y : real) : (term174 y x) = (term175 x y).
Proof. exact (@lem1483488 (term176 x) y). Qed.
Lemma lem1557433 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1557434 (x : real) (y : real) : (term177 y x) = (term178 x y).
Proof. exact (MK_COMB (@lem1557433) (@lem1557432 x y)). Qed.
Lemma lem1557435 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem1557436 (x : real) (y : real) : (term156 y x) = (term179 x y).
Proof. exact (MK_COMB (@lem1557434 x y) (@lem1557435)). Qed.
Lemma lem1557437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1557438 (x : real) (y : real) : (term180 y x) = (term181 x y).
Proof. exact (MK_COMB (@lem1557437) (@lem1557436 x y)). Qed.
Lemma lem1557439 (x : real) (y : real) : (term173 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1557438 x y) (@lem1557419 y)). Qed.
Lemma lem1557442 (x : real) (y : real) : (term104 x y) = (term182 x y).
Proof. exact (TRANS (@lem1557392 x y) (@lem1557439 x y)). Qed.
Lemma lem1557443 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557444 (x : real) (y : real) : (term145 x y) = (term183 x y).
Proof. exact (MK_COMB (@lem1557443) (@lem1557389 x y)). Qed.
Lemma lem1557445 (x : real) (y : real) : (term147 x y) = (term184 x y).
Proof. exact (MK_COMB (@lem1557444 x y) (@lem1557442 x y)). Qed.
Lemma lem1557446 (x : real) (y : real) (h1 : term184 x y) : term184 x y.
Proof. exact (h1). Qed.
Lemma lem1557447 (x : real) (y : real) (h1 : term172 x y) : term172 x y.
Proof. exact (h1). Qed.
Lemma lem1557449 (x : real) (y : real) (h1 : term172 x y) : term169.
Proof. exact (proj1 (@lem1557447 x y h1)). Qed.
Lemma lem1557451 (n : nat) (m : nat) : (term185 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1557452 : term169 = term186.
Proof. exact (@lem1557451 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1557453 : term186 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1557454 : term169 = False.
Proof. exact (TRANS (@lem1557452) (@lem1557453)). Qed.
Lemma lem1557455 (x : real) (y : real) (h1 : term172 x y) : False.
Proof. exact (EQ_MP (@lem1557454) (@lem1557449 x y h1)). Qed.
Lemma lem1557456 (x : real) (y : real) (h1 : term182 x y) : term182 x y.
Proof. exact (h1). Qed.
Lemma lem1557457 (x : real) (y : real) (h1 : term182 x y) : term169.
Proof. exact (proj2 (@lem1557456 x y h1)). Qed.
Lemma lem1557460 (n : nat) (m : nat) : (term185 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1557461 : term169 = term186.
Proof. exact (@lem1557460 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1557462 : term186 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1557463 : term169 = False.
Proof. exact (TRANS (@lem1557461) (@lem1557462)). Qed.
Lemma lem1557464 (x : real) (y : real) (h1 : term182 x y) : False.
Proof. exact (EQ_MP (@lem1557463) (@lem1557457 x y h1)). Qed.
Lemma lem1557465 (x : real) (y : real) (h1 : term184 x y) : False.
Proof. exact (or_elim (@lem1557446 x y h1) (fun h0 : term172 x y => @lem1557455 x y h0) (fun h0 : term182 x y => @lem1557464 x y h0)). Qed.
Lemma lem1557466 (x : real) (y : real) (h1 : term147 x y) : term147 x y.
Proof. exact (h1). Qed.
Lemma lem1557467 (x : real) (y : real) (h1 : term147 x y) : term184 x y.
Proof. exact (EQ_MP (@lem1557445 x y) (@lem1557466 x y h1)). Qed.
Lemma lem1557468 (x : real) (y : real) (h1 : term147 x y) : (term184 x y) = False.
Proof. exact (prop_ext (fun h2 : term184 x y => @lem1557465 x y h2) (fun h2 : False => @lem1557467 x y h1)). Qed.
Lemma lem1557469 (x : real) (y : real) (h1 : term147 x y) : False.
Proof. exact (EQ_MP (@lem1557468 x y h1) (@lem1557467 x y h1)). Qed.
Lemma lem1557470 (x : real) (h1 : term150 x) : term150 x.
Proof. exact (h1). Qed.
Lemma lem1557471 (x : real) (h1 : term150 x) : False.
Proof. exact (ex_elim (@lem1557470 x h1) (fun y : real => fun h0 : term149 x y => @lem1557469 x y h0)). Qed.
Lemma lem1557472 (h1 : term152) : term152.
Proof. exact (h1). Qed.
Lemma lem1557473 (h1 : term152) : False.
Proof. exact (ex_elim (@lem1557472 h1) (fun x : real => fun h0 : term151 x => @lem1557471 x h0)). Qed.
Lemma lem1557474 (h1 : term54) : term54.
Proof. exact (h1). Qed.
Lemma lem1557475 (h1 : term54) : term152.
Proof. exact (EQ_MP (@lem1557336) (@lem1557474 h1)). Qed.
Lemma lem1557476 (h1 : term54) : term152 = False.
Proof. exact (prop_ext (fun h2 : term152 => @lem1557473 h2) (fun h2 : False => @lem1557475 h1)). Qed.
Lemma lem1557477 (h1 : term54) : False.
Proof. exact (EQ_MP (@lem1557476 h1) (@lem1557475 h1)). Qed.
Lemma lem1557478 : term187.
Proof. exact (fun h0 : term54 => @lem1557477 h0). Qed.
Lemma lem1557479 : term188.
Proof. exact (@lem1386578 term32). Qed.
Lemma lem1557480 : term32.
Proof. exact (@lem1557479 (@lem1557478)). Qed.
