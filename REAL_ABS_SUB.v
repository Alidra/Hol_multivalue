Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_SUB_term_abbrevs.
Require Import thm1006570_spec.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1482703_spec.
Require Import thm1482704_spec.
Require Import thm1482981_spec.
Require Import thm1483436_spec.
Require Import thm1483438_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483444_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483490_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm706885_spec.
Require Import thm940073_spec.
Lemma lem1532089 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1532090 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1532089 (term4 x)). Qed.
Lemma lem1532091 (y : real) (x : real) : (term5 x y) = ((term6 x y) = (term6 y x)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1532092 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1532094 (y : real) (x : real) : (term7 x y) = (term8 y x).
Proof. exact (MK_COMB (@lem1532092) (@lem1532091 y x)). Qed.
Lemma lem1532095 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1532094 y x)). Qed.
Lemma lem1532096 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532097 (x : real) : (term3 x) = (term11 x).
Proof. exact (MK_COMB (@lem1532096) (@lem1532095 x)). Qed.
Lemma lem1532098 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1532090 x) (@lem1532097 x)). Qed.
Lemma lem1532099 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1532100 : term12 = term13.
Proof. exact (@lem1532099 term14). Qed.
Lemma lem1532101 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1532102 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1532103 (x : real) : (term17 x) = (term2 x).
Proof. exact (MK_COMB (@lem1532102) (@lem1532101 x)). Qed.
Lemma lem1532104 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1532103 x) (@lem1532098 x)). Qed.
Lemma lem1532105 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1532104 x)). Qed.
Lemma lem1532106 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532107 : term13 = term20.
Proof. exact (MK_COMB (@lem1532106) (@lem1532105)). Qed.
Lemma lem1532109 : term12 = term20.
Proof. exact (TRANS (@lem1532100) (@lem1532107)). Qed.
Lemma lem1532112 (y : real) (x : real) : (term8 y x) = (term8 y x).
Proof. exact (eq_refl (term8 y x)). Qed.
Lemma lem1532113 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1532112 y x)). Qed.
Lemma lem1532114 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532115 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1532114) (@lem1532113 x)). Qed.
Lemma lem1532116 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1532115 x)). Qed.
Lemma lem1532117 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532118 : term20 = term20.
Proof. exact (MK_COMB (@lem1532117) (@lem1532116)). Qed.
Lemma lem1532119 : term12 = term20.
Proof. exact (TRANS (@lem1532109) (@lem1532118)). Qed.
Lemma lem1532120 (y : real) (x : real) : (term8 y x) = (term21 y x).
Proof. exact (@lem1483554 (term6 x y) (term6 y x)). Qed.
Lemma lem1532133 (y : real) (x : real) : (term22 y x) = (term23 y x).
Proof. exact (@lem1483519 (term6 x y) (term6 y x)). Qed.
Lemma lem1532134 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1532135 (y : real) (x : real) : (term24 y x) = (term25 y x).
Proof. exact (MK_COMB (@lem1532134) (@lem1532133 y x)). Qed.
Lemma lem1532136 (y : real) (x : real) : (term25 y x) = (term26 y x).
Proof. exact (@lem1483512 (term23 y x)). Qed.
Lemma lem1532137 (y : real) (x : real) : (term26 y x) = (term27 y x).
Proof. exact (@lem1483508 (term6 x y) term28 (term29 y x)). Qed.
Lemma lem1532138 (y : real) (x : real) : (term30 y x) = (term31 y x).
Proof. exact (@lem1483476 term28 term28 (term6 y x)). Qed.
Lemma lem1532140 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1532141 : term34 = term35.
Proof. exact (@lem1532140 term36 term36). Qed.
Lemma lem1532142 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1532143 : term38 = term36.
Proof. exact (EQ_MP (@lem1532142) (@lem940073)). Qed.
Lemma lem1532144 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1532145 : term35 = term39.
Proof. exact (MK_COMB (@lem1532144) (@lem1532143)). Qed.
Lemma lem1532146 : term34 = term39.
Proof. exact (TRANS (@lem1532141) (@lem1532145)). Qed.
Lemma lem1532147 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1532148 : term40 = term41.
Proof. exact (MK_COMB (@lem1532147) (@lem1532146)). Qed.
Lemma lem1532149 (y : real) (x : real) : (term6 y x) = (term6 y x).
Proof. exact (eq_refl (term6 y x)). Qed.
Lemma lem1532150 (y : real) (x : real) : (term31 y x) = (term42 y x).
Proof. exact (MK_COMB (@lem1532148) (@lem1532149 y x)). Qed.
Lemma lem1532151 (y : real) (x : real) : (term30 y x) = (term42 y x).
Proof. exact (TRANS (@lem1532138 y x) (@lem1532150 y x)). Qed.
Lemma lem1532152 (y : real) (x : real) : (term42 y x) = (term6 y x).
Proof. exact (@lem1483436 (term6 y x)). Qed.
Lemma lem1532153 (y : real) (x : real) : (term30 y x) = (term6 y x).
Proof. exact (TRANS (@lem1532151 y x) (@lem1532152 y x)). Qed.
Lemma lem1532156 (x : real) (y : real) : (term43 x y) = (term43 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1532157 (y : real) (x : real) : (term27 y x) = (term44 y x).
Proof. exact (MK_COMB (@lem1532156 x y) (@lem1532153 y x)). Qed.
Lemma lem1532158 (y : real) (x : real) : (term26 y x) = (term44 y x).
Proof. exact (TRANS (@lem1532137 y x) (@lem1532157 y x)). Qed.
Lemma lem1532159 (y : real) (x : real) : (term25 y x) = (term44 y x).
Proof. exact (TRANS (@lem1532136 y x) (@lem1532158 y x)). Qed.
Lemma lem1532160 (y : real) (x : real) : (term45 y x) = (term45 y x).
Proof. exact (eq_refl (term45 y x)). Qed.
Lemma lem1532161 (y : real) (x : real) : ((term24 y x) = (term25 y x)) = ((term24 y x) = (term44 y x)).
Proof. exact (MK_COMB (@lem1532160 y x) (@lem1532159 y x)). Qed.
Lemma lem1532162 (y : real) (x : real) : (term24 y x) = (term44 y x).
Proof. exact (EQ_MP (@lem1532161 y x) (@lem1532135 y x)). Qed.
Lemma lem1532163 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1532164 (y : real) (x : real) : (term46 y x) = (term47 y x).
Proof. exact (MK_COMB (@lem1532163) (@lem1532162 y x)). Qed.
Lemma lem1532165 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532166 (y : real) (x : real) : (term49 y x) = (term50 y x).
Proof. exact (MK_COMB (@lem1532164 y x) (@lem1532165)). Qed.
Lemma lem1532167 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1532168 (y : real) (x : real) : (term51 y x) = (term52 y x).
Proof. exact (MK_COMB (@lem1532167) (@lem1532133 y x)). Qed.
Lemma lem1532169 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532170 (y : real) (x : real) : (term53 y x) = (term54 y x).
Proof. exact (MK_COMB (@lem1532168 y x) (@lem1532169)). Qed.
Lemma lem1532171 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1532172 (y : real) (x : real) : (term55 y x) = (term56 y x).
Proof. exact (MK_COMB (@lem1532171) (@lem1532170 y x)). Qed.
Lemma lem1532173 (y : real) (x : real) : (term21 y x) = (term57 y x).
Proof. exact (MK_COMB (@lem1532172 y x) (@lem1532166 y x)). Qed.
Lemma lem1532174 (y : real) (x : real) : (term8 y x) = (term57 y x).
Proof. exact (TRANS (@lem1532120 y x) (@lem1532173 y x)). Qed.
Lemma lem1532175 (x : real) : (term10 x) = (term58 x).
Proof. exact (fun_ext (fun y : real => @lem1532174 y x)). Qed.
Lemma lem1532176 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532177 (x : real) : (term11 x) = (term59 x).
Proof. exact (MK_COMB (@lem1532176) (@lem1532175 x)). Qed.
Lemma lem1532178 : term19 = term60.
Proof. exact (fun_ext (fun x : real => @lem1532177 x)). Qed.
Lemma lem1532179 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532180 : term20 = term61.
Proof. exact (MK_COMB (@lem1532179) (@lem1532178)). Qed.
Lemma lem1532181 : term12 = term61.
Proof. exact (TRANS (@lem1532119) (@lem1532180)). Qed.
Lemma lem1532187 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term62 A P Q) = (term63 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1532188 (P : real -> Prop) (Q : real -> Prop) : (term64 P Q) = (term65 P Q).
Proof. exact (@lem1532187 real P Q). Qed.
Lemma lem1532189 (x : real) : (term66 x) = (term67 x).
Proof. exact (@lem1532188 (term68 x) (term69 x)). Qed.
Lemma lem1532190 (y : real) (x : real) : (term70 x y) = (term54 y x).
Proof. exact (eq_refl (term70 x y)). Qed.
Lemma lem1532191 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1532192 (y : real) (x : real) : (term71 x y) = (term56 y x).
Proof. exact (MK_COMB (@lem1532191) (@lem1532190 y x)). Qed.
Lemma lem1532193 (y : real) (x : real) : (term72 x y) = (term50 y x).
Proof. exact (eq_refl (term72 x y)). Qed.
Lemma lem1532194 (y : real) (x : real) : (term73 x y) = (term57 y x).
Proof. exact (MK_COMB (@lem1532192 y x) (@lem1532193 y x)). Qed.
Lemma lem1532195 (x : real) : (term74 x) = (term58 x).
Proof. exact (fun_ext (fun y : real => @lem1532194 y x)). Qed.
Lemma lem1532196 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532197 (x : real) : (term66 x) = (term59 x).
Proof. exact (MK_COMB (@lem1532196) (@lem1532195 x)). Qed.
Lemma lem1532198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1532199 (x : real) : (term75 x) = (term76 x).
Proof. exact (MK_COMB (@lem1532198) (@lem1532197 x)). Qed.
Lemma lem1532200 (y : real) (x : real) : (term70 x y) = (term54 y x).
Proof. exact (eq_refl (term70 x y)). Qed.
Lemma lem1532201 (x : real) : (term77 x) = (term68 x).
Proof. exact (fun_ext (fun y : real => @lem1532200 y x)). Qed.
Lemma lem1532202 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532203 (x : real) : (term78 x) = (term79 x).
Proof. exact (MK_COMB (@lem1532202) (@lem1532201 x)). Qed.
Lemma lem1532204 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1532205 (x : real) : (term80 x) = (term81 x).
Proof. exact (MK_COMB (@lem1532204) (@lem1532203 x)). Qed.
Lemma lem1532206 (y : real) (x : real) : (term72 x y) = (term50 y x).
Proof. exact (eq_refl (term72 x y)). Qed.
Lemma lem1532207 (x : real) : (term82 x) = (term69 x).
Proof. exact (fun_ext (fun y : real => @lem1532206 y x)). Qed.
Lemma lem1532208 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532209 (x : real) : (term83 x) = (term84 x).
Proof. exact (MK_COMB (@lem1532208) (@lem1532207 x)). Qed.
Lemma lem1532210 (x : real) : (term67 x) = (term85 x).
Proof. exact (MK_COMB (@lem1532205 x) (@lem1532209 x)). Qed.
Lemma lem1532211 (x : real) : ((term66 x) = (term67 x)) = ((term59 x) = (term85 x)).
Proof. exact (MK_COMB (@lem1532199 x) (@lem1532210 x)). Qed.
Lemma lem1532212 (x : real) : (term59 x) = (term85 x).
Proof. exact (EQ_MP (@lem1532211 x) (@lem1532189 x)). Qed.
Lemma lem1532221 : term60 = term86.
Proof. exact (fun_ext (fun x : real => @lem1532212 x)). Qed.
Lemma lem1532222 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532223 : term61 = term87.
Proof. exact (MK_COMB (@lem1532222) (@lem1532221)). Qed.
Lemma lem1532225 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term62 A P Q) = (term63 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1532226 (P : real -> Prop) (Q : real -> Prop) : (term64 P Q) = (term65 P Q).
Proof. exact (@lem1532225 real P Q). Qed.
Lemma lem1532227 : term88 = term89.
Proof. exact (@lem1532226 term90 term91). Qed.
Lemma lem1532228 (x : real) : (term92 x) = (term79 x).
Proof. exact (eq_refl (term92 x)). Qed.
Lemma lem1532229 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1532230 (x : real) : (term93 x) = (term81 x).
Proof. exact (MK_COMB (@lem1532229) (@lem1532228 x)). Qed.
Lemma lem1532231 (x : real) : (term94 x) = (term84 x).
Proof. exact (eq_refl (term94 x)). Qed.
Lemma lem1532232 (x : real) : (term95 x) = (term85 x).
Proof. exact (MK_COMB (@lem1532230 x) (@lem1532231 x)). Qed.
Lemma lem1532233 : term96 = term86.
Proof. exact (fun_ext (fun x : real => @lem1532232 x)). Qed.
Lemma lem1532234 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532235 : term88 = term87.
Proof. exact (MK_COMB (@lem1532234) (@lem1532233)). Qed.
Lemma lem1532236 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1532237 : term97 = term98.
Proof. exact (MK_COMB (@lem1532236) (@lem1532235)). Qed.
Lemma lem1532238 (x : real) : (term92 x) = (term79 x).
Proof. exact (eq_refl (term92 x)). Qed.
Lemma lem1532239 : term99 = term90.
Proof. exact (fun_ext (fun x : real => @lem1532238 x)). Qed.
Lemma lem1532240 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532241 : term100 = term101.
Proof. exact (MK_COMB (@lem1532240) (@lem1532239)). Qed.
Lemma lem1532242 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1532243 : term102 = term103.
Proof. exact (MK_COMB (@lem1532242) (@lem1532241)). Qed.
Lemma lem1532244 (x : real) : (term94 x) = (term84 x).
Proof. exact (eq_refl (term94 x)). Qed.
Lemma lem1532245 : term104 = term91.
Proof. exact (fun_ext (fun x : real => @lem1532244 x)). Qed.
Lemma lem1532246 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532247 : term105 = term106.
Proof. exact (MK_COMB (@lem1532246) (@lem1532245)). Qed.
Lemma lem1532248 : term89 = term107.
Proof. exact (MK_COMB (@lem1532243) (@lem1532247)). Qed.
Lemma lem1532249 : (term88 = term89) = (term87 = term107).
Proof. exact (MK_COMB (@lem1532237) (@lem1532248)). Qed.
Lemma lem1532250 : term87 = term107.
Proof. exact (EQ_MP (@lem1532249) (@lem1532227)). Qed.
Lemma lem1532267 : term61 = term107.
Proof. exact (TRANS (@lem1532223) (@lem1532250)). Qed.
Lemma lem1532269 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term63 A P Q) = (term62 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1532270 (P : real -> Prop) (Q : real -> Prop) : (term65 P Q) = (term64 P Q).
Proof. exact (@lem1532269 real P Q). Qed.
Lemma lem1532271 : term89 = term88.
Proof. exact (@lem1532270 term90 term91). Qed.
Lemma lem1532272 (x : real) : (term92 x) = (term79 x).
Proof. exact (eq_refl (term92 x)). Qed.
Lemma lem1532273 : term99 = term90.
Proof. exact (fun_ext (fun x : real => @lem1532272 x)). Qed.
Lemma lem1532274 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532275 : term100 = term101.
Proof. exact (MK_COMB (@lem1532274) (@lem1532273)). Qed.
Lemma lem1532276 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1532277 : term102 = term103.
Proof. exact (MK_COMB (@lem1532276) (@lem1532275)). Qed.
Lemma lem1532278 (x : real) : (term94 x) = (term84 x).
Proof. exact (eq_refl (term94 x)). Qed.
Lemma lem1532279 : term104 = term91.
Proof. exact (fun_ext (fun x : real => @lem1532278 x)). Qed.
Lemma lem1532280 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532281 : term105 = term106.
Proof. exact (MK_COMB (@lem1532280) (@lem1532279)). Qed.
Lemma lem1532282 : term89 = term107.
Proof. exact (MK_COMB (@lem1532277) (@lem1532281)). Qed.
Lemma lem1532283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1532284 : term108 = term109.
Proof. exact (MK_COMB (@lem1532283) (@lem1532282)). Qed.
Lemma lem1532285 (x : real) : (term92 x) = (term79 x).
Proof. exact (eq_refl (term92 x)). Qed.
Lemma lem1532286 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1532287 (x : real) : (term93 x) = (term81 x).
Proof. exact (MK_COMB (@lem1532286) (@lem1532285 x)). Qed.
Lemma lem1532288 (x : real) : (term94 x) = (term84 x).
Proof. exact (eq_refl (term94 x)). Qed.
Lemma lem1532289 (x : real) : (term95 x) = (term85 x).
Proof. exact (MK_COMB (@lem1532287 x) (@lem1532288 x)). Qed.
Lemma lem1532290 : term96 = term86.
Proof. exact (fun_ext (fun x : real => @lem1532289 x)). Qed.
Lemma lem1532291 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532292 : term88 = term87.
Proof. exact (MK_COMB (@lem1532291) (@lem1532290)). Qed.
Lemma lem1532293 : (term89 = term88) = (term107 = term87).
Proof. exact (MK_COMB (@lem1532284) (@lem1532292)). Qed.
Lemma lem1532294 : term107 = term87.
Proof. exact (EQ_MP (@lem1532293) (@lem1532271)). Qed.
Lemma lem1532296 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term63 A P Q) = (term62 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1532297 (P : real -> Prop) (Q : real -> Prop) : (term65 P Q) = (term64 P Q).
Proof. exact (@lem1532296 real P Q). Qed.
Lemma lem1532298 (x : real) : (term67 x) = (term66 x).
Proof. exact (@lem1532297 (term68 x) (term69 x)). Qed.
Lemma lem1532299 (y : real) (x : real) : (term70 x y) = (term54 y x).
Proof. exact (eq_refl (term70 x y)). Qed.
Lemma lem1532300 (x : real) : (term77 x) = (term68 x).
Proof. exact (fun_ext (fun y : real => @lem1532299 y x)). Qed.
Lemma lem1532301 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532302 (x : real) : (term78 x) = (term79 x).
Proof. exact (MK_COMB (@lem1532301) (@lem1532300 x)). Qed.
Lemma lem1532303 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1532304 (x : real) : (term80 x) = (term81 x).
Proof. exact (MK_COMB (@lem1532303) (@lem1532302 x)). Qed.
Lemma lem1532305 (y : real) (x : real) : (term72 x y) = (term50 y x).
Proof. exact (eq_refl (term72 x y)). Qed.
Lemma lem1532306 (x : real) : (term82 x) = (term69 x).
Proof. exact (fun_ext (fun y : real => @lem1532305 y x)). Qed.
Lemma lem1532307 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532308 (x : real) : (term83 x) = (term84 x).
Proof. exact (MK_COMB (@lem1532307) (@lem1532306 x)). Qed.
Lemma lem1532309 (x : real) : (term67 x) = (term85 x).
Proof. exact (MK_COMB (@lem1532304 x) (@lem1532308 x)). Qed.
Lemma lem1532310 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1532311 (x : real) : (term110 x) = (term111 x).
Proof. exact (MK_COMB (@lem1532310) (@lem1532309 x)). Qed.
Lemma lem1532312 (y : real) (x : real) : (term70 x y) = (term54 y x).
Proof. exact (eq_refl (term70 x y)). Qed.
Lemma lem1532313 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1532314 (y : real) (x : real) : (term71 x y) = (term56 y x).
Proof. exact (MK_COMB (@lem1532313) (@lem1532312 y x)). Qed.
Lemma lem1532315 (y : real) (x : real) : (term72 x y) = (term50 y x).
Proof. exact (eq_refl (term72 x y)). Qed.
Lemma lem1532316 (y : real) (x : real) : (term73 x y) = (term57 y x).
Proof. exact (MK_COMB (@lem1532314 y x) (@lem1532315 y x)). Qed.
Lemma lem1532317 (x : real) : (term74 x) = (term58 x).
Proof. exact (fun_ext (fun y : real => @lem1532316 y x)). Qed.
Lemma lem1532318 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532319 (x : real) : (term66 x) = (term59 x).
Proof. exact (MK_COMB (@lem1532318) (@lem1532317 x)). Qed.
Lemma lem1532320 (x : real) : ((term67 x) = (term66 x)) = ((term85 x) = (term59 x)).
Proof. exact (MK_COMB (@lem1532311 x) (@lem1532319 x)). Qed.
Lemma lem1532321 (x : real) : (term85 x) = (term59 x).
Proof. exact (EQ_MP (@lem1532320 x) (@lem1532298 x)). Qed.
Lemma lem1532322 : term86 = term60.
Proof. exact (fun_ext (fun x : real => @lem1532321 x)). Qed.
Lemma lem1532323 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532324 : term87 = term61.
Proof. exact (MK_COMB (@lem1532323) (@lem1532322)). Qed.
Lemma lem1532325 : term107 = term61.
Proof. exact (TRANS (@lem1532294) (@lem1532324)). Qed.
Lemma lem1532326 : term61 = term61.
Proof. exact (TRANS (@lem1532267) (@lem1532325)). Qed.
Lemma lem1532329 : term12 = term61.
Proof. exact (TRANS (@lem1532181) (@lem1532326)). Qed.
Lemma lem1532334 (y : real) (x : real) : (term57 y x) = (term57 y x).
Proof. exact (eq_refl (term57 y x)). Qed.
Lemma lem1532335 (x : real) : (term58 x) = (term58 x).
Proof. exact (fun_ext (fun y : real => @lem1532334 y x)). Qed.
Lemma lem1532336 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532337 (x : real) : (term59 x) = (term59 x).
Proof. exact (MK_COMB (@lem1532336) (@lem1532335 x)). Qed.
Lemma lem1532338 : term60 = term60.
Proof. exact (fun_ext (fun x : real => @lem1532337 x)). Qed.
Lemma lem1532339 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1532340 : term61 = term61.
Proof. exact (MK_COMB (@lem1532339) (@lem1532338)). Qed.
Lemma lem1532341 : term12 = term61.
Proof. exact (TRANS (@lem1532329) (@lem1532340)). Qed.
Lemma lem1532343 (a : real) (x : real) (r : real) : (term112 a x r) = (term113 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1532344 (y : real) (x : real) : (term54 y x) = (term114 y x).
Proof. exact (@lem1532343 (term6 x y) (real_sub y x) term48). Qed.
Lemma lem1532350 (y : real) (x : real) : (real_sub y x) = (term115 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1532355 (x : real) (y : real) : (term115 y x) = (term116 x y).
Proof. exact (@lem1483488 (term117 x) y). Qed.
Lemma lem1532357 (x : real) (y : real) : (real_sub y x) = (term116 x y).
Proof. exact (TRANS (@lem1532350 y x) (@lem1532355 x y)). Qed.
Lemma lem1532360 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1532361 (x : real) (y : real) : (term118 y x) = (term119 x y).
Proof. exact (MK_COMB (@lem1532360) (@lem1532357 x y)). Qed.
Lemma lem1532362 (x : real) (y : real) : (term119 x y) = (term116 x y).
Proof. exact (@lem1483460 (term116 x y)). Qed.
Lemma lem1532363 (x : real) (y : real) : (term118 y x) = (term116 x y).
Proof. exact (TRANS (@lem1532361 x y) (@lem1532362 x y)). Qed.
Lemma lem1532366 (x : real) (y : real) : (term120 x y) = (term120 x y).
Proof. exact (eq_refl (term120 x y)). Qed.
Lemma lem1532367 (x : real) (y : real) : (term121 y x) = (term122 x y).
Proof. exact (MK_COMB (@lem1532366 x y) (@lem1532363 x y)). Qed.
Lemma lem1532368 (x : real) (y : real) : (term122 x y) = (term123 x y).
Proof. exact (@lem1483484 (term117 x) (term6 x y) y). Qed.
Lemma lem1532369 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (@lem1483488 y (term6 x y)). Qed.
Lemma lem1532370 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1532371 (x : real) (y : real) : (term123 x y) = (term127 x y).
Proof. exact (MK_COMB (@lem1532370 x) (@lem1532369 x y)). Qed.
Lemma lem1532372 (x : real) (y : real) : (term122 x y) = (term127 x y).
Proof. exact (TRANS (@lem1532368 x y) (@lem1532371 x y)). Qed.
Lemma lem1532373 (x : real) (y : real) : (term121 y x) = (term127 x y).
Proof. exact (TRANS (@lem1532367 x y) (@lem1532372 x y)). Qed.
Lemma lem1532374 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1532375 (x : real) (y : real) : (term128 y x) = (term129 x y).
Proof. exact (MK_COMB (@lem1532374) (@lem1532373 x y)). Qed.
Lemma lem1532376 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532377 (x : real) (y : real) : (term130 y x) = (term131 x y).
Proof. exact (MK_COMB (@lem1532375 x y) (@lem1532376)). Qed.
Lemma lem1532383 (y : real) (x : real) : (real_sub y x) = (term115 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1532388 (x : real) (y : real) : (term115 y x) = (term116 x y).
Proof. exact (@lem1483488 (term117 x) y). Qed.
Lemma lem1532390 (x : real) (y : real) : (real_sub y x) = (term116 x y).
Proof. exact (TRANS (@lem1532383 y x) (@lem1532388 x y)). Qed.
Lemma lem1532393 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1532394 (x : real) (y : real) : (term133 y x) = (term134 x y).
Proof. exact (MK_COMB (@lem1532393) (@lem1532390 x y)). Qed.
Lemma lem1532395 (x : real) (y : real) : (term134 x y) = (term135 x y).
Proof. exact (@lem1483508 (term117 x) term28 y). Qed.
Lemma lem1532396 (y : real) : (term117 y) = (term117 y).
Proof. exact (eq_refl (term117 y)). Qed.
Lemma lem1532397 (x : real) : (term136 x) = (term137 x).
Proof. exact (@lem1483476 term28 term28 x). Qed.
Lemma lem1532399 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1532400 : term34 = term35.
Proof. exact (@lem1532399 term36 term36). Qed.
Lemma lem1532401 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1532402 : term38 = term36.
Proof. exact (EQ_MP (@lem1532401) (@lem940073)). Qed.
Lemma lem1532403 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1532404 : term35 = term39.
Proof. exact (MK_COMB (@lem1532403) (@lem1532402)). Qed.
Lemma lem1532405 : term34 = term39.
Proof. exact (TRANS (@lem1532400) (@lem1532404)). Qed.
Lemma lem1532406 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1532407 : term40 = term41.
Proof. exact (MK_COMB (@lem1532406) (@lem1532405)). Qed.
Lemma lem1532408 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1532409 (x : real) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem1532407) (@lem1532408 x)). Qed.
Lemma lem1532410 (x : real) : (term136 x) = (term138 x).
Proof. exact (TRANS (@lem1532397 x) (@lem1532409 x)). Qed.
Lemma lem1532411 (x : real) : (term138 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1532412 (x : real) : (term136 x) = x.
Proof. exact (TRANS (@lem1532410 x) (@lem1532411 x)). Qed.
Lemma lem1532413 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1532414 (x : real) : (term139 x) = (real_add x).
Proof. exact (MK_COMB (@lem1532413) (@lem1532412 x)). Qed.
Lemma lem1532415 (x : real) (y : real) : (term135 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem1532414 x) (@lem1532396 y)). Qed.
Lemma lem1532416 (x : real) (y : real) : (term134 x y) = (term115 x y).
Proof. exact (TRANS (@lem1532395 x y) (@lem1532415 x y)). Qed.
Lemma lem1532417 (x : real) (y : real) : (term133 y x) = (term115 x y).
Proof. exact (TRANS (@lem1532394 x y) (@lem1532416 x y)). Qed.
Lemma lem1532420 (x : real) (y : real) : (term120 x y) = (term120 x y).
Proof. exact (eq_refl (term120 x y)). Qed.
Lemma lem1532421 (x : real) (y : real) : (term140 y x) = (term141 x y).
Proof. exact (MK_COMB (@lem1532420 x y) (@lem1532417 x y)). Qed.
Lemma lem1532422 (x : real) (y : real) : (term141 x y) = (term142 x y).
Proof. exact (@lem1483484 x (term6 x y) (term117 y)). Qed.
Lemma lem1532423 (x : real) (y : real) : (term143 x y) = (term144 x y).
Proof. exact (@lem1483488 (term117 y) (term6 x y)). Qed.
Lemma lem1532424 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1532425 (x : real) (y : real) : (term142 x y) = (term145 x y).
Proof. exact (MK_COMB (@lem1532424 x) (@lem1532423 x y)). Qed.
Lemma lem1532426 (x : real) (y : real) : (term141 x y) = (term145 x y).
Proof. exact (TRANS (@lem1532422 x y) (@lem1532425 x y)). Qed.
Lemma lem1532427 (x : real) (y : real) : (term140 y x) = (term145 x y).
Proof. exact (TRANS (@lem1532421 x y) (@lem1532426 x y)). Qed.
Lemma lem1532428 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1532429 (x : real) (y : real) : (term146 y x) = (term147 x y).
Proof. exact (MK_COMB (@lem1532428) (@lem1532427 x y)). Qed.
Lemma lem1532430 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532431 (x : real) (y : real) : (term148 y x) = (term149 x y).
Proof. exact (MK_COMB (@lem1532429 x y) (@lem1532430)). Qed.
Lemma lem1532432 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1532433 (x : real) (y : real) : (term150 y x) = (term151 x y).
Proof. exact (MK_COMB (@lem1532432) (@lem1532431 x y)). Qed.
Lemma lem1532434 (x : real) (y : real) : (term114 y x) = (term152 x y).
Proof. exact (MK_COMB (@lem1532433 x y) (@lem1532377 x y)). Qed.
Lemma lem1532435 (x : real) (y : real) : (term54 y x) = (term152 x y).
Proof. exact (TRANS (@lem1532344 y x) (@lem1532434 x y)). Qed.
Lemma lem1532436 (x : real) (y : real) : (term153 x y) = (term152 x y).
Proof. exact (eq_refl (term153 x y)). Qed.
Lemma lem1532437 (x : real) (y : real) : (term152 x y) = (term153 x y).
Proof. exact (SYM (@lem1532436 x y)). Qed.
Lemma lem1532438 (x : real) (y : real) : (term153 x y) = (term154 x y).
Proof. exact (@lem1482981 (term155 x y) (real_sub x y)). Qed.
Lemma lem1532439 (x : real) (y : real) : (term152 x y) = (term154 x y).
Proof. exact (TRANS (@lem1532437 x y) (@lem1532438 x y)). Qed.
Lemma lem1532440 (x : real) (y : real) : (term156 x y) = (term157 x y).
Proof. exact (eq_refl (term156 x y)). Qed.
Lemma lem1532441 (x : real) (y : real) : (term158 x y) = (term158 x y).
Proof. exact (eq_refl (term158 x y)). Qed.
Lemma lem1532442 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1532441 x y) (@lem1532440 x y)). Qed.
Lemma lem1532443 (x : real) (y : real) : (term161 x y) = (term162 x y).
Proof. exact (eq_refl (term161 x y)). Qed.
Lemma lem1532444 (x : real) (y : real) : (term163 x y) = (term163 x y).
Proof. exact (eq_refl (term163 x y)). Qed.
Lemma lem1532445 (x : real) (y : real) : (term164 x y) = (term165 x y).
Proof. exact (MK_COMB (@lem1532444 x y) (@lem1532443 x y)). Qed.
Lemma lem1532446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1532447 (x : real) (y : real) : (term166 x y) = (term167 x y).
Proof. exact (MK_COMB (@lem1532446) (@lem1532445 x y)). Qed.
Lemma lem1532448 (x : real) (y : real) : (term154 x y) = (term168 x y).
Proof. exact (MK_COMB (@lem1532447 x y) (@lem1532442 x y)). Qed.
Lemma lem1532449 (x : real) (y : real) : (term169 x y) = (term169 x y).
Proof. exact (eq_refl (term169 x y)). Qed.
Lemma lem1532450 (x : real) (y : real) : ((term152 x y) = (term154 x y)) = ((term152 x y) = (term168 x y)).
Proof. exact (MK_COMB (@lem1532449 x y) (@lem1532448 x y)). Qed.
Lemma lem1532451 (x : real) (y : real) : (term152 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem1532450 x y) (@lem1532439 x y)). Qed.
Lemma lem1532452 (x : real) (y : real) : (term170 x y) = (term171 x y).
Proof. exact (@lem1483527 (real_sub x y) term48). Qed.
Lemma lem1532453 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532466 (x : real) (y : real) : (real_sub x y) = (term115 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1532467 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1532468 (x : real) (y : real) : (term172 x y) = (term173 x y).
Proof. exact (MK_COMB (@lem1532467) (@lem1532466 x y)). Qed.
Lemma lem1532469 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (MK_COMB (@lem1532468 x y) (@lem1532453)). Qed.
Lemma lem1532470 (x : real) (y : real) : (term175 x y) = (term176 x y).
Proof. exact (@lem1483519 (term115 x y) term48). Qed.
Lemma lem1532472 (x : nat) : (term177 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1532473 : term178 = term48.
Proof. exact (@lem1532472 term36). Qed.
Lemma lem1532474 (x : real) (y : real) : (term179 x y) = (term179 x y).
Proof. exact (eq_refl (term179 x y)). Qed.
Lemma lem1532475 (x : real) (y : real) : (term176 x y) = (term180 x y).
Proof. exact (MK_COMB (@lem1532474 x y) (@lem1532473)). Qed.
Lemma lem1532476 (x : real) (y : real) : (term180 x y) = (term115 x y).
Proof. exact (@lem1483450 (term115 x y)). Qed.
Lemma lem1532477 (x : real) (y : real) : (term176 x y) = (term115 x y).
Proof. exact (TRANS (@lem1532475 x y) (@lem1532476 x y)). Qed.
Lemma lem1532478 (x : real) (y : real) : (term175 x y) = (term115 x y).
Proof. exact (TRANS (@lem1532470 x y) (@lem1532477 x y)). Qed.
Lemma lem1532479 (x : real) (y : real) : (term174 x y) = (term115 x y).
Proof. exact (TRANS (@lem1532469 x y) (@lem1532478 x y)). Qed.
Lemma lem1532480 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1532481 (x : real) (y : real) : (term181 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1532480) (@lem1532479 x y)). Qed.
Lemma lem1532482 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532483 (x : real) (y : real) : (term171 x y) = (term183 x y).
Proof. exact (MK_COMB (@lem1532481 x y) (@lem1532482)). Qed.
Lemma lem1532484 (x : real) (y : real) : (term170 x y) = (term183 x y).
Proof. exact (TRANS (@lem1532452 x y) (@lem1532483 x y)). Qed.
Lemma lem1532485 (x : real) (y : real) : (term184 x y) = (term185 x y).
Proof. exact (@lem1483525 (term186 x y) term48). Qed.
Lemma lem1532486 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532499 (x : real) (y : real) : (real_sub x y) = (term115 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1532508 (y : real) : (term126 y) = (term126 y).
Proof. exact (eq_refl (term126 y)). Qed.
Lemma lem1532509 (x : real) (y : real) : (term187 x y) = (term188 x y).
Proof. exact (MK_COMB (@lem1532508 y) (@lem1532499 x y)). Qed.
Lemma lem1532510 (x : real) (y : real) : (term188 x y) = (term189 x y).
Proof. exact (@lem1483484 x (term117 y) (term117 y)). Qed.
Lemma lem1532511 (y : real) : (term190 y) = (term191 y).
Proof. exact (@lem1483438 term28 term28 y). Qed.
Lemma lem1532512 : term192 = term193.
Proof. exact (@lem1367763 term36 term36). Qed.
Lemma lem1532513 : term194 = term195.
Proof. exact (@lem706885). Qed.
Lemma lem1532514 : (term194 = term195) = (term196 = term197).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term195). Qed.
Lemma lem1532515 : term196 = term197.
Proof. exact (EQ_MP (@lem1532514) (@lem1532513)). Qed.
Lemma lem1532516 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1532517 : term198 = term199.
Proof. exact (MK_COMB (@lem1532516) (@lem1532515)). Qed.
Lemma lem1532518 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1532519 : term193 = term200.
Proof. exact (MK_COMB (@lem1532518) (@lem1532517)). Qed.
Lemma lem1532520 : term192 = term200.
Proof. exact (TRANS (@lem1532512) (@lem1532519)). Qed.
Lemma lem1532521 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1532522 : term201 = term202.
Proof. exact (MK_COMB (@lem1532521) (@lem1532520)). Qed.
Lemma lem1532523 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1532524 (y : real) : (term191 y) = (term203 y).
Proof. exact (MK_COMB (@lem1532522) (@lem1532523 y)). Qed.
Lemma lem1532525 (y : real) : (term190 y) = (term203 y).
Proof. exact (TRANS (@lem1532511 y) (@lem1532524 y)). Qed.
Lemma lem1532526 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1532527 (x : real) (y : real) : (term189 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem1532526 x) (@lem1532525 y)). Qed.
Lemma lem1532528 (x : real) (y : real) : (term188 x y) = (term204 x y).
Proof. exact (TRANS (@lem1532510 x y) (@lem1532527 x y)). Qed.
Lemma lem1532529 (x : real) (y : real) : (term187 x y) = (term204 x y).
Proof. exact (TRANS (@lem1532509 x y) (@lem1532528 x y)). Qed.
Lemma lem1532532 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1532533 (x : real) (y : real) : (term186 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem1532532 x) (@lem1532529 x y)). Qed.
Lemma lem1532534 (x : real) (y : real) : (term205 x y) = (term206 x y).
Proof. exact (@lem1483490 x x (term203 y)). Qed.
Lemma lem1532535 (x : real) : (real_add x x) = (term207 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1532536 : term208 = term198.
Proof. exact (@lem1367770 term36 term36). Qed.
Lemma lem1532537 : term194 = term195.
Proof. exact (@lem706885). Qed.
Lemma lem1532538 : (term194 = term195) = (term196 = term197).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term195). Qed.
Lemma lem1532539 : term196 = term197.
Proof. exact (EQ_MP (@lem1532538) (@lem1532537)). Qed.
Lemma lem1532540 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1532541 : term198 = term199.
Proof. exact (MK_COMB (@lem1532540) (@lem1532539)). Qed.
Lemma lem1532542 : term208 = term199.
Proof. exact (TRANS (@lem1532536) (@lem1532541)). Qed.
Lemma lem1532543 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1532544 : term209 = term210.
Proof. exact (MK_COMB (@lem1532543) (@lem1532542)). Qed.
Lemma lem1532545 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1532546 (x : real) : (term207 x) = (term211 x).
Proof. exact (MK_COMB (@lem1532544) (@lem1532545 x)). Qed.
Lemma lem1532547 (x : real) : (real_add x x) = (term211 x).
Proof. exact (TRANS (@lem1532535 x) (@lem1532546 x)). Qed.
Lemma lem1532548 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1532549 (x : real) : (term212 x) = (term213 x).
Proof. exact (MK_COMB (@lem1532548) (@lem1532547 x)). Qed.
Lemma lem1532550 (y : real) : (term203 y) = (term203 y).
Proof. exact (eq_refl (term203 y)). Qed.
Lemma lem1532551 (x : real) (y : real) : (term206 x y) = (term214 x y).
Proof. exact (MK_COMB (@lem1532549 x) (@lem1532550 y)). Qed.
Lemma lem1532552 (x : real) (y : real) : (term205 x y) = (term214 x y).
Proof. exact (TRANS (@lem1532534 x y) (@lem1532551 x y)). Qed.
Lemma lem1532553 (x : real) (y : real) : (term186 x y) = (term214 x y).
Proof. exact (TRANS (@lem1532533 x y) (@lem1532552 x y)). Qed.
Lemma lem1532554 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1532555 (x : real) (y : real) : (term215 x y) = (term216 x y).
Proof. exact (MK_COMB (@lem1532554) (@lem1532553 x y)). Qed.
Lemma lem1532556 (x : real) (y : real) : (term217 x y) = (term218 x y).
Proof. exact (MK_COMB (@lem1532555 x y) (@lem1532486)). Qed.
Lemma lem1532557 (x : real) (y : real) : (term218 x y) = (term219 x y).
Proof. exact (@lem1483519 (term214 x y) term48). Qed.
Lemma lem1532559 (x : nat) : (term177 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1532560 : term178 = term48.
Proof. exact (@lem1532559 term36). Qed.
Lemma lem1532561 (x : real) (y : real) : (term220 x y) = (term220 x y).
Proof. exact (eq_refl (term220 x y)). Qed.
Lemma lem1532562 (x : real) (y : real) : (term219 x y) = (term221 x y).
Proof. exact (MK_COMB (@lem1532561 x y) (@lem1532560)). Qed.
Lemma lem1532563 (x : real) (y : real) : (term221 x y) = (term214 x y).
Proof. exact (@lem1483450 (term214 x y)). Qed.
Lemma lem1532564 (x : real) (y : real) : (term219 x y) = (term214 x y).
Proof. exact (TRANS (@lem1532562 x y) (@lem1532563 x y)). Qed.
Lemma lem1532565 (x : real) (y : real) : (term218 x y) = (term214 x y).
Proof. exact (TRANS (@lem1532557 x y) (@lem1532564 x y)). Qed.
Lemma lem1532566 (x : real) (y : real) : (term217 x y) = (term214 x y).
Proof. exact (TRANS (@lem1532556 x y) (@lem1532565 x y)). Qed.
Lemma lem1532567 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1532568 (x : real) (y : real) : (term222 x y) = (term223 x y).
Proof. exact (MK_COMB (@lem1532567) (@lem1532566 x y)). Qed.
Lemma lem1532569 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532570 (x : real) (y : real) : (term185 x y) = (term224 x y).
Proof. exact (MK_COMB (@lem1532568 x y) (@lem1532569)). Qed.
Lemma lem1532571 (x : real) (y : real) : (term184 x y) = (term224 x y).
Proof. exact (TRANS (@lem1532485 x y) (@lem1532570 x y)). Qed.
Lemma lem1532572 (x : real) (y : real) : (term225 x y) = (term226 x y).
Proof. exact (@lem1483525 (term227 x y) term48). Qed.
Lemma lem1532573 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532586 (x : real) (y : real) : (real_sub x y) = (term115 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1532589 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1532590 (x : real) (y : real) : (term228 x y) = (term229 x y).
Proof. exact (MK_COMB (@lem1532589 y) (@lem1532586 x y)). Qed.
Lemma lem1532591 (x : real) (y : real) : (term229 x y) = (term230 x y).
Proof. exact (@lem1483484 x y (term117 y)). Qed.
Lemma lem1532592 (y : real) : (term231 y) = (term232 y).
Proof. exact (@lem1483442 term28 y). Qed.
Lemma lem1532594 (m : nat) : (term233 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1532595 : term234 = term48.
Proof. exact (@lem1532594 term36). Qed.
Lemma lem1532596 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1532597 : term235 = term236.
Proof. exact (MK_COMB (@lem1532596) (@lem1532595)). Qed.
Lemma lem1532598 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1532599 (y : real) : (term232 y) = (term237 y).
Proof. exact (MK_COMB (@lem1532597) (@lem1532598 y)). Qed.
Lemma lem1532600 (y : real) : (term231 y) = (term237 y).
Proof. exact (TRANS (@lem1532592 y) (@lem1532599 y)). Qed.
Lemma lem1532601 (y : real) : (term237 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1532602 (y : real) : (term231 y) = term48.
Proof. exact (TRANS (@lem1532600 y) (@lem1532601 y)). Qed.
Lemma lem1532603 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1532604 (y : real) (x : real) : (term230 x y) = (term238 x).
Proof. exact (MK_COMB (@lem1532603 x) (@lem1532602 y)). Qed.
Lemma lem1532605 (y : real) (x : real) : (term229 x y) = (term238 x).
Proof. exact (TRANS (@lem1532591 x y) (@lem1532604 y x)). Qed.
Lemma lem1532606 (x : real) : (term238 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1532607 (y : real) (x : real) : (term229 x y) = x.
Proof. exact (TRANS (@lem1532605 y x) (@lem1532606 x)). Qed.
Lemma lem1532608 (y : real) (x : real) : (term228 x y) = x.
Proof. exact (TRANS (@lem1532590 x y) (@lem1532607 y x)). Qed.
Lemma lem1532617 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1532618 (y : real) (x : real) : (term227 x y) = (term239 x).
Proof. exact (MK_COMB (@lem1532617 x) (@lem1532608 y x)). Qed.
Lemma lem1532619 (x : real) : (term239 x) = (term232 x).
Proof. exact (@lem1483440 term28 x). Qed.
Lemma lem1532621 (m : nat) : (term233 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1532622 : term234 = term48.
Proof. exact (@lem1532621 term36). Qed.
Lemma lem1532623 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1532624 : term235 = term236.
Proof. exact (MK_COMB (@lem1532623) (@lem1532622)). Qed.
Lemma lem1532625 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1532626 (x : real) : (term232 x) = (term237 x).
Proof. exact (MK_COMB (@lem1532624) (@lem1532625 x)). Qed.
Lemma lem1532627 (x : real) : (term239 x) = (term237 x).
Proof. exact (TRANS (@lem1532619 x) (@lem1532626 x)). Qed.
Lemma lem1532628 (x : real) : (term237 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1532629 (x : real) : (term239 x) = term48.
Proof. exact (TRANS (@lem1532627 x) (@lem1532628 x)). Qed.
Lemma lem1532630 (x : real) (y : real) : (term227 x y) = term48.
Proof. exact (TRANS (@lem1532618 y x) (@lem1532629 x)). Qed.
Lemma lem1532631 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1532632 (x : real) (y : real) : (term240 x y) = term241.
Proof. exact (MK_COMB (@lem1532631) (@lem1532630 x y)). Qed.
Lemma lem1532633 (x : real) (y : real) : (term242 x y) = term243.
Proof. exact (MK_COMB (@lem1532632 x y) (@lem1532573)). Qed.
Lemma lem1532634 : term243 = term244.
Proof. exact (@lem1483519 term48 term48). Qed.
Lemma lem1532636 (x : nat) : (term177 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1532637 : term178 = term48.
Proof. exact (@lem1532636 term36). Qed.
Lemma lem1532638 : term245 = term245.
Proof. exact (eq_refl term245). Qed.
Lemma lem1532639 : term244 = term246.
Proof. exact (MK_COMB (@lem1532638) (@lem1532637)). Qed.
Lemma lem1532640 : term246 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1532641 : term244 = term48.
Proof. exact (TRANS (@lem1532639) (@lem1532640)). Qed.
Lemma lem1532642 : term243 = term48.
Proof. exact (TRANS (@lem1532634) (@lem1532641)). Qed.
Lemma lem1532643 (x : real) (y : real) : (term242 x y) = term48.
Proof. exact (TRANS (@lem1532633 x y) (@lem1532642)). Qed.
Lemma lem1532644 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1532645 (x : real) (y : real) : (term247 x y) = term248.
Proof. exact (MK_COMB (@lem1532644) (@lem1532643 x y)). Qed.
Lemma lem1532646 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532647 (x : real) (y : real) : (term226 x y) = term249.
Proof. exact (MK_COMB (@lem1532645 x y) (@lem1532646)). Qed.
Lemma lem1532648 (x : real) (y : real) : (term225 x y) = term249.
Proof. exact (TRANS (@lem1532572 x y) (@lem1532647 x y)). Qed.
Lemma lem1532649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1532650 (x : real) (y : real) : (term250 x y) = (term251 x y).
Proof. exact (MK_COMB (@lem1532649) (@lem1532571 x y)). Qed.
Lemma lem1532651 (x : real) (y : real) : (term162 x y) = (term252 x y).
Proof. exact (MK_COMB (@lem1532650 x y) (@lem1532648 x y)). Qed.
Lemma lem1532652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1532653 (x : real) (y : real) : (term163 x y) = (term253 x y).
Proof. exact (MK_COMB (@lem1532652) (@lem1532484 x y)). Qed.
Lemma lem1532654 (x : real) (y : real) : (term165 x y) = (term254 x y).
Proof. exact (MK_COMB (@lem1532653 x y) (@lem1532651 x y)). Qed.
Lemma lem1532655 (x : real) (y : real) : (term255 x y) = (term256 x y).
Proof. exact (@lem1483525 term48 (real_sub x y)). Qed.
Lemma lem1532668 (x : real) (y : real) : (real_sub x y) = (term115 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1532671 : term241 = term241.
Proof. exact (eq_refl term241). Qed.
Lemma lem1532672 (x : real) (y : real) : (term257 x y) = (term258 x y).
Proof. exact (MK_COMB (@lem1532671) (@lem1532668 x y)). Qed.
Lemma lem1532673 (x : real) (y : real) : (term258 x y) = (term259 x y).
Proof. exact (@lem1483519 term48 (term115 x y)). Qed.
Lemma lem1532674 (x : real) (y : real) : (term260 x y) = (term261 x y).
Proof. exact (@lem1483508 x term28 (term117 y)). Qed.
Lemma lem1532675 (y : real) : (term136 y) = (term137 y).
Proof. exact (@lem1483476 term28 term28 y). Qed.
Lemma lem1532677 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1532678 : term34 = term35.
Proof. exact (@lem1532677 term36 term36). Qed.
Lemma lem1532679 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1532680 : term38 = term36.
Proof. exact (EQ_MP (@lem1532679) (@lem940073)). Qed.
Lemma lem1532681 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1532682 : term35 = term39.
Proof. exact (MK_COMB (@lem1532681) (@lem1532680)). Qed.
Lemma lem1532683 : term34 = term39.
Proof. exact (TRANS (@lem1532678) (@lem1532682)). Qed.
Lemma lem1532684 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1532685 : term40 = term41.
Proof. exact (MK_COMB (@lem1532684) (@lem1532683)). Qed.
Lemma lem1532686 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1532687 (y : real) : (term137 y) = (term138 y).
Proof. exact (MK_COMB (@lem1532685) (@lem1532686 y)). Qed.
Lemma lem1532688 (y : real) : (term136 y) = (term138 y).
Proof. exact (TRANS (@lem1532675 y) (@lem1532687 y)). Qed.
Lemma lem1532689 (y : real) : (term138 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1532690 (y : real) : (term136 y) = y.
Proof. exact (TRANS (@lem1532688 y) (@lem1532689 y)). Qed.
Lemma lem1532693 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1532694 (x : real) (y : real) : (term261 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1532693 x) (@lem1532690 y)). Qed.
Lemma lem1532695 (x : real) (y : real) : (term260 x y) = (term116 x y).
Proof. exact (TRANS (@lem1532674 x y) (@lem1532694 x y)). Qed.
Lemma lem1532696 : term245 = term245.
Proof. exact (eq_refl term245). Qed.
Lemma lem1532697 (x : real) (y : real) : (term259 x y) = (term262 x y).
Proof. exact (MK_COMB (@lem1532696) (@lem1532695 x y)). Qed.
Lemma lem1532698 (x : real) (y : real) : (term262 x y) = (term116 x y).
Proof. exact (@lem1483448 (term116 x y)). Qed.
Lemma lem1532699 (x : real) (y : real) : (term259 x y) = (term116 x y).
Proof. exact (TRANS (@lem1532697 x y) (@lem1532698 x y)). Qed.
Lemma lem1532700 (x : real) (y : real) : (term258 x y) = (term116 x y).
Proof. exact (TRANS (@lem1532673 x y) (@lem1532699 x y)). Qed.
Lemma lem1532701 (x : real) (y : real) : (term257 x y) = (term116 x y).
Proof. exact (TRANS (@lem1532672 x y) (@lem1532700 x y)). Qed.
Lemma lem1532702 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1532703 (x : real) (y : real) : (term263 x y) = (term264 x y).
Proof. exact (MK_COMB (@lem1532702) (@lem1532701 x y)). Qed.
Lemma lem1532704 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532705 (x : real) (y : real) : (term256 x y) = (term265 x y).
Proof. exact (MK_COMB (@lem1532703 x y) (@lem1532704)). Qed.
Lemma lem1532706 (x : real) (y : real) : (term255 x y) = (term265 x y).
Proof. exact (TRANS (@lem1532655 x y) (@lem1532705 x y)). Qed.
Lemma lem1532707 (x : real) (y : real) : (term266 x y) = (term267 x y).
Proof. exact (@lem1483525 (term268 x y) term48). Qed.
Lemma lem1532708 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532721 (x : real) (y : real) : (real_sub x y) = (term115 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1532722 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1532723 (x : real) (y : real) : (term269 x y) = (term270 x y).
Proof. exact (MK_COMB (@lem1532722) (@lem1532721 x y)). Qed.
Lemma lem1532724 (x : real) (y : real) : (term270 x y) = (term260 x y).
Proof. exact (@lem1483512 (term115 x y)). Qed.
Lemma lem1532725 (x : real) (y : real) : (term260 x y) = (term261 x y).
Proof. exact (@lem1483508 x term28 (term117 y)). Qed.
Lemma lem1532726 (y : real) : (term136 y) = (term137 y).
Proof. exact (@lem1483476 term28 term28 y). Qed.
Lemma lem1532728 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1532729 : term34 = term35.
Proof. exact (@lem1532728 term36 term36). Qed.
Lemma lem1532730 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1532731 : term38 = term36.
Proof. exact (EQ_MP (@lem1532730) (@lem940073)). Qed.
Lemma lem1532732 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1532733 : term35 = term39.
Proof. exact (MK_COMB (@lem1532732) (@lem1532731)). Qed.
Lemma lem1532734 : term34 = term39.
Proof. exact (TRANS (@lem1532729) (@lem1532733)). Qed.
Lemma lem1532735 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1532736 : term40 = term41.
Proof. exact (MK_COMB (@lem1532735) (@lem1532734)). Qed.
Lemma lem1532737 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1532738 (y : real) : (term137 y) = (term138 y).
Proof. exact (MK_COMB (@lem1532736) (@lem1532737 y)). Qed.
Lemma lem1532739 (y : real) : (term136 y) = (term138 y).
Proof. exact (TRANS (@lem1532726 y) (@lem1532738 y)). Qed.
Lemma lem1532740 (y : real) : (term138 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1532741 (y : real) : (term136 y) = y.
Proof. exact (TRANS (@lem1532739 y) (@lem1532740 y)). Qed.
Lemma lem1532744 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1532745 (x : real) (y : real) : (term261 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1532744 x) (@lem1532741 y)). Qed.
Lemma lem1532746 (x : real) (y : real) : (term260 x y) = (term116 x y).
Proof. exact (TRANS (@lem1532725 x y) (@lem1532745 x y)). Qed.
Lemma lem1532747 (x : real) (y : real) : (term270 x y) = (term116 x y).
Proof. exact (TRANS (@lem1532724 x y) (@lem1532746 x y)). Qed.
Lemma lem1532748 (x : real) (y : real) : (term269 x y) = (term116 x y).
Proof. exact (TRANS (@lem1532723 x y) (@lem1532747 x y)). Qed.
Lemma lem1532757 (y : real) : (term126 y) = (term126 y).
Proof. exact (eq_refl (term126 y)). Qed.
Lemma lem1532758 (x : real) (y : real) : (term271 x y) = (term272 x y).
Proof. exact (MK_COMB (@lem1532757 y) (@lem1532748 x y)). Qed.
Lemma lem1532759 (x : real) (y : real) : (term272 x y) = (term273 x y).
Proof. exact (@lem1483484 (term117 x) (term117 y) y). Qed.
Lemma lem1532760 (y : real) : (term239 y) = (term232 y).
Proof. exact (@lem1483440 term28 y). Qed.
Lemma lem1532762 (m : nat) : (term233 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1532763 : term234 = term48.
Proof. exact (@lem1532762 term36). Qed.
Lemma lem1532764 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1532765 : term235 = term236.
Proof. exact (MK_COMB (@lem1532764) (@lem1532763)). Qed.
Lemma lem1532766 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1532767 (y : real) : (term232 y) = (term237 y).
Proof. exact (MK_COMB (@lem1532765) (@lem1532766 y)). Qed.
Lemma lem1532768 (y : real) : (term239 y) = (term237 y).
Proof. exact (TRANS (@lem1532760 y) (@lem1532767 y)). Qed.
Lemma lem1532769 (y : real) : (term237 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1532770 (y : real) : (term239 y) = term48.
Proof. exact (TRANS (@lem1532768 y) (@lem1532769 y)). Qed.
Lemma lem1532771 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1532772 (y : real) (x : real) : (term273 x y) = (term274 x).
Proof. exact (MK_COMB (@lem1532771 x) (@lem1532770 y)). Qed.
Lemma lem1532773 (y : real) (x : real) : (term272 x y) = (term274 x).
Proof. exact (TRANS (@lem1532759 x y) (@lem1532772 y x)). Qed.
Lemma lem1532774 (x : real) : (term274 x) = (term117 x).
Proof. exact (@lem1483450 (term117 x)). Qed.
Lemma lem1532775 (y : real) (x : real) : (term272 x y) = (term117 x).
Proof. exact (TRANS (@lem1532773 y x) (@lem1532774 x)). Qed.
Lemma lem1532776 (y : real) (x : real) : (term271 x y) = (term117 x).
Proof. exact (TRANS (@lem1532758 x y) (@lem1532775 y x)). Qed.
Lemma lem1532779 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1532780 (y : real) (x : real) : (term268 x y) = (term231 x).
Proof. exact (MK_COMB (@lem1532779 x) (@lem1532776 y x)). Qed.
Lemma lem1532781 (x : real) : (term231 x) = (term232 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1532783 (m : nat) : (term233 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1532784 : term234 = term48.
Proof. exact (@lem1532783 term36). Qed.
Lemma lem1532785 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1532786 : term235 = term236.
Proof. exact (MK_COMB (@lem1532785) (@lem1532784)). Qed.
Lemma lem1532787 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1532788 (x : real) : (term232 x) = (term237 x).
Proof. exact (MK_COMB (@lem1532786) (@lem1532787 x)). Qed.
Lemma lem1532789 (x : real) : (term231 x) = (term237 x).
Proof. exact (TRANS (@lem1532781 x) (@lem1532788 x)). Qed.
Lemma lem1532790 (x : real) : (term237 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1532791 (x : real) : (term231 x) = term48.
Proof. exact (TRANS (@lem1532789 x) (@lem1532790 x)). Qed.
Lemma lem1532792 (x : real) (y : real) : (term268 x y) = term48.
Proof. exact (TRANS (@lem1532780 y x) (@lem1532791 x)). Qed.
Lemma lem1532793 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1532794 (x : real) (y : real) : (term275 x y) = term241.
Proof. exact (MK_COMB (@lem1532793) (@lem1532792 x y)). Qed.
Lemma lem1532795 (x : real) (y : real) : (term276 x y) = term243.
Proof. exact (MK_COMB (@lem1532794 x y) (@lem1532708)). Qed.
Lemma lem1532796 : term243 = term244.
Proof. exact (@lem1483519 term48 term48). Qed.
Lemma lem1532798 (x : nat) : (term177 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1532799 : term178 = term48.
Proof. exact (@lem1532798 term36). Qed.
Lemma lem1532800 : term245 = term245.
Proof. exact (eq_refl term245). Qed.
Lemma lem1532801 : term244 = term246.
Proof. exact (MK_COMB (@lem1532800) (@lem1532799)). Qed.
Lemma lem1532802 : term246 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1532803 : term244 = term48.
Proof. exact (TRANS (@lem1532801) (@lem1532802)). Qed.
Lemma lem1532804 : term243 = term48.
Proof. exact (TRANS (@lem1532796) (@lem1532803)). Qed.
Lemma lem1532805 (x : real) (y : real) : (term276 x y) = term48.
Proof. exact (TRANS (@lem1532795 x y) (@lem1532804)). Qed.
Lemma lem1532806 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1532807 (x : real) (y : real) : (term277 x y) = term248.
Proof. exact (MK_COMB (@lem1532806) (@lem1532805 x y)). Qed.
Lemma lem1532808 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532809 (x : real) (y : real) : (term267 x y) = term249.
Proof. exact (MK_COMB (@lem1532807 x y) (@lem1532808)). Qed.
Lemma lem1532810 (x : real) (y : real) : (term266 x y) = term249.
Proof. exact (TRANS (@lem1532707 x y) (@lem1532809 x y)). Qed.
Lemma lem1532811 (x : real) (y : real) : (term278 x y) = (term279 x y).
Proof. exact (@lem1483525 (term280 x y) term48). Qed.
Lemma lem1532812 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532825 (x : real) (y : real) : (real_sub x y) = (term115 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1532826 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1532827 (x : real) (y : real) : (term269 x y) = (term270 x y).
Proof. exact (MK_COMB (@lem1532826) (@lem1532825 x y)). Qed.
Lemma lem1532828 (x : real) (y : real) : (term270 x y) = (term260 x y).
Proof. exact (@lem1483512 (term115 x y)). Qed.
Lemma lem1532829 (x : real) (y : real) : (term260 x y) = (term261 x y).
Proof. exact (@lem1483508 x term28 (term117 y)). Qed.
Lemma lem1532830 (y : real) : (term136 y) = (term137 y).
Proof. exact (@lem1483476 term28 term28 y). Qed.
Lemma lem1532832 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1532833 : term34 = term35.
Proof. exact (@lem1532832 term36 term36). Qed.
Lemma lem1532834 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1532835 : term38 = term36.
Proof. exact (EQ_MP (@lem1532834) (@lem940073)). Qed.
Lemma lem1532836 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1532837 : term35 = term39.
Proof. exact (MK_COMB (@lem1532836) (@lem1532835)). Qed.
Lemma lem1532838 : term34 = term39.
Proof. exact (TRANS (@lem1532833) (@lem1532837)). Qed.
Lemma lem1532839 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1532840 : term40 = term41.
Proof. exact (MK_COMB (@lem1532839) (@lem1532838)). Qed.
Lemma lem1532841 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1532842 (y : real) : (term137 y) = (term138 y).
Proof. exact (MK_COMB (@lem1532840) (@lem1532841 y)). Qed.
Lemma lem1532843 (y : real) : (term136 y) = (term138 y).
Proof. exact (TRANS (@lem1532830 y) (@lem1532842 y)). Qed.
Lemma lem1532844 (y : real) : (term138 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1532845 (y : real) : (term136 y) = y.
Proof. exact (TRANS (@lem1532843 y) (@lem1532844 y)). Qed.
Lemma lem1532848 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1532849 (x : real) (y : real) : (term261 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1532848 x) (@lem1532845 y)). Qed.
Lemma lem1532850 (x : real) (y : real) : (term260 x y) = (term116 x y).
Proof. exact (TRANS (@lem1532829 x y) (@lem1532849 x y)). Qed.
Lemma lem1532851 (x : real) (y : real) : (term270 x y) = (term116 x y).
Proof. exact (TRANS (@lem1532828 x y) (@lem1532850 x y)). Qed.
Lemma lem1532852 (x : real) (y : real) : (term269 x y) = (term116 x y).
Proof. exact (TRANS (@lem1532827 x y) (@lem1532851 x y)). Qed.
Lemma lem1532855 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1532856 (x : real) (y : real) : (term281 x y) = (term282 x y).
Proof. exact (MK_COMB (@lem1532855 y) (@lem1532852 x y)). Qed.
Lemma lem1532857 (x : real) (y : real) : (term282 x y) = (term283 x y).
Proof. exact (@lem1483484 (term117 x) y y). Qed.
Lemma lem1532858 (y : real) : (real_add y y) = (term207 y).
Proof. exact (@lem1483444 y). Qed.
Lemma lem1532859 : term208 = term198.
Proof. exact (@lem1367770 term36 term36). Qed.
Lemma lem1532860 : term194 = term195.
Proof. exact (@lem706885). Qed.
Lemma lem1532861 : (term194 = term195) = (term196 = term197).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term195). Qed.
Lemma lem1532862 : term196 = term197.
Proof. exact (EQ_MP (@lem1532861) (@lem1532860)). Qed.
Lemma lem1532863 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1532864 : term198 = term199.
Proof. exact (MK_COMB (@lem1532863) (@lem1532862)). Qed.
Lemma lem1532865 : term208 = term199.
Proof. exact (TRANS (@lem1532859) (@lem1532864)). Qed.
Lemma lem1532866 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1532867 : term209 = term210.
Proof. exact (MK_COMB (@lem1532866) (@lem1532865)). Qed.
Lemma lem1532868 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1532869 (y : real) : (term207 y) = (term211 y).
Proof. exact (MK_COMB (@lem1532867) (@lem1532868 y)). Qed.
Lemma lem1532870 (y : real) : (real_add y y) = (term211 y).
Proof. exact (TRANS (@lem1532858 y) (@lem1532869 y)). Qed.
Lemma lem1532871 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1532872 (x : real) (y : real) : (term283 x y) = (term284 x y).
Proof. exact (MK_COMB (@lem1532871 x) (@lem1532870 y)). Qed.
Lemma lem1532873 (x : real) (y : real) : (term282 x y) = (term284 x y).
Proof. exact (TRANS (@lem1532857 x y) (@lem1532872 x y)). Qed.
Lemma lem1532874 (x : real) (y : real) : (term281 x y) = (term284 x y).
Proof. exact (TRANS (@lem1532856 x y) (@lem1532873 x y)). Qed.
Lemma lem1532883 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1532884 (x : real) (y : real) : (term280 x y) = (term285 x y).
Proof. exact (MK_COMB (@lem1532883 x) (@lem1532874 x y)). Qed.
Lemma lem1532885 (x : real) (y : real) : (term285 x y) = (term286 x y).
Proof. exact (@lem1483490 (term117 x) (term117 x) (term211 y)). Qed.
Lemma lem1532886 (x : real) : (term190 x) = (term191 x).
Proof. exact (@lem1483438 term28 term28 x). Qed.
Lemma lem1532887 : term192 = term193.
Proof. exact (@lem1367763 term36 term36). Qed.
Lemma lem1532888 : term194 = term195.
Proof. exact (@lem706885). Qed.
Lemma lem1532889 : (term194 = term195) = (term196 = term197).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term195). Qed.
Lemma lem1532890 : term196 = term197.
Proof. exact (EQ_MP (@lem1532889) (@lem1532888)). Qed.
Lemma lem1532891 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1532892 : term198 = term199.
Proof. exact (MK_COMB (@lem1532891) (@lem1532890)). Qed.
Lemma lem1532893 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1532894 : term193 = term200.
Proof. exact (MK_COMB (@lem1532893) (@lem1532892)). Qed.
Lemma lem1532895 : term192 = term200.
Proof. exact (TRANS (@lem1532887) (@lem1532894)). Qed.
Lemma lem1532896 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1532897 : term201 = term202.
Proof. exact (MK_COMB (@lem1532896) (@lem1532895)). Qed.
Lemma lem1532898 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1532899 (x : real) : (term191 x) = (term203 x).
Proof. exact (MK_COMB (@lem1532897) (@lem1532898 x)). Qed.
Lemma lem1532900 (x : real) : (term190 x) = (term203 x).
Proof. exact (TRANS (@lem1532886 x) (@lem1532899 x)). Qed.
Lemma lem1532901 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1532902 (x : real) : (term287 x) = (term288 x).
Proof. exact (MK_COMB (@lem1532901) (@lem1532900 x)). Qed.
Lemma lem1532903 (y : real) : (term211 y) = (term211 y).
Proof. exact (eq_refl (term211 y)). Qed.
Lemma lem1532904 (x : real) (y : real) : (term286 x y) = (term289 x y).
Proof. exact (MK_COMB (@lem1532902 x) (@lem1532903 y)). Qed.
Lemma lem1532905 (x : real) (y : real) : (term285 x y) = (term289 x y).
Proof. exact (TRANS (@lem1532885 x y) (@lem1532904 x y)). Qed.
Lemma lem1532906 (x : real) (y : real) : (term280 x y) = (term289 x y).
Proof. exact (TRANS (@lem1532884 x y) (@lem1532905 x y)). Qed.
Lemma lem1532907 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1532908 (x : real) (y : real) : (term290 x y) = (term291 x y).
Proof. exact (MK_COMB (@lem1532907) (@lem1532906 x y)). Qed.
Lemma lem1532909 (x : real) (y : real) : (term292 x y) = (term293 x y).
Proof. exact (MK_COMB (@lem1532908 x y) (@lem1532812)). Qed.
Lemma lem1532910 (x : real) (y : real) : (term293 x y) = (term294 x y).
Proof. exact (@lem1483519 (term289 x y) term48). Qed.
Lemma lem1532912 (x : nat) : (term177 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1532913 : term178 = term48.
Proof. exact (@lem1532912 term36). Qed.
Lemma lem1532914 (x : real) (y : real) : (term295 x y) = (term295 x y).
Proof. exact (eq_refl (term295 x y)). Qed.
Lemma lem1532915 (x : real) (y : real) : (term294 x y) = (term296 x y).
Proof. exact (MK_COMB (@lem1532914 x y) (@lem1532913)). Qed.
Lemma lem1532916 (x : real) (y : real) : (term296 x y) = (term289 x y).
Proof. exact (@lem1483450 (term289 x y)). Qed.
Lemma lem1532917 (x : real) (y : real) : (term294 x y) = (term289 x y).
Proof. exact (TRANS (@lem1532915 x y) (@lem1532916 x y)). Qed.
Lemma lem1532918 (x : real) (y : real) : (term293 x y) = (term289 x y).
Proof. exact (TRANS (@lem1532910 x y) (@lem1532917 x y)). Qed.
Lemma lem1532919 (x : real) (y : real) : (term292 x y) = (term289 x y).
Proof. exact (TRANS (@lem1532909 x y) (@lem1532918 x y)). Qed.
Lemma lem1532920 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1532921 (x : real) (y : real) : (term297 x y) = (term298 x y).
Proof. exact (MK_COMB (@lem1532920) (@lem1532919 x y)). Qed.
Lemma lem1532922 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532923 (x : real) (y : real) : (term279 x y) = (term299 x y).
Proof. exact (MK_COMB (@lem1532921 x y) (@lem1532922)). Qed.
Lemma lem1532924 (x : real) (y : real) : (term278 x y) = (term299 x y).
Proof. exact (TRANS (@lem1532811 x y) (@lem1532923 x y)). Qed.
Lemma lem1532925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1532926 (x : real) (y : real) : (term300 x y) = term301.
Proof. exact (MK_COMB (@lem1532925) (@lem1532810 x y)). Qed.
Lemma lem1532927 (x : real) (y : real) : (term157 x y) = (term302 x y).
Proof. exact (MK_COMB (@lem1532926 x y) (@lem1532924 x y)). Qed.
Lemma lem1532928 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1532929 (x : real) (y : real) : (term158 x y) = (term303 x y).
Proof. exact (MK_COMB (@lem1532928) (@lem1532706 x y)). Qed.
Lemma lem1532930 (x : real) (y : real) : (term160 x y) = (term304 x y).
Proof. exact (MK_COMB (@lem1532929 x y) (@lem1532927 x y)). Qed.
Lemma lem1532931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1532932 (x : real) (y : real) : (term167 x y) = (term305 x y).
Proof. exact (MK_COMB (@lem1532931) (@lem1532654 x y)). Qed.
Lemma lem1532933 (x : real) (y : real) : (term168 x y) = (term306 x y).
Proof. exact (MK_COMB (@lem1532932 x y) (@lem1532930 x y)). Qed.
Lemma lem1532944 (x : real) (y : real) : (term152 x y) = (term306 x y).
Proof. exact (TRANS (@lem1532451 x y) (@lem1532933 x y)). Qed.
Lemma lem1532945 (x : real) (y : real) : (term54 y x) = (term306 x y).
Proof. exact (TRANS (@lem1532435 x y) (@lem1532944 x y)). Qed.
Lemma lem1532947 (a : real) (x : real) (r : real) : (term307 x a r) = (term113 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1532948 (x : real) (y : real) : (term50 y x) = (term114 x y).
Proof. exact (@lem1532947 (term6 y x) (real_sub x y) term48). Qed.
Lemma lem1532961 (x : real) (y : real) : (real_sub x y) = (term115 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1532964 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1532965 (x : real) (y : real) : (term118 x y) = (term308 x y).
Proof. exact (MK_COMB (@lem1532964) (@lem1532961 x y)). Qed.
Lemma lem1532966 (x : real) (y : real) : (term308 x y) = (term115 x y).
Proof. exact (@lem1483460 (term115 x y)). Qed.
Lemma lem1532967 (x : real) (y : real) : (term118 x y) = (term115 x y).
Proof. exact (TRANS (@lem1532965 x y) (@lem1532966 x y)). Qed.
Lemma lem1532970 (y : real) (x : real) : (term120 y x) = (term120 y x).
Proof. exact (eq_refl (term120 y x)). Qed.
Lemma lem1532971 (x : real) (y : real) : (term121 x y) = (term309 x y).
Proof. exact (MK_COMB (@lem1532970 y x) (@lem1532967 x y)). Qed.
Lemma lem1532972 (x : real) (y : real) : (term309 x y) = (term310 x y).
Proof. exact (@lem1483484 x (term6 y x) (term117 y)). Qed.
Lemma lem1532973 (y : real) (x : real) : (term311 x y) = (term312 y x).
Proof. exact (@lem1483488 (term117 y) (term6 y x)). Qed.
Lemma lem1532974 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1532975 (y : real) (x : real) : (term310 x y) = (term313 y x).
Proof. exact (MK_COMB (@lem1532974 x) (@lem1532973 y x)). Qed.
Lemma lem1532976 (y : real) (x : real) : (term309 x y) = (term313 y x).
Proof. exact (TRANS (@lem1532972 x y) (@lem1532975 y x)). Qed.
Lemma lem1532977 (y : real) (x : real) : (term121 x y) = (term313 y x).
Proof. exact (TRANS (@lem1532971 x y) (@lem1532976 y x)). Qed.
Lemma lem1532978 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1532979 (y : real) (x : real) : (term128 x y) = (term314 y x).
Proof. exact (MK_COMB (@lem1532978) (@lem1532977 y x)). Qed.
Lemma lem1532980 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1532981 (y : real) (x : real) : (term130 x y) = (term315 y x).
Proof. exact (MK_COMB (@lem1532979 y x) (@lem1532980)). Qed.
Lemma lem1532994 (x : real) (y : real) : (real_sub x y) = (term115 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1532997 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1532998 (x : real) (y : real) : (term133 x y) = (term260 x y).
Proof. exact (MK_COMB (@lem1532997) (@lem1532994 x y)). Qed.
Lemma lem1532999 (x : real) (y : real) : (term260 x y) = (term261 x y).
Proof. exact (@lem1483508 x term28 (term117 y)). Qed.
Lemma lem1533000 (y : real) : (term136 y) = (term137 y).
Proof. exact (@lem1483476 term28 term28 y). Qed.
Lemma lem1533002 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1533003 : term34 = term35.
Proof. exact (@lem1533002 term36 term36). Qed.
Lemma lem1533004 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1533005 : term38 = term36.
Proof. exact (EQ_MP (@lem1533004) (@lem940073)). Qed.
Lemma lem1533006 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1533007 : term35 = term39.
Proof. exact (MK_COMB (@lem1533006) (@lem1533005)). Qed.
Lemma lem1533008 : term34 = term39.
Proof. exact (TRANS (@lem1533003) (@lem1533007)). Qed.
Lemma lem1533009 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1533010 : term40 = term41.
Proof. exact (MK_COMB (@lem1533009) (@lem1533008)). Qed.
Lemma lem1533011 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1533012 (y : real) : (term137 y) = (term138 y).
Proof. exact (MK_COMB (@lem1533010) (@lem1533011 y)). Qed.
Lemma lem1533013 (y : real) : (term136 y) = (term138 y).
Proof. exact (TRANS (@lem1533000 y) (@lem1533012 y)). Qed.
Lemma lem1533014 (y : real) : (term138 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1533015 (y : real) : (term136 y) = y.
Proof. exact (TRANS (@lem1533013 y) (@lem1533014 y)). Qed.
Lemma lem1533018 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1533019 (x : real) (y : real) : (term261 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1533018 x) (@lem1533015 y)). Qed.
Lemma lem1533020 (x : real) (y : real) : (term260 x y) = (term116 x y).
Proof. exact (TRANS (@lem1532999 x y) (@lem1533019 x y)). Qed.
Lemma lem1533021 (x : real) (y : real) : (term133 x y) = (term116 x y).
Proof. exact (TRANS (@lem1532998 x y) (@lem1533020 x y)). Qed.
Lemma lem1533024 (y : real) (x : real) : (term120 y x) = (term120 y x).
Proof. exact (eq_refl (term120 y x)). Qed.
Lemma lem1533025 (x : real) (y : real) : (term140 x y) = (term316 x y).
Proof. exact (MK_COMB (@lem1533024 y x) (@lem1533021 x y)). Qed.
Lemma lem1533026 (x : real) (y : real) : (term316 x y) = (term317 x y).
Proof. exact (@lem1483484 (term117 x) (term6 y x) y). Qed.
Lemma lem1533027 (y : real) (x : real) : (term318 x y) = (term319 y x).
Proof. exact (@lem1483488 y (term6 y x)). Qed.
Lemma lem1533028 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1533029 (y : real) (x : real) : (term317 x y) = (term320 y x).
Proof. exact (MK_COMB (@lem1533028 x) (@lem1533027 y x)). Qed.
Lemma lem1533030 (y : real) (x : real) : (term316 x y) = (term320 y x).
Proof. exact (TRANS (@lem1533026 x y) (@lem1533029 y x)). Qed.
Lemma lem1533031 (y : real) (x : real) : (term140 x y) = (term320 y x).
Proof. exact (TRANS (@lem1533025 x y) (@lem1533030 y x)). Qed.
Lemma lem1533032 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1533033 (y : real) (x : real) : (term146 x y) = (term321 y x).
Proof. exact (MK_COMB (@lem1533032) (@lem1533031 y x)). Qed.
Lemma lem1533034 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1533035 (y : real) (x : real) : (term148 x y) = (term322 y x).
Proof. exact (MK_COMB (@lem1533033 y x) (@lem1533034)). Qed.
Lemma lem1533036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1533037 (y : real) (x : real) : (term150 x y) = (term323 y x).
Proof. exact (MK_COMB (@lem1533036) (@lem1533035 y x)). Qed.
Lemma lem1533038 (y : real) (x : real) : (term114 x y) = (term324 y x).
Proof. exact (MK_COMB (@lem1533037 y x) (@lem1532981 y x)). Qed.
Lemma lem1533039 (y : real) (x : real) : (term50 y x) = (term324 y x).
Proof. exact (TRANS (@lem1532948 x y) (@lem1533038 y x)). Qed.
Lemma lem1533040 (y : real) (x : real) : (term325 y x) = (term324 y x).
Proof. exact (eq_refl (term325 y x)). Qed.
Lemma lem1533041 (y : real) (x : real) : (term324 y x) = (term325 y x).
Proof. exact (SYM (@lem1533040 y x)). Qed.
Lemma lem1533042 (y : real) (x : real) : (term325 y x) = (term326 y x).
Proof. exact (@lem1482981 (term327 x y) (real_sub y x)). Qed.
Lemma lem1533043 (y : real) (x : real) : (term324 y x) = (term326 y x).
Proof. exact (TRANS (@lem1533041 y x) (@lem1533042 y x)). Qed.
Lemma lem1533044 (y : real) (x : real) : (term328 y x) = (term329 y x).
Proof. exact (eq_refl (term328 y x)). Qed.
Lemma lem1533045 (y : real) (x : real) : (term158 y x) = (term158 y x).
Proof. exact (eq_refl (term158 y x)). Qed.
Lemma lem1533046 (y : real) (x : real) : (term330 y x) = (term331 y x).
Proof. exact (MK_COMB (@lem1533045 y x) (@lem1533044 y x)). Qed.
Lemma lem1533047 (y : real) (x : real) : (term332 y x) = (term333 y x).
Proof. exact (eq_refl (term332 y x)). Qed.
Lemma lem1533048 (y : real) (x : real) : (term163 y x) = (term163 y x).
Proof. exact (eq_refl (term163 y x)). Qed.
Lemma lem1533049 (y : real) (x : real) : (term334 y x) = (term335 y x).
Proof. exact (MK_COMB (@lem1533048 y x) (@lem1533047 y x)). Qed.
Lemma lem1533050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1533051 (y : real) (x : real) : (term336 y x) = (term337 y x).
Proof. exact (MK_COMB (@lem1533050) (@lem1533049 y x)). Qed.
Lemma lem1533052 (y : real) (x : real) : (term326 y x) = (term338 y x).
Proof. exact (MK_COMB (@lem1533051 y x) (@lem1533046 y x)). Qed.
Lemma lem1533053 (y : real) (x : real) : (term339 y x) = (term339 y x).
Proof. exact (eq_refl (term339 y x)). Qed.
Lemma lem1533054 (y : real) (x : real) : ((term324 y x) = (term326 y x)) = ((term324 y x) = (term338 y x)).
Proof. exact (MK_COMB (@lem1533053 y x) (@lem1533052 y x)). Qed.
Lemma lem1533055 (y : real) (x : real) : (term324 y x) = (term338 y x).
Proof. exact (EQ_MP (@lem1533054 y x) (@lem1533043 y x)). Qed.
Lemma lem1533056 (y : real) (x : real) : (term170 y x) = (term171 y x).
Proof. exact (@lem1483527 (real_sub y x) term48). Qed.
Lemma lem1533057 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1533063 (y : real) (x : real) : (real_sub y x) = (term115 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1533068 (x : real) (y : real) : (term115 y x) = (term116 x y).
Proof. exact (@lem1483488 (term117 x) y). Qed.
Lemma lem1533070 (x : real) (y : real) : (real_sub y x) = (term116 x y).
Proof. exact (TRANS (@lem1533063 y x) (@lem1533068 x y)). Qed.
Lemma lem1533071 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1533072 (x : real) (y : real) : (term172 y x) = (term340 x y).
Proof. exact (MK_COMB (@lem1533071) (@lem1533070 x y)). Qed.
Lemma lem1533073 (x : real) (y : real) : (term174 y x) = (term341 x y).
Proof. exact (MK_COMB (@lem1533072 x y) (@lem1533057)). Qed.
Lemma lem1533074 (x : real) (y : real) : (term341 x y) = (term342 x y).
Proof. exact (@lem1483519 (term116 x y) term48). Qed.
Lemma lem1533076 (x : nat) : (term177 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1533077 : term178 = term48.
Proof. exact (@lem1533076 term36). Qed.
Lemma lem1533078 (x : real) (y : real) : (term343 x y) = (term343 x y).
Proof. exact (eq_refl (term343 x y)). Qed.
Lemma lem1533079 (x : real) (y : real) : (term342 x y) = (term344 x y).
Proof. exact (MK_COMB (@lem1533078 x y) (@lem1533077)). Qed.
Lemma lem1533080 (x : real) (y : real) : (term344 x y) = (term116 x y).
Proof. exact (@lem1483450 (term116 x y)). Qed.
Lemma lem1533081 (x : real) (y : real) : (term342 x y) = (term116 x y).
Proof. exact (TRANS (@lem1533079 x y) (@lem1533080 x y)). Qed.
Lemma lem1533082 (x : real) (y : real) : (term341 x y) = (term116 x y).
Proof. exact (TRANS (@lem1533074 x y) (@lem1533081 x y)). Qed.
Lemma lem1533083 (x : real) (y : real) : (term174 y x) = (term116 x y).
Proof. exact (TRANS (@lem1533073 x y) (@lem1533082 x y)). Qed.
Lemma lem1533084 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1533085 (x : real) (y : real) : (term181 y x) = (term345 x y).
Proof. exact (MK_COMB (@lem1533084) (@lem1533083 x y)). Qed.
Lemma lem1533086 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1533087 (x : real) (y : real) : (term171 y x) = (term346 x y).
Proof. exact (MK_COMB (@lem1533085 x y) (@lem1533086)). Qed.
Lemma lem1533088 (x : real) (y : real) : (term170 y x) = (term346 x y).
Proof. exact (TRANS (@lem1533056 y x) (@lem1533087 x y)). Qed.
Lemma lem1533089 (y : real) (x : real) : (term347 y x) = (term348 y x).
Proof. exact (@lem1483525 (term349 y x) term48). Qed.
Lemma lem1533090 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1533096 (y : real) (x : real) : (real_sub y x) = (term115 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1533101 (x : real) (y : real) : (term115 y x) = (term116 x y).
Proof. exact (@lem1483488 (term117 x) y). Qed.
Lemma lem1533103 (x : real) (y : real) : (real_sub y x) = (term116 x y).
Proof. exact (TRANS (@lem1533096 y x) (@lem1533101 x y)). Qed.
Lemma lem1533106 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1533107 (x : real) (y : real) : (term350 y x) = (term282 x y).
Proof. exact (MK_COMB (@lem1533106 y) (@lem1533103 x y)). Qed.
Lemma lem1533108 (x : real) (y : real) : (term282 x y) = (term283 x y).
Proof. exact (@lem1483484 (term117 x) y y). Qed.
Lemma lem1533109 (y : real) : (real_add y y) = (term207 y).
Proof. exact (@lem1483444 y). Qed.
Lemma lem1533110 : term208 = term198.
Proof. exact (@lem1367770 term36 term36). Qed.
Lemma lem1533111 : term194 = term195.
Proof. exact (@lem706885). Qed.
Lemma lem1533112 : (term194 = term195) = (term196 = term197).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term195). Qed.
Lemma lem1533113 : term196 = term197.
Proof. exact (EQ_MP (@lem1533112) (@lem1533111)). Qed.
Lemma lem1533114 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1533115 : term198 = term199.
Proof. exact (MK_COMB (@lem1533114) (@lem1533113)). Qed.
Lemma lem1533116 : term208 = term199.
Proof. exact (TRANS (@lem1533110) (@lem1533115)). Qed.
Lemma lem1533117 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1533118 : term209 = term210.
Proof. exact (MK_COMB (@lem1533117) (@lem1533116)). Qed.
Lemma lem1533119 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1533120 (y : real) : (term207 y) = (term211 y).
Proof. exact (MK_COMB (@lem1533118) (@lem1533119 y)). Qed.
Lemma lem1533121 (y : real) : (real_add y y) = (term211 y).
Proof. exact (TRANS (@lem1533109 y) (@lem1533120 y)). Qed.
Lemma lem1533122 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1533123 (x : real) (y : real) : (term283 x y) = (term284 x y).
Proof. exact (MK_COMB (@lem1533122 x) (@lem1533121 y)). Qed.
Lemma lem1533124 (x : real) (y : real) : (term282 x y) = (term284 x y).
Proof. exact (TRANS (@lem1533108 x y) (@lem1533123 x y)). Qed.
Lemma lem1533125 (x : real) (y : real) : (term350 y x) = (term284 x y).
Proof. exact (TRANS (@lem1533107 x y) (@lem1533124 x y)). Qed.
Lemma lem1533134 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1533135 (x : real) (y : real) : (term349 y x) = (term285 x y).
Proof. exact (MK_COMB (@lem1533134 x) (@lem1533125 x y)). Qed.
Lemma lem1533136 (x : real) (y : real) : (term285 x y) = (term286 x y).
Proof. exact (@lem1483490 (term117 x) (term117 x) (term211 y)). Qed.
Lemma lem1533137 (x : real) : (term190 x) = (term191 x).
Proof. exact (@lem1483438 term28 term28 x). Qed.
Lemma lem1533138 : term192 = term193.
Proof. exact (@lem1367763 term36 term36). Qed.
Lemma lem1533139 : term194 = term195.
Proof. exact (@lem706885). Qed.
Lemma lem1533140 : (term194 = term195) = (term196 = term197).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term195). Qed.
Lemma lem1533141 : term196 = term197.
Proof. exact (EQ_MP (@lem1533140) (@lem1533139)). Qed.
Lemma lem1533142 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1533143 : term198 = term199.
Proof. exact (MK_COMB (@lem1533142) (@lem1533141)). Qed.
Lemma lem1533144 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1533145 : term193 = term200.
Proof. exact (MK_COMB (@lem1533144) (@lem1533143)). Qed.
Lemma lem1533146 : term192 = term200.
Proof. exact (TRANS (@lem1533138) (@lem1533145)). Qed.
Lemma lem1533147 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1533148 : term201 = term202.
Proof. exact (MK_COMB (@lem1533147) (@lem1533146)). Qed.
Lemma lem1533149 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1533150 (x : real) : (term191 x) = (term203 x).
Proof. exact (MK_COMB (@lem1533148) (@lem1533149 x)). Qed.
Lemma lem1533151 (x : real) : (term190 x) = (term203 x).
Proof. exact (TRANS (@lem1533137 x) (@lem1533150 x)). Qed.
Lemma lem1533152 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1533153 (x : real) : (term287 x) = (term288 x).
Proof. exact (MK_COMB (@lem1533152) (@lem1533151 x)). Qed.
Lemma lem1533154 (y : real) : (term211 y) = (term211 y).
Proof. exact (eq_refl (term211 y)). Qed.
Lemma lem1533155 (x : real) (y : real) : (term286 x y) = (term289 x y).
Proof. exact (MK_COMB (@lem1533153 x) (@lem1533154 y)). Qed.
Lemma lem1533156 (x : real) (y : real) : (term285 x y) = (term289 x y).
Proof. exact (TRANS (@lem1533136 x y) (@lem1533155 x y)). Qed.
Lemma lem1533157 (x : real) (y : real) : (term349 y x) = (term289 x y).
Proof. exact (TRANS (@lem1533135 x y) (@lem1533156 x y)). Qed.
Lemma lem1533158 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1533159 (x : real) (y : real) : (term351 y x) = (term291 x y).
Proof. exact (MK_COMB (@lem1533158) (@lem1533157 x y)). Qed.
Lemma lem1533160 (x : real) (y : real) : (term352 y x) = (term293 x y).
Proof. exact (MK_COMB (@lem1533159 x y) (@lem1533090)). Qed.
Lemma lem1533161 (x : real) (y : real) : (term293 x y) = (term294 x y).
Proof. exact (@lem1483519 (term289 x y) term48). Qed.
Lemma lem1533163 (x : nat) : (term177 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1533164 : term178 = term48.
Proof. exact (@lem1533163 term36). Qed.
Lemma lem1533165 (x : real) (y : real) : (term295 x y) = (term295 x y).
Proof. exact (eq_refl (term295 x y)). Qed.
Lemma lem1533166 (x : real) (y : real) : (term294 x y) = (term296 x y).
Proof. exact (MK_COMB (@lem1533165 x y) (@lem1533164)). Qed.
Lemma lem1533167 (x : real) (y : real) : (term296 x y) = (term289 x y).
Proof. exact (@lem1483450 (term289 x y)). Qed.
Lemma lem1533168 (x : real) (y : real) : (term294 x y) = (term289 x y).
Proof. exact (TRANS (@lem1533166 x y) (@lem1533167 x y)). Qed.
Lemma lem1533169 (x : real) (y : real) : (term293 x y) = (term289 x y).
Proof. exact (TRANS (@lem1533161 x y) (@lem1533168 x y)). Qed.
Lemma lem1533170 (x : real) (y : real) : (term352 y x) = (term289 x y).
Proof. exact (TRANS (@lem1533160 x y) (@lem1533169 x y)). Qed.
Lemma lem1533171 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1533172 (x : real) (y : real) : (term353 y x) = (term298 x y).
Proof. exact (MK_COMB (@lem1533171) (@lem1533170 x y)). Qed.
Lemma lem1533173 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1533174 (x : real) (y : real) : (term348 y x) = (term299 x y).
Proof. exact (MK_COMB (@lem1533172 x y) (@lem1533173)). Qed.
Lemma lem1533175 (x : real) (y : real) : (term347 y x) = (term299 x y).
Proof. exact (TRANS (@lem1533089 y x) (@lem1533174 x y)). Qed.
Lemma lem1533176 (y : real) (x : real) : (term354 y x) = (term355 y x).
Proof. exact (@lem1483525 (term356 y x) term48). Qed.
Lemma lem1533177 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1533183 (y : real) (x : real) : (real_sub y x) = (term115 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1533188 (x : real) (y : real) : (term115 y x) = (term116 x y).
Proof. exact (@lem1483488 (term117 x) y). Qed.
Lemma lem1533190 (x : real) (y : real) : (real_sub y x) = (term116 x y).
Proof. exact (TRANS (@lem1533183 y x) (@lem1533188 x y)). Qed.
Lemma lem1533199 (y : real) : (term126 y) = (term126 y).
Proof. exact (eq_refl (term126 y)). Qed.
Lemma lem1533200 (x : real) (y : real) : (term357 y x) = (term272 x y).
Proof. exact (MK_COMB (@lem1533199 y) (@lem1533190 x y)). Qed.
Lemma lem1533201 (x : real) (y : real) : (term272 x y) = (term273 x y).
Proof. exact (@lem1483484 (term117 x) (term117 y) y). Qed.
Lemma lem1533202 (y : real) : (term239 y) = (term232 y).
Proof. exact (@lem1483440 term28 y). Qed.
Lemma lem1533204 (m : nat) : (term233 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1533205 : term234 = term48.
Proof. exact (@lem1533204 term36). Qed.
Lemma lem1533206 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1533207 : term235 = term236.
Proof. exact (MK_COMB (@lem1533206) (@lem1533205)). Qed.
Lemma lem1533208 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1533209 (y : real) : (term232 y) = (term237 y).
Proof. exact (MK_COMB (@lem1533207) (@lem1533208 y)). Qed.
Lemma lem1533210 (y : real) : (term239 y) = (term237 y).
Proof. exact (TRANS (@lem1533202 y) (@lem1533209 y)). Qed.
Lemma lem1533211 (y : real) : (term237 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1533212 (y : real) : (term239 y) = term48.
Proof. exact (TRANS (@lem1533210 y) (@lem1533211 y)). Qed.
Lemma lem1533213 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1533214 (y : real) (x : real) : (term273 x y) = (term274 x).
Proof. exact (MK_COMB (@lem1533213 x) (@lem1533212 y)). Qed.
Lemma lem1533215 (y : real) (x : real) : (term272 x y) = (term274 x).
Proof. exact (TRANS (@lem1533201 x y) (@lem1533214 y x)). Qed.
Lemma lem1533216 (x : real) : (term274 x) = (term117 x).
Proof. exact (@lem1483450 (term117 x)). Qed.
Lemma lem1533217 (y : real) (x : real) : (term272 x y) = (term117 x).
Proof. exact (TRANS (@lem1533215 y x) (@lem1533216 x)). Qed.
Lemma lem1533218 (y : real) (x : real) : (term357 y x) = (term117 x).
Proof. exact (TRANS (@lem1533200 x y) (@lem1533217 y x)). Qed.
Lemma lem1533221 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1533222 (y : real) (x : real) : (term356 y x) = (term231 x).
Proof. exact (MK_COMB (@lem1533221 x) (@lem1533218 y x)). Qed.
Lemma lem1533223 (x : real) : (term231 x) = (term232 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1533225 (m : nat) : (term233 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1533226 : term234 = term48.
Proof. exact (@lem1533225 term36). Qed.
Lemma lem1533227 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1533228 : term235 = term236.
Proof. exact (MK_COMB (@lem1533227) (@lem1533226)). Qed.
Lemma lem1533229 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1533230 (x : real) : (term232 x) = (term237 x).
Proof. exact (MK_COMB (@lem1533228) (@lem1533229 x)). Qed.
Lemma lem1533231 (x : real) : (term231 x) = (term237 x).
Proof. exact (TRANS (@lem1533223 x) (@lem1533230 x)). Qed.
Lemma lem1533232 (x : real) : (term237 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1533233 (x : real) : (term231 x) = term48.
Proof. exact (TRANS (@lem1533231 x) (@lem1533232 x)). Qed.
Lemma lem1533234 (y : real) (x : real) : (term356 y x) = term48.
Proof. exact (TRANS (@lem1533222 y x) (@lem1533233 x)). Qed.
Lemma lem1533235 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1533236 (y : real) (x : real) : (term358 y x) = term241.
Proof. exact (MK_COMB (@lem1533235) (@lem1533234 y x)). Qed.
Lemma lem1533237 (y : real) (x : real) : (term359 y x) = term243.
Proof. exact (MK_COMB (@lem1533236 y x) (@lem1533177)). Qed.
Lemma lem1533238 : term243 = term244.
Proof. exact (@lem1483519 term48 term48). Qed.
Lemma lem1533240 (x : nat) : (term177 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1533241 : term178 = term48.
Proof. exact (@lem1533240 term36). Qed.
Lemma lem1533242 : term245 = term245.
Proof. exact (eq_refl term245). Qed.
Lemma lem1533243 : term244 = term246.
Proof. exact (MK_COMB (@lem1533242) (@lem1533241)). Qed.
Lemma lem1533244 : term246 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1533245 : term244 = term48.
Proof. exact (TRANS (@lem1533243) (@lem1533244)). Qed.
Lemma lem1533246 : term243 = term48.
Proof. exact (TRANS (@lem1533238) (@lem1533245)). Qed.
Lemma lem1533247 (y : real) (x : real) : (term359 y x) = term48.
Proof. exact (TRANS (@lem1533237 y x) (@lem1533246)). Qed.
Lemma lem1533248 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1533249 (y : real) (x : real) : (term360 y x) = term248.
Proof. exact (MK_COMB (@lem1533248) (@lem1533247 y x)). Qed.
Lemma lem1533250 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1533251 (y : real) (x : real) : (term355 y x) = term249.
Proof. exact (MK_COMB (@lem1533249 y x) (@lem1533250)). Qed.
Lemma lem1533252 (y : real) (x : real) : (term354 y x) = term249.
Proof. exact (TRANS (@lem1533176 y x) (@lem1533251 y x)). Qed.
Lemma lem1533253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1533254 (x : real) (y : real) : (term361 y x) = (term362 x y).
Proof. exact (MK_COMB (@lem1533253) (@lem1533175 x y)). Qed.
Lemma lem1533255 (x : real) (y : real) : (term333 y x) = (term363 x y).
Proof. exact (MK_COMB (@lem1533254 x y) (@lem1533252 y x)). Qed.
Lemma lem1533256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1533257 (x : real) (y : real) : (term163 y x) = (term364 x y).
Proof. exact (MK_COMB (@lem1533256) (@lem1533088 x y)). Qed.
Lemma lem1533258 (x : real) (y : real) : (term335 y x) = (term365 x y).
Proof. exact (MK_COMB (@lem1533257 x y) (@lem1533255 x y)). Qed.
Lemma lem1533259 (y : real) (x : real) : (term255 y x) = (term256 y x).
Proof. exact (@lem1483525 term48 (real_sub y x)). Qed.
Lemma lem1533265 (y : real) (x : real) : (real_sub y x) = (term115 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1533270 (x : real) (y : real) : (term115 y x) = (term116 x y).
Proof. exact (@lem1483488 (term117 x) y). Qed.
Lemma lem1533272 (x : real) (y : real) : (real_sub y x) = (term116 x y).
Proof. exact (TRANS (@lem1533265 y x) (@lem1533270 x y)). Qed.
Lemma lem1533275 : term241 = term241.
Proof. exact (eq_refl term241). Qed.
Lemma lem1533276 (x : real) (y : real) : (term257 y x) = (term366 x y).
Proof. exact (MK_COMB (@lem1533275) (@lem1533272 x y)). Qed.
Lemma lem1533277 (x : real) (y : real) : (term366 x y) = (term367 x y).
Proof. exact (@lem1483519 term48 (term116 x y)). Qed.
Lemma lem1533278 (x : real) (y : real) : (term134 x y) = (term135 x y).
Proof. exact (@lem1483508 (term117 x) term28 y). Qed.
Lemma lem1533279 (y : real) : (term117 y) = (term117 y).
Proof. exact (eq_refl (term117 y)). Qed.
Lemma lem1533280 (x : real) : (term136 x) = (term137 x).
Proof. exact (@lem1483476 term28 term28 x). Qed.
Lemma lem1533282 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1533283 : term34 = term35.
Proof. exact (@lem1533282 term36 term36). Qed.
Lemma lem1533284 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1533285 : term38 = term36.
Proof. exact (EQ_MP (@lem1533284) (@lem940073)). Qed.
Lemma lem1533286 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1533287 : term35 = term39.
Proof. exact (MK_COMB (@lem1533286) (@lem1533285)). Qed.
Lemma lem1533288 : term34 = term39.
Proof. exact (TRANS (@lem1533283) (@lem1533287)). Qed.
Lemma lem1533289 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1533290 : term40 = term41.
Proof. exact (MK_COMB (@lem1533289) (@lem1533288)). Qed.
Lemma lem1533291 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1533292 (x : real) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem1533290) (@lem1533291 x)). Qed.
Lemma lem1533293 (x : real) : (term136 x) = (term138 x).
Proof. exact (TRANS (@lem1533280 x) (@lem1533292 x)). Qed.
Lemma lem1533294 (x : real) : (term138 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1533295 (x : real) : (term136 x) = x.
Proof. exact (TRANS (@lem1533293 x) (@lem1533294 x)). Qed.
Lemma lem1533296 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1533297 (x : real) : (term139 x) = (real_add x).
Proof. exact (MK_COMB (@lem1533296) (@lem1533295 x)). Qed.
Lemma lem1533298 (x : real) (y : real) : (term135 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem1533297 x) (@lem1533279 y)). Qed.
Lemma lem1533299 (x : real) (y : real) : (term134 x y) = (term115 x y).
Proof. exact (TRANS (@lem1533278 x y) (@lem1533298 x y)). Qed.
Lemma lem1533300 : term245 = term245.
Proof. exact (eq_refl term245). Qed.
Lemma lem1533301 (x : real) (y : real) : (term367 x y) = (term368 x y).
Proof. exact (MK_COMB (@lem1533300) (@lem1533299 x y)). Qed.
Lemma lem1533302 (x : real) (y : real) : (term368 x y) = (term115 x y).
Proof. exact (@lem1483448 (term115 x y)). Qed.
Lemma lem1533303 (x : real) (y : real) : (term367 x y) = (term115 x y).
Proof. exact (TRANS (@lem1533301 x y) (@lem1533302 x y)). Qed.
Lemma lem1533304 (x : real) (y : real) : (term366 x y) = (term115 x y).
Proof. exact (TRANS (@lem1533277 x y) (@lem1533303 x y)). Qed.
Lemma lem1533305 (x : real) (y : real) : (term257 y x) = (term115 x y).
Proof. exact (TRANS (@lem1533276 x y) (@lem1533304 x y)). Qed.
Lemma lem1533306 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1533307 (x : real) (y : real) : (term263 y x) = (term369 x y).
Proof. exact (MK_COMB (@lem1533306) (@lem1533305 x y)). Qed.
Lemma lem1533308 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1533309 (x : real) (y : real) : (term256 y x) = (term370 x y).
Proof. exact (MK_COMB (@lem1533307 x y) (@lem1533308)). Qed.
Lemma lem1533310 (x : real) (y : real) : (term255 y x) = (term370 x y).
Proof. exact (TRANS (@lem1533259 y x) (@lem1533309 x y)). Qed.
Lemma lem1533311 (y : real) (x : real) : (term371 y x) = (term372 y x).
Proof. exact (@lem1483525 (term373 y x) term48). Qed.
Lemma lem1533312 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1533318 (y : real) (x : real) : (real_sub y x) = (term115 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1533323 (x : real) (y : real) : (term115 y x) = (term116 x y).
Proof. exact (@lem1483488 (term117 x) y). Qed.
Lemma lem1533325 (x : real) (y : real) : (real_sub y x) = (term116 x y).
Proof. exact (TRANS (@lem1533318 y x) (@lem1533323 x y)). Qed.
Lemma lem1533326 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1533327 (x : real) (y : real) : (term269 y x) = (term374 x y).
Proof. exact (MK_COMB (@lem1533326) (@lem1533325 x y)). Qed.
Lemma lem1533328 (x : real) (y : real) : (term374 x y) = (term134 x y).
Proof. exact (@lem1483512 (term116 x y)). Qed.
Lemma lem1533329 (x : real) (y : real) : (term134 x y) = (term135 x y).
Proof. exact (@lem1483508 (term117 x) term28 y). Qed.
Lemma lem1533330 (y : real) : (term117 y) = (term117 y).
Proof. exact (eq_refl (term117 y)). Qed.
Lemma lem1533331 (x : real) : (term136 x) = (term137 x).
Proof. exact (@lem1483476 term28 term28 x). Qed.
Lemma lem1533333 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1533334 : term34 = term35.
Proof. exact (@lem1533333 term36 term36). Qed.
Lemma lem1533335 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1533336 : term38 = term36.
Proof. exact (EQ_MP (@lem1533335) (@lem940073)). Qed.
Lemma lem1533337 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1533338 : term35 = term39.
Proof. exact (MK_COMB (@lem1533337) (@lem1533336)). Qed.
Lemma lem1533339 : term34 = term39.
Proof. exact (TRANS (@lem1533334) (@lem1533338)). Qed.
Lemma lem1533340 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1533341 : term40 = term41.
Proof. exact (MK_COMB (@lem1533340) (@lem1533339)). Qed.
Lemma lem1533342 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1533343 (x : real) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem1533341) (@lem1533342 x)). Qed.
Lemma lem1533344 (x : real) : (term136 x) = (term138 x).
Proof. exact (TRANS (@lem1533331 x) (@lem1533343 x)). Qed.
Lemma lem1533345 (x : real) : (term138 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1533346 (x : real) : (term136 x) = x.
Proof. exact (TRANS (@lem1533344 x) (@lem1533345 x)). Qed.
Lemma lem1533347 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1533348 (x : real) : (term139 x) = (real_add x).
Proof. exact (MK_COMB (@lem1533347) (@lem1533346 x)). Qed.
Lemma lem1533349 (x : real) (y : real) : (term135 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem1533348 x) (@lem1533330 y)). Qed.
Lemma lem1533350 (x : real) (y : real) : (term134 x y) = (term115 x y).
Proof. exact (TRANS (@lem1533329 x y) (@lem1533349 x y)). Qed.
Lemma lem1533351 (x : real) (y : real) : (term374 x y) = (term115 x y).
Proof. exact (TRANS (@lem1533328 x y) (@lem1533350 x y)). Qed.
Lemma lem1533352 (x : real) (y : real) : (term269 y x) = (term115 x y).
Proof. exact (TRANS (@lem1533327 x y) (@lem1533351 x y)). Qed.
Lemma lem1533355 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1533356 (x : real) (y : real) : (term375 y x) = (term229 x y).
Proof. exact (MK_COMB (@lem1533355 y) (@lem1533352 x y)). Qed.
Lemma lem1533357 (x : real) (y : real) : (term229 x y) = (term230 x y).
Proof. exact (@lem1483484 x y (term117 y)). Qed.
Lemma lem1533358 (y : real) : (term231 y) = (term232 y).
Proof. exact (@lem1483442 term28 y). Qed.
Lemma lem1533360 (m : nat) : (term233 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1533361 : term234 = term48.
Proof. exact (@lem1533360 term36). Qed.
Lemma lem1533362 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1533363 : term235 = term236.
Proof. exact (MK_COMB (@lem1533362) (@lem1533361)). Qed.
Lemma lem1533364 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1533365 (y : real) : (term232 y) = (term237 y).
Proof. exact (MK_COMB (@lem1533363) (@lem1533364 y)). Qed.
Lemma lem1533366 (y : real) : (term231 y) = (term237 y).
Proof. exact (TRANS (@lem1533358 y) (@lem1533365 y)). Qed.
Lemma lem1533367 (y : real) : (term237 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1533368 (y : real) : (term231 y) = term48.
Proof. exact (TRANS (@lem1533366 y) (@lem1533367 y)). Qed.
Lemma lem1533369 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1533370 (y : real) (x : real) : (term230 x y) = (term238 x).
Proof. exact (MK_COMB (@lem1533369 x) (@lem1533368 y)). Qed.
Lemma lem1533371 (y : real) (x : real) : (term229 x y) = (term238 x).
Proof. exact (TRANS (@lem1533357 x y) (@lem1533370 y x)). Qed.
Lemma lem1533372 (x : real) : (term238 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1533373 (y : real) (x : real) : (term229 x y) = x.
Proof. exact (TRANS (@lem1533371 y x) (@lem1533372 x)). Qed.
Lemma lem1533374 (y : real) (x : real) : (term375 y x) = x.
Proof. exact (TRANS (@lem1533356 x y) (@lem1533373 y x)). Qed.
Lemma lem1533383 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1533384 (y : real) (x : real) : (term373 y x) = (term239 x).
Proof. exact (MK_COMB (@lem1533383 x) (@lem1533374 y x)). Qed.
Lemma lem1533385 (x : real) : (term239 x) = (term232 x).
Proof. exact (@lem1483440 term28 x). Qed.
Lemma lem1533387 (m : nat) : (term233 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1533388 : term234 = term48.
Proof. exact (@lem1533387 term36). Qed.
Lemma lem1533389 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1533390 : term235 = term236.
Proof. exact (MK_COMB (@lem1533389) (@lem1533388)). Qed.
Lemma lem1533391 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1533392 (x : real) : (term232 x) = (term237 x).
Proof. exact (MK_COMB (@lem1533390) (@lem1533391 x)). Qed.
Lemma lem1533393 (x : real) : (term239 x) = (term237 x).
Proof. exact (TRANS (@lem1533385 x) (@lem1533392 x)). Qed.
Lemma lem1533394 (x : real) : (term237 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1533395 (x : real) : (term239 x) = term48.
Proof. exact (TRANS (@lem1533393 x) (@lem1533394 x)). Qed.
Lemma lem1533396 (y : real) (x : real) : (term373 y x) = term48.
Proof. exact (TRANS (@lem1533384 y x) (@lem1533395 x)). Qed.
Lemma lem1533397 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1533398 (y : real) (x : real) : (term376 y x) = term241.
Proof. exact (MK_COMB (@lem1533397) (@lem1533396 y x)). Qed.
Lemma lem1533399 (y : real) (x : real) : (term377 y x) = term243.
Proof. exact (MK_COMB (@lem1533398 y x) (@lem1533312)). Qed.
Lemma lem1533400 : term243 = term244.
Proof. exact (@lem1483519 term48 term48). Qed.
Lemma lem1533402 (x : nat) : (term177 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1533403 : term178 = term48.
Proof. exact (@lem1533402 term36). Qed.
Lemma lem1533404 : term245 = term245.
Proof. exact (eq_refl term245). Qed.
Lemma lem1533405 : term244 = term246.
Proof. exact (MK_COMB (@lem1533404) (@lem1533403)). Qed.
Lemma lem1533406 : term246 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1533407 : term244 = term48.
Proof. exact (TRANS (@lem1533405) (@lem1533406)). Qed.
Lemma lem1533408 : term243 = term48.
Proof. exact (TRANS (@lem1533400) (@lem1533407)). Qed.
Lemma lem1533409 (y : real) (x : real) : (term377 y x) = term48.
Proof. exact (TRANS (@lem1533399 y x) (@lem1533408)). Qed.
Lemma lem1533410 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1533411 (y : real) (x : real) : (term378 y x) = term248.
Proof. exact (MK_COMB (@lem1533410) (@lem1533409 y x)). Qed.
Lemma lem1533412 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1533413 (y : real) (x : real) : (term372 y x) = term249.
Proof. exact (MK_COMB (@lem1533411 y x) (@lem1533412)). Qed.
Lemma lem1533414 (y : real) (x : real) : (term371 y x) = term249.
Proof. exact (TRANS (@lem1533311 y x) (@lem1533413 y x)). Qed.
Lemma lem1533415 (y : real) (x : real) : (term379 y x) = (term380 y x).
Proof. exact (@lem1483525 (term381 y x) term48). Qed.
Lemma lem1533416 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1533422 (y : real) (x : real) : (real_sub y x) = (term115 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1533427 (x : real) (y : real) : (term115 y x) = (term116 x y).
Proof. exact (@lem1483488 (term117 x) y). Qed.
Lemma lem1533429 (x : real) (y : real) : (real_sub y x) = (term116 x y).
Proof. exact (TRANS (@lem1533422 y x) (@lem1533427 x y)). Qed.
Lemma lem1533430 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1533431 (x : real) (y : real) : (term269 y x) = (term374 x y).
Proof. exact (MK_COMB (@lem1533430) (@lem1533429 x y)). Qed.
Lemma lem1533432 (x : real) (y : real) : (term374 x y) = (term134 x y).
Proof. exact (@lem1483512 (term116 x y)). Qed.
Lemma lem1533433 (x : real) (y : real) : (term134 x y) = (term135 x y).
Proof. exact (@lem1483508 (term117 x) term28 y). Qed.
Lemma lem1533434 (y : real) : (term117 y) = (term117 y).
Proof. exact (eq_refl (term117 y)). Qed.
Lemma lem1533435 (x : real) : (term136 x) = (term137 x).
Proof. exact (@lem1483476 term28 term28 x). Qed.
Lemma lem1533437 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1533438 : term34 = term35.
Proof. exact (@lem1533437 term36 term36). Qed.
Lemma lem1533439 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1533440 : term38 = term36.
Proof. exact (EQ_MP (@lem1533439) (@lem940073)). Qed.
Lemma lem1533441 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1533442 : term35 = term39.
Proof. exact (MK_COMB (@lem1533441) (@lem1533440)). Qed.
Lemma lem1533443 : term34 = term39.
Proof. exact (TRANS (@lem1533438) (@lem1533442)). Qed.
Lemma lem1533444 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1533445 : term40 = term41.
Proof. exact (MK_COMB (@lem1533444) (@lem1533443)). Qed.
Lemma lem1533446 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1533447 (x : real) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem1533445) (@lem1533446 x)). Qed.
Lemma lem1533448 (x : real) : (term136 x) = (term138 x).
Proof. exact (TRANS (@lem1533435 x) (@lem1533447 x)). Qed.
Lemma lem1533449 (x : real) : (term138 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1533450 (x : real) : (term136 x) = x.
Proof. exact (TRANS (@lem1533448 x) (@lem1533449 x)). Qed.
Lemma lem1533451 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1533452 (x : real) : (term139 x) = (real_add x).
Proof. exact (MK_COMB (@lem1533451) (@lem1533450 x)). Qed.
Lemma lem1533453 (x : real) (y : real) : (term135 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem1533452 x) (@lem1533434 y)). Qed.
Lemma lem1533454 (x : real) (y : real) : (term134 x y) = (term115 x y).
Proof. exact (TRANS (@lem1533433 x y) (@lem1533453 x y)). Qed.
Lemma lem1533455 (x : real) (y : real) : (term374 x y) = (term115 x y).
Proof. exact (TRANS (@lem1533432 x y) (@lem1533454 x y)). Qed.
Lemma lem1533456 (x : real) (y : real) : (term269 y x) = (term115 x y).
Proof. exact (TRANS (@lem1533431 x y) (@lem1533455 x y)). Qed.
Lemma lem1533465 (y : real) : (term126 y) = (term126 y).
Proof. exact (eq_refl (term126 y)). Qed.
Lemma lem1533466 (x : real) (y : real) : (term382 y x) = (term188 x y).
Proof. exact (MK_COMB (@lem1533465 y) (@lem1533456 x y)). Qed.
Lemma lem1533467 (x : real) (y : real) : (term188 x y) = (term189 x y).
Proof. exact (@lem1483484 x (term117 y) (term117 y)). Qed.
Lemma lem1533468 (y : real) : (term190 y) = (term191 y).
Proof. exact (@lem1483438 term28 term28 y). Qed.
Lemma lem1533469 : term192 = term193.
Proof. exact (@lem1367763 term36 term36). Qed.
Lemma lem1533470 : term194 = term195.
Proof. exact (@lem706885). Qed.
Lemma lem1533471 : (term194 = term195) = (term196 = term197).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term195). Qed.
Lemma lem1533472 : term196 = term197.
Proof. exact (EQ_MP (@lem1533471) (@lem1533470)). Qed.
Lemma lem1533473 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1533474 : term198 = term199.
Proof. exact (MK_COMB (@lem1533473) (@lem1533472)). Qed.
Lemma lem1533475 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1533476 : term193 = term200.
Proof. exact (MK_COMB (@lem1533475) (@lem1533474)). Qed.
Lemma lem1533477 : term192 = term200.
Proof. exact (TRANS (@lem1533469) (@lem1533476)). Qed.
Lemma lem1533478 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1533479 : term201 = term202.
Proof. exact (MK_COMB (@lem1533478) (@lem1533477)). Qed.
Lemma lem1533480 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1533481 (y : real) : (term191 y) = (term203 y).
Proof. exact (MK_COMB (@lem1533479) (@lem1533480 y)). Qed.
Lemma lem1533482 (y : real) : (term190 y) = (term203 y).
Proof. exact (TRANS (@lem1533468 y) (@lem1533481 y)). Qed.
Lemma lem1533483 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1533484 (x : real) (y : real) : (term189 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem1533483 x) (@lem1533482 y)). Qed.
Lemma lem1533485 (x : real) (y : real) : (term188 x y) = (term204 x y).
Proof. exact (TRANS (@lem1533467 x y) (@lem1533484 x y)). Qed.
Lemma lem1533486 (x : real) (y : real) : (term382 y x) = (term204 x y).
Proof. exact (TRANS (@lem1533466 x y) (@lem1533485 x y)). Qed.
Lemma lem1533489 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1533490 (x : real) (y : real) : (term381 y x) = (term205 x y).
Proof. exact (MK_COMB (@lem1533489 x) (@lem1533486 x y)). Qed.
Lemma lem1533491 (x : real) (y : real) : (term205 x y) = (term206 x y).
Proof. exact (@lem1483490 x x (term203 y)). Qed.
Lemma lem1533492 (x : real) : (real_add x x) = (term207 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1533493 : term208 = term198.
Proof. exact (@lem1367770 term36 term36). Qed.
Lemma lem1533494 : term194 = term195.
Proof. exact (@lem706885). Qed.
Lemma lem1533495 : (term194 = term195) = (term196 = term197).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term195). Qed.
Lemma lem1533496 : term196 = term197.
Proof. exact (EQ_MP (@lem1533495) (@lem1533494)). Qed.
Lemma lem1533497 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1533498 : term198 = term199.
Proof. exact (MK_COMB (@lem1533497) (@lem1533496)). Qed.
Lemma lem1533499 : term208 = term199.
Proof. exact (TRANS (@lem1533493) (@lem1533498)). Qed.
Lemma lem1533500 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1533501 : term209 = term210.
Proof. exact (MK_COMB (@lem1533500) (@lem1533499)). Qed.
Lemma lem1533502 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1533503 (x : real) : (term207 x) = (term211 x).
Proof. exact (MK_COMB (@lem1533501) (@lem1533502 x)). Qed.
Lemma lem1533504 (x : real) : (real_add x x) = (term211 x).
Proof. exact (TRANS (@lem1533492 x) (@lem1533503 x)). Qed.
Lemma lem1533505 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1533506 (x : real) : (term212 x) = (term213 x).
Proof. exact (MK_COMB (@lem1533505) (@lem1533504 x)). Qed.
Lemma lem1533507 (y : real) : (term203 y) = (term203 y).
Proof. exact (eq_refl (term203 y)). Qed.
Lemma lem1533508 (x : real) (y : real) : (term206 x y) = (term214 x y).
Proof. exact (MK_COMB (@lem1533506 x) (@lem1533507 y)). Qed.
Lemma lem1533509 (x : real) (y : real) : (term205 x y) = (term214 x y).
Proof. exact (TRANS (@lem1533491 x y) (@lem1533508 x y)). Qed.
Lemma lem1533510 (x : real) (y : real) : (term381 y x) = (term214 x y).
Proof. exact (TRANS (@lem1533490 x y) (@lem1533509 x y)). Qed.
Lemma lem1533511 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1533512 (x : real) (y : real) : (term383 y x) = (term216 x y).
Proof. exact (MK_COMB (@lem1533511) (@lem1533510 x y)). Qed.
Lemma lem1533513 (x : real) (y : real) : (term384 y x) = (term218 x y).
Proof. exact (MK_COMB (@lem1533512 x y) (@lem1533416)). Qed.
Lemma lem1533514 (x : real) (y : real) : (term218 x y) = (term219 x y).
Proof. exact (@lem1483519 (term214 x y) term48). Qed.
Lemma lem1533516 (x : nat) : (term177 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1533517 : term178 = term48.
Proof. exact (@lem1533516 term36). Qed.
Lemma lem1533518 (x : real) (y : real) : (term220 x y) = (term220 x y).
Proof. exact (eq_refl (term220 x y)). Qed.
Lemma lem1533519 (x : real) (y : real) : (term219 x y) = (term221 x y).
Proof. exact (MK_COMB (@lem1533518 x y) (@lem1533517)). Qed.
Lemma lem1533520 (x : real) (y : real) : (term221 x y) = (term214 x y).
Proof. exact (@lem1483450 (term214 x y)). Qed.
Lemma lem1533521 (x : real) (y : real) : (term219 x y) = (term214 x y).
Proof. exact (TRANS (@lem1533519 x y) (@lem1533520 x y)). Qed.
Lemma lem1533522 (x : real) (y : real) : (term218 x y) = (term214 x y).
Proof. exact (TRANS (@lem1533514 x y) (@lem1533521 x y)). Qed.
Lemma lem1533523 (x : real) (y : real) : (term384 y x) = (term214 x y).
Proof. exact (TRANS (@lem1533513 x y) (@lem1533522 x y)). Qed.
Lemma lem1533524 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1533525 (x : real) (y : real) : (term385 y x) = (term223 x y).
Proof. exact (MK_COMB (@lem1533524) (@lem1533523 x y)). Qed.
Lemma lem1533526 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1533527 (x : real) (y : real) : (term380 y x) = (term224 x y).
Proof. exact (MK_COMB (@lem1533525 x y) (@lem1533526)). Qed.
Lemma lem1533528 (x : real) (y : real) : (term379 y x) = (term224 x y).
Proof. exact (TRANS (@lem1533415 y x) (@lem1533527 x y)). Qed.
Lemma lem1533529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1533530 (y : real) (x : real) : (term386 y x) = term301.
Proof. exact (MK_COMB (@lem1533529) (@lem1533414 y x)). Qed.
Lemma lem1533531 (x : real) (y : real) : (term329 y x) = (term387 x y).
Proof. exact (MK_COMB (@lem1533530 y x) (@lem1533528 x y)). Qed.
Lemma lem1533532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1533533 (x : real) (y : real) : (term158 y x) = (term388 x y).
Proof. exact (MK_COMB (@lem1533532) (@lem1533310 x y)). Qed.
Lemma lem1533534 (x : real) (y : real) : (term331 y x) = (term389 x y).
Proof. exact (MK_COMB (@lem1533533 x y) (@lem1533531 x y)). Qed.
Lemma lem1533535 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1533536 (x : real) (y : real) : (term337 y x) = (term390 x y).
Proof. exact (MK_COMB (@lem1533535) (@lem1533258 x y)). Qed.
Lemma lem1533537 (x : real) (y : real) : (term338 y x) = (term391 x y).
Proof. exact (MK_COMB (@lem1533536 x y) (@lem1533534 x y)). Qed.
Lemma lem1533548 (x : real) (y : real) : (term324 y x) = (term391 x y).
Proof. exact (TRANS (@lem1533055 y x) (@lem1533537 x y)). Qed.
Lemma lem1533549 (x : real) (y : real) : (term50 y x) = (term391 x y).
Proof. exact (TRANS (@lem1533039 y x) (@lem1533548 x y)). Qed.
Lemma lem1533550 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1533551 (x : real) (y : real) : (term56 y x) = (term392 x y).
Proof. exact (MK_COMB (@lem1533550) (@lem1532945 x y)). Qed.
Lemma lem1533552 (x : real) (y : real) : (term57 y x) = (term393 x y).
Proof. exact (MK_COMB (@lem1533551 x y) (@lem1533549 x y)). Qed.
Lemma lem1533553 (x : real) (y : real) (h1 : term393 x y) : term393 x y.
Proof. exact (h1). Qed.
Lemma lem1533554 (x : real) (y : real) (h1 : term306 x y) : term306 x y.
Proof. exact (h1). Qed.
Lemma lem1533555 (x : real) (y : real) (h1 : term254 x y) : term254 x y.
Proof. exact (h1). Qed.
Lemma lem1533556 (x : real) (y : real) (h1 : term254 x y) : term252 x y.
Proof. exact (proj2 (@lem1533555 x y h1)). Qed.
Lemma lem1533558 (x : real) (y : real) (h1 : term254 x y) : term249.
Proof. exact (proj2 (@lem1533556 x y h1)). Qed.
Lemma lem1533561 (n : nat) (m : nat) : (term394 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1533562 : term249 = term395.
Proof. exact (@lem1533561 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1533563 : term395 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1533564 : term249 = False.
Proof. exact (TRANS (@lem1533562) (@lem1533563)). Qed.
Lemma lem1533565 (x : real) (y : real) (h1 : term254 x y) : False.
Proof. exact (EQ_MP (@lem1533564) (@lem1533558 x y h1)). Qed.
Lemma lem1533566 (x : real) (y : real) (h1 : term304 x y) : term304 x y.
Proof. exact (h1). Qed.
Lemma lem1533567 (x : real) (y : real) (h1 : term304 x y) : term302 x y.
Proof. exact (proj2 (@lem1533566 x y h1)). Qed.
Lemma lem1533570 (x : real) (y : real) (h1 : term304 x y) : term249.
Proof. exact (proj1 (@lem1533567 x y h1)). Qed.
Lemma lem1533572 (n : nat) (m : nat) : (term394 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1533573 : term249 = term395.
Proof. exact (@lem1533572 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1533574 : term395 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1533575 : term249 = False.
Proof. exact (TRANS (@lem1533573) (@lem1533574)). Qed.
Lemma lem1533576 (x : real) (y : real) (h1 : term304 x y) : False.
Proof. exact (EQ_MP (@lem1533575) (@lem1533570 x y h1)). Qed.
Lemma lem1533577 (x : real) (y : real) (h1 : term306 x y) : False.
Proof. exact (or_elim (@lem1533554 x y h1) (fun h0 : term254 x y => @lem1533565 x y h0) (fun h0 : term304 x y => @lem1533576 x y h0)). Qed.
Lemma lem1533578 (x : real) (y : real) (h1 : term391 x y) : term391 x y.
Proof. exact (h1). Qed.
Lemma lem1533579 (x : real) (y : real) (h1 : term365 x y) : term365 x y.
Proof. exact (h1). Qed.
Lemma lem1533580 (x : real) (y : real) (h1 : term365 x y) : term363 x y.
Proof. exact (proj2 (@lem1533579 x y h1)). Qed.
Lemma lem1533582 (x : real) (y : real) (h1 : term365 x y) : term249.
Proof. exact (proj2 (@lem1533580 x y h1)). Qed.
Lemma lem1533585 (n : nat) (m : nat) : (term394 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1533586 : term249 = term395.
Proof. exact (@lem1533585 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1533587 : term395 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1533588 : term249 = False.
Proof. exact (TRANS (@lem1533586) (@lem1533587)). Qed.
Lemma lem1533589 (x : real) (y : real) (h1 : term365 x y) : False.
Proof. exact (EQ_MP (@lem1533588) (@lem1533582 x y h1)). Qed.
Lemma lem1533590 (x : real) (y : real) (h1 : term389 x y) : term389 x y.
Proof. exact (h1). Qed.
Lemma lem1533591 (x : real) (y : real) (h1 : term389 x y) : term387 x y.
Proof. exact (proj2 (@lem1533590 x y h1)). Qed.
Lemma lem1533594 (x : real) (y : real) (h1 : term389 x y) : term249.
Proof. exact (proj1 (@lem1533591 x y h1)). Qed.
Lemma lem1533596 (n : nat) (m : nat) : (term394 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1533597 : term249 = term395.
Proof. exact (@lem1533596 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1533598 : term395 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1533599 : term249 = False.
Proof. exact (TRANS (@lem1533597) (@lem1533598)). Qed.
Lemma lem1533600 (x : real) (y : real) (h1 : term389 x y) : False.
Proof. exact (EQ_MP (@lem1533599) (@lem1533594 x y h1)). Qed.
Lemma lem1533601 (x : real) (y : real) (h1 : term391 x y) : False.
Proof. exact (or_elim (@lem1533578 x y h1) (fun h0 : term365 x y => @lem1533589 x y h0) (fun h0 : term389 x y => @lem1533600 x y h0)). Qed.
Lemma lem1533602 (x : real) (y : real) (h1 : term393 x y) : False.
Proof. exact (or_elim (@lem1533553 x y h1) (fun h0 : term306 x y => @lem1533577 x y h0) (fun h0 : term391 x y => @lem1533601 x y h0)). Qed.
Lemma lem1533603 (y : real) (x : real) (h1 : term57 y x) : term57 y x.
Proof. exact (h1). Qed.
Lemma lem1533604 (y : real) (x : real) (h1 : term57 y x) : term393 x y.
Proof. exact (EQ_MP (@lem1533552 x y) (@lem1533603 y x h1)). Qed.
Lemma lem1533605 (y : real) (x : real) (h1 : term57 y x) : (term393 x y) = False.
Proof. exact (prop_ext (fun h2 : term393 x y => @lem1533602 x y h2) (fun h2 : False => @lem1533604 y x h1)). Qed.
Lemma lem1533606 (y : real) (x : real) (h1 : term57 y x) : False.
Proof. exact (EQ_MP (@lem1533605 y x h1) (@lem1533604 y x h1)). Qed.
Lemma lem1533607 (x : real) (h1 : term59 x) : term59 x.
Proof. exact (h1). Qed.
Lemma lem1533608 (x : real) (h1 : term59 x) : False.
Proof. exact (ex_elim (@lem1533607 x h1) (fun y : real => fun h0 : term58 x y => @lem1533606 y x h0)). Qed.
Lemma lem1533609 (h1 : term61) : term61.
Proof. exact (h1). Qed.
Lemma lem1533610 (h1 : term61) : False.
Proof. exact (ex_elim (@lem1533609 h1) (fun x : real => fun h0 : term60 x => @lem1533608 x h0)). Qed.
Lemma lem1533611 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1533612 (h1 : term12) : term61.
Proof. exact (EQ_MP (@lem1532341) (@lem1533611 h1)). Qed.
Lemma lem1533613 (h1 : term12) : term61 = False.
Proof. exact (prop_ext (fun h2 : term61 => @lem1533610 h2) (fun h2 : False => @lem1533612 h1)). Qed.
Lemma lem1533614 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1533613 h1) (@lem1533612 h1)). Qed.
Lemma lem1533615 : term396.
Proof. exact (fun h0 : term12 => @lem1533614 h0). Qed.
Lemma lem1533616 : term397.
Proof. exact (@lem1386578 term398). Qed.
Lemma lem1533617 : term398.
Proof. exact (@lem1533616 (@lem1533615)). Qed.
