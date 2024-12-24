Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MIN_ASSOC_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482698_spec.
Require Import thm1482715_spec.
Require Import thm1482716_spec.
Require Import thm1483429_spec.
Require Import thm1483436_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483476_spec.
Require Import thm1483488_spec.
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
Require Import thm940073_spec.
Lemma lem1573185 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1573186 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (@lem1573185 (term4 x y)). Qed.
Lemma lem1573187 (x : real) (y : real) (z : real) : (term5 x y z) = ((term6 x y z) = (term7 x y z)).
Proof. exact (eq_refl (term5 x y z)). Qed.
Lemma lem1573188 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1573190 (x : real) (y : real) (z : real) : (term8 x y z) = (term9 x y z).
Proof. exact (MK_COMB (@lem1573188) (@lem1573187 x y z)). Qed.
Lemma lem1573191 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : real => @lem1573190 x y z)). Qed.
Lemma lem1573192 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573193 (x : real) (y : real) : (term3 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1573192) (@lem1573191 x y)). Qed.
Lemma lem1573194 (x : real) (y : real) : (term2 x y) = (term12 x y).
Proof. exact (TRANS (@lem1573186 x y) (@lem1573193 x y)). Qed.
Lemma lem1573195 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1573196 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem1573195 (term15 x)). Qed.
Lemma lem1573197 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1573198 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1573199 (x : real) (y : real) : (term18 x y) = (term2 x y).
Proof. exact (MK_COMB (@lem1573198) (@lem1573197 x y)). Qed.
Lemma lem1573200 (x : real) (y : real) : (term18 x y) = (term12 x y).
Proof. exact (TRANS (@lem1573199 x y) (@lem1573194 x y)). Qed.
Lemma lem1573201 (x : real) : (term19 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1573200 x y)). Qed.
Lemma lem1573202 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573203 (x : real) : (term14 x) = (term21 x).
Proof. exact (MK_COMB (@lem1573202) (@lem1573201 x)). Qed.
Lemma lem1573204 (x : real) : (term13 x) = (term21 x).
Proof. exact (TRANS (@lem1573196 x) (@lem1573203 x)). Qed.
Lemma lem1573205 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1573206 : term22 = term23.
Proof. exact (@lem1573205 term24). Qed.
Lemma lem1573207 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1573208 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1573209 (x : real) : (term27 x) = (term13 x).
Proof. exact (MK_COMB (@lem1573208) (@lem1573207 x)). Qed.
Lemma lem1573210 (x : real) : (term27 x) = (term21 x).
Proof. exact (TRANS (@lem1573209 x) (@lem1573204 x)). Qed.
Lemma lem1573211 : term28 = term29.
Proof. exact (fun_ext (fun x : real => @lem1573210 x)). Qed.
Lemma lem1573212 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573213 : term23 = term30.
Proof. exact (MK_COMB (@lem1573212) (@lem1573211)). Qed.
Lemma lem1573215 : term22 = term30.
Proof. exact (TRANS (@lem1573206) (@lem1573213)). Qed.
Lemma lem1573218 (x : real) (y : real) (z : real) : (term9 x y z) = (term9 x y z).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1573219 (x : real) (y : real) : (term11 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : real => @lem1573218 x y z)). Qed.
Lemma lem1573220 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573221 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1573220) (@lem1573219 x y)). Qed.
Lemma lem1573222 (x : real) : (term20 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1573221 x y)). Qed.
Lemma lem1573223 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573224 (x : real) : (term21 x) = (term21 x).
Proof. exact (MK_COMB (@lem1573223) (@lem1573222 x)). Qed.
Lemma lem1573225 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1573224 x)). Qed.
Lemma lem1573226 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573227 : term30 = term30.
Proof. exact (MK_COMB (@lem1573226) (@lem1573225)). Qed.
Lemma lem1573228 : term22 = term30.
Proof. exact (TRANS (@lem1573215) (@lem1573227)). Qed.
Lemma lem1573229 (x : real) (y : real) (z : real) : (term9 x y z) = (term31 x y z).
Proof. exact (@lem1483554 (term6 x y z) (term7 x y z)). Qed.
Lemma lem1573242 (x : real) (y : real) (z : real) : (term32 x y z) = (term33 x y z).
Proof. exact (@lem1483519 (term6 x y z) (term7 x y z)). Qed.
Lemma lem1573243 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1573244 (x : real) (y : real) (z : real) : (term34 x y z) = (term35 x y z).
Proof. exact (MK_COMB (@lem1573243) (@lem1573242 x y z)). Qed.
Lemma lem1573245 (x : real) (y : real) (z : real) : (term35 x y z) = (term36 x y z).
Proof. exact (@lem1483512 (term33 x y z)). Qed.
Lemma lem1573246 (x : real) (y : real) (z : real) : (term36 x y z) = (term37 x y z).
Proof. exact (@lem1483508 (term6 x y z) term38 (term39 x y z)). Qed.
Lemma lem1573247 (x : real) (y : real) (z : real) : (term40 x y z) = (term41 x y z).
Proof. exact (@lem1483476 term38 term38 (term7 x y z)). Qed.
Lemma lem1573249 (m : nat) (n : nat) : (term42 m n) = (term43 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1573250 : term44 = term45.
Proof. exact (@lem1573249 term46 term46). Qed.
Lemma lem1573251 : (term47 = (BIT1 0)) = (term48 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1573252 : term48 = term46.
Proof. exact (EQ_MP (@lem1573251) (@lem940073)). Qed.
Lemma lem1573253 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1573254 : term45 = term49.
Proof. exact (MK_COMB (@lem1573253) (@lem1573252)). Qed.
Lemma lem1573255 : term44 = term49.
Proof. exact (TRANS (@lem1573250) (@lem1573254)). Qed.
Lemma lem1573256 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1573257 : term50 = term51.
Proof. exact (MK_COMB (@lem1573256) (@lem1573255)). Qed.
Lemma lem1573258 (x : real) (y : real) (z : real) : (term7 x y z) = (term7 x y z).
Proof. exact (eq_refl (term7 x y z)). Qed.
Lemma lem1573259 (x : real) (y : real) (z : real) : (term41 x y z) = (term52 x y z).
Proof. exact (MK_COMB (@lem1573257) (@lem1573258 x y z)). Qed.
Lemma lem1573260 (x : real) (y : real) (z : real) : (term40 x y z) = (term52 x y z).
Proof. exact (TRANS (@lem1573247 x y z) (@lem1573259 x y z)). Qed.
Lemma lem1573261 (x : real) (y : real) (z : real) : (term52 x y z) = (term7 x y z).
Proof. exact (@lem1483436 (term7 x y z)). Qed.
Lemma lem1573262 (x : real) (y : real) (z : real) : (term40 x y z) = (term7 x y z).
Proof. exact (TRANS (@lem1573260 x y z) (@lem1573261 x y z)). Qed.
Lemma lem1573265 (x : real) (y : real) (z : real) : (term53 x y z) = (term53 x y z).
Proof. exact (eq_refl (term53 x y z)). Qed.
Lemma lem1573266 (x : real) (y : real) (z : real) : (term37 x y z) = (term54 x y z).
Proof. exact (MK_COMB (@lem1573265 x y z) (@lem1573262 x y z)). Qed.
Lemma lem1573267 (x : real) (y : real) (z : real) : (term36 x y z) = (term54 x y z).
Proof. exact (TRANS (@lem1573246 x y z) (@lem1573266 x y z)). Qed.
Lemma lem1573268 (x : real) (y : real) (z : real) : (term35 x y z) = (term54 x y z).
Proof. exact (TRANS (@lem1573245 x y z) (@lem1573267 x y z)). Qed.
Lemma lem1573269 (x : real) (y : real) (z : real) : (term55 x y z) = (term55 x y z).
Proof. exact (eq_refl (term55 x y z)). Qed.
Lemma lem1573270 (x : real) (y : real) (z : real) : ((term34 x y z) = (term35 x y z)) = ((term34 x y z) = (term54 x y z)).
Proof. exact (MK_COMB (@lem1573269 x y z) (@lem1573268 x y z)). Qed.
Lemma lem1573271 (x : real) (y : real) (z : real) : (term34 x y z) = (term54 x y z).
Proof. exact (EQ_MP (@lem1573270 x y z) (@lem1573244 x y z)). Qed.
Lemma lem1573272 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1573273 (x : real) (y : real) (z : real) : (term56 x y z) = (term57 x y z).
Proof. exact (MK_COMB (@lem1573272) (@lem1573271 x y z)). Qed.
Lemma lem1573274 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573275 (x : real) (y : real) (z : real) : (term59 x y z) = (term60 x y z).
Proof. exact (MK_COMB (@lem1573273 x y z) (@lem1573274)). Qed.
Lemma lem1573276 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1573277 (x : real) (y : real) (z : real) : (term61 x y z) = (term62 x y z).
Proof. exact (MK_COMB (@lem1573276) (@lem1573242 x y z)). Qed.
Lemma lem1573278 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573279 (x : real) (y : real) (z : real) : (term63 x y z) = (term64 x y z).
Proof. exact (MK_COMB (@lem1573277 x y z) (@lem1573278)). Qed.
Lemma lem1573280 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573281 (x : real) (y : real) (z : real) : (term65 x y z) = (term66 x y z).
Proof. exact (MK_COMB (@lem1573280) (@lem1573279 x y z)). Qed.
Lemma lem1573282 (x : real) (y : real) (z : real) : (term31 x y z) = (term67 x y z).
Proof. exact (MK_COMB (@lem1573281 x y z) (@lem1573275 x y z)). Qed.
Lemma lem1573283 (x : real) (y : real) (z : real) : (term9 x y z) = (term67 x y z).
Proof. exact (TRANS (@lem1573229 x y z) (@lem1573282 x y z)). Qed.
Lemma lem1573284 (x : real) (y : real) : (term11 x y) = (term68 x y).
Proof. exact (fun_ext (fun z : real => @lem1573283 x y z)). Qed.
Lemma lem1573285 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573286 (x : real) (y : real) : (term12 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1573285) (@lem1573284 x y)). Qed.
Lemma lem1573287 (x : real) : (term20 x) = (term70 x).
Proof. exact (fun_ext (fun y : real => @lem1573286 x y)). Qed.
Lemma lem1573288 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573289 (x : real) : (term21 x) = (term71 x).
Proof. exact (MK_COMB (@lem1573288) (@lem1573287 x)). Qed.
Lemma lem1573290 : term29 = term72.
Proof. exact (fun_ext (fun x : real => @lem1573289 x)). Qed.
Lemma lem1573291 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573292 : term30 = term73.
Proof. exact (MK_COMB (@lem1573291) (@lem1573290)). Qed.
Lemma lem1573293 : term22 = term73.
Proof. exact (TRANS (@lem1573228) (@lem1573292)). Qed.
Lemma lem1573303 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1573304 (P : real -> Prop) (Q : real -> Prop) : (term76 P Q) = (term77 P Q).
Proof. exact (@lem1573303 real P Q). Qed.
Lemma lem1573305 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (@lem1573304 (term80 x y) (term81 x y)). Qed.
Lemma lem1573306 (x : real) (y : real) (z : real) : (term82 x y z) = (term64 x y z).
Proof. exact (eq_refl (term82 x y z)). Qed.
Lemma lem1573307 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573308 (x : real) (y : real) (z : real) : (term83 x y z) = (term66 x y z).
Proof. exact (MK_COMB (@lem1573307) (@lem1573306 x y z)). Qed.
Lemma lem1573309 (x : real) (y : real) (z : real) : (term84 x y z) = (term60 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1573310 (x : real) (y : real) (z : real) : (term85 x y z) = (term67 x y z).
Proof. exact (MK_COMB (@lem1573308 x y z) (@lem1573309 x y z)). Qed.
Lemma lem1573311 (x : real) (y : real) : (term86 x y) = (term68 x y).
Proof. exact (fun_ext (fun z : real => @lem1573310 x y z)). Qed.
Lemma lem1573312 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573313 (x : real) (y : real) : (term78 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1573312) (@lem1573311 x y)). Qed.
Lemma lem1573314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1573315 (x : real) (y : real) : (term87 x y) = (term88 x y).
Proof. exact (MK_COMB (@lem1573314) (@lem1573313 x y)). Qed.
Lemma lem1573316 (x : real) (y : real) (z : real) : (term82 x y z) = (term64 x y z).
Proof. exact (eq_refl (term82 x y z)). Qed.
Lemma lem1573317 (x : real) (y : real) : (term89 x y) = (term80 x y).
Proof. exact (fun_ext (fun z : real => @lem1573316 x y z)). Qed.
Lemma lem1573318 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573319 (x : real) (y : real) : (term90 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1573318) (@lem1573317 x y)). Qed.
Lemma lem1573320 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573321 (x : real) (y : real) : (term92 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1573320) (@lem1573319 x y)). Qed.
Lemma lem1573322 (x : real) (y : real) (z : real) : (term84 x y z) = (term60 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1573323 (x : real) (y : real) : (term94 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1573322 x y z)). Qed.
Lemma lem1573324 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573325 (x : real) (y : real) : (term95 x y) = (term96 x y).
Proof. exact (MK_COMB (@lem1573324) (@lem1573323 x y)). Qed.
Lemma lem1573326 (x : real) (y : real) : (term79 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1573321 x y) (@lem1573325 x y)). Qed.
Lemma lem1573327 (x : real) (y : real) : ((term78 x y) = (term79 x y)) = ((term69 x y) = (term97 x y)).
Proof. exact (MK_COMB (@lem1573315 x y) (@lem1573326 x y)). Qed.
Lemma lem1573328 (x : real) (y : real) : (term69 x y) = (term97 x y).
Proof. exact (EQ_MP (@lem1573327 x y) (@lem1573305 x y)). Qed.
Lemma lem1573337 (x : real) : (term70 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1573328 x y)). Qed.
Lemma lem1573338 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573339 (x : real) : (term71 x) = (term99 x).
Proof. exact (MK_COMB (@lem1573338) (@lem1573337 x)). Qed.
Lemma lem1573341 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1573342 (P : real -> Prop) (Q : real -> Prop) : (term76 P Q) = (term77 P Q).
Proof. exact (@lem1573341 real P Q). Qed.
Lemma lem1573343 (x : real) : (term100 x) = (term101 x).
Proof. exact (@lem1573342 (term102 x) (term103 x)). Qed.
Lemma lem1573344 (x : real) (y : real) : (term104 x y) = (term91 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1573345 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573346 (x : real) (y : real) : (term105 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1573345) (@lem1573344 x y)). Qed.
Lemma lem1573347 (x : real) (y : real) : (term106 x y) = (term96 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1573348 (x : real) (y : real) : (term107 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1573346 x y) (@lem1573347 x y)). Qed.
Lemma lem1573349 (x : real) : (term108 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1573348 x y)). Qed.
Lemma lem1573350 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573351 (x : real) : (term100 x) = (term99 x).
Proof. exact (MK_COMB (@lem1573350) (@lem1573349 x)). Qed.
Lemma lem1573352 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1573353 (x : real) : (term109 x) = (term110 x).
Proof. exact (MK_COMB (@lem1573352) (@lem1573351 x)). Qed.
Lemma lem1573354 (x : real) (y : real) : (term104 x y) = (term91 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1573355 (x : real) : (term111 x) = (term102 x).
Proof. exact (fun_ext (fun y : real => @lem1573354 x y)). Qed.
Lemma lem1573356 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573357 (x : real) : (term112 x) = (term113 x).
Proof. exact (MK_COMB (@lem1573356) (@lem1573355 x)). Qed.
Lemma lem1573358 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573359 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1573358) (@lem1573357 x)). Qed.
Lemma lem1573360 (x : real) (y : real) : (term106 x y) = (term96 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1573361 (x : real) : (term116 x) = (term103 x).
Proof. exact (fun_ext (fun y : real => @lem1573360 x y)). Qed.
Lemma lem1573362 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573363 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1573362) (@lem1573361 x)). Qed.
Lemma lem1573364 (x : real) : (term101 x) = (term119 x).
Proof. exact (MK_COMB (@lem1573359 x) (@lem1573363 x)). Qed.
Lemma lem1573365 (x : real) : ((term100 x) = (term101 x)) = ((term99 x) = (term119 x)).
Proof. exact (MK_COMB (@lem1573353 x) (@lem1573364 x)). Qed.
Lemma lem1573366 (x : real) : (term99 x) = (term119 x).
Proof. exact (EQ_MP (@lem1573365 x) (@lem1573343 x)). Qed.
Lemma lem1573383 (x : real) : (term71 x) = (term119 x).
Proof. exact (TRANS (@lem1573339 x) (@lem1573366 x)). Qed.
Lemma lem1573384 : term72 = term120.
Proof. exact (fun_ext (fun x : real => @lem1573383 x)). Qed.
Lemma lem1573385 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573386 : term73 = term121.
Proof. exact (MK_COMB (@lem1573385) (@lem1573384)). Qed.
Lemma lem1573388 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1573389 (P : real -> Prop) (Q : real -> Prop) : (term76 P Q) = (term77 P Q).
Proof. exact (@lem1573388 real P Q). Qed.
Lemma lem1573390 : term122 = term123.
Proof. exact (@lem1573389 term124 term125). Qed.
Lemma lem1573391 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1573392 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573393 (x : real) : (term127 x) = (term115 x).
Proof. exact (MK_COMB (@lem1573392) (@lem1573391 x)). Qed.
Lemma lem1573394 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1573395 (x : real) : (term129 x) = (term119 x).
Proof. exact (MK_COMB (@lem1573393 x) (@lem1573394 x)). Qed.
Lemma lem1573396 : term130 = term120.
Proof. exact (fun_ext (fun x : real => @lem1573395 x)). Qed.
Lemma lem1573397 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573398 : term122 = term121.
Proof. exact (MK_COMB (@lem1573397) (@lem1573396)). Qed.
Lemma lem1573399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1573400 : term131 = term132.
Proof. exact (MK_COMB (@lem1573399) (@lem1573398)). Qed.
Lemma lem1573401 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1573402 : term133 = term124.
Proof. exact (fun_ext (fun x : real => @lem1573401 x)). Qed.
Lemma lem1573403 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573404 : term134 = term135.
Proof. exact (MK_COMB (@lem1573403) (@lem1573402)). Qed.
Lemma lem1573405 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573406 : term136 = term137.
Proof. exact (MK_COMB (@lem1573405) (@lem1573404)). Qed.
Lemma lem1573407 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1573408 : term138 = term125.
Proof. exact (fun_ext (fun x : real => @lem1573407 x)). Qed.
Lemma lem1573409 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573410 : term139 = term140.
Proof. exact (MK_COMB (@lem1573409) (@lem1573408)). Qed.
Lemma lem1573411 : term123 = term141.
Proof. exact (MK_COMB (@lem1573406) (@lem1573410)). Qed.
Lemma lem1573412 : (term122 = term123) = (term121 = term141).
Proof. exact (MK_COMB (@lem1573400) (@lem1573411)). Qed.
Lemma lem1573413 : term121 = term141.
Proof. exact (EQ_MP (@lem1573412) (@lem1573390)). Qed.
Lemma lem1573438 : term73 = term141.
Proof. exact (TRANS (@lem1573386) (@lem1573413)). Qed.
Lemma lem1573440 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1573441 (P : real -> Prop) (Q : real -> Prop) : (term77 P Q) = (term76 P Q).
Proof. exact (@lem1573440 real P Q). Qed.
Lemma lem1573442 : term123 = term122.
Proof. exact (@lem1573441 term124 term125). Qed.
Lemma lem1573443 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1573444 : term133 = term124.
Proof. exact (fun_ext (fun x : real => @lem1573443 x)). Qed.
Lemma lem1573445 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573446 : term134 = term135.
Proof. exact (MK_COMB (@lem1573445) (@lem1573444)). Qed.
Lemma lem1573447 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573448 : term136 = term137.
Proof. exact (MK_COMB (@lem1573447) (@lem1573446)). Qed.
Lemma lem1573449 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1573450 : term138 = term125.
Proof. exact (fun_ext (fun x : real => @lem1573449 x)). Qed.
Lemma lem1573451 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573452 : term139 = term140.
Proof. exact (MK_COMB (@lem1573451) (@lem1573450)). Qed.
Lemma lem1573453 : term123 = term141.
Proof. exact (MK_COMB (@lem1573448) (@lem1573452)). Qed.
Lemma lem1573454 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1573455 : term142 = term143.
Proof. exact (MK_COMB (@lem1573454) (@lem1573453)). Qed.
Lemma lem1573456 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1573457 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573458 (x : real) : (term127 x) = (term115 x).
Proof. exact (MK_COMB (@lem1573457) (@lem1573456 x)). Qed.
Lemma lem1573459 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1573460 (x : real) : (term129 x) = (term119 x).
Proof. exact (MK_COMB (@lem1573458 x) (@lem1573459 x)). Qed.
Lemma lem1573461 : term130 = term120.
Proof. exact (fun_ext (fun x : real => @lem1573460 x)). Qed.
Lemma lem1573462 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573463 : term122 = term121.
Proof. exact (MK_COMB (@lem1573462) (@lem1573461)). Qed.
Lemma lem1573464 : (term123 = term122) = (term141 = term121).
Proof. exact (MK_COMB (@lem1573455) (@lem1573463)). Qed.
Lemma lem1573465 : term141 = term121.
Proof. exact (EQ_MP (@lem1573464) (@lem1573442)). Qed.
Lemma lem1573467 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1573468 (P : real -> Prop) (Q : real -> Prop) : (term77 P Q) = (term76 P Q).
Proof. exact (@lem1573467 real P Q). Qed.
Lemma lem1573469 (x : real) : (term101 x) = (term100 x).
Proof. exact (@lem1573468 (term102 x) (term103 x)). Qed.
Lemma lem1573470 (x : real) (y : real) : (term104 x y) = (term91 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1573471 (x : real) : (term111 x) = (term102 x).
Proof. exact (fun_ext (fun y : real => @lem1573470 x y)). Qed.
Lemma lem1573472 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573473 (x : real) : (term112 x) = (term113 x).
Proof. exact (MK_COMB (@lem1573472) (@lem1573471 x)). Qed.
Lemma lem1573474 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573475 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1573474) (@lem1573473 x)). Qed.
Lemma lem1573476 (x : real) (y : real) : (term106 x y) = (term96 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1573477 (x : real) : (term116 x) = (term103 x).
Proof. exact (fun_ext (fun y : real => @lem1573476 x y)). Qed.
Lemma lem1573478 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573479 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1573478) (@lem1573477 x)). Qed.
Lemma lem1573480 (x : real) : (term101 x) = (term119 x).
Proof. exact (MK_COMB (@lem1573475 x) (@lem1573479 x)). Qed.
Lemma lem1573481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1573482 (x : real) : (term144 x) = (term145 x).
Proof. exact (MK_COMB (@lem1573481) (@lem1573480 x)). Qed.
Lemma lem1573483 (x : real) (y : real) : (term104 x y) = (term91 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1573484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573485 (x : real) (y : real) : (term105 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1573484) (@lem1573483 x y)). Qed.
Lemma lem1573486 (x : real) (y : real) : (term106 x y) = (term96 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1573487 (x : real) (y : real) : (term107 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1573485 x y) (@lem1573486 x y)). Qed.
Lemma lem1573488 (x : real) : (term108 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1573487 x y)). Qed.
Lemma lem1573489 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573490 (x : real) : (term100 x) = (term99 x).
Proof. exact (MK_COMB (@lem1573489) (@lem1573488 x)). Qed.
Lemma lem1573491 (x : real) : ((term101 x) = (term100 x)) = ((term119 x) = (term99 x)).
Proof. exact (MK_COMB (@lem1573482 x) (@lem1573490 x)). Qed.
Lemma lem1573492 (x : real) : (term119 x) = (term99 x).
Proof. exact (EQ_MP (@lem1573491 x) (@lem1573469 x)). Qed.
Lemma lem1573494 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1573495 (P : real -> Prop) (Q : real -> Prop) : (term77 P Q) = (term76 P Q).
Proof. exact (@lem1573494 real P Q). Qed.
Lemma lem1573496 (x : real) (y : real) : (term79 x y) = (term78 x y).
Proof. exact (@lem1573495 (term80 x y) (term81 x y)). Qed.
Lemma lem1573497 (x : real) (y : real) (z : real) : (term82 x y z) = (term64 x y z).
Proof. exact (eq_refl (term82 x y z)). Qed.
Lemma lem1573498 (x : real) (y : real) : (term89 x y) = (term80 x y).
Proof. exact (fun_ext (fun z : real => @lem1573497 x y z)). Qed.
Lemma lem1573499 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573500 (x : real) (y : real) : (term90 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1573499) (@lem1573498 x y)). Qed.
Lemma lem1573501 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573502 (x : real) (y : real) : (term92 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1573501) (@lem1573500 x y)). Qed.
Lemma lem1573503 (x : real) (y : real) (z : real) : (term84 x y z) = (term60 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1573504 (x : real) (y : real) : (term94 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1573503 x y z)). Qed.
Lemma lem1573505 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573506 (x : real) (y : real) : (term95 x y) = (term96 x y).
Proof. exact (MK_COMB (@lem1573505) (@lem1573504 x y)). Qed.
Lemma lem1573507 (x : real) (y : real) : (term79 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1573502 x y) (@lem1573506 x y)). Qed.
Lemma lem1573508 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1573509 (x : real) (y : real) : (term146 x y) = (term147 x y).
Proof. exact (MK_COMB (@lem1573508) (@lem1573507 x y)). Qed.
Lemma lem1573510 (x : real) (y : real) (z : real) : (term82 x y z) = (term64 x y z).
Proof. exact (eq_refl (term82 x y z)). Qed.
Lemma lem1573511 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573512 (x : real) (y : real) (z : real) : (term83 x y z) = (term66 x y z).
Proof. exact (MK_COMB (@lem1573511) (@lem1573510 x y z)). Qed.
Lemma lem1573513 (x : real) (y : real) (z : real) : (term84 x y z) = (term60 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1573514 (x : real) (y : real) (z : real) : (term85 x y z) = (term67 x y z).
Proof. exact (MK_COMB (@lem1573512 x y z) (@lem1573513 x y z)). Qed.
Lemma lem1573515 (x : real) (y : real) : (term86 x y) = (term68 x y).
Proof. exact (fun_ext (fun z : real => @lem1573514 x y z)). Qed.
Lemma lem1573516 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573517 (x : real) (y : real) : (term78 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1573516) (@lem1573515 x y)). Qed.
Lemma lem1573518 (x : real) (y : real) : ((term79 x y) = (term78 x y)) = ((term97 x y) = (term69 x y)).
Proof. exact (MK_COMB (@lem1573509 x y) (@lem1573517 x y)). Qed.
Lemma lem1573519 (x : real) (y : real) : (term97 x y) = (term69 x y).
Proof. exact (EQ_MP (@lem1573518 x y) (@lem1573496 x y)). Qed.
Lemma lem1573520 (x : real) : (term98 x) = (term70 x).
Proof. exact (fun_ext (fun y : real => @lem1573519 x y)). Qed.
Lemma lem1573521 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573522 (x : real) : (term99 x) = (term71 x).
Proof. exact (MK_COMB (@lem1573521) (@lem1573520 x)). Qed.
Lemma lem1573523 (x : real) : (term119 x) = (term71 x).
Proof. exact (TRANS (@lem1573492 x) (@lem1573522 x)). Qed.
Lemma lem1573524 : term120 = term72.
Proof. exact (fun_ext (fun x : real => @lem1573523 x)). Qed.
Lemma lem1573525 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573526 : term121 = term73.
Proof. exact (MK_COMB (@lem1573525) (@lem1573524)). Qed.
Lemma lem1573527 : term141 = term73.
Proof. exact (TRANS (@lem1573465) (@lem1573526)). Qed.
Lemma lem1573528 : term73 = term73.
Proof. exact (TRANS (@lem1573438) (@lem1573527)). Qed.
Lemma lem1573531 : term22 = term73.
Proof. exact (TRANS (@lem1573293) (@lem1573528)). Qed.
Lemma lem1573536 (x : real) (y : real) (z : real) : (term67 x y z) = (term67 x y z).
Proof. exact (eq_refl (term67 x y z)). Qed.
Lemma lem1573537 (x : real) (y : real) : (term68 x y) = (term68 x y).
Proof. exact (fun_ext (fun z : real => @lem1573536 x y z)). Qed.
Lemma lem1573538 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573539 (x : real) (y : real) : (term69 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1573538) (@lem1573537 x y)). Qed.
Lemma lem1573540 (x : real) : (term70 x) = (term70 x).
Proof. exact (fun_ext (fun y : real => @lem1573539 x y)). Qed.
Lemma lem1573541 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573542 (x : real) : (term71 x) = (term71 x).
Proof. exact (MK_COMB (@lem1573541) (@lem1573540 x)). Qed.
Lemma lem1573543 : term72 = term72.
Proof. exact (fun_ext (fun x : real => @lem1573542 x)). Qed.
Lemma lem1573544 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1573545 : term73 = term73.
Proof. exact (MK_COMB (@lem1573544) (@lem1573543)). Qed.
Lemma lem1573546 : term22 = term73.
Proof. exact (TRANS (@lem1573531) (@lem1573545)). Qed.
Lemma lem1573548 (x : real) (a : real) (y : real) (r : real) : (term148 x y a r) = (term149 x a y r).
Proof. exact (proj1 (@lem1482715 x a (@el real) y (@el real) r)). Qed.
Lemma lem1573549 (x : real) (y : real) (z : real) : (term64 x y z) = (term150 x y z).
Proof. exact (@lem1573548 x (term39 x y z) (real_min y z) term58). Qed.
Lemma lem1573562 (x : real) (y : real) (z : real) : (term151 x y z) = (term152 x y z).
Proof. exact (@lem1483488 (real_min y z) (term39 x y z)). Qed.
Lemma lem1573563 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1573564 (x : real) (y : real) (z : real) : (term153 x y z) = (term154 x y z).
Proof. exact (MK_COMB (@lem1573563) (@lem1573562 x y z)). Qed.
Lemma lem1573565 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573566 (x : real) (y : real) (z : real) : (term155 x y z) = (term156 x y z).
Proof. exact (MK_COMB (@lem1573564 x y z) (@lem1573565)). Qed.
Lemma lem1573579 (x : real) (y : real) (z : real) : (term157 y z x) = (term158 x y z).
Proof. exact (@lem1483488 x (term39 x y z)). Qed.
Lemma lem1573580 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1573581 (x : real) (y : real) (z : real) : (term159 y z x) = (term160 x y z).
Proof. exact (MK_COMB (@lem1573580) (@lem1573579 x y z)). Qed.
Lemma lem1573582 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573583 (x : real) (y : real) (z : real) : (term161 y z x) = (term162 x y z).
Proof. exact (MK_COMB (@lem1573581 x y z) (@lem1573582)). Qed.
Lemma lem1573584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1573585 (x : real) (y : real) (z : real) : (term163 y z x) = (term164 x y z).
Proof. exact (MK_COMB (@lem1573584) (@lem1573583 x y z)). Qed.
Lemma lem1573586 (x : real) (y : real) (z : real) : (term150 x y z) = (term165 x y z).
Proof. exact (MK_COMB (@lem1573585 x y z) (@lem1573566 x y z)). Qed.
Lemma lem1573587 (x : real) (y : real) (z : real) : (term64 x y z) = (term165 x y z).
Proof. exact (TRANS (@lem1573549 x y z) (@lem1573586 x y z)). Qed.
Lemma lem1573589 (x : real) (a : real) (y : real) (r : real) : (term148 x y a r) = (term149 x a y r).
Proof. exact (proj1 (@lem1482715 x a (@el real) y (@el real) r)). Qed.
Lemma lem1573590 (x : real) (y : real) (z : real) : (term156 x y z) = (term166 x y z).
Proof. exact (@lem1573589 y (term39 x y z) z term58). Qed.
Lemma lem1573603 (x : real) (y : real) (z : real) : (term167 x y z) = (term168 x y z).
Proof. exact (@lem1483488 z (term39 x y z)). Qed.
Lemma lem1573604 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1573605 (x : real) (y : real) (z : real) : (term169 x y z) = (term170 x y z).
Proof. exact (MK_COMB (@lem1573604) (@lem1573603 x y z)). Qed.
Lemma lem1573606 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573607 (x : real) (y : real) (z : real) : (term171 x y z) = (term172 x y z).
Proof. exact (MK_COMB (@lem1573605 x y z) (@lem1573606)). Qed.
Lemma lem1573620 (x : real) (y : real) (z : real) : (term173 x z y) = (term174 x y z).
Proof. exact (@lem1483488 y (term39 x y z)). Qed.
Lemma lem1573621 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1573622 (x : real) (y : real) (z : real) : (term175 x z y) = (term176 x y z).
Proof. exact (MK_COMB (@lem1573621) (@lem1573620 x y z)). Qed.
Lemma lem1573623 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573624 (x : real) (y : real) (z : real) : (term177 x z y) = (term178 x y z).
Proof. exact (MK_COMB (@lem1573622 x y z) (@lem1573623)). Qed.
Lemma lem1573625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1573626 (x : real) (y : real) (z : real) : (term179 x z y) = (term180 x y z).
Proof. exact (MK_COMB (@lem1573625) (@lem1573624 x y z)). Qed.
Lemma lem1573627 (x : real) (y : real) (z : real) : (term166 x y z) = (term181 x y z).
Proof. exact (MK_COMB (@lem1573626 x y z) (@lem1573607 x y z)). Qed.
Lemma lem1573628 (x : real) (y : real) (z : real) : (term156 x y z) = (term181 x y z).
Proof. exact (TRANS (@lem1573590 x y z) (@lem1573627 x y z)). Qed.
Lemma lem1573629 (x : real) (y : real) (z : real) : (term164 x y z) = (term164 x y z).
Proof. exact (eq_refl (term164 x y z)). Qed.
Lemma lem1573630 (x : real) (y : real) (z : real) : (term165 x y z) = (term182 x y z).
Proof. exact (MK_COMB (@lem1573629 x y z) (@lem1573628 x y z)). Qed.
Lemma lem1573631 (x : real) (y : real) (z : real) : (term64 x y z) = (term182 x y z).
Proof. exact (TRANS (@lem1573587 x y z) (@lem1573630 x y z)). Qed.
Lemma lem1573632 (x : real) (y : real) (z : real) : (term183 x y z) = (term182 x y z).
Proof. exact (eq_refl (term183 x y z)). Qed.
Lemma lem1573633 (x : real) (y : real) (z : real) : (term182 x y z) = (term183 x y z).
Proof. exact (SYM (@lem1573632 x y z)). Qed.
Lemma lem1573634 (x : real) (y : real) (z : real) : (term183 x y z) = (term184 x y z).
Proof. exact (@lem1483429 (real_min x y) (term185 x y z) z). Qed.
Lemma lem1573635 (x : real) (y : real) (z : real) : (term182 x y z) = (term184 x y z).
Proof. exact (TRANS (@lem1573633 x y z) (@lem1573634 x y z)). Qed.
Lemma lem1573636 (x : real) (y : real) (z : real) : (term186 x y z) = (term187 x y z).
Proof. exact (eq_refl (term186 x y z)). Qed.
Lemma lem1573637 (x : real) (y : real) (z : real) : (term188 x y z) = (term188 x y z).
Proof. exact (eq_refl (term188 x y z)). Qed.
Lemma lem1573638 (x : real) (y : real) (z : real) : (term189 x y z) = (term190 x y z).
Proof. exact (MK_COMB (@lem1573637 x y z) (@lem1573636 x y z)). Qed.
Lemma lem1573639 (z : real) (x : real) (y : real) : (term191 z x y) = (term192 z x y).
Proof. exact (eq_refl (term191 z x y)). Qed.
Lemma lem1573640 (z : real) (x : real) (y : real) : (term193 z x y) = (term193 z x y).
Proof. exact (eq_refl (term193 z x y)). Qed.
Lemma lem1573641 (z : real) (x : real) (y : real) : (term194 z x y) = (term195 z x y).
Proof. exact (MK_COMB (@lem1573640 z x y) (@lem1573639 z x y)). Qed.
Lemma lem1573642 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573643 (z : real) (x : real) (y : real) : (term196 z x y) = (term197 z x y).
Proof. exact (MK_COMB (@lem1573642) (@lem1573641 z x y)). Qed.
Lemma lem1573644 (x : real) (y : real) (z : real) : (term184 x y z) = (term198 x y z).
Proof. exact (MK_COMB (@lem1573643 z x y) (@lem1573638 x y z)). Qed.
Lemma lem1573645 (x : real) (y : real) (z : real) : (term199 x y z) = (term199 x y z).
Proof. exact (eq_refl (term199 x y z)). Qed.
Lemma lem1573646 (x : real) (y : real) (z : real) : ((term182 x y z) = (term184 x y z)) = ((term182 x y z) = (term198 x y z)).
Proof. exact (MK_COMB (@lem1573645 x y z) (@lem1573644 x y z)). Qed.
Lemma lem1573647 (x : real) (y : real) (z : real) : (term182 x y z) = (term198 x y z).
Proof. exact (EQ_MP (@lem1573646 x y z) (@lem1573635 x y z)). Qed.
Lemma lem1573648 (z : real) (x : real) (y : real) : (term200 z x y) = (term201 z x y).
Proof. exact (@lem1483527 z (real_min x y)). Qed.
Lemma lem1573661 (z : real) (x : real) (y : real) : (term202 z x y) = (term203 z x y).
Proof. exact (@lem1483519 z (real_min x y)). Qed.
Lemma lem1573662 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1573663 (z : real) (x : real) (y : real) : (term204 z x y) = (term205 z x y).
Proof. exact (MK_COMB (@lem1573662) (@lem1573661 z x y)). Qed.
Lemma lem1573664 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573665 (z : real) (x : real) (y : real) : (term201 z x y) = (term206 z x y).
Proof. exact (MK_COMB (@lem1573663 z x y) (@lem1573664)). Qed.
Lemma lem1573666 (z : real) (x : real) (y : real) : (term200 z x y) = (term206 z x y).
Proof. exact (TRANS (@lem1573648 z x y) (@lem1573665 z x y)). Qed.
Lemma lem1573667 (x : real) (y : real) : (term207 x y) = (term208 x y).
Proof. exact (@lem1483525 (term209 x y) term58). Qed.
Lemma lem1573685 (x : real) (y : real) : (term210 x y) = (term211 x y).
Proof. exact (@lem1483519 (term209 x y) term58). Qed.
Lemma lem1573687 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1573688 : term213 = term58.
Proof. exact (@lem1573687 term46). Qed.
Lemma lem1573689 (x : real) (y : real) : (term214 x y) = (term214 x y).
Proof. exact (eq_refl (term214 x y)). Qed.
Lemma lem1573690 (x : real) (y : real) : (term211 x y) = (term215 x y).
Proof. exact (MK_COMB (@lem1573689 x y) (@lem1573688)). Qed.
Lemma lem1573691 (x : real) (y : real) : (term215 x y) = (term209 x y).
Proof. exact (@lem1483450 (term209 x y)). Qed.
Lemma lem1573692 (x : real) (y : real) : (term211 x y) = (term209 x y).
Proof. exact (TRANS (@lem1573690 x y) (@lem1573691 x y)). Qed.
Lemma lem1573694 (x : real) (y : real) : (term210 x y) = (term209 x y).
Proof. exact (TRANS (@lem1573685 x y) (@lem1573692 x y)). Qed.
Lemma lem1573695 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1573696 (x : real) (y : real) : (term216 x y) = (term217 x y).
Proof. exact (MK_COMB (@lem1573695) (@lem1573694 x y)). Qed.
Lemma lem1573697 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573698 (x : real) (y : real) : (term208 x y) = (term207 x y).
Proof. exact (MK_COMB (@lem1573696 x y) (@lem1573697)). Qed.
Lemma lem1573699 (x : real) (y : real) : (term207 x y) = (term207 x y).
Proof. exact (TRANS (@lem1573667 x y) (@lem1573698 x y)). Qed.
Lemma lem1573700 (x : real) (y : real) : (term218 x y) = (term219 x y).
Proof. exact (@lem1483525 (term220 x y) term58). Qed.
Lemma lem1573718 (x : real) (y : real) : (term221 x y) = (term222 x y).
Proof. exact (@lem1483519 (term220 x y) term58). Qed.
Lemma lem1573720 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1573721 : term213 = term58.
Proof. exact (@lem1573720 term46). Qed.
Lemma lem1573722 (x : real) (y : real) : (term223 x y) = (term223 x y).
Proof. exact (eq_refl (term223 x y)). Qed.
Lemma lem1573723 (x : real) (y : real) : (term222 x y) = (term224 x y).
Proof. exact (MK_COMB (@lem1573722 x y) (@lem1573721)). Qed.
Lemma lem1573724 (x : real) (y : real) : (term224 x y) = (term220 x y).
Proof. exact (@lem1483450 (term220 x y)). Qed.
Lemma lem1573725 (x : real) (y : real) : (term222 x y) = (term220 x y).
Proof. exact (TRANS (@lem1573723 x y) (@lem1573724 x y)). Qed.
Lemma lem1573727 (x : real) (y : real) : (term221 x y) = (term220 x y).
Proof. exact (TRANS (@lem1573718 x y) (@lem1573725 x y)). Qed.
Lemma lem1573728 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1573729 (x : real) (y : real) : (term225 x y) = (term226 x y).
Proof. exact (MK_COMB (@lem1573728) (@lem1573727 x y)). Qed.
Lemma lem1573730 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573731 (x : real) (y : real) : (term219 x y) = (term218 x y).
Proof. exact (MK_COMB (@lem1573729 x y) (@lem1573730)). Qed.
Lemma lem1573732 (x : real) (y : real) : (term218 x y) = (term218 x y).
Proof. exact (TRANS (@lem1573700 x y) (@lem1573731 x y)). Qed.
Lemma lem1573733 (z : real) (x : real) (y : real) : (term227 z x y) = (term228 z x y).
Proof. exact (@lem1483525 (term203 z x y) term58). Qed.
Lemma lem1573751 (z : real) (x : real) (y : real) : (term229 z x y) = (term230 z x y).
Proof. exact (@lem1483519 (term203 z x y) term58). Qed.
Lemma lem1573753 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1573754 : term213 = term58.
Proof. exact (@lem1573753 term46). Qed.
Lemma lem1573755 (z : real) (x : real) (y : real) : (term231 z x y) = (term231 z x y).
Proof. exact (eq_refl (term231 z x y)). Qed.
Lemma lem1573756 (z : real) (x : real) (y : real) : (term230 z x y) = (term232 z x y).
Proof. exact (MK_COMB (@lem1573755 z x y) (@lem1573754)). Qed.
Lemma lem1573757 (z : real) (x : real) (y : real) : (term232 z x y) = (term203 z x y).
Proof. exact (@lem1483450 (term203 z x y)). Qed.
Lemma lem1573758 (z : real) (x : real) (y : real) : (term230 z x y) = (term203 z x y).
Proof. exact (TRANS (@lem1573756 z x y) (@lem1573757 z x y)). Qed.
Lemma lem1573760 (z : real) (x : real) (y : real) : (term229 z x y) = (term203 z x y).
Proof. exact (TRANS (@lem1573751 z x y) (@lem1573758 z x y)). Qed.
Lemma lem1573761 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1573762 (z : real) (x : real) (y : real) : (term233 z x y) = (term234 z x y).
Proof. exact (MK_COMB (@lem1573761) (@lem1573760 z x y)). Qed.
Lemma lem1573763 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573764 (z : real) (x : real) (y : real) : (term228 z x y) = (term227 z x y).
Proof. exact (MK_COMB (@lem1573762 z x y) (@lem1573763)). Qed.
Lemma lem1573765 (z : real) (x : real) (y : real) : (term227 z x y) = (term227 z x y).
Proof. exact (TRANS (@lem1573733 z x y) (@lem1573764 z x y)). Qed.
Lemma lem1573766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1573767 (x : real) (y : real) : (term235 x y) = (term235 x y).
Proof. exact (MK_COMB (@lem1573766) (@lem1573732 x y)). Qed.
Lemma lem1573768 (z : real) (x : real) (y : real) : (term236 z x y) = (term236 z x y).
Proof. exact (MK_COMB (@lem1573767 x y) (@lem1573765 z x y)). Qed.
Lemma lem1573769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1573770 (x : real) (y : real) : (term237 x y) = (term237 x y).
Proof. exact (MK_COMB (@lem1573769) (@lem1573699 x y)). Qed.
Lemma lem1573771 (z : real) (x : real) (y : real) : (term192 z x y) = (term192 z x y).
Proof. exact (MK_COMB (@lem1573770 x y) (@lem1573768 z x y)). Qed.
Lemma lem1573772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1573773 (z : real) (x : real) (y : real) : (term193 z x y) = (term238 z x y).
Proof. exact (MK_COMB (@lem1573772) (@lem1573666 z x y)). Qed.
Lemma lem1573774 (z : real) (x : real) (y : real) : (term195 z x y) = (term239 z x y).
Proof. exact (MK_COMB (@lem1573773 z x y) (@lem1573771 z x y)). Qed.
Lemma lem1573775 (x : real) (y : real) (z : real) : (term240 x y z) = (term241 x y z).
Proof. exact (@lem1483525 (real_min x y) z). Qed.
Lemma lem1573781 (x : real) (y : real) (z : real) : (term242 x y z) = (term243 x y z).
Proof. exact (@lem1483519 (real_min x y) z). Qed.
Lemma lem1573786 (z : real) (x : real) (y : real) : (term243 x y z) = (term244 z x y).
Proof. exact (@lem1483488 (term245 z) (real_min x y)). Qed.
Lemma lem1573788 (z : real) (x : real) (y : real) : (term242 x y z) = (term244 z x y).
Proof. exact (TRANS (@lem1573781 x y z) (@lem1573786 z x y)). Qed.
Lemma lem1573789 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1573790 (z : real) (x : real) (y : real) : (term246 x y z) = (term247 z x y).
Proof. exact (MK_COMB (@lem1573789) (@lem1573788 z x y)). Qed.
Lemma lem1573791 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573792 (z : real) (x : real) (y : real) : (term241 x y z) = (term248 z x y).
Proof. exact (MK_COMB (@lem1573790 z x y) (@lem1573791)). Qed.
Lemma lem1573793 (z : real) (x : real) (y : real) : (term240 x y z) = (term248 z x y).
Proof. exact (TRANS (@lem1573775 x y z) (@lem1573792 z x y)). Qed.
Lemma lem1573794 (x : real) (z : real) : (term249 x z) = (term250 x z).
Proof. exact (@lem1483525 (term251 x z) term58). Qed.
Lemma lem1573812 (x : real) (z : real) : (term252 x z) = (term253 x z).
Proof. exact (@lem1483519 (term251 x z) term58). Qed.
Lemma lem1573814 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1573815 : term213 = term58.
Proof. exact (@lem1573814 term46). Qed.
Lemma lem1573816 (x : real) (z : real) : (term254 x z) = (term254 x z).
Proof. exact (eq_refl (term254 x z)). Qed.
Lemma lem1573817 (x : real) (z : real) : (term253 x z) = (term255 x z).
Proof. exact (MK_COMB (@lem1573816 x z) (@lem1573815)). Qed.
Lemma lem1573818 (x : real) (z : real) : (term255 x z) = (term251 x z).
Proof. exact (@lem1483450 (term251 x z)). Qed.
Lemma lem1573819 (x : real) (z : real) : (term253 x z) = (term251 x z).
Proof. exact (TRANS (@lem1573817 x z) (@lem1573818 x z)). Qed.
Lemma lem1573821 (x : real) (z : real) : (term252 x z) = (term251 x z).
Proof. exact (TRANS (@lem1573812 x z) (@lem1573819 x z)). Qed.
Lemma lem1573822 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1573823 (x : real) (z : real) : (term256 x z) = (term257 x z).
Proof. exact (MK_COMB (@lem1573822) (@lem1573821 x z)). Qed.
Lemma lem1573824 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573825 (x : real) (z : real) : (term250 x z) = (term249 x z).
Proof. exact (MK_COMB (@lem1573823 x z) (@lem1573824)). Qed.
Lemma lem1573826 (x : real) (z : real) : (term249 x z) = (term249 x z).
Proof. exact (TRANS (@lem1573794 x z) (@lem1573825 x z)). Qed.
Lemma lem1573827 (y : real) (z : real) : (term249 y z) = (term250 y z).
Proof. exact (@lem1483525 (term251 y z) term58). Qed.
Lemma lem1573845 (y : real) (z : real) : (term252 y z) = (term253 y z).
Proof. exact (@lem1483519 (term251 y z) term58). Qed.
Lemma lem1573847 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1573848 : term213 = term58.
Proof. exact (@lem1573847 term46). Qed.
Lemma lem1573849 (y : real) (z : real) : (term254 y z) = (term254 y z).
Proof. exact (eq_refl (term254 y z)). Qed.
Lemma lem1573850 (y : real) (z : real) : (term253 y z) = (term255 y z).
Proof. exact (MK_COMB (@lem1573849 y z) (@lem1573848)). Qed.
Lemma lem1573851 (y : real) (z : real) : (term255 y z) = (term251 y z).
Proof. exact (@lem1483450 (term251 y z)). Qed.
Lemma lem1573852 (y : real) (z : real) : (term253 y z) = (term251 y z).
Proof. exact (TRANS (@lem1573850 y z) (@lem1573851 y z)). Qed.
Lemma lem1573854 (y : real) (z : real) : (term252 y z) = (term251 y z).
Proof. exact (TRANS (@lem1573845 y z) (@lem1573852 y z)). Qed.
Lemma lem1573855 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1573856 (y : real) (z : real) : (term256 y z) = (term257 y z).
Proof. exact (MK_COMB (@lem1573855) (@lem1573854 y z)). Qed.
Lemma lem1573857 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573858 (y : real) (z : real) : (term250 y z) = (term249 y z).
Proof. exact (MK_COMB (@lem1573856 y z) (@lem1573857)). Qed.
Lemma lem1573859 (y : real) (z : real) : (term249 y z) = (term249 y z).
Proof. exact (TRANS (@lem1573827 y z) (@lem1573858 y z)). Qed.
Lemma lem1573860 (z : real) : (term258 z) = (term259 z).
Proof. exact (@lem1483525 (term260 z) term58). Qed.
Lemma lem1573861 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573873 (z : real) : (term260 z) = (term261 z).
Proof. exact (@lem1483442 term38 z). Qed.
Lemma lem1573875 (m : nat) : (term262 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1573876 : term263 = term58.
Proof. exact (@lem1573875 term46). Qed.
Lemma lem1573877 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1573878 : term264 = term265.
Proof. exact (MK_COMB (@lem1573877) (@lem1573876)). Qed.
Lemma lem1573879 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1573880 (z : real) : (term261 z) = (term266 z).
Proof. exact (MK_COMB (@lem1573878) (@lem1573879 z)). Qed.
Lemma lem1573881 (z : real) : (term260 z) = (term266 z).
Proof. exact (TRANS (@lem1573873 z) (@lem1573880 z)). Qed.
Lemma lem1573882 (z : real) : (term266 z) = term58.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1573884 (z : real) : (term260 z) = term58.
Proof. exact (TRANS (@lem1573881 z) (@lem1573882 z)). Qed.
Lemma lem1573885 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1573886 (z : real) : (term267 z) = term268.
Proof. exact (MK_COMB (@lem1573885) (@lem1573884 z)). Qed.
Lemma lem1573887 (z : real) : (term269 z) = term270.
Proof. exact (MK_COMB (@lem1573886 z) (@lem1573861)). Qed.
Lemma lem1573888 : term270 = term271.
Proof. exact (@lem1483519 term58 term58). Qed.
Lemma lem1573890 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1573891 : term213 = term58.
Proof. exact (@lem1573890 term46). Qed.
Lemma lem1573892 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem1573893 : term271 = term273.
Proof. exact (MK_COMB (@lem1573892) (@lem1573891)). Qed.
Lemma lem1573894 : term273 = term58.
Proof. exact (@lem1483448 term58). Qed.
Lemma lem1573895 : term271 = term58.
Proof. exact (TRANS (@lem1573893) (@lem1573894)). Qed.
Lemma lem1573896 : term270 = term58.
Proof. exact (TRANS (@lem1573888) (@lem1573895)). Qed.
Lemma lem1573897 (z : real) : (term269 z) = term58.
Proof. exact (TRANS (@lem1573887 z) (@lem1573896)). Qed.
Lemma lem1573898 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1573899 (z : real) : (term274 z) = term275.
Proof. exact (MK_COMB (@lem1573898) (@lem1573897 z)). Qed.
Lemma lem1573900 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573901 (z : real) : (term259 z) = term276.
Proof. exact (MK_COMB (@lem1573899 z) (@lem1573900)). Qed.
Lemma lem1573902 (z : real) : (term258 z) = term276.
Proof. exact (TRANS (@lem1573860 z) (@lem1573901 z)). Qed.
Lemma lem1573903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1573904 (y : real) (z : real) : (term277 y z) = (term277 y z).
Proof. exact (MK_COMB (@lem1573903) (@lem1573859 y z)). Qed.
Lemma lem1573905 (y : real) (z : real) : (term278 y z) = (term279 y z).
Proof. exact (MK_COMB (@lem1573904 y z) (@lem1573902 z)). Qed.
Lemma lem1573906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1573907 (x : real) (z : real) : (term277 x z) = (term277 x z).
Proof. exact (MK_COMB (@lem1573906) (@lem1573826 x z)). Qed.
Lemma lem1573908 (x : real) (y : real) (z : real) : (term187 x y z) = (term280 x y z).
Proof. exact (MK_COMB (@lem1573907 x z) (@lem1573905 y z)). Qed.
Lemma lem1573909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1573910 (z : real) (x : real) (y : real) : (term188 x y z) = (term281 z x y).
Proof. exact (MK_COMB (@lem1573909) (@lem1573793 z x y)). Qed.
Lemma lem1573911 (x : real) (y : real) (z : real) : (term190 x y z) = (term282 x y z).
Proof. exact (MK_COMB (@lem1573910 z x y) (@lem1573908 x y z)). Qed.
Lemma lem1573912 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573913 (z : real) (x : real) (y : real) : (term197 z x y) = (term283 z x y).
Proof. exact (MK_COMB (@lem1573912) (@lem1573774 z x y)). Qed.
Lemma lem1573914 (x : real) (y : real) (z : real) : (term198 x y z) = (term284 x y z).
Proof. exact (MK_COMB (@lem1573913 z x y) (@lem1573911 x y z)). Qed.
Lemma lem1573915 (x : real) (y : real) (z : real) : (term182 x y z) = (term284 x y z).
Proof. exact (TRANS (@lem1573647 x y z) (@lem1573914 x y z)). Qed.
Lemma lem1573917 (x : real) (a : real) (y : real) (r : real) : (term285 a x y r) = (term149 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1573918 (x : real) (z : real) (y : real) : (term248 z x y) = (term286 x z y).
Proof. exact (@lem1573917 x (term245 z) y term58). Qed.
Lemma lem1573931 (y : real) (z : real) : (term287 z y) = (term251 y z).
Proof. exact (@lem1483488 y (term245 z)). Qed.
Lemma lem1573932 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1573933 (y : real) (z : real) : (term288 z y) = (term257 y z).
Proof. exact (MK_COMB (@lem1573932) (@lem1573931 y z)). Qed.
Lemma lem1573934 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573935 (y : real) (z : real) : (term289 z y) = (term249 y z).
Proof. exact (MK_COMB (@lem1573933 y z) (@lem1573934)). Qed.
Lemma lem1573948 (x : real) (z : real) : (term287 z x) = (term251 x z).
Proof. exact (@lem1483488 x (term245 z)). Qed.
Lemma lem1573949 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1573950 (x : real) (z : real) : (term288 z x) = (term257 x z).
Proof. exact (MK_COMB (@lem1573949) (@lem1573948 x z)). Qed.
Lemma lem1573951 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573952 (x : real) (z : real) : (term289 z x) = (term249 x z).
Proof. exact (MK_COMB (@lem1573950 x z) (@lem1573951)). Qed.
Lemma lem1573953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1573954 (x : real) (z : real) : (term290 z x) = (term277 x z).
Proof. exact (MK_COMB (@lem1573953) (@lem1573952 x z)). Qed.
Lemma lem1573955 (x : real) (y : real) (z : real) : (term286 x z y) = (term291 x y z).
Proof. exact (MK_COMB (@lem1573954 x z) (@lem1573935 y z)). Qed.
Lemma lem1573956 (x : real) (y : real) (z : real) : (term248 z x y) = (term291 x y z).
Proof. exact (TRANS (@lem1573918 x z y) (@lem1573955 x y z)). Qed.
Lemma lem1573957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1573958 (x : real) (y : real) (z : real) : (term281 z x y) = (term292 x y z).
Proof. exact (MK_COMB (@lem1573957) (@lem1573956 x y z)). Qed.
Lemma lem1573959 (x : real) (y : real) (z : real) : (term280 x y z) = (term280 x y z).
Proof. exact (eq_refl (term280 x y z)). Qed.
Lemma lem1573962 (x : real) (y : real) (z : real) : (term282 x y z) = (term293 x y z).
Proof. exact (MK_COMB (@lem1573958 x y z) (@lem1573959 x y z)). Qed.
Lemma lem1573964 (z : real) (x : real) (y : real) : (term294 z x y) = (term239 z x y).
Proof. exact (eq_refl (term294 z x y)). Qed.
Lemma lem1573965 (z : real) (x : real) (y : real) : (term239 z x y) = (term294 z x y).
Proof. exact (SYM (@lem1573964 z x y)). Qed.
Lemma lem1573966 (x : real) (z : real) (y : real) : (term294 z x y) = (term295 x z y).
Proof. exact (@lem1483429 x (term296 x y z) y). Qed.
Lemma lem1573967 (x : real) (z : real) (y : real) : (term239 z x y) = (term295 x z y).
Proof. exact (TRANS (@lem1573965 z x y) (@lem1573966 x z y)). Qed.
Lemma lem1573968 (x : real) (z : real) (y : real) : (term297 x z y) = (term298 x z y).
Proof. exact (eq_refl (term297 x z y)). Qed.
Lemma lem1573969 (x : real) (y : real) : (term299 x y) = (term299 x y).
Proof. exact (eq_refl (term299 x y)). Qed.
Lemma lem1573970 (x : real) (z : real) (y : real) : (term300 x z y) = (term301 x z y).
Proof. exact (MK_COMB (@lem1573969 x y) (@lem1573968 x z y)). Qed.
Lemma lem1573971 (y : real) (z : real) (x : real) : (term302 y z x) = (term303 y z x).
Proof. exact (eq_refl (term302 y z x)). Qed.
Lemma lem1573972 (y : real) (x : real) : (term304 y x) = (term304 y x).
Proof. exact (eq_refl (term304 y x)). Qed.
Lemma lem1573973 (y : real) (z : real) (x : real) : (term305 y z x) = (term306 y z x).
Proof. exact (MK_COMB (@lem1573972 y x) (@lem1573971 y z x)). Qed.
Lemma lem1573974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573975 (y : real) (z : real) (x : real) : (term307 y z x) = (term308 y z x).
Proof. exact (MK_COMB (@lem1573974) (@lem1573973 y z x)). Qed.
Lemma lem1573976 (x : real) (z : real) (y : real) : (term295 x z y) = (term309 x z y).
Proof. exact (MK_COMB (@lem1573975 y z x) (@lem1573970 x z y)). Qed.
Lemma lem1573977 (z : real) (x : real) (y : real) : (term310 z x y) = (term310 z x y).
Proof. exact (eq_refl (term310 z x y)). Qed.
Lemma lem1573978 (x : real) (z : real) (y : real) : ((term239 z x y) = (term295 x z y)) = ((term239 z x y) = (term309 x z y)).
Proof. exact (MK_COMB (@lem1573977 z x y) (@lem1573976 x z y)). Qed.
Lemma lem1573979 (x : real) (z : real) (y : real) : (term239 z x y) = (term309 x z y).
Proof. exact (EQ_MP (@lem1573978 x z y) (@lem1573967 x z y)). Qed.
Lemma lem1573980 (y : real) (x : real) : (real_ge y x) = (term311 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1573986 (y : real) (x : real) : (real_sub y x) = (term251 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1573991 (x : real) (y : real) : (term251 y x) = (term287 x y).
Proof. exact (@lem1483488 (term245 x) y). Qed.
Lemma lem1573993 (x : real) (y : real) : (real_sub y x) = (term287 x y).
Proof. exact (TRANS (@lem1573986 y x) (@lem1573991 x y)). Qed.
Lemma lem1573994 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1573995 (x : real) (y : real) : (term312 y x) = (term313 x y).
Proof. exact (MK_COMB (@lem1573994) (@lem1573993 x y)). Qed.
Lemma lem1573996 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573997 (x : real) (y : real) : (term311 y x) = (term314 x y).
Proof. exact (MK_COMB (@lem1573995 x y) (@lem1573996)). Qed.
Lemma lem1573998 (x : real) (y : real) : (real_ge y x) = (term314 x y).
Proof. exact (TRANS (@lem1573980 y x) (@lem1573997 x y)). Qed.
Lemma lem1573999 (z : real) (x : real) : (term315 z x) = (term316 z x).
Proof. exact (@lem1483527 (term251 z x) term58). Qed.
Lemma lem1574000 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574013 (x : real) (z : real) : (term251 z x) = (term287 x z).
Proof. exact (@lem1483488 (term245 x) z). Qed.
Lemma lem1574014 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1574015 (x : real) (z : real) : (term317 z x) = (term318 x z).
Proof. exact (MK_COMB (@lem1574014) (@lem1574013 x z)). Qed.
Lemma lem1574016 (x : real) (z : real) : (term252 z x) = (term319 x z).
Proof. exact (MK_COMB (@lem1574015 x z) (@lem1574000)). Qed.
Lemma lem1574017 (x : real) (z : real) : (term319 x z) = (term320 x z).
Proof. exact (@lem1483519 (term287 x z) term58). Qed.
Lemma lem1574019 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1574020 : term213 = term58.
Proof. exact (@lem1574019 term46). Qed.
Lemma lem1574021 (x : real) (z : real) : (term321 x z) = (term321 x z).
Proof. exact (eq_refl (term321 x z)). Qed.
Lemma lem1574022 (x : real) (z : real) : (term320 x z) = (term322 x z).
Proof. exact (MK_COMB (@lem1574021 x z) (@lem1574020)). Qed.
Lemma lem1574023 (x : real) (z : real) : (term322 x z) = (term287 x z).
Proof. exact (@lem1483450 (term287 x z)). Qed.
Lemma lem1574024 (x : real) (z : real) : (term320 x z) = (term287 x z).
Proof. exact (TRANS (@lem1574022 x z) (@lem1574023 x z)). Qed.
Lemma lem1574025 (x : real) (z : real) : (term319 x z) = (term287 x z).
Proof. exact (TRANS (@lem1574017 x z) (@lem1574024 x z)). Qed.
Lemma lem1574026 (x : real) (z : real) : (term252 z x) = (term287 x z).
Proof. exact (TRANS (@lem1574016 x z) (@lem1574025 x z)). Qed.
Lemma lem1574027 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1574028 (x : real) (z : real) : (term323 z x) = (term313 x z).
Proof. exact (MK_COMB (@lem1574027) (@lem1574026 x z)). Qed.
Lemma lem1574029 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574030 (x : real) (z : real) : (term316 z x) = (term314 x z).
Proof. exact (MK_COMB (@lem1574028 x z) (@lem1574029)). Qed.
Lemma lem1574031 (x : real) (z : real) : (term315 z x) = (term314 x z).
Proof. exact (TRANS (@lem1573999 z x) (@lem1574030 x z)). Qed.
Lemma lem1574032 (x : real) : (term258 x) = (term259 x).
Proof. exact (@lem1483525 (term260 x) term58). Qed.
Lemma lem1574033 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574045 (x : real) : (term260 x) = (term261 x).
Proof. exact (@lem1483442 term38 x). Qed.
Lemma lem1574047 (m : nat) : (term262 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1574048 : term263 = term58.
Proof. exact (@lem1574047 term46). Qed.
Lemma lem1574049 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1574050 : term264 = term265.
Proof. exact (MK_COMB (@lem1574049) (@lem1574048)). Qed.
Lemma lem1574051 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1574052 (x : real) : (term261 x) = (term266 x).
Proof. exact (MK_COMB (@lem1574050) (@lem1574051 x)). Qed.
Lemma lem1574053 (x : real) : (term260 x) = (term266 x).
Proof. exact (TRANS (@lem1574045 x) (@lem1574052 x)). Qed.
Lemma lem1574054 (x : real) : (term266 x) = term58.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1574056 (x : real) : (term260 x) = term58.
Proof. exact (TRANS (@lem1574053 x) (@lem1574054 x)). Qed.
Lemma lem1574057 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1574058 (x : real) : (term267 x) = term268.
Proof. exact (MK_COMB (@lem1574057) (@lem1574056 x)). Qed.
Lemma lem1574059 (x : real) : (term269 x) = term270.
Proof. exact (MK_COMB (@lem1574058 x) (@lem1574033)). Qed.
Lemma lem1574060 : term270 = term271.
Proof. exact (@lem1483519 term58 term58). Qed.
Lemma lem1574062 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1574063 : term213 = term58.
Proof. exact (@lem1574062 term46). Qed.
Lemma lem1574064 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem1574065 : term271 = term273.
Proof. exact (MK_COMB (@lem1574064) (@lem1574063)). Qed.
Lemma lem1574066 : term273 = term58.
Proof. exact (@lem1483448 term58). Qed.
Lemma lem1574067 : term271 = term58.
Proof. exact (TRANS (@lem1574065) (@lem1574066)). Qed.
Lemma lem1574068 : term270 = term58.
Proof. exact (TRANS (@lem1574060) (@lem1574067)). Qed.
Lemma lem1574069 (x : real) : (term269 x) = term58.
Proof. exact (TRANS (@lem1574059 x) (@lem1574068)). Qed.
Lemma lem1574070 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574071 (x : real) : (term274 x) = term275.
Proof. exact (MK_COMB (@lem1574070) (@lem1574069 x)). Qed.
Lemma lem1574072 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574073 (x : real) : (term259 x) = term276.
Proof. exact (MK_COMB (@lem1574071 x) (@lem1574072)). Qed.
Lemma lem1574074 (x : real) : (term258 x) = term276.
Proof. exact (TRANS (@lem1574032 x) (@lem1574073 x)). Qed.
Lemma lem1574075 (y : real) (x : real) : (term249 y x) = (term250 y x).
Proof. exact (@lem1483525 (term251 y x) term58). Qed.
Lemma lem1574076 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574089 (x : real) (y : real) : (term251 y x) = (term287 x y).
Proof. exact (@lem1483488 (term245 x) y). Qed.
Lemma lem1574090 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1574091 (x : real) (y : real) : (term317 y x) = (term318 x y).
Proof. exact (MK_COMB (@lem1574090) (@lem1574089 x y)). Qed.
Lemma lem1574092 (x : real) (y : real) : (term252 y x) = (term319 x y).
Proof. exact (MK_COMB (@lem1574091 x y) (@lem1574076)). Qed.
Lemma lem1574093 (x : real) (y : real) : (term319 x y) = (term320 x y).
Proof. exact (@lem1483519 (term287 x y) term58). Qed.
Lemma lem1574095 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1574096 : term213 = term58.
Proof. exact (@lem1574095 term46). Qed.
Lemma lem1574097 (x : real) (y : real) : (term321 x y) = (term321 x y).
Proof. exact (eq_refl (term321 x y)). Qed.
Lemma lem1574098 (x : real) (y : real) : (term320 x y) = (term322 x y).
Proof. exact (MK_COMB (@lem1574097 x y) (@lem1574096)). Qed.
Lemma lem1574099 (x : real) (y : real) : (term322 x y) = (term287 x y).
Proof. exact (@lem1483450 (term287 x y)). Qed.
Lemma lem1574100 (x : real) (y : real) : (term320 x y) = (term287 x y).
Proof. exact (TRANS (@lem1574098 x y) (@lem1574099 x y)). Qed.
Lemma lem1574101 (x : real) (y : real) : (term319 x y) = (term287 x y).
Proof. exact (TRANS (@lem1574093 x y) (@lem1574100 x y)). Qed.
Lemma lem1574102 (x : real) (y : real) : (term252 y x) = (term287 x y).
Proof. exact (TRANS (@lem1574092 x y) (@lem1574101 x y)). Qed.
Lemma lem1574103 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574104 (x : real) (y : real) : (term256 y x) = (term288 x y).
Proof. exact (MK_COMB (@lem1574103) (@lem1574102 x y)). Qed.
Lemma lem1574105 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574106 (x : real) (y : real) : (term250 y x) = (term289 x y).
Proof. exact (MK_COMB (@lem1574104 x y) (@lem1574105)). Qed.
Lemma lem1574107 (x : real) (y : real) : (term249 y x) = (term289 x y).
Proof. exact (TRANS (@lem1574075 y x) (@lem1574106 x y)). Qed.
Lemma lem1574108 (z : real) (x : real) : (term249 z x) = (term250 z x).
Proof. exact (@lem1483525 (term251 z x) term58). Qed.
Lemma lem1574109 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574122 (x : real) (z : real) : (term251 z x) = (term287 x z).
Proof. exact (@lem1483488 (term245 x) z). Qed.
Lemma lem1574123 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1574124 (x : real) (z : real) : (term317 z x) = (term318 x z).
Proof. exact (MK_COMB (@lem1574123) (@lem1574122 x z)). Qed.
Lemma lem1574125 (x : real) (z : real) : (term252 z x) = (term319 x z).
Proof. exact (MK_COMB (@lem1574124 x z) (@lem1574109)). Qed.
Lemma lem1574126 (x : real) (z : real) : (term319 x z) = (term320 x z).
Proof. exact (@lem1483519 (term287 x z) term58). Qed.
Lemma lem1574128 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1574129 : term213 = term58.
Proof. exact (@lem1574128 term46). Qed.
Lemma lem1574130 (x : real) (z : real) : (term321 x z) = (term321 x z).
Proof. exact (eq_refl (term321 x z)). Qed.
Lemma lem1574131 (x : real) (z : real) : (term320 x z) = (term322 x z).
Proof. exact (MK_COMB (@lem1574130 x z) (@lem1574129)). Qed.
Lemma lem1574132 (x : real) (z : real) : (term322 x z) = (term287 x z).
Proof. exact (@lem1483450 (term287 x z)). Qed.
Lemma lem1574133 (x : real) (z : real) : (term320 x z) = (term287 x z).
Proof. exact (TRANS (@lem1574131 x z) (@lem1574132 x z)). Qed.
Lemma lem1574134 (x : real) (z : real) : (term319 x z) = (term287 x z).
Proof. exact (TRANS (@lem1574126 x z) (@lem1574133 x z)). Qed.
Lemma lem1574135 (x : real) (z : real) : (term252 z x) = (term287 x z).
Proof. exact (TRANS (@lem1574125 x z) (@lem1574134 x z)). Qed.
Lemma lem1574136 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574137 (x : real) (z : real) : (term256 z x) = (term288 x z).
Proof. exact (MK_COMB (@lem1574136) (@lem1574135 x z)). Qed.
Lemma lem1574138 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574139 (x : real) (z : real) : (term250 z x) = (term289 x z).
Proof. exact (MK_COMB (@lem1574137 x z) (@lem1574138)). Qed.
Lemma lem1574140 (x : real) (z : real) : (term249 z x) = (term289 x z).
Proof. exact (TRANS (@lem1574108 z x) (@lem1574139 x z)). Qed.
Lemma lem1574141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574142 (x : real) (y : real) : (term277 y x) = (term290 x y).
Proof. exact (MK_COMB (@lem1574141) (@lem1574107 x y)). Qed.
Lemma lem1574143 (y : real) (x : real) (z : real) : (term291 y z x) = (term286 y x z).
Proof. exact (MK_COMB (@lem1574142 x y) (@lem1574140 x z)). Qed.
Lemma lem1574144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574145 (x : real) : (term324 x) = term325.
Proof. exact (MK_COMB (@lem1574144) (@lem1574074 x)). Qed.
Lemma lem1574146 (y : real) (x : real) (z : real) : (term326 y z x) = (term327 y x z).
Proof. exact (MK_COMB (@lem1574145 x) (@lem1574143 y x z)). Qed.
Lemma lem1574147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574148 (x : real) (z : real) : (term328 z x) = (term329 x z).
Proof. exact (MK_COMB (@lem1574147) (@lem1574031 x z)). Qed.
Lemma lem1574149 (y : real) (x : real) (z : real) : (term303 y z x) = (term330 y x z).
Proof. exact (MK_COMB (@lem1574148 x z) (@lem1574146 y x z)). Qed.
Lemma lem1574150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574151 (x : real) (y : real) : (term304 y x) = (term329 x y).
Proof. exact (MK_COMB (@lem1574150) (@lem1573998 x y)). Qed.
Lemma lem1574152 (y : real) (x : real) (z : real) : (term306 y z x) = (term331 y x z).
Proof. exact (MK_COMB (@lem1574151 x y) (@lem1574149 y x z)). Qed.
Lemma lem1574153 (x : real) (y : real) : (real_gt x y) = (term332 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1574166 (x : real) (y : real) : (real_sub x y) = (term251 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1574167 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574168 (x : real) (y : real) : (term333 x y) = (term257 x y).
Proof. exact (MK_COMB (@lem1574167) (@lem1574166 x y)). Qed.
Lemma lem1574169 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574170 (x : real) (y : real) : (term332 x y) = (term249 x y).
Proof. exact (MK_COMB (@lem1574168 x y) (@lem1574169)). Qed.
Lemma lem1574171 (x : real) (y : real) : (real_gt x y) = (term249 x y).
Proof. exact (TRANS (@lem1574153 x y) (@lem1574170 x y)). Qed.
Lemma lem1574172 (z : real) (y : real) : (term315 z y) = (term316 z y).
Proof. exact (@lem1483527 (term251 z y) term58). Qed.
Lemma lem1574173 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574186 (y : real) (z : real) : (term251 z y) = (term287 y z).
Proof. exact (@lem1483488 (term245 y) z). Qed.
Lemma lem1574187 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1574188 (y : real) (z : real) : (term317 z y) = (term318 y z).
Proof. exact (MK_COMB (@lem1574187) (@lem1574186 y z)). Qed.
Lemma lem1574189 (y : real) (z : real) : (term252 z y) = (term319 y z).
Proof. exact (MK_COMB (@lem1574188 y z) (@lem1574173)). Qed.
Lemma lem1574190 (y : real) (z : real) : (term319 y z) = (term320 y z).
Proof. exact (@lem1483519 (term287 y z) term58). Qed.
Lemma lem1574192 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1574193 : term213 = term58.
Proof. exact (@lem1574192 term46). Qed.
Lemma lem1574194 (y : real) (z : real) : (term321 y z) = (term321 y z).
Proof. exact (eq_refl (term321 y z)). Qed.
Lemma lem1574195 (y : real) (z : real) : (term320 y z) = (term322 y z).
Proof. exact (MK_COMB (@lem1574194 y z) (@lem1574193)). Qed.
Lemma lem1574196 (y : real) (z : real) : (term322 y z) = (term287 y z).
Proof. exact (@lem1483450 (term287 y z)). Qed.
Lemma lem1574197 (y : real) (z : real) : (term320 y z) = (term287 y z).
Proof. exact (TRANS (@lem1574195 y z) (@lem1574196 y z)). Qed.
Lemma lem1574198 (y : real) (z : real) : (term319 y z) = (term287 y z).
Proof. exact (TRANS (@lem1574190 y z) (@lem1574197 y z)). Qed.
Lemma lem1574199 (y : real) (z : real) : (term252 z y) = (term287 y z).
Proof. exact (TRANS (@lem1574189 y z) (@lem1574198 y z)). Qed.
Lemma lem1574200 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1574201 (y : real) (z : real) : (term323 z y) = (term313 y z).
Proof. exact (MK_COMB (@lem1574200) (@lem1574199 y z)). Qed.
Lemma lem1574202 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574203 (y : real) (z : real) : (term316 z y) = (term314 y z).
Proof. exact (MK_COMB (@lem1574201 y z) (@lem1574202)). Qed.
Lemma lem1574204 (y : real) (z : real) : (term315 z y) = (term314 y z).
Proof. exact (TRANS (@lem1574172 z y) (@lem1574203 y z)). Qed.
Lemma lem1574205 (x : real) (y : real) : (term249 x y) = (term250 x y).
Proof. exact (@lem1483525 (term251 x y) term58). Qed.
Lemma lem1574223 (x : real) (y : real) : (term252 x y) = (term253 x y).
Proof. exact (@lem1483519 (term251 x y) term58). Qed.
Lemma lem1574225 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1574226 : term213 = term58.
Proof. exact (@lem1574225 term46). Qed.
Lemma lem1574227 (x : real) (y : real) : (term254 x y) = (term254 x y).
Proof. exact (eq_refl (term254 x y)). Qed.
Lemma lem1574228 (x : real) (y : real) : (term253 x y) = (term255 x y).
Proof. exact (MK_COMB (@lem1574227 x y) (@lem1574226)). Qed.
Lemma lem1574229 (x : real) (y : real) : (term255 x y) = (term251 x y).
Proof. exact (@lem1483450 (term251 x y)). Qed.
Lemma lem1574230 (x : real) (y : real) : (term253 x y) = (term251 x y).
Proof. exact (TRANS (@lem1574228 x y) (@lem1574229 x y)). Qed.
Lemma lem1574232 (x : real) (y : real) : (term252 x y) = (term251 x y).
Proof. exact (TRANS (@lem1574223 x y) (@lem1574230 x y)). Qed.
Lemma lem1574233 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574234 (x : real) (y : real) : (term256 x y) = (term257 x y).
Proof. exact (MK_COMB (@lem1574233) (@lem1574232 x y)). Qed.
Lemma lem1574235 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574236 (x : real) (y : real) : (term250 x y) = (term249 x y).
Proof. exact (MK_COMB (@lem1574234 x y) (@lem1574235)). Qed.
Lemma lem1574237 (x : real) (y : real) : (term249 x y) = (term249 x y).
Proof. exact (TRANS (@lem1574205 x y) (@lem1574236 x y)). Qed.
Lemma lem1574238 (y : real) : (term258 y) = (term259 y).
Proof. exact (@lem1483525 (term260 y) term58). Qed.
Lemma lem1574239 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574251 (y : real) : (term260 y) = (term261 y).
Proof. exact (@lem1483442 term38 y). Qed.
Lemma lem1574253 (m : nat) : (term262 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1574254 : term263 = term58.
Proof. exact (@lem1574253 term46). Qed.
Lemma lem1574255 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1574256 : term264 = term265.
Proof. exact (MK_COMB (@lem1574255) (@lem1574254)). Qed.
Lemma lem1574257 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1574258 (y : real) : (term261 y) = (term266 y).
Proof. exact (MK_COMB (@lem1574256) (@lem1574257 y)). Qed.
Lemma lem1574259 (y : real) : (term260 y) = (term266 y).
Proof. exact (TRANS (@lem1574251 y) (@lem1574258 y)). Qed.
Lemma lem1574260 (y : real) : (term266 y) = term58.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1574262 (y : real) : (term260 y) = term58.
Proof. exact (TRANS (@lem1574259 y) (@lem1574260 y)). Qed.
Lemma lem1574263 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1574264 (y : real) : (term267 y) = term268.
Proof. exact (MK_COMB (@lem1574263) (@lem1574262 y)). Qed.
Lemma lem1574265 (y : real) : (term269 y) = term270.
Proof. exact (MK_COMB (@lem1574264 y) (@lem1574239)). Qed.
Lemma lem1574266 : term270 = term271.
Proof. exact (@lem1483519 term58 term58). Qed.
Lemma lem1574268 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1574269 : term213 = term58.
Proof. exact (@lem1574268 term46). Qed.
Lemma lem1574270 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem1574271 : term271 = term273.
Proof. exact (MK_COMB (@lem1574270) (@lem1574269)). Qed.
Lemma lem1574272 : term273 = term58.
Proof. exact (@lem1483448 term58). Qed.
Lemma lem1574273 : term271 = term58.
Proof. exact (TRANS (@lem1574271) (@lem1574272)). Qed.
Lemma lem1574274 : term270 = term58.
Proof. exact (TRANS (@lem1574266) (@lem1574273)). Qed.
Lemma lem1574275 (y : real) : (term269 y) = term58.
Proof. exact (TRANS (@lem1574265 y) (@lem1574274)). Qed.
Lemma lem1574276 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574277 (y : real) : (term274 y) = term275.
Proof. exact (MK_COMB (@lem1574276) (@lem1574275 y)). Qed.
Lemma lem1574278 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574279 (y : real) : (term259 y) = term276.
Proof. exact (MK_COMB (@lem1574277 y) (@lem1574278)). Qed.
Lemma lem1574280 (y : real) : (term258 y) = term276.
Proof. exact (TRANS (@lem1574238 y) (@lem1574279 y)). Qed.
Lemma lem1574281 (z : real) (y : real) : (term249 z y) = (term250 z y).
Proof. exact (@lem1483525 (term251 z y) term58). Qed.
Lemma lem1574282 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574295 (y : real) (z : real) : (term251 z y) = (term287 y z).
Proof. exact (@lem1483488 (term245 y) z). Qed.
Lemma lem1574296 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1574297 (y : real) (z : real) : (term317 z y) = (term318 y z).
Proof. exact (MK_COMB (@lem1574296) (@lem1574295 y z)). Qed.
Lemma lem1574298 (y : real) (z : real) : (term252 z y) = (term319 y z).
Proof. exact (MK_COMB (@lem1574297 y z) (@lem1574282)). Qed.
Lemma lem1574299 (y : real) (z : real) : (term319 y z) = (term320 y z).
Proof. exact (@lem1483519 (term287 y z) term58). Qed.
Lemma lem1574301 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1574302 : term213 = term58.
Proof. exact (@lem1574301 term46). Qed.
Lemma lem1574303 (y : real) (z : real) : (term321 y z) = (term321 y z).
Proof. exact (eq_refl (term321 y z)). Qed.
Lemma lem1574304 (y : real) (z : real) : (term320 y z) = (term322 y z).
Proof. exact (MK_COMB (@lem1574303 y z) (@lem1574302)). Qed.
Lemma lem1574305 (y : real) (z : real) : (term322 y z) = (term287 y z).
Proof. exact (@lem1483450 (term287 y z)). Qed.
Lemma lem1574306 (y : real) (z : real) : (term320 y z) = (term287 y z).
Proof. exact (TRANS (@lem1574304 y z) (@lem1574305 y z)). Qed.
Lemma lem1574307 (y : real) (z : real) : (term319 y z) = (term287 y z).
Proof. exact (TRANS (@lem1574299 y z) (@lem1574306 y z)). Qed.
Lemma lem1574308 (y : real) (z : real) : (term252 z y) = (term287 y z).
Proof. exact (TRANS (@lem1574298 y z) (@lem1574307 y z)). Qed.
Lemma lem1574309 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574310 (y : real) (z : real) : (term256 z y) = (term288 y z).
Proof. exact (MK_COMB (@lem1574309) (@lem1574308 y z)). Qed.
Lemma lem1574311 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574312 (y : real) (z : real) : (term250 z y) = (term289 y z).
Proof. exact (MK_COMB (@lem1574310 y z) (@lem1574311)). Qed.
Lemma lem1574313 (y : real) (z : real) : (term249 z y) = (term289 y z).
Proof. exact (TRANS (@lem1574281 z y) (@lem1574312 y z)). Qed.
Lemma lem1574314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574315 (y : real) : (term324 y) = term325.
Proof. exact (MK_COMB (@lem1574314) (@lem1574280 y)). Qed.
Lemma lem1574316 (y : real) (z : real) : (term334 z y) = (term335 y z).
Proof. exact (MK_COMB (@lem1574315 y) (@lem1574313 y z)). Qed.
Lemma lem1574317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574318 (x : real) (y : real) : (term277 x y) = (term277 x y).
Proof. exact (MK_COMB (@lem1574317) (@lem1574237 x y)). Qed.
Lemma lem1574319 (x : real) (y : real) (z : real) : (term336 x z y) = (term337 x y z).
Proof. exact (MK_COMB (@lem1574318 x y) (@lem1574316 y z)). Qed.
Lemma lem1574320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574321 (y : real) (z : real) : (term328 z y) = (term329 y z).
Proof. exact (MK_COMB (@lem1574320) (@lem1574204 y z)). Qed.
Lemma lem1574322 (x : real) (y : real) (z : real) : (term298 x z y) = (term338 x y z).
Proof. exact (MK_COMB (@lem1574321 y z) (@lem1574319 x y z)). Qed.
Lemma lem1574323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574324 (x : real) (y : real) : (term299 x y) = (term277 x y).
Proof. exact (MK_COMB (@lem1574323) (@lem1574171 x y)). Qed.
Lemma lem1574325 (x : real) (y : real) (z : real) : (term301 x z y) = (term339 x y z).
Proof. exact (MK_COMB (@lem1574324 x y) (@lem1574322 x y z)). Qed.
Lemma lem1574326 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1574327 (y : real) (x : real) (z : real) : (term308 y z x) = (term340 y x z).
Proof. exact (MK_COMB (@lem1574326) (@lem1574152 y x z)). Qed.
Lemma lem1574328 (x : real) (y : real) (z : real) : (term309 x z y) = (term341 x y z).
Proof. exact (MK_COMB (@lem1574327 y x z) (@lem1574325 x y z)). Qed.
Lemma lem1574340 (x : real) (y : real) (z : real) : (term239 z x y) = (term341 x y z).
Proof. exact (TRANS (@lem1573979 x z y) (@lem1574328 x y z)). Qed.
Lemma lem1574341 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1574342 (x : real) (y : real) (z : real) : (term283 z x y) = (term342 x y z).
Proof. exact (MK_COMB (@lem1574341) (@lem1574340 x y z)). Qed.
Lemma lem1574343 (x : real) (y : real) (z : real) : (term284 x y z) = (term343 x y z).
Proof. exact (MK_COMB (@lem1574342 x y z) (@lem1573962 x y z)). Qed.
Lemma lem1574344 (x : real) (y : real) (z : real) : (term182 x y z) = (term343 x y z).
Proof. exact (TRANS (@lem1573915 x y z) (@lem1574343 x y z)). Qed.
Lemma lem1574345 (x : real) (y : real) (z : real) : (term64 x y z) = (term343 x y z).
Proof. exact (TRANS (@lem1573631 x y z) (@lem1574344 x y z)). Qed.
Lemma lem1574347 (x : real) (a : real) (y : real) (r : real) : (term285 a x y r) = (term149 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1574348 (x : real) (y : real) (z : real) : (term60 x y z) = (term344 x y z).
Proof. exact (@lem1574347 (real_min x y) (term345 x y z) z term58). Qed.
Lemma lem1574361 (x : real) (y : real) (z : real) : (term346 x y z) = (term347 x y z).
Proof. exact (@lem1483488 z (term345 x y z)). Qed.
Lemma lem1574362 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574363 (x : real) (y : real) (z : real) : (term348 x y z) = (term349 x y z).
Proof. exact (MK_COMB (@lem1574362) (@lem1574361 x y z)). Qed.
Lemma lem1574364 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574365 (x : real) (y : real) (z : real) : (term350 x y z) = (term351 x y z).
Proof. exact (MK_COMB (@lem1574363 x y z) (@lem1574364)). Qed.
Lemma lem1574378 (x : real) (y : real) (z : real) : (term352 z x y) = (term353 x y z).
Proof. exact (@lem1483488 (real_min x y) (term345 x y z)). Qed.
Lemma lem1574379 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574380 (x : real) (y : real) (z : real) : (term354 z x y) = (term355 x y z).
Proof. exact (MK_COMB (@lem1574379) (@lem1574378 x y z)). Qed.
Lemma lem1574381 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574382 (x : real) (y : real) (z : real) : (term356 z x y) = (term357 x y z).
Proof. exact (MK_COMB (@lem1574380 x y z) (@lem1574381)). Qed.
Lemma lem1574383 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574384 (x : real) (y : real) (z : real) : (term358 z x y) = (term359 x y z).
Proof. exact (MK_COMB (@lem1574383) (@lem1574382 x y z)). Qed.
Lemma lem1574385 (x : real) (y : real) (z : real) : (term344 x y z) = (term360 x y z).
Proof. exact (MK_COMB (@lem1574384 x y z) (@lem1574365 x y z)). Qed.
Lemma lem1574386 (x : real) (y : real) (z : real) : (term60 x y z) = (term360 x y z).
Proof. exact (TRANS (@lem1574348 x y z) (@lem1574385 x y z)). Qed.
Lemma lem1574388 (x : real) (a : real) (y : real) (r : real) : (term148 x y a r) = (term149 x a y r).
Proof. exact (proj1 (@lem1482715 x a (@el real) y (@el real) r)). Qed.
Lemma lem1574389 (x : real) (z : real) (y : real) : (term357 x y z) = (term361 x z y).
Proof. exact (@lem1574388 x (term345 x y z) y term58). Qed.
Lemma lem1574402 (x : real) (y : real) (z : real) : (term362 x z y) = (term363 x y z).
Proof. exact (@lem1483488 y (term345 x y z)). Qed.
Lemma lem1574403 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574404 (x : real) (y : real) (z : real) : (term364 x z y) = (term365 x y z).
Proof. exact (MK_COMB (@lem1574403) (@lem1574402 x y z)). Qed.
Lemma lem1574405 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574406 (x : real) (y : real) (z : real) : (term366 x z y) = (term367 x y z).
Proof. exact (MK_COMB (@lem1574404 x y z) (@lem1574405)). Qed.
Lemma lem1574419 (x : real) (y : real) (z : real) : (term368 y z x) = (term369 x y z).
Proof. exact (@lem1483488 x (term345 x y z)). Qed.
Lemma lem1574420 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574421 (x : real) (y : real) (z : real) : (term370 y z x) = (term371 x y z).
Proof. exact (MK_COMB (@lem1574420) (@lem1574419 x y z)). Qed.
Lemma lem1574422 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574423 (x : real) (y : real) (z : real) : (term372 y z x) = (term373 x y z).
Proof. exact (MK_COMB (@lem1574421 x y z) (@lem1574422)). Qed.
Lemma lem1574424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574425 (x : real) (y : real) (z : real) : (term374 y z x) = (term375 x y z).
Proof. exact (MK_COMB (@lem1574424) (@lem1574423 x y z)). Qed.
Lemma lem1574426 (x : real) (y : real) (z : real) : (term361 x z y) = (term376 x y z).
Proof. exact (MK_COMB (@lem1574425 x y z) (@lem1574406 x y z)). Qed.
Lemma lem1574427 (x : real) (y : real) (z : real) : (term357 x y z) = (term376 x y z).
Proof. exact (TRANS (@lem1574389 x z y) (@lem1574426 x y z)). Qed.
Lemma lem1574428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574429 (x : real) (y : real) (z : real) : (term359 x y z) = (term377 x y z).
Proof. exact (MK_COMB (@lem1574428) (@lem1574427 x y z)). Qed.
Lemma lem1574430 (x : real) (y : real) (z : real) : (term351 x y z) = (term351 x y z).
Proof. exact (eq_refl (term351 x y z)). Qed.
Lemma lem1574431 (x : real) (y : real) (z : real) : (term360 x y z) = (term378 x y z).
Proof. exact (MK_COMB (@lem1574429 x y z) (@lem1574430 x y z)). Qed.
Lemma lem1574432 (x : real) (y : real) (z : real) : (term60 x y z) = (term378 x y z).
Proof. exact (TRANS (@lem1574386 x y z) (@lem1574431 x y z)). Qed.
Lemma lem1574433 (x : real) (y : real) (z : real) : (term379 x y z) = (term378 x y z).
Proof. exact (eq_refl (term379 x y z)). Qed.
Lemma lem1574434 (x : real) (y : real) (z : real) : (term378 x y z) = (term379 x y z).
Proof. exact (SYM (@lem1574433 x y z)). Qed.
Lemma lem1574435 (x : real) (y : real) (z : real) : (term379 x y z) = (term380 x y z).
Proof. exact (@lem1483429 x (term381 x y z) (real_min y z)). Qed.
Lemma lem1574436 (x : real) (y : real) (z : real) : (term378 x y z) = (term380 x y z).
Proof. exact (TRANS (@lem1574434 x y z) (@lem1574435 x y z)). Qed.
Lemma lem1574437 (x : real) (y : real) (z : real) : (term382 x y z) = (term383 x y z).
Proof. exact (eq_refl (term382 x y z)). Qed.
Lemma lem1574438 (x : real) (y : real) (z : real) : (term384 x y z) = (term384 x y z).
Proof. exact (eq_refl (term384 x y z)). Qed.
Lemma lem1574439 (x : real) (y : real) (z : real) : (term385 x y z) = (term386 x y z).
Proof. exact (MK_COMB (@lem1574438 x y z) (@lem1574437 x y z)). Qed.
Lemma lem1574440 (y : real) (z : real) (x : real) : (term387 y z x) = (term388 y z x).
Proof. exact (eq_refl (term387 y z x)). Qed.
Lemma lem1574441 (y : real) (z : real) (x : real) : (term389 y z x) = (term389 y z x).
Proof. exact (eq_refl (term389 y z x)). Qed.
Lemma lem1574442 (y : real) (z : real) (x : real) : (term390 y z x) = (term391 y z x).
Proof. exact (MK_COMB (@lem1574441 y z x) (@lem1574440 y z x)). Qed.
Lemma lem1574443 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1574444 (y : real) (z : real) (x : real) : (term392 y z x) = (term393 y z x).
Proof. exact (MK_COMB (@lem1574443) (@lem1574442 y z x)). Qed.
Lemma lem1574445 (x : real) (y : real) (z : real) : (term380 x y z) = (term394 x y z).
Proof. exact (MK_COMB (@lem1574444 y z x) (@lem1574439 x y z)). Qed.
Lemma lem1574446 (x : real) (y : real) (z : real) : (term395 x y z) = (term395 x y z).
Proof. exact (eq_refl (term395 x y z)). Qed.
Lemma lem1574447 (x : real) (y : real) (z : real) : ((term378 x y z) = (term380 x y z)) = ((term378 x y z) = (term394 x y z)).
Proof. exact (MK_COMB (@lem1574446 x y z) (@lem1574445 x y z)). Qed.
Lemma lem1574448 (x : real) (y : real) (z : real) : (term378 x y z) = (term394 x y z).
Proof. exact (EQ_MP (@lem1574447 x y z) (@lem1574436 x y z)). Qed.
Lemma lem1574449 (y : real) (z : real) (x : real) : (term396 y z x) = (term397 y z x).
Proof. exact (@lem1483527 (real_min y z) x). Qed.
Lemma lem1574455 (y : real) (z : real) (x : real) : (term242 y z x) = (term243 y z x).
Proof. exact (@lem1483519 (real_min y z) x). Qed.
Lemma lem1574460 (x : real) (y : real) (z : real) : (term243 y z x) = (term244 x y z).
Proof. exact (@lem1483488 (term245 x) (real_min y z)). Qed.
Lemma lem1574462 (x : real) (y : real) (z : real) : (term242 y z x) = (term244 x y z).
Proof. exact (TRANS (@lem1574455 y z x) (@lem1574460 x y z)). Qed.
Lemma lem1574463 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1574464 (x : real) (y : real) (z : real) : (term398 y z x) = (term399 x y z).
Proof. exact (MK_COMB (@lem1574463) (@lem1574462 x y z)). Qed.
Lemma lem1574465 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574466 (x : real) (y : real) (z : real) : (term397 y z x) = (term400 x y z).
Proof. exact (MK_COMB (@lem1574464 x y z) (@lem1574465)). Qed.
Lemma lem1574467 (x : real) (y : real) (z : real) : (term396 y z x) = (term400 x y z).
Proof. exact (TRANS (@lem1574449 y z x) (@lem1574466 x y z)). Qed.
Lemma lem1574468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574469 (x : real) : (term324 x) = term325.
Proof. exact (MK_COMB (@lem1574468) (@lem1574074 x)). Qed.
Lemma lem1574470 (x : real) (y : real) : (term334 y x) = (term335 x y).
Proof. exact (MK_COMB (@lem1574469 x) (@lem1574107 x y)). Qed.
Lemma lem1574471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574472 (x : real) (y : real) : (term401 y x) = (term402 x y).
Proof. exact (MK_COMB (@lem1574471) (@lem1574470 x y)). Qed.
Lemma lem1574473 (y : real) (x : real) (z : real) : (term388 y z x) = (term403 y x z).
Proof. exact (MK_COMB (@lem1574472 x y) (@lem1574140 x z)). Qed.
Lemma lem1574474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574475 (x : real) (y : real) (z : real) : (term389 y z x) = (term404 x y z).
Proof. exact (MK_COMB (@lem1574474) (@lem1574467 x y z)). Qed.
Lemma lem1574476 (y : real) (x : real) (z : real) : (term391 y z x) = (term405 y x z).
Proof. exact (MK_COMB (@lem1574475 x y z) (@lem1574473 y x z)). Qed.
Lemma lem1574477 (x : real) (y : real) (z : real) : (term406 x y z) = (term407 x y z).
Proof. exact (@lem1483525 x (real_min y z)). Qed.
Lemma lem1574490 (x : real) (y : real) (z : real) : (term202 x y z) = (term203 x y z).
Proof. exact (@lem1483519 x (real_min y z)). Qed.
Lemma lem1574491 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574492 (x : real) (y : real) (z : real) : (term408 x y z) = (term234 x y z).
Proof. exact (MK_COMB (@lem1574491) (@lem1574490 x y z)). Qed.
Lemma lem1574493 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574494 (x : real) (y : real) (z : real) : (term407 x y z) = (term227 x y z).
Proof. exact (MK_COMB (@lem1574492 x y z) (@lem1574493)). Qed.
Lemma lem1574495 (x : real) (y : real) (z : real) : (term406 x y z) = (term227 x y z).
Proof. exact (TRANS (@lem1574477 x y z) (@lem1574494 x y z)). Qed.
Lemma lem1574496 (x : real) (y : real) (z : real) : (term227 x y z) = (term228 x y z).
Proof. exact (@lem1483525 (term203 x y z) term58). Qed.
Lemma lem1574514 (x : real) (y : real) (z : real) : (term229 x y z) = (term230 x y z).
Proof. exact (@lem1483519 (term203 x y z) term58). Qed.
Lemma lem1574516 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1574517 : term213 = term58.
Proof. exact (@lem1574516 term46). Qed.
Lemma lem1574518 (x : real) (y : real) (z : real) : (term231 x y z) = (term231 x y z).
Proof. exact (eq_refl (term231 x y z)). Qed.
Lemma lem1574519 (x : real) (y : real) (z : real) : (term230 x y z) = (term232 x y z).
Proof. exact (MK_COMB (@lem1574518 x y z) (@lem1574517)). Qed.
Lemma lem1574520 (x : real) (y : real) (z : real) : (term232 x y z) = (term203 x y z).
Proof. exact (@lem1483450 (term203 x y z)). Qed.
Lemma lem1574521 (x : real) (y : real) (z : real) : (term230 x y z) = (term203 x y z).
Proof. exact (TRANS (@lem1574519 x y z) (@lem1574520 x y z)). Qed.
Lemma lem1574523 (x : real) (y : real) (z : real) : (term229 x y z) = (term203 x y z).
Proof. exact (TRANS (@lem1574514 x y z) (@lem1574521 x y z)). Qed.
Lemma lem1574524 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574525 (x : real) (y : real) (z : real) : (term233 x y z) = (term234 x y z).
Proof. exact (MK_COMB (@lem1574524) (@lem1574523 x y z)). Qed.
Lemma lem1574526 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574527 (x : real) (y : real) (z : real) : (term228 x y z) = (term227 x y z).
Proof. exact (MK_COMB (@lem1574525 x y z) (@lem1574526)). Qed.
Lemma lem1574528 (x : real) (y : real) (z : real) : (term227 x y z) = (term227 x y z).
Proof. exact (TRANS (@lem1574496 x y z) (@lem1574527 x y z)). Qed.
Lemma lem1574529 (y : real) (z : real) : (term207 y z) = (term208 y z).
Proof. exact (@lem1483525 (term209 y z) term58). Qed.
Lemma lem1574547 (y : real) (z : real) : (term210 y z) = (term211 y z).
Proof. exact (@lem1483519 (term209 y z) term58). Qed.
Lemma lem1574549 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1574550 : term213 = term58.
Proof. exact (@lem1574549 term46). Qed.
Lemma lem1574551 (y : real) (z : real) : (term214 y z) = (term214 y z).
Proof. exact (eq_refl (term214 y z)). Qed.
Lemma lem1574552 (y : real) (z : real) : (term211 y z) = (term215 y z).
Proof. exact (MK_COMB (@lem1574551 y z) (@lem1574550)). Qed.
Lemma lem1574553 (y : real) (z : real) : (term215 y z) = (term209 y z).
Proof. exact (@lem1483450 (term209 y z)). Qed.
Lemma lem1574554 (y : real) (z : real) : (term211 y z) = (term209 y z).
Proof. exact (TRANS (@lem1574552 y z) (@lem1574553 y z)). Qed.
Lemma lem1574556 (y : real) (z : real) : (term210 y z) = (term209 y z).
Proof. exact (TRANS (@lem1574547 y z) (@lem1574554 y z)). Qed.
Lemma lem1574557 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574558 (y : real) (z : real) : (term216 y z) = (term217 y z).
Proof. exact (MK_COMB (@lem1574557) (@lem1574556 y z)). Qed.
Lemma lem1574559 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574560 (y : real) (z : real) : (term208 y z) = (term207 y z).
Proof. exact (MK_COMB (@lem1574558 y z) (@lem1574559)). Qed.
Lemma lem1574561 (y : real) (z : real) : (term207 y z) = (term207 y z).
Proof. exact (TRANS (@lem1574529 y z) (@lem1574560 y z)). Qed.
Lemma lem1574562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574563 (x : real) (y : real) (z : real) : (term409 x y z) = (term409 x y z).
Proof. exact (MK_COMB (@lem1574562) (@lem1574528 x y z)). Qed.
Lemma lem1574564 (x : real) (y : real) (z : real) : (term410 x y z) = (term410 x y z).
Proof. exact (MK_COMB (@lem1574563 x y z) (@lem1574561 y z)). Qed.
Lemma lem1574565 (y : real) (z : real) : (term218 y z) = (term219 y z).
Proof. exact (@lem1483525 (term220 y z) term58). Qed.
Lemma lem1574583 (y : real) (z : real) : (term221 y z) = (term222 y z).
Proof. exact (@lem1483519 (term220 y z) term58). Qed.
Lemma lem1574585 (x : nat) : (term212 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1574586 : term213 = term58.
Proof. exact (@lem1574585 term46). Qed.
Lemma lem1574587 (y : real) (z : real) : (term223 y z) = (term223 y z).
Proof. exact (eq_refl (term223 y z)). Qed.
Lemma lem1574588 (y : real) (z : real) : (term222 y z) = (term224 y z).
Proof. exact (MK_COMB (@lem1574587 y z) (@lem1574586)). Qed.
Lemma lem1574589 (y : real) (z : real) : (term224 y z) = (term220 y z).
Proof. exact (@lem1483450 (term220 y z)). Qed.
Lemma lem1574590 (y : real) (z : real) : (term222 y z) = (term220 y z).
Proof. exact (TRANS (@lem1574588 y z) (@lem1574589 y z)). Qed.
Lemma lem1574592 (y : real) (z : real) : (term221 y z) = (term220 y z).
Proof. exact (TRANS (@lem1574583 y z) (@lem1574590 y z)). Qed.
Lemma lem1574593 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574594 (y : real) (z : real) : (term225 y z) = (term226 y z).
Proof. exact (MK_COMB (@lem1574593) (@lem1574592 y z)). Qed.
Lemma lem1574595 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574596 (y : real) (z : real) : (term219 y z) = (term218 y z).
Proof. exact (MK_COMB (@lem1574594 y z) (@lem1574595)). Qed.
Lemma lem1574597 (y : real) (z : real) : (term218 y z) = (term218 y z).
Proof. exact (TRANS (@lem1574565 y z) (@lem1574596 y z)). Qed.
Lemma lem1574598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574599 (x : real) (y : real) (z : real) : (term411 x y z) = (term411 x y z).
Proof. exact (MK_COMB (@lem1574598) (@lem1574564 x y z)). Qed.
Lemma lem1574600 (x : real) (y : real) (z : real) : (term383 x y z) = (term383 x y z).
Proof. exact (MK_COMB (@lem1574599 x y z) (@lem1574597 y z)). Qed.
Lemma lem1574601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574602 (x : real) (y : real) (z : real) : (term384 x y z) = (term409 x y z).
Proof. exact (MK_COMB (@lem1574601) (@lem1574495 x y z)). Qed.
Lemma lem1574603 (x : real) (y : real) (z : real) : (term386 x y z) = (term412 x y z).
Proof. exact (MK_COMB (@lem1574602 x y z) (@lem1574600 x y z)). Qed.
Lemma lem1574604 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1574605 (y : real) (x : real) (z : real) : (term393 y z x) = (term413 y x z).
Proof. exact (MK_COMB (@lem1574604) (@lem1574476 y x z)). Qed.
Lemma lem1574606 (x : real) (y : real) (z : real) : (term394 x y z) = (term414 x y z).
Proof. exact (MK_COMB (@lem1574605 y x z) (@lem1574603 x y z)). Qed.
Lemma lem1574607 (x : real) (y : real) (z : real) : (term378 x y z) = (term414 x y z).
Proof. exact (TRANS (@lem1574448 x y z) (@lem1574606 x y z)). Qed.
Lemma lem1574609 (x : real) (y : real) (z : real) : (term415 x y z) = (term412 x y z).
Proof. exact (eq_refl (term415 x y z)). Qed.
Lemma lem1574610 (x : real) (y : real) (z : real) : (term412 x y z) = (term415 x y z).
Proof. exact (SYM (@lem1574609 x y z)). Qed.
Lemma lem1574611 (x : real) (y : real) (z : real) : (term415 x y z) = (term416 x y z).
Proof. exact (@lem1483429 y (term417 x y z) z). Qed.
Lemma lem1574612 (x : real) (y : real) (z : real) : (term412 x y z) = (term416 x y z).
Proof. exact (TRANS (@lem1574610 x y z) (@lem1574611 x y z)). Qed.
Lemma lem1574613 (x : real) (y : real) (z : real) : (term418 x y z) = (term419 x y z).
Proof. exact (eq_refl (term418 x y z)). Qed.
Lemma lem1574614 (y : real) (z : real) : (term299 y z) = (term299 y z).
Proof. exact (eq_refl (term299 y z)). Qed.
Lemma lem1574615 (x : real) (y : real) (z : real) : (term420 x y z) = (term421 x y z).
Proof. exact (MK_COMB (@lem1574614 y z) (@lem1574613 x y z)). Qed.
Lemma lem1574616 (x : real) (z : real) (y : real) : (term422 x z y) = (term423 x z y).
Proof. exact (eq_refl (term422 x z y)). Qed.
Lemma lem1574617 (z : real) (y : real) : (term304 z y) = (term304 z y).
Proof. exact (eq_refl (term304 z y)). Qed.
Lemma lem1574618 (x : real) (z : real) (y : real) : (term424 x z y) = (term425 x z y).
Proof. exact (MK_COMB (@lem1574617 z y) (@lem1574616 x z y)). Qed.
Lemma lem1574619 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1574620 (x : real) (z : real) (y : real) : (term426 x z y) = (term427 x z y).
Proof. exact (MK_COMB (@lem1574619) (@lem1574618 x z y)). Qed.
Lemma lem1574621 (x : real) (y : real) (z : real) : (term416 x y z) = (term428 x y z).
Proof. exact (MK_COMB (@lem1574620 x z y) (@lem1574615 x y z)). Qed.
Lemma lem1574622 (x : real) (y : real) (z : real) : (term429 x y z) = (term429 x y z).
Proof. exact (eq_refl (term429 x y z)). Qed.
Lemma lem1574623 (x : real) (y : real) (z : real) : ((term412 x y z) = (term416 x y z)) = ((term412 x y z) = (term428 x y z)).
Proof. exact (MK_COMB (@lem1574622 x y z) (@lem1574621 x y z)). Qed.
Lemma lem1574624 (x : real) (y : real) (z : real) : (term412 x y z) = (term428 x y z).
Proof. exact (EQ_MP (@lem1574623 x y z) (@lem1574612 x y z)). Qed.
Lemma lem1574625 (z : real) (y : real) : (real_ge z y) = (term311 z y).
Proof. exact (@lem1483527 z y). Qed.
Lemma lem1574631 (z : real) (y : real) : (real_sub z y) = (term251 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1574636 (y : real) (z : real) : (term251 z y) = (term287 y z).
Proof. exact (@lem1483488 (term245 y) z). Qed.
Lemma lem1574638 (y : real) (z : real) : (real_sub z y) = (term287 y z).
Proof. exact (TRANS (@lem1574631 z y) (@lem1574636 y z)). Qed.
Lemma lem1574639 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1574640 (y : real) (z : real) : (term312 z y) = (term313 y z).
Proof. exact (MK_COMB (@lem1574639) (@lem1574638 y z)). Qed.
Lemma lem1574641 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574642 (y : real) (z : real) : (term311 z y) = (term314 y z).
Proof. exact (MK_COMB (@lem1574640 y z) (@lem1574641)). Qed.
Lemma lem1574643 (y : real) (z : real) : (real_ge z y) = (term314 y z).
Proof. exact (TRANS (@lem1574625 z y) (@lem1574642 y z)). Qed.
Lemma lem1574644 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574645 (x : real) (y : real) : (term277 x y) = (term277 x y).
Proof. exact (MK_COMB (@lem1574644) (@lem1574237 x y)). Qed.
Lemma lem1574646 (x : real) (y : real) : (term278 x y) = (term279 x y).
Proof. exact (MK_COMB (@lem1574645 x y) (@lem1574280 y)). Qed.
Lemma lem1574647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574648 (x : real) (y : real) : (term430 x y) = (term431 x y).
Proof. exact (MK_COMB (@lem1574647) (@lem1574646 x y)). Qed.
Lemma lem1574649 (x : real) (y : real) (z : real) : (term432 x z y) = (term433 x y z).
Proof. exact (MK_COMB (@lem1574648 x y) (@lem1574313 y z)). Qed.
Lemma lem1574650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574651 (x : real) (y : real) : (term277 x y) = (term277 x y).
Proof. exact (MK_COMB (@lem1574650) (@lem1574237 x y)). Qed.
Lemma lem1574652 (x : real) (y : real) (z : real) : (term423 x z y) = (term434 x y z).
Proof. exact (MK_COMB (@lem1574651 x y) (@lem1574649 x y z)). Qed.
Lemma lem1574653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574654 (y : real) (z : real) : (term304 z y) = (term329 y z).
Proof. exact (MK_COMB (@lem1574653) (@lem1574643 y z)). Qed.
Lemma lem1574655 (x : real) (y : real) (z : real) : (term425 x z y) = (term435 x y z).
Proof. exact (MK_COMB (@lem1574654 y z) (@lem1574652 x y z)). Qed.
Lemma lem1574656 (y : real) (z : real) : (real_gt y z) = (term332 y z).
Proof. exact (@lem1483525 y z). Qed.
Lemma lem1574669 (y : real) (z : real) : (real_sub y z) = (term251 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1574670 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574671 (y : real) (z : real) : (term333 y z) = (term257 y z).
Proof. exact (MK_COMB (@lem1574670) (@lem1574669 y z)). Qed.
Lemma lem1574672 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1574673 (y : real) (z : real) : (term332 y z) = (term249 y z).
Proof. exact (MK_COMB (@lem1574671 y z) (@lem1574672)). Qed.
Lemma lem1574674 (y : real) (z : real) : (real_gt y z) = (term249 y z).
Proof. exact (TRANS (@lem1574656 y z) (@lem1574673 y z)). Qed.
Lemma lem1574675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574676 (x : real) (z : real) : (term277 x z) = (term277 x z).
Proof. exact (MK_COMB (@lem1574675) (@lem1573826 x z)). Qed.
Lemma lem1574677 (x : real) (y : real) (z : real) : (term291 x y z) = (term291 x y z).
Proof. exact (MK_COMB (@lem1574676 x z) (@lem1573859 y z)). Qed.
Lemma lem1574678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574679 (x : real) (y : real) (z : real) : (term292 x y z) = (term292 x y z).
Proof. exact (MK_COMB (@lem1574678) (@lem1574677 x y z)). Qed.
Lemma lem1574680 (x : real) (y : real) (z : real) : (term436 x y z) = (term437 x y z).
Proof. exact (MK_COMB (@lem1574679 x y z) (@lem1573902 z)). Qed.
Lemma lem1574681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574682 (x : real) (z : real) : (term277 x z) = (term277 x z).
Proof. exact (MK_COMB (@lem1574681) (@lem1573826 x z)). Qed.
Lemma lem1574683 (x : real) (y : real) (z : real) : (term419 x y z) = (term438 x y z).
Proof. exact (MK_COMB (@lem1574682 x z) (@lem1574680 x y z)). Qed.
Lemma lem1574684 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574685 (y : real) (z : real) : (term299 y z) = (term277 y z).
Proof. exact (MK_COMB (@lem1574684) (@lem1574674 y z)). Qed.
Lemma lem1574686 (x : real) (y : real) (z : real) : (term421 x y z) = (term439 x y z).
Proof. exact (MK_COMB (@lem1574685 y z) (@lem1574683 x y z)). Qed.
Lemma lem1574687 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1574688 (x : real) (y : real) (z : real) : (term427 x z y) = (term440 x y z).
Proof. exact (MK_COMB (@lem1574687) (@lem1574655 x y z)). Qed.
Lemma lem1574689 (x : real) (y : real) (z : real) : (term428 x y z) = (term441 x y z).
Proof. exact (MK_COMB (@lem1574688 x y z) (@lem1574686 x y z)). Qed.
Lemma lem1574701 (x : real) (y : real) (z : real) : (term412 x y z) = (term441 x y z).
Proof. exact (TRANS (@lem1574624 x y z) (@lem1574689 x y z)). Qed.
Lemma lem1574703 (x : real) (a : real) (y : real) (r : real) : (term442 a x y r) = (term443 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem1574742 (y : real) (x : real) (z : real) : (term400 x y z) = (term444 y x z).
Proof. exact (@lem1574703 y (term245 x) z term58). Qed.
Lemma lem1574743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1574744 (y : real) (x : real) (z : real) : (term404 x y z) = (term445 y x z).
Proof. exact (MK_COMB (@lem1574743) (@lem1574742 y x z)). Qed.
Lemma lem1574745 (y : real) (x : real) (z : real) : (term403 y x z) = (term403 y x z).
Proof. exact (eq_refl (term403 y x z)). Qed.
Lemma lem1574748 (y : real) (x : real) (z : real) : (term405 y x z) = (term446 y x z).
Proof. exact (MK_COMB (@lem1574744 y x z) (@lem1574745 y x z)). Qed.
Lemma lem1574749 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1574750 (y : real) (x : real) (z : real) : (term413 y x z) = (term447 y x z).
Proof. exact (MK_COMB (@lem1574749) (@lem1574748 y x z)). Qed.
Lemma lem1574751 (x : real) (y : real) (z : real) : (term414 x y z) = (term448 x y z).
Proof. exact (MK_COMB (@lem1574750 y x z) (@lem1574701 x y z)). Qed.
Lemma lem1574752 (x : real) (y : real) (z : real) : (term378 x y z) = (term448 x y z).
Proof. exact (TRANS (@lem1574607 x y z) (@lem1574751 x y z)). Qed.
Lemma lem1574753 (x : real) (y : real) (z : real) : (term60 x y z) = (term448 x y z).
Proof. exact (TRANS (@lem1574432 x y z) (@lem1574752 x y z)). Qed.
Lemma lem1574754 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1574755 (x : real) (y : real) (z : real) : (term66 x y z) = (term449 x y z).
Proof. exact (MK_COMB (@lem1574754) (@lem1574345 x y z)). Qed.
Lemma lem1574756 (x : real) (y : real) (z : real) : (term67 x y z) = (term450 x y z).
Proof. exact (MK_COMB (@lem1574755 x y z) (@lem1574753 x y z)). Qed.
Lemma lem1574757 (x : real) (y : real) (z : real) (h1 : term450 x y z) : term450 x y z.
Proof. exact (h1). Qed.
Lemma lem1574758 (x : real) (y : real) (z : real) (h1 : term343 x y z) : term343 x y z.
Proof. exact (h1). Qed.
Lemma lem1574759 (x : real) (y : real) (z : real) (h1 : term341 x y z) : term341 x y z.
Proof. exact (h1). Qed.
Lemma lem1574760 (y : real) (x : real) (z : real) (h1 : term331 y x z) : term331 y x z.
Proof. exact (h1). Qed.
Lemma lem1574761 (y : real) (x : real) (z : real) (h1 : term331 y x z) : term330 y x z.
Proof. exact (proj2 (@lem1574760 y x z h1)). Qed.
Lemma lem1574763 (y : real) (x : real) (z : real) (h1 : term331 y x z) : term327 y x z.
Proof. exact (proj2 (@lem1574761 y x z h1)). Qed.
Lemma lem1574766 (y : real) (x : real) (z : real) (h1 : term331 y x z) : term276.
Proof. exact (proj1 (@lem1574763 y x z h1)). Qed.
Lemma lem1574770 (n : nat) (m : nat) : (term451 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1574771 : term276 = term452.
Proof. exact (@lem1574770 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1574772 : term452 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1574773 : term276 = False.
Proof. exact (TRANS (@lem1574771) (@lem1574772)). Qed.
Lemma lem1574774 (y : real) (x : real) (z : real) (h1 : term331 y x z) : False.
Proof. exact (EQ_MP (@lem1574773) (@lem1574766 y x z h1)). Qed.
Lemma lem1574775 (x : real) (y : real) (z : real) (h1 : term339 x y z) : term339 x y z.
Proof. exact (h1). Qed.
Lemma lem1574776 (x : real) (y : real) (z : real) (h1 : term339 x y z) : term338 x y z.
Proof. exact (proj2 (@lem1574775 x y z h1)). Qed.
Lemma lem1574778 (x : real) (y : real) (z : real) (h1 : term339 x y z) : term337 x y z.
Proof. exact (proj2 (@lem1574776 x y z h1)). Qed.
Lemma lem1574780 (x : real) (y : real) (z : real) (h1 : term339 x y z) : term335 y z.
Proof. exact (proj2 (@lem1574778 x y z h1)). Qed.
Lemma lem1574783 (x : real) (y : real) (z : real) (h1 : term339 x y z) : term276.
Proof. exact (proj1 (@lem1574780 x y z h1)). Qed.
Lemma lem1574785 (n : nat) (m : nat) : (term451 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1574786 : term276 = term452.
Proof. exact (@lem1574785 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1574787 : term452 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1574788 : term276 = False.
Proof. exact (TRANS (@lem1574786) (@lem1574787)). Qed.
Lemma lem1574789 (x : real) (y : real) (z : real) (h1 : term339 x y z) : False.
Proof. exact (EQ_MP (@lem1574788) (@lem1574783 x y z h1)). Qed.
Lemma lem1574790 (x : real) (y : real) (z : real) (h1 : term341 x y z) : False.
Proof. exact (or_elim (@lem1574759 x y z h1) (fun h0 : term331 y x z => @lem1574774 y x z h0) (fun h0 : term339 x y z => @lem1574789 x y z h0)). Qed.
Lemma lem1574791 (x : real) (y : real) (z : real) (h1 : term293 x y z) : term293 x y z.
Proof. exact (h1). Qed.
Lemma lem1574792 (x : real) (y : real) (z : real) (h1 : term293 x y z) : term280 x y z.
Proof. exact (proj2 (@lem1574791 x y z h1)). Qed.
Lemma lem1574796 (x : real) (y : real) (z : real) (h1 : term293 x y z) : term279 y z.
Proof. exact (proj2 (@lem1574792 x y z h1)). Qed.
Lemma lem1574798 (x : real) (y : real) (z : real) (h1 : term293 x y z) : term276.
Proof. exact (proj2 (@lem1574796 x y z h1)). Qed.
Lemma lem1574801 (n : nat) (m : nat) : (term451 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1574802 : term276 = term452.
Proof. exact (@lem1574801 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1574803 : term452 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1574804 : term276 = False.
Proof. exact (TRANS (@lem1574802) (@lem1574803)). Qed.
Lemma lem1574805 (x : real) (y : real) (z : real) (h1 : term293 x y z) : False.
Proof. exact (EQ_MP (@lem1574804) (@lem1574798 x y z h1)). Qed.
Lemma lem1574806 (x : real) (y : real) (z : real) (h1 : term343 x y z) : False.
Proof. exact (or_elim (@lem1574758 x y z h1) (fun h0 : term341 x y z => @lem1574790 x y z h0) (fun h0 : term293 x y z => @lem1574805 x y z h0)). Qed.
Lemma lem1574807 (x : real) (y : real) (z : real) (h1 : term448 x y z) : term448 x y z.
Proof. exact (h1). Qed.
Lemma lem1574808 (y : real) (x : real) (z : real) (h1 : term446 y x z) : term446 y x z.
Proof. exact (h1). Qed.
Lemma lem1574809 (y : real) (x : real) (z : real) (h1 : term446 y x z) : term403 y x z.
Proof. exact (proj2 (@lem1574808 y x z h1)). Qed.
Lemma lem1574814 (y : real) (x : real) (z : real) (h1 : term446 y x z) : term335 x y.
Proof. exact (proj1 (@lem1574809 y x z h1)). Qed.
Lemma lem1574816 (y : real) (x : real) (z : real) (h1 : term446 y x z) : term276.
Proof. exact (proj1 (@lem1574814 y x z h1)). Qed.
Lemma lem1574818 (n : nat) (m : nat) : (term451 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1574819 : term276 = term452.
Proof. exact (@lem1574818 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1574820 : term452 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1574821 : term276 = False.
Proof. exact (TRANS (@lem1574819) (@lem1574820)). Qed.
Lemma lem1574822 (y : real) (x : real) (z : real) (h1 : term446 y x z) : False.
Proof. exact (EQ_MP (@lem1574821) (@lem1574816 y x z h1)). Qed.
Lemma lem1574823 (x : real) (y : real) (z : real) (h1 : term441 x y z) : term441 x y z.
Proof. exact (h1). Qed.
Lemma lem1574824 (x : real) (y : real) (z : real) (h1 : term435 x y z) : term435 x y z.
Proof. exact (h1). Qed.
Lemma lem1574825 (x : real) (y : real) (z : real) (h1 : term435 x y z) : term434 x y z.
Proof. exact (proj2 (@lem1574824 x y z h1)). Qed.
Lemma lem1574827 (x : real) (y : real) (z : real) (h1 : term435 x y z) : term433 x y z.
Proof. exact (proj2 (@lem1574825 x y z h1)). Qed.
Lemma lem1574830 (x : real) (y : real) (z : real) (h1 : term435 x y z) : term279 x y.
Proof. exact (proj1 (@lem1574827 x y z h1)). Qed.
Lemma lem1574831 (x : real) (y : real) (z : real) (h1 : term435 x y z) : term276.
Proof. exact (proj2 (@lem1574830 x y z h1)). Qed.
Lemma lem1574834 (n : nat) (m : nat) : (term451 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1574835 : term276 = term452.
Proof. exact (@lem1574834 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1574836 : term452 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1574837 : term276 = False.
Proof. exact (TRANS (@lem1574835) (@lem1574836)). Qed.
Lemma lem1574838 (x : real) (y : real) (z : real) (h1 : term435 x y z) : False.
Proof. exact (EQ_MP (@lem1574837) (@lem1574831 x y z h1)). Qed.
Lemma lem1574839 (x : real) (y : real) (z : real) (h1 : term439 x y z) : term439 x y z.
Proof. exact (h1). Qed.
Lemma lem1574840 (x : real) (y : real) (z : real) (h1 : term439 x y z) : term438 x y z.
Proof. exact (proj2 (@lem1574839 x y z h1)). Qed.
Lemma lem1574842 (x : real) (y : real) (z : real) (h1 : term439 x y z) : term437 x y z.
Proof. exact (proj2 (@lem1574840 x y z h1)). Qed.
Lemma lem1574844 (x : real) (y : real) (z : real) (h1 : term439 x y z) : term276.
Proof. exact (proj2 (@lem1574842 x y z h1)). Qed.
Lemma lem1574849 (n : nat) (m : nat) : (term451 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1574850 : term276 = term452.
Proof. exact (@lem1574849 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1574851 : term452 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1574852 : term276 = False.
Proof. exact (TRANS (@lem1574850) (@lem1574851)). Qed.
Lemma lem1574853 (x : real) (y : real) (z : real) (h1 : term439 x y z) : False.
Proof. exact (EQ_MP (@lem1574852) (@lem1574844 x y z h1)). Qed.
Lemma lem1574854 (x : real) (y : real) (z : real) (h1 : term441 x y z) : False.
Proof. exact (or_elim (@lem1574823 x y z h1) (fun h0 : term435 x y z => @lem1574838 x y z h0) (fun h0 : term439 x y z => @lem1574853 x y z h0)). Qed.
Lemma lem1574855 (x : real) (y : real) (z : real) (h1 : term448 x y z) : False.
Proof. exact (or_elim (@lem1574807 x y z h1) (fun h0 : term446 y x z => @lem1574822 y x z h0) (fun h0 : term441 x y z => @lem1574854 x y z h0)). Qed.
Lemma lem1574856 (x : real) (y : real) (z : real) (h1 : term450 x y z) : False.
Proof. exact (or_elim (@lem1574757 x y z h1) (fun h0 : term343 x y z => @lem1574806 x y z h0) (fun h0 : term448 x y z => @lem1574855 x y z h0)). Qed.
Lemma lem1574857 (x : real) (y : real) (z : real) (h1 : term67 x y z) : term67 x y z.
Proof. exact (h1). Qed.
Lemma lem1574858 (x : real) (y : real) (z : real) (h1 : term67 x y z) : term450 x y z.
Proof. exact (EQ_MP (@lem1574756 x y z) (@lem1574857 x y z h1)). Qed.
Lemma lem1574859 (x : real) (y : real) (z : real) (h1 : term67 x y z) : (term450 x y z) = False.
Proof. exact (prop_ext (fun h2 : term450 x y z => @lem1574856 x y z h2) (fun h2 : False => @lem1574858 x y z h1)). Qed.
Lemma lem1574860 (x : real) (y : real) (z : real) (h1 : term67 x y z) : False.
Proof. exact (EQ_MP (@lem1574859 x y z h1) (@lem1574858 x y z h1)). Qed.
Lemma lem1574861 (x : real) (y : real) (h1 : term69 x y) : term69 x y.
Proof. exact (h1). Qed.
Lemma lem1574862 (x : real) (y : real) (h1 : term69 x y) : False.
Proof. exact (ex_elim (@lem1574861 x y h1) (fun z : real => fun h0 : term68 x y z => @lem1574860 x y z h0)). Qed.
Lemma lem1574863 (x : real) (h1 : term71 x) : term71 x.
Proof. exact (h1). Qed.
Lemma lem1574864 (x : real) (h1 : term71 x) : False.
Proof. exact (ex_elim (@lem1574863 x h1) (fun y : real => fun h0 : term70 x y => @lem1574862 x y h0)). Qed.
Lemma lem1574865 (h1 : term73) : term73.
Proof. exact (h1). Qed.
Lemma lem1574866 (h1 : term73) : False.
Proof. exact (ex_elim (@lem1574865 h1) (fun x : real => fun h0 : term72 x => @lem1574864 x h0)). Qed.
Lemma lem1574867 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1574868 (h1 : term22) : term73.
Proof. exact (EQ_MP (@lem1573546) (@lem1574867 h1)). Qed.
Lemma lem1574869 (h1 : term22) : term73 = False.
Proof. exact (prop_ext (fun h2 : term73 => @lem1574866 h2) (fun h2 : False => @lem1574868 h1)). Qed.
Lemma lem1574870 (h1 : term22) : False.
Proof. exact (EQ_MP (@lem1574869 h1) (@lem1574868 h1)). Qed.
Lemma lem1574871 : term453.
Proof. exact (fun h0 : term22 => @lem1574870 h0). Qed.
Lemma lem1574872 : term454.
Proof. exact (@lem1386578 term455). Qed.
Lemma lem1574873 : term455.
Proof. exact (@lem1574872 (@lem1574871)). Qed.
