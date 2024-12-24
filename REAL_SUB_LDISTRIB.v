Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_LDISTRIB_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483476_spec.
Require Import thm1483478_spec.
Require Import thm1483480_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1526158 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1526159 (y : real) (x : real) : (term2 y x) = (term3 y x).
Proof. exact (@lem1526158 (term4 y x)). Qed.
Lemma lem1526160 (y : real) (x : real) (z : real) : (term5 y x z) = ((term6 x y z) = (term7 y x z)).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1526161 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1526163 (y : real) (x : real) (z : real) : (term8 y x z) = (term9 y x z).
Proof. exact (MK_COMB (@lem1526161) (@lem1526160 y x z)). Qed.
Lemma lem1526164 (y : real) (x : real) : (term10 y x) = (term11 y x).
Proof. exact (fun_ext (fun z : real => @lem1526163 y x z)). Qed.
Lemma lem1526165 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526166 (y : real) (x : real) : (term3 y x) = (term12 y x).
Proof. exact (MK_COMB (@lem1526165) (@lem1526164 y x)). Qed.
Lemma lem1526167 (y : real) (x : real) : (term2 y x) = (term12 y x).
Proof. exact (TRANS (@lem1526159 y x) (@lem1526166 y x)). Qed.
Lemma lem1526168 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1526169 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem1526168 (term15 x)). Qed.
Lemma lem1526170 (y : real) (x : real) : (term16 x y) = (term17 y x).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1526171 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1526172 (y : real) (x : real) : (term18 x y) = (term2 y x).
Proof. exact (MK_COMB (@lem1526171) (@lem1526170 y x)). Qed.
Lemma lem1526173 (y : real) (x : real) : (term18 x y) = (term12 y x).
Proof. exact (TRANS (@lem1526172 y x) (@lem1526167 y x)). Qed.
Lemma lem1526174 (x : real) : (term19 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1526173 y x)). Qed.
Lemma lem1526175 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526176 (x : real) : (term14 x) = (term21 x).
Proof. exact (MK_COMB (@lem1526175) (@lem1526174 x)). Qed.
Lemma lem1526177 (x : real) : (term13 x) = (term21 x).
Proof. exact (TRANS (@lem1526169 x) (@lem1526176 x)). Qed.
Lemma lem1526178 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1526179 : term22 = term23.
Proof. exact (@lem1526178 term24). Qed.
Lemma lem1526180 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1526181 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1526182 (x : real) : (term27 x) = (term13 x).
Proof. exact (MK_COMB (@lem1526181) (@lem1526180 x)). Qed.
Lemma lem1526183 (x : real) : (term27 x) = (term21 x).
Proof. exact (TRANS (@lem1526182 x) (@lem1526177 x)). Qed.
Lemma lem1526184 : term28 = term29.
Proof. exact (fun_ext (fun x : real => @lem1526183 x)). Qed.
Lemma lem1526185 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526186 : term23 = term30.
Proof. exact (MK_COMB (@lem1526185) (@lem1526184)). Qed.
Lemma lem1526188 : term22 = term30.
Proof. exact (TRANS (@lem1526179) (@lem1526186)). Qed.
Lemma lem1526191 (y : real) (x : real) (z : real) : (term9 y x z) = (term9 y x z).
Proof. exact (eq_refl (term9 y x z)). Qed.
Lemma lem1526192 (y : real) (x : real) : (term11 y x) = (term11 y x).
Proof. exact (fun_ext (fun z : real => @lem1526191 y x z)). Qed.
Lemma lem1526193 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526194 (y : real) (x : real) : (term12 y x) = (term12 y x).
Proof. exact (MK_COMB (@lem1526193) (@lem1526192 y x)). Qed.
Lemma lem1526195 (x : real) : (term20 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1526194 y x)). Qed.
Lemma lem1526196 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526197 (x : real) : (term21 x) = (term21 x).
Proof. exact (MK_COMB (@lem1526196) (@lem1526195 x)). Qed.
Lemma lem1526198 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1526197 x)). Qed.
Lemma lem1526199 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526200 : term30 = term30.
Proof. exact (MK_COMB (@lem1526199) (@lem1526198)). Qed.
Lemma lem1526201 : term22 = term30.
Proof. exact (TRANS (@lem1526188) (@lem1526200)). Qed.
Lemma lem1526202 (y : real) (x : real) (z : real) : (term9 y x z) = (term31 y x z).
Proof. exact (@lem1483554 (term6 x y z) (term7 y x z)). Qed.
Lemma lem1526227 (y : real) (x : real) (z : real) : (term7 y x z) = (term32 y x z).
Proof. exact (@lem1483519 (real_mul x y) (real_mul x z)). Qed.
Lemma lem1526240 (y : real) (z : real) : (real_sub y z) = (term33 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1526243 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1526244 (x : real) (y : real) (z : real) : (term6 x y z) = (term34 x y z).
Proof. exact (MK_COMB (@lem1526243 x) (@lem1526240 y z)). Qed.
Lemma lem1526245 (y : real) (x : real) (z : real) : (term34 x y z) = (term35 y x z).
Proof. exact (@lem1483508 y x (term36 z)). Qed.
Lemma lem1526250 (x : real) (z : real) : (term37 x z) = (term38 x z).
Proof. exact (@lem1483478 term39 x z). Qed.
Lemma lem1526253 (x : real) (y : real) : (term40 x y) = (term40 x y).
Proof. exact (eq_refl (term40 x y)). Qed.
Lemma lem1526254 (y : real) (x : real) (z : real) : (term35 y x z) = (term32 y x z).
Proof. exact (MK_COMB (@lem1526253 x y) (@lem1526250 x z)). Qed.
Lemma lem1526255 (y : real) (x : real) (z : real) : (term34 x y z) = (term32 y x z).
Proof. exact (TRANS (@lem1526245 y x z) (@lem1526254 y x z)). Qed.
Lemma lem1526256 (y : real) (x : real) (z : real) : (term6 x y z) = (term32 y x z).
Proof. exact (TRANS (@lem1526244 x y z) (@lem1526255 y x z)). Qed.
Lemma lem1526257 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1526258 (y : real) (x : real) (z : real) : (term41 x y z) = (term42 y x z).
Proof. exact (MK_COMB (@lem1526257) (@lem1526256 y x z)). Qed.
Lemma lem1526259 (y : real) (x : real) (z : real) : (term43 y x z) = (term44 y x z).
Proof. exact (MK_COMB (@lem1526258 y x z) (@lem1526227 y x z)). Qed.
Lemma lem1526260 (y : real) (x : real) (z : real) : (term44 y x z) = (term45 y x z).
Proof. exact (@lem1483519 (term32 y x z) (term32 y x z)). Qed.
Lemma lem1526261 (y : real) (x : real) (z : real) : (term46 y x z) = (term47 y x z).
Proof. exact (@lem1483508 (real_mul x y) term39 (term38 x z)). Qed.
Lemma lem1526262 (x : real) (z : real) : (term48 x z) = (term49 x z).
Proof. exact (@lem1483476 term39 term39 (real_mul x z)). Qed.
Lemma lem1526264 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1526265 : term52 = term53.
Proof. exact (@lem1526264 term54 term54). Qed.
Lemma lem1526266 : (term55 = (BIT1 0)) = (term56 = term54).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1526267 : term56 = term54.
Proof. exact (EQ_MP (@lem1526266) (@lem940073)). Qed.
Lemma lem1526268 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1526269 : term53 = term57.
Proof. exact (MK_COMB (@lem1526268) (@lem1526267)). Qed.
Lemma lem1526270 : term52 = term57.
Proof. exact (TRANS (@lem1526265) (@lem1526269)). Qed.
Lemma lem1526271 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1526272 : term58 = term59.
Proof. exact (MK_COMB (@lem1526271) (@lem1526270)). Qed.
Lemma lem1526273 (x : real) (z : real) : (real_mul x z) = (real_mul x z).
Proof. exact (eq_refl (real_mul x z)). Qed.
Lemma lem1526274 (x : real) (z : real) : (term49 x z) = (term60 x z).
Proof. exact (MK_COMB (@lem1526272) (@lem1526273 x z)). Qed.
Lemma lem1526275 (x : real) (z : real) : (term48 x z) = (term60 x z).
Proof. exact (TRANS (@lem1526262 x z) (@lem1526274 x z)). Qed.
Lemma lem1526276 (x : real) (z : real) : (term60 x z) = (real_mul x z).
Proof. exact (@lem1483436 (real_mul x z)). Qed.
Lemma lem1526277 (x : real) (z : real) : (term48 x z) = (real_mul x z).
Proof. exact (TRANS (@lem1526275 x z) (@lem1526276 x z)). Qed.
Lemma lem1526280 (x : real) (y : real) : (term61 x y) = (term61 x y).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem1526281 (y : real) (x : real) (z : real) : (term47 y x z) = (term62 y x z).
Proof. exact (MK_COMB (@lem1526280 x y) (@lem1526277 x z)). Qed.
Lemma lem1526282 (y : real) (x : real) (z : real) : (term46 y x z) = (term62 y x z).
Proof. exact (TRANS (@lem1526261 y x z) (@lem1526281 y x z)). Qed.
Lemma lem1526283 (y : real) (x : real) (z : real) : (term63 y x z) = (term63 y x z).
Proof. exact (eq_refl (term63 y x z)). Qed.
Lemma lem1526284 (y : real) (x : real) (z : real) : (term45 y x z) = (term64 y x z).
Proof. exact (MK_COMB (@lem1526283 y x z) (@lem1526282 y x z)). Qed.
Lemma lem1526285 (y : real) (x : real) (z : real) : (term64 y x z) = (term65 y x z).
Proof. exact (@lem1483480 (real_mul x y) (term38 x y) (term38 x z) (real_mul x z)). Qed.
Lemma lem1526286 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (@lem1483442 term39 (real_mul x y)). Qed.
Lemma lem1526288 (m : nat) : (term68 m) = term69.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1526289 : term70 = term69.
Proof. exact (@lem1526288 term54). Qed.
Lemma lem1526290 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1526291 : term71 = term72.
Proof. exact (MK_COMB (@lem1526290) (@lem1526289)). Qed.
Lemma lem1526292 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1526293 (x : real) (y : real) : (term67 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem1526291) (@lem1526292 x y)). Qed.
Lemma lem1526294 (x : real) (y : real) : (term66 x y) = (term73 x y).
Proof. exact (TRANS (@lem1526286 x y) (@lem1526293 x y)). Qed.
Lemma lem1526295 (x : real) (y : real) : (term73 x y) = term69.
Proof. exact (@lem1483446 (real_mul x y)). Qed.
Lemma lem1526296 (x : real) (y : real) : (term66 x y) = term69.
Proof. exact (TRANS (@lem1526294 x y) (@lem1526295 x y)). Qed.
Lemma lem1526297 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1526298 (x : real) (y : real) : (term74 x y) = term75.
Proof. exact (MK_COMB (@lem1526297) (@lem1526296 x y)). Qed.
Lemma lem1526299 (x : real) (z : real) : (term76 x z) = (term67 x z).
Proof. exact (@lem1483440 term39 (real_mul x z)). Qed.
Lemma lem1526301 (m : nat) : (term68 m) = term69.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1526302 : term70 = term69.
Proof. exact (@lem1526301 term54). Qed.
Lemma lem1526303 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1526304 : term71 = term72.
Proof. exact (MK_COMB (@lem1526303) (@lem1526302)). Qed.
Lemma lem1526305 (x : real) (z : real) : (real_mul x z) = (real_mul x z).
Proof. exact (eq_refl (real_mul x z)). Qed.
Lemma lem1526306 (x : real) (z : real) : (term67 x z) = (term73 x z).
Proof. exact (MK_COMB (@lem1526304) (@lem1526305 x z)). Qed.
Lemma lem1526307 (x : real) (z : real) : (term76 x z) = (term73 x z).
Proof. exact (TRANS (@lem1526299 x z) (@lem1526306 x z)). Qed.
Lemma lem1526308 (x : real) (z : real) : (term73 x z) = term69.
Proof. exact (@lem1483446 (real_mul x z)). Qed.
Lemma lem1526309 (x : real) (z : real) : (term76 x z) = term69.
Proof. exact (TRANS (@lem1526307 x z) (@lem1526308 x z)). Qed.
Lemma lem1526310 (y : real) (x : real) (z : real) : (term65 y x z) = term77.
Proof. exact (MK_COMB (@lem1526298 x y) (@lem1526309 x z)). Qed.
Lemma lem1526311 (y : real) (x : real) (z : real) : (term64 y x z) = term77.
Proof. exact (TRANS (@lem1526285 y x z) (@lem1526310 y x z)). Qed.
Lemma lem1526312 : term77 = term69.
Proof. exact (@lem1483448 term69). Qed.
Lemma lem1526313 (y : real) (x : real) (z : real) : (term64 y x z) = term69.
Proof. exact (TRANS (@lem1526311 y x z) (@lem1526312)). Qed.
Lemma lem1526314 (y : real) (x : real) (z : real) : (term45 y x z) = term69.
Proof. exact (TRANS (@lem1526284 y x z) (@lem1526313 y x z)). Qed.
Lemma lem1526315 (y : real) (x : real) (z : real) : (term44 y x z) = term69.
Proof. exact (TRANS (@lem1526260 y x z) (@lem1526314 y x z)). Qed.
Lemma lem1526316 (y : real) (x : real) (z : real) : (term43 y x z) = term69.
Proof. exact (TRANS (@lem1526259 y x z) (@lem1526315 y x z)). Qed.
Lemma lem1526317 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1526318 (y : real) (x : real) (z : real) : (term78 y x z) = term79.
Proof. exact (MK_COMB (@lem1526317) (@lem1526316 y x z)). Qed.
Lemma lem1526319 : term79 = term80.
Proof. exact (@lem1483512 term69). Qed.
Lemma lem1526321 (x : nat) : (term81 x) = term69.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1526322 : term80 = term69.
Proof. exact (@lem1526321 term54). Qed.
Lemma lem1526323 : term79 = term69.
Proof. exact (TRANS (@lem1526319) (@lem1526322)). Qed.
Lemma lem1526324 (y : real) (x : real) (z : real) : (term82 y x z) = (term82 y x z).
Proof. exact (eq_refl (term82 y x z)). Qed.
Lemma lem1526325 (y : real) (x : real) (z : real) : ((term78 y x z) = term79) = ((term78 y x z) = term69).
Proof. exact (MK_COMB (@lem1526324 y x z) (@lem1526323)). Qed.
Lemma lem1526326 (y : real) (x : real) (z : real) : (term78 y x z) = term69.
Proof. exact (EQ_MP (@lem1526325 y x z) (@lem1526318 y x z)). Qed.
Lemma lem1526327 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1526328 (y : real) (x : real) (z : real) : (term83 y x z) = term84.
Proof. exact (MK_COMB (@lem1526327) (@lem1526326 y x z)). Qed.
Lemma lem1526329 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1526330 (y : real) (x : real) (z : real) : (term85 y x z) = term86.
Proof. exact (MK_COMB (@lem1526328 y x z) (@lem1526329)). Qed.
Lemma lem1526331 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1526332 (y : real) (x : real) (z : real) : (term87 y x z) = term84.
Proof. exact (MK_COMB (@lem1526331) (@lem1526316 y x z)). Qed.
Lemma lem1526333 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1526334 (y : real) (x : real) (z : real) : (term88 y x z) = term86.
Proof. exact (MK_COMB (@lem1526332 y x z) (@lem1526333)). Qed.
Lemma lem1526335 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1526336 (y : real) (x : real) (z : real) : (term89 y x z) = term90.
Proof. exact (MK_COMB (@lem1526335) (@lem1526334 y x z)). Qed.
Lemma lem1526337 (y : real) (x : real) (z : real) : (term31 y x z) = term91.
Proof. exact (MK_COMB (@lem1526336 y x z) (@lem1526330 y x z)). Qed.
Lemma lem1526338 (y : real) (x : real) (z : real) : (term9 y x z) = term91.
Proof. exact (TRANS (@lem1526202 y x z) (@lem1526337 y x z)). Qed.
Lemma lem1526339 (y : real) (x : real) : (term11 y x) = term92.
Proof. exact (fun_ext (fun z : real => @lem1526338 y x z)). Qed.
Lemma lem1526340 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526341 (y : real) (x : real) : (term12 y x) = term93.
Proof. exact (MK_COMB (@lem1526340) (@lem1526339 y x)). Qed.
Lemma lem1526342 (x : real) : (term20 x) = term94.
Proof. exact (fun_ext (fun y : real => @lem1526341 y x)). Qed.
Lemma lem1526343 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526344 (x : real) : (term21 x) = term95.
Proof. exact (MK_COMB (@lem1526343) (@lem1526342 x)). Qed.
Lemma lem1526345 : term29 = term96.
Proof. exact (fun_ext (fun x : real => @lem1526344 x)). Qed.
Lemma lem1526346 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526347 : term30 = term97.
Proof. exact (MK_COMB (@lem1526346) (@lem1526345)). Qed.
Lemma lem1526348 : term22 = term97.
Proof. exact (TRANS (@lem1526201) (@lem1526347)). Qed.
Lemma lem1526350 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1526351 (t : Prop) : (term99 t) = t.
Proof. exact (@lem1526350 real t). Qed.
Lemma lem1526352 : term97 = term95.
Proof. exact (@lem1526351 term95). Qed.
Lemma lem1526354 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1526355 (t : Prop) : (term99 t) = t.
Proof. exact (@lem1526354 real t). Qed.
Lemma lem1526356 : term95 = term93.
Proof. exact (@lem1526355 term93). Qed.
Lemma lem1526358 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term100 A P Q) = (term101 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1526359 (P : real -> Prop) (Q : real -> Prop) : (term102 P Q) = (term103 P Q).
Proof. exact (@lem1526358 real P Q). Qed.
Lemma lem1526360 : term104 = term105.
Proof. exact (@lem1526359 term106 term106). Qed.
Lemma lem1526361 (z : real) : (term107 z) = term86.
Proof. exact (eq_refl (term107 z)). Qed.
Lemma lem1526362 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1526363 (z : real) : (term108 z) = term90.
Proof. exact (MK_COMB (@lem1526362) (@lem1526361 z)). Qed.
Lemma lem1526364 (z : real) : (term107 z) = term86.
Proof. exact (eq_refl (term107 z)). Qed.
Lemma lem1526365 (z : real) : (term109 z) = term91.
Proof. exact (MK_COMB (@lem1526363 z) (@lem1526364 z)). Qed.
Lemma lem1526366 : term110 = term92.
Proof. exact (fun_ext (fun z : real => @lem1526365 z)). Qed.
Lemma lem1526367 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526368 : term104 = term93.
Proof. exact (MK_COMB (@lem1526367) (@lem1526366)). Qed.
Lemma lem1526369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1526370 : term111 = term112.
Proof. exact (MK_COMB (@lem1526369) (@lem1526368)). Qed.
Lemma lem1526371 (z : real) : (term107 z) = term86.
Proof. exact (eq_refl (term107 z)). Qed.
Lemma lem1526372 : term113 = term106.
Proof. exact (fun_ext (fun z : real => @lem1526371 z)). Qed.
Lemma lem1526373 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526374 : term114 = term115.
Proof. exact (MK_COMB (@lem1526373) (@lem1526372)). Qed.
Lemma lem1526375 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1526376 : term116 = term117.
Proof. exact (MK_COMB (@lem1526375) (@lem1526374)). Qed.
Lemma lem1526377 (z : real) : (term107 z) = term86.
Proof. exact (eq_refl (term107 z)). Qed.
Lemma lem1526378 : term113 = term106.
Proof. exact (fun_ext (fun z : real => @lem1526377 z)). Qed.
Lemma lem1526379 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526380 : term114 = term115.
Proof. exact (MK_COMB (@lem1526379) (@lem1526378)). Qed.
Lemma lem1526381 : term105 = term118.
Proof. exact (MK_COMB (@lem1526376) (@lem1526380)). Qed.
Lemma lem1526382 : (term104 = term105) = (term93 = term118).
Proof. exact (MK_COMB (@lem1526370) (@lem1526381)). Qed.
Lemma lem1526383 : term93 = term118.
Proof. exact (EQ_MP (@lem1526382) (@lem1526360)). Qed.
Lemma lem1526384 : term95 = term118.
Proof. exact (TRANS (@lem1526356) (@lem1526383)). Qed.
Lemma lem1526385 : term97 = term118.
Proof. exact (TRANS (@lem1526352) (@lem1526384)). Qed.
Lemma lem1526387 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1526388 (t : Prop) : (term99 t) = t.
Proof. exact (@lem1526387 real t). Qed.
Lemma lem1526389 : term115 = term86.
Proof. exact (@lem1526388 term86). Qed.
Lemma lem1526390 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1526391 : term117 = term90.
Proof. exact (MK_COMB (@lem1526390) (@lem1526389)). Qed.
Lemma lem1526393 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1526394 (t : Prop) : (term99 t) = t.
Proof. exact (@lem1526393 real t). Qed.
Lemma lem1526395 : term115 = term86.
Proof. exact (@lem1526394 term86). Qed.
Lemma lem1526396 : term118 = term91.
Proof. exact (MK_COMB (@lem1526391) (@lem1526395)). Qed.
Lemma lem1526399 : term97 = term91.
Proof. exact (TRANS (@lem1526385) (@lem1526396)). Qed.
Lemma lem1526408 : term22 = term91.
Proof. exact (TRANS (@lem1526348) (@lem1526399)). Qed.
Lemma lem1526418 (h1 : term91) : term91.
Proof. exact (h1). Qed.
Lemma lem1526419 (h1 : term86) : term86.
Proof. exact (h1). Qed.
Lemma lem1526421 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1526422 : term86 = term120.
Proof. exact (@lem1526421 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1526423 : term120 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1526424 : term86 = False.
Proof. exact (TRANS (@lem1526422) (@lem1526423)). Qed.
Lemma lem1526425 (h1 : term86) : False.
Proof. exact (EQ_MP (@lem1526424) (@lem1526419 h1)). Qed.
Lemma lem1526426 (h1 : term86) : term86.
Proof. exact (h1). Qed.
Lemma lem1526428 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1526429 : term86 = term120.
Proof. exact (@lem1526428 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1526430 : term120 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1526431 : term86 = False.
Proof. exact (TRANS (@lem1526429) (@lem1526430)). Qed.
Lemma lem1526432 (h1 : term86) : False.
Proof. exact (EQ_MP (@lem1526431) (@lem1526426 h1)). Qed.
Lemma lem1526433 (h1 : term91) : False.
Proof. exact (or_elim (@lem1526418 h1) (fun h0 : term86 => @lem1526425 h0) (fun h0 : term86 => @lem1526432 h0)). Qed.
Lemma lem1526435 (h1 : term91) : term91.
Proof. exact (h1). Qed.
Lemma lem1526436 (h1 : term91) : term91 = False.
Proof. exact (prop_ext (fun h2 : term91 => @lem1526433 h1) (fun h2 : False => @lem1526435 h1)). Qed.
Lemma lem1526437 (h1 : term91) : False.
Proof. exact (EQ_MP (@lem1526436 h1) (@lem1526435 h1)). Qed.
Lemma lem1526438 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1526439 (h1 : term22) : term91.
Proof. exact (EQ_MP (@lem1526408) (@lem1526438 h1)). Qed.
Lemma lem1526440 (h1 : term22) : term91 = False.
Proof. exact (prop_ext (fun h2 : term91 => @lem1526437 h2) (fun h2 : False => @lem1526439 h1)). Qed.
Lemma lem1526441 (h1 : term22) : False.
Proof. exact (EQ_MP (@lem1526440 h1) (@lem1526439 h1)). Qed.
Lemma lem1526442 : term121.
Proof. exact (fun h0 : term22 => @lem1526441 h0). Qed.
Lemma lem1526443 : term122.
Proof. exact (@lem1386578 term123). Qed.
Lemma lem1526444 : term123.
Proof. exact (@lem1526443 (@lem1526442)). Qed.
