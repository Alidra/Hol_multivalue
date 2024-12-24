Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_SUB_RADD_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1513146 (x : real) (z : real) (y : real) : (term0 x z y) = (term1 x z y).
Proof. exact (@lem17646 (term2 x y z) (term3 x z y)). Qed.
Lemma lem1513147 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1513148 (x : real) (y : real) : (term6 x y) = (term7 x y).
Proof. exact (@lem1513147 (term8 x y)). Qed.
Lemma lem1513149 (x : real) (z : real) (y : real) : (term9 x y z) = ((term2 x y z) = (term3 x z y)).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1513150 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1513151 (x : real) (z : real) (y : real) : (term10 x y z) = (term0 x z y).
Proof. exact (MK_COMB (@lem1513150) (@lem1513149 x z y)). Qed.
Lemma lem1513152 (x : real) (z : real) (y : real) : (term10 x y z) = (term1 x z y).
Proof. exact (TRANS (@lem1513151 x z y) (@lem1513146 x z y)). Qed.
Lemma lem1513153 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (fun_ext (fun z : real => @lem1513152 x z y)). Qed.
Lemma lem1513154 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513155 (x : real) (y : real) : (term7 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1513154) (@lem1513153 x y)). Qed.
Lemma lem1513156 (x : real) (y : real) : (term6 x y) = (term13 x y).
Proof. exact (TRANS (@lem1513148 x y) (@lem1513155 x y)). Qed.
Lemma lem1513157 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1513158 (x : real) : (term14 x) = (term15 x).
Proof. exact (@lem1513157 (term16 x)). Qed.
Lemma lem1513159 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1513160 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1513161 (x : real) (y : real) : (term19 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem1513160) (@lem1513159 x y)). Qed.
Lemma lem1513162 (x : real) (y : real) : (term19 x y) = (term13 x y).
Proof. exact (TRANS (@lem1513161 x y) (@lem1513156 x y)). Qed.
Lemma lem1513163 (x : real) : (term20 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1513162 x y)). Qed.
Lemma lem1513164 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513165 (x : real) : (term15 x) = (term22 x).
Proof. exact (MK_COMB (@lem1513164) (@lem1513163 x)). Qed.
Lemma lem1513166 (x : real) : (term14 x) = (term22 x).
Proof. exact (TRANS (@lem1513158 x) (@lem1513165 x)). Qed.
Lemma lem1513167 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1513168 : term23 = term24.
Proof. exact (@lem1513167 term25). Qed.
Lemma lem1513169 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1513170 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1513171 (x : real) : (term28 x) = (term14 x).
Proof. exact (MK_COMB (@lem1513170) (@lem1513169 x)). Qed.
Lemma lem1513172 (x : real) : (term28 x) = (term22 x).
Proof. exact (TRANS (@lem1513171 x) (@lem1513166 x)). Qed.
Lemma lem1513173 : term29 = term30.
Proof. exact (fun_ext (fun x : real => @lem1513172 x)). Qed.
Lemma lem1513174 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513175 : term24 = term31.
Proof. exact (MK_COMB (@lem1513174) (@lem1513173)). Qed.
Lemma lem1513177 : term23 = term31.
Proof. exact (TRANS (@lem1513168) (@lem1513175)). Qed.
Lemma lem1513194 (x : real) (z : real) (y : real) : (term1 x z y) = (term1 x z y).
Proof. exact (eq_refl (term1 x z y)). Qed.
Lemma lem1513195 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (fun_ext (fun z : real => @lem1513194 x z y)). Qed.
Lemma lem1513196 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513197 (x : real) (y : real) : (term13 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1513196) (@lem1513195 x y)). Qed.
Lemma lem1513198 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1513197 x y)). Qed.
Lemma lem1513199 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513200 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1513199) (@lem1513198 x)). Qed.
Lemma lem1513201 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1513200 x)). Qed.
Lemma lem1513202 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513203 : term31 = term31.
Proof. exact (MK_COMB (@lem1513202) (@lem1513201)). Qed.
Lemma lem1513204 : term23 = term31.
Proof. exact (TRANS (@lem1513177) (@lem1513203)). Qed.
Lemma lem1513205 (z : real) (x : real) (y : real) : (term2 x y z) = (term32 z x y).
Proof. exact (@lem1483521 z (real_sub x y)). Qed.
Lemma lem1513218 (x : real) (y : real) : (real_sub x y) = (term33 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1513221 (z : real) : (real_sub z) = (real_sub z).
Proof. exact (eq_refl (real_sub z)). Qed.
Lemma lem1513222 (z : real) (x : real) (y : real) : (term34 z x y) = (term35 z x y).
Proof. exact (MK_COMB (@lem1513221 z) (@lem1513218 x y)). Qed.
Lemma lem1513223 (z : real) (x : real) (y : real) : (term35 z x y) = (term36 z x y).
Proof. exact (@lem1483519 z (term33 x y)). Qed.
Lemma lem1513224 (x : real) (y : real) : (term37 x y) = (term38 x y).
Proof. exact (@lem1483508 x term39 (term40 y)). Qed.
Lemma lem1513225 (y : real) : (term41 y) = (term42 y).
Proof. exact (@lem1483476 term39 term39 y). Qed.
Lemma lem1513227 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1513228 : term45 = term46.
Proof. exact (@lem1513227 term47 term47). Qed.
Lemma lem1513229 : (term48 = (BIT1 0)) = (term49 = term47).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1513230 : term49 = term47.
Proof. exact (EQ_MP (@lem1513229) (@lem940073)). Qed.
Lemma lem1513231 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1513232 : term46 = term50.
Proof. exact (MK_COMB (@lem1513231) (@lem1513230)). Qed.
Lemma lem1513233 : term45 = term50.
Proof. exact (TRANS (@lem1513228) (@lem1513232)). Qed.
Lemma lem1513234 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1513235 : term51 = term52.
Proof. exact (MK_COMB (@lem1513234) (@lem1513233)). Qed.
Lemma lem1513236 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1513237 (y : real) : (term42 y) = (term53 y).
Proof. exact (MK_COMB (@lem1513235) (@lem1513236 y)). Qed.
Lemma lem1513238 (y : real) : (term41 y) = (term53 y).
Proof. exact (TRANS (@lem1513225 y) (@lem1513237 y)). Qed.
Lemma lem1513239 (y : real) : (term53 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1513240 (y : real) : (term41 y) = y.
Proof. exact (TRANS (@lem1513238 y) (@lem1513239 y)). Qed.
Lemma lem1513243 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1513244 (x : real) (y : real) : (term38 x y) = (term55 x y).
Proof. exact (MK_COMB (@lem1513243 x) (@lem1513240 y)). Qed.
Lemma lem1513245 (x : real) (y : real) : (term37 x y) = (term55 x y).
Proof. exact (TRANS (@lem1513224 x y) (@lem1513244 x y)). Qed.
Lemma lem1513246 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1513247 (z : real) (x : real) (y : real) : (term36 z x y) = (term56 z x y).
Proof. exact (MK_COMB (@lem1513246 z) (@lem1513245 x y)). Qed.
Lemma lem1513248 (x : real) (z : real) (y : real) : (term56 z x y) = (term57 x z y).
Proof. exact (@lem1483484 (term40 x) z y). Qed.
Lemma lem1513249 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1513250 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1513251 (x : real) (y : real) (z : real) : (term57 x z y) = (term57 x y z).
Proof. exact (MK_COMB (@lem1513250 x) (@lem1513249 y z)). Qed.
Lemma lem1513252 (x : real) (y : real) (z : real) : (term56 z x y) = (term57 x y z).
Proof. exact (TRANS (@lem1513248 x z y) (@lem1513251 x y z)). Qed.
Lemma lem1513253 (x : real) (y : real) (z : real) : (term36 z x y) = (term57 x y z).
Proof. exact (TRANS (@lem1513247 z x y) (@lem1513252 x y z)). Qed.
Lemma lem1513254 (x : real) (y : real) (z : real) : (term35 z x y) = (term57 x y z).
Proof. exact (TRANS (@lem1513223 z x y) (@lem1513253 x y z)). Qed.
Lemma lem1513255 (x : real) (y : real) (z : real) : (term34 z x y) = (term57 x y z).
Proof. exact (TRANS (@lem1513222 z x y) (@lem1513254 x y z)). Qed.
Lemma lem1513256 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1513257 (x : real) (y : real) (z : real) : (term58 z x y) = (term59 x y z).
Proof. exact (MK_COMB (@lem1513256) (@lem1513255 x y z)). Qed.
Lemma lem1513258 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1513259 (x : real) (y : real) (z : real) : (term32 z x y) = (term61 x y z).
Proof. exact (MK_COMB (@lem1513257 x y z) (@lem1513258)). Qed.
Lemma lem1513260 (x : real) (y : real) (z : real) : (term2 x y z) = (term61 x y z).
Proof. exact (TRANS (@lem1513205 z x y) (@lem1513259 x y z)). Qed.
Lemma lem1513261 (x : real) (z : real) (y : real) : (term62 x z y) = (term63 x z y).
Proof. exact (@lem1483531 x (real_add z y)). Qed.
Lemma lem1513268 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1513271 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1513272 (x : real) (y : real) (z : real) : (term64 x z y) = (term64 x y z).
Proof. exact (MK_COMB (@lem1513271 x) (@lem1513268 y z)). Qed.
Lemma lem1513273 (x : real) (y : real) (z : real) : (term64 x y z) = (term65 x y z).
Proof. exact (@lem1483519 x (real_add y z)). Qed.
Lemma lem1513280 (y : real) (z : real) : (term66 y z) = (term67 y z).
Proof. exact (@lem1483508 y term39 z). Qed.
Lemma lem1513281 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1513284 (x : real) (y : real) (z : real) : (term65 x y z) = (term68 x y z).
Proof. exact (MK_COMB (@lem1513281 x) (@lem1513280 y z)). Qed.
Lemma lem1513285 (x : real) (y : real) (z : real) : (term64 x y z) = (term68 x y z).
Proof. exact (TRANS (@lem1513273 x y z) (@lem1513284 x y z)). Qed.
Lemma lem1513286 (x : real) (y : real) (z : real) : (term64 x z y) = (term68 x y z).
Proof. exact (TRANS (@lem1513272 x y z) (@lem1513285 x y z)). Qed.
Lemma lem1513287 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1513288 (x : real) (y : real) (z : real) : (term69 x z y) = (term70 x y z).
Proof. exact (MK_COMB (@lem1513287) (@lem1513286 x y z)). Qed.
Lemma lem1513289 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1513290 (x : real) (y : real) (z : real) : (term63 x z y) = (term71 x y z).
Proof. exact (MK_COMB (@lem1513288 x y z) (@lem1513289)). Qed.
Lemma lem1513291 (x : real) (y : real) (z : real) : (term62 x z y) = (term71 x y z).
Proof. exact (TRANS (@lem1513261 x z y) (@lem1513290 x y z)). Qed.
Lemma lem1513292 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1513293 (x : real) (y : real) (z : real) : (term72 x y z) = (term73 x y z).
Proof. exact (MK_COMB (@lem1513292) (@lem1513260 x y z)). Qed.
Lemma lem1513294 (x : real) (y : real) (z : real) : (term74 x z y) = (term75 x y z).
Proof. exact (MK_COMB (@lem1513293 x y z) (@lem1513291 x y z)). Qed.
Lemma lem1513295 (x : real) (y : real) (z : real) : (term76 x y z) = (term77 x y z).
Proof. exact (@lem1483531 (real_sub x y) z). Qed.
Lemma lem1513296 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1513309 (x : real) (y : real) : (real_sub x y) = (term33 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1513310 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1513311 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1513310) (@lem1513309 x y)). Qed.
Lemma lem1513312 (x : real) (y : real) (z : real) : (term80 x y z) = (term81 x y z).
Proof. exact (MK_COMB (@lem1513311 x y) (@lem1513296 z)). Qed.
Lemma lem1513313 (x : real) (y : real) (z : real) : (term81 x y z) = (term82 x y z).
Proof. exact (@lem1483519 (term33 x y) z). Qed.
Lemma lem1513322 (x : real) (y : real) (z : real) : (term82 x y z) = (term68 x y z).
Proof. exact (@lem1483482 x (term40 y) (term40 z)). Qed.
Lemma lem1513323 (x : real) (y : real) (z : real) : (term81 x y z) = (term68 x y z).
Proof. exact (TRANS (@lem1513313 x y z) (@lem1513322 x y z)). Qed.
Lemma lem1513324 (x : real) (y : real) (z : real) : (term80 x y z) = (term68 x y z).
Proof. exact (TRANS (@lem1513312 x y z) (@lem1513323 x y z)). Qed.
Lemma lem1513325 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1513326 (x : real) (y : real) (z : real) : (term83 x y z) = (term70 x y z).
Proof. exact (MK_COMB (@lem1513325) (@lem1513324 x y z)). Qed.
Lemma lem1513327 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1513328 (x : real) (y : real) (z : real) : (term77 x y z) = (term71 x y z).
Proof. exact (MK_COMB (@lem1513326 x y z) (@lem1513327)). Qed.
Lemma lem1513329 (x : real) (y : real) (z : real) : (term76 x y z) = (term71 x y z).
Proof. exact (TRANS (@lem1513295 x y z) (@lem1513328 x y z)). Qed.
Lemma lem1513330 (z : real) (y : real) (x : real) : (term3 x z y) = (term84 z y x).
Proof. exact (@lem1483521 (real_add z y) x). Qed.
Lemma lem1513331 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1513338 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1513339 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1513340 (y : real) (z : real) : (term85 z y) = (term85 y z).
Proof. exact (MK_COMB (@lem1513339) (@lem1513338 y z)). Qed.
Lemma lem1513341 (y : real) (z : real) (x : real) : (term86 z y x) = (term86 y z x).
Proof. exact (MK_COMB (@lem1513340 y z) (@lem1513331 x)). Qed.
Lemma lem1513342 (y : real) (z : real) (x : real) : (term86 y z x) = (term87 y z x).
Proof. exact (@lem1483519 (real_add y z) x). Qed.
Lemma lem1513347 (x : real) (y : real) (z : real) : (term87 y z x) = (term57 x y z).
Proof. exact (@lem1483488 (term40 x) (real_add y z)). Qed.
Lemma lem1513348 (x : real) (y : real) (z : real) : (term86 y z x) = (term57 x y z).
Proof. exact (TRANS (@lem1513342 y z x) (@lem1513347 x y z)). Qed.
Lemma lem1513349 (x : real) (y : real) (z : real) : (term86 z y x) = (term57 x y z).
Proof. exact (TRANS (@lem1513341 y z x) (@lem1513348 x y z)). Qed.
Lemma lem1513350 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1513351 (x : real) (y : real) (z : real) : (term88 z y x) = (term59 x y z).
Proof. exact (MK_COMB (@lem1513350) (@lem1513349 x y z)). Qed.
Lemma lem1513352 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1513353 (x : real) (y : real) (z : real) : (term84 z y x) = (term61 x y z).
Proof. exact (MK_COMB (@lem1513351 x y z) (@lem1513352)). Qed.
Lemma lem1513354 (x : real) (y : real) (z : real) : (term3 x z y) = (term61 x y z).
Proof. exact (TRANS (@lem1513330 z y x) (@lem1513353 x y z)). Qed.
Lemma lem1513355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1513356 (x : real) (y : real) (z : real) : (term89 x y z) = (term90 x y z).
Proof. exact (MK_COMB (@lem1513355) (@lem1513329 x y z)). Qed.
Lemma lem1513357 (x : real) (y : real) (z : real) : (term91 x z y) = (term92 x y z).
Proof. exact (MK_COMB (@lem1513356 x y z) (@lem1513354 x y z)). Qed.
Lemma lem1513358 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1513359 (x : real) (y : real) (z : real) : (term93 x z y) = (term94 x y z).
Proof. exact (MK_COMB (@lem1513358) (@lem1513294 x y z)). Qed.
Lemma lem1513360 (x : real) (y : real) (z : real) : (term1 x z y) = (term95 x y z).
Proof. exact (MK_COMB (@lem1513359 x y z) (@lem1513357 x y z)). Qed.
Lemma lem1513361 (x : real) (y : real) : (term12 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1513360 x y z)). Qed.
Lemma lem1513362 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513363 (x : real) (y : real) : (term13 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1513362) (@lem1513361 x y)). Qed.
Lemma lem1513364 (x : real) : (term21 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1513363 x y)). Qed.
Lemma lem1513365 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513366 (x : real) : (term22 x) = (term99 x).
Proof. exact (MK_COMB (@lem1513365) (@lem1513364 x)). Qed.
Lemma lem1513367 : term30 = term100.
Proof. exact (fun_ext (fun x : real => @lem1513366 x)). Qed.
Lemma lem1513368 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513369 : term31 = term101.
Proof. exact (MK_COMB (@lem1513368) (@lem1513367)). Qed.
Lemma lem1513370 : term23 = term101.
Proof. exact (TRANS (@lem1513204) (@lem1513369)). Qed.
Lemma lem1513380 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1513381 (P : real -> Prop) (Q : real -> Prop) : (term104 P Q) = (term105 P Q).
Proof. exact (@lem1513380 real P Q). Qed.
Lemma lem1513382 (x : real) (y : real) : (term106 x y) = (term107 x y).
Proof. exact (@lem1513381 (term108 x y) (term109 x y)). Qed.
Lemma lem1513383 (x : real) (y : real) (z : real) : (term110 x y z) = (term75 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1513384 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1513385 (x : real) (y : real) (z : real) : (term111 x y z) = (term94 x y z).
Proof. exact (MK_COMB (@lem1513384) (@lem1513383 x y z)). Qed.
Lemma lem1513386 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1513387 (x : real) (y : real) (z : real) : (term113 x y z) = (term95 x y z).
Proof. exact (MK_COMB (@lem1513385 x y z) (@lem1513386 x y z)). Qed.
Lemma lem1513388 (x : real) (y : real) : (term114 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1513387 x y z)). Qed.
Lemma lem1513389 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513390 (x : real) (y : real) : (term106 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1513389) (@lem1513388 x y)). Qed.
Lemma lem1513391 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1513392 (x : real) (y : real) : (term115 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1513391) (@lem1513390 x y)). Qed.
Lemma lem1513393 (x : real) (y : real) (z : real) : (term110 x y z) = (term75 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1513394 (x : real) (y : real) : (term117 x y) = (term108 x y).
Proof. exact (fun_ext (fun z : real => @lem1513393 x y z)). Qed.
Lemma lem1513395 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513396 (x : real) (y : real) : (term118 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1513395) (@lem1513394 x y)). Qed.
Lemma lem1513397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1513398 (x : real) (y : real) : (term120 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1513397) (@lem1513396 x y)). Qed.
Lemma lem1513399 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1513400 (x : real) (y : real) : (term122 x y) = (term109 x y).
Proof. exact (fun_ext (fun z : real => @lem1513399 x y z)). Qed.
Lemma lem1513401 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513402 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1513401) (@lem1513400 x y)). Qed.
Lemma lem1513403 (x : real) (y : real) : (term107 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1513398 x y) (@lem1513402 x y)). Qed.
Lemma lem1513404 (x : real) (y : real) : ((term106 x y) = (term107 x y)) = ((term97 x y) = (term125 x y)).
Proof. exact (MK_COMB (@lem1513392 x y) (@lem1513403 x y)). Qed.
Lemma lem1513405 (x : real) (y : real) : (term97 x y) = (term125 x y).
Proof. exact (EQ_MP (@lem1513404 x y) (@lem1513382 x y)). Qed.
Lemma lem1513502 (x : real) : (term98 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1513405 x y)). Qed.
Lemma lem1513503 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513504 (x : real) : (term99 x) = (term127 x).
Proof. exact (MK_COMB (@lem1513503) (@lem1513502 x)). Qed.
Lemma lem1513506 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1513507 (P : real -> Prop) (Q : real -> Prop) : (term104 P Q) = (term105 P Q).
Proof. exact (@lem1513506 real P Q). Qed.
Lemma lem1513508 (x : real) : (term128 x) = (term129 x).
Proof. exact (@lem1513507 (term130 x) (term131 x)). Qed.
Lemma lem1513509 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1513510 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1513511 (x : real) (y : real) : (term133 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1513510) (@lem1513509 x y)). Qed.
Lemma lem1513512 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1513513 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1513511 x y) (@lem1513512 x y)). Qed.
Lemma lem1513514 (x : real) : (term136 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1513513 x y)). Qed.
Lemma lem1513515 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513516 (x : real) : (term128 x) = (term127 x).
Proof. exact (MK_COMB (@lem1513515) (@lem1513514 x)). Qed.
Lemma lem1513517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1513518 (x : real) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem1513517) (@lem1513516 x)). Qed.
Lemma lem1513519 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1513520 (x : real) : (term139 x) = (term130 x).
Proof. exact (fun_ext (fun y : real => @lem1513519 x y)). Qed.
Lemma lem1513521 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513522 (x : real) : (term140 x) = (term141 x).
Proof. exact (MK_COMB (@lem1513521) (@lem1513520 x)). Qed.
Lemma lem1513523 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1513524 (x : real) : (term142 x) = (term143 x).
Proof. exact (MK_COMB (@lem1513523) (@lem1513522 x)). Qed.
Lemma lem1513525 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1513526 (x : real) : (term144 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1513525 x y)). Qed.
Lemma lem1513527 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513528 (x : real) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1513527) (@lem1513526 x)). Qed.
Lemma lem1513529 (x : real) : (term129 x) = (term147 x).
Proof. exact (MK_COMB (@lem1513524 x) (@lem1513528 x)). Qed.
Lemma lem1513530 (x : real) : ((term128 x) = (term129 x)) = ((term127 x) = (term147 x)).
Proof. exact (MK_COMB (@lem1513518 x) (@lem1513529 x)). Qed.
Lemma lem1513531 (x : real) : (term127 x) = (term147 x).
Proof. exact (EQ_MP (@lem1513530 x) (@lem1513508 x)). Qed.
Lemma lem1513636 (x : real) : (term99 x) = (term147 x).
Proof. exact (TRANS (@lem1513504 x) (@lem1513531 x)). Qed.
Lemma lem1513637 : term100 = term148.
Proof. exact (fun_ext (fun x : real => @lem1513636 x)). Qed.
Lemma lem1513638 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513639 : term101 = term149.
Proof. exact (MK_COMB (@lem1513638) (@lem1513637)). Qed.
Lemma lem1513641 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1513642 (P : real -> Prop) (Q : real -> Prop) : (term104 P Q) = (term105 P Q).
Proof. exact (@lem1513641 real P Q). Qed.
Lemma lem1513643 : term150 = term151.
Proof. exact (@lem1513642 term152 term153). Qed.
Lemma lem1513644 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1513645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1513646 (x : real) : (term155 x) = (term143 x).
Proof. exact (MK_COMB (@lem1513645) (@lem1513644 x)). Qed.
Lemma lem1513647 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1513648 (x : real) : (term157 x) = (term147 x).
Proof. exact (MK_COMB (@lem1513646 x) (@lem1513647 x)). Qed.
Lemma lem1513649 : term158 = term148.
Proof. exact (fun_ext (fun x : real => @lem1513648 x)). Qed.
Lemma lem1513650 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513651 : term150 = term149.
Proof. exact (MK_COMB (@lem1513650) (@lem1513649)). Qed.
Lemma lem1513652 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1513653 : term159 = term160.
Proof. exact (MK_COMB (@lem1513652) (@lem1513651)). Qed.
Lemma lem1513654 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1513655 : term161 = term152.
Proof. exact (fun_ext (fun x : real => @lem1513654 x)). Qed.
Lemma lem1513656 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513657 : term162 = term163.
Proof. exact (MK_COMB (@lem1513656) (@lem1513655)). Qed.
Lemma lem1513658 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1513659 : term164 = term165.
Proof. exact (MK_COMB (@lem1513658) (@lem1513657)). Qed.
Lemma lem1513660 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1513661 : term166 = term153.
Proof. exact (fun_ext (fun x : real => @lem1513660 x)). Qed.
Lemma lem1513662 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513663 : term167 = term168.
Proof. exact (MK_COMB (@lem1513662) (@lem1513661)). Qed.
Lemma lem1513664 : term151 = term169.
Proof. exact (MK_COMB (@lem1513659) (@lem1513663)). Qed.
Lemma lem1513665 : (term150 = term151) = (term149 = term169).
Proof. exact (MK_COMB (@lem1513653) (@lem1513664)). Qed.
Lemma lem1513666 : term149 = term169.
Proof. exact (EQ_MP (@lem1513665) (@lem1513643)). Qed.
Lemma lem1513779 : term101 = term169.
Proof. exact (TRANS (@lem1513639) (@lem1513666)). Qed.
Lemma lem1513781 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1513782 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term104 P Q).
Proof. exact (@lem1513781 real P Q). Qed.
Lemma lem1513783 : term151 = term150.
Proof. exact (@lem1513782 term152 term153). Qed.
Lemma lem1513784 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1513785 : term161 = term152.
Proof. exact (fun_ext (fun x : real => @lem1513784 x)). Qed.
Lemma lem1513786 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513787 : term162 = term163.
Proof. exact (MK_COMB (@lem1513786) (@lem1513785)). Qed.
Lemma lem1513788 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1513789 : term164 = term165.
Proof. exact (MK_COMB (@lem1513788) (@lem1513787)). Qed.
Lemma lem1513790 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1513791 : term166 = term153.
Proof. exact (fun_ext (fun x : real => @lem1513790 x)). Qed.
Lemma lem1513792 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513793 : term167 = term168.
Proof. exact (MK_COMB (@lem1513792) (@lem1513791)). Qed.
Lemma lem1513794 : term151 = term169.
Proof. exact (MK_COMB (@lem1513789) (@lem1513793)). Qed.
Lemma lem1513795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1513796 : term170 = term171.
Proof. exact (MK_COMB (@lem1513795) (@lem1513794)). Qed.
Lemma lem1513797 (x : real) : (term154 x) = (term141 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1513798 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1513799 (x : real) : (term155 x) = (term143 x).
Proof. exact (MK_COMB (@lem1513798) (@lem1513797 x)). Qed.
Lemma lem1513800 (x : real) : (term156 x) = (term146 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1513801 (x : real) : (term157 x) = (term147 x).
Proof. exact (MK_COMB (@lem1513799 x) (@lem1513800 x)). Qed.
Lemma lem1513802 : term158 = term148.
Proof. exact (fun_ext (fun x : real => @lem1513801 x)). Qed.
Lemma lem1513803 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513804 : term150 = term149.
Proof. exact (MK_COMB (@lem1513803) (@lem1513802)). Qed.
Lemma lem1513805 : (term151 = term150) = (term169 = term149).
Proof. exact (MK_COMB (@lem1513796) (@lem1513804)). Qed.
Lemma lem1513806 : term169 = term149.
Proof. exact (EQ_MP (@lem1513805) (@lem1513783)). Qed.
Lemma lem1513808 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1513809 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term104 P Q).
Proof. exact (@lem1513808 real P Q). Qed.
Lemma lem1513810 (x : real) : (term129 x) = (term128 x).
Proof. exact (@lem1513809 (term130 x) (term131 x)). Qed.
Lemma lem1513811 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1513812 (x : real) : (term139 x) = (term130 x).
Proof. exact (fun_ext (fun y : real => @lem1513811 x y)). Qed.
Lemma lem1513813 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513814 (x : real) : (term140 x) = (term141 x).
Proof. exact (MK_COMB (@lem1513813) (@lem1513812 x)). Qed.
Lemma lem1513815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1513816 (x : real) : (term142 x) = (term143 x).
Proof. exact (MK_COMB (@lem1513815) (@lem1513814 x)). Qed.
Lemma lem1513817 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1513818 (x : real) : (term144 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1513817 x y)). Qed.
Lemma lem1513819 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513820 (x : real) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1513819) (@lem1513818 x)). Qed.
Lemma lem1513821 (x : real) : (term129 x) = (term147 x).
Proof. exact (MK_COMB (@lem1513816 x) (@lem1513820 x)). Qed.
Lemma lem1513822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1513823 (x : real) : (term172 x) = (term173 x).
Proof. exact (MK_COMB (@lem1513822) (@lem1513821 x)). Qed.
Lemma lem1513824 (x : real) (y : real) : (term132 x y) = (term119 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1513825 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1513826 (x : real) (y : real) : (term133 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1513825) (@lem1513824 x y)). Qed.
Lemma lem1513827 (x : real) (y : real) : (term134 x y) = (term124 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1513828 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1513826 x y) (@lem1513827 x y)). Qed.
Lemma lem1513829 (x : real) : (term136 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1513828 x y)). Qed.
Lemma lem1513830 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513831 (x : real) : (term128 x) = (term127 x).
Proof. exact (MK_COMB (@lem1513830) (@lem1513829 x)). Qed.
Lemma lem1513832 (x : real) : ((term129 x) = (term128 x)) = ((term147 x) = (term127 x)).
Proof. exact (MK_COMB (@lem1513823 x) (@lem1513831 x)). Qed.
Lemma lem1513833 (x : real) : (term147 x) = (term127 x).
Proof. exact (EQ_MP (@lem1513832 x) (@lem1513810 x)). Qed.
Lemma lem1513835 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1513836 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term104 P Q).
Proof. exact (@lem1513835 real P Q). Qed.
Lemma lem1513837 (x : real) (y : real) : (term107 x y) = (term106 x y).
Proof. exact (@lem1513836 (term108 x y) (term109 x y)). Qed.
Lemma lem1513838 (x : real) (y : real) (z : real) : (term110 x y z) = (term75 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1513839 (x : real) (y : real) : (term117 x y) = (term108 x y).
Proof. exact (fun_ext (fun z : real => @lem1513838 x y z)). Qed.
Lemma lem1513840 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513841 (x : real) (y : real) : (term118 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1513840) (@lem1513839 x y)). Qed.
Lemma lem1513842 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1513843 (x : real) (y : real) : (term120 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem1513842) (@lem1513841 x y)). Qed.
Lemma lem1513844 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1513845 (x : real) (y : real) : (term122 x y) = (term109 x y).
Proof. exact (fun_ext (fun z : real => @lem1513844 x y z)). Qed.
Lemma lem1513846 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513847 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1513846) (@lem1513845 x y)). Qed.
Lemma lem1513848 (x : real) (y : real) : (term107 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1513843 x y) (@lem1513847 x y)). Qed.
Lemma lem1513849 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1513850 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (MK_COMB (@lem1513849) (@lem1513848 x y)). Qed.
Lemma lem1513851 (x : real) (y : real) (z : real) : (term110 x y z) = (term75 x y z).
Proof. exact (eq_refl (term110 x y z)). Qed.
Lemma lem1513852 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1513853 (x : real) (y : real) (z : real) : (term111 x y z) = (term94 x y z).
Proof. exact (MK_COMB (@lem1513852) (@lem1513851 x y z)). Qed.
Lemma lem1513854 (x : real) (y : real) (z : real) : (term112 x y z) = (term92 x y z).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem1513855 (x : real) (y : real) (z : real) : (term113 x y z) = (term95 x y z).
Proof. exact (MK_COMB (@lem1513853 x y z) (@lem1513854 x y z)). Qed.
Lemma lem1513856 (x : real) (y : real) : (term114 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1513855 x y z)). Qed.
Lemma lem1513857 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513858 (x : real) (y : real) : (term106 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1513857) (@lem1513856 x y)). Qed.
Lemma lem1513859 (x : real) (y : real) : ((term107 x y) = (term106 x y)) = ((term125 x y) = (term97 x y)).
Proof. exact (MK_COMB (@lem1513850 x y) (@lem1513858 x y)). Qed.
Lemma lem1513860 (x : real) (y : real) : (term125 x y) = (term97 x y).
Proof. exact (EQ_MP (@lem1513859 x y) (@lem1513837 x y)). Qed.
Lemma lem1513861 (x : real) : (term126 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1513860 x y)). Qed.
Lemma lem1513862 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513863 (x : real) : (term127 x) = (term99 x).
Proof. exact (MK_COMB (@lem1513862) (@lem1513861 x)). Qed.
Lemma lem1513864 (x : real) : (term147 x) = (term99 x).
Proof. exact (TRANS (@lem1513833 x) (@lem1513863 x)). Qed.
Lemma lem1513865 : term148 = term100.
Proof. exact (fun_ext (fun x : real => @lem1513864 x)). Qed.
Lemma lem1513866 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513867 : term149 = term101.
Proof. exact (MK_COMB (@lem1513866) (@lem1513865)). Qed.
Lemma lem1513868 : term169 = term101.
Proof. exact (TRANS (@lem1513806) (@lem1513867)). Qed.
Lemma lem1513869 : term101 = term101.
Proof. exact (TRANS (@lem1513779) (@lem1513868)). Qed.
Lemma lem1513872 : term23 = term101.
Proof. exact (TRANS (@lem1513370) (@lem1513869)). Qed.
Lemma lem1513889 (x : real) (y : real) (z : real) : (term95 x y z) = (term95 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1513890 (x : real) (y : real) : (term96 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1513889 x y z)). Qed.
Lemma lem1513891 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513892 (x : real) (y : real) : (term97 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1513891) (@lem1513890 x y)). Qed.
Lemma lem1513893 (x : real) : (term98 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1513892 x y)). Qed.
Lemma lem1513894 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513895 (x : real) : (term99 x) = (term99 x).
Proof. exact (MK_COMB (@lem1513894) (@lem1513893 x)). Qed.
Lemma lem1513896 : term100 = term100.
Proof. exact (fun_ext (fun x : real => @lem1513895 x)). Qed.
Lemma lem1513897 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1513898 : term101 = term101.
Proof. exact (MK_COMB (@lem1513897) (@lem1513896)). Qed.
Lemma lem1513899 : term23 = term101.
Proof. exact (TRANS (@lem1513872) (@lem1513898)). Qed.
Lemma lem1513909 (x : real) (y : real) (z : real) (h1 : term95 x y z) : term95 x y z.
Proof. exact (h1). Qed.
Lemma lem1513910 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term75 x y z.
Proof. exact (h1). Qed.
Lemma lem1513911 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term71 x y z.
Proof. exact (proj2 (@lem1513910 x y z h1)). Qed.
Lemma lem1513912 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term61 x y z.
Proof. exact (proj1 (@lem1513910 x y z h1)). Qed.
Lemma lem1513914 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1513915 : term177 = term178.
Proof. exact (@lem1513914 (NUMERAL 0) term47). Qed.
Lemma lem1513916 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1513917 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1513918 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1513917 h1) (fun h1 : term178 = True => @lem1513916)). Qed.
Lemma lem1513919 : term178 = True.
Proof. exact (EQ_MP (@lem1513918) (@lem1513916)). Qed.
Lemma lem1513920 : term177 = True.
Proof. exact (TRANS (@lem1513915) (@lem1513919)). Qed.
Lemma lem1513921 : True = term177.
Proof. exact (SYM (@lem1513920)). Qed.
Lemma lem1513922 : term177.
Proof. exact (EQ_MP (@lem1513921) (@lem0)). Qed.
Lemma lem1513923 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term180 x y z.
Proof. exact (conj (@lem1513922) (@lem1513911 x y z h1)). Qed.
Lemma lem1513925 (x : real) (y : real) : term181 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1513926 (x : real) (y : real) (z : real) : term182 x y z.
Proof. exact (@lem1513925 term50 (term68 x y z)). Qed.
Lemma lem1513927 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term183 x y z.
Proof. exact (@lem1513926 x y z (@lem1513923 x y z h1)). Qed.
Lemma lem1513928 (x : real) (y : real) (z : real) : (term184 x y z) = (term68 x y z).
Proof. exact (@lem1483460 (term68 x y z)). Qed.
Lemma lem1513929 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1513930 (x : real) (y : real) (z : real) : (term185 x y z) = (term70 x y z).
Proof. exact (MK_COMB (@lem1513929) (@lem1513928 x y z)). Qed.
Lemma lem1513931 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1513932 (x : real) (y : real) (z : real) : (term183 x y z) = (term71 x y z).
Proof. exact (MK_COMB (@lem1513930 x y z) (@lem1513931)). Qed.
Lemma lem1513933 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term71 x y z.
Proof. exact (EQ_MP (@lem1513932 x y z) (@lem1513927 x y z h1)). Qed.
Lemma lem1513935 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1513936 : term177 = term178.
Proof. exact (@lem1513935 (NUMERAL 0) term47). Qed.
Lemma lem1513937 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1513938 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1513939 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1513938 h1) (fun h1 : term178 = True => @lem1513937)). Qed.
Lemma lem1513940 : term178 = True.
Proof. exact (EQ_MP (@lem1513939) (@lem1513937)). Qed.
Lemma lem1513941 : term177 = True.
Proof. exact (TRANS (@lem1513936) (@lem1513940)). Qed.
Lemma lem1513942 : True = term177.
Proof. exact (SYM (@lem1513941)). Qed.
Lemma lem1513943 : term177.
Proof. exact (EQ_MP (@lem1513942) (@lem0)). Qed.
Lemma lem1513944 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term186 x y z.
Proof. exact (conj (@lem1513943) (@lem1513912 x y z h1)). Qed.
Lemma lem1513946 (x : real) (y : real) : term187 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1513947 (x : real) (y : real) (z : real) : term188 x y z.
Proof. exact (@lem1513946 term50 (term57 x y z)). Qed.
Lemma lem1513948 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term189 x y z.
Proof. exact (@lem1513947 x y z (@lem1513944 x y z h1)). Qed.
Lemma lem1513949 (x : real) (y : real) (z : real) : (term190 x y z) = (term57 x y z).
Proof. exact (@lem1483460 (term57 x y z)). Qed.
Lemma lem1513950 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1513951 (x : real) (y : real) (z : real) : (term191 x y z) = (term59 x y z).
Proof. exact (MK_COMB (@lem1513950) (@lem1513949 x y z)). Qed.
Lemma lem1513952 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1513953 (x : real) (y : real) (z : real) : (term189 x y z) = (term61 x y z).
Proof. exact (MK_COMB (@lem1513951 x y z) (@lem1513952)). Qed.
Lemma lem1513954 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term61 x y z.
Proof. exact (EQ_MP (@lem1513953 x y z) (@lem1513948 x y z h1)). Qed.
Lemma lem1513955 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term75 x y z.
Proof. exact (conj (@lem1513954 x y z h1) (@lem1513933 x y z h1)). Qed.
Lemma lem1513957 (x : real) (y : real) : term192 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1513958 (x : real) (y : real) (z : real) : term193 x y z.
Proof. exact (@lem1513957 (term57 x y z) (term68 x y z)). Qed.
Lemma lem1513959 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term194 x y z.
Proof. exact (@lem1513958 x y z (@lem1513955 x y z h1)). Qed.
Lemma lem1513960 (x : real) (y : real) (z : real) : (term195 x y z) = (term196 x y z).
Proof. exact (@lem1483480 (term40 x) x (real_add y z) (term67 y z)). Qed.
Lemma lem1513961 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483440 term39 x). Qed.
Lemma lem1513963 (m : nat) : (term199 m) = term60.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1513964 : term200 = term60.
Proof. exact (@lem1513963 term47). Qed.
Lemma lem1513965 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1513966 : term201 = term202.
Proof. exact (MK_COMB (@lem1513965) (@lem1513964)). Qed.
Lemma lem1513967 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1513968 (x : real) : (term198 x) = (term203 x).
Proof. exact (MK_COMB (@lem1513966) (@lem1513967 x)). Qed.
Lemma lem1513969 (x : real) : (term197 x) = (term203 x).
Proof. exact (TRANS (@lem1513961 x) (@lem1513968 x)). Qed.
Lemma lem1513970 (x : real) : (term203 x) = term60.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1513971 (x : real) : (term197 x) = term60.
Proof. exact (TRANS (@lem1513969 x) (@lem1513970 x)). Qed.
Lemma lem1513972 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1513973 (x : real) : (term204 x) = term205.
Proof. exact (MK_COMB (@lem1513972) (@lem1513971 x)). Qed.
Lemma lem1513974 (y : real) (z : real) : (term206 y z) = (term207 y z).
Proof. exact (@lem1483480 y (term40 y) z (term40 z)). Qed.
Lemma lem1513975 (y : real) : (term208 y) = (term198 y).
Proof. exact (@lem1483442 term39 y). Qed.
Lemma lem1513977 (m : nat) : (term199 m) = term60.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1513978 : term200 = term60.
Proof. exact (@lem1513977 term47). Qed.
Lemma lem1513979 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1513980 : term201 = term202.
Proof. exact (MK_COMB (@lem1513979) (@lem1513978)). Qed.
Lemma lem1513981 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1513982 (y : real) : (term198 y) = (term203 y).
Proof. exact (MK_COMB (@lem1513980) (@lem1513981 y)). Qed.
Lemma lem1513983 (y : real) : (term208 y) = (term203 y).
Proof. exact (TRANS (@lem1513975 y) (@lem1513982 y)). Qed.
Lemma lem1513984 (y : real) : (term203 y) = term60.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1513985 (y : real) : (term208 y) = term60.
Proof. exact (TRANS (@lem1513983 y) (@lem1513984 y)). Qed.
Lemma lem1513986 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1513987 (y : real) : (term209 y) = term205.
Proof. exact (MK_COMB (@lem1513986) (@lem1513985 y)). Qed.
Lemma lem1513988 (z : real) : (term208 z) = (term198 z).
Proof. exact (@lem1483442 term39 z). Qed.
Lemma lem1513990 (m : nat) : (term199 m) = term60.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1513991 : term200 = term60.
Proof. exact (@lem1513990 term47). Qed.
Lemma lem1513992 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1513993 : term201 = term202.
Proof. exact (MK_COMB (@lem1513992) (@lem1513991)). Qed.
Lemma lem1513994 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1513995 (z : real) : (term198 z) = (term203 z).
Proof. exact (MK_COMB (@lem1513993) (@lem1513994 z)). Qed.
Lemma lem1513996 (z : real) : (term208 z) = (term203 z).
Proof. exact (TRANS (@lem1513988 z) (@lem1513995 z)). Qed.
Lemma lem1513997 (z : real) : (term203 z) = term60.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1513998 (z : real) : (term208 z) = term60.
Proof. exact (TRANS (@lem1513996 z) (@lem1513997 z)). Qed.
Lemma lem1513999 (y : real) (z : real) : (term207 y z) = term210.
Proof. exact (MK_COMB (@lem1513987 y) (@lem1513998 z)). Qed.
Lemma lem1514000 (y : real) (z : real) : (term206 y z) = term210.
Proof. exact (TRANS (@lem1513974 y z) (@lem1513999 y z)). Qed.
Lemma lem1514001 : term210 = term60.
Proof. exact (@lem1483448 term60). Qed.
Lemma lem1514002 (y : real) (z : real) : (term206 y z) = term60.
Proof. exact (TRANS (@lem1514000 y z) (@lem1514001)). Qed.
Lemma lem1514003 (x : real) (y : real) (z : real) : (term196 x y z) = term210.
Proof. exact (MK_COMB (@lem1513973 x) (@lem1514002 y z)). Qed.
Lemma lem1514004 (x : real) (y : real) (z : real) : (term195 x y z) = term210.
Proof. exact (TRANS (@lem1513960 x y z) (@lem1514003 x y z)). Qed.
Lemma lem1514005 : term210 = term60.
Proof. exact (@lem1483448 term60). Qed.
Lemma lem1514006 (x : real) (y : real) (z : real) : (term195 x y z) = term60.
Proof. exact (TRANS (@lem1514004 x y z) (@lem1514005)). Qed.
Lemma lem1514007 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1514008 (x : real) (y : real) (z : real) : (term211 x y z) = term212.
Proof. exact (MK_COMB (@lem1514007) (@lem1514006 x y z)). Qed.
Lemma lem1514009 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1514010 (x : real) (y : real) (z : real) : (term194 x y z) = term213.
Proof. exact (MK_COMB (@lem1514008 x y z) (@lem1514009)). Qed.
Lemma lem1514011 (x : real) (y : real) (z : real) (h1 : term75 x y z) : term213.
Proof. exact (EQ_MP (@lem1514010 x y z) (@lem1513959 x y z h1)). Qed.
Lemma lem1514013 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1514014 : term213 = term214.
Proof. exact (@lem1514013 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1514015 : term214 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1514016 : term213 = False.
Proof. exact (TRANS (@lem1514014) (@lem1514015)). Qed.
Lemma lem1514017 (x : real) (y : real) (z : real) (h1 : term75 x y z) : False.
Proof. exact (EQ_MP (@lem1514016) (@lem1514011 x y z h1)). Qed.
Lemma lem1514018 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term92 x y z.
Proof. exact (h1). Qed.
Lemma lem1514019 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term61 x y z.
Proof. exact (proj2 (@lem1514018 x y z h1)). Qed.
Lemma lem1514020 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term71 x y z.
Proof. exact (proj1 (@lem1514018 x y z h1)). Qed.
Lemma lem1514022 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1514023 : term177 = term178.
Proof. exact (@lem1514022 (NUMERAL 0) term47). Qed.
Lemma lem1514024 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1514025 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1514026 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1514025 h1) (fun h1 : term178 = True => @lem1514024)). Qed.
Lemma lem1514027 : term178 = True.
Proof. exact (EQ_MP (@lem1514026) (@lem1514024)). Qed.
Lemma lem1514028 : term177 = True.
Proof. exact (TRANS (@lem1514023) (@lem1514027)). Qed.
Lemma lem1514029 : True = term177.
Proof. exact (SYM (@lem1514028)). Qed.
Lemma lem1514030 : term177.
Proof. exact (EQ_MP (@lem1514029) (@lem0)). Qed.
Lemma lem1514031 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term180 x y z.
Proof. exact (conj (@lem1514030) (@lem1514020 x y z h1)). Qed.
Lemma lem1514033 (x : real) (y : real) : term181 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1514034 (x : real) (y : real) (z : real) : term182 x y z.
Proof. exact (@lem1514033 term50 (term68 x y z)). Qed.
Lemma lem1514035 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term183 x y z.
Proof. exact (@lem1514034 x y z (@lem1514031 x y z h1)). Qed.
Lemma lem1514036 (x : real) (y : real) (z : real) : (term184 x y z) = (term68 x y z).
Proof. exact (@lem1483460 (term68 x y z)). Qed.
Lemma lem1514037 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1514038 (x : real) (y : real) (z : real) : (term185 x y z) = (term70 x y z).
Proof. exact (MK_COMB (@lem1514037) (@lem1514036 x y z)). Qed.
Lemma lem1514039 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1514040 (x : real) (y : real) (z : real) : (term183 x y z) = (term71 x y z).
Proof. exact (MK_COMB (@lem1514038 x y z) (@lem1514039)). Qed.
Lemma lem1514041 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term71 x y z.
Proof. exact (EQ_MP (@lem1514040 x y z) (@lem1514035 x y z h1)). Qed.
Lemma lem1514043 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1514044 : term177 = term178.
Proof. exact (@lem1514043 (NUMERAL 0) term47). Qed.
Lemma lem1514045 : term179 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1514046 (h1 : term179 = (BIT1 0)) : term178 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1514047 : (term179 = (BIT1 0)) = (term178 = True).
Proof. exact (prop_ext (fun h1 : term179 = (BIT1 0) => @lem1514046 h1) (fun h1 : term178 = True => @lem1514045)). Qed.
Lemma lem1514048 : term178 = True.
Proof. exact (EQ_MP (@lem1514047) (@lem1514045)). Qed.
Lemma lem1514049 : term177 = True.
Proof. exact (TRANS (@lem1514044) (@lem1514048)). Qed.
Lemma lem1514050 : True = term177.
Proof. exact (SYM (@lem1514049)). Qed.
Lemma lem1514051 : term177.
Proof. exact (EQ_MP (@lem1514050) (@lem0)). Qed.
Lemma lem1514052 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term186 x y z.
Proof. exact (conj (@lem1514051) (@lem1514019 x y z h1)). Qed.
Lemma lem1514054 (x : real) (y : real) : term187 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1514055 (x : real) (y : real) (z : real) : term188 x y z.
Proof. exact (@lem1514054 term50 (term57 x y z)). Qed.
Lemma lem1514056 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term189 x y z.
Proof. exact (@lem1514055 x y z (@lem1514052 x y z h1)). Qed.
Lemma lem1514057 (x : real) (y : real) (z : real) : (term190 x y z) = (term57 x y z).
Proof. exact (@lem1483460 (term57 x y z)). Qed.
Lemma lem1514058 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1514059 (x : real) (y : real) (z : real) : (term191 x y z) = (term59 x y z).
Proof. exact (MK_COMB (@lem1514058) (@lem1514057 x y z)). Qed.
Lemma lem1514060 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1514061 (x : real) (y : real) (z : real) : (term189 x y z) = (term61 x y z).
Proof. exact (MK_COMB (@lem1514059 x y z) (@lem1514060)). Qed.
Lemma lem1514062 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term61 x y z.
Proof. exact (EQ_MP (@lem1514061 x y z) (@lem1514056 x y z h1)). Qed.
Lemma lem1514063 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term75 x y z.
Proof. exact (conj (@lem1514062 x y z h1) (@lem1514041 x y z h1)). Qed.
Lemma lem1514065 (x : real) (y : real) : term192 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1514066 (x : real) (y : real) (z : real) : term193 x y z.
Proof. exact (@lem1514065 (term57 x y z) (term68 x y z)). Qed.
Lemma lem1514067 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term194 x y z.
Proof. exact (@lem1514066 x y z (@lem1514063 x y z h1)). Qed.
Lemma lem1514068 (x : real) (y : real) (z : real) : (term195 x y z) = (term196 x y z).
Proof. exact (@lem1483480 (term40 x) x (real_add y z) (term67 y z)). Qed.
Lemma lem1514069 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483440 term39 x). Qed.
Lemma lem1514071 (m : nat) : (term199 m) = term60.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1514072 : term200 = term60.
Proof. exact (@lem1514071 term47). Qed.
Lemma lem1514073 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1514074 : term201 = term202.
Proof. exact (MK_COMB (@lem1514073) (@lem1514072)). Qed.
Lemma lem1514075 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1514076 (x : real) : (term198 x) = (term203 x).
Proof. exact (MK_COMB (@lem1514074) (@lem1514075 x)). Qed.
Lemma lem1514077 (x : real) : (term197 x) = (term203 x).
Proof. exact (TRANS (@lem1514069 x) (@lem1514076 x)). Qed.
Lemma lem1514078 (x : real) : (term203 x) = term60.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1514079 (x : real) : (term197 x) = term60.
Proof. exact (TRANS (@lem1514077 x) (@lem1514078 x)). Qed.
Lemma lem1514080 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1514081 (x : real) : (term204 x) = term205.
Proof. exact (MK_COMB (@lem1514080) (@lem1514079 x)). Qed.
Lemma lem1514082 (y : real) (z : real) : (term206 y z) = (term207 y z).
Proof. exact (@lem1483480 y (term40 y) z (term40 z)). Qed.
Lemma lem1514083 (y : real) : (term208 y) = (term198 y).
Proof. exact (@lem1483442 term39 y). Qed.
Lemma lem1514085 (m : nat) : (term199 m) = term60.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1514086 : term200 = term60.
Proof. exact (@lem1514085 term47). Qed.
Lemma lem1514087 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1514088 : term201 = term202.
Proof. exact (MK_COMB (@lem1514087) (@lem1514086)). Qed.
Lemma lem1514089 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1514090 (y : real) : (term198 y) = (term203 y).
Proof. exact (MK_COMB (@lem1514088) (@lem1514089 y)). Qed.
Lemma lem1514091 (y : real) : (term208 y) = (term203 y).
Proof. exact (TRANS (@lem1514083 y) (@lem1514090 y)). Qed.
Lemma lem1514092 (y : real) : (term203 y) = term60.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1514093 (y : real) : (term208 y) = term60.
Proof. exact (TRANS (@lem1514091 y) (@lem1514092 y)). Qed.
Lemma lem1514094 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1514095 (y : real) : (term209 y) = term205.
Proof. exact (MK_COMB (@lem1514094) (@lem1514093 y)). Qed.
Lemma lem1514096 (z : real) : (term208 z) = (term198 z).
Proof. exact (@lem1483442 term39 z). Qed.
Lemma lem1514098 (m : nat) : (term199 m) = term60.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1514099 : term200 = term60.
Proof. exact (@lem1514098 term47). Qed.
Lemma lem1514100 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1514101 : term201 = term202.
Proof. exact (MK_COMB (@lem1514100) (@lem1514099)). Qed.
Lemma lem1514102 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1514103 (z : real) : (term198 z) = (term203 z).
Proof. exact (MK_COMB (@lem1514101) (@lem1514102 z)). Qed.
Lemma lem1514104 (z : real) : (term208 z) = (term203 z).
Proof. exact (TRANS (@lem1514096 z) (@lem1514103 z)). Qed.
Lemma lem1514105 (z : real) : (term203 z) = term60.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1514106 (z : real) : (term208 z) = term60.
Proof. exact (TRANS (@lem1514104 z) (@lem1514105 z)). Qed.
Lemma lem1514107 (y : real) (z : real) : (term207 y z) = term210.
Proof. exact (MK_COMB (@lem1514095 y) (@lem1514106 z)). Qed.
Lemma lem1514108 (y : real) (z : real) : (term206 y z) = term210.
Proof. exact (TRANS (@lem1514082 y z) (@lem1514107 y z)). Qed.
Lemma lem1514109 : term210 = term60.
Proof. exact (@lem1483448 term60). Qed.
Lemma lem1514110 (y : real) (z : real) : (term206 y z) = term60.
Proof. exact (TRANS (@lem1514108 y z) (@lem1514109)). Qed.
Lemma lem1514111 (x : real) (y : real) (z : real) : (term196 x y z) = term210.
Proof. exact (MK_COMB (@lem1514081 x) (@lem1514110 y z)). Qed.
Lemma lem1514112 (x : real) (y : real) (z : real) : (term195 x y z) = term210.
Proof. exact (TRANS (@lem1514068 x y z) (@lem1514111 x y z)). Qed.
Lemma lem1514113 : term210 = term60.
Proof. exact (@lem1483448 term60). Qed.
Lemma lem1514114 (x : real) (y : real) (z : real) : (term195 x y z) = term60.
Proof. exact (TRANS (@lem1514112 x y z) (@lem1514113)). Qed.
Lemma lem1514115 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1514116 (x : real) (y : real) (z : real) : (term211 x y z) = term212.
Proof. exact (MK_COMB (@lem1514115) (@lem1514114 x y z)). Qed.
Lemma lem1514117 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1514118 (x : real) (y : real) (z : real) : (term194 x y z) = term213.
Proof. exact (MK_COMB (@lem1514116 x y z) (@lem1514117)). Qed.
Lemma lem1514119 (x : real) (y : real) (z : real) (h1 : term92 x y z) : term213.
Proof. exact (EQ_MP (@lem1514118 x y z) (@lem1514067 x y z h1)). Qed.
Lemma lem1514121 (n : nat) (m : nat) : (term176 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1514122 : term213 = term214.
Proof. exact (@lem1514121 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1514123 : term214 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1514124 : term213 = False.
Proof. exact (TRANS (@lem1514122) (@lem1514123)). Qed.
Lemma lem1514125 (x : real) (y : real) (z : real) (h1 : term92 x y z) : False.
Proof. exact (EQ_MP (@lem1514124) (@lem1514119 x y z h1)). Qed.
Lemma lem1514126 (x : real) (y : real) (z : real) (h1 : term95 x y z) : False.
Proof. exact (or_elim (@lem1513909 x y z h1) (fun h0 : term75 x y z => @lem1514017 x y z h0) (fun h0 : term92 x y z => @lem1514125 x y z h0)). Qed.
Lemma lem1514128 (x : real) (y : real) (z : real) (h1 : term95 x y z) : term95 x y z.
Proof. exact (h1). Qed.
Lemma lem1514129 (x : real) (y : real) (z : real) (h1 : term95 x y z) : (term95 x y z) = False.
Proof. exact (prop_ext (fun h2 : term95 x y z => @lem1514126 x y z h1) (fun h2 : False => @lem1514128 x y z h1)). Qed.
Lemma lem1514130 (x : real) (y : real) (z : real) (h1 : term95 x y z) : False.
Proof. exact (EQ_MP (@lem1514129 x y z h1) (@lem1514128 x y z h1)). Qed.
Lemma lem1514131 (x : real) (y : real) (h1 : term97 x y) : term97 x y.
Proof. exact (h1). Qed.
Lemma lem1514132 (x : real) (y : real) (h1 : term97 x y) : False.
Proof. exact (ex_elim (@lem1514131 x y h1) (fun z : real => fun h0 : term96 x y z => @lem1514130 x y z h0)). Qed.
Lemma lem1514133 (x : real) (h1 : term99 x) : term99 x.
Proof. exact (h1). Qed.
Lemma lem1514134 (x : real) (h1 : term99 x) : False.
Proof. exact (ex_elim (@lem1514133 x h1) (fun y : real => fun h0 : term98 x y => @lem1514132 x y h0)). Qed.
Lemma lem1514135 (h1 : term101) : term101.
Proof. exact (h1). Qed.
Lemma lem1514136 (h1 : term101) : False.
Proof. exact (ex_elim (@lem1514135 h1) (fun x : real => fun h0 : term100 x => @lem1514134 x h0)). Qed.
Lemma lem1514137 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem1514138 (h1 : term23) : term101.
Proof. exact (EQ_MP (@lem1513899) (@lem1514137 h1)). Qed.
Lemma lem1514139 (h1 : term23) : term101 = False.
Proof. exact (prop_ext (fun h2 : term101 => @lem1514136 h2) (fun h2 : False => @lem1514138 h1)). Qed.
Lemma lem1514140 (h1 : term23) : False.
Proof. exact (EQ_MP (@lem1514139 h1) (@lem1514138 h1)). Qed.
Lemma lem1514141 : term215.
Proof. exact (fun h0 : term23 => @lem1514140 h0). Qed.
Lemma lem1514142 : term216.
Proof. exact (@lem1386578 term217). Qed.
Lemma lem1514143 : term217.
Proof. exact (@lem1514142 (@lem1514141)). Qed.
