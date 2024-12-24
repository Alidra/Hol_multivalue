Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_ADD2_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483490_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm912739_spec.
Lemma lem1501153 (w : real) (y : real) (x : real) (z : real) : (term0 w y x z) = (term1 w y x z).
Proof. exact (@lem17362 (term2 w x y z) (term3 w y x z)). Qed.
Lemma lem1501154 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1501155 (w : real) (y : real) (x : real) : (term6 w y x) = (term7 w y x).
Proof. exact (@lem1501154 (term8 w y x)). Qed.
Lemma lem1501156 (w : real) (y : real) (x : real) (z : real) : (term9 w y x z) = (term10 w y x z).
Proof. exact (eq_refl (term9 w y x z)). Qed.
Lemma lem1501157 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1501158 (w : real) (y : real) (x : real) (z : real) : (term11 w y x z) = (term0 w y x z).
Proof. exact (MK_COMB (@lem1501157) (@lem1501156 w y x z)). Qed.
Lemma lem1501159 (w : real) (y : real) (x : real) (z : real) : (term11 w y x z) = (term1 w y x z).
Proof. exact (TRANS (@lem1501158 w y x z) (@lem1501153 w y x z)). Qed.
Lemma lem1501160 (w : real) (y : real) (x : real) : (term12 w y x) = (term13 w y x).
Proof. exact (fun_ext (fun z : real => @lem1501159 w y x z)). Qed.
Lemma lem1501161 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501162 (w : real) (y : real) (x : real) : (term7 w y x) = (term14 w y x).
Proof. exact (MK_COMB (@lem1501161) (@lem1501160 w y x)). Qed.
Lemma lem1501163 (w : real) (y : real) (x : real) : (term6 w y x) = (term14 w y x).
Proof. exact (TRANS (@lem1501155 w y x) (@lem1501162 w y x)). Qed.
Lemma lem1501164 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1501165 (w : real) (x : real) : (term15 w x) = (term16 w x).
Proof. exact (@lem1501164 (term17 w x)). Qed.
Lemma lem1501166 (w : real) (y : real) (x : real) : (term18 w x y) = (term19 w y x).
Proof. exact (eq_refl (term18 w x y)). Qed.
Lemma lem1501167 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1501168 (w : real) (y : real) (x : real) : (term20 w x y) = (term6 w y x).
Proof. exact (MK_COMB (@lem1501167) (@lem1501166 w y x)). Qed.
Lemma lem1501169 (w : real) (y : real) (x : real) : (term20 w x y) = (term14 w y x).
Proof. exact (TRANS (@lem1501168 w y x) (@lem1501163 w y x)). Qed.
Lemma lem1501170 (w : real) (x : real) : (term21 w x) = (term22 w x).
Proof. exact (fun_ext (fun y : real => @lem1501169 w y x)). Qed.
Lemma lem1501171 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501172 (w : real) (x : real) : (term16 w x) = (term23 w x).
Proof. exact (MK_COMB (@lem1501171) (@lem1501170 w x)). Qed.
Lemma lem1501173 (w : real) (x : real) : (term15 w x) = (term23 w x).
Proof. exact (TRANS (@lem1501165 w x) (@lem1501172 w x)). Qed.
Lemma lem1501174 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1501175 (w : real) : (term24 w) = (term25 w).
Proof. exact (@lem1501174 (term26 w)). Qed.
Lemma lem1501176 (w : real) (x : real) : (term27 w x) = (term28 w x).
Proof. exact (eq_refl (term27 w x)). Qed.
Lemma lem1501177 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1501178 (w : real) (x : real) : (term29 w x) = (term15 w x).
Proof. exact (MK_COMB (@lem1501177) (@lem1501176 w x)). Qed.
Lemma lem1501179 (w : real) (x : real) : (term29 w x) = (term23 w x).
Proof. exact (TRANS (@lem1501178 w x) (@lem1501173 w x)). Qed.
Lemma lem1501180 (w : real) : (term30 w) = (term31 w).
Proof. exact (fun_ext (fun x : real => @lem1501179 w x)). Qed.
Lemma lem1501181 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501182 (w : real) : (term25 w) = (term32 w).
Proof. exact (MK_COMB (@lem1501181) (@lem1501180 w)). Qed.
Lemma lem1501183 (w : real) : (term24 w) = (term32 w).
Proof. exact (TRANS (@lem1501175 w) (@lem1501182 w)). Qed.
Lemma lem1501184 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1501185 : term33 = term34.
Proof. exact (@lem1501184 term35). Qed.
Lemma lem1501186 (w : real) : (term36 w) = (term37 w).
Proof. exact (eq_refl (term36 w)). Qed.
Lemma lem1501187 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1501188 (w : real) : (term38 w) = (term24 w).
Proof. exact (MK_COMB (@lem1501187) (@lem1501186 w)). Qed.
Lemma lem1501189 (w : real) : (term38 w) = (term32 w).
Proof. exact (TRANS (@lem1501188 w) (@lem1501183 w)). Qed.
Lemma lem1501190 : term39 = term40.
Proof. exact (fun_ext (fun w : real => @lem1501189 w)). Qed.
Lemma lem1501191 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501192 : term34 = term41.
Proof. exact (MK_COMB (@lem1501191) (@lem1501190)). Qed.
Lemma lem1501194 : term33 = term41.
Proof. exact (TRANS (@lem1501185) (@lem1501192)). Qed.
Lemma lem1501205 (w : real) (y : real) (x : real) (z : real) : (term1 w y x z) = (term1 w y x z).
Proof. exact (eq_refl (term1 w y x z)). Qed.
Lemma lem1501206 (w : real) (y : real) (x : real) : (term13 w y x) = (term13 w y x).
Proof. exact (fun_ext (fun z : real => @lem1501205 w y x z)). Qed.
Lemma lem1501207 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501208 (w : real) (y : real) (x : real) : (term14 w y x) = (term14 w y x).
Proof. exact (MK_COMB (@lem1501207) (@lem1501206 w y x)). Qed.
Lemma lem1501209 (w : real) (x : real) : (term22 w x) = (term22 w x).
Proof. exact (fun_ext (fun y : real => @lem1501208 w y x)). Qed.
Lemma lem1501210 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501211 (w : real) (x : real) : (term23 w x) = (term23 w x).
Proof. exact (MK_COMB (@lem1501210) (@lem1501209 w x)). Qed.
Lemma lem1501212 (w : real) : (term31 w) = (term31 w).
Proof. exact (fun_ext (fun x : real => @lem1501211 w x)). Qed.
Lemma lem1501213 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501214 (w : real) : (term32 w) = (term32 w).
Proof. exact (MK_COMB (@lem1501213) (@lem1501212 w)). Qed.
Lemma lem1501215 : term40 = term40.
Proof. exact (fun_ext (fun w : real => @lem1501214 w)). Qed.
Lemma lem1501216 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501217 : term41 = term41.
Proof. exact (MK_COMB (@lem1501216) (@lem1501215)). Qed.
Lemma lem1501218 : term33 = term41.
Proof. exact (TRANS (@lem1501194) (@lem1501217)). Qed.
Lemma lem1501219 (x : real) (w : real) : (real_lt w x) = (term42 x w).
Proof. exact (@lem1483521 x w). Qed.
Lemma lem1501225 (x : real) (w : real) : (real_sub x w) = (term43 x w).
Proof. exact (@lem1483519 x w). Qed.
Lemma lem1501230 (w : real) (x : real) : (term43 x w) = (term44 w x).
Proof. exact (@lem1483488 (term45 w) x). Qed.
Lemma lem1501232 (w : real) (x : real) : (real_sub x w) = (term44 w x).
Proof. exact (TRANS (@lem1501225 x w) (@lem1501230 w x)). Qed.
Lemma lem1501233 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1501234 (w : real) (x : real) : (term46 x w) = (term47 w x).
Proof. exact (MK_COMB (@lem1501233) (@lem1501232 w x)). Qed.
Lemma lem1501235 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1501236 (w : real) (x : real) : (term42 x w) = (term49 w x).
Proof. exact (MK_COMB (@lem1501234 w x) (@lem1501235)). Qed.
Lemma lem1501237 (w : real) (x : real) : (real_lt w x) = (term49 w x).
Proof. exact (TRANS (@lem1501219 x w) (@lem1501236 w x)). Qed.
Lemma lem1501238 (z : real) (y : real) : (real_lt y z) = (term42 z y).
Proof. exact (@lem1483521 z y). Qed.
Lemma lem1501244 (z : real) (y : real) : (real_sub z y) = (term43 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1501249 (y : real) (z : real) : (term43 z y) = (term44 y z).
Proof. exact (@lem1483488 (term45 y) z). Qed.
Lemma lem1501251 (y : real) (z : real) : (real_sub z y) = (term44 y z).
Proof. exact (TRANS (@lem1501244 z y) (@lem1501249 y z)). Qed.
Lemma lem1501252 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1501253 (y : real) (z : real) : (term46 z y) = (term47 y z).
Proof. exact (MK_COMB (@lem1501252) (@lem1501251 y z)). Qed.
Lemma lem1501254 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1501255 (y : real) (z : real) : (term42 z y) = (term49 y z).
Proof. exact (MK_COMB (@lem1501253 y z) (@lem1501254)). Qed.
Lemma lem1501256 (y : real) (z : real) : (real_lt y z) = (term49 y z).
Proof. exact (TRANS (@lem1501238 z y) (@lem1501255 y z)). Qed.
Lemma lem1501257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1501258 (w : real) (x : real) : (term50 w x) = (term51 w x).
Proof. exact (MK_COMB (@lem1501257) (@lem1501237 w x)). Qed.
Lemma lem1501259 (w : real) (x : real) (y : real) (z : real) : (term2 w x y z) = (term52 w x y z).
Proof. exact (MK_COMB (@lem1501258 w x) (@lem1501256 y z)). Qed.
Lemma lem1501260 (w : real) (y : real) (x : real) (z : real) : (term53 w y x z) = (term54 w y x z).
Proof. exact (@lem1483531 (real_add w y) (real_add x z)). Qed.
Lemma lem1501278 (w : real) (y : real) (x : real) (z : real) : (term55 w y x z) = (term56 w y x z).
Proof. exact (@lem1483519 (real_add w y) (real_add x z)). Qed.
Lemma lem1501285 (x : real) (z : real) : (term57 x z) = (term58 x z).
Proof. exact (@lem1483508 x term59 z). Qed.
Lemma lem1501286 (w : real) (y : real) : (term60 w y) = (term60 w y).
Proof. exact (eq_refl (term60 w y)). Qed.
Lemma lem1501287 (w : real) (y : real) (x : real) (z : real) : (term56 w y x z) = (term61 w y x z).
Proof. exact (MK_COMB (@lem1501286 w y) (@lem1501285 x z)). Qed.
Lemma lem1501288 (w : real) (y : real) (x : real) (z : real) : (term61 w y x z) = (term62 w y x z).
Proof. exact (@lem1483482 w y (term58 x z)). Qed.
Lemma lem1501293 (x : real) (y : real) (z : real) : (term63 y x z) = (term64 x y z).
Proof. exact (@lem1483484 (term45 x) y (term45 z)). Qed.
Lemma lem1501294 (w : real) : (real_add w) = (real_add w).
Proof. exact (eq_refl (real_add w)). Qed.
Lemma lem1501295 (w : real) (x : real) (y : real) (z : real) : (term62 w y x z) = (term65 w x y z).
Proof. exact (MK_COMB (@lem1501294 w) (@lem1501293 x y z)). Qed.
Lemma lem1501296 (w : real) (x : real) (y : real) (z : real) : (term61 w y x z) = (term65 w x y z).
Proof. exact (TRANS (@lem1501288 w y x z) (@lem1501295 w x y z)). Qed.
Lemma lem1501297 (w : real) (x : real) (y : real) (z : real) : (term56 w y x z) = (term65 w x y z).
Proof. exact (TRANS (@lem1501287 w y x z) (@lem1501296 w x y z)). Qed.
Lemma lem1501299 (w : real) (x : real) (y : real) (z : real) : (term55 w y x z) = (term65 w x y z).
Proof. exact (TRANS (@lem1501278 w y x z) (@lem1501297 w x y z)). Qed.
Lemma lem1501300 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1501301 (w : real) (x : real) (y : real) (z : real) : (term66 w y x z) = (term67 w x y z).
Proof. exact (MK_COMB (@lem1501300) (@lem1501299 w x y z)). Qed.
Lemma lem1501302 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1501303 (w : real) (x : real) (y : real) (z : real) : (term54 w y x z) = (term68 w x y z).
Proof. exact (MK_COMB (@lem1501301 w x y z) (@lem1501302)). Qed.
Lemma lem1501304 (w : real) (x : real) (y : real) (z : real) : (term53 w y x z) = (term68 w x y z).
Proof. exact (TRANS (@lem1501260 w y x z) (@lem1501303 w x y z)). Qed.
Lemma lem1501305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1501306 (w : real) (x : real) (y : real) (z : real) : (term69 w x y z) = (term70 w x y z).
Proof. exact (MK_COMB (@lem1501305) (@lem1501259 w x y z)). Qed.
Lemma lem1501307 (w : real) (x : real) (y : real) (z : real) : (term1 w y x z) = (term71 w x y z).
Proof. exact (MK_COMB (@lem1501306 w x y z) (@lem1501304 w x y z)). Qed.
Lemma lem1501308 (w : real) (x : real) (y : real) : (term13 w y x) = (term72 w x y).
Proof. exact (fun_ext (fun z : real => @lem1501307 w x y z)). Qed.
Lemma lem1501309 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501310 (w : real) (x : real) (y : real) : (term14 w y x) = (term73 w x y).
Proof. exact (MK_COMB (@lem1501309) (@lem1501308 w x y)). Qed.
Lemma lem1501311 (w : real) (x : real) : (term22 w x) = (term74 w x).
Proof. exact (fun_ext (fun y : real => @lem1501310 w x y)). Qed.
Lemma lem1501312 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501313 (w : real) (x : real) : (term23 w x) = (term75 w x).
Proof. exact (MK_COMB (@lem1501312) (@lem1501311 w x)). Qed.
Lemma lem1501314 (w : real) : (term31 w) = (term76 w).
Proof. exact (fun_ext (fun x : real => @lem1501313 w x)). Qed.
Lemma lem1501315 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501316 (w : real) : (term32 w) = (term77 w).
Proof. exact (MK_COMB (@lem1501315) (@lem1501314 w)). Qed.
Lemma lem1501317 : term40 = term78.
Proof. exact (fun_ext (fun w : real => @lem1501316 w)). Qed.
Lemma lem1501318 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501319 : term41 = term79.
Proof. exact (MK_COMB (@lem1501318) (@lem1501317)). Qed.
Lemma lem1501386 : term33 = term79.
Proof. exact (TRANS (@lem1501218) (@lem1501319)). Qed.
Lemma lem1501399 (w : real) (x : real) (y : real) (z : real) : (term71 w x y z) = (term71 w x y z).
Proof. exact (eq_refl (term71 w x y z)). Qed.
Lemma lem1501400 (w : real) (x : real) (y : real) : (term72 w x y) = (term72 w x y).
Proof. exact (fun_ext (fun z : real => @lem1501399 w x y z)). Qed.
Lemma lem1501401 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501402 (w : real) (x : real) (y : real) : (term73 w x y) = (term73 w x y).
Proof. exact (MK_COMB (@lem1501401) (@lem1501400 w x y)). Qed.
Lemma lem1501403 (w : real) (x : real) : (term74 w x) = (term74 w x).
Proof. exact (fun_ext (fun y : real => @lem1501402 w x y)). Qed.
Lemma lem1501404 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501405 (w : real) (x : real) : (term75 w x) = (term75 w x).
Proof. exact (MK_COMB (@lem1501404) (@lem1501403 w x)). Qed.
Lemma lem1501406 (w : real) : (term76 w) = (term76 w).
Proof. exact (fun_ext (fun x : real => @lem1501405 w x)). Qed.
Lemma lem1501407 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501408 (w : real) : (term77 w) = (term77 w).
Proof. exact (MK_COMB (@lem1501407) (@lem1501406 w)). Qed.
Lemma lem1501409 : term78 = term78.
Proof. exact (fun_ext (fun w : real => @lem1501408 w)). Qed.
Lemma lem1501410 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1501411 : term79 = term79.
Proof. exact (MK_COMB (@lem1501410) (@lem1501409)). Qed.
Lemma lem1501412 : term33 = term79.
Proof. exact (TRANS (@lem1501386) (@lem1501411)). Qed.
Lemma lem1501416 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term71 w x y z.
Proof. exact (h1). Qed.
Lemma lem1501417 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term68 w x y z.
Proof. exact (proj2 (@lem1501416 w x y z h1)). Qed.
Lemma lem1501418 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term52 w x y z.
Proof. exact (proj1 (@lem1501416 w x y z h1)). Qed.
Lemma lem1501419 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term49 y z.
Proof. exact (proj2 (@lem1501418 w x y z h1)). Qed.
Lemma lem1501420 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term49 w x.
Proof. exact (proj1 (@lem1501418 w x y z h1)). Qed.
Lemma lem1501422 (n : nat) (m : nat) : (term80 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1501423 : term81 = term82.
Proof. exact (@lem1501422 (NUMERAL 0) term83). Qed.
Lemma lem1501424 : term84 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1501425 (h1 : term84 = (BIT1 0)) : term82 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1501426 : (term84 = (BIT1 0)) = (term82 = True).
Proof. exact (prop_ext (fun h1 : term84 = (BIT1 0) => @lem1501425 h1) (fun h1 : term82 = True => @lem1501424)). Qed.
Lemma lem1501427 : term82 = True.
Proof. exact (EQ_MP (@lem1501426) (@lem1501424)). Qed.
Lemma lem1501428 : term81 = True.
Proof. exact (TRANS (@lem1501423) (@lem1501427)). Qed.
Lemma lem1501429 : True = term81.
Proof. exact (SYM (@lem1501428)). Qed.
Lemma lem1501430 : term81.
Proof. exact (EQ_MP (@lem1501429) (@lem0)). Qed.
Lemma lem1501431 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term85 y z.
Proof. exact (conj (@lem1501430) (@lem1501419 w x y z h1)). Qed.
Lemma lem1501433 (x : real) (y : real) : term86 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1501434 (y : real) (z : real) : term87 y z.
Proof. exact (@lem1501433 term88 (term44 y z)). Qed.
Lemma lem1501435 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term89 y z.
Proof. exact (@lem1501434 y z (@lem1501431 w x y z h1)). Qed.
Lemma lem1501436 (y : real) (z : real) : (term90 y z) = (term44 y z).
Proof. exact (@lem1483460 (term44 y z)). Qed.
Lemma lem1501437 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1501438 (y : real) (z : real) : (term91 y z) = (term47 y z).
Proof. exact (MK_COMB (@lem1501437) (@lem1501436 y z)). Qed.
Lemma lem1501439 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1501440 (y : real) (z : real) : (term89 y z) = (term49 y z).
Proof. exact (MK_COMB (@lem1501438 y z) (@lem1501439)). Qed.
Lemma lem1501441 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term49 y z.
Proof. exact (EQ_MP (@lem1501440 y z) (@lem1501435 w x y z h1)). Qed.
Lemma lem1501443 (n : nat) (m : nat) : (term80 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1501444 : term81 = term82.
Proof. exact (@lem1501443 (NUMERAL 0) term83). Qed.
Lemma lem1501445 : term84 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1501446 (h1 : term84 = (BIT1 0)) : term82 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1501447 : (term84 = (BIT1 0)) = (term82 = True).
Proof. exact (prop_ext (fun h1 : term84 = (BIT1 0) => @lem1501446 h1) (fun h1 : term82 = True => @lem1501445)). Qed.
Lemma lem1501448 : term82 = True.
Proof. exact (EQ_MP (@lem1501447) (@lem1501445)). Qed.
Lemma lem1501449 : term81 = True.
Proof. exact (TRANS (@lem1501444) (@lem1501448)). Qed.
Lemma lem1501450 : True = term81.
Proof. exact (SYM (@lem1501449)). Qed.
Lemma lem1501451 : term81.
Proof. exact (EQ_MP (@lem1501450) (@lem0)). Qed.
Lemma lem1501452 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term92 w x y z.
Proof. exact (conj (@lem1501451) (@lem1501417 w x y z h1)). Qed.
Lemma lem1501454 (x : real) (y : real) : term93 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1501455 (w : real) (x : real) (y : real) (z : real) : term94 w x y z.
Proof. exact (@lem1501454 term88 (term65 w x y z)). Qed.
Lemma lem1501456 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term95 w x y z.
Proof. exact (@lem1501455 w x y z (@lem1501452 w x y z h1)). Qed.
Lemma lem1501457 (w : real) (x : real) (y : real) (z : real) : (term96 w x y z) = (term65 w x y z).
Proof. exact (@lem1483460 (term65 w x y z)). Qed.
Lemma lem1501458 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1501459 (w : real) (x : real) (y : real) (z : real) : (term97 w x y z) = (term67 w x y z).
Proof. exact (MK_COMB (@lem1501458) (@lem1501457 w x y z)). Qed.
Lemma lem1501460 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1501461 (w : real) (x : real) (y : real) (z : real) : (term95 w x y z) = (term68 w x y z).
Proof. exact (MK_COMB (@lem1501459 w x y z) (@lem1501460)). Qed.
Lemma lem1501462 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term68 w x y z.
Proof. exact (EQ_MP (@lem1501461 w x y z) (@lem1501456 w x y z h1)). Qed.
Lemma lem1501464 (n : nat) (m : nat) : (term80 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1501465 : term81 = term82.
Proof. exact (@lem1501464 (NUMERAL 0) term83). Qed.
Lemma lem1501466 : term84 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1501467 (h1 : term84 = (BIT1 0)) : term82 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1501468 : (term84 = (BIT1 0)) = (term82 = True).
Proof. exact (prop_ext (fun h1 : term84 = (BIT1 0) => @lem1501467 h1) (fun h1 : term82 = True => @lem1501466)). Qed.
Lemma lem1501469 : term82 = True.
Proof. exact (EQ_MP (@lem1501468) (@lem1501466)). Qed.
Lemma lem1501470 : term81 = True.
Proof. exact (TRANS (@lem1501465) (@lem1501469)). Qed.
Lemma lem1501471 : True = term81.
Proof. exact (SYM (@lem1501470)). Qed.
Lemma lem1501472 : term81.
Proof. exact (EQ_MP (@lem1501471) (@lem0)). Qed.
Lemma lem1501473 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term85 w x.
Proof. exact (conj (@lem1501472) (@lem1501420 w x y z h1)). Qed.
Lemma lem1501475 (x : real) (y : real) : term86 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1501476 (w : real) (x : real) : term87 w x.
Proof. exact (@lem1501475 term88 (term44 w x)). Qed.
Lemma lem1501477 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term89 w x.
Proof. exact (@lem1501476 w x (@lem1501473 w x y z h1)). Qed.
Lemma lem1501478 (w : real) (x : real) : (term90 w x) = (term44 w x).
Proof. exact (@lem1483460 (term44 w x)). Qed.
Lemma lem1501479 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1501480 (w : real) (x : real) : (term91 w x) = (term47 w x).
Proof. exact (MK_COMB (@lem1501479) (@lem1501478 w x)). Qed.
Lemma lem1501481 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1501482 (w : real) (x : real) : (term89 w x) = (term49 w x).
Proof. exact (MK_COMB (@lem1501480 w x) (@lem1501481)). Qed.
Lemma lem1501483 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term49 w x.
Proof. exact (EQ_MP (@lem1501482 w x) (@lem1501477 w x y z h1)). Qed.
Lemma lem1501484 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term98 w x y z.
Proof. exact (conj (@lem1501483 w x y z h1) (@lem1501462 w x y z h1)). Qed.
Lemma lem1501486 (x : real) (y : real) : term99 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1501487 (w : real) (x : real) (y : real) (z : real) : term100 w x y z.
Proof. exact (@lem1501486 (term44 w x) (term65 w x y z)). Qed.
Lemma lem1501488 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term101 w x y z.
Proof. exact (@lem1501487 w x y z (@lem1501484 w x y z h1)). Qed.
Lemma lem1501489 (w : real) (x : real) (y : real) (z : real) : (term102 w x y z) = (term103 w x y z).
Proof. exact (@lem1483480 (term45 w) w x (term64 x y z)). Qed.
Lemma lem1501490 (w : real) : (term104 w) = (term105 w).
Proof. exact (@lem1483440 term59 w). Qed.
Lemma lem1501492 (m : nat) : (term106 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1501493 : term107 = term48.
Proof. exact (@lem1501492 term83). Qed.
Lemma lem1501494 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1501495 : term108 = term109.
Proof. exact (MK_COMB (@lem1501494) (@lem1501493)). Qed.
Lemma lem1501496 (w : real) : w = w.
Proof. exact (eq_refl w). Qed.
Lemma lem1501497 (w : real) : (term105 w) = (term110 w).
Proof. exact (MK_COMB (@lem1501495) (@lem1501496 w)). Qed.
Lemma lem1501498 (w : real) : (term104 w) = (term110 w).
Proof. exact (TRANS (@lem1501490 w) (@lem1501497 w)). Qed.
Lemma lem1501499 (w : real) : (term110 w) = term48.
Proof. exact (@lem1483446 w). Qed.
Lemma lem1501500 (w : real) : (term104 w) = term48.
Proof. exact (TRANS (@lem1501498 w) (@lem1501499 w)). Qed.
Lemma lem1501501 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1501502 (w : real) : (term111 w) = term112.
Proof. exact (MK_COMB (@lem1501501) (@lem1501500 w)). Qed.
Lemma lem1501503 (x : real) (y : real) (z : real) : (term113 x y z) = (term114 x y z).
Proof. exact (@lem1483490 x (term45 x) (term43 y z)). Qed.
Lemma lem1501504 (x : real) : (term115 x) = (term105 x).
Proof. exact (@lem1483442 term59 x). Qed.
Lemma lem1501506 (m : nat) : (term106 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1501507 : term107 = term48.
Proof. exact (@lem1501506 term83). Qed.
Lemma lem1501508 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1501509 : term108 = term109.
Proof. exact (MK_COMB (@lem1501508) (@lem1501507)). Qed.
Lemma lem1501510 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1501511 (x : real) : (term105 x) = (term110 x).
Proof. exact (MK_COMB (@lem1501509) (@lem1501510 x)). Qed.
Lemma lem1501512 (x : real) : (term115 x) = (term110 x).
Proof. exact (TRANS (@lem1501504 x) (@lem1501511 x)). Qed.
Lemma lem1501513 (x : real) : (term110 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1501514 (x : real) : (term115 x) = term48.
Proof. exact (TRANS (@lem1501512 x) (@lem1501513 x)). Qed.
Lemma lem1501515 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1501516 (x : real) : (term116 x) = term112.
Proof. exact (MK_COMB (@lem1501515) (@lem1501514 x)). Qed.
Lemma lem1501517 (y : real) (z : real) : (term43 y z) = (term43 y z).
Proof. exact (eq_refl (term43 y z)). Qed.
Lemma lem1501518 (x : real) (y : real) (z : real) : (term114 x y z) = (term117 y z).
Proof. exact (MK_COMB (@lem1501516 x) (@lem1501517 y z)). Qed.
Lemma lem1501519 (x : real) (y : real) (z : real) : (term113 x y z) = (term117 y z).
Proof. exact (TRANS (@lem1501503 x y z) (@lem1501518 x y z)). Qed.
Lemma lem1501520 (y : real) (z : real) : (term117 y z) = (term43 y z).
Proof. exact (@lem1483448 (term43 y z)). Qed.
Lemma lem1501521 (x : real) (y : real) (z : real) : (term113 x y z) = (term43 y z).
Proof. exact (TRANS (@lem1501519 x y z) (@lem1501520 y z)). Qed.
Lemma lem1501522 (w : real) (x : real) (y : real) (z : real) : (term103 w x y z) = (term117 y z).
Proof. exact (MK_COMB (@lem1501502 w) (@lem1501521 x y z)). Qed.
Lemma lem1501523 (w : real) (x : real) (y : real) (z : real) : (term102 w x y z) = (term117 y z).
Proof. exact (TRANS (@lem1501489 w x y z) (@lem1501522 w x y z)). Qed.
Lemma lem1501524 (y : real) (z : real) : (term117 y z) = (term43 y z).
Proof. exact (@lem1483448 (term43 y z)). Qed.
Lemma lem1501525 (w : real) (x : real) (y : real) (z : real) : (term102 w x y z) = (term43 y z).
Proof. exact (TRANS (@lem1501523 w x y z) (@lem1501524 y z)). Qed.
Lemma lem1501526 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1501527 (w : real) (x : real) (y : real) (z : real) : (term118 w x y z) = (term119 y z).
Proof. exact (MK_COMB (@lem1501526) (@lem1501525 w x y z)). Qed.
Lemma lem1501528 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1501529 (w : real) (x : real) (y : real) (z : real) : (term101 w x y z) = (term120 y z).
Proof. exact (MK_COMB (@lem1501527 w x y z) (@lem1501528)). Qed.
Lemma lem1501530 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term120 y z.
Proof. exact (EQ_MP (@lem1501529 w x y z) (@lem1501488 w x y z h1)). Qed.
Lemma lem1501532 (n : nat) (m : nat) : (term80 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1501533 : term81 = term82.
Proof. exact (@lem1501532 (NUMERAL 0) term83). Qed.
Lemma lem1501534 : term84 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1501535 (h1 : term84 = (BIT1 0)) : term82 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1501536 : (term84 = (BIT1 0)) = (term82 = True).
Proof. exact (prop_ext (fun h1 : term84 = (BIT1 0) => @lem1501535 h1) (fun h1 : term82 = True => @lem1501534)). Qed.
Lemma lem1501537 : term82 = True.
Proof. exact (EQ_MP (@lem1501536) (@lem1501534)). Qed.
Lemma lem1501538 : term81 = True.
Proof. exact (TRANS (@lem1501533) (@lem1501537)). Qed.
Lemma lem1501539 : True = term81.
Proof. exact (SYM (@lem1501538)). Qed.
Lemma lem1501540 : term81.
Proof. exact (EQ_MP (@lem1501539) (@lem0)). Qed.
Lemma lem1501541 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term121 y z.
Proof. exact (conj (@lem1501540) (@lem1501530 w x y z h1)). Qed.
Lemma lem1501543 (x : real) (y : real) : term86 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1501544 (y : real) (z : real) : term122 y z.
Proof. exact (@lem1501543 term88 (term43 y z)). Qed.
Lemma lem1501545 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term123 y z.
Proof. exact (@lem1501544 y z (@lem1501541 w x y z h1)). Qed.
Lemma lem1501546 (y : real) (z : real) : (term124 y z) = (term43 y z).
Proof. exact (@lem1483460 (term43 y z)). Qed.
Lemma lem1501547 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1501548 (y : real) (z : real) : (term125 y z) = (term119 y z).
Proof. exact (MK_COMB (@lem1501547) (@lem1501546 y z)). Qed.
Lemma lem1501549 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1501550 (y : real) (z : real) : (term123 y z) = (term120 y z).
Proof. exact (MK_COMB (@lem1501548 y z) (@lem1501549)). Qed.
Lemma lem1501551 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term120 y z.
Proof. exact (EQ_MP (@lem1501550 y z) (@lem1501545 w x y z h1)). Qed.
Lemma lem1501552 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term126 y z.
Proof. exact (conj (@lem1501551 w x y z h1) (@lem1501441 w x y z h1)). Qed.
Lemma lem1501554 (x : real) (y : real) : term127 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1501555 (y : real) (z : real) : term128 y z.
Proof. exact (@lem1501554 (term43 y z) (term44 y z)). Qed.
Lemma lem1501556 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term129 y z.
Proof. exact (@lem1501555 y z (@lem1501552 w x y z h1)). Qed.
Lemma lem1501557 (y : real) (z : real) : (term130 y z) = (term131 y z).
Proof. exact (@lem1483480 y (term45 y) (term45 z) z). Qed.
Lemma lem1501558 (y : real) : (term115 y) = (term105 y).
Proof. exact (@lem1483442 term59 y). Qed.
Lemma lem1501560 (m : nat) : (term106 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1501561 : term107 = term48.
Proof. exact (@lem1501560 term83). Qed.
Lemma lem1501562 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1501563 : term108 = term109.
Proof. exact (MK_COMB (@lem1501562) (@lem1501561)). Qed.
Lemma lem1501564 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1501565 (y : real) : (term105 y) = (term110 y).
Proof. exact (MK_COMB (@lem1501563) (@lem1501564 y)). Qed.
Lemma lem1501566 (y : real) : (term115 y) = (term110 y).
Proof. exact (TRANS (@lem1501558 y) (@lem1501565 y)). Qed.
Lemma lem1501567 (y : real) : (term110 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1501568 (y : real) : (term115 y) = term48.
Proof. exact (TRANS (@lem1501566 y) (@lem1501567 y)). Qed.
Lemma lem1501569 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1501570 (y : real) : (term116 y) = term112.
Proof. exact (MK_COMB (@lem1501569) (@lem1501568 y)). Qed.
Lemma lem1501571 (z : real) : (term104 z) = (term105 z).
Proof. exact (@lem1483440 term59 z). Qed.
Lemma lem1501573 (m : nat) : (term106 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1501574 : term107 = term48.
Proof. exact (@lem1501573 term83). Qed.
Lemma lem1501575 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1501576 : term108 = term109.
Proof. exact (MK_COMB (@lem1501575) (@lem1501574)). Qed.
Lemma lem1501577 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1501578 (z : real) : (term105 z) = (term110 z).
Proof. exact (MK_COMB (@lem1501576) (@lem1501577 z)). Qed.
Lemma lem1501579 (z : real) : (term104 z) = (term110 z).
Proof. exact (TRANS (@lem1501571 z) (@lem1501578 z)). Qed.
Lemma lem1501580 (z : real) : (term110 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1501581 (z : real) : (term104 z) = term48.
Proof. exact (TRANS (@lem1501579 z) (@lem1501580 z)). Qed.
Lemma lem1501582 (y : real) (z : real) : (term131 y z) = term132.
Proof. exact (MK_COMB (@lem1501570 y) (@lem1501581 z)). Qed.
Lemma lem1501583 (y : real) (z : real) : (term130 y z) = term132.
Proof. exact (TRANS (@lem1501557 y z) (@lem1501582 y z)). Qed.
Lemma lem1501584 : term132 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1501585 (y : real) (z : real) : (term130 y z) = term48.
Proof. exact (TRANS (@lem1501583 y z) (@lem1501584)). Qed.
Lemma lem1501586 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1501587 (y : real) (z : real) : (term133 y z) = term134.
Proof. exact (MK_COMB (@lem1501586) (@lem1501585 y z)). Qed.
Lemma lem1501588 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1501589 (y : real) (z : real) : (term129 y z) = term135.
Proof. exact (MK_COMB (@lem1501587 y z) (@lem1501588)). Qed.
Lemma lem1501590 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term135.
Proof. exact (EQ_MP (@lem1501589 y z) (@lem1501556 w x y z h1)). Qed.
Lemma lem1501592 (n : nat) (m : nat) : (term80 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1501593 : term135 = term136.
Proof. exact (@lem1501592 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1501594 : term136 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1501595 : term135 = False.
Proof. exact (TRANS (@lem1501593) (@lem1501594)). Qed.
Lemma lem1501596 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : False.
Proof. exact (EQ_MP (@lem1501595) (@lem1501590 w x y z h1)). Qed.
Lemma lem1501598 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : term71 w x y z.
Proof. exact (h1). Qed.
Lemma lem1501599 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : (term71 w x y z) = False.
Proof. exact (prop_ext (fun h2 : term71 w x y z => @lem1501596 w x y z h1) (fun h2 : False => @lem1501598 w x y z h1)). Qed.
Lemma lem1501600 (w : real) (x : real) (y : real) (z : real) (h1 : term71 w x y z) : False.
Proof. exact (EQ_MP (@lem1501599 w x y z h1) (@lem1501598 w x y z h1)). Qed.
Lemma lem1501601 (w : real) (x : real) (y : real) (h1 : term73 w x y) : term73 w x y.
Proof. exact (h1). Qed.
Lemma lem1501602 (w : real) (x : real) (y : real) (h1 : term73 w x y) : False.
Proof. exact (ex_elim (@lem1501601 w x y h1) (fun z : real => fun h0 : term72 w x y z => @lem1501600 w x y z h0)). Qed.
Lemma lem1501603 (w : real) (x : real) (h1 : term75 w x) : term75 w x.
Proof. exact (h1). Qed.
Lemma lem1501604 (w : real) (x : real) (h1 : term75 w x) : False.
Proof. exact (ex_elim (@lem1501603 w x h1) (fun y : real => fun h0 : term74 w x y => @lem1501602 w x y h0)). Qed.
Lemma lem1501605 (w : real) (h1 : term77 w) : term77 w.
Proof. exact (h1). Qed.
Lemma lem1501606 (w : real) (h1 : term77 w) : False.
Proof. exact (ex_elim (@lem1501605 w h1) (fun x : real => fun h0 : term76 w x => @lem1501604 w x h0)). Qed.
Lemma lem1501607 (h1 : term79) : term79.
Proof. exact (h1). Qed.
Lemma lem1501608 (h1 : term79) : False.
Proof. exact (ex_elim (@lem1501607 h1) (fun w : real => fun h0 : term78 w => @lem1501606 w h0)). Qed.
Lemma lem1501609 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1501610 (h1 : term33) : term79.
Proof. exact (EQ_MP (@lem1501412) (@lem1501609 h1)). Qed.
Lemma lem1501611 (h1 : term33) : term79 = False.
Proof. exact (prop_ext (fun h2 : term79 => @lem1501608 h2) (fun h2 : False => @lem1501610 h1)). Qed.
Lemma lem1501612 (h1 : term33) : False.
Proof. exact (EQ_MP (@lem1501611 h1) (@lem1501610 h1)). Qed.
Lemma lem1501613 : term137.
Proof. exact (fun h0 : term33 => @lem1501612 h0). Qed.
Lemma lem1501614 : term138.
Proof. exact (@lem1386578 term139). Qed.
Lemma lem1501615 : term139.
Proof. exact (@lem1501614 (@lem1501613)). Qed.
