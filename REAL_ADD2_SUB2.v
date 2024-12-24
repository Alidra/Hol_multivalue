Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ADD2_SUB2_term_abbrevs.
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
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
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
Lemma lem1517245 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1517246 (a : real) (c : real) (b : real) : (term2 a c b) = (term3 a c b).
Proof. exact (@lem1517245 (term4 a c b)). Qed.
Lemma lem1517247 (a : real) (c : real) (b : real) (d : real) : (term5 a c b d) = ((term6 a b c d) = (term7 a c b d)).
Proof. exact (eq_refl (term5 a c b d)). Qed.
Lemma lem1517248 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1517250 (a : real) (c : real) (b : real) (d : real) : (term8 a c b d) = (term9 a c b d).
Proof. exact (MK_COMB (@lem1517248) (@lem1517247 a c b d)). Qed.
Lemma lem1517251 (a : real) (c : real) (b : real) : (term10 a c b) = (term11 a c b).
Proof. exact (fun_ext (fun d : real => @lem1517250 a c b d)). Qed.
Lemma lem1517252 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517253 (a : real) (c : real) (b : real) : (term3 a c b) = (term12 a c b).
Proof. exact (MK_COMB (@lem1517252) (@lem1517251 a c b)). Qed.
Lemma lem1517254 (a : real) (c : real) (b : real) : (term2 a c b) = (term12 a c b).
Proof. exact (TRANS (@lem1517246 a c b) (@lem1517253 a c b)). Qed.
Lemma lem1517255 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1517256 (a : real) (b : real) : (term13 a b) = (term14 a b).
Proof. exact (@lem1517255 (term15 a b)). Qed.
Lemma lem1517257 (a : real) (c : real) (b : real) : (term16 a b c) = (term17 a c b).
Proof. exact (eq_refl (term16 a b c)). Qed.
Lemma lem1517258 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1517259 (a : real) (c : real) (b : real) : (term18 a b c) = (term2 a c b).
Proof. exact (MK_COMB (@lem1517258) (@lem1517257 a c b)). Qed.
Lemma lem1517260 (a : real) (c : real) (b : real) : (term18 a b c) = (term12 a c b).
Proof. exact (TRANS (@lem1517259 a c b) (@lem1517254 a c b)). Qed.
Lemma lem1517261 (a : real) (b : real) : (term19 a b) = (term20 a b).
Proof. exact (fun_ext (fun c : real => @lem1517260 a c b)). Qed.
Lemma lem1517262 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517263 (a : real) (b : real) : (term14 a b) = (term21 a b).
Proof. exact (MK_COMB (@lem1517262) (@lem1517261 a b)). Qed.
Lemma lem1517264 (a : real) (b : real) : (term13 a b) = (term21 a b).
Proof. exact (TRANS (@lem1517256 a b) (@lem1517263 a b)). Qed.
Lemma lem1517265 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1517266 (a : real) : (term22 a) = (term23 a).
Proof. exact (@lem1517265 (term24 a)). Qed.
Lemma lem1517267 (a : real) (b : real) : (term25 a b) = (term26 a b).
Proof. exact (eq_refl (term25 a b)). Qed.
Lemma lem1517268 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1517269 (a : real) (b : real) : (term27 a b) = (term13 a b).
Proof. exact (MK_COMB (@lem1517268) (@lem1517267 a b)). Qed.
Lemma lem1517270 (a : real) (b : real) : (term27 a b) = (term21 a b).
Proof. exact (TRANS (@lem1517269 a b) (@lem1517264 a b)). Qed.
Lemma lem1517271 (a : real) : (term28 a) = (term29 a).
Proof. exact (fun_ext (fun b : real => @lem1517270 a b)). Qed.
Lemma lem1517272 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517273 (a : real) : (term23 a) = (term30 a).
Proof. exact (MK_COMB (@lem1517272) (@lem1517271 a)). Qed.
Lemma lem1517274 (a : real) : (term22 a) = (term30 a).
Proof. exact (TRANS (@lem1517266 a) (@lem1517273 a)). Qed.
Lemma lem1517275 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1517276 : term31 = term32.
Proof. exact (@lem1517275 term33). Qed.
Lemma lem1517277 (a : real) : (term34 a) = (term35 a).
Proof. exact (eq_refl (term34 a)). Qed.
Lemma lem1517278 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1517279 (a : real) : (term36 a) = (term22 a).
Proof. exact (MK_COMB (@lem1517278) (@lem1517277 a)). Qed.
Lemma lem1517280 (a : real) : (term36 a) = (term30 a).
Proof. exact (TRANS (@lem1517279 a) (@lem1517274 a)). Qed.
Lemma lem1517281 : term37 = term38.
Proof. exact (fun_ext (fun a : real => @lem1517280 a)). Qed.
Lemma lem1517282 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517283 : term32 = term39.
Proof. exact (MK_COMB (@lem1517282) (@lem1517281)). Qed.
Lemma lem1517285 : term31 = term39.
Proof. exact (TRANS (@lem1517276) (@lem1517283)). Qed.
Lemma lem1517288 (a : real) (c : real) (b : real) (d : real) : (term9 a c b d) = (term9 a c b d).
Proof. exact (eq_refl (term9 a c b d)). Qed.
Lemma lem1517289 (a : real) (c : real) (b : real) : (term11 a c b) = (term11 a c b).
Proof. exact (fun_ext (fun d : real => @lem1517288 a c b d)). Qed.
Lemma lem1517290 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517291 (a : real) (c : real) (b : real) : (term12 a c b) = (term12 a c b).
Proof. exact (MK_COMB (@lem1517290) (@lem1517289 a c b)). Qed.
Lemma lem1517292 (a : real) (b : real) : (term20 a b) = (term20 a b).
Proof. exact (fun_ext (fun c : real => @lem1517291 a c b)). Qed.
Lemma lem1517293 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517294 (a : real) (b : real) : (term21 a b) = (term21 a b).
Proof. exact (MK_COMB (@lem1517293) (@lem1517292 a b)). Qed.
Lemma lem1517295 (a : real) : (term29 a) = (term29 a).
Proof. exact (fun_ext (fun b : real => @lem1517294 a b)). Qed.
Lemma lem1517296 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517297 (a : real) : (term30 a) = (term30 a).
Proof. exact (MK_COMB (@lem1517296) (@lem1517295 a)). Qed.
Lemma lem1517298 : term38 = term38.
Proof. exact (fun_ext (fun a : real => @lem1517297 a)). Qed.
Lemma lem1517299 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517300 : term39 = term39.
Proof. exact (MK_COMB (@lem1517299) (@lem1517298)). Qed.
Lemma lem1517301 : term31 = term39.
Proof. exact (TRANS (@lem1517285) (@lem1517300)). Qed.
Lemma lem1517302 (a : real) (c : real) (b : real) (d : real) : (term9 a c b d) = (term40 a c b d).
Proof. exact (@lem1483554 (term6 a b c d) (term7 a c b d)). Qed.
Lemma lem1517315 (b : real) (d : real) : (real_sub b d) = (term41 b d).
Proof. exact (@lem1483519 b d). Qed.
Lemma lem1517328 (a : real) (c : real) : (real_sub a c) = (term41 a c).
Proof. exact (@lem1483519 a c). Qed.
Lemma lem1517329 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1517330 (a : real) (c : real) : (term42 a c) = (term43 a c).
Proof. exact (MK_COMB (@lem1517329) (@lem1517328 a c)). Qed.
Lemma lem1517331 (a : real) (c : real) (b : real) (d : real) : (term7 a c b d) = (term44 a c b d).
Proof. exact (MK_COMB (@lem1517330 a c) (@lem1517315 b d)). Qed.
Lemma lem1517332 (a : real) (c : real) (b : real) (d : real) : (term44 a c b d) = (term45 a c b d).
Proof. exact (@lem1483482 a (term46 c) (term41 b d)). Qed.
Lemma lem1517337 (b : real) (c : real) (d : real) : (term47 c b d) = (term48 b c d).
Proof. exact (@lem1483484 b (term46 c) (term46 d)). Qed.
Lemma lem1517338 (a : real) : (real_add a) = (real_add a).
Proof. exact (eq_refl (real_add a)). Qed.
Lemma lem1517339 (a : real) (b : real) (c : real) (d : real) : (term45 a c b d) = (term49 a b c d).
Proof. exact (MK_COMB (@lem1517338 a) (@lem1517337 b c d)). Qed.
Lemma lem1517340 (a : real) (b : real) (c : real) (d : real) : (term44 a c b d) = (term49 a b c d).
Proof. exact (TRANS (@lem1517332 a c b d) (@lem1517339 a b c d)). Qed.
Lemma lem1517341 (a : real) (b : real) (c : real) (d : real) : (term7 a c b d) = (term49 a b c d).
Proof. exact (TRANS (@lem1517331 a c b d) (@lem1517340 a b c d)). Qed.
Lemma lem1517359 (a : real) (b : real) (c : real) (d : real) : (term6 a b c d) = (term50 a b c d).
Proof. exact (@lem1483519 (real_add a b) (real_add c d)). Qed.
Lemma lem1517366 (c : real) (d : real) : (term51 c d) = (term52 c d).
Proof. exact (@lem1483508 c term53 d). Qed.
Lemma lem1517367 (a : real) (b : real) : (term54 a b) = (term54 a b).
Proof. exact (eq_refl (term54 a b)). Qed.
Lemma lem1517368 (a : real) (b : real) (c : real) (d : real) : (term50 a b c d) = (term55 a b c d).
Proof. exact (MK_COMB (@lem1517367 a b) (@lem1517366 c d)). Qed.
Lemma lem1517373 (a : real) (b : real) (c : real) (d : real) : (term55 a b c d) = (term49 a b c d).
Proof. exact (@lem1483482 a b (term52 c d)). Qed.
Lemma lem1517374 (a : real) (b : real) (c : real) (d : real) : (term50 a b c d) = (term49 a b c d).
Proof. exact (TRANS (@lem1517368 a b c d) (@lem1517373 a b c d)). Qed.
Lemma lem1517376 (a : real) (b : real) (c : real) (d : real) : (term6 a b c d) = (term49 a b c d).
Proof. exact (TRANS (@lem1517359 a b c d) (@lem1517374 a b c d)). Qed.
Lemma lem1517377 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1517378 (a : real) (b : real) (c : real) (d : real) : (term56 a b c d) = (term57 a b c d).
Proof. exact (MK_COMB (@lem1517377) (@lem1517376 a b c d)). Qed.
Lemma lem1517379 (a : real) (b : real) (c : real) (d : real) : (term58 a c b d) = (term59 a b c d).
Proof. exact (MK_COMB (@lem1517378 a b c d) (@lem1517341 a b c d)). Qed.
Lemma lem1517380 (a : real) (b : real) (c : real) (d : real) : (term59 a b c d) = (term60 a b c d).
Proof. exact (@lem1483519 (term49 a b c d) (term49 a b c d)). Qed.
Lemma lem1517381 (a : real) (b : real) (c : real) (d : real) : (term61 a b c d) = (term62 a b c d).
Proof. exact (@lem1483508 a term53 (term48 b c d)). Qed.
Lemma lem1517382 (b : real) (c : real) (d : real) : (term63 b c d) = (term64 b c d).
Proof. exact (@lem1483508 b term53 (term52 c d)). Qed.
Lemma lem1517383 (c : real) (d : real) : (term65 c d) = (term66 c d).
Proof. exact (@lem1483508 (term46 c) term53 (term46 d)). Qed.
Lemma lem1517384 (d : real) : (term67 d) = (term68 d).
Proof. exact (@lem1483476 term53 term53 d). Qed.
Lemma lem1517386 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1517387 : term71 = term72.
Proof. exact (@lem1517386 term73 term73). Qed.
Lemma lem1517388 : (term74 = (BIT1 0)) = (term75 = term73).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1517389 : term75 = term73.
Proof. exact (EQ_MP (@lem1517388) (@lem940073)). Qed.
Lemma lem1517390 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1517391 : term72 = term76.
Proof. exact (MK_COMB (@lem1517390) (@lem1517389)). Qed.
Lemma lem1517392 : term71 = term76.
Proof. exact (TRANS (@lem1517387) (@lem1517391)). Qed.
Lemma lem1517393 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1517394 : term77 = term78.
Proof. exact (MK_COMB (@lem1517393) (@lem1517392)). Qed.
Lemma lem1517395 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1517396 (d : real) : (term68 d) = (term79 d).
Proof. exact (MK_COMB (@lem1517394) (@lem1517395 d)). Qed.
Lemma lem1517397 (d : real) : (term67 d) = (term79 d).
Proof. exact (TRANS (@lem1517384 d) (@lem1517396 d)). Qed.
Lemma lem1517398 (d : real) : (term79 d) = d.
Proof. exact (@lem1483436 d). Qed.
Lemma lem1517399 (d : real) : (term67 d) = d.
Proof. exact (TRANS (@lem1517397 d) (@lem1517398 d)). Qed.
Lemma lem1517400 (c : real) : (term67 c) = (term68 c).
Proof. exact (@lem1483476 term53 term53 c). Qed.
Lemma lem1517402 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1517403 : term71 = term72.
Proof. exact (@lem1517402 term73 term73). Qed.
Lemma lem1517404 : (term74 = (BIT1 0)) = (term75 = term73).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1517405 : term75 = term73.
Proof. exact (EQ_MP (@lem1517404) (@lem940073)). Qed.
Lemma lem1517406 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1517407 : term72 = term76.
Proof. exact (MK_COMB (@lem1517406) (@lem1517405)). Qed.
Lemma lem1517408 : term71 = term76.
Proof. exact (TRANS (@lem1517403) (@lem1517407)). Qed.
Lemma lem1517409 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1517410 : term77 = term78.
Proof. exact (MK_COMB (@lem1517409) (@lem1517408)). Qed.
Lemma lem1517411 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem1517412 (c : real) : (term68 c) = (term79 c).
Proof. exact (MK_COMB (@lem1517410) (@lem1517411 c)). Qed.
Lemma lem1517413 (c : real) : (term67 c) = (term79 c).
Proof. exact (TRANS (@lem1517400 c) (@lem1517412 c)). Qed.
Lemma lem1517414 (c : real) : (term79 c) = c.
Proof. exact (@lem1483436 c). Qed.
Lemma lem1517415 (c : real) : (term67 c) = c.
Proof. exact (TRANS (@lem1517413 c) (@lem1517414 c)). Qed.
Lemma lem1517416 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1517417 (c : real) : (term80 c) = (real_add c).
Proof. exact (MK_COMB (@lem1517416) (@lem1517415 c)). Qed.
Lemma lem1517418 (c : real) (d : real) : (term66 c d) = (real_add c d).
Proof. exact (MK_COMB (@lem1517417 c) (@lem1517399 d)). Qed.
Lemma lem1517419 (c : real) (d : real) : (term65 c d) = (real_add c d).
Proof. exact (TRANS (@lem1517383 c d) (@lem1517418 c d)). Qed.
Lemma lem1517422 (b : real) : (term81 b) = (term81 b).
Proof. exact (eq_refl (term81 b)). Qed.
Lemma lem1517423 (b : real) (c : real) (d : real) : (term64 b c d) = (term82 b c d).
Proof. exact (MK_COMB (@lem1517422 b) (@lem1517419 c d)). Qed.
Lemma lem1517424 (b : real) (c : real) (d : real) : (term63 b c d) = (term82 b c d).
Proof. exact (TRANS (@lem1517382 b c d) (@lem1517423 b c d)). Qed.
Lemma lem1517427 (a : real) : (term81 a) = (term81 a).
Proof. exact (eq_refl (term81 a)). Qed.
Lemma lem1517428 (a : real) (b : real) (c : real) (d : real) : (term62 a b c d) = (term83 a b c d).
Proof. exact (MK_COMB (@lem1517427 a) (@lem1517424 b c d)). Qed.
Lemma lem1517429 (a : real) (b : real) (c : real) (d : real) : (term61 a b c d) = (term83 a b c d).
Proof. exact (TRANS (@lem1517381 a b c d) (@lem1517428 a b c d)). Qed.
Lemma lem1517430 (a : real) (b : real) (c : real) (d : real) : (term84 a b c d) = (term84 a b c d).
Proof. exact (eq_refl (term84 a b c d)). Qed.
Lemma lem1517431 (a : real) (b : real) (c : real) (d : real) : (term60 a b c d) = (term85 a b c d).
Proof. exact (MK_COMB (@lem1517430 a b c d) (@lem1517429 a b c d)). Qed.
Lemma lem1517432 (a : real) (b : real) (c : real) (d : real) : (term85 a b c d) = (term86 a b c d).
Proof. exact (@lem1483480 a (term46 a) (term48 b c d) (term82 b c d)). Qed.
Lemma lem1517433 (a : real) : (term87 a) = (term88 a).
Proof. exact (@lem1483442 term53 a). Qed.
Lemma lem1517435 (m : nat) : (term89 m) = term90.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1517436 : term91 = term90.
Proof. exact (@lem1517435 term73). Qed.
Lemma lem1517437 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1517438 : term92 = term93.
Proof. exact (MK_COMB (@lem1517437) (@lem1517436)). Qed.
Lemma lem1517439 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1517440 (a : real) : (term88 a) = (term94 a).
Proof. exact (MK_COMB (@lem1517438) (@lem1517439 a)). Qed.
Lemma lem1517441 (a : real) : (term87 a) = (term94 a).
Proof. exact (TRANS (@lem1517433 a) (@lem1517440 a)). Qed.
Lemma lem1517442 (a : real) : (term94 a) = term90.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1517443 (a : real) : (term87 a) = term90.
Proof. exact (TRANS (@lem1517441 a) (@lem1517442 a)). Qed.
Lemma lem1517444 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1517445 (a : real) : (term95 a) = term96.
Proof. exact (MK_COMB (@lem1517444) (@lem1517443 a)). Qed.
Lemma lem1517446 (b : real) (c : real) (d : real) : (term97 b c d) = (term98 b c d).
Proof. exact (@lem1483480 b (term46 b) (term52 c d) (real_add c d)). Qed.
Lemma lem1517447 (b : real) : (term87 b) = (term88 b).
Proof. exact (@lem1483442 term53 b). Qed.
Lemma lem1517449 (m : nat) : (term89 m) = term90.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1517450 : term91 = term90.
Proof. exact (@lem1517449 term73). Qed.
Lemma lem1517451 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1517452 : term92 = term93.
Proof. exact (MK_COMB (@lem1517451) (@lem1517450)). Qed.
Lemma lem1517453 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1517454 (b : real) : (term88 b) = (term94 b).
Proof. exact (MK_COMB (@lem1517452) (@lem1517453 b)). Qed.
Lemma lem1517455 (b : real) : (term87 b) = (term94 b).
Proof. exact (TRANS (@lem1517447 b) (@lem1517454 b)). Qed.
Lemma lem1517456 (b : real) : (term94 b) = term90.
Proof. exact (@lem1483446 b). Qed.
Lemma lem1517457 (b : real) : (term87 b) = term90.
Proof. exact (TRANS (@lem1517455 b) (@lem1517456 b)). Qed.
Lemma lem1517458 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1517459 (b : real) : (term95 b) = term96.
Proof. exact (MK_COMB (@lem1517458) (@lem1517457 b)). Qed.
Lemma lem1517460 (c : real) (d : real) : (term99 c d) = (term100 c d).
Proof. exact (@lem1483480 (term46 c) c (term46 d) d). Qed.
Lemma lem1517461 (c : real) : (term101 c) = (term88 c).
Proof. exact (@lem1483440 term53 c). Qed.
Lemma lem1517463 (m : nat) : (term89 m) = term90.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1517464 : term91 = term90.
Proof. exact (@lem1517463 term73). Qed.
Lemma lem1517465 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1517466 : term92 = term93.
Proof. exact (MK_COMB (@lem1517465) (@lem1517464)). Qed.
Lemma lem1517467 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem1517468 (c : real) : (term88 c) = (term94 c).
Proof. exact (MK_COMB (@lem1517466) (@lem1517467 c)). Qed.
Lemma lem1517469 (c : real) : (term101 c) = (term94 c).
Proof. exact (TRANS (@lem1517461 c) (@lem1517468 c)). Qed.
Lemma lem1517470 (c : real) : (term94 c) = term90.
Proof. exact (@lem1483446 c). Qed.
Lemma lem1517471 (c : real) : (term101 c) = term90.
Proof. exact (TRANS (@lem1517469 c) (@lem1517470 c)). Qed.
Lemma lem1517472 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1517473 (c : real) : (term102 c) = term96.
Proof. exact (MK_COMB (@lem1517472) (@lem1517471 c)). Qed.
Lemma lem1517474 (d : real) : (term101 d) = (term88 d).
Proof. exact (@lem1483440 term53 d). Qed.
Lemma lem1517476 (m : nat) : (term89 m) = term90.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1517477 : term91 = term90.
Proof. exact (@lem1517476 term73). Qed.
Lemma lem1517478 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1517479 : term92 = term93.
Proof. exact (MK_COMB (@lem1517478) (@lem1517477)). Qed.
Lemma lem1517480 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1517481 (d : real) : (term88 d) = (term94 d).
Proof. exact (MK_COMB (@lem1517479) (@lem1517480 d)). Qed.
Lemma lem1517482 (d : real) : (term101 d) = (term94 d).
Proof. exact (TRANS (@lem1517474 d) (@lem1517481 d)). Qed.
Lemma lem1517483 (d : real) : (term94 d) = term90.
Proof. exact (@lem1483446 d). Qed.
Lemma lem1517484 (d : real) : (term101 d) = term90.
Proof. exact (TRANS (@lem1517482 d) (@lem1517483 d)). Qed.
Lemma lem1517485 (c : real) (d : real) : (term100 c d) = term103.
Proof. exact (MK_COMB (@lem1517473 c) (@lem1517484 d)). Qed.
Lemma lem1517486 (c : real) (d : real) : (term99 c d) = term103.
Proof. exact (TRANS (@lem1517460 c d) (@lem1517485 c d)). Qed.
Lemma lem1517487 : term103 = term90.
Proof. exact (@lem1483448 term90). Qed.
Lemma lem1517488 (c : real) (d : real) : (term99 c d) = term90.
Proof. exact (TRANS (@lem1517486 c d) (@lem1517487)). Qed.
Lemma lem1517489 (b : real) (c : real) (d : real) : (term98 b c d) = term103.
Proof. exact (MK_COMB (@lem1517459 b) (@lem1517488 c d)). Qed.
Lemma lem1517490 (b : real) (c : real) (d : real) : (term97 b c d) = term103.
Proof. exact (TRANS (@lem1517446 b c d) (@lem1517489 b c d)). Qed.
Lemma lem1517491 : term103 = term90.
Proof. exact (@lem1483448 term90). Qed.
Lemma lem1517492 (b : real) (c : real) (d : real) : (term97 b c d) = term90.
Proof. exact (TRANS (@lem1517490 b c d) (@lem1517491)). Qed.
Lemma lem1517493 (a : real) (b : real) (c : real) (d : real) : (term86 a b c d) = term103.
Proof. exact (MK_COMB (@lem1517445 a) (@lem1517492 b c d)). Qed.
Lemma lem1517494 (a : real) (b : real) (c : real) (d : real) : (term85 a b c d) = term103.
Proof. exact (TRANS (@lem1517432 a b c d) (@lem1517493 a b c d)). Qed.
Lemma lem1517495 : term103 = term90.
Proof. exact (@lem1483448 term90). Qed.
Lemma lem1517496 (a : real) (b : real) (c : real) (d : real) : (term85 a b c d) = term90.
Proof. exact (TRANS (@lem1517494 a b c d) (@lem1517495)). Qed.
Lemma lem1517497 (a : real) (b : real) (c : real) (d : real) : (term60 a b c d) = term90.
Proof. exact (TRANS (@lem1517431 a b c d) (@lem1517496 a b c d)). Qed.
Lemma lem1517498 (a : real) (b : real) (c : real) (d : real) : (term59 a b c d) = term90.
Proof. exact (TRANS (@lem1517380 a b c d) (@lem1517497 a b c d)). Qed.
Lemma lem1517499 (a : real) (c : real) (b : real) (d : real) : (term58 a c b d) = term90.
Proof. exact (TRANS (@lem1517379 a b c d) (@lem1517498 a b c d)). Qed.
Lemma lem1517500 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1517501 (a : real) (c : real) (b : real) (d : real) : (term104 a c b d) = term105.
Proof. exact (MK_COMB (@lem1517500) (@lem1517499 a c b d)). Qed.
Lemma lem1517502 : term105 = term106.
Proof. exact (@lem1483512 term90). Qed.
Lemma lem1517504 (x : nat) : (term107 x) = term90.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1517505 : term106 = term90.
Proof. exact (@lem1517504 term73). Qed.
Lemma lem1517506 : term105 = term90.
Proof. exact (TRANS (@lem1517502) (@lem1517505)). Qed.
Lemma lem1517507 (a : real) (c : real) (b : real) (d : real) : (term108 a c b d) = (term108 a c b d).
Proof. exact (eq_refl (term108 a c b d)). Qed.
Lemma lem1517508 (a : real) (c : real) (b : real) (d : real) : ((term104 a c b d) = term105) = ((term104 a c b d) = term90).
Proof. exact (MK_COMB (@lem1517507 a c b d) (@lem1517506)). Qed.
Lemma lem1517509 (a : real) (c : real) (b : real) (d : real) : (term104 a c b d) = term90.
Proof. exact (EQ_MP (@lem1517508 a c b d) (@lem1517501 a c b d)). Qed.
Lemma lem1517510 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1517511 (a : real) (c : real) (b : real) (d : real) : (term109 a c b d) = term110.
Proof. exact (MK_COMB (@lem1517510) (@lem1517509 a c b d)). Qed.
Lemma lem1517512 : term90 = term90.
Proof. exact (eq_refl term90). Qed.
Lemma lem1517513 (a : real) (c : real) (b : real) (d : real) : (term111 a c b d) = term112.
Proof. exact (MK_COMB (@lem1517511 a c b d) (@lem1517512)). Qed.
Lemma lem1517514 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1517515 (a : real) (c : real) (b : real) (d : real) : (term113 a c b d) = term110.
Proof. exact (MK_COMB (@lem1517514) (@lem1517499 a c b d)). Qed.
Lemma lem1517516 : term90 = term90.
Proof. exact (eq_refl term90). Qed.
Lemma lem1517517 (a : real) (c : real) (b : real) (d : real) : (term114 a c b d) = term112.
Proof. exact (MK_COMB (@lem1517515 a c b d) (@lem1517516)). Qed.
Lemma lem1517518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1517519 (a : real) (c : real) (b : real) (d : real) : (term115 a c b d) = term116.
Proof. exact (MK_COMB (@lem1517518) (@lem1517517 a c b d)). Qed.
Lemma lem1517520 (a : real) (c : real) (b : real) (d : real) : (term40 a c b d) = term117.
Proof. exact (MK_COMB (@lem1517519 a c b d) (@lem1517513 a c b d)). Qed.
Lemma lem1517521 (a : real) (c : real) (b : real) (d : real) : (term9 a c b d) = term117.
Proof. exact (TRANS (@lem1517302 a c b d) (@lem1517520 a c b d)). Qed.
Lemma lem1517522 (a : real) (c : real) (b : real) : (term11 a c b) = term118.
Proof. exact (fun_ext (fun d : real => @lem1517521 a c b d)). Qed.
Lemma lem1517523 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517524 (a : real) (c : real) (b : real) : (term12 a c b) = term119.
Proof. exact (MK_COMB (@lem1517523) (@lem1517522 a c b)). Qed.
Lemma lem1517525 (a : real) (b : real) : (term20 a b) = term120.
Proof. exact (fun_ext (fun c : real => @lem1517524 a c b)). Qed.
Lemma lem1517526 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517527 (a : real) (b : real) : (term21 a b) = term121.
Proof. exact (MK_COMB (@lem1517526) (@lem1517525 a b)). Qed.
Lemma lem1517528 (a : real) : (term29 a) = term122.
Proof. exact (fun_ext (fun b : real => @lem1517527 a b)). Qed.
Lemma lem1517529 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517530 (a : real) : (term30 a) = term123.
Proof. exact (MK_COMB (@lem1517529) (@lem1517528 a)). Qed.
Lemma lem1517531 : term38 = term124.
Proof. exact (fun_ext (fun a : real => @lem1517530 a)). Qed.
Lemma lem1517532 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517533 : term39 = term125.
Proof. exact (MK_COMB (@lem1517532) (@lem1517531)). Qed.
Lemma lem1517534 : term31 = term125.
Proof. exact (TRANS (@lem1517301) (@lem1517533)). Qed.
Lemma lem1517536 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1517537 (t : Prop) : (term127 t) = t.
Proof. exact (@lem1517536 real t). Qed.
Lemma lem1517538 : term125 = term123.
Proof. exact (@lem1517537 term123). Qed.
Lemma lem1517540 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1517541 (t : Prop) : (term127 t) = t.
Proof. exact (@lem1517540 real t). Qed.
Lemma lem1517542 : term123 = term121.
Proof. exact (@lem1517541 term121). Qed.
Lemma lem1517544 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1517545 (t : Prop) : (term127 t) = t.
Proof. exact (@lem1517544 real t). Qed.
Lemma lem1517546 : term121 = term119.
Proof. exact (@lem1517545 term119). Qed.
Lemma lem1517548 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1517549 (P : real -> Prop) (Q : real -> Prop) : (term130 P Q) = (term131 P Q).
Proof. exact (@lem1517548 real P Q). Qed.
Lemma lem1517550 : term132 = term133.
Proof. exact (@lem1517549 term134 term134). Qed.
Lemma lem1517551 (d : real) : (term135 d) = term112.
Proof. exact (eq_refl (term135 d)). Qed.
Lemma lem1517552 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1517553 (d : real) : (term136 d) = term116.
Proof. exact (MK_COMB (@lem1517552) (@lem1517551 d)). Qed.
Lemma lem1517554 (d : real) : (term135 d) = term112.
Proof. exact (eq_refl (term135 d)). Qed.
Lemma lem1517555 (d : real) : (term137 d) = term117.
Proof. exact (MK_COMB (@lem1517553 d) (@lem1517554 d)). Qed.
Lemma lem1517556 : term138 = term118.
Proof. exact (fun_ext (fun d : real => @lem1517555 d)). Qed.
Lemma lem1517557 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517558 : term132 = term119.
Proof. exact (MK_COMB (@lem1517557) (@lem1517556)). Qed.
Lemma lem1517559 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1517560 : term139 = term140.
Proof. exact (MK_COMB (@lem1517559) (@lem1517558)). Qed.
Lemma lem1517561 (d : real) : (term135 d) = term112.
Proof. exact (eq_refl (term135 d)). Qed.
Lemma lem1517562 : term141 = term134.
Proof. exact (fun_ext (fun d : real => @lem1517561 d)). Qed.
Lemma lem1517563 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517564 : term142 = term143.
Proof. exact (MK_COMB (@lem1517563) (@lem1517562)). Qed.
Lemma lem1517565 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1517566 : term144 = term145.
Proof. exact (MK_COMB (@lem1517565) (@lem1517564)). Qed.
Lemma lem1517567 (d : real) : (term135 d) = term112.
Proof. exact (eq_refl (term135 d)). Qed.
Lemma lem1517568 : term141 = term134.
Proof. exact (fun_ext (fun d : real => @lem1517567 d)). Qed.
Lemma lem1517569 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517570 : term142 = term143.
Proof. exact (MK_COMB (@lem1517569) (@lem1517568)). Qed.
Lemma lem1517571 : term133 = term146.
Proof. exact (MK_COMB (@lem1517566) (@lem1517570)). Qed.
Lemma lem1517572 : (term132 = term133) = (term119 = term146).
Proof. exact (MK_COMB (@lem1517560) (@lem1517571)). Qed.
Lemma lem1517573 : term119 = term146.
Proof. exact (EQ_MP (@lem1517572) (@lem1517550)). Qed.
Lemma lem1517574 : term121 = term146.
Proof. exact (TRANS (@lem1517546) (@lem1517573)). Qed.
Lemma lem1517575 : term123 = term146.
Proof. exact (TRANS (@lem1517542) (@lem1517574)). Qed.
Lemma lem1517576 : term125 = term146.
Proof. exact (TRANS (@lem1517538) (@lem1517575)). Qed.
Lemma lem1517578 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1517579 (t : Prop) : (term127 t) = t.
Proof. exact (@lem1517578 real t). Qed.
Lemma lem1517580 : term143 = term112.
Proof. exact (@lem1517579 term112). Qed.
Lemma lem1517581 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1517582 : term145 = term116.
Proof. exact (MK_COMB (@lem1517581) (@lem1517580)). Qed.
Lemma lem1517584 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1517585 (t : Prop) : (term127 t) = t.
Proof. exact (@lem1517584 real t). Qed.
Lemma lem1517586 : term143 = term112.
Proof. exact (@lem1517585 term112). Qed.
Lemma lem1517587 : term146 = term117.
Proof. exact (MK_COMB (@lem1517582) (@lem1517586)). Qed.
Lemma lem1517590 : term125 = term117.
Proof. exact (TRANS (@lem1517576) (@lem1517587)). Qed.
Lemma lem1517599 : term31 = term117.
Proof. exact (TRANS (@lem1517534) (@lem1517590)). Qed.
Lemma lem1517609 (h1 : term117) : term117.
Proof. exact (h1). Qed.
Lemma lem1517610 (h1 : term112) : term112.
Proof. exact (h1). Qed.
Lemma lem1517612 (n : nat) (m : nat) : (term147 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1517613 : term112 = term148.
Proof. exact (@lem1517612 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1517614 : term148 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1517615 : term112 = False.
Proof. exact (TRANS (@lem1517613) (@lem1517614)). Qed.
Lemma lem1517616 (h1 : term112) : False.
Proof. exact (EQ_MP (@lem1517615) (@lem1517610 h1)). Qed.
Lemma lem1517617 (h1 : term112) : term112.
Proof. exact (h1). Qed.
Lemma lem1517619 (n : nat) (m : nat) : (term147 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1517620 : term112 = term148.
Proof. exact (@lem1517619 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1517621 : term148 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1517622 : term112 = False.
Proof. exact (TRANS (@lem1517620) (@lem1517621)). Qed.
Lemma lem1517623 (h1 : term112) : False.
Proof. exact (EQ_MP (@lem1517622) (@lem1517617 h1)). Qed.
Lemma lem1517624 (h1 : term117) : False.
Proof. exact (or_elim (@lem1517609 h1) (fun h0 : term112 => @lem1517616 h0) (fun h0 : term112 => @lem1517623 h0)). Qed.
Lemma lem1517626 (h1 : term117) : term117.
Proof. exact (h1). Qed.
Lemma lem1517627 (h1 : term117) : term117 = False.
Proof. exact (prop_ext (fun h2 : term117 => @lem1517624 h1) (fun h2 : False => @lem1517626 h1)). Qed.
Lemma lem1517628 (h1 : term117) : False.
Proof. exact (EQ_MP (@lem1517627 h1) (@lem1517626 h1)). Qed.
Lemma lem1517629 (h1 : term31) : term31.
Proof. exact (h1). Qed.
Lemma lem1517630 (h1 : term31) : term117.
Proof. exact (EQ_MP (@lem1517599) (@lem1517629 h1)). Qed.
Lemma lem1517631 (h1 : term31) : term117 = False.
Proof. exact (prop_ext (fun h2 : term117 => @lem1517628 h2) (fun h2 : False => @lem1517630 h1)). Qed.
Lemma lem1517632 (h1 : term31) : False.
Proof. exact (EQ_MP (@lem1517631 h1) (@lem1517630 h1)). Qed.
Lemma lem1517633 : term149.
Proof. exact (fun h0 : term31 => @lem1517632 h0). Qed.
Lemma lem1517634 : term150.
Proof. exact (@lem1386578 term151). Qed.
Lemma lem1517635 : term151.
Proof. exact (@lem1517634 (@lem1517633)). Qed.
