Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_FINITE_AVOID_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import LT_spec.
Require Import NOT_LT_spec.
Require Import num_FINITE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16464_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem4624131 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4624132 : term1 = term2.
Proof. exact (@lem4624131 term1). Qed.
Lemma lem4624133 : term2 = term1.
Proof. exact (SYM (@lem4624132)). Qed.
Lemma lem4624134 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem4624137 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem4624138 : term5.
Proof. exact (fun h0 : term4 => @lem4624137 h0). Qed.
Lemma lem4624139 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem4624140 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem4624141 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem4624139 h2 (@lem4624140 h1)). Qed.
Lemma lem4624142 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem4624141 h1 h0). Qed.
Lemma lem4624143 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem4624144 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem4624142 h1 (@lem4624143 h2)). Qed.
Lemma lem4624145 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem4624144 h0 h1). Qed.
Lemma lem4624146 : term7.
Proof. exact (fun h0 : term5 => @lem4624145 h0). Qed.
Lemma lem4624149 : term5.
Proof. exact (@lem4624146 (@lem4624138)). Qed.
Lemma lem4624181 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem4624182 (m : nat) : ((term8 m) = False) = (term9 m).
Proof. exact (@lem4624181 (term8 m)). Qed.
Lemma lem4624183 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem4624182 m)). Qed.
Lemma lem4624184 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624185 : term12 = term13.
Proof. exact (MK_COMB (@lem4624184) (@lem4624183)). Qed.
Lemma lem4624190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4624191 : term14 = term15.
Proof. exact (MK_COMB (@lem4624190) (@lem4624185)). Qed.
Lemma lem4624202 : term16 = term16.
Proof. exact (eq_refl term16). Qed.
Lemma lem4624203 : term17 = term18.
Proof. exact (MK_COMB (@lem4624191) (@lem4624202)). Qed.
Lemma lem4624206 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4624207 : term19 = term20.
Proof. exact (MK_COMB (@lem4624206) (@lem4624203)). Qed.
Lemma lem4624209 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4624210 : term21 = term22.
Proof. exact (@lem4624209 term23). Qed.
Lemma lem4624225 : term24 = term25.
Proof. exact (MK_COMB (@lem4624207) (@lem4624210)). Qed.
Lemma lem4624228 : term26 = term26.
Proof. exact (eq_refl term26). Qed.
Lemma lem4624229 : term27 = term28.
Proof. exact (MK_COMB (@lem4624228) (@lem4624225)). Qed.
Lemma lem4624232 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem4624239 : term4 = term30.
Proof. exact (MK_COMB (@lem4624232) (@lem4624229)). Qed.
Lemma lem4624244 (s : nat -> Prop) (x : nat) (a : nat) : (term31 s x a) = (term31 s x a).
Proof. exact (eq_refl (term31 s x a)). Qed.
Lemma lem4624245 (s : nat -> Prop) (a : nat) : (term32 s a) = (term32 s a).
Proof. exact (fun_ext (fun x : nat => @lem4624244 s x a)). Qed.
Lemma lem4624246 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624247 (s : nat -> Prop) (a : nat) : (term33 s a) = (term33 s a).
Proof. exact (MK_COMB (@lem4624246) (@lem4624245 s a)). Qed.
Lemma lem4624248 (s : nat -> Prop) : (term34 s) = (term34 s).
Proof. exact (fun_ext (fun a : nat => @lem4624247 s a)). Qed.
Lemma lem4624249 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4624250 (s : nat -> Prop) : (term35 s) = (term35 s).
Proof. exact (MK_COMB (@lem4624249) (@lem4624248 s)). Qed.
Lemma lem4624253 (s : nat -> Prop) : (term36 s) = (term36 s).
Proof. exact (eq_refl (term36 s)). Qed.
Lemma lem4624254 (s : nat -> Prop) : ((@FINITE nat s) = (term35 s)) = ((@FINITE nat s) = (term35 s)).
Proof. exact (MK_COMB (@lem4624253 s) (@lem4624250 s)). Qed.
Lemma lem4624255 : term37 = term37.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4624254 s)). Qed.
Lemma lem4624256 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4624257 : term23 = term23.
Proof. exact (MK_COMB (@lem4624256) (@lem4624255)). Qed.
Lemma lem4624258 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4624259 : term22 = term22.
Proof. exact (MK_COMB (@lem4624258) (@lem4624257)). Qed.
Lemma lem4624268 (m : nat) (n : nat) : ((term38 m n) = (term39 m n)) = ((term38 m n) = (term39 m n)).
Proof. exact (eq_refl ((term38 m n) = (term39 m n))). Qed.
Lemma lem4624269 (m : nat) : (term40 m) = (term40 m).
Proof. exact (fun_ext (fun n : nat => @lem4624268 m n)). Qed.
Lemma lem4624270 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624271 (m : nat) : (term41 m) = (term41 m).
Proof. exact (MK_COMB (@lem4624270) (@lem4624269 m)). Qed.
Lemma lem4624272 : term42 = term42.
Proof. exact (fun_ext (fun m : nat => @lem4624271 m)). Qed.
Lemma lem4624273 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624274 : term16 = term16.
Proof. exact (MK_COMB (@lem4624273) (@lem4624272)). Qed.
Lemma lem4624277 (m : nat) : (term9 m) = (term9 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem4624278 : term11 = term11.
Proof. exact (fun_ext (fun m : nat => @lem4624277 m)). Qed.
Lemma lem4624279 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624280 : term13 = term13.
Proof. exact (MK_COMB (@lem4624279) (@lem4624278)). Qed.
Lemma lem4624281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4624282 : term15 = term15.
Proof. exact (MK_COMB (@lem4624281) (@lem4624280)). Qed.
Lemma lem4624283 : term18 = term18.
Proof. exact (MK_COMB (@lem4624282) (@lem4624274)). Qed.
Lemma lem4624284 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4624285 : term20 = term20.
Proof. exact (MK_COMB (@lem4624284) (@lem4624283)). Qed.
Lemma lem4624286 : term25 = term25.
Proof. exact (MK_COMB (@lem4624285) (@lem4624259)). Qed.
Lemma lem4624293 (n : nat) (m : nat) : ((term43 m n) = (Peano.le n m)) = ((term43 m n) = (Peano.le n m)).
Proof. exact (eq_refl ((term43 m n) = (Peano.le n m))). Qed.
Lemma lem4624294 (m : nat) : (term44 m) = (term44 m).
Proof. exact (fun_ext (fun n : nat => @lem4624293 n m)). Qed.
Lemma lem4624295 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624296 (m : nat) : (term45 m) = (term45 m).
Proof. exact (MK_COMB (@lem4624295) (@lem4624294 m)). Qed.
Lemma lem4624297 : term46 = term46.
Proof. exact (fun_ext (fun m : nat => @lem4624296 m)). Qed.
Lemma lem4624298 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624299 : term47 = term47.
Proof. exact (MK_COMB (@lem4624298) (@lem4624297)). Qed.
Lemma lem4624300 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4624301 : term26 = term26.
Proof. exact (MK_COMB (@lem4624300) (@lem4624299)). Qed.
Lemma lem4624302 : term28 = term28.
Proof. exact (MK_COMB (@lem4624301) (@lem4624286)). Qed.
Lemma lem4624305 (a : nat) (s : nat -> Prop) : (term48 a s) = (term48 a s).
Proof. exact (eq_refl (term48 a s)). Qed.
Lemma lem4624306 (s : nat -> Prop) : (term49 s) = (term49 s).
Proof. exact (fun_ext (fun a : nat => @lem4624305 a s)). Qed.
Lemma lem4624307 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4624308 (s : nat -> Prop) : (term50 s) = (term50 s).
Proof. exact (MK_COMB (@lem4624307) (@lem4624306 s)). Qed.
Lemma lem4624311 (s : nat -> Prop) : (term51 s) = (term51 s).
Proof. exact (eq_refl (term51 s)). Qed.
Lemma lem4624312 (s : nat -> Prop) : (term52 s) = (term52 s).
Proof. exact (MK_COMB (@lem4624311 s) (@lem4624308 s)). Qed.
Lemma lem4624313 : term53 = term53.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4624312 s)). Qed.
Lemma lem4624314 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4624315 : term1 = term1.
Proof. exact (MK_COMB (@lem4624314) (@lem4624313)). Qed.
Lemma lem4624316 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4624317 : term3 = term3.
Proof. exact (MK_COMB (@lem4624316) (@lem4624315)). Qed.
Lemma lem4624318 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4624319 : term29 = term29.
Proof. exact (MK_COMB (@lem4624318) (@lem4624317)). Qed.
Lemma lem4624320 : term30 = term30.
Proof. exact (MK_COMB (@lem4624319) (@lem4624302)). Qed.
Lemma lem4624397 : term4 = term30.
Proof. exact (TRANS (@lem4624239) (@lem4624320)). Qed.
Lemma lem4624398 : term30 = term4.
Proof. exact (SYM (@lem4624397)). Qed.
Lemma lem4624399 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem4624400 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem4624401 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem4624402 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem4624406 (a : nat) (s : nat -> Prop) : (term54 a s) = (@IN nat a s).
Proof. exact (@lem16933 (@IN nat a s)). Qed.
Lemma lem4624407 (P : nat -> Prop) : (term55 P) = (term56 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem4624408 (s : nat -> Prop) : (term57 s) = (term58 s).
Proof. exact (@lem4624407 (term49 s)). Qed.
Lemma lem4624409 (a : nat) (s : nat -> Prop) : (term59 s a) = (term48 a s).
Proof. exact (eq_refl (term59 s a)). Qed.
Lemma lem4624410 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4624411 (a : nat) (s : nat -> Prop) : (term60 s a) = (term54 a s).
Proof. exact (MK_COMB (@lem4624410) (@lem4624409 a s)). Qed.
Lemma lem4624412 (a : nat) (s : nat -> Prop) : (term60 s a) = (@IN nat a s).
Proof. exact (TRANS (@lem4624411 a s) (@lem4624406 a s)). Qed.
Lemma lem4624413 (s : nat -> Prop) : (term61 s) = (term62 s).
Proof. exact (fun_ext (fun a : nat => @lem4624412 a s)). Qed.
Lemma lem4624414 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624415 (s : nat -> Prop) : (term58 s) = (term63 s).
Proof. exact (MK_COMB (@lem4624414) (@lem4624413 s)). Qed.
Lemma lem4624416 (s : nat -> Prop) : (term57 s) = (term63 s).
Proof. exact (TRANS (@lem4624408 s) (@lem4624415 s)). Qed.
Lemma lem4624418 (s : nat -> Prop) : (term64 s) = (term64 s).
Proof. exact (eq_refl (term64 s)). Qed.
Lemma lem4624419 (s : nat -> Prop) : (term65 s) = (term66 s).
Proof. exact (MK_COMB (@lem4624418 s) (@lem4624416 s)). Qed.
Lemma lem4624420 (s : nat -> Prop) : (term67 s) = (term65 s).
Proof. exact (@lem17362 (@FINITE nat s) (term50 s)). Qed.
Lemma lem4624421 (s : nat -> Prop) : (term67 s) = (term66 s).
Proof. exact (TRANS (@lem4624420 s) (@lem4624419 s)). Qed.
Lemma lem4624422 (P : type993) : (term68 P) = (term69 P).
Proof. exact (@lem18392 (nat -> Prop) P). Qed.
Lemma lem4624423 : term3 = term70.
Proof. exact (@lem4624422 term53). Qed.
Lemma lem4624424 (s : nat -> Prop) : (term71 s) = (term52 s).
Proof. exact (eq_refl (term71 s)). Qed.
Lemma lem4624425 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4624426 (s : nat -> Prop) : (term72 s) = (term67 s).
Proof. exact (MK_COMB (@lem4624425) (@lem4624424 s)). Qed.
Lemma lem4624427 (s : nat -> Prop) : (term72 s) = (term66 s).
Proof. exact (TRANS (@lem4624426 s) (@lem4624421 s)). Qed.
Lemma lem4624428 : term73 = term74.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4624427 s)). Qed.
Lemma lem4624429 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem4624430 : term70 = term75.
Proof. exact (MK_COMB (@lem4624429) (@lem4624428)). Qed.
Lemma lem4624467 : term3 = term75.
Proof. exact (TRANS (@lem4624423) (@lem4624430)). Qed.
Lemma lem4624468 (h1 : term3) : term75.
Proof. exact (EQ_MP (@lem4624467) (@lem4624399 h1)). Qed.
Lemma lem4624472 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (@lem16933 (Peano.lt m n)). Qed.
Lemma lem4624474 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem4624475 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4624476 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem4624475) (@lem4624472 m n)). Qed.
Lemma lem4624477 (n : nat) (m : nat) : (term79 n m) = (term80 n m).
Proof. exact (MK_COMB (@lem4624476 m n) (@lem4624474 n m)). Qed.
Lemma lem4624482 (n : nat) (m : nat) : (term81 n m) = (term81 n m).
Proof. exact (eq_refl (term81 n m)). Qed.
Lemma lem4624483 (n : nat) (m : nat) : (term82 n m) = (term83 n m).
Proof. exact (MK_COMB (@lem4624482 n m) (@lem4624477 n m)). Qed.
Lemma lem4624484 (n : nat) (m : nat) : ((term43 m n) = (Peano.le n m)) = (term82 n m).
Proof. exact (@lem17784 (term43 m n) (Peano.le n m)). Qed.
Lemma lem4624485 (n : nat) (m : nat) : ((term43 m n) = (Peano.le n m)) = (term83 n m).
Proof. exact (TRANS (@lem4624484 n m) (@lem4624483 n m)). Qed.
Lemma lem4624486 (m : nat) : (term44 m) = (term84 m).
Proof. exact (fun_ext (fun n : nat => @lem4624485 n m)). Qed.
Lemma lem4624487 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624488 (m : nat) : (term45 m) = (term85 m).
Proof. exact (MK_COMB (@lem4624487) (@lem4624486 m)). Qed.
Lemma lem4624489 : term46 = term86.
Proof. exact (fun_ext (fun m : nat => @lem4624488 m)). Qed.
Lemma lem4624490 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624491 : term47 = term87.
Proof. exact (MK_COMB (@lem4624490) (@lem4624489)). Qed.
Lemma lem4624497 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4624498 (P : nat -> Prop) (Q : nat -> Prop) : (term90 P Q) = (term91 P Q).
Proof. exact (@lem4624497 nat P Q). Qed.
Lemma lem4624499 (m : nat) : (term92 m) = (term93 m).
Proof. exact (@lem4624498 (term94 m) (term95 m)). Qed.
Lemma lem4624500 (n : nat) (m : nat) : (term96 m n) = (term97 n m).
Proof. exact (eq_refl (term96 m n)). Qed.
Lemma lem4624501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4624502 (n : nat) (m : nat) : (term98 m n) = (term81 n m).
Proof. exact (MK_COMB (@lem4624501) (@lem4624500 n m)). Qed.
Lemma lem4624503 (n : nat) (m : nat) : (term99 m n) = (term80 n m).
Proof. exact (eq_refl (term99 m n)). Qed.
Lemma lem4624504 (n : nat) (m : nat) : (term100 m n) = (term83 n m).
Proof. exact (MK_COMB (@lem4624502 n m) (@lem4624503 n m)). Qed.
Lemma lem4624505 (m : nat) : (term101 m) = (term84 m).
Proof. exact (fun_ext (fun n : nat => @lem4624504 n m)). Qed.
Lemma lem4624506 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624507 (m : nat) : (term92 m) = (term85 m).
Proof. exact (MK_COMB (@lem4624506) (@lem4624505 m)). Qed.
Lemma lem4624508 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4624509 (m : nat) : (term102 m) = (term103 m).
Proof. exact (MK_COMB (@lem4624508) (@lem4624507 m)). Qed.
Lemma lem4624510 (n : nat) (m : nat) : (term96 m n) = (term97 n m).
Proof. exact (eq_refl (term96 m n)). Qed.
Lemma lem4624511 (m : nat) : (term104 m) = (term94 m).
Proof. exact (fun_ext (fun n : nat => @lem4624510 n m)). Qed.
Lemma lem4624512 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624513 (m : nat) : (term105 m) = (term106 m).
Proof. exact (MK_COMB (@lem4624512) (@lem4624511 m)). Qed.
Lemma lem4624514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4624515 (m : nat) : (term107 m) = (term108 m).
Proof. exact (MK_COMB (@lem4624514) (@lem4624513 m)). Qed.
Lemma lem4624516 (n : nat) (m : nat) : (term99 m n) = (term80 n m).
Proof. exact (eq_refl (term99 m n)). Qed.
Lemma lem4624517 (m : nat) : (term109 m) = (term95 m).
Proof. exact (fun_ext (fun n : nat => @lem4624516 n m)). Qed.
Lemma lem4624518 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624519 (m : nat) : (term110 m) = (term111 m).
Proof. exact (MK_COMB (@lem4624518) (@lem4624517 m)). Qed.
Lemma lem4624520 (m : nat) : (term93 m) = (term112 m).
Proof. exact (MK_COMB (@lem4624515 m) (@lem4624519 m)). Qed.
Lemma lem4624521 (m : nat) : ((term92 m) = (term93 m)) = ((term85 m) = (term112 m)).
Proof. exact (MK_COMB (@lem4624509 m) (@lem4624520 m)). Qed.
Lemma lem4624522 (m : nat) : (term85 m) = (term112 m).
Proof. exact (EQ_MP (@lem4624521 m) (@lem4624499 m)). Qed.
Lemma lem4624619 : term86 = term113.
Proof. exact (fun_ext (fun m : nat => @lem4624522 m)). Qed.
Lemma lem4624620 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624621 : term87 = term114.
Proof. exact (MK_COMB (@lem4624620) (@lem4624619)). Qed.
Lemma lem4624623 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4624624 (P : nat -> Prop) (Q : nat -> Prop) : (term90 P Q) = (term91 P Q).
Proof. exact (@lem4624623 nat P Q). Qed.
Lemma lem4624625 : term115 = term116.
Proof. exact (@lem4624624 term117 term118). Qed.
Lemma lem4624626 (m : nat) : (term119 m) = (term106 m).
Proof. exact (eq_refl (term119 m)). Qed.
Lemma lem4624627 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4624628 (m : nat) : (term120 m) = (term108 m).
Proof. exact (MK_COMB (@lem4624627) (@lem4624626 m)). Qed.
Lemma lem4624629 (m : nat) : (term121 m) = (term111 m).
Proof. exact (eq_refl (term121 m)). Qed.
Lemma lem4624630 (m : nat) : (term122 m) = (term112 m).
Proof. exact (MK_COMB (@lem4624628 m) (@lem4624629 m)). Qed.
Lemma lem4624631 : term123 = term113.
Proof. exact (fun_ext (fun m : nat => @lem4624630 m)). Qed.
Lemma lem4624632 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624633 : term115 = term114.
Proof. exact (MK_COMB (@lem4624632) (@lem4624631)). Qed.
Lemma lem4624634 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4624635 : term124 = term125.
Proof. exact (MK_COMB (@lem4624634) (@lem4624633)). Qed.
Lemma lem4624636 (m : nat) : (term119 m) = (term106 m).
Proof. exact (eq_refl (term119 m)). Qed.
Lemma lem4624637 : term126 = term117.
Proof. exact (fun_ext (fun m : nat => @lem4624636 m)). Qed.
Lemma lem4624638 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624639 : term127 = term128.
Proof. exact (MK_COMB (@lem4624638) (@lem4624637)). Qed.
Lemma lem4624640 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4624641 : term129 = term130.
Proof. exact (MK_COMB (@lem4624640) (@lem4624639)). Qed.
Lemma lem4624642 (m : nat) : (term121 m) = (term111 m).
Proof. exact (eq_refl (term121 m)). Qed.
Lemma lem4624643 : term131 = term118.
Proof. exact (fun_ext (fun m : nat => @lem4624642 m)). Qed.
Lemma lem4624644 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624645 : term132 = term133.
Proof. exact (MK_COMB (@lem4624644) (@lem4624643)). Qed.
Lemma lem4624646 : term116 = term134.
Proof. exact (MK_COMB (@lem4624641) (@lem4624645)). Qed.
Lemma lem4624647 : (term115 = term116) = (term114 = term134).
Proof. exact (MK_COMB (@lem4624635) (@lem4624646)). Qed.
Lemma lem4624648 : term114 = term134.
Proof. exact (EQ_MP (@lem4624647) (@lem4624625)). Qed.
Lemma lem4624755 : term87 = term134.
Proof. exact (TRANS (@lem4624621) (@lem4624648)). Qed.
Lemma lem4624756 : term47 = term134.
Proof. exact (TRANS (@lem4624491) (@lem4624755)). Qed.
Lemma lem4624757 (h1 : term47) : term134.
Proof. exact (EQ_MP (@lem4624756) (@lem4624400 h1)). Qed.
Lemma lem4624758 (m : nat) : (term9 m) = (term9 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem4624759 : term11 = term11.
Proof. exact (fun_ext (fun m : nat => @lem4624758 m)). Qed.
Lemma lem4624760 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624761 : term13 = term13.
Proof. exact (MK_COMB (@lem4624760) (@lem4624759)). Qed.
Lemma lem4624772 (m : nat) (n : nat) : (term135 m n) = (term136 m n).
Proof. exact (@lem17160 (m = n) (Peano.lt m n)). Qed.
Lemma lem4624778 (m : nat) (n : nat) : (term137 m n) = (term137 m n).
Proof. exact (eq_refl (term137 m n)). Qed.
Lemma lem4624780 (m : nat) (n : nat) : (term138 m n) = (term138 m n).
Proof. exact (eq_refl (term138 m n)). Qed.
Lemma lem4624781 (m : nat) (n : nat) : (term139 m n) = (term140 m n).
Proof. exact (MK_COMB (@lem4624780 m n) (@lem4624772 m n)). Qed.
Lemma lem4624782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4624783 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (MK_COMB (@lem4624782) (@lem4624781 m n)). Qed.
Lemma lem4624784 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (MK_COMB (@lem4624783 m n) (@lem4624778 m n)). Qed.
Lemma lem4624785 (m : nat) (n : nat) : ((term38 m n) = (term39 m n)) = (term143 m n).
Proof. exact (@lem17784 (term38 m n) (term39 m n)). Qed.
Lemma lem4624786 (m : nat) (n : nat) : ((term38 m n) = (term39 m n)) = (term144 m n).
Proof. exact (TRANS (@lem4624785 m n) (@lem4624784 m n)). Qed.
Lemma lem4624787 (m : nat) : (term40 m) = (term145 m).
Proof. exact (fun_ext (fun n : nat => @lem4624786 m n)). Qed.
Lemma lem4624788 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624789 (m : nat) : (term41 m) = (term146 m).
Proof. exact (MK_COMB (@lem4624788) (@lem4624787 m)). Qed.
Lemma lem4624790 : term42 = term147.
Proof. exact (fun_ext (fun m : nat => @lem4624789 m)). Qed.
Lemma lem4624791 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624792 : term16 = term148.
Proof. exact (MK_COMB (@lem4624791) (@lem4624790)). Qed.
Lemma lem4624793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4624794 : term15 = term15.
Proof. exact (MK_COMB (@lem4624793) (@lem4624761)). Qed.
Lemma lem4624795 : term18 = term149.
Proof. exact (MK_COMB (@lem4624794) (@lem4624792)). Qed.
Lemma lem4624805 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4624806 (P : nat -> Prop) (Q : nat -> Prop) : (term90 P Q) = (term91 P Q).
Proof. exact (@lem4624805 nat P Q). Qed.
Lemma lem4624807 (m : nat) : (term150 m) = (term151 m).
Proof. exact (@lem4624806 (term152 m) (term153 m)). Qed.
Lemma lem4624808 (m : nat) (n : nat) : (term154 m n) = (term140 m n).
Proof. exact (eq_refl (term154 m n)). Qed.
Lemma lem4624809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4624810 (m : nat) (n : nat) : (term155 m n) = (term142 m n).
Proof. exact (MK_COMB (@lem4624809) (@lem4624808 m n)). Qed.
Lemma lem4624811 (m : nat) (n : nat) : (term156 m n) = (term137 m n).
Proof. exact (eq_refl (term156 m n)). Qed.
Lemma lem4624812 (m : nat) (n : nat) : (term157 m n) = (term144 m n).
Proof. exact (MK_COMB (@lem4624810 m n) (@lem4624811 m n)). Qed.
Lemma lem4624813 (m : nat) : (term158 m) = (term145 m).
Proof. exact (fun_ext (fun n : nat => @lem4624812 m n)). Qed.
Lemma lem4624814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624815 (m : nat) : (term150 m) = (term146 m).
Proof. exact (MK_COMB (@lem4624814) (@lem4624813 m)). Qed.
Lemma lem4624816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4624817 (m : nat) : (term159 m) = (term160 m).
Proof. exact (MK_COMB (@lem4624816) (@lem4624815 m)). Qed.
Lemma lem4624818 (m : nat) (n : nat) : (term154 m n) = (term140 m n).
Proof. exact (eq_refl (term154 m n)). Qed.
Lemma lem4624819 (m : nat) : (term161 m) = (term152 m).
Proof. exact (fun_ext (fun n : nat => @lem4624818 m n)). Qed.
Lemma lem4624820 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624821 (m : nat) : (term162 m) = (term163 m).
Proof. exact (MK_COMB (@lem4624820) (@lem4624819 m)). Qed.
Lemma lem4624822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4624823 (m : nat) : (term164 m) = (term165 m).
Proof. exact (MK_COMB (@lem4624822) (@lem4624821 m)). Qed.
Lemma lem4624824 (m : nat) (n : nat) : (term156 m n) = (term137 m n).
Proof. exact (eq_refl (term156 m n)). Qed.
Lemma lem4624825 (m : nat) : (term166 m) = (term153 m).
Proof. exact (fun_ext (fun n : nat => @lem4624824 m n)). Qed.
Lemma lem4624826 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624827 (m : nat) : (term167 m) = (term168 m).
Proof. exact (MK_COMB (@lem4624826) (@lem4624825 m)). Qed.
Lemma lem4624828 (m : nat) : (term151 m) = (term169 m).
Proof. exact (MK_COMB (@lem4624823 m) (@lem4624827 m)). Qed.
Lemma lem4624829 (m : nat) : ((term150 m) = (term151 m)) = ((term146 m) = (term169 m)).
Proof. exact (MK_COMB (@lem4624817 m) (@lem4624828 m)). Qed.
Lemma lem4624830 (m : nat) : (term146 m) = (term169 m).
Proof. exact (EQ_MP (@lem4624829 m) (@lem4624807 m)). Qed.
Lemma lem4624927 : term147 = term170.
Proof. exact (fun_ext (fun m : nat => @lem4624830 m)). Qed.
Lemma lem4624928 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624929 : term148 = term171.
Proof. exact (MK_COMB (@lem4624928) (@lem4624927)). Qed.
Lemma lem4624931 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4624932 (P : nat -> Prop) (Q : nat -> Prop) : (term90 P Q) = (term91 P Q).
Proof. exact (@lem4624931 nat P Q). Qed.
Lemma lem4624933 : term172 = term173.
Proof. exact (@lem4624932 term174 term175). Qed.
Lemma lem4624934 (m : nat) : (term176 m) = (term163 m).
Proof. exact (eq_refl (term176 m)). Qed.
Lemma lem4624935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4624936 (m : nat) : (term177 m) = (term165 m).
Proof. exact (MK_COMB (@lem4624935) (@lem4624934 m)). Qed.
Lemma lem4624937 (m : nat) : (term178 m) = (term168 m).
Proof. exact (eq_refl (term178 m)). Qed.
Lemma lem4624938 (m : nat) : (term179 m) = (term169 m).
Proof. exact (MK_COMB (@lem4624936 m) (@lem4624937 m)). Qed.
Lemma lem4624939 : term180 = term170.
Proof. exact (fun_ext (fun m : nat => @lem4624938 m)). Qed.
Lemma lem4624940 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624941 : term172 = term171.
Proof. exact (MK_COMB (@lem4624940) (@lem4624939)). Qed.
Lemma lem4624942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4624943 : term181 = term182.
Proof. exact (MK_COMB (@lem4624942) (@lem4624941)). Qed.
Lemma lem4624944 (m : nat) : (term176 m) = (term163 m).
Proof. exact (eq_refl (term176 m)). Qed.
Lemma lem4624945 : term183 = term174.
Proof. exact (fun_ext (fun m : nat => @lem4624944 m)). Qed.
Lemma lem4624946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624947 : term184 = term185.
Proof. exact (MK_COMB (@lem4624946) (@lem4624945)). Qed.
Lemma lem4624948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4624949 : term186 = term187.
Proof. exact (MK_COMB (@lem4624948) (@lem4624947)). Qed.
Lemma lem4624950 (m : nat) : (term178 m) = (term168 m).
Proof. exact (eq_refl (term178 m)). Qed.
Lemma lem4624951 : term188 = term175.
Proof. exact (fun_ext (fun m : nat => @lem4624950 m)). Qed.
Lemma lem4624952 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624953 : term189 = term190.
Proof. exact (MK_COMB (@lem4624952) (@lem4624951)). Qed.
Lemma lem4624954 : term173 = term191.
Proof. exact (MK_COMB (@lem4624949) (@lem4624953)). Qed.
Lemma lem4624955 : (term172 = term173) = (term171 = term191).
Proof. exact (MK_COMB (@lem4624943) (@lem4624954)). Qed.
Lemma lem4624956 : term171 = term191.
Proof. exact (EQ_MP (@lem4624955) (@lem4624933)). Qed.
Lemma lem4625061 : term148 = term191.
Proof. exact (TRANS (@lem4624929) (@lem4624956)). Qed.
Lemma lem4625062 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem4625065 : term149 = term192.
Proof. exact (MK_COMB (@lem4625062) (@lem4625061)). Qed.
Lemma lem4625066 : term18 = term192.
Proof. exact (TRANS (@lem4624795) (@lem4625065)). Qed.
Lemma lem4625067 (h1 : term18) : term192.
Proof. exact (EQ_MP (@lem4625066) (@lem4624401 h1)). Qed.
Lemma lem4625078 (s : nat -> Prop) (x : nat) (a : nat) : (term193 s x a) = (term194 s x a).
Proof. exact (@lem17362 (@IN nat x s) (Peano.le x a)). Qed.
Lemma lem4625083 (s : nat -> Prop) (x : nat) (a : nat) : (term31 s x a) = (term195 s x a).
Proof. exact (@lem17265 (@IN nat x s) (Peano.le x a)). Qed.
Lemma lem4625084 (P : nat -> Prop) : (term196 P) = (term197 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4625085 (s : nat -> Prop) (a : nat) : (term198 s a) = (term199 s a).
Proof. exact (@lem4625084 (term32 s a)). Qed.
Lemma lem4625086 (s : nat -> Prop) (x : nat) (a : nat) : (term200 s a x) = (term31 s x a).
Proof. exact (eq_refl (term200 s a x)). Qed.
Lemma lem4625087 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4625088 (s : nat -> Prop) (x : nat) (a : nat) : (term201 s a x) = (term193 s x a).
Proof. exact (MK_COMB (@lem4625087) (@lem4625086 s x a)). Qed.
Lemma lem4625089 (s : nat -> Prop) (x : nat) (a : nat) : (term201 s a x) = (term194 s x a).
Proof. exact (TRANS (@lem4625088 s x a) (@lem4625078 s x a)). Qed.
Lemma lem4625090 (s : nat -> Prop) (a : nat) : (term202 s a) = (term203 s a).
Proof. exact (fun_ext (fun x : nat => @lem4625089 s x a)). Qed.
Lemma lem4625091 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4625092 (s : nat -> Prop) (a : nat) : (term199 s a) = (term204 s a).
Proof. exact (MK_COMB (@lem4625091) (@lem4625090 s a)). Qed.
Lemma lem4625093 (s : nat -> Prop) (a : nat) : (term198 s a) = (term204 s a).
Proof. exact (TRANS (@lem4625085 s a) (@lem4625092 s a)). Qed.
Lemma lem4625094 (s : nat -> Prop) (a : nat) : (term32 s a) = (term205 s a).
Proof. exact (fun_ext (fun x : nat => @lem4625083 s x a)). Qed.
Lemma lem4625095 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625096 (s : nat -> Prop) (a : nat) : (term33 s a) = (term206 s a).
Proof. exact (MK_COMB (@lem4625095) (@lem4625094 s a)). Qed.
Lemma lem4625097 (P : nat -> Prop) : (term55 P) = (term56 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem4625098 (s : nat -> Prop) : (term207 s) = (term208 s).
Proof. exact (@lem4625097 (term34 s)). Qed.
Lemma lem4625099 (s : nat -> Prop) (a : nat) : (term209 s a) = (term33 s a).
Proof. exact (eq_refl (term209 s a)). Qed.
Lemma lem4625100 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4625101 (s : nat -> Prop) (a : nat) : (term210 s a) = (term198 s a).
Proof. exact (MK_COMB (@lem4625100) (@lem4625099 s a)). Qed.
Lemma lem4625102 (s : nat -> Prop) (a : nat) : (term210 s a) = (term204 s a).
Proof. exact (TRANS (@lem4625101 s a) (@lem4625093 s a)). Qed.
Lemma lem4625103 (s : nat -> Prop) : (term211 s) = (term212 s).
Proof. exact (fun_ext (fun a : nat => @lem4625102 s a)). Qed.
Lemma lem4625104 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625105 (s : nat -> Prop) : (term208 s) = (term213 s).
Proof. exact (MK_COMB (@lem4625104) (@lem4625103 s)). Qed.
Lemma lem4625106 (s : nat -> Prop) : (term207 s) = (term213 s).
Proof. exact (TRANS (@lem4625098 s) (@lem4625105 s)). Qed.
Lemma lem4625107 (s : nat -> Prop) : (term34 s) = (term214 s).
Proof. exact (fun_ext (fun a : nat => @lem4625096 s a)). Qed.
Lemma lem4625108 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4625109 (s : nat -> Prop) : (term35 s) = (term215 s).
Proof. exact (MK_COMB (@lem4625108) (@lem4625107 s)). Qed.
Lemma lem4625111 (s : nat -> Prop) : (term216 s) = (term216 s).
Proof. exact (eq_refl (term216 s)). Qed.
Lemma lem4625112 (s : nat -> Prop) : (term217 s) = (term218 s).
Proof. exact (MK_COMB (@lem4625111 s) (@lem4625109 s)). Qed.
Lemma lem4625114 (s : nat -> Prop) : (term219 s) = (term219 s).
Proof. exact (eq_refl (term219 s)). Qed.
Lemma lem4625115 (s : nat -> Prop) : (term220 s) = (term221 s).
Proof. exact (MK_COMB (@lem4625114 s) (@lem4625106 s)). Qed.
Lemma lem4625116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4625117 (s : nat -> Prop) : (term222 s) = (term223 s).
Proof. exact (MK_COMB (@lem4625116) (@lem4625115 s)). Qed.
Lemma lem4625118 (s : nat -> Prop) : (term224 s) = (term225 s).
Proof. exact (MK_COMB (@lem4625117 s) (@lem4625112 s)). Qed.
Lemma lem4625119 (s : nat -> Prop) : ((@FINITE nat s) = (term35 s)) = (term224 s).
Proof. exact (@lem17784 (@FINITE nat s) (term35 s)). Qed.
Lemma lem4625120 (s : nat -> Prop) : ((@FINITE nat s) = (term35 s)) = (term225 s).
Proof. exact (TRANS (@lem4625119 s) (@lem4625118 s)). Qed.
Lemma lem4625121 : term37 = term226.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4625120 s)). Qed.
Lemma lem4625122 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4625123 : term23 = term227.
Proof. exact (MK_COMB (@lem4625122) (@lem4625121)). Qed.
Lemma lem4625125 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4625126 (P : type993) (Q : type993) : (term228 P Q) = (term229 P Q).
Proof. exact (@lem4625125 (nat -> Prop) P Q). Qed.
Lemma lem4625127 : term230 = term231.
Proof. exact (@lem4625126 term232 term233). Qed.
Lemma lem4625128 (s : nat -> Prop) : (term234 s) = (term221 s).
Proof. exact (eq_refl (term234 s)). Qed.
Lemma lem4625129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4625130 (s : nat -> Prop) : (term235 s) = (term223 s).
Proof. exact (MK_COMB (@lem4625129) (@lem4625128 s)). Qed.
Lemma lem4625131 (s : nat -> Prop) : (term236 s) = (term218 s).
Proof. exact (eq_refl (term236 s)). Qed.
Lemma lem4625132 (s : nat -> Prop) : (term237 s) = (term225 s).
Proof. exact (MK_COMB (@lem4625130 s) (@lem4625131 s)). Qed.
Lemma lem4625133 : term238 = term226.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4625132 s)). Qed.
Lemma lem4625134 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4625135 : term230 = term227.
Proof. exact (MK_COMB (@lem4625134) (@lem4625133)). Qed.
Lemma lem4625136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4625137 : term239 = term240.
Proof. exact (MK_COMB (@lem4625136) (@lem4625135)). Qed.
Lemma lem4625138 (s : nat -> Prop) : (term234 s) = (term221 s).
Proof. exact (eq_refl (term234 s)). Qed.
Lemma lem4625139 : term241 = term232.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4625138 s)). Qed.
Lemma lem4625140 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4625141 : term242 = term243.
Proof. exact (MK_COMB (@lem4625140) (@lem4625139)). Qed.
Lemma lem4625142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4625143 : term244 = term245.
Proof. exact (MK_COMB (@lem4625142) (@lem4625141)). Qed.
Lemma lem4625144 (s : nat -> Prop) : (term236 s) = (term218 s).
Proof. exact (eq_refl (term236 s)). Qed.
Lemma lem4625145 : term246 = term233.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4625144 s)). Qed.
Lemma lem4625146 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4625147 : term247 = term248.
Proof. exact (MK_COMB (@lem4625146) (@lem4625145)). Qed.
Lemma lem4625148 : term231 = term249.
Proof. exact (MK_COMB (@lem4625143) (@lem4625147)). Qed.
Lemma lem4625149 : (term230 = term231) = (term227 = term249).
Proof. exact (MK_COMB (@lem4625137) (@lem4625148)). Qed.
Lemma lem4625150 : term227 = term249.
Proof. exact (EQ_MP (@lem4625149) (@lem4625127)). Qed.
Lemma lem4625332 {A B : Type'} (P : type1413 A B) : (term250 A B P) = (term251 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4625333 (P : type1605) : (term252 P) = (term253 P).
Proof. exact (@lem4625332 nat nat P). Qed.
Lemma lem4625334 (s : nat -> Prop) : (term254 s) = (term255 s).
Proof. exact (@lem4625333 (term256 s)). Qed.
Lemma lem4625335 (s : nat -> Prop) (a : nat) : (term257 s a) = (term203 s a).
Proof. exact (eq_refl (term257 s a)). Qed.
Lemma lem4625336 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4625337 (s : nat -> Prop) (a : nat) (x : nat) : (term258 s a x) = (term259 s a x).
Proof. exact (MK_COMB (@lem4625335 s a) (@lem4625336 x)). Qed.
Lemma lem4625338 (s : nat -> Prop) (x : nat) (a : nat) : (term259 s a x) = (term194 s x a).
Proof. exact (eq_refl (term259 s a x)). Qed.
Lemma lem4625339 (s : nat -> Prop) (x : nat) (a : nat) : (term258 s a x) = (term194 s x a).
Proof. exact (TRANS (@lem4625337 s a x) (@lem4625338 s x a)). Qed.
Lemma lem4625340 (s : nat -> Prop) (a : nat) : (term260 s a) = (term203 s a).
Proof. exact (fun_ext (fun x : nat => @lem4625339 s x a)). Qed.
Lemma lem4625341 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4625342 (s : nat -> Prop) (a : nat) : (term261 s a) = (term204 s a).
Proof. exact (MK_COMB (@lem4625341) (@lem4625340 s a)). Qed.
Lemma lem4625343 (s : nat -> Prop) : (term262 s) = (term212 s).
Proof. exact (fun_ext (fun a : nat => @lem4625342 s a)). Qed.
Lemma lem4625344 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625345 (s : nat -> Prop) : (term254 s) = (term213 s).
Proof. exact (MK_COMB (@lem4625344) (@lem4625343 s)). Qed.
Lemma lem4625346 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4625347 (s : nat -> Prop) : (term263 s) = (term264 s).
Proof. exact (MK_COMB (@lem4625346) (@lem4625345 s)). Qed.
Lemma lem4625348 (s : nat -> Prop) (a : nat) : (term257 s a) = (term203 s a).
Proof. exact (eq_refl (term257 s a)). Qed.
Lemma lem4625349 (x : nat -> nat) (a : nat) : (x a) = (x a).
Proof. exact (eq_refl (x a)). Qed.
Lemma lem4625350 (s : nat -> Prop) (x : nat -> nat) (a : nat) : (term265 s x a) = (term266 s x a).
Proof. exact (MK_COMB (@lem4625348 s a) (@lem4625349 x a)). Qed.
Lemma lem4625351 (s : nat -> Prop) (x : nat -> nat) (a : nat) : (term266 s x a) = (term267 s x a).
Proof. exact (eq_refl (term266 s x a)). Qed.
Lemma lem4625352 (s : nat -> Prop) (x : nat -> nat) (a : nat) : (term265 s x a) = (term267 s x a).
Proof. exact (TRANS (@lem4625350 s x a) (@lem4625351 s x a)). Qed.
Lemma lem4625353 (s : nat -> Prop) (x : nat -> nat) : (term268 s x) = (term269 s x).
Proof. exact (fun_ext (fun a : nat => @lem4625352 s x a)). Qed.
Lemma lem4625354 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625355 (s : nat -> Prop) (x : nat -> nat) : (term270 s x) = (term271 s x).
Proof. exact (MK_COMB (@lem4625354) (@lem4625353 s x)). Qed.
Lemma lem4625356 (s : nat -> Prop) : (term272 s) = (term273 s).
Proof. exact (fun_ext (fun x : nat -> nat => @lem4625355 s x)). Qed.
Lemma lem4625357 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4625358 (s : nat -> Prop) : (term255 s) = (term274 s).
Proof. exact (MK_COMB (@lem4625357) (@lem4625356 s)). Qed.
Lemma lem4625359 (s : nat -> Prop) : ((term254 s) = (term255 s)) = ((term213 s) = (term274 s)).
Proof. exact (MK_COMB (@lem4625347 s) (@lem4625358 s)). Qed.
Lemma lem4625360 (s : nat -> Prop) : (term213 s) = (term274 s).
Proof. exact (EQ_MP (@lem4625359 s) (@lem4625334 s)). Qed.
Lemma lem4625361 (s : nat -> Prop) : (term219 s) = (term219 s).
Proof. exact (eq_refl (term219 s)). Qed.
Lemma lem4625362 (s : nat -> Prop) : (term221 s) = (term275 s).
Proof. exact (MK_COMB (@lem4625361 s) (@lem4625360 s)). Qed.
Lemma lem4625364 {A : Type'} (P : Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4625365 (P : Prop) (Q : type1002) : (term278 P Q) = (term279 P Q).
Proof. exact (@lem4625364 (nat -> nat) P Q). Qed.
Lemma lem4625366 (s : nat -> Prop) : (term280 s) = (term281 s).
Proof. exact (@lem4625365 (@FINITE nat s) (term273 s)). Qed.
Lemma lem4625367 (s : nat -> Prop) (x : nat -> nat) : (term282 s x) = (term271 s x).
Proof. exact (eq_refl (term282 s x)). Qed.
Lemma lem4625368 (s : nat -> Prop) : (term283 s) = (term273 s).
Proof. exact (fun_ext (fun x : nat -> nat => @lem4625367 s x)). Qed.
Lemma lem4625369 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4625370 (s : nat -> Prop) : (term284 s) = (term274 s).
Proof. exact (MK_COMB (@lem4625369) (@lem4625368 s)). Qed.
Lemma lem4625371 (s : nat -> Prop) : (term219 s) = (term219 s).
Proof. exact (eq_refl (term219 s)). Qed.
Lemma lem4625372 (s : nat -> Prop) : (term280 s) = (term275 s).
Proof. exact (MK_COMB (@lem4625371 s) (@lem4625370 s)). Qed.
Lemma lem4625373 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4625374 (s : nat -> Prop) : (term285 s) = (term286 s).
Proof. exact (MK_COMB (@lem4625373) (@lem4625372 s)). Qed.
Lemma lem4625375 (s : nat -> Prop) (x : nat -> nat) : (term282 s x) = (term271 s x).
Proof. exact (eq_refl (term282 s x)). Qed.
Lemma lem4625376 (s : nat -> Prop) : (term219 s) = (term219 s).
Proof. exact (eq_refl (term219 s)). Qed.
Lemma lem4625377 (s : nat -> Prop) (x : nat -> nat) : (term287 s x) = (term288 s x).
Proof. exact (MK_COMB (@lem4625376 s) (@lem4625375 s x)). Qed.
Lemma lem4625378 (s : nat -> Prop) : (term289 s) = (term290 s).
Proof. exact (fun_ext (fun x : nat -> nat => @lem4625377 s x)). Qed.
Lemma lem4625379 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4625380 (s : nat -> Prop) : (term281 s) = (term291 s).
Proof. exact (MK_COMB (@lem4625379) (@lem4625378 s)). Qed.
Lemma lem4625381 (s : nat -> Prop) : ((term280 s) = (term281 s)) = ((term275 s) = (term291 s)).
Proof. exact (MK_COMB (@lem4625374 s) (@lem4625380 s)). Qed.
Lemma lem4625382 (s : nat -> Prop) : (term275 s) = (term291 s).
Proof. exact (EQ_MP (@lem4625381 s) (@lem4625366 s)). Qed.
Lemma lem4625383 (s : nat -> Prop) : (term221 s) = (term291 s).
Proof. exact (TRANS (@lem4625362 s) (@lem4625382 s)). Qed.
Lemma lem4625384 : term232 = term292.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4625383 s)). Qed.
Lemma lem4625385 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4625386 : term243 = term293.
Proof. exact (MK_COMB (@lem4625385) (@lem4625384)). Qed.
Lemma lem4625388 {A B : Type'} (P : type1413 A B) : (term250 A B P) = (term251 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4625389 (P : type986) : (term294 P) = (term295 P).
Proof. exact (@lem4625388 (nat -> Prop) (nat -> nat) P). Qed.
Lemma lem4625390 : term296 = term297.
Proof. exact (@lem4625389 term298). Qed.
Lemma lem4625391 (s : nat -> Prop) : (term299 s) = (term290 s).
Proof. exact (eq_refl (term299 s)). Qed.
Lemma lem4625392 (x : nat -> nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4625393 (s : nat -> Prop) (x : nat -> nat) : (term300 s x) = (term301 s x).
Proof. exact (MK_COMB (@lem4625391 s) (@lem4625392 x)). Qed.
Lemma lem4625394 (s : nat -> Prop) (x : nat -> nat) : (term301 s x) = (term288 s x).
Proof. exact (eq_refl (term301 s x)). Qed.
Lemma lem4625395 (s : nat -> Prop) (x : nat -> nat) : (term300 s x) = (term288 s x).
Proof. exact (TRANS (@lem4625393 s x) (@lem4625394 s x)). Qed.
Lemma lem4625396 (s : nat -> Prop) : (term302 s) = (term290 s).
Proof. exact (fun_ext (fun x : nat -> nat => @lem4625395 s x)). Qed.
Lemma lem4625397 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4625398 (s : nat -> Prop) : (term303 s) = (term291 s).
Proof. exact (MK_COMB (@lem4625397) (@lem4625396 s)). Qed.
Lemma lem4625399 : term304 = term292.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4625398 s)). Qed.
Lemma lem4625400 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4625401 : term296 = term293.
Proof. exact (MK_COMB (@lem4625400) (@lem4625399)). Qed.
Lemma lem4625402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4625403 : term305 = term306.
Proof. exact (MK_COMB (@lem4625402) (@lem4625401)). Qed.
Lemma lem4625404 (s : nat -> Prop) : (term299 s) = (term290 s).
Proof. exact (eq_refl (term299 s)). Qed.
Lemma lem4625405 (x : type992) (s : nat -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem4625406 (x : type992) (s : nat -> Prop) : (term307 x s) = (term308 x s).
Proof. exact (MK_COMB (@lem4625404 s) (@lem4625405 x s)). Qed.
Lemma lem4625407 (x : type992) (s : nat -> Prop) : (term308 x s) = (term309 x s).
Proof. exact (eq_refl (term308 x s)). Qed.
Lemma lem4625408 (x : type992) (s : nat -> Prop) : (term307 x s) = (term309 x s).
Proof. exact (TRANS (@lem4625406 x s) (@lem4625407 x s)). Qed.
Lemma lem4625409 (x : type992) : (term310 x) = (term311 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4625408 x s)). Qed.
Lemma lem4625410 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4625411 (x : type992) : (term312 x) = (term313 x).
Proof. exact (MK_COMB (@lem4625410) (@lem4625409 x)). Qed.
Lemma lem4625412 : term314 = term315.
Proof. exact (fun_ext (fun x : type992 => @lem4625411 x)). Qed.
Lemma lem4625413 : (@ex ((nat -> Prop) -> nat -> nat)) = (@ex ((nat -> Prop) -> nat -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat -> nat))). Qed.
Lemma lem4625414 : term297 = term316.
Proof. exact (MK_COMB (@lem4625413) (@lem4625412)). Qed.
Lemma lem4625415 : (term296 = term297) = (term293 = term316).
Proof. exact (MK_COMB (@lem4625403) (@lem4625414)). Qed.
Lemma lem4625416 : term293 = term316.
Proof. exact (EQ_MP (@lem4625415) (@lem4625390)). Qed.
Lemma lem4625417 : term243 = term316.
Proof. exact (TRANS (@lem4625386) (@lem4625416)). Qed.
Lemma lem4625418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4625419 : term245 = term317.
Proof. exact (MK_COMB (@lem4625418) (@lem4625417)). Qed.
Lemma lem4625421 {A : Type'} (P : Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4625422 (P : Prop) (Q : nat -> Prop) : (term318 P Q) = (term319 P Q).
Proof. exact (@lem4625421 nat P Q). Qed.
Lemma lem4625423 (s : nat -> Prop) : (term320 s) = (term321 s).
Proof. exact (@lem4625422 (term322 s) (term214 s)). Qed.
Lemma lem4625424 (s : nat -> Prop) (a : nat) : (term323 s a) = (term206 s a).
Proof. exact (eq_refl (term323 s a)). Qed.
Lemma lem4625425 (s : nat -> Prop) : (term324 s) = (term214 s).
Proof. exact (fun_ext (fun a : nat => @lem4625424 s a)). Qed.
Lemma lem4625426 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4625427 (s : nat -> Prop) : (term325 s) = (term215 s).
Proof. exact (MK_COMB (@lem4625426) (@lem4625425 s)). Qed.
Lemma lem4625428 (s : nat -> Prop) : (term216 s) = (term216 s).
Proof. exact (eq_refl (term216 s)). Qed.
Lemma lem4625429 (s : nat -> Prop) : (term320 s) = (term218 s).
Proof. exact (MK_COMB (@lem4625428 s) (@lem4625427 s)). Qed.
Lemma lem4625430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4625431 (s : nat -> Prop) : (term326 s) = (term327 s).
Proof. exact (MK_COMB (@lem4625430) (@lem4625429 s)). Qed.
Lemma lem4625432 (s : nat -> Prop) (a : nat) : (term323 s a) = (term206 s a).
Proof. exact (eq_refl (term323 s a)). Qed.
Lemma lem4625433 (s : nat -> Prop) : (term216 s) = (term216 s).
Proof. exact (eq_refl (term216 s)). Qed.
Lemma lem4625434 (s : nat -> Prop) (a : nat) : (term328 s a) = (term329 s a).
Proof. exact (MK_COMB (@lem4625433 s) (@lem4625432 s a)). Qed.
Lemma lem4625435 (s : nat -> Prop) : (term330 s) = (term331 s).
Proof. exact (fun_ext (fun a : nat => @lem4625434 s a)). Qed.
Lemma lem4625436 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4625437 (s : nat -> Prop) : (term321 s) = (term332 s).
Proof. exact (MK_COMB (@lem4625436) (@lem4625435 s)). Qed.
Lemma lem4625438 (s : nat -> Prop) : ((term320 s) = (term321 s)) = ((term218 s) = (term332 s)).
Proof. exact (MK_COMB (@lem4625431 s) (@lem4625437 s)). Qed.
Lemma lem4625439 (s : nat -> Prop) : (term218 s) = (term332 s).
Proof. exact (EQ_MP (@lem4625438 s) (@lem4625423 s)). Qed.
Lemma lem4625440 : term233 = term333.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4625439 s)). Qed.
Lemma lem4625441 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4625442 : term248 = term334.
Proof. exact (MK_COMB (@lem4625441) (@lem4625440)). Qed.
Lemma lem4625444 {A B : Type'} (P : type1413 A B) : (term250 A B P) = (term251 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4625445 (P : type991) : (term335 P) = (term336 P).
Proof. exact (@lem4625444 (nat -> Prop) nat P). Qed.
Lemma lem4625446 : term337 = term338.
Proof. exact (@lem4625445 term339). Qed.
Lemma lem4625447 (s : nat -> Prop) : (term340 s) = (term331 s).
Proof. exact (eq_refl (term340 s)). Qed.
Lemma lem4625448 (a : nat) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4625449 (s : nat -> Prop) (a : nat) : (term341 s a) = (term342 s a).
Proof. exact (MK_COMB (@lem4625447 s) (@lem4625448 a)). Qed.
Lemma lem4625450 (s : nat -> Prop) (a : nat) : (term342 s a) = (term329 s a).
Proof. exact (eq_refl (term342 s a)). Qed.
Lemma lem4625451 (s : nat -> Prop) (a : nat) : (term341 s a) = (term329 s a).
Proof. exact (TRANS (@lem4625449 s a) (@lem4625450 s a)). Qed.
Lemma lem4625452 (s : nat -> Prop) : (term343 s) = (term331 s).
Proof. exact (fun_ext (fun a : nat => @lem4625451 s a)). Qed.
Lemma lem4625453 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4625454 (s : nat -> Prop) : (term344 s) = (term332 s).
Proof. exact (MK_COMB (@lem4625453) (@lem4625452 s)). Qed.
Lemma lem4625455 : term345 = term333.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4625454 s)). Qed.
Lemma lem4625456 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4625457 : term337 = term334.
Proof. exact (MK_COMB (@lem4625456) (@lem4625455)). Qed.
Lemma lem4625458 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4625459 : term346 = term347.
Proof. exact (MK_COMB (@lem4625458) (@lem4625457)). Qed.
Lemma lem4625460 (s : nat -> Prop) : (term340 s) = (term331 s).
Proof. exact (eq_refl (term340 s)). Qed.
Lemma lem4625461 (a : type994) (s : nat -> Prop) : (a s) = (a s).
Proof. exact (eq_refl (a s)). Qed.
Lemma lem4625462 (a : type994) (s : nat -> Prop) : (term348 a s) = (term349 a s).
Proof. exact (MK_COMB (@lem4625460 s) (@lem4625461 a s)). Qed.
Lemma lem4625463 (a : type994) (s : nat -> Prop) : (term349 a s) = (term350 a s).
Proof. exact (eq_refl (term349 a s)). Qed.
Lemma lem4625464 (a : type994) (s : nat -> Prop) : (term348 a s) = (term350 a s).
Proof. exact (TRANS (@lem4625462 a s) (@lem4625463 a s)). Qed.
Lemma lem4625465 (a : type994) : (term351 a) = (term352 a).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4625464 a s)). Qed.
Lemma lem4625466 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4625467 (a : type994) : (term353 a) = (term354 a).
Proof. exact (MK_COMB (@lem4625466) (@lem4625465 a)). Qed.
Lemma lem4625468 : term355 = term356.
Proof. exact (fun_ext (fun a : type994 => @lem4625467 a)). Qed.
Lemma lem4625469 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem4625470 : term338 = term357.
Proof. exact (MK_COMB (@lem4625469) (@lem4625468)). Qed.
Lemma lem4625471 : (term337 = term338) = (term334 = term357).
Proof. exact (MK_COMB (@lem4625459) (@lem4625470)). Qed.
Lemma lem4625472 : term334 = term357.
Proof. exact (EQ_MP (@lem4625471) (@lem4625446)). Qed.
Lemma lem4625473 : term248 = term357.
Proof. exact (TRANS (@lem4625442) (@lem4625472)). Qed.
Lemma lem4625474 : term249 = term358.
Proof. exact (MK_COMB (@lem4625419) (@lem4625473)). Qed.
Lemma lem4625476 {A : Type'} (P : A -> Prop) (Q : Prop) : (term359 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4625477 (P : type251) (Q : Prop) : (term361 P Q) = (term362 P Q).
Proof. exact (@lem4625476 type992 P Q). Qed.
Lemma lem4625478 : term363 = term364.
Proof. exact (@lem4625477 term315 term357). Qed.
Lemma lem4625479 (x : type992) : (term365 x) = (term313 x).
Proof. exact (eq_refl (term365 x)). Qed.
Lemma lem4625480 : term366 = term315.
Proof. exact (fun_ext (fun x : type992 => @lem4625479 x)). Qed.
Lemma lem4625481 : (@ex ((nat -> Prop) -> nat -> nat)) = (@ex ((nat -> Prop) -> nat -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat -> nat))). Qed.
Lemma lem4625482 : term367 = term316.
Proof. exact (MK_COMB (@lem4625481) (@lem4625480)). Qed.
Lemma lem4625483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4625484 : term368 = term317.
Proof. exact (MK_COMB (@lem4625483) (@lem4625482)). Qed.
Lemma lem4625485 : term357 = term357.
Proof. exact (eq_refl term357). Qed.
Lemma lem4625486 : term363 = term358.
Proof. exact (MK_COMB (@lem4625484) (@lem4625485)). Qed.
Lemma lem4625487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4625488 : term369 = term370.
Proof. exact (MK_COMB (@lem4625487) (@lem4625486)). Qed.
Lemma lem4625489 (x : type992) : (term365 x) = (term313 x).
Proof. exact (eq_refl (term365 x)). Qed.
Lemma lem4625490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4625491 (x : type992) : (term371 x) = (term372 x).
Proof. exact (MK_COMB (@lem4625490) (@lem4625489 x)). Qed.
Lemma lem4625492 : term357 = term357.
Proof. exact (eq_refl term357). Qed.
Lemma lem4625493 (x : type992) : (term373 x) = (term374 x).
Proof. exact (MK_COMB (@lem4625491 x) (@lem4625492)). Qed.
Lemma lem4625494 : term375 = term376.
Proof. exact (fun_ext (fun x : type992 => @lem4625493 x)). Qed.
Lemma lem4625495 : (@ex ((nat -> Prop) -> nat -> nat)) = (@ex ((nat -> Prop) -> nat -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat -> nat))). Qed.
Lemma lem4625496 : term364 = term377.
Proof. exact (MK_COMB (@lem4625495) (@lem4625494)). Qed.
Lemma lem4625497 : (term363 = term364) = (term358 = term377).
Proof. exact (MK_COMB (@lem4625488) (@lem4625496)). Qed.
Lemma lem4625498 : term358 = term377.
Proof. exact (EQ_MP (@lem4625497) (@lem4625478)). Qed.
Lemma lem4625500 {A : Type'} (P : Prop) (Q : A -> Prop) : (term378 A P Q) = (term379 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4625501 (P : Prop) (Q : type252) : (term380 P Q) = (term381 P Q).
Proof. exact (@lem4625500 type994 P Q). Qed.
Lemma lem4625502 (x : type992) : (term382 x) = (term383 x).
Proof. exact (@lem4625501 (term313 x) term356). Qed.
Lemma lem4625503 (a : type994) : (term384 a) = (term354 a).
Proof. exact (eq_refl (term384 a)). Qed.
Lemma lem4625504 : term385 = term356.
Proof. exact (fun_ext (fun a : type994 => @lem4625503 a)). Qed.
Lemma lem4625505 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem4625506 : term386 = term357.
Proof. exact (MK_COMB (@lem4625505) (@lem4625504)). Qed.
Lemma lem4625507 (x : type992) : (term372 x) = (term372 x).
Proof. exact (eq_refl (term372 x)). Qed.
Lemma lem4625508 (x : type992) : (term382 x) = (term374 x).
Proof. exact (MK_COMB (@lem4625507 x) (@lem4625506)). Qed.
Lemma lem4625509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4625510 (x : type992) : (term387 x) = (term388 x).
Proof. exact (MK_COMB (@lem4625509) (@lem4625508 x)). Qed.
Lemma lem4625511 (a : type994) : (term384 a) = (term354 a).
Proof. exact (eq_refl (term384 a)). Qed.
Lemma lem4625512 (x : type992) : (term372 x) = (term372 x).
Proof. exact (eq_refl (term372 x)). Qed.
Lemma lem4625513 (x : type992) (a : type994) : (term389 x a) = (term390 x a).
Proof. exact (MK_COMB (@lem4625512 x) (@lem4625511 a)). Qed.
Lemma lem4625514 (x : type992) : (term391 x) = (term392 x).
Proof. exact (fun_ext (fun a : type994 => @lem4625513 x a)). Qed.
Lemma lem4625515 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem4625516 (x : type992) : (term383 x) = (term393 x).
Proof. exact (MK_COMB (@lem4625515) (@lem4625514 x)). Qed.
Lemma lem4625517 (x : type992) : ((term382 x) = (term383 x)) = ((term374 x) = (term393 x)).
Proof. exact (MK_COMB (@lem4625510 x) (@lem4625516 x)). Qed.
Lemma lem4625518 (x : type992) : (term374 x) = (term393 x).
Proof. exact (EQ_MP (@lem4625517 x) (@lem4625502 x)). Qed.
Lemma lem4625519 : term376 = term394.
Proof. exact (fun_ext (fun x : type992 => @lem4625518 x)). Qed.
Lemma lem4625520 : (@ex ((nat -> Prop) -> nat -> nat)) = (@ex ((nat -> Prop) -> nat -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat -> nat))). Qed.
Lemma lem4625521 : term377 = term395.
Proof. exact (MK_COMB (@lem4625520) (@lem4625519)). Qed.
Lemma lem4625522 : term358 = term395.
Proof. exact (TRANS (@lem4625498) (@lem4625521)). Qed.
Lemma lem4625523 : term249 = term395.
Proof. exact (TRANS (@lem4625474) (@lem4625522)). Qed.
Lemma lem4625524 : term227 = term395.
Proof. exact (TRANS (@lem4625150) (@lem4625523)). Qed.
Lemma lem4625525 : term23 = term395.
Proof. exact (TRANS (@lem4625123) (@lem4625524)). Qed.
Lemma lem4625526 (h1 : term23) : term395.
Proof. exact (EQ_MP (@lem4625525) (@lem4624402 h1)). Qed.
Lemma lem4625527 (x : type992) (h1 : term393 x) : term393 x.
Proof. exact (h1). Qed.
Lemma lem4625528 (x : type992) (a : type994) (h1 : term390 x a) : term390 x a.
Proof. exact (h1). Qed.
Lemma lem4625529 (s : nat -> Prop) (h1 : term66 s) : term66 s.
Proof. exact (h1). Qed.
Lemma lem4625542 (n : nat) (m : nat) : (term80 n m) = (term80 n m).
Proof. exact (eq_refl (term80 n m)). Qed.
Lemma lem4625543 (m : nat) : (term95 m) = (term95 m).
Proof. exact (fun_ext (fun n : nat => @lem4625542 n m)). Qed.
Lemma lem4625544 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625545 (m : nat) : (term111 m) = (term111 m).
Proof. exact (MK_COMB (@lem4625544) (@lem4625543 m)). Qed.
Lemma lem4625546 : term118 = term118.
Proof. exact (fun_ext (fun m : nat => @lem4625545 m)). Qed.
Lemma lem4625547 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625548 : term133 = term133.
Proof. exact (MK_COMB (@lem4625547) (@lem4625546)). Qed.
Lemma lem4625565 (n : nat) (m : nat) : (term97 n m) = (term97 n m).
Proof. exact (eq_refl (term97 n m)). Qed.
Lemma lem4625566 (m : nat) : (term94 m) = (term94 m).
Proof. exact (fun_ext (fun n : nat => @lem4625565 n m)). Qed.
Lemma lem4625567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625568 (m : nat) : (term106 m) = (term106 m).
Proof. exact (MK_COMB (@lem4625567) (@lem4625566 m)). Qed.
Lemma lem4625569 : term117 = term117.
Proof. exact (fun_ext (fun m : nat => @lem4625568 m)). Qed.
Lemma lem4625570 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625571 : term128 = term128.
Proof. exact (MK_COMB (@lem4625570) (@lem4625569)). Qed.
Lemma lem4625572 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4625573 : term130 = term130.
Proof. exact (MK_COMB (@lem4625572) (@lem4625571)). Qed.
Lemma lem4625574 : term134 = term134.
Proof. exact (MK_COMB (@lem4625573) (@lem4625548)). Qed.
Lemma lem4625575 (h1 : term47) : term134.
Proof. exact (EQ_MP (@lem4625574) (@lem4624757 h1)). Qed.
Lemma lem4625600 (m : nat) (n : nat) : (term137 m n) = (term137 m n).
Proof. exact (eq_refl (term137 m n)). Qed.
Lemma lem4625601 (m : nat) : (term153 m) = (term153 m).
Proof. exact (fun_ext (fun n : nat => @lem4625600 m n)). Qed.
Lemma lem4625602 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625603 (m : nat) : (term168 m) = (term168 m).
Proof. exact (MK_COMB (@lem4625602) (@lem4625601 m)). Qed.
Lemma lem4625604 : term175 = term175.
Proof. exact (fun_ext (fun m : nat => @lem4625603 m)). Qed.
Lemma lem4625605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625606 : term190 = term190.
Proof. exact (MK_COMB (@lem4625605) (@lem4625604)). Qed.
Lemma lem4625633 (m : nat) (n : nat) : (term140 m n) = (term140 m n).
Proof. exact (eq_refl (term140 m n)). Qed.
Lemma lem4625634 (m : nat) : (term152 m) = (term152 m).
Proof. exact (fun_ext (fun n : nat => @lem4625633 m n)). Qed.
Lemma lem4625635 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625636 (m : nat) : (term163 m) = (term163 m).
Proof. exact (MK_COMB (@lem4625635) (@lem4625634 m)). Qed.
Lemma lem4625637 : term174 = term174.
Proof. exact (fun_ext (fun m : nat => @lem4625636 m)). Qed.
Lemma lem4625638 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625639 : term185 = term185.
Proof. exact (MK_COMB (@lem4625638) (@lem4625637)). Qed.
Lemma lem4625640 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4625641 : term187 = term187.
Proof. exact (MK_COMB (@lem4625640) (@lem4625639)). Qed.
Lemma lem4625642 : term191 = term191.
Proof. exact (MK_COMB (@lem4625641) (@lem4625606)). Qed.
Lemma lem4625651 (m : nat) : (term9 m) = (term9 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem4625652 : term11 = term11.
Proof. exact (fun_ext (fun m : nat => @lem4625651 m)). Qed.
Lemma lem4625653 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625654 : term13 = term13.
Proof. exact (MK_COMB (@lem4625653) (@lem4625652)). Qed.
Lemma lem4625655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4625656 : term15 = term15.
Proof. exact (MK_COMB (@lem4625655) (@lem4625654)). Qed.
Lemma lem4625657 : term192 = term192.
Proof. exact (MK_COMB (@lem4625656) (@lem4625642)). Qed.
Lemma lem4625658 (h1 : term18) : term192.
Proof. exact (EQ_MP (@lem4625657) (@lem4625067 h1)). Qed.
Lemma lem4625675 (x : nat) (a : type994) (s : nat -> Prop) : (term396 x a s) = (term396 x a s).
Proof. exact (eq_refl (term396 x a s)). Qed.
Lemma lem4625676 (a : type994) (s : nat -> Prop) : (term397 a s) = (term397 a s).
Proof. exact (fun_ext (fun x : nat => @lem4625675 x a s)). Qed.
Lemma lem4625677 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625678 (a : type994) (s : nat -> Prop) : (term398 a s) = (term398 a s).
Proof. exact (MK_COMB (@lem4625677) (@lem4625676 a s)). Qed.
Lemma lem4625685 (s : nat -> Prop) : (term216 s) = (term216 s).
Proof. exact (eq_refl (term216 s)). Qed.
Lemma lem4625686 (a : type994) (s : nat -> Prop) : (term350 a s) = (term350 a s).
Proof. exact (MK_COMB (@lem4625685 s) (@lem4625678 a s)). Qed.
Lemma lem4625687 (a : type994) : (term352 a) = (term352 a).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4625686 a s)). Qed.
Lemma lem4625688 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4625689 (a : type994) : (term354 a) = (term354 a).
Proof. exact (MK_COMB (@lem4625688) (@lem4625687 a)). Qed.
Lemma lem4625712 (x : type992) (s : nat -> Prop) (a : nat) : (term399 x s a) = (term399 x s a).
Proof. exact (eq_refl (term399 x s a)). Qed.
Lemma lem4625713 (x : type992) (s : nat -> Prop) : (term400 x s) = (term400 x s).
Proof. exact (fun_ext (fun a : nat => @lem4625712 x s a)). Qed.
Lemma lem4625714 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625715 (x : type992) (s : nat -> Prop) : (term401 x s) = (term401 x s).
Proof. exact (MK_COMB (@lem4625714) (@lem4625713 x s)). Qed.
Lemma lem4625720 (s : nat -> Prop) : (term219 s) = (term219 s).
Proof. exact (eq_refl (term219 s)). Qed.
Lemma lem4625721 (x : type992) (s : nat -> Prop) : (term309 x s) = (term309 x s).
Proof. exact (MK_COMB (@lem4625720 s) (@lem4625715 x s)). Qed.
Lemma lem4625722 (x : type992) : (term311 x) = (term311 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4625721 x s)). Qed.
Lemma lem4625723 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4625724 (x : type992) : (term313 x) = (term313 x).
Proof. exact (MK_COMB (@lem4625723) (@lem4625722 x)). Qed.
Lemma lem4625725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4625726 (x : type992) : (term372 x) = (term372 x).
Proof. exact (MK_COMB (@lem4625725) (@lem4625724 x)). Qed.
Lemma lem4625727 (x : type992) (a : type994) : (term390 x a) = (term390 x a).
Proof. exact (MK_COMB (@lem4625726 x) (@lem4625689 a)). Qed.
Lemma lem4625728 (x : type992) (a : type994) (h1 : term390 x a) : term390 x a.
Proof. exact (EQ_MP (@lem4625727 x a) (@lem4625528 x a h1)). Qed.
Lemma lem4625733 (a : nat) (s : nat -> Prop) : (@IN nat a s) = (@IN nat a s).
Proof. exact (eq_refl (@IN nat a s)). Qed.
Lemma lem4625734 (s : nat -> Prop) : (term62 s) = (term62 s).
Proof. exact (fun_ext (fun a : nat => @lem4625733 a s)). Qed.
Lemma lem4625735 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625736 (s : nat -> Prop) : (term63 s) = (term63 s).
Proof. exact (MK_COMB (@lem4625735) (@lem4625734 s)). Qed.
Lemma lem4625741 (s : nat -> Prop) : (term64 s) = (term64 s).
Proof. exact (eq_refl (term64 s)). Qed.
Lemma lem4625742 (s : nat -> Prop) : (term66 s) = (term66 s).
Proof. exact (MK_COMB (@lem4625741 s) (@lem4625736 s)). Qed.
Lemma lem4625743 (s : nat -> Prop) (h1 : term66 s) : term66 s.
Proof. exact (EQ_MP (@lem4625742 s) (@lem4625529 s h1)). Qed.
Lemma lem4625744 (s : nat -> Prop) (h1 : term66 s) : term63 s.
Proof. exact (proj2 (@lem4625743 s h1)). Qed.
Lemma lem4625746 (x : type992) (a : type994) (h1 : term390 x a) : term354 a.
Proof. exact (proj2 (@lem4625728 x a h1)). Qed.
Lemma lem4625748 (h1 : term18) : term191.
Proof. exact (proj2 (@lem4625658 h1)). Qed.
Lemma lem4625751 (h1 : term18) : term185.
Proof. exact (proj1 (@lem4625748 h1)). Qed.
Lemma lem4625753 (h1 : term47) : term128.
Proof. exact (proj1 (@lem4625575 h1)). Qed.
Lemma lem4625759 (a : nat) (s : nat -> Prop) : (@IN nat a s) = (@IN nat a s).
Proof. exact (eq_refl (@IN nat a s)). Qed.
Lemma lem4625760 (s : nat -> Prop) : (term62 s) = (term62 s).
Proof. exact (fun_ext (fun a : nat => @lem4625759 a s)). Qed.
Lemma lem4625761 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625763 (s : nat -> Prop) : (term63 s) = (term63 s).
Proof. exact (MK_COMB (@lem4625761) (@lem4625760 s)). Qed.
Lemma lem4625764 (s : nat -> Prop) (h1 : term66 s) : term63 s.
Proof. exact (EQ_MP (@lem4625763 s) (@lem4625744 s h1)). Qed.
Lemma lem4625814 {A : Type'} (P : Prop) (Q : A -> Prop) : (term402 A P Q) = (term403 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4625815 (P : Prop) (Q : nat -> Prop) : (term404 P Q) = (term405 P Q).
Proof. exact (@lem4625814 nat P Q). Qed.
Lemma lem4625816 (a : type994) (s : nat -> Prop) : (term406 a s) = (term407 a s).
Proof. exact (@lem4625815 (term322 s) (term397 a s)). Qed.
Lemma lem4625817 (x : nat) (a : type994) (s : nat -> Prop) : (term408 a s x) = (term396 x a s).
Proof. exact (eq_refl (term408 a s x)). Qed.
Lemma lem4625818 (a : type994) (s : nat -> Prop) : (term409 a s) = (term397 a s).
Proof. exact (fun_ext (fun x : nat => @lem4625817 x a s)). Qed.
Lemma lem4625819 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625820 (a : type994) (s : nat -> Prop) : (term410 a s) = (term398 a s).
Proof. exact (MK_COMB (@lem4625819) (@lem4625818 a s)). Qed.
Lemma lem4625821 (s : nat -> Prop) : (term216 s) = (term216 s).
Proof. exact (eq_refl (term216 s)). Qed.
Lemma lem4625822 (a : type994) (s : nat -> Prop) : (term406 a s) = (term350 a s).
Proof. exact (MK_COMB (@lem4625821 s) (@lem4625820 a s)). Qed.
Lemma lem4625823 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4625824 (a : type994) (s : nat -> Prop) : (term411 a s) = (term412 a s).
Proof. exact (MK_COMB (@lem4625823) (@lem4625822 a s)). Qed.
Lemma lem4625825 (x : nat) (a : type994) (s : nat -> Prop) : (term408 a s x) = (term396 x a s).
Proof. exact (eq_refl (term408 a s x)). Qed.
Lemma lem4625826 (s : nat -> Prop) : (term216 s) = (term216 s).
Proof. exact (eq_refl (term216 s)). Qed.
Lemma lem4625827 (x : nat) (a : type994) (s : nat -> Prop) : (term413 a s x) = (term414 x a s).
Proof. exact (MK_COMB (@lem4625826 s) (@lem4625825 x a s)). Qed.
Lemma lem4625828 (a : type994) (s : nat -> Prop) : (term415 a s) = (term416 a s).
Proof. exact (fun_ext (fun x : nat => @lem4625827 x a s)). Qed.
Lemma lem4625829 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625830 (a : type994) (s : nat -> Prop) : (term407 a s) = (term417 a s).
Proof. exact (MK_COMB (@lem4625829) (@lem4625828 a s)). Qed.
Lemma lem4625831 (a : type994) (s : nat -> Prop) : ((term406 a s) = (term407 a s)) = ((term350 a s) = (term417 a s)).
Proof. exact (MK_COMB (@lem4625824 a s) (@lem4625830 a s)). Qed.
Lemma lem4625832 (a : type994) (s : nat -> Prop) : (term350 a s) = (term417 a s).
Proof. exact (EQ_MP (@lem4625831 a s) (@lem4625816 a s)). Qed.
Lemma lem4625833 (a : type994) : (term352 a) = (term418 a).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4625832 a s)). Qed.
Lemma lem4625834 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4625835 (a : type994) : (term354 a) = (term419 a).
Proof. exact (MK_COMB (@lem4625834) (@lem4625833 a)). Qed.
Lemma lem4625848 (x : nat) (a : type994) (s : nat -> Prop) : (term414 x a s) = (term414 x a s).
Proof. exact (eq_refl (term414 x a s)). Qed.
Lemma lem4625849 (a : type994) (s : nat -> Prop) : (term416 a s) = (term416 a s).
Proof. exact (fun_ext (fun x : nat => @lem4625848 x a s)). Qed.
Lemma lem4625850 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625851 (a : type994) (s : nat -> Prop) : (term417 a s) = (term417 a s).
Proof. exact (MK_COMB (@lem4625850) (@lem4625849 a s)). Qed.
Lemma lem4625852 (a : type994) : (term418 a) = (term418 a).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4625851 a s)). Qed.
Lemma lem4625853 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4625854 (a : type994) : (term419 a) = (term419 a).
Proof. exact (MK_COMB (@lem4625853) (@lem4625852 a)). Qed.
Lemma lem4625855 (a : type994) : (term354 a) = (term419 a).
Proof. exact (TRANS (@lem4625835 a) (@lem4625854 a)). Qed.
Lemma lem4625856 (x : type992) (a : type994) (h1 : term390 x a) : term419 a.
Proof. exact (EQ_MP (@lem4625855 a) (@lem4625746 x a h1)). Qed.
Lemma lem4625881 (m : nat) (n : nat) : (term140 m n) = (term420 m n).
Proof. exact (@lem19490 (term421 m n) (term38 m n) (term43 m n)). Qed.
Lemma lem4625882 (m : nat) : (term152 m) = (term422 m).
Proof. exact (fun_ext (fun n : nat => @lem4625881 m n)). Qed.
Lemma lem4625883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625884 (m : nat) : (term163 m) = (term423 m).
Proof. exact (MK_COMB (@lem4625883) (@lem4625882 m)). Qed.
Lemma lem4625885 : term174 = term424.
Proof. exact (fun_ext (fun m : nat => @lem4625884 m)). Qed.
Lemma lem4625886 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625888 : term185 = term425.
Proof. exact (MK_COMB (@lem4625886) (@lem4625885)). Qed.
Lemma lem4625889 (h1 : term18) : term425.
Proof. exact (EQ_MP (@lem4625888) (@lem4625751 h1)). Qed.
Lemma lem4625919 (n : nat) (m : nat) : (term97 n m) = (term97 n m).
Proof. exact (eq_refl (term97 n m)). Qed.
Lemma lem4625920 (m : nat) : (term94 m) = (term94 m).
Proof. exact (fun_ext (fun n : nat => @lem4625919 n m)). Qed.
Lemma lem4625921 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625922 (m : nat) : (term106 m) = (term106 m).
Proof. exact (MK_COMB (@lem4625921) (@lem4625920 m)). Qed.
Lemma lem4625923 : term117 = term117.
Proof. exact (fun_ext (fun m : nat => @lem4625922 m)). Qed.
Lemma lem4625924 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4625926 : term128 = term128.
Proof. exact (MK_COMB (@lem4625924) (@lem4625923)). Qed.
Lemma lem4625927 (h1 : term47) : term128.
Proof. exact (EQ_MP (@lem4625926) (@lem4625753 h1)). Qed.
Lemma lem4625944 (_55537 : nat) (s : nat -> Prop) (h1 : term66 s) : term426 s _55537.
Proof. exact (@lem4625764 s h1 _55537). Qed.
Lemma lem4625945 (_55537 : nat) (s : nat -> Prop) : (term426 s _55537) = (@IN nat _55537 s).
Proof. exact (eq_refl (term426 s _55537)). Qed.
Lemma lem4625953 (_55540 : nat -> Prop) (x : type992) (a : type994) (h1 : term390 x a) : term427 a _55540.
Proof. exact (@lem4625856 x a h1 _55540). Qed.
Lemma lem4625954 (a : type994) (_55540 : nat -> Prop) : (term427 a _55540) = (term417 a _55540).
Proof. exact (eq_refl (term427 a _55540)). Qed.
Lemma lem4625955 (_55540 : nat -> Prop) (x : type992) (a : type994) (h1 : term390 x a) : term417 a _55540.
Proof. exact (EQ_MP (@lem4625954 a _55540) (@lem4625953 _55540 x a h1)). Qed.
Lemma lem4625956 (_55540 : nat -> Prop) (_55541 : nat) (x : type992) (a : type994) (h1 : term390 x a) : term428 a _55540 _55541.
Proof. exact (@lem4625955 _55540 x a h1 _55541). Qed.
Lemma lem4625957 (_55541 : nat) (a : type994) (_55540 : nat -> Prop) : (term428 a _55540 _55541) = (term414 _55541 a _55540).
Proof. exact (eq_refl (term428 a _55540 _55541)). Qed.
Lemma lem4625962 (_55543 : nat) (h1 : term18) : term429 _55543.
Proof. exact (@lem4625889 h1 _55543). Qed.
Lemma lem4625963 (_55543 : nat) : (term429 _55543) = (term423 _55543).
Proof. exact (eq_refl (term429 _55543)). Qed.
Lemma lem4625964 (_55543 : nat) (h1 : term18) : term423 _55543.
Proof. exact (EQ_MP (@lem4625963 _55543) (@lem4625962 _55543 h1)). Qed.
Lemma lem4625965 (_55543 : nat) (_55544 : nat) (h1 : term18) : term430 _55543 _55544.
Proof. exact (@lem4625964 _55543 h1 _55544). Qed.
Lemma lem4625966 (_55543 : nat) (_55544 : nat) : (term430 _55543 _55544) = (term420 _55543 _55544).
Proof. exact (eq_refl (term430 _55543 _55544)). Qed.
Lemma lem4625967 (_55543 : nat) (_55544 : nat) (h1 : term18) : term420 _55543 _55544.
Proof. exact (EQ_MP (@lem4625966 _55543 _55544) (@lem4625965 _55543 _55544 h1)). Qed.
Lemma lem4625974 (_55547 : nat) (h1 : term47) : term119 _55547.
Proof. exact (@lem4625927 h1 _55547). Qed.
Lemma lem4625975 (_55547 : nat) : (term119 _55547) = (term106 _55547).
Proof. exact (eq_refl (term119 _55547)). Qed.
Lemma lem4625976 (_55547 : nat) (h1 : term47) : term106 _55547.
Proof. exact (EQ_MP (@lem4625975 _55547) (@lem4625974 _55547 h1)). Qed.
Lemma lem4625977 (_55547 : nat) (_55548 : nat) (h1 : term47) : term96 _55547 _55548.
Proof. exact (@lem4625976 _55547 h1 _55548). Qed.
Lemma lem4625978 (_55548 : nat) (_55547 : nat) : (term96 _55547 _55548) = (term97 _55548 _55547).
Proof. exact (eq_refl (term96 _55547 _55548)). Qed.
Lemma lem4626003 (_55541 : nat) (_55540 : nat -> Prop) (x : type992) (a : type994) (h1 : term390 x a) : term414 _55541 a _55540.
Proof. exact (EQ_MP (@lem4625957 _55541 a _55540) (@lem4625956 _55540 _55541 x a h1)). Qed.
Lemma lem4626021 (_55548 : nat) (_55547 : nat) (h1 : term47) : term97 _55548 _55547.
Proof. exact (EQ_MP (@lem4625978 _55548 _55547) (@lem4625977 _55547 _55548 h1)). Qed.
Lemma lem4626033 (_55543 : nat) (_55544 : nat) (h1 : term18) : term431 _55543 _55544.
Proof. exact (proj1 (@lem4625967 _55543 _55544 h1)). Qed.
Lemma lem4626165 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4626166 (a : type994) (s : nat -> Prop) : (a s) = (a s).
Proof. exact (@lem4626165 (a s)). Qed.
Lemma lem4626167 (a : type994) (s : nat -> Prop) : term432 a s.
Proof. exact (fun h0 : term433 a s => @lem4626166 a s). Qed.
Lemma lem4626169 (p : Prop) : (term434 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4626170 (a : type994) (s : nat -> Prop) : (term432 a s) = ((a s) = (a s)).
Proof. exact (@lem4626169 ((a s) = (a s))). Qed.
Lemma lem4626171 (a : type994) (s : nat -> Prop) : (a s) = (a s).
Proof. exact (EQ_MP (@lem4626170 a s) (@lem4626167 a s)). Qed.
Lemma lem4626173 (b : Prop) (a : Prop) : (a \/ b) = (term435 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4626174 (_55543 : nat) (_55544 : nat) : (term431 _55543 _55544) = (term436 _55543 _55544).
Proof. exact (@lem4626173 (term421 _55543 _55544) (term38 _55543 _55544)). Qed.
Lemma lem4626176 (a : Prop) : (term437 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4626177 (_55543 : nat) (_55544 : nat) : (term438 _55543 _55544) = (_55543 = _55544).
Proof. exact (@lem4626176 (_55543 = _55544)). Qed.
Lemma lem4626178 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4626179 (_55543 : nat) (_55544 : nat) : (term439 _55543 _55544) = (term440 _55543 _55544).
Proof. exact (MK_COMB (@lem4626178) (@lem4626177 _55543 _55544)). Qed.
Lemma lem4626180 (_55543 : nat) (_55544 : nat) : (term38 _55543 _55544) = (term38 _55543 _55544).
Proof. exact (eq_refl (term38 _55543 _55544)). Qed.
Lemma lem4626181 (_55543 : nat) (_55544 : nat) : (term436 _55543 _55544) = (term441 _55543 _55544).
Proof. exact (MK_COMB (@lem4626179 _55543 _55544) (@lem4626180 _55543 _55544)). Qed.
Lemma lem4626182 (_55543 : nat) (_55544 : nat) : (term431 _55543 _55544) = (term441 _55543 _55544).
Proof. exact (TRANS (@lem4626174 _55543 _55544) (@lem4626181 _55543 _55544)). Qed.
Lemma lem4626185 (_55543 : nat) (_55544 : nat) (h1 : term18) : term441 _55543 _55544.
Proof. exact (EQ_MP (@lem4626182 _55543 _55544) (@lem4626033 _55543 _55544 h1)). Qed.
Lemma lem4626186 (a : type994) (s : nat -> Prop) (h1 : term18) : term442 a s.
Proof. exact (@lem4626185 (a s) (a s) h1). Qed.
Lemma lem4626189 (a : type994) (s : nat -> Prop) (h1 : term18) : term443 a s.
Proof. exact (@lem4626186 a s h1 (@lem4626171 a s)). Qed.
Lemma lem4626190 (a : type994) (s : nat -> Prop) (h1 : term18) : term444 a s.
Proof. exact (fun h0 : term445 a s => @lem4626189 a s h1). Qed.
Lemma lem4626192 (p : Prop) : (term434 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4626193 (a : type994) (s : nat -> Prop) : (term444 a s) = (term443 a s).
Proof. exact (@lem4626192 (term443 a s)). Qed.
Lemma lem4626194 (a : type994) (s : nat -> Prop) (h1 : term18) : term443 a s.
Proof. exact (EQ_MP (@lem4626193 a s) (@lem4626190 a s h1)). Qed.
Lemma lem4626196 (s : nat -> Prop) (h1 : term66 s) : @FINITE nat s.
Proof. exact (proj1 (@lem4625743 s h1)). Qed.
Lemma lem4626197 (s : nat -> Prop) (h1 : term66 s) : term446 s.
Proof. exact (fun h0 : term322 s => @lem4626196 s h1). Qed.
Lemma lem4626199 (p : Prop) : (term434 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4626200 (s : nat -> Prop) : (term446 s) = (@FINITE nat s).
Proof. exact (@lem4626199 (@FINITE nat s)). Qed.
Lemma lem4626201 (s : nat -> Prop) (h1 : term66 s) : @FINITE nat s.
Proof. exact (EQ_MP (@lem4626200 s) (@lem4626197 s h1)). Qed.
Lemma lem4626203 (_55537 : nat) (s : nat -> Prop) (h1 : term66 s) : @IN nat _55537 s.
Proof. exact (EQ_MP (@lem4625945 _55537 s) (@lem4625944 _55537 s h1)). Qed.
Lemma lem4626204 (a : type994) (s : nat -> Prop) (h1 : term66 s) : term447 a s.
Proof. exact (@lem4626203 (term448 a s) s h1). Qed.
Lemma lem4626205 (a : type994) (s : nat -> Prop) (h1 : term66 s) : term449 a s.
Proof. exact (fun h0 : term450 a s => @lem4626204 a s h1). Qed.
Lemma lem4626207 (p : Prop) : (term434 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4626208 (a : type994) (s : nat -> Prop) : (term449 a s) = (term447 a s).
Proof. exact (@lem4626207 (term447 a s)). Qed.
Lemma lem4626209 (a : type994) (s : nat -> Prop) (h1 : term66 s) : term447 a s.
Proof. exact (EQ_MP (@lem4626208 a s) (@lem4626205 a s h1)). Qed.
Lemma lem4626225 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4626226 (a : type994) (_55541 : nat) (_55540 : nat -> Prop) : (term396 _55541 a _55540) = (term451 a _55541 _55540).
Proof. exact (@lem4626225 (term452 _55541 a _55540) (term48 _55541 _55540)). Qed.
Lemma lem4626232 (_55540 : nat -> Prop) : (term216 _55540) = (term216 _55540).
Proof. exact (eq_refl (term216 _55540)). Qed.
Lemma lem4626233 (a : type994) (_55541 : nat) (_55540 : nat -> Prop) : (term414 _55541 a _55540) = (term453 a _55541 _55540).
Proof. exact (MK_COMB (@lem4626232 _55540) (@lem4626226 a _55541 _55540)). Qed.
Lemma lem4626237 (q : Prop) (p : Prop) (r : Prop) : (term454 p q r) = (term454 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4626238 (a : type994) (_55541 : nat) (_55540 : nat -> Prop) : (term453 a _55541 _55540) = (term455 a _55541 _55540).
Proof. exact (@lem4626237 (term452 _55541 a _55540) (term322 _55540) (term48 _55541 _55540)). Qed.
Lemma lem4626254 (a : type994) (_55541 : nat) (_55540 : nat -> Prop) : (term414 _55541 a _55540) = (term455 a _55541 _55540).
Proof. exact (TRANS (@lem4626233 a _55541 _55540) (@lem4626238 a _55541 _55540)). Qed.
Lemma lem4626255 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4626256 (a : type994) (_55541 : nat) (_55540 : nat -> Prop) : (term456 _55541 a _55540) = (term457 a _55541 _55540).
Proof. exact (MK_COMB (@lem4626255) (@lem4626254 a _55541 _55540)). Qed.
Lemma lem4626272 (a : type994) (_55541 : nat) (_55540 : nat -> Prop) : (term455 a _55541 _55540) = (term455 a _55541 _55540).
Proof. exact (eq_refl (term455 a _55541 _55540)). Qed.
Lemma lem4626273 (a : type994) (_55541 : nat) (_55540 : nat -> Prop) : ((term414 _55541 a _55540) = (term455 a _55541 _55540)) = ((term455 a _55541 _55540) = (term455 a _55541 _55540)).
Proof. exact (MK_COMB (@lem4626256 a _55541 _55540) (@lem4626272 a _55541 _55540)). Qed.
Lemma lem4626275 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4626276 (x : Prop) : (x = x) = True.
Proof. exact (@lem4626275 Prop x). Qed.
Lemma lem4626277 (a : type994) (_55541 : nat) (_55540 : nat -> Prop) : ((term455 a _55541 _55540) = (term455 a _55541 _55540)) = True.
Proof. exact (@lem4626276 (term455 a _55541 _55540)). Qed.
Lemma lem4626278 (a : type994) (_55541 : nat) (_55540 : nat -> Prop) : ((term414 _55541 a _55540) = (term455 a _55541 _55540)) = True.
Proof. exact (TRANS (@lem4626273 a _55541 _55540) (@lem4626277 a _55541 _55540)). Qed.
Lemma lem4626279 (a : type994) (_55541 : nat) (_55540 : nat -> Prop) : True = ((term414 _55541 a _55540) = (term455 a _55541 _55540)).
Proof. exact (SYM (@lem4626278 a _55541 _55540)). Qed.
Lemma lem4626280 (a : type994) (_55541 : nat) (_55540 : nat -> Prop) : (term414 _55541 a _55540) = (term455 a _55541 _55540).
Proof. exact (EQ_MP (@lem4626279 a _55541 _55540) (@lem0)). Qed.
Lemma lem4626281 (_55541 : nat) (_55540 : nat -> Prop) (x : type992) (a : type994) (h1 : term390 x a) : term455 a _55541 _55540.
Proof. exact (EQ_MP (@lem4626280 a _55541 _55540) (@lem4626003 _55541 _55540 x a h1)). Qed.
Lemma lem4626283 (b : Prop) (a : Prop) : (a \/ b) = (term435 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4626284 (_55541 : nat) (a : type994) (_55540 : nat -> Prop) : (term455 a _55541 _55540) = (term458 _55541 a _55540).
Proof. exact (@lem4626283 (term459 _55541 _55540) (term452 _55541 a _55540)). Qed.
Lemma lem4626286 (a : Prop) (b : Prop) : (term460 a b) = (term461 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4626287 (_55541 : nat) (_55540 : nat -> Prop) : (term462 _55541 _55540) = (term463 _55541 _55540).
Proof. exact (@lem4626286 (term322 _55540) (term48 _55541 _55540)). Qed.
Lemma lem4626289 (a : Prop) : (term437 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4626290 (_55540 : nat -> Prop) : (term464 _55540) = (@FINITE nat _55540).
Proof. exact (@lem4626289 (@FINITE nat _55540)). Qed.
Lemma lem4626291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4626292 (_55540 : nat -> Prop) : (term465 _55540) = (term64 _55540).
Proof. exact (MK_COMB (@lem4626291) (@lem4626290 _55540)). Qed.
Lemma lem4626294 (a : Prop) : (term437 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4626295 (_55541 : nat) (_55540 : nat -> Prop) : (term54 _55541 _55540) = (@IN nat _55541 _55540).
Proof. exact (@lem4626294 (@IN nat _55541 _55540)). Qed.
Lemma lem4626296 (_55541 : nat) (_55540 : nat -> Prop) : (term463 _55541 _55540) = (term466 _55541 _55540).
Proof. exact (MK_COMB (@lem4626292 _55540) (@lem4626295 _55541 _55540)). Qed.
Lemma lem4626297 (_55541 : nat) (_55540 : nat -> Prop) : (term462 _55541 _55540) = (term466 _55541 _55540).
Proof. exact (TRANS (@lem4626287 _55541 _55540) (@lem4626296 _55541 _55540)). Qed.
Lemma lem4626298 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4626299 (_55541 : nat) (_55540 : nat -> Prop) : (term467 _55541 _55540) = (term468 _55541 _55540).
Proof. exact (MK_COMB (@lem4626298) (@lem4626297 _55541 _55540)). Qed.
Lemma lem4626300 (_55541 : nat) (a : type994) (_55540 : nat -> Prop) : (term452 _55541 a _55540) = (term452 _55541 a _55540).
Proof. exact (eq_refl (term452 _55541 a _55540)). Qed.
Lemma lem4626301 (_55541 : nat) (a : type994) (_55540 : nat -> Prop) : (term458 _55541 a _55540) = (term469 _55541 a _55540).
Proof. exact (MK_COMB (@lem4626299 _55541 _55540) (@lem4626300 _55541 a _55540)). Qed.
Lemma lem4626302 (_55541 : nat) (a : type994) (_55540 : nat -> Prop) : (term455 a _55541 _55540) = (term469 _55541 a _55540).
Proof. exact (TRANS (@lem4626284 _55541 a _55540) (@lem4626301 _55541 a _55540)). Qed.
Lemma lem4626304 (a : type994) (s : nat -> Prop) (h1 : term66 s) : term470 a s.
Proof. exact (conj (@lem4626201 s h1) (@lem4626209 a s h1)). Qed.
Lemma lem4626306 (_55541 : nat) (_55540 : nat -> Prop) (x : type992) (a : type994) (h1 : term390 x a) : term469 _55541 a _55540.
Proof. exact (EQ_MP (@lem4626302 _55541 a _55540) (@lem4626281 _55541 _55540 x a h1)). Qed.
Lemma lem4626307 (s : nat -> Prop) (x : type992) (a : type994) (h1 : term390 x a) : term471 a s.
Proof. exact (@lem4626306 (term448 a s) s x a h1). Qed.
Lemma lem4626310 (x : type992) (a : type994) (s : nat -> Prop) (h1 : term390 x a) (h2 : term66 s) : term472 a s.
Proof. exact (@lem4626307 s x a h1 (@lem4626304 a s h2)). Qed.
Lemma lem4626311 (x : type992) (a : type994) (s : nat -> Prop) (h1 : term390 x a) (h2 : term66 s) : term473 a s.
Proof. exact (fun h0 : term474 a s => @lem4626310 x a s h1 h2). Qed.
Lemma lem4626313 (p : Prop) : (term434 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4626314 (a : type994) (s : nat -> Prop) : (term473 a s) = (term472 a s).
Proof. exact (@lem4626313 (term472 a s)). Qed.
Lemma lem4626315 (x : type992) (a : type994) (s : nat -> Prop) (h1 : term390 x a) (h2 : term66 s) : term472 a s.
Proof. exact (EQ_MP (@lem4626314 a s) (@lem4626311 x a s h1 h2)). Qed.
Lemma lem4626317 (a : Prop) (b : Prop) : (term475 a b) = (term476 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4626318 (_55548 : nat) (_55547 : nat) : (term97 _55548 _55547) = (term477 _55548 _55547).
Proof. exact (@lem4626317 (Peano.lt _55547 _55548) (Peano.le _55548 _55547)). Qed.
Lemma lem4626320 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4626321 (_55548 : nat) (_55547 : nat) : (term477 _55548 _55547) = (term478 _55548 _55547).
Proof. exact (@lem4626320 (term479 _55548 _55547)). Qed.
Lemma lem4626322 (_55548 : nat) (_55547 : nat) : (term97 _55548 _55547) = (term478 _55548 _55547).
Proof. exact (TRANS (@lem4626318 _55548 _55547) (@lem4626321 _55548 _55547)). Qed.
Lemma lem4626324 (x : type992) (a : type994) (s : nat -> Prop) (h1 : term390 x a) (h2 : term18) (h3 : term66 s) : term480 a s.
Proof. exact (conj (@lem4626194 a s h2) (@lem4626315 x a s h1 h3)). Qed.
Lemma lem4626326 (_55548 : nat) (_55547 : nat) (h1 : term47) : term478 _55548 _55547.
Proof. exact (EQ_MP (@lem4626322 _55548 _55547) (@lem4626021 _55548 _55547 h1)). Qed.
Lemma lem4626327 (a : type994) (s : nat -> Prop) (h1 : term47) : term481 a s.
Proof. exact (@lem4626326 (term448 a s) (a s) h1). Qed.
Lemma lem4626330 (x : type992) (a : type994) (s : nat -> Prop) (h1 : term47) (h2 : term390 x a) (h3 : term18) (h4 : term66 s) : False.
Proof. exact (@lem4626327 a s h1 (@lem4626324 x a s h2 h3 h4)). Qed.
Lemma lem4626331 (x : type992) (a : type994) (s : nat -> Prop) (h1 : term47) (h2 : term390 x a) (h3 : term18) (h4 : term66 s) : term482.
Proof. exact (fun h0 : ~ False => @lem4626330 x a s h1 h2 h3 h4). Qed.
Lemma lem4626333 (p : Prop) : (term434 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4626334 : term482 = False.
Proof. exact (@lem4626333 False). Qed.
Lemma lem4626335 (x : type992) (a : type994) (s : nat -> Prop) (h1 : term47) (h2 : term390 x a) (h3 : term18) (h4 : term66 s) : False.
Proof. exact (EQ_MP (@lem4626334) (@lem4626331 x a s h1 h2 h3 h4)). Qed.
Lemma lem4626336 (x : type992) (a : type994) (s : nat -> Prop) (h1 : term47) (h2 : term390 x a) (h3 : term18) (h4 : term66 s) : (term66 s) = False.
Proof. exact (prop_ext (fun h5 : term66 s => @lem4626335 x a s h1 h2 h3 h4) (fun h5 : False => @lem4625743 s h4)). Qed.
Lemma lem4626337 (x : type992) (a : type994) (s : nat -> Prop) (h1 : term47) (h2 : term390 x a) (h3 : term18) (h4 : term66 s) : False.
Proof. exact (EQ_MP (@lem4626336 x a s h1 h2 h3 h4) (@lem4625743 s h4)). Qed.
Lemma lem4626338 (x : type992) (a : type994) (s : nat -> Prop) (h1 : term47) (h2 : term390 x a) (h3 : term18) (h4 : term66 s) : (term390 x a) = False.
Proof. exact (prop_ext (fun h5 : term390 x a => @lem4626337 x a s h1 h2 h3 h4) (fun h5 : False => @lem4625728 x a h2)). Qed.
Lemma lem4626339 (x : type992) (a : type994) (s : nat -> Prop) (h1 : term47) (h2 : term390 x a) (h3 : term18) (h4 : term66 s) : False.
Proof. exact (EQ_MP (@lem4626338 x a s h1 h2 h3 h4) (@lem4625728 x a h2)). Qed.
Lemma lem4626340 (x : type992) (a : type994) (h1 : term47) (h2 : term3) (h3 : term390 x a) (h4 : term18) : False.
Proof. exact (ex_elim (@lem4624468 h2) (fun s : nat -> Prop => fun h0 : term74 s => @lem4626339 x a s h1 h3 h4 h0)). Qed.
Lemma lem4626341 (x : type992) (h1 : term47) (h2 : term393 x) (h3 : term3) (h4 : term18) : False.
Proof. exact (ex_elim (@lem4625527 x h2) (fun a : type994 => fun h0 : term392 x a => @lem4626340 x a h1 h3 h0 h4)). Qed.
Lemma lem4626342 (h1 : term23) (h2 : term47) (h3 : term3) (h4 : term18) : False.
Proof. exact (ex_elim (@lem4625526 h1) (fun x : type992 => fun h0 : term394 x => @lem4626341 x h2 h0 h3 h4)). Qed.
Lemma lem4626343 (h1 : term47) (h2 : term3) (h3 : term18) : term21.
Proof. exact (fun h0 : term23 => @lem4626342 h0 h1 h2 h3). Qed.
Lemma lem4626344 : term21 = term22.
Proof. exact (@lem69 term23). Qed.
Lemma lem4626345 (h1 : term47) (h2 : term3) (h3 : term18) : term22.
Proof. exact (EQ_MP (@lem4626344) (@lem4626343 h1 h2 h3)). Qed.
Lemma lem4626346 (h1 : term47) (h2 : term3) : term25.
Proof. exact (fun h0 : term18 => @lem4626345 h1 h2 h0). Qed.
Lemma lem4626347 (h1 : term3) : term28.
Proof. exact (fun h0 : term47 => @lem4626346 h0 h1). Qed.
Lemma lem4626348 : term30.
Proof. exact (fun h0 : term3 => @lem4626347 h0). Qed.
Lemma lem4626349 : term4.
Proof. exact (EQ_MP (@lem4624398) (@lem4626348)). Qed.
Lemma lem4626351 : term4.
Proof. exact (@lem4624149 (@lem4626349)). Qed.
Lemma lem4626352 (h1 : term3) : term27.
Proof. exact (@lem4626351 (@lem4624134 h1)). Qed.
Lemma lem4626353 (h1 : term3) : term24.
Proof. exact (@lem4626352 h1 (@lem98377)). Qed.
Lemma lem4626354 (h1 : term3) : term21.
Proof. exact (@lem4626353 h1 (@lem89997)). Qed.
Lemma lem4626355 (h1 : term3) : False.
Proof. exact (@lem4626354 h1 (@lem4624119)). Qed.
Lemma lem4626356 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem4626355 h1) (fun h2 : False => @lem4624134 h1)). Qed.
Lemma lem4626357 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem4626356 h1) (@lem4624134 h1)). Qed.
Lemma lem4626358 : term2.
Proof. exact (fun h0 : term3 => @lem4626357 h0). Qed.
Lemma lem4626359 : term1.
Proof. exact (EQ_MP (@lem4624133) (@lem4626358)). Qed.
