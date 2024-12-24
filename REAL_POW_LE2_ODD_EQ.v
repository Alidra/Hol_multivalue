Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_LE2_ODD_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_NOT_LE_spec.
Require Import REAL_POW_LE2_ODD_spec.
Require Import REAL_POW_LT2_ODD_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem1663095 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1663096 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1663097 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1663096 t1) (@lem1663095 t1)). Qed.
Lemma lem1663098 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1663097 t1 t2). Qed.
Lemma lem1663099 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1663100 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1663099 t1 t2) (@lem1663098 t1 t2)). Qed.
Lemma lem1663101 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1663100 t1 t2 t3). Qed.
Lemma lem1663102 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1663103 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1663102 t1 t2 t3) (@lem1663101 t1 t2 t3)). Qed.
Lemma lem1663104 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1663103 t1 t2 t3)). Qed.
Lemma lem1663106 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1663107 : term8 = term9.
Proof. exact (@lem1663106 term8). Qed.
Lemma lem1663108 : term9 = term8.
Proof. exact (SYM (@lem1663107)). Qed.
Lemma lem1663109 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1663112 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1663113 : term12.
Proof. exact (fun h0 : term11 => @lem1663112 h0). Qed.
Lemma lem1663114 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1663115 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1663116 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1663114 h2 (@lem1663115 h1)). Qed.
Lemma lem1663117 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1663116 h1 h0). Qed.
Lemma lem1663118 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1663119 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1663117 h1 (@lem1663118 h2)). Qed.
Lemma lem1663120 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1663119 h0 h1). Qed.
Lemma lem1663121 : term14.
Proof. exact (fun h0 : term12 => @lem1663120 h0). Qed.
Lemma lem1663124 : term12.
Proof. exact (@lem1663121 (@lem1663113)). Qed.
Lemma lem1663170 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1663171 : term15 = term16.
Proof. exact (@lem1663170 term17). Qed.
Lemma lem1663188 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1663189 : term19 = term20.
Proof. exact (MK_COMB (@lem1663188) (@lem1663171)). Qed.
Lemma lem1663192 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1663193 : term22 = term23.
Proof. exact (MK_COMB (@lem1663192) (@lem1663189)). Qed.
Lemma lem1663196 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1663203 : term11 = term25.
Proof. exact (MK_COMB (@lem1663196) (@lem1663193)). Qed.
Lemma lem1663212 (x : real) (y : real) (n : nat) : (term26 x y n) = (term26 x y n).
Proof. exact (eq_refl (term26 x y n)). Qed.
Lemma lem1663213 (x : real) (n : nat) : (term27 x n) = (term27 x n).
Proof. exact (fun_ext (fun y : real => @lem1663212 x y n)). Qed.
Lemma lem1663214 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1663215 (x : real) (n : nat) : (term28 x n) = (term28 x n).
Proof. exact (MK_COMB (@lem1663214) (@lem1663213 x n)). Qed.
Lemma lem1663216 (n : nat) : (term29 n) = (term29 n).
Proof. exact (fun_ext (fun x : real => @lem1663215 x n)). Qed.
Lemma lem1663217 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1663218 (n : nat) : (term30 n) = (term30 n).
Proof. exact (MK_COMB (@lem1663217) (@lem1663216 n)). Qed.
Lemma lem1663219 : term31 = term31.
Proof. exact (fun_ext (fun n : nat => @lem1663218 n)). Qed.
Lemma lem1663220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1663221 : term17 = term17.
Proof. exact (MK_COMB (@lem1663220) (@lem1663219)). Qed.
Lemma lem1663222 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1663223 : term16 = term16.
Proof. exact (MK_COMB (@lem1663222) (@lem1663221)). Qed.
Lemma lem1663232 (x : real) (y : real) (n : nat) : (term32 x y n) = (term32 x y n).
Proof. exact (eq_refl (term32 x y n)). Qed.
Lemma lem1663233 (x : real) (n : nat) : (term33 x n) = (term33 x n).
Proof. exact (fun_ext (fun y : real => @lem1663232 x y n)). Qed.
Lemma lem1663234 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1663235 (x : real) (n : nat) : (term34 x n) = (term34 x n).
Proof. exact (MK_COMB (@lem1663234) (@lem1663233 x n)). Qed.
Lemma lem1663236 (n : nat) : (term35 n) = (term35 n).
Proof. exact (fun_ext (fun x : real => @lem1663235 x n)). Qed.
Lemma lem1663237 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1663238 (n : nat) : (term36 n) = (term36 n).
Proof. exact (MK_COMB (@lem1663237) (@lem1663236 n)). Qed.
Lemma lem1663239 : term37 = term37.
Proof. exact (fun_ext (fun n : nat => @lem1663238 n)). Qed.
Lemma lem1663240 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1663241 : term38 = term38.
Proof. exact (MK_COMB (@lem1663240) (@lem1663239)). Qed.
Lemma lem1663242 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1663243 : term18 = term18.
Proof. exact (MK_COMB (@lem1663242) (@lem1663241)). Qed.
Lemma lem1663244 : term20 = term20.
Proof. exact (MK_COMB (@lem1663243) (@lem1663223)). Qed.
Lemma lem1663251 (y : real) (x : real) : ((term39 x y) = (real_lt y x)) = ((term39 x y) = (real_lt y x)).
Proof. exact (eq_refl ((term39 x y) = (real_lt y x))). Qed.
Lemma lem1663252 (x : real) : (term40 x) = (term40 x).
Proof. exact (fun_ext (fun y : real => @lem1663251 y x)). Qed.
Lemma lem1663253 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1663254 (x : real) : (term41 x) = (term41 x).
Proof. exact (MK_COMB (@lem1663253) (@lem1663252 x)). Qed.
Lemma lem1663255 : term42 = term42.
Proof. exact (fun_ext (fun x : real => @lem1663254 x)). Qed.
Lemma lem1663256 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1663257 : term43 = term43.
Proof. exact (MK_COMB (@lem1663256) (@lem1663255)). Qed.
Lemma lem1663258 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1663259 : term21 = term21.
Proof. exact (MK_COMB (@lem1663258) (@lem1663257)). Qed.
Lemma lem1663260 : term23 = term23.
Proof. exact (MK_COMB (@lem1663259) (@lem1663244)). Qed.
Lemma lem1663269 (n : nat) (x : real) (y : real) : (term44 n x y) = (term44 n x y).
Proof. exact (eq_refl (term44 n x y)). Qed.
Lemma lem1663270 (n : nat) (x : real) : (term45 n x) = (term45 n x).
Proof. exact (fun_ext (fun y : real => @lem1663269 n x y)). Qed.
Lemma lem1663271 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1663272 (n : nat) (x : real) : (term46 n x) = (term46 n x).
Proof. exact (MK_COMB (@lem1663271) (@lem1663270 n x)). Qed.
Lemma lem1663273 (n : nat) : (term47 n) = (term47 n).
Proof. exact (fun_ext (fun x : real => @lem1663272 n x)). Qed.
Lemma lem1663274 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1663275 (n : nat) : (term48 n) = (term48 n).
Proof. exact (MK_COMB (@lem1663274) (@lem1663273 n)). Qed.
Lemma lem1663276 : term49 = term49.
Proof. exact (fun_ext (fun n : nat => @lem1663275 n)). Qed.
Lemma lem1663277 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1663278 : term8 = term8.
Proof. exact (MK_COMB (@lem1663277) (@lem1663276)). Qed.
Lemma lem1663279 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1663280 : term10 = term10.
Proof. exact (MK_COMB (@lem1663279) (@lem1663278)). Qed.
Lemma lem1663281 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1663282 : term24 = term24.
Proof. exact (MK_COMB (@lem1663281) (@lem1663280)). Qed.
Lemma lem1663283 : term25 = term25.
Proof. exact (MK_COMB (@lem1663282) (@lem1663260)). Qed.
Lemma lem1663368 : term11 = term25.
Proof. exact (TRANS (@lem1663203) (@lem1663283)). Qed.
Lemma lem1663369 : term25 = term11.
Proof. exact (SYM (@lem1663368)). Qed.
Lemma lem1663370 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1663371 (h1 : term43) : term43.
Proof. exact (h1). Qed.
Lemma lem1663372 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1663373 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1663389 (n : nat) (x : real) (y : real) : (term50 n x y) = (term51 n x y).
Proof. exact (@lem17646 (term52 x y n) (real_le x y)). Qed.
Lemma lem1663391 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1663392 (n : nat) (x : real) (y : real) : (term54 n x y) = (term55 n x y).
Proof. exact (MK_COMB (@lem1663391 n) (@lem1663389 n x y)). Qed.
Lemma lem1663393 (n : nat) (x : real) (y : real) : (term56 n x y) = (term54 n x y).
Proof. exact (@lem17362 (Coq.Arith.PeanoNat.Nat.Odd n) ((term52 x y n) = (real_le x y))). Qed.
Lemma lem1663394 (n : nat) (x : real) (y : real) : (term56 n x y) = (term55 n x y).
Proof. exact (TRANS (@lem1663393 n x y) (@lem1663392 n x y)). Qed.
Lemma lem1663395 (P : real -> Prop) : (term57 P) = (term58 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1663396 (n : nat) (x : real) : (term59 n x) = (term60 n x).
Proof. exact (@lem1663395 (term45 n x)). Qed.
Lemma lem1663397 (n : nat) (x : real) (y : real) : (term61 n x y) = (term44 n x y).
Proof. exact (eq_refl (term61 n x y)). Qed.
Lemma lem1663398 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1663399 (n : nat) (x : real) (y : real) : (term62 n x y) = (term56 n x y).
Proof. exact (MK_COMB (@lem1663398) (@lem1663397 n x y)). Qed.
Lemma lem1663400 (n : nat) (x : real) (y : real) : (term62 n x y) = (term55 n x y).
Proof. exact (TRANS (@lem1663399 n x y) (@lem1663394 n x y)). Qed.
Lemma lem1663401 (n : nat) (x : real) : (term63 n x) = (term64 n x).
Proof. exact (fun_ext (fun y : real => @lem1663400 n x y)). Qed.
Lemma lem1663402 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663403 (n : nat) (x : real) : (term60 n x) = (term65 n x).
Proof. exact (MK_COMB (@lem1663402) (@lem1663401 n x)). Qed.
Lemma lem1663404 (n : nat) (x : real) : (term59 n x) = (term65 n x).
Proof. exact (TRANS (@lem1663396 n x) (@lem1663403 n x)). Qed.
Lemma lem1663405 (P : real -> Prop) : (term57 P) = (term58 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1663406 (n : nat) : (term66 n) = (term67 n).
Proof. exact (@lem1663405 (term47 n)). Qed.
Lemma lem1663407 (n : nat) (x : real) : (term68 n x) = (term46 n x).
Proof. exact (eq_refl (term68 n x)). Qed.
Lemma lem1663408 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1663409 (n : nat) (x : real) : (term69 n x) = (term59 n x).
Proof. exact (MK_COMB (@lem1663408) (@lem1663407 n x)). Qed.
Lemma lem1663410 (n : nat) (x : real) : (term69 n x) = (term65 n x).
Proof. exact (TRANS (@lem1663409 n x) (@lem1663404 n x)). Qed.
Lemma lem1663411 (n : nat) : (term70 n) = (term71 n).
Proof. exact (fun_ext (fun x : real => @lem1663410 n x)). Qed.
Lemma lem1663412 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663413 (n : nat) : (term67 n) = (term72 n).
Proof. exact (MK_COMB (@lem1663412) (@lem1663411 n)). Qed.
Lemma lem1663414 (n : nat) : (term66 n) = (term72 n).
Proof. exact (TRANS (@lem1663406 n) (@lem1663413 n)). Qed.
Lemma lem1663415 (P : nat -> Prop) : (term73 P) = (term74 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem1663416 : term10 = term75.
Proof. exact (@lem1663415 term49). Qed.
Lemma lem1663417 (n : nat) : (term76 n) = (term48 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem1663418 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1663419 (n : nat) : (term77 n) = (term66 n).
Proof. exact (MK_COMB (@lem1663418) (@lem1663417 n)). Qed.
Lemma lem1663420 (n : nat) : (term77 n) = (term72 n).
Proof. exact (TRANS (@lem1663419 n) (@lem1663414 n)). Qed.
Lemma lem1663421 : term78 = term79.
Proof. exact (fun_ext (fun n : nat => @lem1663420 n)). Qed.
Lemma lem1663422 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1663423 : term75 = term80.
Proof. exact (MK_COMB (@lem1663422) (@lem1663421)). Qed.
Lemma lem1663424 : term10 = term80.
Proof. exact (TRANS (@lem1663416) (@lem1663423)). Qed.
Lemma lem1663434 {A : Type'} (P : Prop) (Q : A -> Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1663435 (P : Prop) (Q : real -> Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem1663434 real P Q). Qed.
Lemma lem1663436 (n : nat) (x : real) : (term85 n x) = (term86 n x).
Proof. exact (@lem1663435 (Coq.Arith.PeanoNat.Nat.Odd n) (term87 n x)). Qed.
Lemma lem1663437 (n : nat) (x : real) (y : real) : (term88 n x y) = (term51 n x y).
Proof. exact (eq_refl (term88 n x y)). Qed.
Lemma lem1663438 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1663439 (n : nat) (x : real) (y : real) : (term89 n x y) = (term55 n x y).
Proof. exact (MK_COMB (@lem1663438 n) (@lem1663437 n x y)). Qed.
Lemma lem1663440 (n : nat) (x : real) : (term90 n x) = (term64 n x).
Proof. exact (fun_ext (fun y : real => @lem1663439 n x y)). Qed.
Lemma lem1663441 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663442 (n : nat) (x : real) : (term85 n x) = (term65 n x).
Proof. exact (MK_COMB (@lem1663441) (@lem1663440 n x)). Qed.
Lemma lem1663443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1663444 (n : nat) (x : real) : (term91 n x) = (term92 n x).
Proof. exact (MK_COMB (@lem1663443) (@lem1663442 n x)). Qed.
Lemma lem1663445 (n : nat) (x : real) (y : real) : (term88 n x y) = (term51 n x y).
Proof. exact (eq_refl (term88 n x y)). Qed.
Lemma lem1663446 (n : nat) (x : real) : (term93 n x) = (term87 n x).
Proof. exact (fun_ext (fun y : real => @lem1663445 n x y)). Qed.
Lemma lem1663447 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663448 (n : nat) (x : real) : (term94 n x) = (term95 n x).
Proof. exact (MK_COMB (@lem1663447) (@lem1663446 n x)). Qed.
Lemma lem1663449 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1663450 (n : nat) (x : real) : (term86 n x) = (term96 n x).
Proof. exact (MK_COMB (@lem1663449 n) (@lem1663448 n x)). Qed.
Lemma lem1663451 (n : nat) (x : real) : ((term85 n x) = (term86 n x)) = ((term65 n x) = (term96 n x)).
Proof. exact (MK_COMB (@lem1663444 n x) (@lem1663450 n x)). Qed.
Lemma lem1663452 (n : nat) (x : real) : (term65 n x) = (term96 n x).
Proof. exact (EQ_MP (@lem1663451 n x) (@lem1663436 n x)). Qed.
Lemma lem1663454 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1663455 (P : real -> Prop) (Q : real -> Prop) : (term99 P Q) = (term100 P Q).
Proof. exact (@lem1663454 real P Q). Qed.
Lemma lem1663456 (n : nat) (x : real) : (term101 n x) = (term102 n x).
Proof. exact (@lem1663455 (term103 n x) (term104 n x)). Qed.
Lemma lem1663457 (n : nat) (x : real) (y : real) : (term105 n x y) = (term106 n x y).
Proof. exact (eq_refl (term105 n x y)). Qed.
Lemma lem1663458 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1663459 (n : nat) (x : real) (y : real) : (term107 n x y) = (term108 n x y).
Proof. exact (MK_COMB (@lem1663458) (@lem1663457 n x y)). Qed.
Lemma lem1663460 (n : nat) (x : real) (y : real) : (term109 n x y) = (term110 n x y).
Proof. exact (eq_refl (term109 n x y)). Qed.
Lemma lem1663461 (n : nat) (x : real) (y : real) : (term111 n x y) = (term51 n x y).
Proof. exact (MK_COMB (@lem1663459 n x y) (@lem1663460 n x y)). Qed.
Lemma lem1663462 (n : nat) (x : real) : (term112 n x) = (term87 n x).
Proof. exact (fun_ext (fun y : real => @lem1663461 n x y)). Qed.
Lemma lem1663463 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663464 (n : nat) (x : real) : (term101 n x) = (term95 n x).
Proof. exact (MK_COMB (@lem1663463) (@lem1663462 n x)). Qed.
Lemma lem1663465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1663466 (n : nat) (x : real) : (term113 n x) = (term114 n x).
Proof. exact (MK_COMB (@lem1663465) (@lem1663464 n x)). Qed.
Lemma lem1663467 (n : nat) (x : real) (y : real) : (term105 n x y) = (term106 n x y).
Proof. exact (eq_refl (term105 n x y)). Qed.
Lemma lem1663468 (n : nat) (x : real) : (term115 n x) = (term103 n x).
Proof. exact (fun_ext (fun y : real => @lem1663467 n x y)). Qed.
Lemma lem1663469 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663470 (n : nat) (x : real) : (term116 n x) = (term117 n x).
Proof. exact (MK_COMB (@lem1663469) (@lem1663468 n x)). Qed.
Lemma lem1663471 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1663472 (n : nat) (x : real) : (term118 n x) = (term119 n x).
Proof. exact (MK_COMB (@lem1663471) (@lem1663470 n x)). Qed.
Lemma lem1663473 (n : nat) (x : real) (y : real) : (term109 n x y) = (term110 n x y).
Proof. exact (eq_refl (term109 n x y)). Qed.
Lemma lem1663474 (n : nat) (x : real) : (term120 n x) = (term104 n x).
Proof. exact (fun_ext (fun y : real => @lem1663473 n x y)). Qed.
Lemma lem1663475 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663476 (n : nat) (x : real) : (term121 n x) = (term122 n x).
Proof. exact (MK_COMB (@lem1663475) (@lem1663474 n x)). Qed.
Lemma lem1663477 (n : nat) (x : real) : (term102 n x) = (term123 n x).
Proof. exact (MK_COMB (@lem1663472 n x) (@lem1663476 n x)). Qed.
Lemma lem1663478 (n : nat) (x : real) : ((term101 n x) = (term102 n x)) = ((term95 n x) = (term123 n x)).
Proof. exact (MK_COMB (@lem1663466 n x) (@lem1663477 n x)). Qed.
Lemma lem1663479 (n : nat) (x : real) : (term95 n x) = (term123 n x).
Proof. exact (EQ_MP (@lem1663478 n x) (@lem1663456 n x)). Qed.
Lemma lem1663576 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1663577 (n : nat) (x : real) : (term96 n x) = (term124 n x).
Proof. exact (MK_COMB (@lem1663576 n) (@lem1663479 n x)). Qed.
Lemma lem1663578 (n : nat) (x : real) : (term65 n x) = (term124 n x).
Proof. exact (TRANS (@lem1663452 n x) (@lem1663577 n x)). Qed.
Lemma lem1663579 (n : nat) : (term71 n) = (term125 n).
Proof. exact (fun_ext (fun x : real => @lem1663578 n x)). Qed.
Lemma lem1663580 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663581 (n : nat) : (term72 n) = (term126 n).
Proof. exact (MK_COMB (@lem1663580) (@lem1663579 n)). Qed.
Lemma lem1663583 {A : Type'} (P : Prop) (Q : A -> Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1663584 (P : Prop) (Q : real -> Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem1663583 real P Q). Qed.
Lemma lem1663585 (n : nat) : (term127 n) = (term128 n).
Proof. exact (@lem1663584 (Coq.Arith.PeanoNat.Nat.Odd n) (term129 n)). Qed.
Lemma lem1663586 (n : nat) (x : real) : (term130 n x) = (term123 n x).
Proof. exact (eq_refl (term130 n x)). Qed.
Lemma lem1663587 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1663588 (n : nat) (x : real) : (term131 n x) = (term124 n x).
Proof. exact (MK_COMB (@lem1663587 n) (@lem1663586 n x)). Qed.
Lemma lem1663589 (n : nat) : (term132 n) = (term125 n).
Proof. exact (fun_ext (fun x : real => @lem1663588 n x)). Qed.
Lemma lem1663590 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663591 (n : nat) : (term127 n) = (term126 n).
Proof. exact (MK_COMB (@lem1663590) (@lem1663589 n)). Qed.
Lemma lem1663592 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1663593 (n : nat) : (term133 n) = (term134 n).
Proof. exact (MK_COMB (@lem1663592) (@lem1663591 n)). Qed.
Lemma lem1663594 (n : nat) (x : real) : (term130 n x) = (term123 n x).
Proof. exact (eq_refl (term130 n x)). Qed.
Lemma lem1663595 (n : nat) : (term135 n) = (term129 n).
Proof. exact (fun_ext (fun x : real => @lem1663594 n x)). Qed.
Lemma lem1663596 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663597 (n : nat) : (term136 n) = (term137 n).
Proof. exact (MK_COMB (@lem1663596) (@lem1663595 n)). Qed.
Lemma lem1663598 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1663599 (n : nat) : (term128 n) = (term138 n).
Proof. exact (MK_COMB (@lem1663598 n) (@lem1663597 n)). Qed.
Lemma lem1663600 (n : nat) : ((term127 n) = (term128 n)) = ((term126 n) = (term138 n)).
Proof. exact (MK_COMB (@lem1663593 n) (@lem1663599 n)). Qed.
Lemma lem1663601 (n : nat) : (term126 n) = (term138 n).
Proof. exact (EQ_MP (@lem1663600 n) (@lem1663585 n)). Qed.
Lemma lem1663603 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1663604 (P : real -> Prop) (Q : real -> Prop) : (term99 P Q) = (term100 P Q).
Proof. exact (@lem1663603 real P Q). Qed.
Lemma lem1663605 (n : nat) : (term139 n) = (term140 n).
Proof. exact (@lem1663604 (term141 n) (term142 n)). Qed.
Lemma lem1663606 (n : nat) (x : real) : (term143 n x) = (term117 n x).
Proof. exact (eq_refl (term143 n x)). Qed.
Lemma lem1663607 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1663608 (n : nat) (x : real) : (term144 n x) = (term119 n x).
Proof. exact (MK_COMB (@lem1663607) (@lem1663606 n x)). Qed.
Lemma lem1663609 (n : nat) (x : real) : (term145 n x) = (term122 n x).
Proof. exact (eq_refl (term145 n x)). Qed.
Lemma lem1663610 (n : nat) (x : real) : (term146 n x) = (term123 n x).
Proof. exact (MK_COMB (@lem1663608 n x) (@lem1663609 n x)). Qed.
Lemma lem1663611 (n : nat) : (term147 n) = (term129 n).
Proof. exact (fun_ext (fun x : real => @lem1663610 n x)). Qed.
Lemma lem1663612 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663613 (n : nat) : (term139 n) = (term137 n).
Proof. exact (MK_COMB (@lem1663612) (@lem1663611 n)). Qed.
Lemma lem1663614 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1663615 (n : nat) : (term148 n) = (term149 n).
Proof. exact (MK_COMB (@lem1663614) (@lem1663613 n)). Qed.
Lemma lem1663616 (n : nat) (x : real) : (term143 n x) = (term117 n x).
Proof. exact (eq_refl (term143 n x)). Qed.
Lemma lem1663617 (n : nat) : (term150 n) = (term141 n).
Proof. exact (fun_ext (fun x : real => @lem1663616 n x)). Qed.
Lemma lem1663618 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663619 (n : nat) : (term151 n) = (term152 n).
Proof. exact (MK_COMB (@lem1663618) (@lem1663617 n)). Qed.
Lemma lem1663620 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1663621 (n : nat) : (term153 n) = (term154 n).
Proof. exact (MK_COMB (@lem1663620) (@lem1663619 n)). Qed.
Lemma lem1663622 (n : nat) (x : real) : (term145 n x) = (term122 n x).
Proof. exact (eq_refl (term145 n x)). Qed.
Lemma lem1663623 (n : nat) : (term155 n) = (term142 n).
Proof. exact (fun_ext (fun x : real => @lem1663622 n x)). Qed.
Lemma lem1663624 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663625 (n : nat) : (term156 n) = (term157 n).
Proof. exact (MK_COMB (@lem1663624) (@lem1663623 n)). Qed.
Lemma lem1663626 (n : nat) : (term140 n) = (term158 n).
Proof. exact (MK_COMB (@lem1663621 n) (@lem1663625 n)). Qed.
Lemma lem1663627 (n : nat) : ((term139 n) = (term140 n)) = ((term137 n) = (term158 n)).
Proof. exact (MK_COMB (@lem1663615 n) (@lem1663626 n)). Qed.
Lemma lem1663628 (n : nat) : (term137 n) = (term158 n).
Proof. exact (EQ_MP (@lem1663627 n) (@lem1663605 n)). Qed.
Lemma lem1663733 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1663734 (n : nat) : (term138 n) = (term159 n).
Proof. exact (MK_COMB (@lem1663733 n) (@lem1663628 n)). Qed.
Lemma lem1663735 (n : nat) : (term126 n) = (term159 n).
Proof. exact (TRANS (@lem1663601 n) (@lem1663734 n)). Qed.
Lemma lem1663736 (n : nat) : (term72 n) = (term159 n).
Proof. exact (TRANS (@lem1663581 n) (@lem1663735 n)). Qed.
Lemma lem1663737 : term79 = term160.
Proof. exact (fun_ext (fun n : nat => @lem1663736 n)). Qed.
Lemma lem1663738 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1663739 : term80 = term161.
Proof. exact (MK_COMB (@lem1663738) (@lem1663737)). Qed.
Lemma lem1663769 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term98 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1663770 (P : real -> Prop) (Q : real -> Prop) : (term100 P Q) = (term99 P Q).
Proof. exact (@lem1663769 real P Q). Qed.
Lemma lem1663771 (n : nat) : (term140 n) = (term139 n).
Proof. exact (@lem1663770 (term141 n) (term142 n)). Qed.
Lemma lem1663772 (n : nat) (x : real) : (term143 n x) = (term117 n x).
Proof. exact (eq_refl (term143 n x)). Qed.
Lemma lem1663773 (n : nat) : (term150 n) = (term141 n).
Proof. exact (fun_ext (fun x : real => @lem1663772 n x)). Qed.
Lemma lem1663774 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663775 (n : nat) : (term151 n) = (term152 n).
Proof. exact (MK_COMB (@lem1663774) (@lem1663773 n)). Qed.
Lemma lem1663776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1663777 (n : nat) : (term153 n) = (term154 n).
Proof. exact (MK_COMB (@lem1663776) (@lem1663775 n)). Qed.
Lemma lem1663778 (n : nat) (x : real) : (term145 n x) = (term122 n x).
Proof. exact (eq_refl (term145 n x)). Qed.
Lemma lem1663779 (n : nat) : (term155 n) = (term142 n).
Proof. exact (fun_ext (fun x : real => @lem1663778 n x)). Qed.
Lemma lem1663780 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663781 (n : nat) : (term156 n) = (term157 n).
Proof. exact (MK_COMB (@lem1663780) (@lem1663779 n)). Qed.
Lemma lem1663782 (n : nat) : (term140 n) = (term158 n).
Proof. exact (MK_COMB (@lem1663777 n) (@lem1663781 n)). Qed.
Lemma lem1663783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1663784 (n : nat) : (term162 n) = (term163 n).
Proof. exact (MK_COMB (@lem1663783) (@lem1663782 n)). Qed.
Lemma lem1663785 (n : nat) (x : real) : (term143 n x) = (term117 n x).
Proof. exact (eq_refl (term143 n x)). Qed.
Lemma lem1663786 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1663787 (n : nat) (x : real) : (term144 n x) = (term119 n x).
Proof. exact (MK_COMB (@lem1663786) (@lem1663785 n x)). Qed.
Lemma lem1663788 (n : nat) (x : real) : (term145 n x) = (term122 n x).
Proof. exact (eq_refl (term145 n x)). Qed.
Lemma lem1663789 (n : nat) (x : real) : (term146 n x) = (term123 n x).
Proof. exact (MK_COMB (@lem1663787 n x) (@lem1663788 n x)). Qed.
Lemma lem1663790 (n : nat) : (term147 n) = (term129 n).
Proof. exact (fun_ext (fun x : real => @lem1663789 n x)). Qed.
Lemma lem1663791 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663792 (n : nat) : (term139 n) = (term137 n).
Proof. exact (MK_COMB (@lem1663791) (@lem1663790 n)). Qed.
Lemma lem1663793 (n : nat) : ((term140 n) = (term139 n)) = ((term158 n) = (term137 n)).
Proof. exact (MK_COMB (@lem1663784 n) (@lem1663792 n)). Qed.
Lemma lem1663794 (n : nat) : (term158 n) = (term137 n).
Proof. exact (EQ_MP (@lem1663793 n) (@lem1663771 n)). Qed.
Lemma lem1663796 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term98 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1663797 (P : real -> Prop) (Q : real -> Prop) : (term100 P Q) = (term99 P Q).
Proof. exact (@lem1663796 real P Q). Qed.
Lemma lem1663798 (n : nat) (x : real) : (term102 n x) = (term101 n x).
Proof. exact (@lem1663797 (term103 n x) (term104 n x)). Qed.
Lemma lem1663799 (n : nat) (x : real) (y : real) : (term105 n x y) = (term106 n x y).
Proof. exact (eq_refl (term105 n x y)). Qed.
Lemma lem1663800 (n : nat) (x : real) : (term115 n x) = (term103 n x).
Proof. exact (fun_ext (fun y : real => @lem1663799 n x y)). Qed.
Lemma lem1663801 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663802 (n : nat) (x : real) : (term116 n x) = (term117 n x).
Proof. exact (MK_COMB (@lem1663801) (@lem1663800 n x)). Qed.
Lemma lem1663803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1663804 (n : nat) (x : real) : (term118 n x) = (term119 n x).
Proof. exact (MK_COMB (@lem1663803) (@lem1663802 n x)). Qed.
Lemma lem1663805 (n : nat) (x : real) (y : real) : (term109 n x y) = (term110 n x y).
Proof. exact (eq_refl (term109 n x y)). Qed.
Lemma lem1663806 (n : nat) (x : real) : (term120 n x) = (term104 n x).
Proof. exact (fun_ext (fun y : real => @lem1663805 n x y)). Qed.
Lemma lem1663807 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663808 (n : nat) (x : real) : (term121 n x) = (term122 n x).
Proof. exact (MK_COMB (@lem1663807) (@lem1663806 n x)). Qed.
Lemma lem1663809 (n : nat) (x : real) : (term102 n x) = (term123 n x).
Proof. exact (MK_COMB (@lem1663804 n x) (@lem1663808 n x)). Qed.
Lemma lem1663810 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1663811 (n : nat) (x : real) : (term164 n x) = (term165 n x).
Proof. exact (MK_COMB (@lem1663810) (@lem1663809 n x)). Qed.
Lemma lem1663812 (n : nat) (x : real) (y : real) : (term105 n x y) = (term106 n x y).
Proof. exact (eq_refl (term105 n x y)). Qed.
Lemma lem1663813 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1663814 (n : nat) (x : real) (y : real) : (term107 n x y) = (term108 n x y).
Proof. exact (MK_COMB (@lem1663813) (@lem1663812 n x y)). Qed.
Lemma lem1663815 (n : nat) (x : real) (y : real) : (term109 n x y) = (term110 n x y).
Proof. exact (eq_refl (term109 n x y)). Qed.
Lemma lem1663816 (n : nat) (x : real) (y : real) : (term111 n x y) = (term51 n x y).
Proof. exact (MK_COMB (@lem1663814 n x y) (@lem1663815 n x y)). Qed.
Lemma lem1663817 (n : nat) (x : real) : (term112 n x) = (term87 n x).
Proof. exact (fun_ext (fun y : real => @lem1663816 n x y)). Qed.
Lemma lem1663818 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663819 (n : nat) (x : real) : (term101 n x) = (term95 n x).
Proof. exact (MK_COMB (@lem1663818) (@lem1663817 n x)). Qed.
Lemma lem1663820 (n : nat) (x : real) : ((term102 n x) = (term101 n x)) = ((term123 n x) = (term95 n x)).
Proof. exact (MK_COMB (@lem1663811 n x) (@lem1663819 n x)). Qed.
Lemma lem1663821 (n : nat) (x : real) : (term123 n x) = (term95 n x).
Proof. exact (EQ_MP (@lem1663820 n x) (@lem1663798 n x)). Qed.
Lemma lem1663822 (n : nat) : (term129 n) = (term166 n).
Proof. exact (fun_ext (fun x : real => @lem1663821 n x)). Qed.
Lemma lem1663823 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663824 (n : nat) : (term137 n) = (term167 n).
Proof. exact (MK_COMB (@lem1663823) (@lem1663822 n)). Qed.
Lemma lem1663825 (n : nat) : (term158 n) = (term167 n).
Proof. exact (TRANS (@lem1663794 n) (@lem1663824 n)). Qed.
Lemma lem1663826 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1663827 (n : nat) : (term159 n) = (term168 n).
Proof. exact (MK_COMB (@lem1663826 n) (@lem1663825 n)). Qed.
Lemma lem1663829 {A : Type'} (P : Prop) (Q : A -> Prop) : (term82 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1663830 (P : Prop) (Q : real -> Prop) : (term84 P Q) = (term83 P Q).
Proof. exact (@lem1663829 real P Q). Qed.
Lemma lem1663831 (n : nat) : (term169 n) = (term170 n).
Proof. exact (@lem1663830 (Coq.Arith.PeanoNat.Nat.Odd n) (term166 n)). Qed.
Lemma lem1663832 (n : nat) (x : real) : (term171 n x) = (term95 n x).
Proof. exact (eq_refl (term171 n x)). Qed.
Lemma lem1663833 (n : nat) : (term172 n) = (term166 n).
Proof. exact (fun_ext (fun x : real => @lem1663832 n x)). Qed.
Lemma lem1663834 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663835 (n : nat) : (term173 n) = (term167 n).
Proof. exact (MK_COMB (@lem1663834) (@lem1663833 n)). Qed.
Lemma lem1663836 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1663837 (n : nat) : (term169 n) = (term168 n).
Proof. exact (MK_COMB (@lem1663836 n) (@lem1663835 n)). Qed.
Lemma lem1663838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1663839 (n : nat) : (term174 n) = (term175 n).
Proof. exact (MK_COMB (@lem1663838) (@lem1663837 n)). Qed.
Lemma lem1663840 (n : nat) (x : real) : (term171 n x) = (term95 n x).
Proof. exact (eq_refl (term171 n x)). Qed.
Lemma lem1663841 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1663842 (n : nat) (x : real) : (term176 n x) = (term96 n x).
Proof. exact (MK_COMB (@lem1663841 n) (@lem1663840 n x)). Qed.
Lemma lem1663843 (n : nat) : (term177 n) = (term178 n).
Proof. exact (fun_ext (fun x : real => @lem1663842 n x)). Qed.
Lemma lem1663844 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663845 (n : nat) : (term170 n) = (term179 n).
Proof. exact (MK_COMB (@lem1663844) (@lem1663843 n)). Qed.
Lemma lem1663846 (n : nat) : ((term169 n) = (term170 n)) = ((term168 n) = (term179 n)).
Proof. exact (MK_COMB (@lem1663839 n) (@lem1663845 n)). Qed.
Lemma lem1663847 (n : nat) : (term168 n) = (term179 n).
Proof. exact (EQ_MP (@lem1663846 n) (@lem1663831 n)). Qed.
Lemma lem1663849 {A : Type'} (P : Prop) (Q : A -> Prop) : (term82 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1663850 (P : Prop) (Q : real -> Prop) : (term84 P Q) = (term83 P Q).
Proof. exact (@lem1663849 real P Q). Qed.
Lemma lem1663851 (n : nat) (x : real) : (term86 n x) = (term85 n x).
Proof. exact (@lem1663850 (Coq.Arith.PeanoNat.Nat.Odd n) (term87 n x)). Qed.
Lemma lem1663852 (n : nat) (x : real) (y : real) : (term88 n x y) = (term51 n x y).
Proof. exact (eq_refl (term88 n x y)). Qed.
Lemma lem1663853 (n : nat) (x : real) : (term93 n x) = (term87 n x).
Proof. exact (fun_ext (fun y : real => @lem1663852 n x y)). Qed.
Lemma lem1663854 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663855 (n : nat) (x : real) : (term94 n x) = (term95 n x).
Proof. exact (MK_COMB (@lem1663854) (@lem1663853 n x)). Qed.
Lemma lem1663856 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1663857 (n : nat) (x : real) : (term86 n x) = (term96 n x).
Proof. exact (MK_COMB (@lem1663856 n) (@lem1663855 n x)). Qed.
Lemma lem1663858 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1663859 (n : nat) (x : real) : (term180 n x) = (term181 n x).
Proof. exact (MK_COMB (@lem1663858) (@lem1663857 n x)). Qed.
Lemma lem1663860 (n : nat) (x : real) (y : real) : (term88 n x y) = (term51 n x y).
Proof. exact (eq_refl (term88 n x y)). Qed.
Lemma lem1663861 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1663862 (n : nat) (x : real) (y : real) : (term89 n x y) = (term55 n x y).
Proof. exact (MK_COMB (@lem1663861 n) (@lem1663860 n x y)). Qed.
Lemma lem1663863 (n : nat) (x : real) : (term90 n x) = (term64 n x).
Proof. exact (fun_ext (fun y : real => @lem1663862 n x y)). Qed.
Lemma lem1663864 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663865 (n : nat) (x : real) : (term85 n x) = (term65 n x).
Proof. exact (MK_COMB (@lem1663864) (@lem1663863 n x)). Qed.
Lemma lem1663866 (n : nat) (x : real) : ((term86 n x) = (term85 n x)) = ((term96 n x) = (term65 n x)).
Proof. exact (MK_COMB (@lem1663859 n x) (@lem1663865 n x)). Qed.
Lemma lem1663867 (n : nat) (x : real) : (term96 n x) = (term65 n x).
Proof. exact (EQ_MP (@lem1663866 n x) (@lem1663851 n x)). Qed.
Lemma lem1663868 (n : nat) : (term178 n) = (term71 n).
Proof. exact (fun_ext (fun x : real => @lem1663867 n x)). Qed.
Lemma lem1663869 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1663870 (n : nat) : (term179 n) = (term72 n).
Proof. exact (MK_COMB (@lem1663869) (@lem1663868 n)). Qed.
Lemma lem1663871 (n : nat) : (term168 n) = (term72 n).
Proof. exact (TRANS (@lem1663847 n) (@lem1663870 n)). Qed.
Lemma lem1663872 (n : nat) : (term159 n) = (term72 n).
Proof. exact (TRANS (@lem1663827 n) (@lem1663871 n)). Qed.
Lemma lem1663873 : term160 = term79.
Proof. exact (fun_ext (fun n : nat => @lem1663872 n)). Qed.
Lemma lem1663874 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1663875 : term161 = term80.
Proof. exact (MK_COMB (@lem1663874) (@lem1663873)). Qed.
Lemma lem1663876 : term80 = term80.
Proof. exact (TRANS (@lem1663739) (@lem1663875)). Qed.
Lemma lem1663877 : term10 = term80.
Proof. exact (TRANS (@lem1663424) (@lem1663876)). Qed.
Lemma lem1663878 (h1 : term10) : term80.
Proof. exact (EQ_MP (@lem1663877) (@lem1663370 h1)). Qed.
Lemma lem1663882 (x : real) (y : real) : (term182 x y) = (real_le x y).
Proof. exact (@lem16933 (real_le x y)). Qed.
Lemma lem1663884 (y : real) (x : real) : (real_lt y x) = (real_lt y x).
Proof. exact (eq_refl (real_lt y x)). Qed.
Lemma lem1663885 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1663886 (x : real) (y : real) : (term183 x y) = (term184 x y).
Proof. exact (MK_COMB (@lem1663885) (@lem1663882 x y)). Qed.
Lemma lem1663887 (y : real) (x : real) : (term185 y x) = (term186 y x).
Proof. exact (MK_COMB (@lem1663886 x y) (@lem1663884 y x)). Qed.
Lemma lem1663892 (y : real) (x : real) : (term187 y x) = (term187 y x).
Proof. exact (eq_refl (term187 y x)). Qed.
Lemma lem1663893 (y : real) (x : real) : (term188 y x) = (term189 y x).
Proof. exact (MK_COMB (@lem1663892 y x) (@lem1663887 y x)). Qed.
Lemma lem1663894 (y : real) (x : real) : ((term39 x y) = (real_lt y x)) = (term188 y x).
Proof. exact (@lem17784 (term39 x y) (real_lt y x)). Qed.
Lemma lem1663895 (y : real) (x : real) : ((term39 x y) = (real_lt y x)) = (term189 y x).
Proof. exact (TRANS (@lem1663894 y x) (@lem1663893 y x)). Qed.
Lemma lem1663896 (x : real) : (term40 x) = (term190 x).
Proof. exact (fun_ext (fun y : real => @lem1663895 y x)). Qed.
Lemma lem1663897 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1663898 (x : real) : (term41 x) = (term191 x).
Proof. exact (MK_COMB (@lem1663897) (@lem1663896 x)). Qed.
Lemma lem1663899 : term42 = term192.
Proof. exact (fun_ext (fun x : real => @lem1663898 x)). Qed.
Lemma lem1663900 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1663901 : term43 = term193.
Proof. exact (MK_COMB (@lem1663900) (@lem1663899)). Qed.
Lemma lem1663907 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1663908 (P : real -> Prop) (Q : real -> Prop) : (term196 P Q) = (term197 P Q).
Proof. exact (@lem1663907 real P Q). Qed.
Lemma lem1663909 (x : real) : (term198 x) = (term199 x).
Proof. exact (@lem1663908 (term200 x) (term201 x)). Qed.
Lemma lem1663910 (y : real) (x : real) : (term202 x y) = (term203 y x).
Proof. exact (eq_refl (term202 x y)). Qed.
Lemma lem1663911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1663912 (y : real) (x : real) : (term204 x y) = (term187 y x).
Proof. exact (MK_COMB (@lem1663911) (@lem1663910 y x)). Qed.
Lemma lem1663913 (y : real) (x : real) : (term205 x y) = (term186 y x).
Proof. exact (eq_refl (term205 x y)). Qed.
Lemma lem1663914 (y : real) (x : real) : (term206 x y) = (term189 y x).
Proof. exact (MK_COMB (@lem1663912 y x) (@lem1663913 y x)). Qed.
Lemma lem1663915 (x : real) : (term207 x) = (term190 x).
Proof. exact (fun_ext (fun y : real => @lem1663914 y x)). Qed.
Lemma lem1663916 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1663917 (x : real) : (term198 x) = (term191 x).
Proof. exact (MK_COMB (@lem1663916) (@lem1663915 x)). Qed.
Lemma lem1663918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1663919 (x : real) : (term208 x) = (term209 x).
Proof. exact (MK_COMB (@lem1663918) (@lem1663917 x)). Qed.
Lemma lem1663920 (y : real) (x : real) : (term202 x y) = (term203 y x).
Proof. exact (eq_refl (term202 x y)). Qed.
Lemma lem1663921 (x : real) : (term210 x) = (term200 x).
Proof. exact (fun_ext (fun y : real => @lem1663920 y x)). Qed.
Lemma lem1663922 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1663923 (x : real) : (term211 x) = (term212 x).
Proof. exact (MK_COMB (@lem1663922) (@lem1663921 x)). Qed.
Lemma lem1663924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1663925 (x : real) : (term213 x) = (term214 x).
Proof. exact (MK_COMB (@lem1663924) (@lem1663923 x)). Qed.
Lemma lem1663926 (y : real) (x : real) : (term205 x y) = (term186 y x).
Proof. exact (eq_refl (term205 x y)). Qed.
Lemma lem1663927 (x : real) : (term215 x) = (term201 x).
Proof. exact (fun_ext (fun y : real => @lem1663926 y x)). Qed.
Lemma lem1663928 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1663929 (x : real) : (term216 x) = (term217 x).
Proof. exact (MK_COMB (@lem1663928) (@lem1663927 x)). Qed.
Lemma lem1663930 (x : real) : (term199 x) = (term218 x).
Proof. exact (MK_COMB (@lem1663925 x) (@lem1663929 x)). Qed.
Lemma lem1663931 (x : real) : ((term198 x) = (term199 x)) = ((term191 x) = (term218 x)).
Proof. exact (MK_COMB (@lem1663919 x) (@lem1663930 x)). Qed.
Lemma lem1663932 (x : real) : (term191 x) = (term218 x).
Proof. exact (EQ_MP (@lem1663931 x) (@lem1663909 x)). Qed.
Lemma lem1664029 : term192 = term219.
Proof. exact (fun_ext (fun x : real => @lem1663932 x)). Qed.
Lemma lem1664030 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664031 : term193 = term220.
Proof. exact (MK_COMB (@lem1664030) (@lem1664029)). Qed.
Lemma lem1664033 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1664034 (P : real -> Prop) (Q : real -> Prop) : (term196 P Q) = (term197 P Q).
Proof. exact (@lem1664033 real P Q). Qed.
Lemma lem1664035 : term221 = term222.
Proof. exact (@lem1664034 term223 term224). Qed.
Lemma lem1664036 (x : real) : (term225 x) = (term212 x).
Proof. exact (eq_refl (term225 x)). Qed.
Lemma lem1664037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1664038 (x : real) : (term226 x) = (term214 x).
Proof. exact (MK_COMB (@lem1664037) (@lem1664036 x)). Qed.
Lemma lem1664039 (x : real) : (term227 x) = (term217 x).
Proof. exact (eq_refl (term227 x)). Qed.
Lemma lem1664040 (x : real) : (term228 x) = (term218 x).
Proof. exact (MK_COMB (@lem1664038 x) (@lem1664039 x)). Qed.
Lemma lem1664041 : term229 = term219.
Proof. exact (fun_ext (fun x : real => @lem1664040 x)). Qed.
Lemma lem1664042 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664043 : term221 = term220.
Proof. exact (MK_COMB (@lem1664042) (@lem1664041)). Qed.
Lemma lem1664044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1664045 : term230 = term231.
Proof. exact (MK_COMB (@lem1664044) (@lem1664043)). Qed.
Lemma lem1664046 (x : real) : (term225 x) = (term212 x).
Proof. exact (eq_refl (term225 x)). Qed.
Lemma lem1664047 : term232 = term223.
Proof. exact (fun_ext (fun x : real => @lem1664046 x)). Qed.
Lemma lem1664048 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664049 : term233 = term234.
Proof. exact (MK_COMB (@lem1664048) (@lem1664047)). Qed.
Lemma lem1664050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1664051 : term235 = term236.
Proof. exact (MK_COMB (@lem1664050) (@lem1664049)). Qed.
Lemma lem1664052 (x : real) : (term227 x) = (term217 x).
Proof. exact (eq_refl (term227 x)). Qed.
Lemma lem1664053 : term237 = term224.
Proof. exact (fun_ext (fun x : real => @lem1664052 x)). Qed.
Lemma lem1664054 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664055 : term238 = term239.
Proof. exact (MK_COMB (@lem1664054) (@lem1664053)). Qed.
Lemma lem1664056 : term222 = term240.
Proof. exact (MK_COMB (@lem1664051) (@lem1664055)). Qed.
Lemma lem1664057 : (term221 = term222) = (term220 = term240).
Proof. exact (MK_COMB (@lem1664045) (@lem1664056)). Qed.
Lemma lem1664058 : term220 = term240.
Proof. exact (EQ_MP (@lem1664057) (@lem1664035)). Qed.
Lemma lem1664165 : term193 = term240.
Proof. exact (TRANS (@lem1664031) (@lem1664058)). Qed.
Lemma lem1664166 : term43 = term240.
Proof. exact (TRANS (@lem1663901) (@lem1664165)). Qed.
Lemma lem1664167 (h1 : term43) : term240.
Proof. exact (EQ_MP (@lem1664166) (@lem1663371 h1)). Qed.
Lemma lem1664174 (x : real) (y : real) (n : nat) : (term241 x y n) = (term242 x y n).
Proof. exact (@lem17045 (real_le x y) (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem1664175 (x : real) (y : real) (n : nat) : (term52 x y n) = (term52 x y n).
Proof. exact (eq_refl (term52 x y n)). Qed.
Lemma lem1664176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1664177 (x : real) (y : real) (n : nat) : (term243 x y n) = (term244 x y n).
Proof. exact (MK_COMB (@lem1664176) (@lem1664174 x y n)). Qed.
Lemma lem1664178 (x : real) (y : real) (n : nat) : (term245 x y n) = (term246 x y n).
Proof. exact (MK_COMB (@lem1664177 x y n) (@lem1664175 x y n)). Qed.
Lemma lem1664179 (x : real) (y : real) (n : nat) : (term32 x y n) = (term245 x y n).
Proof. exact (@lem17265 (term247 x y n) (term52 x y n)). Qed.
Lemma lem1664180 (x : real) (y : real) (n : nat) : (term32 x y n) = (term246 x y n).
Proof. exact (TRANS (@lem1664179 x y n) (@lem1664178 x y n)). Qed.
Lemma lem1664181 (x : real) (n : nat) : (term33 x n) = (term248 x n).
Proof. exact (fun_ext (fun y : real => @lem1664180 x y n)). Qed.
Lemma lem1664182 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664183 (x : real) (n : nat) : (term34 x n) = (term249 x n).
Proof. exact (MK_COMB (@lem1664182) (@lem1664181 x n)). Qed.
Lemma lem1664184 (n : nat) : (term35 n) = (term250 n).
Proof. exact (fun_ext (fun x : real => @lem1664183 x n)). Qed.
Lemma lem1664185 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664186 (n : nat) : (term36 n) = (term251 n).
Proof. exact (MK_COMB (@lem1664185) (@lem1664184 n)). Qed.
Lemma lem1664187 : term37 = term252.
Proof. exact (fun_ext (fun n : nat => @lem1664186 n)). Qed.
Lemma lem1664188 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1664249 : term38 = term253.
Proof. exact (MK_COMB (@lem1664188) (@lem1664187)). Qed.
Lemma lem1664250 (h1 : term38) : term253.
Proof. exact (EQ_MP (@lem1664249) (@lem1663372 h1)). Qed.
Lemma lem1664257 (x : real) (y : real) (n : nat) : (term254 x y n) = (term255 x y n).
Proof. exact (@lem17045 (real_lt x y) (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem1664258 (x : real) (y : real) (n : nat) : (term256 x y n) = (term256 x y n).
Proof. exact (eq_refl (term256 x y n)). Qed.
Lemma lem1664259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1664260 (x : real) (y : real) (n : nat) : (term257 x y n) = (term258 x y n).
Proof. exact (MK_COMB (@lem1664259) (@lem1664257 x y n)). Qed.
Lemma lem1664261 (x : real) (y : real) (n : nat) : (term259 x y n) = (term260 x y n).
Proof. exact (MK_COMB (@lem1664260 x y n) (@lem1664258 x y n)). Qed.
Lemma lem1664262 (x : real) (y : real) (n : nat) : (term26 x y n) = (term259 x y n).
Proof. exact (@lem17265 (term261 x y n) (term256 x y n)). Qed.
Lemma lem1664263 (x : real) (y : real) (n : nat) : (term26 x y n) = (term260 x y n).
Proof. exact (TRANS (@lem1664262 x y n) (@lem1664261 x y n)). Qed.
Lemma lem1664264 (x : real) (n : nat) : (term27 x n) = (term262 x n).
Proof. exact (fun_ext (fun y : real => @lem1664263 x y n)). Qed.
Lemma lem1664265 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664266 (x : real) (n : nat) : (term28 x n) = (term263 x n).
Proof. exact (MK_COMB (@lem1664265) (@lem1664264 x n)). Qed.
Lemma lem1664267 (n : nat) : (term29 n) = (term264 n).
Proof. exact (fun_ext (fun x : real => @lem1664266 x n)). Qed.
Lemma lem1664268 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664269 (n : nat) : (term30 n) = (term265 n).
Proof. exact (MK_COMB (@lem1664268) (@lem1664267 n)). Qed.
Lemma lem1664270 : term31 = term266.
Proof. exact (fun_ext (fun n : nat => @lem1664269 n)). Qed.
Lemma lem1664271 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1664332 : term17 = term267.
Proof. exact (MK_COMB (@lem1664271) (@lem1664270)). Qed.
Lemma lem1664333 (h1 : term17) : term267.
Proof. exact (EQ_MP (@lem1664332) (@lem1663373 h1)). Qed.
Lemma lem1664334 (n : nat) (h1 : term72 n) : term72 n.
Proof. exact (h1). Qed.
Lemma lem1664335 (n : nat) (x : real) (h1 : term65 n x) : term65 n x.
Proof. exact (h1). Qed.
Lemma lem1664349 (y : real) (x : real) : (term186 y x) = (term186 y x).
Proof. exact (eq_refl (term186 y x)). Qed.
Lemma lem1664350 (x : real) : (term201 x) = (term201 x).
Proof. exact (fun_ext (fun y : real => @lem1664349 y x)). Qed.
Lemma lem1664351 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664352 (x : real) : (term217 x) = (term217 x).
Proof. exact (MK_COMB (@lem1664351) (@lem1664350 x)). Qed.
Lemma lem1664353 : term224 = term224.
Proof. exact (fun_ext (fun x : real => @lem1664352 x)). Qed.
Lemma lem1664354 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664355 : term239 = term239.
Proof. exact (MK_COMB (@lem1664354) (@lem1664353)). Qed.
Lemma lem1664372 (y : real) (x : real) : (term203 y x) = (term203 y x).
Proof. exact (eq_refl (term203 y x)). Qed.
Lemma lem1664373 (x : real) : (term200 x) = (term200 x).
Proof. exact (fun_ext (fun y : real => @lem1664372 y x)). Qed.
Lemma lem1664374 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664375 (x : real) : (term212 x) = (term212 x).
Proof. exact (MK_COMB (@lem1664374) (@lem1664373 x)). Qed.
Lemma lem1664376 : term223 = term223.
Proof. exact (fun_ext (fun x : real => @lem1664375 x)). Qed.
Lemma lem1664377 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664378 : term234 = term234.
Proof. exact (MK_COMB (@lem1664377) (@lem1664376)). Qed.
Lemma lem1664379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1664380 : term236 = term236.
Proof. exact (MK_COMB (@lem1664379) (@lem1664378)). Qed.
Lemma lem1664381 : term240 = term240.
Proof. exact (MK_COMB (@lem1664380) (@lem1664355)). Qed.
Lemma lem1664382 (h1 : term43) : term240.
Proof. exact (EQ_MP (@lem1664381) (@lem1664167 h1)). Qed.
Lemma lem1664413 (x : real) (y : real) (n : nat) : (term246 x y n) = (term246 x y n).
Proof. exact (eq_refl (term246 x y n)). Qed.
Lemma lem1664414 (x : real) (n : nat) : (term248 x n) = (term248 x n).
Proof. exact (fun_ext (fun y : real => @lem1664413 x y n)). Qed.
Lemma lem1664415 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664416 (x : real) (n : nat) : (term249 x n) = (term249 x n).
Proof. exact (MK_COMB (@lem1664415) (@lem1664414 x n)). Qed.
Lemma lem1664417 (n : nat) : (term250 n) = (term250 n).
Proof. exact (fun_ext (fun x : real => @lem1664416 x n)). Qed.
Lemma lem1664418 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664419 (n : nat) : (term251 n) = (term251 n).
Proof. exact (MK_COMB (@lem1664418) (@lem1664417 n)). Qed.
Lemma lem1664420 : term252 = term252.
Proof. exact (fun_ext (fun n : nat => @lem1664419 n)). Qed.
Lemma lem1664421 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1664422 : term253 = term253.
Proof. exact (MK_COMB (@lem1664421) (@lem1664420)). Qed.
Lemma lem1664423 (h1 : term38) : term253.
Proof. exact (EQ_MP (@lem1664422) (@lem1664250 h1)). Qed.
Lemma lem1664454 (x : real) (y : real) (n : nat) : (term260 x y n) = (term260 x y n).
Proof. exact (eq_refl (term260 x y n)). Qed.
Lemma lem1664455 (x : real) (n : nat) : (term262 x n) = (term262 x n).
Proof. exact (fun_ext (fun y : real => @lem1664454 x y n)). Qed.
Lemma lem1664456 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664457 (x : real) (n : nat) : (term263 x n) = (term263 x n).
Proof. exact (MK_COMB (@lem1664456) (@lem1664455 x n)). Qed.
Lemma lem1664458 (n : nat) : (term264 n) = (term264 n).
Proof. exact (fun_ext (fun x : real => @lem1664457 x n)). Qed.
Lemma lem1664459 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664460 (n : nat) : (term265 n) = (term265 n).
Proof. exact (MK_COMB (@lem1664459) (@lem1664458 n)). Qed.
Lemma lem1664461 : term266 = term266.
Proof. exact (fun_ext (fun n : nat => @lem1664460 n)). Qed.
Lemma lem1664462 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1664463 : term267 = term267.
Proof. exact (MK_COMB (@lem1664462) (@lem1664461)). Qed.
Lemma lem1664464 (h1 : term17) : term267.
Proof. exact (EQ_MP (@lem1664463) (@lem1664333 h1)). Qed.
Lemma lem1664520 (n : nat) (x : real) (y : real) (h1 : term55 n x y) : term55 n x y.
Proof. exact (h1). Qed.
Lemma lem1664521 (n : nat) (x : real) (y : real) (h1 : term55 n x y) : term51 n x y.
Proof. exact (proj2 (@lem1664520 n x y h1)). Qed.
Lemma lem1664523 (h1 : term43) : term239.
Proof. exact (proj2 (@lem1664382 h1)). Qed.
Lemma lem1664524 (h1 : term43) : term234.
Proof. exact (proj1 (@lem1664382 h1)). Qed.
Lemma lem1664525 (n : nat) (x : real) (y : real) (h1 : term106 n x y) : term106 n x y.
Proof. exact (h1). Qed.
Lemma lem1664526 (n : nat) (x : real) (y : real) (h1 : term110 n x y) : term110 n x y.
Proof. exact (h1). Qed.
Lemma lem1664569 (x : real) (y : real) (n : nat) : (term260 x y n) = (term260 x y n).
Proof. exact (eq_refl (term260 x y n)). Qed.
Lemma lem1664570 (x : real) (n : nat) : (term262 x n) = (term262 x n).
Proof. exact (fun_ext (fun y : real => @lem1664569 x y n)). Qed.
Lemma lem1664571 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664572 (x : real) (n : nat) : (term263 x n) = (term263 x n).
Proof. exact (MK_COMB (@lem1664571) (@lem1664570 x n)). Qed.
Lemma lem1664573 (n : nat) : (term264 n) = (term264 n).
Proof. exact (fun_ext (fun x : real => @lem1664572 x n)). Qed.
Lemma lem1664574 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664575 (n : nat) : (term265 n) = (term265 n).
Proof. exact (MK_COMB (@lem1664574) (@lem1664573 n)). Qed.
Lemma lem1664576 : term266 = term266.
Proof. exact (fun_ext (fun n : nat => @lem1664575 n)). Qed.
Lemma lem1664577 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1664579 : term267 = term267.
Proof. exact (MK_COMB (@lem1664577) (@lem1664576)). Qed.
Lemma lem1664580 (h1 : term17) : term267.
Proof. exact (EQ_MP (@lem1664579) (@lem1664464 h1)). Qed.
Lemma lem1664592 (y : real) (x : real) : (term203 y x) = (term203 y x).
Proof. exact (eq_refl (term203 y x)). Qed.
Lemma lem1664593 (x : real) : (term200 x) = (term200 x).
Proof. exact (fun_ext (fun y : real => @lem1664592 y x)). Qed.
Lemma lem1664594 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664595 (x : real) : (term212 x) = (term212 x).
Proof. exact (MK_COMB (@lem1664594) (@lem1664593 x)). Qed.
Lemma lem1664596 : term223 = term223.
Proof. exact (fun_ext (fun x : real => @lem1664595 x)). Qed.
Lemma lem1664597 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664599 : term234 = term234.
Proof. exact (MK_COMB (@lem1664597) (@lem1664596)). Qed.
Lemma lem1664600 (h1 : term43) : term234.
Proof. exact (EQ_MP (@lem1664599) (@lem1664524 h1)). Qed.
Lemma lem1664608 (y : real) (x : real) : (term186 y x) = (term186 y x).
Proof. exact (eq_refl (term186 y x)). Qed.
Lemma lem1664609 (x : real) : (term201 x) = (term201 x).
Proof. exact (fun_ext (fun y : real => @lem1664608 y x)). Qed.
Lemma lem1664610 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664611 (x : real) : (term217 x) = (term217 x).
Proof. exact (MK_COMB (@lem1664610) (@lem1664609 x)). Qed.
Lemma lem1664612 : term224 = term224.
Proof. exact (fun_ext (fun x : real => @lem1664611 x)). Qed.
Lemma lem1664613 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664615 : term239 = term239.
Proof. exact (MK_COMB (@lem1664613) (@lem1664612)). Qed.
Lemma lem1664616 (h1 : term43) : term239.
Proof. exact (EQ_MP (@lem1664615) (@lem1664523 h1)). Qed.
Lemma lem1664638 (x : real) (y : real) (n : nat) : (term246 x y n) = (term246 x y n).
Proof. exact (eq_refl (term246 x y n)). Qed.
Lemma lem1664639 (x : real) (n : nat) : (term248 x n) = (term248 x n).
Proof. exact (fun_ext (fun y : real => @lem1664638 x y n)). Qed.
Lemma lem1664640 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664641 (x : real) (n : nat) : (term249 x n) = (term249 x n).
Proof. exact (MK_COMB (@lem1664640) (@lem1664639 x n)). Qed.
Lemma lem1664642 (n : nat) : (term250 n) = (term250 n).
Proof. exact (fun_ext (fun x : real => @lem1664641 x n)). Qed.
Lemma lem1664643 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1664644 (n : nat) : (term251 n) = (term251 n).
Proof. exact (MK_COMB (@lem1664643) (@lem1664642 n)). Qed.
Lemma lem1664645 : term252 = term252.
Proof. exact (fun_ext (fun n : nat => @lem1664644 n)). Qed.
Lemma lem1664646 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1664648 : term253 = term253.
Proof. exact (MK_COMB (@lem1664646) (@lem1664645)). Qed.
Lemma lem1664649 (h1 : term38) : term253.
Proof. exact (EQ_MP (@lem1664648) (@lem1664423 h1)). Qed.
Lemma lem1664728 (_25748 : nat) (h1 : term17) : term268 _25748.
Proof. exact (@lem1664580 h1 _25748). Qed.
Lemma lem1664729 (_25748 : nat) : (term268 _25748) = (term265 _25748).
Proof. exact (eq_refl (term268 _25748)). Qed.
Lemma lem1664730 (_25748 : nat) (h1 : term17) : term265 _25748.
Proof. exact (EQ_MP (@lem1664729 _25748) (@lem1664728 _25748 h1)). Qed.
Lemma lem1664731 (_25748 : nat) (_25749 : real) (h1 : term17) : term269 _25748 _25749.
Proof. exact (@lem1664730 _25748 h1 _25749). Qed.
Lemma lem1664732 (_25749 : real) (_25748 : nat) : (term269 _25748 _25749) = (term263 _25749 _25748).
Proof. exact (eq_refl (term269 _25748 _25749)). Qed.
Lemma lem1664733 (_25749 : real) (_25748 : nat) (h1 : term17) : term263 _25749 _25748.
Proof. exact (EQ_MP (@lem1664732 _25749 _25748) (@lem1664731 _25748 _25749 h1)). Qed.
Lemma lem1664734 (_25749 : real) (_25748 : nat) (_25750 : real) (h1 : term17) : term270 _25749 _25748 _25750.
Proof. exact (@lem1664733 _25749 _25748 h1 _25750). Qed.
Lemma lem1664735 (_25749 : real) (_25750 : real) (_25748 : nat) : (term270 _25749 _25748 _25750) = (term260 _25749 _25750 _25748).
Proof. exact (eq_refl (term270 _25749 _25748 _25750)). Qed.
Lemma lem1664736 (_25749 : real) (_25750 : real) (_25748 : nat) (h1 : term17) : term260 _25749 _25750 _25748.
Proof. exact (EQ_MP (@lem1664735 _25749 _25750 _25748) (@lem1664734 _25749 _25748 _25750 h1)). Qed.
Lemma lem1664737 (_25751 : real) (h1 : term43) : term225 _25751.
Proof. exact (@lem1664600 h1 _25751). Qed.
Lemma lem1664738 (_25751 : real) : (term225 _25751) = (term212 _25751).
Proof. exact (eq_refl (term225 _25751)). Qed.
Lemma lem1664739 (_25751 : real) (h1 : term43) : term212 _25751.
Proof. exact (EQ_MP (@lem1664738 _25751) (@lem1664737 _25751 h1)). Qed.
Lemma lem1664740 (_25751 : real) (_25752 : real) (h1 : term43) : term202 _25751 _25752.
Proof. exact (@lem1664739 _25751 h1 _25752). Qed.
Lemma lem1664741 (_25752 : real) (_25751 : real) : (term202 _25751 _25752) = (term203 _25752 _25751).
Proof. exact (eq_refl (term202 _25751 _25752)). Qed.
Lemma lem1664743 (_25753 : real) (h1 : term43) : term227 _25753.
Proof. exact (@lem1664616 h1 _25753). Qed.
Lemma lem1664744 (_25753 : real) : (term227 _25753) = (term217 _25753).
Proof. exact (eq_refl (term227 _25753)). Qed.
Lemma lem1664745 (_25753 : real) (h1 : term43) : term217 _25753.
Proof. exact (EQ_MP (@lem1664744 _25753) (@lem1664743 _25753 h1)). Qed.
Lemma lem1664746 (_25753 : real) (_25754 : real) (h1 : term43) : term205 _25753 _25754.
Proof. exact (@lem1664745 _25753 h1 _25754). Qed.
Lemma lem1664747 (_25754 : real) (_25753 : real) : (term205 _25753 _25754) = (term186 _25754 _25753).
Proof. exact (eq_refl (term205 _25753 _25754)). Qed.
Lemma lem1664749 (_25755 : nat) (h1 : term38) : term271 _25755.
Proof. exact (@lem1664649 h1 _25755). Qed.
Lemma lem1664750 (_25755 : nat) : (term271 _25755) = (term251 _25755).
Proof. exact (eq_refl (term271 _25755)). Qed.
Lemma lem1664751 (_25755 : nat) (h1 : term38) : term251 _25755.
Proof. exact (EQ_MP (@lem1664750 _25755) (@lem1664749 _25755 h1)). Qed.
Lemma lem1664752 (_25755 : nat) (_25756 : real) (h1 : term38) : term272 _25755 _25756.
Proof. exact (@lem1664751 _25755 h1 _25756). Qed.
Lemma lem1664753 (_25756 : real) (_25755 : nat) : (term272 _25755 _25756) = (term249 _25756 _25755).
Proof. exact (eq_refl (term272 _25755 _25756)). Qed.
Lemma lem1664754 (_25756 : real) (_25755 : nat) (h1 : term38) : term249 _25756 _25755.
Proof. exact (EQ_MP (@lem1664753 _25756 _25755) (@lem1664752 _25755 _25756 h1)). Qed.
Lemma lem1664755 (_25756 : real) (_25755 : nat) (_25757 : real) (h1 : term38) : term273 _25756 _25755 _25757.
Proof. exact (@lem1664754 _25756 _25755 h1 _25757). Qed.
Lemma lem1664756 (_25756 : real) (_25757 : real) (_25755 : nat) : (term273 _25756 _25755 _25757) = (term246 _25756 _25757 _25755).
Proof. exact (eq_refl (term273 _25756 _25755 _25757)). Qed.
Lemma lem1664757 (_25756 : real) (_25757 : real) (_25755 : nat) (h1 : term38) : term246 _25756 _25757 _25755.
Proof. exact (EQ_MP (@lem1664756 _25756 _25757 _25755) (@lem1664755 _25756 _25755 _25757 h1)). Qed.
Lemma lem1664801 (_25749 : real) (_25750 : real) (_25748 : nat) : (term260 _25749 _25750 _25748) = (term274 _25749 _25750 _25748).
Proof. exact (@lem1663104 (term275 _25749 _25750) (term276 _25748) (term256 _25749 _25750 _25748)). Qed.
Lemma lem1664802 (_25749 : real) (_25750 : real) (_25748 : nat) (h1 : term17) : term274 _25749 _25750 _25748.
Proof. exact (EQ_MP (@lem1664801 _25749 _25750 _25748) (@lem1664736 _25749 _25750 _25748 h1)). Qed.
Lemma lem1664810 (_25752 : real) (_25751 : real) (h1 : term43) : term203 _25752 _25751.
Proof. exact (EQ_MP (@lem1664741 _25752 _25751) (@lem1664740 _25751 _25752 h1)). Qed.
Lemma lem1664816 (_25754 : real) (_25753 : real) (h1 : term43) : term186 _25754 _25753.
Proof. exact (EQ_MP (@lem1664747 _25754 _25753) (@lem1664746 _25753 _25754 h1)). Qed.
Lemma lem1664820 (n : nat) (x : real) (y : real) (h1 : term106 n x y) : term39 x y.
Proof. exact (proj2 (@lem1664525 n x y h1)). Qed.
Lemma lem1664831 (_25756 : real) (_25757 : real) (_25755 : nat) : (term246 _25756 _25757 _25755) = (term277 _25756 _25757 _25755).
Proof. exact (@lem1663104 (term39 _25756 _25757) (term276 _25755) (term52 _25756 _25757 _25755)). Qed.
Lemma lem1664832 (_25756 : real) (_25757 : real) (_25755 : nat) (h1 : term38) : term277 _25756 _25757 _25755.
Proof. exact (EQ_MP (@lem1664831 _25756 _25757 _25755) (@lem1664757 _25756 _25757 _25755 h1)). Qed.
Lemma lem1664860 (n : nat) (x : real) (y : real) (h1 : term110 n x y) : term278 x y n.
Proof. exact (proj1 (@lem1664526 n x y h1)). Qed.
Lemma lem1664864 (n : nat) (x : real) (y : real) (h1 : term55 n x y) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (proj1 (@lem1664520 n x y h1)). Qed.
Lemma lem1664865 (n : nat) (x : real) (y : real) (h1 : term55 n x y) : term279 n.
Proof. exact (fun h0 : term276 n => @lem1664864 n x y h1). Qed.
Lemma lem1664867 (p : Prop) : (term280 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1664868 (n : nat) : (term279 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (@lem1664867 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem1664869 (n : nat) (x : real) (y : real) (h1 : term55 n x y) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (EQ_MP (@lem1664868 n) (@lem1664865 n x y h1)). Qed.
Lemma lem1664871 (n : nat) (x : real) (y : real) (h1 : term106 n x y) : term52 x y n.
Proof. exact (proj1 (@lem1664525 n x y h1)). Qed.
Lemma lem1664872 (n : nat) (x : real) (y : real) (h1 : term106 n x y) : term281 x y n.
Proof. exact (fun h0 : term278 x y n => @lem1664871 n x y h1). Qed.
Lemma lem1664874 (p : Prop) : (term280 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1664875 (x : real) (y : real) (n : nat) : (term281 x y n) = (term52 x y n).
Proof. exact (@lem1664874 (term52 x y n)). Qed.
Lemma lem1664876 (n : nat) (x : real) (y : real) (h1 : term106 n x y) : term52 x y n.
Proof. exact (EQ_MP (@lem1664875 x y n) (@lem1664872 n x y h1)). Qed.
Lemma lem1664887 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1664888 (_25752 : real) (_25751 : real) : (term282 _25751 _25752) = (term203 _25752 _25751).
Proof. exact (@lem1664887 (term39 _25751 _25752) (term275 _25752 _25751)). Qed.
Lemma lem1664894 (_25752 : real) (_25751 : real) : (term283 _25752 _25751) = (term283 _25752 _25751).
Proof. exact (eq_refl (term283 _25752 _25751)). Qed.
Lemma lem1664895 (_25752 : real) (_25751 : real) : ((term203 _25752 _25751) = (term282 _25751 _25752)) = ((term203 _25752 _25751) = (term203 _25752 _25751)).
Proof. exact (MK_COMB (@lem1664894 _25752 _25751) (@lem1664888 _25752 _25751)). Qed.
Lemma lem1664897 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1664898 (x : Prop) : (x = x) = True.
Proof. exact (@lem1664897 Prop x). Qed.
Lemma lem1664899 (_25752 : real) (_25751 : real) : ((term203 _25752 _25751) = (term203 _25752 _25751)) = True.
Proof. exact (@lem1664898 (term203 _25752 _25751)). Qed.
Lemma lem1664900 (_25751 : real) (_25752 : real) : ((term203 _25752 _25751) = (term282 _25751 _25752)) = True.
Proof. exact (TRANS (@lem1664895 _25752 _25751) (@lem1664899 _25752 _25751)). Qed.
Lemma lem1664901 (_25751 : real) (_25752 : real) : True = ((term203 _25752 _25751) = (term282 _25751 _25752)).
Proof. exact (SYM (@lem1664900 _25751 _25752)). Qed.
Lemma lem1664902 (_25751 : real) (_25752 : real) : (term203 _25752 _25751) = (term282 _25751 _25752).
Proof. exact (EQ_MP (@lem1664901 _25751 _25752) (@lem0)). Qed.
Lemma lem1664903 (_25751 : real) (_25752 : real) (h1 : term43) : term282 _25751 _25752.
Proof. exact (EQ_MP (@lem1664902 _25751 _25752) (@lem1664810 _25752 _25751 h1)). Qed.
Lemma lem1664905 (b : Prop) (a : Prop) : (a \/ b) = (term284 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1664906 (_25752 : real) (_25751 : real) : (term282 _25751 _25752) = (term285 _25752 _25751).
Proof. exact (@lem1664905 (term39 _25751 _25752) (term275 _25752 _25751)). Qed.
Lemma lem1664908 (a : Prop) : (term286 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1664909 (_25751 : real) (_25752 : real) : (term182 _25751 _25752) = (real_le _25751 _25752).
Proof. exact (@lem1664908 (real_le _25751 _25752)). Qed.
Lemma lem1664910 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1664911 (_25751 : real) (_25752 : real) : (term287 _25751 _25752) = (term288 _25751 _25752).
Proof. exact (MK_COMB (@lem1664910) (@lem1664909 _25751 _25752)). Qed.
Lemma lem1664912 (_25752 : real) (_25751 : real) : (term275 _25752 _25751) = (term275 _25752 _25751).
Proof. exact (eq_refl (term275 _25752 _25751)). Qed.
Lemma lem1664913 (_25752 : real) (_25751 : real) : (term285 _25752 _25751) = (term289 _25752 _25751).
Proof. exact (MK_COMB (@lem1664911 _25751 _25752) (@lem1664912 _25752 _25751)). Qed.
Lemma lem1664914 (_25752 : real) (_25751 : real) : (term282 _25751 _25752) = (term289 _25752 _25751).
Proof. exact (TRANS (@lem1664906 _25752 _25751) (@lem1664913 _25752 _25751)). Qed.
Lemma lem1664917 (_25752 : real) (_25751 : real) (h1 : term43) : term289 _25752 _25751.
Proof. exact (EQ_MP (@lem1664914 _25752 _25751) (@lem1664903 _25751 _25752 h1)). Qed.
Lemma lem1664918 (y : real) (x : real) (n : nat) (h1 : term43) : term290 y x n.
Proof. exact (@lem1664917 (real_pow y n) (real_pow x n) h1). Qed.
Lemma lem1664921 (n : nat) (x : real) (y : real) (h1 : term43) (h2 : term106 n x y) : term291 y x n.
Proof. exact (@lem1664918 y x n h1 (@lem1664876 n x y h2)). Qed.
Lemma lem1664922 (n : nat) (x : real) (y : real) (h1 : term43) (h2 : term106 n x y) : term292 y x n.
Proof. exact (fun h0 : term256 y x n => @lem1664921 n x y h1 h2). Qed.
Lemma lem1664924 (p : Prop) : (term293 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1664925 (y : real) (x : real) (n : nat) : (term292 y x n) = (term291 y x n).
Proof. exact (@lem1664924 (term256 y x n)). Qed.
Lemma lem1664926 (n : nat) (x : real) (y : real) (h1 : term43) (h2 : term106 n x y) : term291 y x n.
Proof. exact (EQ_MP (@lem1664925 y x n) (@lem1664922 n x y h1 h2)). Qed.
Lemma lem1664928 (b : Prop) (a : Prop) : (a \/ b) = (term284 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1664929 (_25748 : nat) (_25749 : real) (_25750 : real) : (term274 _25749 _25750 _25748) = (term294 _25748 _25749 _25750).
Proof. exact (@lem1664928 (term295 _25749 _25750 _25748) (term275 _25749 _25750)). Qed.
Lemma lem1664931 (a : Prop) (b : Prop) : (term296 a b) = (term297 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1664932 (_25749 : real) (_25750 : real) (_25748 : nat) : (term298 _25749 _25750 _25748) = (term299 _25749 _25750 _25748).
Proof. exact (@lem1664931 (term276 _25748) (term256 _25749 _25750 _25748)). Qed.
Lemma lem1664934 (a : Prop) : (term286 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1664935 (_25748 : nat) : (term300 _25748) = (Coq.Arith.PeanoNat.Nat.Odd _25748).
Proof. exact (@lem1664934 (Coq.Arith.PeanoNat.Nat.Odd _25748)). Qed.
Lemma lem1664936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1664937 (_25748 : nat) : (term301 _25748) = (term53 _25748).
Proof. exact (MK_COMB (@lem1664936) (@lem1664935 _25748)). Qed.
Lemma lem1664938 (_25749 : real) (_25750 : real) (_25748 : nat) : (term291 _25749 _25750 _25748) = (term291 _25749 _25750 _25748).
Proof. exact (eq_refl (term291 _25749 _25750 _25748)). Qed.
Lemma lem1664939 (_25749 : real) (_25750 : real) (_25748 : nat) : (term299 _25749 _25750 _25748) = (term302 _25749 _25750 _25748).
Proof. exact (MK_COMB (@lem1664937 _25748) (@lem1664938 _25749 _25750 _25748)). Qed.
Lemma lem1664940 (_25749 : real) (_25750 : real) (_25748 : nat) : (term298 _25749 _25750 _25748) = (term302 _25749 _25750 _25748).
Proof. exact (TRANS (@lem1664932 _25749 _25750 _25748) (@lem1664939 _25749 _25750 _25748)). Qed.
Lemma lem1664941 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1664942 (_25749 : real) (_25750 : real) (_25748 : nat) : (term303 _25749 _25750 _25748) = (term304 _25749 _25750 _25748).
Proof. exact (MK_COMB (@lem1664941) (@lem1664940 _25749 _25750 _25748)). Qed.
Lemma lem1664943 (_25749 : real) (_25750 : real) : (term275 _25749 _25750) = (term275 _25749 _25750).
Proof. exact (eq_refl (term275 _25749 _25750)). Qed.
Lemma lem1664944 (_25748 : nat) (_25749 : real) (_25750 : real) : (term294 _25748 _25749 _25750) = (term305 _25748 _25749 _25750).
Proof. exact (MK_COMB (@lem1664942 _25749 _25750 _25748) (@lem1664943 _25749 _25750)). Qed.
Lemma lem1664945 (_25748 : nat) (_25749 : real) (_25750 : real) : (term274 _25749 _25750 _25748) = (term305 _25748 _25749 _25750).
Proof. exact (TRANS (@lem1664929 _25748 _25749 _25750) (@lem1664944 _25748 _25749 _25750)). Qed.
Lemma lem1664947 (n : nat) (x : real) (y : real) (h1 : term43) (h2 : term55 n x y) (h3 : term106 n x y) : term302 y x n.
Proof. exact (conj (@lem1664869 n x y h2) (@lem1664926 n x y h1 h3)). Qed.
Lemma lem1664949 (_25748 : nat) (_25749 : real) (_25750 : real) (h1 : term17) : term305 _25748 _25749 _25750.
Proof. exact (EQ_MP (@lem1664945 _25748 _25749 _25750) (@lem1664802 _25749 _25750 _25748 h1)). Qed.
Lemma lem1664950 (n : nat) (y : real) (x : real) (h1 : term17) : term305 n y x.
Proof. exact (@lem1664949 n y x h1). Qed.
Lemma lem1664953 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term43) (h3 : term55 n x y) (h4 : term106 n x y) : term275 y x.
Proof. exact (@lem1664950 n y x h1 (@lem1664947 n x y h2 h3 h4)). Qed.
Lemma lem1664954 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term43) (h3 : term55 n x y) (h4 : term106 n x y) : term306 y x.
Proof. exact (fun h0 : real_lt y x => @lem1664953 n x y h1 h2 h3 h4). Qed.
Lemma lem1664956 (p : Prop) : (term293 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1664957 (y : real) (x : real) : (term306 y x) = (term275 y x).
Proof. exact (@lem1664956 (real_lt y x)). Qed.
Lemma lem1664958 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term43) (h3 : term55 n x y) (h4 : term106 n x y) : term275 y x.
Proof. exact (EQ_MP (@lem1664957 y x) (@lem1664954 n x y h1 h2 h3 h4)). Qed.
Lemma lem1664960 (b : Prop) (a : Prop) : (a \/ b) = (term284 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1664963 (_25753 : real) (_25754 : real) : (term186 _25754 _25753) = (term307 _25753 _25754).
Proof. exact (@lem1664960 (real_lt _25754 _25753) (real_le _25753 _25754)). Qed.
Lemma lem1664966 (_25753 : real) (_25754 : real) (h1 : term43) : term307 _25753 _25754.
Proof. exact (EQ_MP (@lem1664963 _25753 _25754) (@lem1664816 _25754 _25753 h1)). Qed.
Lemma lem1664967 (x : real) (y : real) (h1 : term43) : term307 x y.
Proof. exact (@lem1664966 x y h1). Qed.
Lemma lem1664970 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term43) (h3 : term55 n x y) (h4 : term106 n x y) : real_le x y.
Proof. exact (@lem1664967 x y h2 (@lem1664958 n x y h1 h2 h3 h4)). Qed.
Lemma lem1664971 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term43) (h3 : term55 n x y) (h4 : term106 n x y) : term308 x y.
Proof. exact (fun h0 : term39 x y => @lem1664970 n x y h1 h2 h3 h4). Qed.
Lemma lem1664973 (p : Prop) : (term280 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1664974 (x : real) (y : real) : (term308 x y) = (real_le x y).
Proof. exact (@lem1664973 (real_le x y)). Qed.
Lemma lem1664975 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term43) (h3 : term55 n x y) (h4 : term106 n x y) : real_le x y.
Proof. exact (EQ_MP (@lem1664974 x y) (@lem1664971 n x y h1 h2 h3 h4)). Qed.
Lemma lem1664978 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1664980 (x : real) (y : real) : (term39 x y) = (term309 x y).
Proof. exact (@lem1664978 (real_le x y)). Qed.
Lemma lem1664983 (n : nat) (x : real) (y : real) (h1 : term106 n x y) : term309 x y.
Proof. exact (EQ_MP (@lem1664980 x y) (@lem1664820 n x y h1)). Qed.
Lemma lem1664986 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term43) (h3 : term55 n x y) (h4 : term106 n x y) : False.
Proof. exact (@lem1664983 n x y h4 (@lem1664975 n x y h1 h2 h3 h4)). Qed.
Lemma lem1664987 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term43) (h3 : term55 n x y) (h4 : term106 n x y) : term310.
Proof. exact (fun h0 : ~ False => @lem1664986 n x y h1 h2 h3 h4). Qed.
Lemma lem1664989 (p : Prop) : (term280 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1664990 : term310 = False.
Proof. exact (@lem1664989 False). Qed.
Lemma lem1664991 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term43) (h3 : term55 n x y) (h4 : term106 n x y) : False.
Proof. exact (EQ_MP (@lem1664990) (@lem1664987 n x y h1 h2 h3 h4)). Qed.
Lemma lem1664993 (n : nat) (x : real) (y : real) (h1 : term110 n x y) : real_le x y.
Proof. exact (proj2 (@lem1664526 n x y h1)). Qed.
Lemma lem1664994 (n : nat) (x : real) (y : real) (h1 : term110 n x y) : term308 x y.
Proof. exact (fun h0 : term39 x y => @lem1664993 n x y h1). Qed.
Lemma lem1664996 (p : Prop) : (term280 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1664997 (x : real) (y : real) : (term308 x y) = (real_le x y).
Proof. exact (@lem1664996 (real_le x y)). Qed.
Lemma lem1664998 (n : nat) (x : real) (y : real) (h1 : term110 n x y) : real_le x y.
Proof. exact (EQ_MP (@lem1664997 x y) (@lem1664994 n x y h1)). Qed.
Lemma lem1665000 (n : nat) (x : real) (y : real) (h1 : term55 n x y) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (proj1 (@lem1664520 n x y h1)). Qed.
Lemma lem1665001 (n : nat) (x : real) (y : real) (h1 : term55 n x y) : term279 n.
Proof. exact (fun h0 : term276 n => @lem1665000 n x y h1). Qed.
Lemma lem1665003 (p : Prop) : (term280 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1665004 (n : nat) : (term279 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (@lem1665003 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem1665005 (n : nat) (x : real) (y : real) (h1 : term55 n x y) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (EQ_MP (@lem1665004 n) (@lem1665001 n x y h1)). Qed.
Lemma lem1665011 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1665012 (_25756 : real) (_25757 : real) (_25755 : nat) : (term277 _25756 _25757 _25755) = (term311 _25756 _25757 _25755).
Proof. exact (@lem1665011 (term276 _25755) (term39 _25756 _25757) (term52 _25756 _25757 _25755)). Qed.
Lemma lem1665026 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1665027 (_25755 : nat) (_25756 : real) (_25757 : real) : (term312 _25756 _25757 _25755) = (term313 _25755 _25756 _25757).
Proof. exact (@lem1665026 (term52 _25756 _25757 _25755) (term39 _25756 _25757)). Qed.
Lemma lem1665033 (_25755 : nat) : (term314 _25755) = (term314 _25755).
Proof. exact (eq_refl (term314 _25755)). Qed.
Lemma lem1665034 (_25755 : nat) (_25756 : real) (_25757 : real) : (term311 _25756 _25757 _25755) = (term315 _25755 _25756 _25757).
Proof. exact (MK_COMB (@lem1665033 _25755) (@lem1665027 _25755 _25756 _25757)). Qed.
Lemma lem1665038 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1665039 (_25755 : nat) (_25756 : real) (_25757 : real) : (term315 _25755 _25756 _25757) = (term316 _25755 _25756 _25757).
Proof. exact (@lem1665038 (term52 _25756 _25757 _25755) (term276 _25755) (term39 _25756 _25757)). Qed.
Lemma lem1665055 (_25755 : nat) (_25756 : real) (_25757 : real) : (term311 _25756 _25757 _25755) = (term316 _25755 _25756 _25757).
Proof. exact (TRANS (@lem1665034 _25755 _25756 _25757) (@lem1665039 _25755 _25756 _25757)). Qed.
Lemma lem1665056 (_25755 : nat) (_25756 : real) (_25757 : real) : (term277 _25756 _25757 _25755) = (term316 _25755 _25756 _25757).
Proof. exact (TRANS (@lem1665012 _25756 _25757 _25755) (@lem1665055 _25755 _25756 _25757)). Qed.
Lemma lem1665057 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1665058 (_25755 : nat) (_25756 : real) (_25757 : real) : (term317 _25756 _25757 _25755) = (term318 _25755 _25756 _25757).
Proof. exact (MK_COMB (@lem1665057) (@lem1665056 _25755 _25756 _25757)). Qed.
Lemma lem1665072 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1665073 (_25755 : nat) (_25756 : real) (_25757 : real) : (term242 _25756 _25757 _25755) = (term319 _25755 _25756 _25757).
Proof. exact (@lem1665072 (term276 _25755) (term39 _25756 _25757)). Qed.
Lemma lem1665079 (_25756 : real) (_25757 : real) (_25755 : nat) : (term320 _25756 _25757 _25755) = (term320 _25756 _25757 _25755).
Proof. exact (eq_refl (term320 _25756 _25757 _25755)). Qed.
Lemma lem1665080 (_25755 : nat) (_25756 : real) (_25757 : real) : (term321 _25756 _25757 _25755) = (term316 _25755 _25756 _25757).
Proof. exact (MK_COMB (@lem1665079 _25756 _25757 _25755) (@lem1665073 _25755 _25756 _25757)). Qed.
Lemma lem1665091 (_25755 : nat) (_25756 : real) (_25757 : real) : ((term277 _25756 _25757 _25755) = (term321 _25756 _25757 _25755)) = ((term316 _25755 _25756 _25757) = (term316 _25755 _25756 _25757)).
Proof. exact (MK_COMB (@lem1665058 _25755 _25756 _25757) (@lem1665080 _25755 _25756 _25757)). Qed.
Lemma lem1665093 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1665094 (x : Prop) : (x = x) = True.
Proof. exact (@lem1665093 Prop x). Qed.
Lemma lem1665095 (_25755 : nat) (_25756 : real) (_25757 : real) : ((term316 _25755 _25756 _25757) = (term316 _25755 _25756 _25757)) = True.
Proof. exact (@lem1665094 (term316 _25755 _25756 _25757)). Qed.
Lemma lem1665096 (_25756 : real) (_25757 : real) (_25755 : nat) : ((term277 _25756 _25757 _25755) = (term321 _25756 _25757 _25755)) = True.
Proof. exact (TRANS (@lem1665091 _25755 _25756 _25757) (@lem1665095 _25755 _25756 _25757)). Qed.
Lemma lem1665097 (_25756 : real) (_25757 : real) (_25755 : nat) : True = ((term277 _25756 _25757 _25755) = (term321 _25756 _25757 _25755)).
Proof. exact (SYM (@lem1665096 _25756 _25757 _25755)). Qed.
Lemma lem1665098 (_25756 : real) (_25757 : real) (_25755 : nat) : (term277 _25756 _25757 _25755) = (term321 _25756 _25757 _25755).
Proof. exact (EQ_MP (@lem1665097 _25756 _25757 _25755) (@lem0)). Qed.
Lemma lem1665099 (_25756 : real) (_25757 : real) (_25755 : nat) (h1 : term38) : term321 _25756 _25757 _25755.
Proof. exact (EQ_MP (@lem1665098 _25756 _25757 _25755) (@lem1664832 _25756 _25757 _25755 h1)). Qed.
Lemma lem1665101 (b : Prop) (a : Prop) : (a \/ b) = (term284 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1665102 (_25756 : real) (_25757 : real) (_25755 : nat) : (term321 _25756 _25757 _25755) = (term322 _25756 _25757 _25755).
Proof. exact (@lem1665101 (term242 _25756 _25757 _25755) (term52 _25756 _25757 _25755)). Qed.
Lemma lem1665104 (a : Prop) (b : Prop) : (term296 a b) = (term297 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1665105 (_25756 : real) (_25757 : real) (_25755 : nat) : (term323 _25756 _25757 _25755) = (term324 _25756 _25757 _25755).
Proof. exact (@lem1665104 (term39 _25756 _25757) (term276 _25755)). Qed.
Lemma lem1665107 (a : Prop) : (term286 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1665108 (_25756 : real) (_25757 : real) : (term182 _25756 _25757) = (real_le _25756 _25757).
Proof. exact (@lem1665107 (real_le _25756 _25757)). Qed.
Lemma lem1665109 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1665110 (_25756 : real) (_25757 : real) : (term325 _25756 _25757) = (term326 _25756 _25757).
Proof. exact (MK_COMB (@lem1665109) (@lem1665108 _25756 _25757)). Qed.
Lemma lem1665112 (a : Prop) : (term286 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1665113 (_25755 : nat) : (term300 _25755) = (Coq.Arith.PeanoNat.Nat.Odd _25755).
Proof. exact (@lem1665112 (Coq.Arith.PeanoNat.Nat.Odd _25755)). Qed.
Lemma lem1665114 (_25756 : real) (_25757 : real) (_25755 : nat) : (term324 _25756 _25757 _25755) = (term247 _25756 _25757 _25755).
Proof. exact (MK_COMB (@lem1665110 _25756 _25757) (@lem1665113 _25755)). Qed.
Lemma lem1665115 (_25756 : real) (_25757 : real) (_25755 : nat) : (term323 _25756 _25757 _25755) = (term247 _25756 _25757 _25755).
Proof. exact (TRANS (@lem1665105 _25756 _25757 _25755) (@lem1665114 _25756 _25757 _25755)). Qed.
Lemma lem1665116 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1665117 (_25756 : real) (_25757 : real) (_25755 : nat) : (term327 _25756 _25757 _25755) = (term328 _25756 _25757 _25755).
Proof. exact (MK_COMB (@lem1665116) (@lem1665115 _25756 _25757 _25755)). Qed.
Lemma lem1665118 (_25756 : real) (_25757 : real) (_25755 : nat) : (term52 _25756 _25757 _25755) = (term52 _25756 _25757 _25755).
Proof. exact (eq_refl (term52 _25756 _25757 _25755)). Qed.
Lemma lem1665119 (_25756 : real) (_25757 : real) (_25755 : nat) : (term322 _25756 _25757 _25755) = (term32 _25756 _25757 _25755).
Proof. exact (MK_COMB (@lem1665117 _25756 _25757 _25755) (@lem1665118 _25756 _25757 _25755)). Qed.
Lemma lem1665120 (_25756 : real) (_25757 : real) (_25755 : nat) : (term321 _25756 _25757 _25755) = (term32 _25756 _25757 _25755).
Proof. exact (TRANS (@lem1665102 _25756 _25757 _25755) (@lem1665119 _25756 _25757 _25755)). Qed.
Lemma lem1665122 (n : nat) (x : real) (y : real) (h1 : term55 n x y) (h2 : term110 n x y) : term247 x y n.
Proof. exact (conj (@lem1664998 n x y h2) (@lem1665005 n x y h1)). Qed.
Lemma lem1665124 (_25756 : real) (_25757 : real) (_25755 : nat) (h1 : term38) : term32 _25756 _25757 _25755.
Proof. exact (EQ_MP (@lem1665120 _25756 _25757 _25755) (@lem1665099 _25756 _25757 _25755 h1)). Qed.
Lemma lem1665125 (x : real) (y : real) (n : nat) (h1 : term38) : term32 x y n.
Proof. exact (@lem1665124 x y n h1). Qed.
Lemma lem1665128 (n : nat) (x : real) (y : real) (h1 : term38) (h2 : term55 n x y) (h3 : term110 n x y) : term52 x y n.
Proof. exact (@lem1665125 x y n h1 (@lem1665122 n x y h2 h3)). Qed.
Lemma lem1665129 (n : nat) (x : real) (y : real) (h1 : term38) (h2 : term55 n x y) (h3 : term110 n x y) : term281 x y n.
Proof. exact (fun h0 : term278 x y n => @lem1665128 n x y h1 h2 h3). Qed.
Lemma lem1665131 (p : Prop) : (term280 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1665132 (x : real) (y : real) (n : nat) : (term281 x y n) = (term52 x y n).
Proof. exact (@lem1665131 (term52 x y n)). Qed.
Lemma lem1665133 (n : nat) (x : real) (y : real) (h1 : term38) (h2 : term55 n x y) (h3 : term110 n x y) : term52 x y n.
Proof. exact (EQ_MP (@lem1665132 x y n) (@lem1665129 n x y h1 h2 h3)). Qed.
Lemma lem1665136 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1665138 (x : real) (y : real) (n : nat) : (term278 x y n) = (term329 x y n).
Proof. exact (@lem1665136 (term52 x y n)). Qed.
Lemma lem1665141 (n : nat) (x : real) (y : real) (h1 : term110 n x y) : term329 x y n.
Proof. exact (EQ_MP (@lem1665138 x y n) (@lem1664860 n x y h1)). Qed.
Lemma lem1665144 (n : nat) (x : real) (y : real) (h1 : term38) (h2 : term55 n x y) (h3 : term110 n x y) : False.
Proof. exact (@lem1665141 n x y h3 (@lem1665133 n x y h1 h2 h3)). Qed.
Lemma lem1665145 (n : nat) (x : real) (y : real) (h1 : term38) (h2 : term55 n x y) (h3 : term110 n x y) : term310.
Proof. exact (fun h0 : ~ False => @lem1665144 n x y h1 h2 h3). Qed.
Lemma lem1665147 (p : Prop) : (term280 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1665148 : term310 = False.
Proof. exact (@lem1665147 False). Qed.
Lemma lem1665149 (n : nat) (x : real) (y : real) (h1 : term38) (h2 : term55 n x y) (h3 : term110 n x y) : False.
Proof. exact (EQ_MP (@lem1665148) (@lem1665145 n x y h1 h2 h3)). Qed.
Lemma lem1665150 (n : nat) (x : real) (y : real) (h1 : term38) (h2 : term17) (h3 : term43) (h4 : term55 n x y) : False.
Proof. exact (or_elim (@lem1664521 n x y h4) (fun h0 : term106 n x y => @lem1664991 n x y h2 h3 h4 h0) (fun h0 : term110 n x y => @lem1665149 n x y h1 h4 h0)). Qed.
Lemma lem1665151 (n : nat) (x : real) (y : real) (h1 : term38) (h2 : term17) (h3 : term43) (h4 : term55 n x y) : (term55 n x y) = False.
Proof. exact (prop_ext (fun h5 : term55 n x y => @lem1665150 n x y h1 h2 h3 h4) (fun h5 : False => @lem1664520 n x y h4)). Qed.
Lemma lem1665152 (n : nat) (x : real) (y : real) (h1 : term38) (h2 : term17) (h3 : term43) (h4 : term55 n x y) : False.
Proof. exact (EQ_MP (@lem1665151 n x y h1 h2 h3 h4) (@lem1664520 n x y h4)). Qed.
Lemma lem1665153 (n : nat) (x : real) (h1 : term38) (h2 : term17) (h3 : term43) (h4 : term65 n x) : False.
Proof. exact (ex_elim (@lem1664335 n x h4) (fun y : real => fun h0 : term64 n x y => @lem1665152 n x y h1 h2 h3 h0)). Qed.
Lemma lem1665154 (n : nat) (h1 : term38) (h2 : term17) (h3 : term43) (h4 : term72 n) : False.
Proof. exact (ex_elim (@lem1664334 n h4) (fun x : real => fun h0 : term71 n x => @lem1665153 n x h1 h2 h3 h0)). Qed.
Lemma lem1665155 (h1 : term38) (h2 : term17) (h3 : term43) (h4 : term10) : False.
Proof. exact (ex_elim (@lem1663878 h4) (fun n : nat => fun h0 : term79 n => @lem1665154 n h1 h2 h3 h0)). Qed.
Lemma lem1665156 (h1 : term38) (h2 : term43) (h3 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1665155 h1 h0 h2 h3). Qed.
Lemma lem1665157 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1665158 (h1 : term38) (h2 : term43) (h3 : term10) : term16.
Proof. exact (EQ_MP (@lem1665157) (@lem1665156 h1 h2 h3)). Qed.
Lemma lem1665159 (h1 : term43) (h2 : term10) : term20.
Proof. exact (fun h0 : term38 => @lem1665158 h0 h1 h2). Qed.
Lemma lem1665160 (h1 : term10) : term23.
Proof. exact (fun h0 : term43 => @lem1665159 h0 h1). Qed.
Lemma lem1665161 : term25.
Proof. exact (fun h0 : term10 => @lem1665160 h0). Qed.
Lemma lem1665162 : term11.
Proof. exact (EQ_MP (@lem1663369) (@lem1665161)). Qed.
Lemma lem1665164 : term11.
Proof. exact (@lem1663124 (@lem1665162)). Qed.
Lemma lem1665165 (h1 : term10) : term22.
Proof. exact (@lem1665164 (@lem1663109 h1)). Qed.
Lemma lem1665166 (h1 : term10) : term19.
Proof. exact (@lem1665165 h1 (@lem1495933)). Qed.
Lemma lem1665167 (h1 : term10) : term15.
Proof. exact (@lem1665166 h1 (@lem1661016)). Qed.
Lemma lem1665168 (h1 : term10) : False.
Proof. exact (@lem1665167 h1 (@lem1660753)). Qed.
Lemma lem1665169 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1665168 h1) (fun h2 : False => @lem1663109 h1)). Qed.
Lemma lem1665170 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1665169 h1) (@lem1663109 h1)). Qed.
Lemma lem1665171 : term9.
Proof. exact (fun h0 : term10 => @lem1665170 h0). Qed.
Lemma lem1665172 : term8.
Proof. exact (EQ_MP (@lem1663108) (@lem1665171)). Qed.
