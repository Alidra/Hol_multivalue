Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUP_LT_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_LET_TRANS_spec.
Require Import SUP_FINITE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
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
Lemma lem5152082 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5152083 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5152084 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5152083 t1) (@lem5152082 t1)). Qed.
Lemma lem5152085 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5152084 t1 t2). Qed.
Lemma lem5152086 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5152087 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5152086 t1 t2) (@lem5152085 t1 t2)). Qed.
Lemma lem5152088 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5152087 t1 t2 t3). Qed.
Lemma lem5152089 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5152090 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5152089 t1 t2 t3) (@lem5152088 t1 t2 t3)). Qed.
Lemma lem5152091 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5152090 t1 t2 t3)). Qed.
Lemma lem5152093 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5152094 : term8 = term9.
Proof. exact (@lem5152093 term8). Qed.
Lemma lem5152095 : term9 = term8.
Proof. exact (SYM (@lem5152094)). Qed.
Lemma lem5152096 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5152099 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5152100 : term12.
Proof. exact (fun h0 : term11 => @lem5152099 h0). Qed.
Lemma lem5152101 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5152102 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5152103 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5152101 h2 (@lem5152102 h1)). Qed.
Lemma lem5152104 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem5152103 h1 h0). Qed.
Lemma lem5152105 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5152106 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5152104 h1 (@lem5152105 h2)). Qed.
Lemma lem5152107 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem5152106 h0 h1). Qed.
Lemma lem5152108 : term14.
Proof. exact (fun h0 : term12 => @lem5152107 h0). Qed.
Lemma lem5152111 : term12.
Proof. exact (@lem5152108 (@lem5152100)). Qed.
Lemma lem5152151 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5152152 : term15 = term16.
Proof. exact (@lem5152151 term17). Qed.
Lemma lem5152169 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem5152170 : term19 = term20.
Proof. exact (MK_COMB (@lem5152169) (@lem5152152)). Qed.
Lemma lem5152173 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem5152180 : term11 = term22.
Proof. exact (MK_COMB (@lem5152173) (@lem5152170)). Qed.
Lemma lem5152185 (x : real) (s : real -> Prop) : (term23 x s) = (term23 x s).
Proof. exact (eq_refl (term23 x s)). Qed.
Lemma lem5152186 (s : real -> Prop) : (term24 s) = (term24 s).
Proof. exact (fun_ext (fun x : real => @lem5152185 x s)). Qed.
Lemma lem5152187 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5152188 (s : real -> Prop) : (term25 s) = (term25 s).
Proof. exact (MK_COMB (@lem5152187) (@lem5152186 s)). Qed.
Lemma lem5152191 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5152192 (s : real -> Prop) : (term27 s) = (term27 s).
Proof. exact (MK_COMB (@lem5152191 s) (@lem5152188 s)). Qed.
Lemma lem5152201 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5152202 (s : real -> Prop) : (term29 s) = (term29 s).
Proof. exact (MK_COMB (@lem5152201 s) (@lem5152192 s)). Qed.
Lemma lem5152203 : term30 = term30.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5152202 s)). Qed.
Lemma lem5152204 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5152205 : term17 = term17.
Proof. exact (MK_COMB (@lem5152204) (@lem5152203)). Qed.
Lemma lem5152206 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5152207 : term16 = term16.
Proof. exact (MK_COMB (@lem5152206) (@lem5152205)). Qed.
Lemma lem5152216 (y : real) (x : real) (z : real) : (term31 y x z) = (term31 y x z).
Proof. exact (eq_refl (term31 y x z)). Qed.
Lemma lem5152217 (y : real) (x : real) : (term32 y x) = (term32 y x).
Proof. exact (fun_ext (fun z : real => @lem5152216 y x z)). Qed.
Lemma lem5152218 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5152219 (y : real) (x : real) : (term33 y x) = (term33 y x).
Proof. exact (MK_COMB (@lem5152218) (@lem5152217 y x)). Qed.
Lemma lem5152220 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem5152219 y x)). Qed.
Lemma lem5152221 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5152222 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem5152221) (@lem5152220 x)). Qed.
Lemma lem5152223 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem5152222 x)). Qed.
Lemma lem5152224 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5152225 : term37 = term37.
Proof. exact (MK_COMB (@lem5152224) (@lem5152223)). Qed.
Lemma lem5152226 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5152227 : term18 = term18.
Proof. exact (MK_COMB (@lem5152226) (@lem5152225)). Qed.
Lemma lem5152228 : term20 = term20.
Proof. exact (MK_COMB (@lem5152227) (@lem5152207)). Qed.
Lemma lem5152233 (s : real -> Prop) (x : real) (a : real) : (term38 s x a) = (term38 s x a).
Proof. exact (eq_refl (term38 s x a)). Qed.
Lemma lem5152234 (s : real -> Prop) (a : real) : (term39 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5152233 s x a)). Qed.
Lemma lem5152235 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5152236 (s : real -> Prop) (a : real) : (term40 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5152235) (@lem5152234 s a)). Qed.
Lemma lem5152239 (s : real -> Prop) (a : real) : (term41 s a) = (term41 s a).
Proof. exact (eq_refl (term41 s a)). Qed.
Lemma lem5152240 (s : real -> Prop) (a : real) : ((term42 s a) = (term40 s a)) = ((term42 s a) = (term40 s a)).
Proof. exact (MK_COMB (@lem5152239 s a) (@lem5152236 s a)). Qed.
Lemma lem5152249 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5152250 (s : real -> Prop) (a : real) : (term43 s a) = (term43 s a).
Proof. exact (MK_COMB (@lem5152249 s) (@lem5152240 s a)). Qed.
Lemma lem5152251 (s : real -> Prop) : (term44 s) = (term44 s).
Proof. exact (fun_ext (fun a : real => @lem5152250 s a)). Qed.
Lemma lem5152252 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5152253 (s : real -> Prop) : (term45 s) = (term45 s).
Proof. exact (MK_COMB (@lem5152252) (@lem5152251 s)). Qed.
Lemma lem5152254 : term46 = term46.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5152253 s)). Qed.
Lemma lem5152255 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5152256 : term8 = term8.
Proof. exact (MK_COMB (@lem5152255) (@lem5152254)). Qed.
Lemma lem5152257 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5152258 : term10 = term10.
Proof. exact (MK_COMB (@lem5152257) (@lem5152256)). Qed.
Lemma lem5152259 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5152260 : term21 = term21.
Proof. exact (MK_COMB (@lem5152259) (@lem5152258)). Qed.
Lemma lem5152261 : term22 = term22.
Proof. exact (MK_COMB (@lem5152260) (@lem5152228)). Qed.
Lemma lem5152334 : term11 = term22.
Proof. exact (TRANS (@lem5152180) (@lem5152261)). Qed.
Lemma lem5152335 : term22 = term11.
Proof. exact (SYM (@lem5152334)). Qed.
Lemma lem5152336 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5152337 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem5152338 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem5152354 (s : real -> Prop) (x : real) (a : real) : (term47 s x a) = (term48 s x a).
Proof. exact (@lem17362 (@IN real x s) (real_lt x a)). Qed.
Lemma lem5152359 (s : real -> Prop) (x : real) (a : real) : (term38 s x a) = (term49 s x a).
Proof. exact (@lem17265 (@IN real x s) (real_lt x a)). Qed.
Lemma lem5152360 (P : real -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5152361 (s : real -> Prop) (a : real) : (term52 s a) = (term53 s a).
Proof. exact (@lem5152360 (term39 s a)). Qed.
Lemma lem5152362 (s : real -> Prop) (x : real) (a : real) : (term54 s a x) = (term38 s x a).
Proof. exact (eq_refl (term54 s a x)). Qed.
Lemma lem5152363 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5152364 (s : real -> Prop) (x : real) (a : real) : (term55 s a x) = (term47 s x a).
Proof. exact (MK_COMB (@lem5152363) (@lem5152362 s x a)). Qed.
Lemma lem5152365 (s : real -> Prop) (x : real) (a : real) : (term55 s a x) = (term48 s x a).
Proof. exact (TRANS (@lem5152364 s x a) (@lem5152354 s x a)). Qed.
Lemma lem5152366 (s : real -> Prop) (a : real) : (term56 s a) = (term57 s a).
Proof. exact (fun_ext (fun x : real => @lem5152365 s x a)). Qed.
Lemma lem5152367 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152368 (s : real -> Prop) (a : real) : (term53 s a) = (term58 s a).
Proof. exact (MK_COMB (@lem5152367) (@lem5152366 s a)). Qed.
Lemma lem5152369 (s : real -> Prop) (a : real) : (term52 s a) = (term58 s a).
Proof. exact (TRANS (@lem5152361 s a) (@lem5152368 s a)). Qed.
Lemma lem5152370 (s : real -> Prop) (a : real) : (term39 s a) = (term59 s a).
Proof. exact (fun_ext (fun x : real => @lem5152359 s x a)). Qed.
Lemma lem5152371 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5152372 (s : real -> Prop) (a : real) : (term40 s a) = (term60 s a).
Proof. exact (MK_COMB (@lem5152371) (@lem5152370 s a)). Qed.
Lemma lem5152374 (s : real -> Prop) (a : real) : (term61 s a) = (term61 s a).
Proof. exact (eq_refl (term61 s a)). Qed.
Lemma lem5152375 (s : real -> Prop) (a : real) : (term62 s a) = (term63 s a).
Proof. exact (MK_COMB (@lem5152374 s a) (@lem5152372 s a)). Qed.
Lemma lem5152377 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (eq_refl (term64 s a)). Qed.
Lemma lem5152378 (s : real -> Prop) (a : real) : (term65 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5152377 s a) (@lem5152369 s a)). Qed.
Lemma lem5152379 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5152380 (s : real -> Prop) (a : real) : (term67 s a) = (term68 s a).
Proof. exact (MK_COMB (@lem5152379) (@lem5152378 s a)). Qed.
Lemma lem5152381 (s : real -> Prop) (a : real) : (term69 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5152380 s a) (@lem5152375 s a)). Qed.
Lemma lem5152382 (s : real -> Prop) (a : real) : (term71 s a) = (term69 s a).
Proof. exact (@lem17646 (term42 s a) (term40 s a)). Qed.
Lemma lem5152383 (s : real -> Prop) (a : real) : (term71 s a) = (term70 s a).
Proof. exact (TRANS (@lem5152382 s a) (@lem5152381 s a)). Qed.
Lemma lem5152385 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5152386 (s : real -> Prop) (a : real) : (term73 s a) = (term74 s a).
Proof. exact (MK_COMB (@lem5152385 s) (@lem5152383 s a)). Qed.
Lemma lem5152387 (s : real -> Prop) (a : real) : (term75 s a) = (term73 s a).
Proof. exact (@lem17362 (term76 s) ((term42 s a) = (term40 s a))). Qed.
Lemma lem5152388 (s : real -> Prop) (a : real) : (term75 s a) = (term74 s a).
Proof. exact (TRANS (@lem5152387 s a) (@lem5152386 s a)). Qed.
Lemma lem5152389 (P : real -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5152390 (s : real -> Prop) : (term77 s) = (term78 s).
Proof. exact (@lem5152389 (term44 s)). Qed.
Lemma lem5152391 (s : real -> Prop) (a : real) : (term79 s a) = (term43 s a).
Proof. exact (eq_refl (term79 s a)). Qed.
Lemma lem5152392 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5152393 (s : real -> Prop) (a : real) : (term80 s a) = (term75 s a).
Proof. exact (MK_COMB (@lem5152392) (@lem5152391 s a)). Qed.
Lemma lem5152394 (s : real -> Prop) (a : real) : (term80 s a) = (term74 s a).
Proof. exact (TRANS (@lem5152393 s a) (@lem5152388 s a)). Qed.
Lemma lem5152395 (s : real -> Prop) : (term81 s) = (term82 s).
Proof. exact (fun_ext (fun a : real => @lem5152394 s a)). Qed.
Lemma lem5152396 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152397 (s : real -> Prop) : (term78 s) = (term83 s).
Proof. exact (MK_COMB (@lem5152396) (@lem5152395 s)). Qed.
Lemma lem5152398 (s : real -> Prop) : (term77 s) = (term83 s).
Proof. exact (TRANS (@lem5152390 s) (@lem5152397 s)). Qed.
Lemma lem5152399 (P : type1022) : (term84 P) = (term85 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5152400 : term10 = term86.
Proof. exact (@lem5152399 term46). Qed.
Lemma lem5152401 (s : real -> Prop) : (term87 s) = (term45 s).
Proof. exact (eq_refl (term87 s)). Qed.
Lemma lem5152402 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5152403 (s : real -> Prop) : (term88 s) = (term77 s).
Proof. exact (MK_COMB (@lem5152402) (@lem5152401 s)). Qed.
Lemma lem5152404 (s : real -> Prop) : (term88 s) = (term83 s).
Proof. exact (TRANS (@lem5152403 s) (@lem5152398 s)). Qed.
Lemma lem5152405 : term89 = term90.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5152404 s)). Qed.
Lemma lem5152406 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5152407 : term86 = term91.
Proof. exact (MK_COMB (@lem5152406) (@lem5152405)). Qed.
Lemma lem5152408 : term10 = term91.
Proof. exact (TRANS (@lem5152400) (@lem5152407)). Qed.
Lemma lem5152414 {A : Type'} (P : Prop) (Q : A -> Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem5152415 (P : Prop) (Q : real -> Prop) : (term94 P Q) = (term95 P Q).
Proof. exact (@lem5152414 real P Q). Qed.
Lemma lem5152416 (s : real -> Prop) : (term96 s) = (term97 s).
Proof. exact (@lem5152415 (term76 s) (term98 s)). Qed.
Lemma lem5152417 (s : real -> Prop) (a : real) : (term99 s a) = (term70 s a).
Proof. exact (eq_refl (term99 s a)). Qed.
Lemma lem5152418 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5152419 (s : real -> Prop) (a : real) : (term100 s a) = (term74 s a).
Proof. exact (MK_COMB (@lem5152418 s) (@lem5152417 s a)). Qed.
Lemma lem5152420 (s : real -> Prop) : (term101 s) = (term82 s).
Proof. exact (fun_ext (fun a : real => @lem5152419 s a)). Qed.
Lemma lem5152421 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152422 (s : real -> Prop) : (term96 s) = (term83 s).
Proof. exact (MK_COMB (@lem5152421) (@lem5152420 s)). Qed.
Lemma lem5152423 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5152424 (s : real -> Prop) : (term102 s) = (term103 s).
Proof. exact (MK_COMB (@lem5152423) (@lem5152422 s)). Qed.
Lemma lem5152425 (s : real -> Prop) (a : real) : (term99 s a) = (term70 s a).
Proof. exact (eq_refl (term99 s a)). Qed.
Lemma lem5152426 (s : real -> Prop) : (term104 s) = (term98 s).
Proof. exact (fun_ext (fun a : real => @lem5152425 s a)). Qed.
Lemma lem5152427 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152428 (s : real -> Prop) : (term105 s) = (term106 s).
Proof. exact (MK_COMB (@lem5152427) (@lem5152426 s)). Qed.
Lemma lem5152429 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5152430 (s : real -> Prop) : (term97 s) = (term107 s).
Proof. exact (MK_COMB (@lem5152429 s) (@lem5152428 s)). Qed.
Lemma lem5152431 (s : real -> Prop) : ((term96 s) = (term97 s)) = ((term83 s) = (term107 s)).
Proof. exact (MK_COMB (@lem5152424 s) (@lem5152430 s)). Qed.
Lemma lem5152432 (s : real -> Prop) : (term83 s) = (term107 s).
Proof. exact (EQ_MP (@lem5152431 s) (@lem5152416 s)). Qed.
Lemma lem5152434 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5152435 (P : real -> Prop) (Q : real -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem5152434 real P Q). Qed.
Lemma lem5152436 (s : real -> Prop) : (term112 s) = (term113 s).
Proof. exact (@lem5152435 (term114 s) (term115 s)). Qed.
Lemma lem5152437 (s : real -> Prop) (a : real) : (term116 s a) = (term66 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5152438 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5152439 (s : real -> Prop) (a : real) : (term117 s a) = (term68 s a).
Proof. exact (MK_COMB (@lem5152438) (@lem5152437 s a)). Qed.
Lemma lem5152440 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5152441 (s : real -> Prop) (a : real) : (term119 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5152439 s a) (@lem5152440 s a)). Qed.
Lemma lem5152442 (s : real -> Prop) : (term120 s) = (term98 s).
Proof. exact (fun_ext (fun a : real => @lem5152441 s a)). Qed.
Lemma lem5152443 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152444 (s : real -> Prop) : (term112 s) = (term106 s).
Proof. exact (MK_COMB (@lem5152443) (@lem5152442 s)). Qed.
Lemma lem5152445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5152446 (s : real -> Prop) : (term121 s) = (term122 s).
Proof. exact (MK_COMB (@lem5152445) (@lem5152444 s)). Qed.
Lemma lem5152447 (s : real -> Prop) (a : real) : (term116 s a) = (term66 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5152448 (s : real -> Prop) : (term123 s) = (term114 s).
Proof. exact (fun_ext (fun a : real => @lem5152447 s a)). Qed.
Lemma lem5152449 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152450 (s : real -> Prop) : (term124 s) = (term125 s).
Proof. exact (MK_COMB (@lem5152449) (@lem5152448 s)). Qed.
Lemma lem5152451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5152452 (s : real -> Prop) : (term126 s) = (term127 s).
Proof. exact (MK_COMB (@lem5152451) (@lem5152450 s)). Qed.
Lemma lem5152453 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5152454 (s : real -> Prop) : (term128 s) = (term115 s).
Proof. exact (fun_ext (fun a : real => @lem5152453 s a)). Qed.
Lemma lem5152455 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152456 (s : real -> Prop) : (term129 s) = (term130 s).
Proof. exact (MK_COMB (@lem5152455) (@lem5152454 s)). Qed.
Lemma lem5152457 (s : real -> Prop) : (term113 s) = (term131 s).
Proof. exact (MK_COMB (@lem5152452 s) (@lem5152456 s)). Qed.
Lemma lem5152458 (s : real -> Prop) : ((term112 s) = (term113 s)) = ((term106 s) = (term131 s)).
Proof. exact (MK_COMB (@lem5152446 s) (@lem5152457 s)). Qed.
Lemma lem5152459 (s : real -> Prop) : (term106 s) = (term131 s).
Proof. exact (EQ_MP (@lem5152458 s) (@lem5152436 s)). Qed.
Lemma lem5152652 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5152653 (s : real -> Prop) : (term107 s) = (term132 s).
Proof. exact (MK_COMB (@lem5152652 s) (@lem5152459 s)). Qed.
Lemma lem5152654 (s : real -> Prop) : (term83 s) = (term132 s).
Proof. exact (TRANS (@lem5152432 s) (@lem5152653 s)). Qed.
Lemma lem5152655 : term90 = term133.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5152654 s)). Qed.
Lemma lem5152656 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5152657 : term91 = term134.
Proof. exact (MK_COMB (@lem5152656) (@lem5152655)). Qed.
Lemma lem5152707 {A : Type'} (P : Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5152708 (P : Prop) (Q : real -> Prop) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem5152707 real P Q). Qed.
Lemma lem5152709 (s : real -> Prop) (a : real) : (term135 s a) = (term136 s a).
Proof. exact (@lem5152708 (term42 s a) (term57 s a)). Qed.
Lemma lem5152710 (s : real -> Prop) (x : real) (a : real) : (term137 s a x) = (term48 s x a).
Proof. exact (eq_refl (term137 s a x)). Qed.
Lemma lem5152711 (s : real -> Prop) (a : real) : (term138 s a) = (term57 s a).
Proof. exact (fun_ext (fun x : real => @lem5152710 s x a)). Qed.
Lemma lem5152712 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152713 (s : real -> Prop) (a : real) : (term139 s a) = (term58 s a).
Proof. exact (MK_COMB (@lem5152712) (@lem5152711 s a)). Qed.
Lemma lem5152714 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (eq_refl (term64 s a)). Qed.
Lemma lem5152715 (s : real -> Prop) (a : real) : (term135 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5152714 s a) (@lem5152713 s a)). Qed.
Lemma lem5152716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5152717 (s : real -> Prop) (a : real) : (term140 s a) = (term141 s a).
Proof. exact (MK_COMB (@lem5152716) (@lem5152715 s a)). Qed.
Lemma lem5152718 (s : real -> Prop) (x : real) (a : real) : (term137 s a x) = (term48 s x a).
Proof. exact (eq_refl (term137 s a x)). Qed.
Lemma lem5152719 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (eq_refl (term64 s a)). Qed.
Lemma lem5152720 (s : real -> Prop) (x : real) (a : real) : (term142 s a x) = (term143 s x a).
Proof. exact (MK_COMB (@lem5152719 s a) (@lem5152718 s x a)). Qed.
Lemma lem5152721 (s : real -> Prop) (a : real) : (term144 s a) = (term145 s a).
Proof. exact (fun_ext (fun x : real => @lem5152720 s x a)). Qed.
Lemma lem5152722 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152723 (s : real -> Prop) (a : real) : (term136 s a) = (term146 s a).
Proof. exact (MK_COMB (@lem5152722) (@lem5152721 s a)). Qed.
Lemma lem5152724 (s : real -> Prop) (a : real) : ((term135 s a) = (term136 s a)) = ((term66 s a) = (term146 s a)).
Proof. exact (MK_COMB (@lem5152717 s a) (@lem5152723 s a)). Qed.
Lemma lem5152725 (s : real -> Prop) (a : real) : (term66 s a) = (term146 s a).
Proof. exact (EQ_MP (@lem5152724 s a) (@lem5152709 s a)). Qed.
Lemma lem5152726 (s : real -> Prop) : (term114 s) = (term147 s).
Proof. exact (fun_ext (fun a : real => @lem5152725 s a)). Qed.
Lemma lem5152727 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152728 (s : real -> Prop) : (term125 s) = (term148 s).
Proof. exact (MK_COMB (@lem5152727) (@lem5152726 s)). Qed.
Lemma lem5152729 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5152730 (s : real -> Prop) : (term127 s) = (term149 s).
Proof. exact (MK_COMB (@lem5152729) (@lem5152728 s)). Qed.
Lemma lem5152731 (s : real -> Prop) : (term130 s) = (term130 s).
Proof. exact (eq_refl (term130 s)). Qed.
Lemma lem5152732 (s : real -> Prop) : (term131 s) = (term150 s).
Proof. exact (MK_COMB (@lem5152730 s) (@lem5152731 s)). Qed.
Lemma lem5152734 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5152735 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem5152734 real P Q). Qed.
Lemma lem5152736 (s : real -> Prop) : (term151 s) = (term152 s).
Proof. exact (@lem5152735 (term147 s) (term115 s)). Qed.
Lemma lem5152737 (s : real -> Prop) (a : real) : (term153 s a) = (term146 s a).
Proof. exact (eq_refl (term153 s a)). Qed.
Lemma lem5152738 (s : real -> Prop) : (term154 s) = (term147 s).
Proof. exact (fun_ext (fun a : real => @lem5152737 s a)). Qed.
Lemma lem5152739 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152740 (s : real -> Prop) : (term155 s) = (term148 s).
Proof. exact (MK_COMB (@lem5152739) (@lem5152738 s)). Qed.
Lemma lem5152741 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5152742 (s : real -> Prop) : (term156 s) = (term149 s).
Proof. exact (MK_COMB (@lem5152741) (@lem5152740 s)). Qed.
Lemma lem5152743 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5152744 (s : real -> Prop) : (term128 s) = (term115 s).
Proof. exact (fun_ext (fun a : real => @lem5152743 s a)). Qed.
Lemma lem5152745 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152746 (s : real -> Prop) : (term129 s) = (term130 s).
Proof. exact (MK_COMB (@lem5152745) (@lem5152744 s)). Qed.
Lemma lem5152747 (s : real -> Prop) : (term151 s) = (term150 s).
Proof. exact (MK_COMB (@lem5152742 s) (@lem5152746 s)). Qed.
Lemma lem5152748 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5152749 (s : real -> Prop) : (term157 s) = (term158 s).
Proof. exact (MK_COMB (@lem5152748) (@lem5152747 s)). Qed.
Lemma lem5152750 (s : real -> Prop) (a : real) : (term153 s a) = (term146 s a).
Proof. exact (eq_refl (term153 s a)). Qed.
Lemma lem5152751 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5152752 (s : real -> Prop) (a : real) : (term159 s a) = (term160 s a).
Proof. exact (MK_COMB (@lem5152751) (@lem5152750 s a)). Qed.
Lemma lem5152753 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5152754 (s : real -> Prop) (a : real) : (term161 s a) = (term162 s a).
Proof. exact (MK_COMB (@lem5152752 s a) (@lem5152753 s a)). Qed.
Lemma lem5152755 (s : real -> Prop) : (term163 s) = (term164 s).
Proof. exact (fun_ext (fun a : real => @lem5152754 s a)). Qed.
Lemma lem5152756 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152757 (s : real -> Prop) : (term152 s) = (term165 s).
Proof. exact (MK_COMB (@lem5152756) (@lem5152755 s)). Qed.
Lemma lem5152758 (s : real -> Prop) : ((term151 s) = (term152 s)) = ((term150 s) = (term165 s)).
Proof. exact (MK_COMB (@lem5152749 s) (@lem5152757 s)). Qed.
Lemma lem5152759 (s : real -> Prop) : (term150 s) = (term165 s).
Proof. exact (EQ_MP (@lem5152758 s) (@lem5152736 s)). Qed.
Lemma lem5152761 {A : Type'} (P : A -> Prop) (Q : Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5152762 (P : real -> Prop) (Q : Prop) : (term168 P Q) = (term169 P Q).
Proof. exact (@lem5152761 real P Q). Qed.
Lemma lem5152763 (s : real -> Prop) (a : real) : (term170 s a) = (term171 s a).
Proof. exact (@lem5152762 (term145 s a) (term63 s a)). Qed.
Lemma lem5152764 (s : real -> Prop) (x : real) (a : real) : (term172 s a x) = (term143 s x a).
Proof. exact (eq_refl (term172 s a x)). Qed.
Lemma lem5152765 (s : real -> Prop) (a : real) : (term173 s a) = (term145 s a).
Proof. exact (fun_ext (fun x : real => @lem5152764 s x a)). Qed.
Lemma lem5152766 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152767 (s : real -> Prop) (a : real) : (term174 s a) = (term146 s a).
Proof. exact (MK_COMB (@lem5152766) (@lem5152765 s a)). Qed.
Lemma lem5152768 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5152769 (s : real -> Prop) (a : real) : (term175 s a) = (term160 s a).
Proof. exact (MK_COMB (@lem5152768) (@lem5152767 s a)). Qed.
Lemma lem5152770 (s : real -> Prop) (a : real) : (term63 s a) = (term63 s a).
Proof. exact (eq_refl (term63 s a)). Qed.
Lemma lem5152771 (s : real -> Prop) (a : real) : (term170 s a) = (term162 s a).
Proof. exact (MK_COMB (@lem5152769 s a) (@lem5152770 s a)). Qed.
Lemma lem5152772 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5152773 (s : real -> Prop) (a : real) : (term176 s a) = (term177 s a).
Proof. exact (MK_COMB (@lem5152772) (@lem5152771 s a)). Qed.
Lemma lem5152774 (s : real -> Prop) (x : real) (a : real) : (term172 s a x) = (term143 s x a).
Proof. exact (eq_refl (term172 s a x)). Qed.
Lemma lem5152775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5152776 (s : real -> Prop) (x : real) (a : real) : (term178 s a x) = (term179 s x a).
Proof. exact (MK_COMB (@lem5152775) (@lem5152774 s x a)). Qed.
Lemma lem5152777 (s : real -> Prop) (a : real) : (term63 s a) = (term63 s a).
Proof. exact (eq_refl (term63 s a)). Qed.
Lemma lem5152778 (x : real) (s : real -> Prop) (a : real) : (term180 x s a) = (term181 x s a).
Proof. exact (MK_COMB (@lem5152776 s x a) (@lem5152777 s a)). Qed.
Lemma lem5152779 (s : real -> Prop) (a : real) : (term182 s a) = (term183 s a).
Proof. exact (fun_ext (fun x : real => @lem5152778 x s a)). Qed.
Lemma lem5152780 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152781 (s : real -> Prop) (a : real) : (term171 s a) = (term184 s a).
Proof. exact (MK_COMB (@lem5152780) (@lem5152779 s a)). Qed.
Lemma lem5152782 (s : real -> Prop) (a : real) : ((term170 s a) = (term171 s a)) = ((term162 s a) = (term184 s a)).
Proof. exact (MK_COMB (@lem5152773 s a) (@lem5152781 s a)). Qed.
Lemma lem5152783 (s : real -> Prop) (a : real) : (term162 s a) = (term184 s a).
Proof. exact (EQ_MP (@lem5152782 s a) (@lem5152763 s a)). Qed.
Lemma lem5152784 (s : real -> Prop) : (term164 s) = (term185 s).
Proof. exact (fun_ext (fun a : real => @lem5152783 s a)). Qed.
Lemma lem5152785 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152786 (s : real -> Prop) : (term165 s) = (term186 s).
Proof. exact (MK_COMB (@lem5152785) (@lem5152784 s)). Qed.
Lemma lem5152787 (s : real -> Prop) : (term150 s) = (term186 s).
Proof. exact (TRANS (@lem5152759 s) (@lem5152786 s)). Qed.
Lemma lem5152788 (s : real -> Prop) : (term131 s) = (term186 s).
Proof. exact (TRANS (@lem5152732 s) (@lem5152787 s)). Qed.
Lemma lem5152789 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5152790 (s : real -> Prop) : (term132 s) = (term187 s).
Proof. exact (MK_COMB (@lem5152789 s) (@lem5152788 s)). Qed.
Lemma lem5152792 {A : Type'} (P : Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5152793 (P : Prop) (Q : real -> Prop) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem5152792 real P Q). Qed.
Lemma lem5152794 (s : real -> Prop) : (term188 s) = (term189 s).
Proof. exact (@lem5152793 (term76 s) (term185 s)). Qed.
Lemma lem5152795 (s : real -> Prop) (a : real) : (term190 s a) = (term184 s a).
Proof. exact (eq_refl (term190 s a)). Qed.
Lemma lem5152796 (s : real -> Prop) : (term191 s) = (term185 s).
Proof. exact (fun_ext (fun a : real => @lem5152795 s a)). Qed.
Lemma lem5152797 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152798 (s : real -> Prop) : (term192 s) = (term186 s).
Proof. exact (MK_COMB (@lem5152797) (@lem5152796 s)). Qed.
Lemma lem5152799 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5152800 (s : real -> Prop) : (term188 s) = (term187 s).
Proof. exact (MK_COMB (@lem5152799 s) (@lem5152798 s)). Qed.
Lemma lem5152801 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5152802 (s : real -> Prop) : (term193 s) = (term194 s).
Proof. exact (MK_COMB (@lem5152801) (@lem5152800 s)). Qed.
Lemma lem5152803 (s : real -> Prop) (a : real) : (term190 s a) = (term184 s a).
Proof. exact (eq_refl (term190 s a)). Qed.
Lemma lem5152804 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5152805 (s : real -> Prop) (a : real) : (term195 s a) = (term196 s a).
Proof. exact (MK_COMB (@lem5152804 s) (@lem5152803 s a)). Qed.
Lemma lem5152806 (s : real -> Prop) : (term197 s) = (term198 s).
Proof. exact (fun_ext (fun a : real => @lem5152805 s a)). Qed.
Lemma lem5152807 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152808 (s : real -> Prop) : (term189 s) = (term199 s).
Proof. exact (MK_COMB (@lem5152807) (@lem5152806 s)). Qed.
Lemma lem5152809 (s : real -> Prop) : ((term188 s) = (term189 s)) = ((term187 s) = (term199 s)).
Proof. exact (MK_COMB (@lem5152802 s) (@lem5152808 s)). Qed.
Lemma lem5152810 (s : real -> Prop) : (term187 s) = (term199 s).
Proof. exact (EQ_MP (@lem5152809 s) (@lem5152794 s)). Qed.
Lemma lem5152812 {A : Type'} (P : Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5152813 (P : Prop) (Q : real -> Prop) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem5152812 real P Q). Qed.
Lemma lem5152814 (s : real -> Prop) (a : real) : (term200 s a) = (term201 s a).
Proof. exact (@lem5152813 (term76 s) (term183 s a)). Qed.
Lemma lem5152815 (x : real) (s : real -> Prop) (a : real) : (term202 s a x) = (term181 x s a).
Proof. exact (eq_refl (term202 s a x)). Qed.
Lemma lem5152816 (s : real -> Prop) (a : real) : (term203 s a) = (term183 s a).
Proof. exact (fun_ext (fun x : real => @lem5152815 x s a)). Qed.
Lemma lem5152817 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152818 (s : real -> Prop) (a : real) : (term204 s a) = (term184 s a).
Proof. exact (MK_COMB (@lem5152817) (@lem5152816 s a)). Qed.
Lemma lem5152819 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5152820 (s : real -> Prop) (a : real) : (term200 s a) = (term196 s a).
Proof. exact (MK_COMB (@lem5152819 s) (@lem5152818 s a)). Qed.
Lemma lem5152821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5152822 (s : real -> Prop) (a : real) : (term205 s a) = (term206 s a).
Proof. exact (MK_COMB (@lem5152821) (@lem5152820 s a)). Qed.
Lemma lem5152823 (x : real) (s : real -> Prop) (a : real) : (term202 s a x) = (term181 x s a).
Proof. exact (eq_refl (term202 s a x)). Qed.
Lemma lem5152824 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5152825 (x : real) (s : real -> Prop) (a : real) : (term207 s a x) = (term208 x s a).
Proof. exact (MK_COMB (@lem5152824 s) (@lem5152823 x s a)). Qed.
Lemma lem5152826 (s : real -> Prop) (a : real) : (term209 s a) = (term210 s a).
Proof. exact (fun_ext (fun x : real => @lem5152825 x s a)). Qed.
Lemma lem5152827 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152828 (s : real -> Prop) (a : real) : (term201 s a) = (term211 s a).
Proof. exact (MK_COMB (@lem5152827) (@lem5152826 s a)). Qed.
Lemma lem5152829 (s : real -> Prop) (a : real) : ((term200 s a) = (term201 s a)) = ((term196 s a) = (term211 s a)).
Proof. exact (MK_COMB (@lem5152822 s a) (@lem5152828 s a)). Qed.
Lemma lem5152830 (s : real -> Prop) (a : real) : (term196 s a) = (term211 s a).
Proof. exact (EQ_MP (@lem5152829 s a) (@lem5152814 s a)). Qed.
Lemma lem5152831 (s : real -> Prop) : (term198 s) = (term212 s).
Proof. exact (fun_ext (fun a : real => @lem5152830 s a)). Qed.
Lemma lem5152832 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5152833 (s : real -> Prop) : (term199 s) = (term213 s).
Proof. exact (MK_COMB (@lem5152832) (@lem5152831 s)). Qed.
Lemma lem5152834 (s : real -> Prop) : (term187 s) = (term213 s).
Proof. exact (TRANS (@lem5152810 s) (@lem5152833 s)). Qed.
Lemma lem5152835 (s : real -> Prop) : (term132 s) = (term213 s).
Proof. exact (TRANS (@lem5152790 s) (@lem5152834 s)). Qed.
Lemma lem5152836 : term133 = term214.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5152835 s)). Qed.
Lemma lem5152837 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5152838 : term134 = term215.
Proof. exact (MK_COMB (@lem5152837) (@lem5152836)). Qed.
Lemma lem5152839 : term91 = term215.
Proof. exact (TRANS (@lem5152657) (@lem5152838)). Qed.
Lemma lem5152840 : term10 = term215.
Proof. exact (TRANS (@lem5152408) (@lem5152839)). Qed.
Lemma lem5152841 (h1 : term10) : term215.
Proof. exact (EQ_MP (@lem5152840) (@lem5152336 h1)). Qed.
Lemma lem5152848 (x : real) (y : real) (z : real) : (term216 x y z) = (term217 x y z).
Proof. exact (@lem17045 (real_le x y) (real_lt y z)). Qed.
Lemma lem5152849 (x : real) (z : real) : (real_lt x z) = (real_lt x z).
Proof. exact (eq_refl (real_lt x z)). Qed.
Lemma lem5152850 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5152851 (x : real) (y : real) (z : real) : (term218 x y z) = (term219 x y z).
Proof. exact (MK_COMB (@lem5152850) (@lem5152848 x y z)). Qed.
Lemma lem5152852 (y : real) (x : real) (z : real) : (term220 y x z) = (term221 y x z).
Proof. exact (MK_COMB (@lem5152851 x y z) (@lem5152849 x z)). Qed.
Lemma lem5152853 (y : real) (x : real) (z : real) : (term31 y x z) = (term220 y x z).
Proof. exact (@lem17265 (term222 x y z) (real_lt x z)). Qed.
Lemma lem5152854 (y : real) (x : real) (z : real) : (term31 y x z) = (term221 y x z).
Proof. exact (TRANS (@lem5152853 y x z) (@lem5152852 y x z)). Qed.
Lemma lem5152855 (y : real) (x : real) : (term32 y x) = (term223 y x).
Proof. exact (fun_ext (fun z : real => @lem5152854 y x z)). Qed.
Lemma lem5152856 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5152857 (y : real) (x : real) : (term33 y x) = (term224 y x).
Proof. exact (MK_COMB (@lem5152856) (@lem5152855 y x)). Qed.
Lemma lem5152858 (x : real) : (term34 x) = (term225 x).
Proof. exact (fun_ext (fun y : real => @lem5152857 y x)). Qed.
Lemma lem5152859 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5152860 (x : real) : (term35 x) = (term226 x).
Proof. exact (MK_COMB (@lem5152859) (@lem5152858 x)). Qed.
Lemma lem5152861 : term36 = term227.
Proof. exact (fun_ext (fun x : real => @lem5152860 x)). Qed.
Lemma lem5152862 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5152923 : term37 = term228.
Proof. exact (MK_COMB (@lem5152862) (@lem5152861)). Qed.
Lemma lem5152924 (h1 : term37) : term228.
Proof. exact (EQ_MP (@lem5152923) (@lem5152337 h1)). Qed.
Lemma lem5152928 (s : real -> Prop) : (term229 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5152930 (s : real -> Prop) : (term230 s) = (term230 s).
Proof. exact (eq_refl (term230 s)). Qed.
Lemma lem5152931 (s : real -> Prop) : (term231 s) = (term232 s).
Proof. exact (MK_COMB (@lem5152930 s) (@lem5152928 s)). Qed.
Lemma lem5152932 (s : real -> Prop) : (term233 s) = (term231 s).
Proof. exact (@lem17045 (@FINITE real s) (term234 s)). Qed.
Lemma lem5152933 (s : real -> Prop) : (term233 s) = (term232 s).
Proof. exact (TRANS (@lem5152932 s) (@lem5152931 s)). Qed.
Lemma lem5152941 (x : real) (s : real -> Prop) : (term23 x s) = (term235 x s).
Proof. exact (@lem17265 (@IN real x s) (term236 x s)). Qed.
Lemma lem5152942 (s : real -> Prop) : (term24 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5152941 x s)). Qed.
Lemma lem5152943 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5152944 (s : real -> Prop) : (term25 s) = (term238 s).
Proof. exact (MK_COMB (@lem5152943) (@lem5152942 s)). Qed.
Lemma lem5152946 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5152947 (s : real -> Prop) : (term27 s) = (term239 s).
Proof. exact (MK_COMB (@lem5152946 s) (@lem5152944 s)). Qed.
Lemma lem5152948 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5152949 (s : real -> Prop) : (term240 s) = (term241 s).
Proof. exact (MK_COMB (@lem5152948) (@lem5152933 s)). Qed.
Lemma lem5152950 (s : real -> Prop) : (term242 s) = (term243 s).
Proof. exact (MK_COMB (@lem5152949 s) (@lem5152947 s)). Qed.
Lemma lem5152951 (s : real -> Prop) : (term29 s) = (term242 s).
Proof. exact (@lem17265 (term76 s) (term27 s)). Qed.
Lemma lem5152952 (s : real -> Prop) : (term29 s) = (term243 s).
Proof. exact (TRANS (@lem5152951 s) (@lem5152950 s)). Qed.
Lemma lem5152953 : term30 = term244.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5152952 s)). Qed.
Lemma lem5152954 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5153055 : term17 = term245.
Proof. exact (MK_COMB (@lem5152954) (@lem5152953)). Qed.
Lemma lem5153056 (h1 : term17) : term245.
Proof. exact (EQ_MP (@lem5153055) (@lem5152338 h1)). Qed.
Lemma lem5153057 (s : real -> Prop) (h1 : term213 s) : term213 s.
Proof. exact (h1). Qed.
Lemma lem5153058 (s : real -> Prop) (a : real) (h1 : term211 s a) : term211 s a.
Proof. exact (h1). Qed.
Lemma lem5153059 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term208 x s a.
Proof. exact (h1). Qed.
Lemma lem5153084 (y : real) (x : real) (z : real) : (term221 y x z) = (term221 y x z).
Proof. exact (eq_refl (term221 y x z)). Qed.
Lemma lem5153085 (y : real) (x : real) : (term223 y x) = (term223 y x).
Proof. exact (fun_ext (fun z : real => @lem5153084 y x z)). Qed.
Lemma lem5153086 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153087 (y : real) (x : real) : (term224 y x) = (term224 y x).
Proof. exact (MK_COMB (@lem5153086) (@lem5153085 y x)). Qed.
Lemma lem5153088 (x : real) : (term225 x) = (term225 x).
Proof. exact (fun_ext (fun y : real => @lem5153087 y x)). Qed.
Lemma lem5153089 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153090 (x : real) : (term226 x) = (term226 x).
Proof. exact (MK_COMB (@lem5153089) (@lem5153088 x)). Qed.
Lemma lem5153091 : term227 = term227.
Proof. exact (fun_ext (fun x : real => @lem5153090 x)). Qed.
Lemma lem5153092 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153093 : term228 = term228.
Proof. exact (MK_COMB (@lem5153092) (@lem5153091)). Qed.
Lemma lem5153094 (h1 : term37) : term228.
Proof. exact (EQ_MP (@lem5153093) (@lem5152924 h1)). Qed.
Lemma lem5153111 (x : real) (s : real -> Prop) : (term235 x s) = (term235 x s).
Proof. exact (eq_refl (term235 x s)). Qed.
Lemma lem5153112 (s : real -> Prop) : (term237 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5153111 x s)). Qed.
Lemma lem5153113 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153114 (s : real -> Prop) : (term238 s) = (term238 s).
Proof. exact (MK_COMB (@lem5153113) (@lem5153112 s)). Qed.
Lemma lem5153123 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5153124 (s : real -> Prop) : (term239 s) = (term239 s).
Proof. exact (MK_COMB (@lem5153123 s) (@lem5153114 s)). Qed.
Lemma lem5153139 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5153140 (s : real -> Prop) : (term243 s) = (term243 s).
Proof. exact (MK_COMB (@lem5153139 s) (@lem5153124 s)). Qed.
Lemma lem5153141 : term244 = term244.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5153140 s)). Qed.
Lemma lem5153142 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5153143 : term245 = term245.
Proof. exact (MK_COMB (@lem5153142) (@lem5153141)). Qed.
Lemma lem5153144 (h1 : term17) : term245.
Proof. exact (EQ_MP (@lem5153143) (@lem5153056 h1)). Qed.
Lemma lem5153159 (s : real -> Prop) (x : real) (a : real) : (term49 s x a) = (term49 s x a).
Proof. exact (eq_refl (term49 s x a)). Qed.
Lemma lem5153160 (s : real -> Prop) (a : real) : (term59 s a) = (term59 s a).
Proof. exact (fun_ext (fun x : real => @lem5153159 s x a)). Qed.
Lemma lem5153161 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153162 (s : real -> Prop) (a : real) : (term60 s a) = (term60 s a).
Proof. exact (MK_COMB (@lem5153161) (@lem5153160 s a)). Qed.
Lemma lem5153173 (s : real -> Prop) (a : real) : (term61 s a) = (term61 s a).
Proof. exact (eq_refl (term61 s a)). Qed.
Lemma lem5153174 (s : real -> Prop) (a : real) : (term63 s a) = (term63 s a).
Proof. exact (MK_COMB (@lem5153173 s a) (@lem5153162 s a)). Qed.
Lemma lem5153201 (s : real -> Prop) (x : real) (a : real) : (term179 s x a) = (term179 s x a).
Proof. exact (eq_refl (term179 s x a)). Qed.
Lemma lem5153202 (x : real) (s : real -> Prop) (a : real) : (term181 x s a) = (term181 x s a).
Proof. exact (MK_COMB (@lem5153201 s x a) (@lem5153174 s a)). Qed.
Lemma lem5153217 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5153218 (x : real) (s : real -> Prop) (a : real) : (term208 x s a) = (term208 x s a).
Proof. exact (MK_COMB (@lem5153217 s) (@lem5153202 x s a)). Qed.
Lemma lem5153219 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term208 x s a.
Proof. exact (EQ_MP (@lem5153218 x s a) (@lem5153059 x s a h1)). Qed.
Lemma lem5153220 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term181 x s a.
Proof. exact (proj2 (@lem5153219 x s a h1)). Qed.
Lemma lem5153221 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term76 s.
Proof. exact (proj1 (@lem5153219 x s a h1)). Qed.
Lemma lem5153224 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term143 s x a.
Proof. exact (h1). Qed.
Lemma lem5153225 (s : real -> Prop) (a : real) (h1 : term63 s a) : term63 s a.
Proof. exact (h1). Qed.
Lemma lem5153226 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term48 s x a.
Proof. exact (proj2 (@lem5153224 s x a h1)). Qed.
Lemma lem5153230 (s : real -> Prop) (a : real) (h1 : term63 s a) : term60 s a.
Proof. exact (proj2 (@lem5153225 s a h1)). Qed.
Lemma lem5153245 (y : real) (x : real) (z : real) : (term221 y x z) = (term221 y x z).
Proof. exact (eq_refl (term221 y x z)). Qed.
Lemma lem5153246 (y : real) (x : real) : (term223 y x) = (term223 y x).
Proof. exact (fun_ext (fun z : real => @lem5153245 y x z)). Qed.
Lemma lem5153247 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153248 (y : real) (x : real) : (term224 y x) = (term224 y x).
Proof. exact (MK_COMB (@lem5153247) (@lem5153246 y x)). Qed.
Lemma lem5153249 (x : real) : (term225 x) = (term225 x).
Proof. exact (fun_ext (fun y : real => @lem5153248 y x)). Qed.
Lemma lem5153250 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153251 (x : real) : (term226 x) = (term226 x).
Proof. exact (MK_COMB (@lem5153250) (@lem5153249 x)). Qed.
Lemma lem5153252 : term227 = term227.
Proof. exact (fun_ext (fun x : real => @lem5153251 x)). Qed.
Lemma lem5153253 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153255 : term228 = term228.
Proof. exact (MK_COMB (@lem5153253) (@lem5153252)). Qed.
Lemma lem5153256 (h1 : term37) : term228.
Proof. exact (EQ_MP (@lem5153255) (@lem5153094 h1)). Qed.
Lemma lem5153258 {A : Type'} (P : Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5153259 (P : Prop) (Q : real -> Prop) : (term248 P Q) = (term249 P Q).
Proof. exact (@lem5153258 real P Q). Qed.
Lemma lem5153260 (s : real -> Prop) : (term250 s) = (term251 s).
Proof. exact (@lem5153259 (term252 s) (term237 s)). Qed.
Lemma lem5153261 (x : real) (s : real -> Prop) : (term253 s x) = (term235 x s).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5153262 (s : real -> Prop) : (term254 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5153261 x s)). Qed.
Lemma lem5153263 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153264 (s : real -> Prop) : (term255 s) = (term238 s).
Proof. exact (MK_COMB (@lem5153263) (@lem5153262 s)). Qed.
Lemma lem5153265 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5153266 (s : real -> Prop) : (term250 s) = (term239 s).
Proof. exact (MK_COMB (@lem5153265 s) (@lem5153264 s)). Qed.
Lemma lem5153267 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5153268 (s : real -> Prop) : (term256 s) = (term257 s).
Proof. exact (MK_COMB (@lem5153267) (@lem5153266 s)). Qed.
Lemma lem5153269 (x : real) (s : real -> Prop) : (term253 s x) = (term235 x s).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5153270 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5153271 (x : real) (s : real -> Prop) : (term258 s x) = (term259 x s).
Proof. exact (MK_COMB (@lem5153270 s) (@lem5153269 x s)). Qed.
Lemma lem5153272 (s : real -> Prop) : (term260 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5153271 x s)). Qed.
Lemma lem5153273 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153274 (s : real -> Prop) : (term251 s) = (term262 s).
Proof. exact (MK_COMB (@lem5153273) (@lem5153272 s)). Qed.
Lemma lem5153275 (s : real -> Prop) : ((term250 s) = (term251 s)) = ((term239 s) = (term262 s)).
Proof. exact (MK_COMB (@lem5153268 s) (@lem5153274 s)). Qed.
Lemma lem5153276 (s : real -> Prop) : (term239 s) = (term262 s).
Proof. exact (EQ_MP (@lem5153275 s) (@lem5153260 s)). Qed.
Lemma lem5153277 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5153278 (s : real -> Prop) : (term243 s) = (term263 s).
Proof. exact (MK_COMB (@lem5153277 s) (@lem5153276 s)). Qed.
Lemma lem5153280 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5153281 (P : Prop) (Q : real -> Prop) : (term266 P Q) = (term267 P Q).
Proof. exact (@lem5153280 real P Q). Qed.
Lemma lem5153282 (s : real -> Prop) : (term268 s) = (term269 s).
Proof. exact (@lem5153281 (term232 s) (term261 s)). Qed.
Lemma lem5153283 (x : real) (s : real -> Prop) : (term270 s x) = (term259 x s).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5153284 (s : real -> Prop) : (term271 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5153283 x s)). Qed.
Lemma lem5153285 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153286 (s : real -> Prop) : (term272 s) = (term262 s).
Proof. exact (MK_COMB (@lem5153285) (@lem5153284 s)). Qed.
Lemma lem5153287 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5153288 (s : real -> Prop) : (term268 s) = (term263 s).
Proof. exact (MK_COMB (@lem5153287 s) (@lem5153286 s)). Qed.
Lemma lem5153289 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5153290 (s : real -> Prop) : (term273 s) = (term274 s).
Proof. exact (MK_COMB (@lem5153289) (@lem5153288 s)). Qed.
Lemma lem5153291 (x : real) (s : real -> Prop) : (term270 s x) = (term259 x s).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5153292 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5153293 (x : real) (s : real -> Prop) : (term275 s x) = (term276 x s).
Proof. exact (MK_COMB (@lem5153292 s) (@lem5153291 x s)). Qed.
Lemma lem5153294 (s : real -> Prop) : (term277 s) = (term278 s).
Proof. exact (fun_ext (fun x : real => @lem5153293 x s)). Qed.
Lemma lem5153295 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153296 (s : real -> Prop) : (term269 s) = (term279 s).
Proof. exact (MK_COMB (@lem5153295) (@lem5153294 s)). Qed.
Lemma lem5153297 (s : real -> Prop) : ((term268 s) = (term269 s)) = ((term263 s) = (term279 s)).
Proof. exact (MK_COMB (@lem5153290 s) (@lem5153296 s)). Qed.
Lemma lem5153298 (s : real -> Prop) : (term263 s) = (term279 s).
Proof. exact (EQ_MP (@lem5153297 s) (@lem5153282 s)). Qed.
Lemma lem5153299 (s : real -> Prop) : (term243 s) = (term279 s).
Proof. exact (TRANS (@lem5153278 s) (@lem5153298 s)). Qed.
Lemma lem5153300 : term244 = term280.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5153299 s)). Qed.
Lemma lem5153301 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5153302 : term245 = term281.
Proof. exact (MK_COMB (@lem5153301) (@lem5153300)). Qed.
Lemma lem5153331 (x : real) (s : real -> Prop) : (term276 x s) = (term282 x s).
Proof. exact (@lem19490 (term252 s) (term232 s) (term235 x s)). Qed.
Lemma lem5153332 (s : real -> Prop) : (term278 s) = (term283 s).
Proof. exact (fun_ext (fun x : real => @lem5153331 x s)). Qed.
Lemma lem5153333 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153334 (s : real -> Prop) : (term279 s) = (term284 s).
Proof. exact (MK_COMB (@lem5153333) (@lem5153332 s)). Qed.
Lemma lem5153335 : term280 = term285.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5153334 s)). Qed.
Lemma lem5153336 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5153337 : term281 = term286.
Proof. exact (MK_COMB (@lem5153336) (@lem5153335)). Qed.
Lemma lem5153338 : term245 = term286.
Proof. exact (TRANS (@lem5153302) (@lem5153337)). Qed.
Lemma lem5153339 (h1 : term17) : term286.
Proof. exact (EQ_MP (@lem5153338) (@lem5153144 h1)). Qed.
Lemma lem5153386 {A : Type'} (P : Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5153387 (P : Prop) (Q : real -> Prop) : (term248 P Q) = (term249 P Q).
Proof. exact (@lem5153386 real P Q). Qed.
Lemma lem5153388 (s : real -> Prop) : (term250 s) = (term251 s).
Proof. exact (@lem5153387 (term252 s) (term237 s)). Qed.
Lemma lem5153389 (x : real) (s : real -> Prop) : (term253 s x) = (term235 x s).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5153390 (s : real -> Prop) : (term254 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5153389 x s)). Qed.
Lemma lem5153391 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153392 (s : real -> Prop) : (term255 s) = (term238 s).
Proof. exact (MK_COMB (@lem5153391) (@lem5153390 s)). Qed.
Lemma lem5153393 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5153394 (s : real -> Prop) : (term250 s) = (term239 s).
Proof. exact (MK_COMB (@lem5153393 s) (@lem5153392 s)). Qed.
Lemma lem5153395 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5153396 (s : real -> Prop) : (term256 s) = (term257 s).
Proof. exact (MK_COMB (@lem5153395) (@lem5153394 s)). Qed.
Lemma lem5153397 (x : real) (s : real -> Prop) : (term253 s x) = (term235 x s).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5153398 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5153399 (x : real) (s : real -> Prop) : (term258 s x) = (term259 x s).
Proof. exact (MK_COMB (@lem5153398 s) (@lem5153397 x s)). Qed.
Lemma lem5153400 (s : real -> Prop) : (term260 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5153399 x s)). Qed.
Lemma lem5153401 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153402 (s : real -> Prop) : (term251 s) = (term262 s).
Proof. exact (MK_COMB (@lem5153401) (@lem5153400 s)). Qed.
Lemma lem5153403 (s : real -> Prop) : ((term250 s) = (term251 s)) = ((term239 s) = (term262 s)).
Proof. exact (MK_COMB (@lem5153396 s) (@lem5153402 s)). Qed.
Lemma lem5153404 (s : real -> Prop) : (term239 s) = (term262 s).
Proof. exact (EQ_MP (@lem5153403 s) (@lem5153388 s)). Qed.
Lemma lem5153405 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5153406 (s : real -> Prop) : (term243 s) = (term263 s).
Proof. exact (MK_COMB (@lem5153405 s) (@lem5153404 s)). Qed.
Lemma lem5153408 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5153409 (P : Prop) (Q : real -> Prop) : (term266 P Q) = (term267 P Q).
Proof. exact (@lem5153408 real P Q). Qed.
Lemma lem5153410 (s : real -> Prop) : (term268 s) = (term269 s).
Proof. exact (@lem5153409 (term232 s) (term261 s)). Qed.
Lemma lem5153411 (x : real) (s : real -> Prop) : (term270 s x) = (term259 x s).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5153412 (s : real -> Prop) : (term271 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5153411 x s)). Qed.
Lemma lem5153413 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153414 (s : real -> Prop) : (term272 s) = (term262 s).
Proof. exact (MK_COMB (@lem5153413) (@lem5153412 s)). Qed.
Lemma lem5153415 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5153416 (s : real -> Prop) : (term268 s) = (term263 s).
Proof. exact (MK_COMB (@lem5153415 s) (@lem5153414 s)). Qed.
Lemma lem5153417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5153418 (s : real -> Prop) : (term273 s) = (term274 s).
Proof. exact (MK_COMB (@lem5153417) (@lem5153416 s)). Qed.
Lemma lem5153419 (x : real) (s : real -> Prop) : (term270 s x) = (term259 x s).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5153420 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5153421 (x : real) (s : real -> Prop) : (term275 s x) = (term276 x s).
Proof. exact (MK_COMB (@lem5153420 s) (@lem5153419 x s)). Qed.
Lemma lem5153422 (s : real -> Prop) : (term277 s) = (term278 s).
Proof. exact (fun_ext (fun x : real => @lem5153421 x s)). Qed.
Lemma lem5153423 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153424 (s : real -> Prop) : (term269 s) = (term279 s).
Proof. exact (MK_COMB (@lem5153423) (@lem5153422 s)). Qed.
Lemma lem5153425 (s : real -> Prop) : ((term268 s) = (term269 s)) = ((term263 s) = (term279 s)).
Proof. exact (MK_COMB (@lem5153418 s) (@lem5153424 s)). Qed.
Lemma lem5153426 (s : real -> Prop) : (term263 s) = (term279 s).
Proof. exact (EQ_MP (@lem5153425 s) (@lem5153410 s)). Qed.
Lemma lem5153427 (s : real -> Prop) : (term243 s) = (term279 s).
Proof. exact (TRANS (@lem5153406 s) (@lem5153426 s)). Qed.
Lemma lem5153428 : term244 = term280.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5153427 s)). Qed.
Lemma lem5153429 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5153430 : term245 = term281.
Proof. exact (MK_COMB (@lem5153429) (@lem5153428)). Qed.
Lemma lem5153459 (x : real) (s : real -> Prop) : (term276 x s) = (term282 x s).
Proof. exact (@lem19490 (term252 s) (term232 s) (term235 x s)). Qed.
Lemma lem5153460 (s : real -> Prop) : (term278 s) = (term283 s).
Proof. exact (fun_ext (fun x : real => @lem5153459 x s)). Qed.
Lemma lem5153461 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153462 (s : real -> Prop) : (term279 s) = (term284 s).
Proof. exact (MK_COMB (@lem5153461) (@lem5153460 s)). Qed.
Lemma lem5153463 : term280 = term285.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5153462 s)). Qed.
Lemma lem5153464 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5153465 : term281 = term286.
Proof. exact (MK_COMB (@lem5153464) (@lem5153463)). Qed.
Lemma lem5153466 : term245 = term286.
Proof. exact (TRANS (@lem5153430) (@lem5153465)). Qed.
Lemma lem5153467 (h1 : term17) : term286.
Proof. exact (EQ_MP (@lem5153466) (@lem5153144 h1)). Qed.
Lemma lem5153487 (s : real -> Prop) (x : real) (a : real) : (term49 s x a) = (term49 s x a).
Proof. exact (eq_refl (term49 s x a)). Qed.
Lemma lem5153488 (s : real -> Prop) (a : real) : (term59 s a) = (term59 s a).
Proof. exact (fun_ext (fun x : real => @lem5153487 s x a)). Qed.
Lemma lem5153489 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5153491 (s : real -> Prop) (a : real) : (term60 s a) = (term60 s a).
Proof. exact (MK_COMB (@lem5153489) (@lem5153488 s a)). Qed.
Lemma lem5153492 (s : real -> Prop) (a : real) (h1 : term63 s a) : term60 s a.
Proof. exact (EQ_MP (@lem5153491 s a) (@lem5153230 s a h1)). Qed.
Lemma lem5153493 (_67289 : real) (h1 : term37) : term287 _67289.
Proof. exact (@lem5153256 h1 _67289). Qed.
Lemma lem5153494 (_67289 : real) : (term287 _67289) = (term226 _67289).
Proof. exact (eq_refl (term287 _67289)). Qed.
Lemma lem5153495 (_67289 : real) (h1 : term37) : term226 _67289.
Proof. exact (EQ_MP (@lem5153494 _67289) (@lem5153493 _67289 h1)). Qed.
Lemma lem5153496 (_67289 : real) (_67290 : real) (h1 : term37) : term288 _67289 _67290.
Proof. exact (@lem5153495 _67289 h1 _67290). Qed.
Lemma lem5153497 (_67290 : real) (_67289 : real) : (term288 _67289 _67290) = (term224 _67290 _67289).
Proof. exact (eq_refl (term288 _67289 _67290)). Qed.
Lemma lem5153498 (_67290 : real) (_67289 : real) (h1 : term37) : term224 _67290 _67289.
Proof. exact (EQ_MP (@lem5153497 _67290 _67289) (@lem5153496 _67289 _67290 h1)). Qed.
Lemma lem5153499 (_67290 : real) (_67289 : real) (_67291 : real) (h1 : term37) : term289 _67290 _67289 _67291.
Proof. exact (@lem5153498 _67290 _67289 h1 _67291). Qed.
Lemma lem5153500 (_67290 : real) (_67289 : real) (_67291 : real) : (term289 _67290 _67289 _67291) = (term221 _67290 _67289 _67291).
Proof. exact (eq_refl (term289 _67290 _67289 _67291)). Qed.
Lemma lem5153501 (_67290 : real) (_67289 : real) (_67291 : real) (h1 : term37) : term221 _67290 _67289 _67291.
Proof. exact (EQ_MP (@lem5153500 _67290 _67289 _67291) (@lem5153499 _67290 _67289 _67291 h1)). Qed.
Lemma lem5153502 (_67292 : real -> Prop) (h1 : term17) : term290 _67292.
Proof. exact (@lem5153339 h1 _67292). Qed.
Lemma lem5153503 (_67292 : real -> Prop) : (term290 _67292) = (term284 _67292).
Proof. exact (eq_refl (term290 _67292)). Qed.
Lemma lem5153504 (_67292 : real -> Prop) (h1 : term17) : term284 _67292.
Proof. exact (EQ_MP (@lem5153503 _67292) (@lem5153502 _67292 h1)). Qed.
Lemma lem5153505 (_67292 : real -> Prop) (_67293 : real) (h1 : term17) : term291 _67292 _67293.
Proof. exact (@lem5153504 _67292 h1 _67293). Qed.
Lemma lem5153506 (_67293 : real) (_67292 : real -> Prop) : (term291 _67292 _67293) = (term282 _67293 _67292).
Proof. exact (eq_refl (term291 _67292 _67293)). Qed.
Lemma lem5153507 (_67293 : real) (_67292 : real -> Prop) (h1 : term17) : term282 _67293 _67292.
Proof. exact (EQ_MP (@lem5153506 _67293 _67292) (@lem5153505 _67292 _67293 h1)). Qed.
Lemma lem5153517 (_67297 : real -> Prop) (h1 : term17) : term290 _67297.
Proof. exact (@lem5153467 h1 _67297). Qed.
Lemma lem5153518 (_67297 : real -> Prop) : (term290 _67297) = (term284 _67297).
Proof. exact (eq_refl (term290 _67297)). Qed.
Lemma lem5153519 (_67297 : real -> Prop) (h1 : term17) : term284 _67297.
Proof. exact (EQ_MP (@lem5153518 _67297) (@lem5153517 _67297 h1)). Qed.
Lemma lem5153520 (_67297 : real -> Prop) (_67298 : real) (h1 : term17) : term291 _67297 _67298.
Proof. exact (@lem5153519 _67297 h1 _67298). Qed.
Lemma lem5153521 (_67298 : real) (_67297 : real -> Prop) : (term291 _67297 _67298) = (term282 _67298 _67297).
Proof. exact (eq_refl (term291 _67297 _67298)). Qed.
Lemma lem5153522 (_67298 : real) (_67297 : real -> Prop) (h1 : term17) : term282 _67298 _67297.
Proof. exact (EQ_MP (@lem5153521 _67298 _67297) (@lem5153520 _67297 _67298 h1)). Qed.
Lemma lem5153523 (_67299 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term292 s a _67299.
Proof. exact (@lem5153492 s a h1 _67299). Qed.
Lemma lem5153524 (s : real -> Prop) (_67299 : real) (a : real) : (term292 s a _67299) = (term49 s _67299 a).
Proof. exact (eq_refl (term292 s a _67299)). Qed.
Lemma lem5153526 (_67293 : real) (_67292 : real -> Prop) (h1 : term17) : term293 _67293 _67292.
Proof. exact (proj2 (@lem5153507 _67293 _67292 h1)). Qed.
Lemma lem5153529 (_67297 : real -> Prop) (h1 : term17) : term294 _67297.
Proof. exact (proj1 (@lem5153522 (@el real) _67297 h1)). Qed.
Lemma lem5153540 (_67290 : real) (_67289 : real) (_67291 : real) : (term221 _67290 _67289 _67291) = (term295 _67290 _67289 _67291).
Proof. exact (@lem5152091 (term296 _67289 _67290) (term297 _67290 _67291) (real_lt _67289 _67291)). Qed.
Lemma lem5153541 (_67290 : real) (_67289 : real) (_67291 : real) (h1 : term37) : term295 _67290 _67289 _67291.
Proof. exact (EQ_MP (@lem5153540 _67290 _67289 _67291) (@lem5153501 _67290 _67289 _67291 h1)). Qed.
Lemma lem5153551 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term297 x a.
Proof. exact (proj2 (@lem5153226 s x a h1)). Qed.
Lemma lem5153578 (_67293 : real) (_67292 : real -> Prop) : (term293 _67293 _67292) = (term298 _67293 _67292).
Proof. exact (@lem5152091 (term299 _67292) (_67292 = (@EMPTY real)) (term235 _67293 _67292)). Qed.
Lemma lem5153579 (_67293 : real) (_67292 : real -> Prop) (h1 : term17) : term298 _67293 _67292.
Proof. exact (EQ_MP (@lem5153578 _67293 _67292) (@lem5153526 _67293 _67292 h1)). Qed.
Lemma lem5153597 (s : real -> Prop) (a : real) (h1 : term63 s a) : term300 s a.
Proof. exact (proj1 (@lem5153225 s a h1)). Qed.
Lemma lem5153603 (_67299 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term49 s _67299 a.
Proof. exact (EQ_MP (@lem5153524 s _67299 a) (@lem5153523 _67299 s a h1)). Qed.
Lemma lem5153614 (_67297 : real -> Prop) : (term294 _67297) = (term301 _67297).
Proof. exact (@lem5152091 (term299 _67297) (_67297 = (@EMPTY real)) (term252 _67297)). Qed.
Lemma lem5153615 (_67297 : real -> Prop) (h1 : term17) : term301 _67297.
Proof. exact (EQ_MP (@lem5153614 _67297) (@lem5153529 _67297 h1)). Qed.
Lemma lem5153714 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (proj1 (@lem5153221 x s a h1)). Qed.
Lemma lem5153715 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term302 s.
Proof. exact (fun h0 : term299 s => @lem5153714 x s a h1). Qed.
Lemma lem5153717 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5153718 (s : real -> Prop) : (term302 s) = (@FINITE real s).
Proof. exact (@lem5153717 (@FINITE real s)). Qed.
Lemma lem5153719 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (EQ_MP (@lem5153718 s) (@lem5153715 x s a h1)). Qed.
Lemma lem5153721 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (proj2 (@lem5153221 x s a h1)). Qed.
Lemma lem5153722 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term304 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5153721 x s a h1). Qed.
Lemma lem5153724 (p : Prop) : (term305 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5153725 (s : real -> Prop) : (term304 s) = (term234 s).
Proof. exact (@lem5153724 (s = (@EMPTY real))). Qed.
Lemma lem5153726 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (EQ_MP (@lem5153725 s) (@lem5153722 x s a h1)). Qed.
Lemma lem5153728 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : @IN real x s.
Proof. exact (proj1 (@lem5153226 s x a h1)). Qed.
Lemma lem5153729 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term306 x s.
Proof. exact (fun h0 : term307 x s => @lem5153728 s x a h1). Qed.
Lemma lem5153731 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5153732 (x : real) (s : real -> Prop) : (term306 x s) = (@IN real x s).
Proof. exact (@lem5153731 (@IN real x s)). Qed.
Lemma lem5153733 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : @IN real x s.
Proof. exact (EQ_MP (@lem5153732 x s) (@lem5153729 s x a h1)). Qed.
Lemma lem5153739 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5153740 (_67293 : real) (_67292 : real -> Prop) : (term298 _67293 _67292) = (term308 _67293 _67292).
Proof. exact (@lem5153739 (_67292 = (@EMPTY real)) (term299 _67292) (term235 _67293 _67292)). Qed.
Lemma lem5153766 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5153767 (_67293 : real) (_67292 : real -> Prop) : (term235 _67293 _67292) = (term309 _67293 _67292).
Proof. exact (@lem5153766 (term236 _67293 _67292) (term307 _67293 _67292)). Qed.
Lemma lem5153773 (_67292 : real -> Prop) : (term230 _67292) = (term230 _67292).
Proof. exact (eq_refl (term230 _67292)). Qed.
Lemma lem5153774 (_67293 : real) (_67292 : real -> Prop) : (term310 _67293 _67292) = (term311 _67293 _67292).
Proof. exact (MK_COMB (@lem5153773 _67292) (@lem5153767 _67293 _67292)). Qed.
Lemma lem5153778 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5153779 (_67293 : real) (_67292 : real -> Prop) : (term311 _67293 _67292) = (term312 _67293 _67292).
Proof. exact (@lem5153778 (term236 _67293 _67292) (term299 _67292) (term307 _67293 _67292)). Qed.
Lemma lem5153795 (_67293 : real) (_67292 : real -> Prop) : (term310 _67293 _67292) = (term312 _67293 _67292).
Proof. exact (TRANS (@lem5153774 _67293 _67292) (@lem5153779 _67293 _67292)). Qed.
Lemma lem5153796 (_67292 : real -> Prop) : (term313 _67292) = (term313 _67292).
Proof. exact (eq_refl (term313 _67292)). Qed.
Lemma lem5153797 (_67293 : real) (_67292 : real -> Prop) : (term308 _67293 _67292) = (term314 _67293 _67292).
Proof. exact (MK_COMB (@lem5153796 _67292) (@lem5153795 _67293 _67292)). Qed.
Lemma lem5153808 (_67293 : real) (_67292 : real -> Prop) : (term298 _67293 _67292) = (term314 _67293 _67292).
Proof. exact (TRANS (@lem5153740 _67293 _67292) (@lem5153797 _67293 _67292)). Qed.
Lemma lem5153809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5153810 (_67293 : real) (_67292 : real -> Prop) : (term315 _67293 _67292) = (term316 _67293 _67292).
Proof. exact (MK_COMB (@lem5153809) (@lem5153808 _67293 _67292)). Qed.
Lemma lem5153824 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5153825 (_67293 : real) (_67292 : real -> Prop) : (term317 _67293 _67292) = (term318 _67293 _67292).
Proof. exact (@lem5153824 (_67292 = (@EMPTY real)) (term299 _67292) (term307 _67293 _67292)). Qed.
Lemma lem5153843 (_67293 : real) (_67292 : real -> Prop) : (term319 _67293 _67292) = (term319 _67293 _67292).
Proof. exact (eq_refl (term319 _67293 _67292)). Qed.
Lemma lem5153844 (_67293 : real) (_67292 : real -> Prop) : (term320 _67293 _67292) = (term321 _67293 _67292).
Proof. exact (MK_COMB (@lem5153843 _67293 _67292) (@lem5153825 _67293 _67292)). Qed.
Lemma lem5153848 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5153849 (_67293 : real) (_67292 : real -> Prop) : (term321 _67293 _67292) = (term314 _67293 _67292).
Proof. exact (@lem5153848 (_67292 = (@EMPTY real)) (term236 _67293 _67292) (term322 _67293 _67292)). Qed.
Lemma lem5153877 (_67293 : real) (_67292 : real -> Prop) : (term320 _67293 _67292) = (term314 _67293 _67292).
Proof. exact (TRANS (@lem5153844 _67293 _67292) (@lem5153849 _67293 _67292)). Qed.
Lemma lem5153878 (_67293 : real) (_67292 : real -> Prop) : ((term298 _67293 _67292) = (term320 _67293 _67292)) = ((term314 _67293 _67292) = (term314 _67293 _67292)).
Proof. exact (MK_COMB (@lem5153810 _67293 _67292) (@lem5153877 _67293 _67292)). Qed.
Lemma lem5153880 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5153881 (x : Prop) : (x = x) = True.
Proof. exact (@lem5153880 Prop x). Qed.
Lemma lem5153882 (_67293 : real) (_67292 : real -> Prop) : ((term314 _67293 _67292) = (term314 _67293 _67292)) = True.
Proof. exact (@lem5153881 (term314 _67293 _67292)). Qed.
Lemma lem5153883 (_67293 : real) (_67292 : real -> Prop) : ((term298 _67293 _67292) = (term320 _67293 _67292)) = True.
Proof. exact (TRANS (@lem5153878 _67293 _67292) (@lem5153882 _67293 _67292)). Qed.
Lemma lem5153884 (_67293 : real) (_67292 : real -> Prop) : True = ((term298 _67293 _67292) = (term320 _67293 _67292)).
Proof. exact (SYM (@lem5153883 _67293 _67292)). Qed.
Lemma lem5153885 (_67293 : real) (_67292 : real -> Prop) : (term298 _67293 _67292) = (term320 _67293 _67292).
Proof. exact (EQ_MP (@lem5153884 _67293 _67292) (@lem0)). Qed.
Lemma lem5153886 (_67293 : real) (_67292 : real -> Prop) (h1 : term17) : term320 _67293 _67292.
Proof. exact (EQ_MP (@lem5153885 _67293 _67292) (@lem5153579 _67293 _67292 h1)). Qed.
Lemma lem5153888 (b : Prop) (a : Prop) : (a \/ b) = (term323 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5153889 (_67293 : real) (_67292 : real -> Prop) : (term320 _67293 _67292) = (term324 _67293 _67292).
Proof. exact (@lem5153888 (term317 _67293 _67292) (term236 _67293 _67292)). Qed.
Lemma lem5153891 (a : Prop) (b : Prop) : (term325 a b) = (term326 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5153892 (_67293 : real) (_67292 : real -> Prop) : (term327 _67293 _67292) = (term328 _67293 _67292).
Proof. exact (@lem5153891 (term299 _67292) (term329 _67293 _67292)). Qed.
Lemma lem5153894 (a : Prop) : (term330 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5153895 (_67292 : real -> Prop) : (term331 _67292) = (@FINITE real _67292).
Proof. exact (@lem5153894 (@FINITE real _67292)). Qed.
Lemma lem5153896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5153897 (_67292 : real -> Prop) : (term332 _67292) = (term333 _67292).
Proof. exact (MK_COMB (@lem5153896) (@lem5153895 _67292)). Qed.
Lemma lem5153899 (a : Prop) (b : Prop) : (term325 a b) = (term326 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5153900 (_67293 : real) (_67292 : real -> Prop) : (term334 _67293 _67292) = (term335 _67293 _67292).
Proof. exact (@lem5153899 (_67292 = (@EMPTY real)) (term307 _67293 _67292)). Qed.
Lemma lem5153902 (a : Prop) : (term330 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5153903 (_67293 : real) (_67292 : real -> Prop) : (term336 _67293 _67292) = (@IN real _67293 _67292).
Proof. exact (@lem5153902 (@IN real _67293 _67292)). Qed.
Lemma lem5153904 (_67292 : real -> Prop) : (term337 _67292) = (term337 _67292).
Proof. exact (eq_refl (term337 _67292)). Qed.
Lemma lem5153905 (_67293 : real) (_67292 : real -> Prop) : (term335 _67293 _67292) = (term338 _67293 _67292).
Proof. exact (MK_COMB (@lem5153904 _67292) (@lem5153903 _67293 _67292)). Qed.
Lemma lem5153906 (_67293 : real) (_67292 : real -> Prop) : (term334 _67293 _67292) = (term338 _67293 _67292).
Proof. exact (TRANS (@lem5153900 _67293 _67292) (@lem5153905 _67293 _67292)). Qed.
Lemma lem5153907 (_67293 : real) (_67292 : real -> Prop) : (term328 _67293 _67292) = (term339 _67293 _67292).
Proof. exact (MK_COMB (@lem5153897 _67292) (@lem5153906 _67293 _67292)). Qed.
Lemma lem5153908 (_67293 : real) (_67292 : real -> Prop) : (term327 _67293 _67292) = (term339 _67293 _67292).
Proof. exact (TRANS (@lem5153892 _67293 _67292) (@lem5153907 _67293 _67292)). Qed.
Lemma lem5153909 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5153910 (_67293 : real) (_67292 : real -> Prop) : (term340 _67293 _67292) = (term341 _67293 _67292).
Proof. exact (MK_COMB (@lem5153909) (@lem5153908 _67293 _67292)). Qed.
Lemma lem5153911 (_67293 : real) (_67292 : real -> Prop) : (term236 _67293 _67292) = (term236 _67293 _67292).
Proof. exact (eq_refl (term236 _67293 _67292)). Qed.
Lemma lem5153912 (_67293 : real) (_67292 : real -> Prop) : (term324 _67293 _67292) = (term342 _67293 _67292).
Proof. exact (MK_COMB (@lem5153910 _67293 _67292) (@lem5153911 _67293 _67292)). Qed.
Lemma lem5153913 (_67293 : real) (_67292 : real -> Prop) : (term320 _67293 _67292) = (term342 _67293 _67292).
Proof. exact (TRANS (@lem5153889 _67293 _67292) (@lem5153912 _67293 _67292)). Qed.
Lemma lem5153915 (s : real -> Prop) (x : real) (a : real) (h1 : term208 x s a) (h2 : term143 s x a) : term338 x s.
Proof. exact (conj (@lem5153726 x s a h1) (@lem5153733 s x a h2)). Qed.
Lemma lem5153916 (s : real -> Prop) (x : real) (a : real) (h1 : term208 x s a) (h2 : term143 s x a) : term339 x s.
Proof. exact (conj (@lem5153719 x s a h1) (@lem5153915 s x a h1 h2)). Qed.
Lemma lem5153918 (_67293 : real) (_67292 : real -> Prop) (h1 : term17) : term342 _67293 _67292.
Proof. exact (EQ_MP (@lem5153913 _67293 _67292) (@lem5153886 _67293 _67292 h1)). Qed.
Lemma lem5153919 (x : real) (s : real -> Prop) (h1 : term17) : term342 x s.
Proof. exact (@lem5153918 x s h1). Qed.
Lemma lem5153922 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s x a) : term236 x s.
Proof. exact (@lem5153919 x s h1 (@lem5153916 s x a h2 h3)). Qed.
Lemma lem5153923 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s x a) : term343 x s.
Proof. exact (fun h0 : term344 x s => @lem5153922 s x a h1 h2 h3). Qed.
Lemma lem5153925 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5153926 (x : real) (s : real -> Prop) : (term343 x s) = (term236 x s).
Proof. exact (@lem5153925 (term236 x s)). Qed.
Lemma lem5153927 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s x a) : term236 x s.
Proof. exact (EQ_MP (@lem5153926 x s) (@lem5153923 s x a h1 h2 h3)). Qed.
Lemma lem5153929 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term42 s a.
Proof. exact (proj1 (@lem5153224 s x a h1)). Qed.
Lemma lem5153930 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term345 s a.
Proof. exact (fun h0 : term300 s a => @lem5153929 s x a h1). Qed.
Lemma lem5153932 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5153933 (s : real -> Prop) (a : real) : (term345 s a) = (term42 s a).
Proof. exact (@lem5153932 (term42 s a)). Qed.
Lemma lem5153934 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term42 s a.
Proof. exact (EQ_MP (@lem5153933 s a) (@lem5153930 s x a h1)). Qed.
Lemma lem5153950 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5153951 (_67289 : real) (_67290 : real) (_67291 : real) : (term346 _67290 _67289 _67291) = (term347 _67289 _67290 _67291).
Proof. exact (@lem5153950 (real_lt _67289 _67291) (term297 _67290 _67291)). Qed.
Lemma lem5153957 (_67289 : real) (_67290 : real) : (term348 _67289 _67290) = (term348 _67289 _67290).
Proof. exact (eq_refl (term348 _67289 _67290)). Qed.
Lemma lem5153958 (_67289 : real) (_67290 : real) (_67291 : real) : (term295 _67290 _67289 _67291) = (term349 _67289 _67290 _67291).
Proof. exact (MK_COMB (@lem5153957 _67289 _67290) (@lem5153951 _67289 _67290 _67291)). Qed.
Lemma lem5153962 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5153963 (_67289 : real) (_67290 : real) (_67291 : real) : (term349 _67289 _67290 _67291) = (term350 _67289 _67290 _67291).
Proof. exact (@lem5153962 (real_lt _67289 _67291) (term296 _67289 _67290) (term297 _67290 _67291)). Qed.
Lemma lem5153979 (_67289 : real) (_67290 : real) (_67291 : real) : (term295 _67290 _67289 _67291) = (term350 _67289 _67290 _67291).
Proof. exact (TRANS (@lem5153958 _67289 _67290 _67291) (@lem5153963 _67289 _67290 _67291)). Qed.
Lemma lem5153980 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5153981 (_67289 : real) (_67290 : real) (_67291 : real) : (term351 _67290 _67289 _67291) = (term352 _67289 _67290 _67291).
Proof. exact (MK_COMB (@lem5153980) (@lem5153979 _67289 _67290 _67291)). Qed.
Lemma lem5153997 (_67289 : real) (_67290 : real) (_67291 : real) : (term350 _67289 _67290 _67291) = (term350 _67289 _67290 _67291).
Proof. exact (eq_refl (term350 _67289 _67290 _67291)). Qed.
Lemma lem5153998 (_67289 : real) (_67290 : real) (_67291 : real) : ((term295 _67290 _67289 _67291) = (term350 _67289 _67290 _67291)) = ((term350 _67289 _67290 _67291) = (term350 _67289 _67290 _67291)).
Proof. exact (MK_COMB (@lem5153981 _67289 _67290 _67291) (@lem5153997 _67289 _67290 _67291)). Qed.
Lemma lem5154000 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5154001 (x : Prop) : (x = x) = True.
Proof. exact (@lem5154000 Prop x). Qed.
Lemma lem5154002 (_67289 : real) (_67290 : real) (_67291 : real) : ((term350 _67289 _67290 _67291) = (term350 _67289 _67290 _67291)) = True.
Proof. exact (@lem5154001 (term350 _67289 _67290 _67291)). Qed.
Lemma lem5154003 (_67289 : real) (_67290 : real) (_67291 : real) : ((term295 _67290 _67289 _67291) = (term350 _67289 _67290 _67291)) = True.
Proof. exact (TRANS (@lem5153998 _67289 _67290 _67291) (@lem5154002 _67289 _67290 _67291)). Qed.
Lemma lem5154004 (_67289 : real) (_67290 : real) (_67291 : real) : True = ((term295 _67290 _67289 _67291) = (term350 _67289 _67290 _67291)).
Proof. exact (SYM (@lem5154003 _67289 _67290 _67291)). Qed.
Lemma lem5154005 (_67289 : real) (_67290 : real) (_67291 : real) : (term295 _67290 _67289 _67291) = (term350 _67289 _67290 _67291).
Proof. exact (EQ_MP (@lem5154004 _67289 _67290 _67291) (@lem0)). Qed.
Lemma lem5154006 (_67289 : real) (_67290 : real) (_67291 : real) (h1 : term37) : term350 _67289 _67290 _67291.
Proof. exact (EQ_MP (@lem5154005 _67289 _67290 _67291) (@lem5153541 _67290 _67289 _67291 h1)). Qed.
Lemma lem5154008 (b : Prop) (a : Prop) : (a \/ b) = (term323 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5154009 (_67290 : real) (_67289 : real) (_67291 : real) : (term350 _67289 _67290 _67291) = (term353 _67290 _67289 _67291).
Proof. exact (@lem5154008 (term217 _67289 _67290 _67291) (real_lt _67289 _67291)). Qed.
Lemma lem5154011 (a : Prop) (b : Prop) : (term325 a b) = (term326 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5154012 (_67289 : real) (_67290 : real) (_67291 : real) : (term354 _67289 _67290 _67291) = (term355 _67289 _67290 _67291).
Proof. exact (@lem5154011 (term296 _67289 _67290) (term297 _67290 _67291)). Qed.
Lemma lem5154014 (a : Prop) : (term330 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5154015 (_67289 : real) (_67290 : real) : (term356 _67289 _67290) = (real_le _67289 _67290).
Proof. exact (@lem5154014 (real_le _67289 _67290)). Qed.
Lemma lem5154016 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5154017 (_67289 : real) (_67290 : real) : (term357 _67289 _67290) = (term358 _67289 _67290).
Proof. exact (MK_COMB (@lem5154016) (@lem5154015 _67289 _67290)). Qed.
Lemma lem5154019 (a : Prop) : (term330 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5154020 (_67290 : real) (_67291 : real) : (term359 _67290 _67291) = (real_lt _67290 _67291).
Proof. exact (@lem5154019 (real_lt _67290 _67291)). Qed.
Lemma lem5154021 (_67289 : real) (_67290 : real) (_67291 : real) : (term355 _67289 _67290 _67291) = (term222 _67289 _67290 _67291).
Proof. exact (MK_COMB (@lem5154017 _67289 _67290) (@lem5154020 _67290 _67291)). Qed.
Lemma lem5154022 (_67289 : real) (_67290 : real) (_67291 : real) : (term354 _67289 _67290 _67291) = (term222 _67289 _67290 _67291).
Proof. exact (TRANS (@lem5154012 _67289 _67290 _67291) (@lem5154021 _67289 _67290 _67291)). Qed.
Lemma lem5154023 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5154024 (_67289 : real) (_67290 : real) (_67291 : real) : (term360 _67289 _67290 _67291) = (term361 _67289 _67290 _67291).
Proof. exact (MK_COMB (@lem5154023) (@lem5154022 _67289 _67290 _67291)). Qed.
Lemma lem5154025 (_67289 : real) (_67291 : real) : (real_lt _67289 _67291) = (real_lt _67289 _67291).
Proof. exact (eq_refl (real_lt _67289 _67291)). Qed.
Lemma lem5154026 (_67290 : real) (_67289 : real) (_67291 : real) : (term353 _67290 _67289 _67291) = (term31 _67290 _67289 _67291).
Proof. exact (MK_COMB (@lem5154024 _67289 _67290 _67291) (@lem5154025 _67289 _67291)). Qed.
Lemma lem5154027 (_67290 : real) (_67289 : real) (_67291 : real) : (term350 _67289 _67290 _67291) = (term31 _67290 _67289 _67291).
Proof. exact (TRANS (@lem5154009 _67290 _67289 _67291) (@lem5154026 _67290 _67289 _67291)). Qed.
Lemma lem5154029 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s x a) : term362 x s a.
Proof. exact (conj (@lem5153927 s x a h1 h2 h3) (@lem5153934 s x a h3)). Qed.
Lemma lem5154031 (_67290 : real) (_67289 : real) (_67291 : real) (h1 : term37) : term31 _67290 _67289 _67291.
Proof. exact (EQ_MP (@lem5154027 _67290 _67289 _67291) (@lem5154006 _67289 _67290 _67291 h1)). Qed.
Lemma lem5154032 (s : real -> Prop) (x : real) (a : real) (h1 : term37) : term363 s x a.
Proof. exact (@lem5154031 (sup s) x a h1). Qed.
Lemma lem5154035 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s x a) : real_lt x a.
Proof. exact (@lem5154032 s x a h2 (@lem5154029 s x a h1 h3 h4)). Qed.
Lemma lem5154036 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s x a) : term364 x a.
Proof. exact (fun h0 : term297 x a => @lem5154035 s x a h1 h2 h3 h4). Qed.
Lemma lem5154038 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5154039 (x : real) (a : real) : (term364 x a) = (real_lt x a).
Proof. exact (@lem5154038 (real_lt x a)). Qed.
Lemma lem5154040 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s x a) : real_lt x a.
Proof. exact (EQ_MP (@lem5154039 x a) (@lem5154036 s x a h1 h2 h3 h4)). Qed.
Lemma lem5154043 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5154045 (x : real) (a : real) : (term297 x a) = (term365 x a).
Proof. exact (@lem5154043 (real_lt x a)). Qed.
Lemma lem5154048 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term365 x a.
Proof. exact (EQ_MP (@lem5154045 x a) (@lem5153551 s x a h1)). Qed.
Lemma lem5154051 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s x a) : False.
Proof. exact (@lem5154048 s x a h4 (@lem5154040 s x a h1 h2 h3 h4)). Qed.
Lemma lem5154052 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s x a) : term366.
Proof. exact (fun h0 : ~ False => @lem5154051 s x a h1 h2 h3 h4). Qed.
Lemma lem5154054 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5154055 : term366 = False.
Proof. exact (@lem5154054 False). Qed.
Lemma lem5154056 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s x a) : False.
Proof. exact (EQ_MP (@lem5154055) (@lem5154052 s x a h1 h2 h3 h4)). Qed.
Lemma lem5154139 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (proj1 (@lem5153221 x s a h1)). Qed.
Lemma lem5154140 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term302 s.
Proof. exact (fun h0 : term299 s => @lem5154139 x s a h1). Qed.
Lemma lem5154142 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5154143 (s : real -> Prop) : (term302 s) = (@FINITE real s).
Proof. exact (@lem5154142 (@FINITE real s)). Qed.
Lemma lem5154144 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (EQ_MP (@lem5154143 s) (@lem5154140 x s a h1)). Qed.
Lemma lem5154146 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (proj2 (@lem5153221 x s a h1)). Qed.
Lemma lem5154147 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term304 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5154146 x s a h1). Qed.
Lemma lem5154149 (p : Prop) : (term305 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5154150 (s : real -> Prop) : (term304 s) = (term234 s).
Proof. exact (@lem5154149 (s = (@EMPTY real))). Qed.
Lemma lem5154151 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (EQ_MP (@lem5154150 s) (@lem5154147 x s a h1)). Qed.
Lemma lem5154157 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5154158 (_67297 : real -> Prop) : (term301 _67297) = (term367 _67297).
Proof. exact (@lem5154157 (_67297 = (@EMPTY real)) (term299 _67297) (term252 _67297)). Qed.
Lemma lem5154174 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5154175 (_67297 : real -> Prop) : (term368 _67297) = (term369 _67297).
Proof. exact (@lem5154174 (term252 _67297) (term299 _67297)). Qed.
Lemma lem5154181 (_67297 : real -> Prop) : (term313 _67297) = (term313 _67297).
Proof. exact (eq_refl (term313 _67297)). Qed.
Lemma lem5154182 (_67297 : real -> Prop) : (term367 _67297) = (term370 _67297).
Proof. exact (MK_COMB (@lem5154181 _67297) (@lem5154175 _67297)). Qed.
Lemma lem5154193 (_67297 : real -> Prop) : (term301 _67297) = (term370 _67297).
Proof. exact (TRANS (@lem5154158 _67297) (@lem5154182 _67297)). Qed.
Lemma lem5154194 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5154195 (_67297 : real -> Prop) : (term371 _67297) = (term372 _67297).
Proof. exact (MK_COMB (@lem5154194) (@lem5154193 _67297)). Qed.
Lemma lem5154209 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5154210 (_67297 : real -> Prop) : (term232 _67297) = (term373 _67297).
Proof. exact (@lem5154209 (_67297 = (@EMPTY real)) (term299 _67297)). Qed.
Lemma lem5154218 (_67297 : real -> Prop) : (term374 _67297) = (term374 _67297).
Proof. exact (eq_refl (term374 _67297)). Qed.
Lemma lem5154219 (_67297 : real -> Prop) : (term375 _67297) = (term376 _67297).
Proof. exact (MK_COMB (@lem5154218 _67297) (@lem5154210 _67297)). Qed.
Lemma lem5154223 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5154224 (_67297 : real -> Prop) : (term376 _67297) = (term370 _67297).
Proof. exact (@lem5154223 (_67297 = (@EMPTY real)) (term252 _67297) (term299 _67297)). Qed.
Lemma lem5154242 (_67297 : real -> Prop) : (term375 _67297) = (term370 _67297).
Proof. exact (TRANS (@lem5154219 _67297) (@lem5154224 _67297)). Qed.
Lemma lem5154243 (_67297 : real -> Prop) : ((term301 _67297) = (term375 _67297)) = ((term370 _67297) = (term370 _67297)).
Proof. exact (MK_COMB (@lem5154195 _67297) (@lem5154242 _67297)). Qed.
Lemma lem5154245 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5154246 (x : Prop) : (x = x) = True.
Proof. exact (@lem5154245 Prop x). Qed.
Lemma lem5154247 (_67297 : real -> Prop) : ((term370 _67297) = (term370 _67297)) = True.
Proof. exact (@lem5154246 (term370 _67297)). Qed.
Lemma lem5154248 (_67297 : real -> Prop) : ((term301 _67297) = (term375 _67297)) = True.
Proof. exact (TRANS (@lem5154243 _67297) (@lem5154247 _67297)). Qed.
Lemma lem5154249 (_67297 : real -> Prop) : True = ((term301 _67297) = (term375 _67297)).
Proof. exact (SYM (@lem5154248 _67297)). Qed.
Lemma lem5154250 (_67297 : real -> Prop) : (term301 _67297) = (term375 _67297).
Proof. exact (EQ_MP (@lem5154249 _67297) (@lem0)). Qed.
Lemma lem5154251 (_67297 : real -> Prop) (h1 : term17) : term375 _67297.
Proof. exact (EQ_MP (@lem5154250 _67297) (@lem5153615 _67297 h1)). Qed.
Lemma lem5154253 (b : Prop) (a : Prop) : (a \/ b) = (term323 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5154254 (_67297 : real -> Prop) : (term375 _67297) = (term377 _67297).
Proof. exact (@lem5154253 (term232 _67297) (term252 _67297)). Qed.
Lemma lem5154256 (a : Prop) (b : Prop) : (term325 a b) = (term326 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5154257 (_67297 : real -> Prop) : (term378 _67297) = (term379 _67297).
Proof. exact (@lem5154256 (term299 _67297) (_67297 = (@EMPTY real))). Qed.
Lemma lem5154259 (a : Prop) : (term330 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5154260 (_67297 : real -> Prop) : (term331 _67297) = (@FINITE real _67297).
Proof. exact (@lem5154259 (@FINITE real _67297)). Qed.
Lemma lem5154261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5154262 (_67297 : real -> Prop) : (term332 _67297) = (term333 _67297).
Proof. exact (MK_COMB (@lem5154261) (@lem5154260 _67297)). Qed.
Lemma lem5154263 (_67297 : real -> Prop) : (term234 _67297) = (term234 _67297).
Proof. exact (eq_refl (term234 _67297)). Qed.
Lemma lem5154264 (_67297 : real -> Prop) : (term379 _67297) = (term76 _67297).
Proof. exact (MK_COMB (@lem5154262 _67297) (@lem5154263 _67297)). Qed.
Lemma lem5154265 (_67297 : real -> Prop) : (term378 _67297) = (term76 _67297).
Proof. exact (TRANS (@lem5154257 _67297) (@lem5154264 _67297)). Qed.
Lemma lem5154266 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5154267 (_67297 : real -> Prop) : (term380 _67297) = (term28 _67297).
Proof. exact (MK_COMB (@lem5154266) (@lem5154265 _67297)). Qed.
Lemma lem5154268 (_67297 : real -> Prop) : (term252 _67297) = (term252 _67297).
Proof. exact (eq_refl (term252 _67297)). Qed.
Lemma lem5154269 (_67297 : real -> Prop) : (term377 _67297) = (term381 _67297).
Proof. exact (MK_COMB (@lem5154267 _67297) (@lem5154268 _67297)). Qed.
Lemma lem5154270 (_67297 : real -> Prop) : (term375 _67297) = (term381 _67297).
Proof. exact (TRANS (@lem5154254 _67297) (@lem5154269 _67297)). Qed.
Lemma lem5154272 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term76 s.
Proof. exact (conj (@lem5154144 x s a h1) (@lem5154151 x s a h1)). Qed.
Lemma lem5154274 (_67297 : real -> Prop) (h1 : term17) : term381 _67297.
Proof. exact (EQ_MP (@lem5154270 _67297) (@lem5154251 _67297 h1)). Qed.
Lemma lem5154275 (s : real -> Prop) (h1 : term17) : term381 s.
Proof. exact (@lem5154274 s h1). Qed.
Lemma lem5154278 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term208 x s a) : term252 s.
Proof. exact (@lem5154275 s h1 (@lem5154272 x s a h2)). Qed.
Lemma lem5154279 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term208 x s a) : term382 s.
Proof. exact (fun h0 : term383 s => @lem5154278 x s a h1 h2). Qed.
Lemma lem5154281 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5154282 (s : real -> Prop) : (term382 s) = (term252 s).
Proof. exact (@lem5154281 (term252 s)). Qed.
Lemma lem5154283 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term208 x s a) : term252 s.
Proof. exact (EQ_MP (@lem5154282 s) (@lem5154279 x s a h1 h2)). Qed.
Lemma lem5154289 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5154290 (a : real) (_67299 : real) (s : real -> Prop) : (term49 s _67299 a) = (term384 a _67299 s).
Proof. exact (@lem5154289 (real_lt _67299 a) (term307 _67299 s)). Qed.
Lemma lem5154296 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5154297 (a : real) (_67299 : real) (s : real -> Prop) : (term385 s _67299 a) = (term386 a _67299 s).
Proof. exact (MK_COMB (@lem5154296) (@lem5154290 a _67299 s)). Qed.
Lemma lem5154303 (a : real) (_67299 : real) (s : real -> Prop) : (term384 a _67299 s) = (term384 a _67299 s).
Proof. exact (eq_refl (term384 a _67299 s)). Qed.
Lemma lem5154304 (a : real) (_67299 : real) (s : real -> Prop) : ((term49 s _67299 a) = (term384 a _67299 s)) = ((term384 a _67299 s) = (term384 a _67299 s)).
Proof. exact (MK_COMB (@lem5154297 a _67299 s) (@lem5154303 a _67299 s)). Qed.
Lemma lem5154306 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5154307 (x : Prop) : (x = x) = True.
Proof. exact (@lem5154306 Prop x). Qed.
Lemma lem5154308 (a : real) (_67299 : real) (s : real -> Prop) : ((term384 a _67299 s) = (term384 a _67299 s)) = True.
Proof. exact (@lem5154307 (term384 a _67299 s)). Qed.
Lemma lem5154309 (a : real) (_67299 : real) (s : real -> Prop) : ((term49 s _67299 a) = (term384 a _67299 s)) = True.
Proof. exact (TRANS (@lem5154304 a _67299 s) (@lem5154308 a _67299 s)). Qed.
Lemma lem5154310 (a : real) (_67299 : real) (s : real -> Prop) : True = ((term49 s _67299 a) = (term384 a _67299 s)).
Proof. exact (SYM (@lem5154309 a _67299 s)). Qed.
Lemma lem5154311 (a : real) (_67299 : real) (s : real -> Prop) : (term49 s _67299 a) = (term384 a _67299 s).
Proof. exact (EQ_MP (@lem5154310 a _67299 s) (@lem0)). Qed.
Lemma lem5154312 (_67299 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term384 a _67299 s.
Proof. exact (EQ_MP (@lem5154311 a _67299 s) (@lem5153603 _67299 s a h1)). Qed.
Lemma lem5154314 (b : Prop) (a : Prop) : (a \/ b) = (term323 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5154315 (s : real -> Prop) (_67299 : real) (a : real) : (term384 a _67299 s) = (term387 s _67299 a).
Proof. exact (@lem5154314 (term307 _67299 s) (real_lt _67299 a)). Qed.
Lemma lem5154317 (a : Prop) : (term330 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5154318 (_67299 : real) (s : real -> Prop) : (term336 _67299 s) = (@IN real _67299 s).
Proof. exact (@lem5154317 (@IN real _67299 s)). Qed.
Lemma lem5154319 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5154320 (_67299 : real) (s : real -> Prop) : (term388 _67299 s) = (term389 _67299 s).
Proof. exact (MK_COMB (@lem5154319) (@lem5154318 _67299 s)). Qed.
Lemma lem5154321 (_67299 : real) (a : real) : (real_lt _67299 a) = (real_lt _67299 a).
Proof. exact (eq_refl (real_lt _67299 a)). Qed.
Lemma lem5154322 (s : real -> Prop) (_67299 : real) (a : real) : (term387 s _67299 a) = (term38 s _67299 a).
Proof. exact (MK_COMB (@lem5154320 _67299 s) (@lem5154321 _67299 a)). Qed.
Lemma lem5154323 (s : real -> Prop) (_67299 : real) (a : real) : (term384 a _67299 s) = (term38 s _67299 a).
Proof. exact (TRANS (@lem5154315 s _67299 a) (@lem5154322 s _67299 a)). Qed.
Lemma lem5154326 (_67299 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term38 s _67299 a.
Proof. exact (EQ_MP (@lem5154323 s _67299 a) (@lem5154312 _67299 s a h1)). Qed.
Lemma lem5154327 (s : real -> Prop) (a : real) (h1 : term63 s a) : term390 s a.
Proof. exact (@lem5154326 (sup s) s a h1). Qed.
Lemma lem5154330 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term42 s a.
Proof. exact (@lem5154327 s a h2 (@lem5154283 x s a h1 h3)). Qed.
Lemma lem5154331 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term345 s a.
Proof. exact (fun h0 : term300 s a => @lem5154330 x s a h1 h2 h3). Qed.
Lemma lem5154333 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5154334 (s : real -> Prop) (a : real) : (term345 s a) = (term42 s a).
Proof. exact (@lem5154333 (term42 s a)). Qed.
Lemma lem5154335 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term42 s a.
Proof. exact (EQ_MP (@lem5154334 s a) (@lem5154331 x s a h1 h2 h3)). Qed.
Lemma lem5154338 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5154340 (s : real -> Prop) (a : real) : (term300 s a) = (term391 s a).
Proof. exact (@lem5154338 (term42 s a)). Qed.
Lemma lem5154343 (s : real -> Prop) (a : real) (h1 : term63 s a) : term391 s a.
Proof. exact (EQ_MP (@lem5154340 s a) (@lem5153597 s a h1)). Qed.
Lemma lem5154346 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : False.
Proof. exact (@lem5154343 s a h2 (@lem5154335 x s a h1 h2 h3)). Qed.
Lemma lem5154347 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term366.
Proof. exact (fun h0 : ~ False => @lem5154346 x s a h1 h2 h3). Qed.
Lemma lem5154349 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5154350 : term366 = False.
Proof. exact (@lem5154349 False). Qed.
Lemma lem5154351 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : False.
Proof. exact (EQ_MP (@lem5154350) (@lem5154347 x s a h1 h2 h3)). Qed.
Lemma lem5154352 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) : False.
Proof. exact (or_elim (@lem5153220 x s a h3) (fun h0 : term143 s x a => @lem5154056 s x a h1 h2 h3 h0) (fun h0 : term63 s a => @lem5154351 x s a h1 h0 h3)). Qed.
Lemma lem5154353 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) : (term208 x s a) = False.
Proof. exact (prop_ext (fun h4 : term208 x s a => @lem5154352 x s a h1 h2 h3) (fun h4 : False => @lem5153219 x s a h3)). Qed.
Lemma lem5154354 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) : False.
Proof. exact (EQ_MP (@lem5154353 x s a h1 h2 h3) (@lem5153219 x s a h3)). Qed.
Lemma lem5154355 (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term211 s a) : False.
Proof. exact (ex_elim (@lem5153058 s a h3) (fun x : real => fun h0 : term210 s a x => @lem5154354 x s a h1 h2 h0)). Qed.
Lemma lem5154356 (s : real -> Prop) (h1 : term17) (h2 : term37) (h3 : term213 s) : False.
Proof. exact (ex_elim (@lem5153057 s h3) (fun a : real => fun h0 : term212 s a => @lem5154355 s a h1 h2 h0)). Qed.
Lemma lem5154357 (h1 : term17) (h2 : term37) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5152841 h3) (fun s : real -> Prop => fun h0 : term214 s => @lem5154356 s h1 h2 h0)). Qed.
Lemma lem5154358 (h1 : term37) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem5154357 h0 h1 h2). Qed.
Lemma lem5154359 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem5154360 (h1 : term37) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem5154359) (@lem5154358 h1 h2)). Qed.
Lemma lem5154361 (h1 : term10) : term20.
Proof. exact (fun h0 : term37 => @lem5154360 h0 h1). Qed.
Lemma lem5154362 : term22.
Proof. exact (fun h0 : term10 => @lem5154361 h0). Qed.
Lemma lem5154363 : term11.
Proof. exact (EQ_MP (@lem5152335) (@lem5154362)). Qed.
Lemma lem5154365 : term11.
Proof. exact (@lem5152111 (@lem5154363)). Qed.
Lemma lem5154366 (h1 : term10) : term19.
Proof. exact (@lem5154365 (@lem5152096 h1)). Qed.
Lemma lem5154367 (h1 : term10) : term15.
Proof. exact (@lem5154366 h1 (@lem1371386)). Qed.
Lemma lem5154368 (h1 : term10) : False.
Proof. exact (@lem5154367 h1 (@lem5145274)). Qed.
Lemma lem5154369 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem5154368 h1) (fun h2 : False => @lem5152096 h1)). Qed.
Lemma lem5154370 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem5154369 h1) (@lem5152096 h1)). Qed.
Lemma lem5154371 : term9.
Proof. exact (fun h0 : term10 => @lem5154370 h0). Qed.
Lemma lem5154372 : term8.
Proof. exact (EQ_MP (@lem5152095) (@lem5154371)). Qed.
