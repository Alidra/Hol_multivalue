Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7689527_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm7673035_spec.
Lemma lem7673124 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7673125 {A B : Type'} : (term1 A B) = (term2 A B).
Proof. exact (@lem7673124 (term1 A B)). Qed.
Lemma lem7673126 {A B : Type'} : (term2 A B) = (term1 A B).
Proof. exact (SYM (@lem7673125 A B)). Qed.
Lemma lem7673127 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (h1). Qed.
Lemma lem7673128 {A B : Type'} : term4 A B.
Proof. exact (@lem7673035 A B). Qed.
Lemma lem7673131 {A : Type'} : term5 A.
Proof. exact (@lem7673035 A A). Qed.
Lemma lem7673134 {B : Type'} : term5 B.
Proof. exact (@lem7673035 B B). Qed.
Lemma lem7673140 {A B : Type'} (h1 : term6 A B) : term6 A B.
Proof. exact (h1). Qed.
Lemma lem7673141 {A B : Type'} : term7 A B.
Proof. exact (fun h0 : term6 A B => @lem7673140 A B h0). Qed.
Lemma lem7673142 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (h1). Qed.
Lemma lem7673143 {A B : Type'} (h1 : term6 A B) : term6 A B.
Proof. exact (h1). Qed.
Lemma lem7673144 {A B : Type'} (h1 : term6 A B) (h2 : term7 A B) : term6 A B.
Proof. exact (@lem7673142 A B h2 (@lem7673143 A B h1)). Qed.
Lemma lem7673145 {A B : Type'} (h1 : term6 A B) : term8 A B.
Proof. exact (fun h0 : term7 A B => @lem7673144 A B h1 h0). Qed.
Lemma lem7673146 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (h1). Qed.
Lemma lem7673147 {A B : Type'} (h1 : term6 A B) (h2 : term7 A B) : term6 A B.
Proof. exact (@lem7673145 A B h1 (@lem7673146 A B h2)). Qed.
Lemma lem7673148 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (fun h0 : term6 A B => @lem7673147 A B h0 h1). Qed.
Lemma lem7673149 {A B : Type'} : term9 A B.
Proof. exact (fun h0 : term7 A B => @lem7673148 A B h0). Qed.
Lemma lem7673152 {A B : Type'} : term7 A B.
Proof. exact (@lem7673149 A B (@lem7673141 A B)). Qed.
Lemma lem7673153 {A B : Type'} : term7 A B.
Proof. exact (@lem7673152 A B). Qed.
Lemma lem7673235 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7673236 {B : Type'} : (term10 B) = (term11 B).
Proof. exact (@lem7673235 (term5 B)). Qed.
Lemma lem7673247 {A B : Type'} : (term12 A B) = (term12 A B).
Proof. exact (eq_refl (term12 A B)). Qed.
Lemma lem7673248 {A B : Type'} : (term13 A B) = (term14 A B).
Proof. exact (MK_COMB (@lem7673247 A B) (@lem7673236 B)). Qed.
Lemma lem7673251 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (eq_refl (term15 A)). Qed.
Lemma lem7673252 {A B : Type'} : (term16 A B) = (term17 A B).
Proof. exact (MK_COMB (@lem7673251 A) (@lem7673248 A B)). Qed.
Lemma lem7673255 {A B : Type'} : (term18 A B) = (term18 A B).
Proof. exact (eq_refl (term18 A B)). Qed.
Lemma lem7673262 {A B : Type'} : (term6 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem7673255 A B) (@lem7673252 A B)). Qed.
Lemma lem7673268 {A B : Type'} (h1 : (term20 A B) = False) : (term20 A B) = False.
Proof. exact (h1). Qed.
Lemma lem7673269 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7673270 {A B : Type'} (h1 : (term20 A B) = False) : (term21 A B) = (@COND nat False).
Proof. exact (MK_COMB (@lem7673269) (@lem7673268 A B h1)). Qed.
Lemma lem7673271 {A B : Type'} : (term22 A B) = (term22 A B).
Proof. exact (eq_refl (term22 A B)). Qed.
Lemma lem7673272 {A B : Type'} (h1 : (term20 A B) = False) : (term23 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem7673270 A B h1) (@lem7673271 A B)). Qed.
Lemma lem7673273 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7673274 {A B : Type'} (h1 : (term20 A B) = False) : (term26 A B) = (term27 A B).
Proof. exact (MK_COMB (@lem7673272 A B h1) (@lem7673273)). Qed.
Lemma lem7673276 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7673277 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7673276 nat t1 t2). Qed.
Lemma lem7673278 {A B : Type'} : (term27 A B) = term25.
Proof. exact (@lem7673277 (term22 A B) term25). Qed.
Lemma lem7673279 {A B : Type'} (h1 : (term20 A B) = False) : (term26 A B) = term25.
Proof. exact (TRANS (@lem7673274 A B h1) (@lem7673278 A B)). Qed.
Lemma lem7673280 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7673281 {A B : Type'} (h1 : (term20 A B) = False) : (term29 A B) = term30.
Proof. exact (MK_COMB (@lem7673280) (@lem7673279 A B h1)). Qed.
Lemma lem7673282 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem7673283 {A B : Type'} (x : nat) (h1 : (term20 A B) = False) : (term31 A B x) = (term32 x).
Proof. exact (MK_COMB (@lem7673282 x) (@lem7673281 A B h1)). Qed.
Lemma lem7673284 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term33 A B x x') = (term33 A B x x').
Proof. exact (eq_refl (term33 A B x x')). Qed.
Lemma lem7673285 {A B : Type'} (x : finite_diff A B) (x' : nat) (h1 : (term20 A B) = False) : (term34 A B x x') = (term35 A B x x').
Proof. exact (MK_COMB (@lem7673284 A B x x') (@lem7673283 A B x' h1)). Qed.
Lemma lem7673288 {A B : Type'} (x : finite_diff A B) (h1 : (term20 A B) = False) : (term36 A B x) = (term37 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7673285 A B x x' h1)). Qed.
Lemma lem7673289 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7673290 {A B : Type'} (x : finite_diff A B) (h1 : (term20 A B) = False) : (term38 A B x) = (term39 A B x).
Proof. exact (MK_COMB (@lem7673289) (@lem7673288 A B x h1)). Qed.
Lemma lem7673295 {A B : Type'} (h1 : (term20 A B) = False) : (term40 A B) = (term41 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7673290 A B x h1)). Qed.
Lemma lem7673296 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7673297 {A B : Type'} (h1 : (term20 A B) = False) : (term1 A B) = (term42 A B).
Proof. exact (MK_COMB (@lem7673296 A B) (@lem7673295 A B h1)). Qed.
Lemma lem7673302 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7673303 {A B : Type'} (h1 : (term20 A B) = False) : (term3 A B) = (term43 A B).
Proof. exact (MK_COMB (@lem7673302) (@lem7673297 A B h1)). Qed.
Lemma lem7673304 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7673305 {A B : Type'} (h1 : (term20 A B) = False) : (term18 A B) = (term44 A B).
Proof. exact (MK_COMB (@lem7673304) (@lem7673303 A B h1)). Qed.
Lemma lem7673332 {A B : Type'} (h1 : (term20 A B) = False) : (term20 A B) = False.
Proof. exact (h1). Qed.
Lemma lem7673333 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7673334 {A B : Type'} (h1 : (term20 A B) = False) : (term21 A B) = (@COND nat False).
Proof. exact (MK_COMB (@lem7673333) (@lem7673332 A B h1)). Qed.
Lemma lem7673335 {A B : Type'} : (term22 A B) = (term22 A B).
Proof. exact (eq_refl (term22 A B)). Qed.
Lemma lem7673336 {A B : Type'} (h1 : (term20 A B) = False) : (term23 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem7673334 A B h1) (@lem7673335 A B)). Qed.
Lemma lem7673337 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7673338 {A B : Type'} (h1 : (term20 A B) = False) : (term26 A B) = (term27 A B).
Proof. exact (MK_COMB (@lem7673336 A B h1) (@lem7673337)). Qed.
Lemma lem7673340 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7673341 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7673340 nat t1 t2). Qed.
Lemma lem7673342 {A B : Type'} : (term27 A B) = term25.
Proof. exact (@lem7673341 (term22 A B) term25). Qed.
Lemma lem7673343 {A B : Type'} (h1 : (term20 A B) = False) : (term26 A B) = term25.
Proof. exact (TRANS (@lem7673338 A B h1) (@lem7673342 A B)). Qed.
Lemma lem7673344 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7673345 {A B : Type'} (h1 : (term20 A B) = False) : (term29 A B) = term30.
Proof. exact (MK_COMB (@lem7673344) (@lem7673343 A B h1)). Qed.
Lemma lem7673346 (r : nat) : (@IN nat r) = (@IN nat r).
Proof. exact (eq_refl (@IN nat r)). Qed.
Lemma lem7673347 {A B : Type'} (r : nat) (h1 : (term20 A B) = False) : (term31 A B r) = (term32 r).
Proof. exact (MK_COMB (@lem7673346 r) (@lem7673345 A B h1)). Qed.
Lemma lem7673348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7673349 {A B : Type'} (r : nat) (h1 : (term20 A B) = False) : (term45 A B r) = (term46 r).
Proof. exact (MK_COMB (@lem7673348) (@lem7673347 A B r h1)). Qed.
Lemma lem7673352 {A B : Type'} (r : nat) : ((term47 A B r) = r) = ((term47 A B r) = r).
Proof. exact (eq_refl ((term47 A B r) = r)). Qed.
Lemma lem7673353 {A B : Type'} (r : nat) (h1 : (term20 A B) = False) : ((term31 A B r) = ((term47 A B r) = r)) = ((term32 r) = ((term47 A B r) = r)).
Proof. exact (MK_COMB (@lem7673349 A B r h1) (@lem7673352 A B r)). Qed.
Lemma lem7673356 {A B : Type'} (h1 : (term20 A B) = False) : (term48 A B) = (term49 A B).
Proof. exact (fun_ext (fun r : nat => @lem7673353 A B r h1)). Qed.
Lemma lem7673357 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7673358 {A B : Type'} (h1 : (term20 A B) = False) : (term50 A B) = (term51 A B).
Proof. exact (MK_COMB (@lem7673357) (@lem7673356 A B h1)). Qed.
Lemma lem7673363 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (eq_refl (term52 A B)). Qed.
Lemma lem7673364 {A B : Type'} (h1 : (term20 A B) = False) : (term4 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem7673363 A B) (@lem7673358 A B h1)). Qed.
Lemma lem7673367 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7673368 {A B : Type'} (h1 : (term20 A B) = False) : (term12 A B) = (term54 A B).
Proof. exact (MK_COMB (@lem7673367) (@lem7673364 A B h1)). Qed.
Lemma lem7673388 {B : Type'} : (term11 B) = (term11 B).
Proof. exact (eq_refl (term11 B)). Qed.
Lemma lem7673389 {A B : Type'} (h1 : (term20 A B) = False) : (term14 A B) = (term55 A B).
Proof. exact (MK_COMB (@lem7673368 A B h1) (@lem7673388 B)). Qed.
Lemma lem7673392 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (eq_refl (term15 A)). Qed.
Lemma lem7673393 {A B : Type'} (h1 : (term20 A B) = False) : (term17 A B) = (term56 A B).
Proof. exact (MK_COMB (@lem7673392 A) (@lem7673389 A B h1)). Qed.
Lemma lem7673396 {A B : Type'} (h1 : (term20 A B) = False) : (term19 A B) = (term57 A B).
Proof. exact (MK_COMB (@lem7673305 A B h1) (@lem7673393 A B h1)). Qed.
Lemma lem7673399 {A B : Type'} : term58 A B.
Proof. exact (fun h0 : (term20 A B) = False => @lem7673396 A B h0). Qed.
Lemma lem7673403 {A B : Type'} (h1 : (term20 A B) = True) : (term20 A B) = True.
Proof. exact (h1). Qed.
Lemma lem7673404 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7673405 {A B : Type'} (h1 : (term20 A B) = True) : (term21 A B) = (@COND nat True).
Proof. exact (MK_COMB (@lem7673404) (@lem7673403 A B h1)). Qed.
Lemma lem7673406 {A B : Type'} : (term22 A B) = (term22 A B).
Proof. exact (eq_refl (term22 A B)). Qed.
Lemma lem7673407 {A B : Type'} (h1 : (term20 A B) = True) : (term23 A B) = (term59 A B).
Proof. exact (MK_COMB (@lem7673405 A B h1) (@lem7673406 A B)). Qed.
Lemma lem7673408 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7673409 {A B : Type'} (h1 : (term20 A B) = True) : (term26 A B) = (term60 A B).
Proof. exact (MK_COMB (@lem7673407 A B h1) (@lem7673408)). Qed.
Lemma lem7673411 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7673412 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7673411 nat t2 t1). Qed.
Lemma lem7673413 {A B : Type'} : (term60 A B) = (term22 A B).
Proof. exact (@lem7673412 term25 (term22 A B)). Qed.
Lemma lem7673414 {A B : Type'} (h1 : (term20 A B) = True) : (term26 A B) = (term22 A B).
Proof. exact (TRANS (@lem7673409 A B h1) (@lem7673413 A B)). Qed.
Lemma lem7673415 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7673416 {A B : Type'} (h1 : (term20 A B) = True) : (term29 A B) = (term61 A B).
Proof. exact (MK_COMB (@lem7673415) (@lem7673414 A B h1)). Qed.
Lemma lem7673417 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem7673418 {A B : Type'} (x : nat) (h1 : (term20 A B) = True) : (term31 A B x) = (term62 A B x).
Proof. exact (MK_COMB (@lem7673417 x) (@lem7673416 A B h1)). Qed.
Lemma lem7673419 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term33 A B x x') = (term33 A B x x').
Proof. exact (eq_refl (term33 A B x x')). Qed.
Lemma lem7673420 {A B : Type'} (x : finite_diff A B) (x' : nat) (h1 : (term20 A B) = True) : (term34 A B x x') = (term63 A B x x').
Proof. exact (MK_COMB (@lem7673419 A B x x') (@lem7673418 A B x' h1)). Qed.
Lemma lem7673423 {A B : Type'} (x : finite_diff A B) (h1 : (term20 A B) = True) : (term36 A B x) = (term64 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7673420 A B x x' h1)). Qed.
Lemma lem7673424 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7673425 {A B : Type'} (x : finite_diff A B) (h1 : (term20 A B) = True) : (term38 A B x) = (term65 A B x).
Proof. exact (MK_COMB (@lem7673424) (@lem7673423 A B x h1)). Qed.
Lemma lem7673430 {A B : Type'} (h1 : (term20 A B) = True) : (term40 A B) = (term66 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7673425 A B x h1)). Qed.
Lemma lem7673431 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7673432 {A B : Type'} (h1 : (term20 A B) = True) : (term1 A B) = (term67 A B).
Proof. exact (MK_COMB (@lem7673431 A B) (@lem7673430 A B h1)). Qed.
Lemma lem7673437 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7673438 {A B : Type'} (h1 : (term20 A B) = True) : (term3 A B) = (term68 A B).
Proof. exact (MK_COMB (@lem7673437) (@lem7673432 A B h1)). Qed.
Lemma lem7673439 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7673440 {A B : Type'} (h1 : (term20 A B) = True) : (term18 A B) = (term69 A B).
Proof. exact (MK_COMB (@lem7673439) (@lem7673438 A B h1)). Qed.
Lemma lem7673467 {A B : Type'} (h1 : (term20 A B) = True) : (term20 A B) = True.
Proof. exact (h1). Qed.
Lemma lem7673468 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7673469 {A B : Type'} (h1 : (term20 A B) = True) : (term21 A B) = (@COND nat True).
Proof. exact (MK_COMB (@lem7673468) (@lem7673467 A B h1)). Qed.
Lemma lem7673470 {A B : Type'} : (term22 A B) = (term22 A B).
Proof. exact (eq_refl (term22 A B)). Qed.
Lemma lem7673471 {A B : Type'} (h1 : (term20 A B) = True) : (term23 A B) = (term59 A B).
Proof. exact (MK_COMB (@lem7673469 A B h1) (@lem7673470 A B)). Qed.
Lemma lem7673472 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7673473 {A B : Type'} (h1 : (term20 A B) = True) : (term26 A B) = (term60 A B).
Proof. exact (MK_COMB (@lem7673471 A B h1) (@lem7673472)). Qed.
Lemma lem7673475 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7673476 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7673475 nat t2 t1). Qed.
Lemma lem7673477 {A B : Type'} : (term60 A B) = (term22 A B).
Proof. exact (@lem7673476 term25 (term22 A B)). Qed.
Lemma lem7673478 {A B : Type'} (h1 : (term20 A B) = True) : (term26 A B) = (term22 A B).
Proof. exact (TRANS (@lem7673473 A B h1) (@lem7673477 A B)). Qed.
Lemma lem7673479 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7673480 {A B : Type'} (h1 : (term20 A B) = True) : (term29 A B) = (term61 A B).
Proof. exact (MK_COMB (@lem7673479) (@lem7673478 A B h1)). Qed.
Lemma lem7673481 (r : nat) : (@IN nat r) = (@IN nat r).
Proof. exact (eq_refl (@IN nat r)). Qed.
Lemma lem7673482 {A B : Type'} (r : nat) (h1 : (term20 A B) = True) : (term31 A B r) = (term62 A B r).
Proof. exact (MK_COMB (@lem7673481 r) (@lem7673480 A B h1)). Qed.
Lemma lem7673483 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7673484 {A B : Type'} (r : nat) (h1 : (term20 A B) = True) : (term45 A B r) = (term70 A B r).
Proof. exact (MK_COMB (@lem7673483) (@lem7673482 A B r h1)). Qed.
Lemma lem7673487 {A B : Type'} (r : nat) : ((term47 A B r) = r) = ((term47 A B r) = r).
Proof. exact (eq_refl ((term47 A B r) = r)). Qed.
Lemma lem7673488 {A B : Type'} (r : nat) (h1 : (term20 A B) = True) : ((term31 A B r) = ((term47 A B r) = r)) = ((term62 A B r) = ((term47 A B r) = r)).
Proof. exact (MK_COMB (@lem7673484 A B r h1) (@lem7673487 A B r)). Qed.
Lemma lem7673491 {A B : Type'} (h1 : (term20 A B) = True) : (term48 A B) = (term71 A B).
Proof. exact (fun_ext (fun r : nat => @lem7673488 A B r h1)). Qed.
Lemma lem7673492 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7673493 {A B : Type'} (h1 : (term20 A B) = True) : (term50 A B) = (term72 A B).
Proof. exact (MK_COMB (@lem7673492) (@lem7673491 A B h1)). Qed.
Lemma lem7673498 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (eq_refl (term52 A B)). Qed.
Lemma lem7673499 {A B : Type'} (h1 : (term20 A B) = True) : (term4 A B) = (term73 A B).
Proof. exact (MK_COMB (@lem7673498 A B) (@lem7673493 A B h1)). Qed.
Lemma lem7673502 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7673503 {A B : Type'} (h1 : (term20 A B) = True) : (term12 A B) = (term74 A B).
Proof. exact (MK_COMB (@lem7673502) (@lem7673499 A B h1)). Qed.
Lemma lem7673523 {B : Type'} : (term11 B) = (term11 B).
Proof. exact (eq_refl (term11 B)). Qed.
Lemma lem7673524 {A B : Type'} (h1 : (term20 A B) = True) : (term14 A B) = (term75 A B).
Proof. exact (MK_COMB (@lem7673503 A B h1) (@lem7673523 B)). Qed.
Lemma lem7673527 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (eq_refl (term15 A)). Qed.
Lemma lem7673528 {A B : Type'} (h1 : (term20 A B) = True) : (term17 A B) = (term76 A B).
Proof. exact (MK_COMB (@lem7673527 A) (@lem7673524 A B h1)). Qed.
Lemma lem7673531 {A B : Type'} (h1 : (term20 A B) = True) : (term19 A B) = (term77 A B).
Proof. exact (MK_COMB (@lem7673440 A B h1) (@lem7673528 A B h1)). Qed.
Lemma lem7673534 {A B : Type'} : term78 A B.
Proof. exact (fun h0 : (term20 A B) = True => @lem7673531 A B h0). Qed.
Lemma lem7673535 {A B : Type'} : term79 A B.
Proof. exact (conj (@lem7673399 A B) (@lem7673534 A B)). Qed.
Lemma lem7673537 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term80 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem7673538 {A B : Type'} : term81 A B.
Proof. exact (@lem7673537 (term19 A B) (term77 A B) (term20 A B) (term57 A B)). Qed.
Lemma lem7673553 {A B : Type'} : (term19 A B) = (term82 A B).
Proof. exact (@lem7673538 A B (@lem7673535 A B)). Qed.
Lemma lem7673578 {A : Type'} (h1 : (term83 A) = False) : (term83 A) = False.
Proof. exact (h1). Qed.
Lemma lem7673579 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7673580 {A : Type'} (h1 : (term83 A) = False) : (term84 A) = (@COND nat False).
Proof. exact (MK_COMB (@lem7673579) (@lem7673578 A h1)). Qed.
Lemma lem7673581 {A : Type'} : (term85 A) = (term85 A).
Proof. exact (eq_refl (term85 A)). Qed.
Lemma lem7673582 {A : Type'} (h1 : (term83 A) = False) : (term86 A) = (term87 A).
Proof. exact (MK_COMB (@lem7673580 A h1) (@lem7673581 A)). Qed.
Lemma lem7673583 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7673584 {A : Type'} (h1 : (term83 A) = False) : (term88 A) = (term89 A).
Proof. exact (MK_COMB (@lem7673582 A h1) (@lem7673583)). Qed.
Lemma lem7673586 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7673587 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7673586 nat t1 t2). Qed.
Lemma lem7673588 {A : Type'} : (term89 A) = term25.
Proof. exact (@lem7673587 (term85 A) term25). Qed.
Lemma lem7673589 {A : Type'} (h1 : (term83 A) = False) : (term88 A) = term25.
Proof. exact (TRANS (@lem7673584 A h1) (@lem7673588 A)). Qed.
Lemma lem7673590 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7673591 {A : Type'} (h1 : (term83 A) = False) : (term90 A) = term30.
Proof. exact (MK_COMB (@lem7673590) (@lem7673589 A h1)). Qed.
Lemma lem7673592 (r : nat) : (@IN nat r) = (@IN nat r).
Proof. exact (eq_refl (@IN nat r)). Qed.
Lemma lem7673593 {A : Type'} (r : nat) (h1 : (term83 A) = False) : (term91 A r) = (term32 r).
Proof. exact (MK_COMB (@lem7673592 r) (@lem7673591 A h1)). Qed.
Lemma lem7673594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7673595 {A : Type'} (r : nat) (h1 : (term83 A) = False) : (term92 A r) = (term46 r).
Proof. exact (MK_COMB (@lem7673594) (@lem7673593 A r h1)). Qed.
Lemma lem7673598 {A : Type'} (r : nat) : ((term93 A r) = r) = ((term93 A r) = r).
Proof. exact (eq_refl ((term93 A r) = r)). Qed.
Lemma lem7673599 {A : Type'} (r : nat) (h1 : (term83 A) = False) : ((term91 A r) = ((term93 A r) = r)) = ((term32 r) = ((term93 A r) = r)).
Proof. exact (MK_COMB (@lem7673595 A r h1) (@lem7673598 A r)). Qed.
Lemma lem7673602 {A : Type'} (h1 : (term83 A) = False) : (term94 A) = (term95 A).
Proof. exact (fun_ext (fun r : nat => @lem7673599 A r h1)). Qed.
Lemma lem7673603 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7673604 {A : Type'} (h1 : (term83 A) = False) : (term96 A) = (term97 A).
Proof. exact (MK_COMB (@lem7673603) (@lem7673602 A h1)). Qed.
Lemma lem7673609 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (eq_refl (term98 A)). Qed.
Lemma lem7673610 {A : Type'} (h1 : (term83 A) = False) : (term5 A) = (term99 A).
Proof. exact (MK_COMB (@lem7673609 A) (@lem7673604 A h1)). Qed.
Lemma lem7673613 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7673614 {A : Type'} (h1 : (term83 A) = False) : (term15 A) = (term100 A).
Proof. exact (MK_COMB (@lem7673613) (@lem7673610 A h1)). Qed.
Lemma lem7673652 {A B : Type'} : (term75 A B) = (term75 A B).
Proof. exact (eq_refl (term75 A B)). Qed.
Lemma lem7673653 {A B : Type'} (h1 : (term83 A) = False) : (term76 A B) = (term101 A B).
Proof. exact (MK_COMB (@lem7673614 A h1) (@lem7673652 A B)). Qed.
Lemma lem7673656 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (eq_refl (term69 A B)). Qed.
Lemma lem7673657 {A B : Type'} (h1 : (term83 A) = False) : (term77 A B) = (term102 A B).
Proof. exact (MK_COMB (@lem7673656 A B) (@lem7673653 A B h1)). Qed.
Lemma lem7673660 {A B : Type'} : (term103 A B) = (term103 A B).
Proof. exact (eq_refl (term103 A B)). Qed.
Lemma lem7673661 {A B : Type'} (h1 : (term83 A) = False) : (term104 A B) = (term105 A B).
Proof. exact (MK_COMB (@lem7673660 A B) (@lem7673657 A B h1)). Qed.
Lemma lem7673664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7673665 {A B : Type'} (h1 : (term83 A) = False) : (term106 A B) = (term107 A B).
Proof. exact (MK_COMB (@lem7673664) (@lem7673661 A B h1)). Qed.
Lemma lem7673688 {A : Type'} (h1 : (term83 A) = False) : (term83 A) = False.
Proof. exact (h1). Qed.
Lemma lem7673689 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7673690 {A : Type'} (h1 : (term83 A) = False) : (term84 A) = (@COND nat False).
Proof. exact (MK_COMB (@lem7673689) (@lem7673688 A h1)). Qed.
Lemma lem7673691 {A : Type'} : (term85 A) = (term85 A).
Proof. exact (eq_refl (term85 A)). Qed.
Lemma lem7673692 {A : Type'} (h1 : (term83 A) = False) : (term86 A) = (term87 A).
Proof. exact (MK_COMB (@lem7673690 A h1) (@lem7673691 A)). Qed.
Lemma lem7673693 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7673694 {A : Type'} (h1 : (term83 A) = False) : (term88 A) = (term89 A).
Proof. exact (MK_COMB (@lem7673692 A h1) (@lem7673693)). Qed.
Lemma lem7673696 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7673697 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7673696 nat t1 t2). Qed.
Lemma lem7673698 {A : Type'} : (term89 A) = term25.
Proof. exact (@lem7673697 (term85 A) term25). Qed.
Lemma lem7673699 {A : Type'} (h1 : (term83 A) = False) : (term88 A) = term25.
Proof. exact (TRANS (@lem7673694 A h1) (@lem7673698 A)). Qed.
Lemma lem7673700 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7673701 {A : Type'} (h1 : (term83 A) = False) : (term90 A) = term30.
Proof. exact (MK_COMB (@lem7673700) (@lem7673699 A h1)). Qed.
Lemma lem7673702 (r : nat) : (@IN nat r) = (@IN nat r).
Proof. exact (eq_refl (@IN nat r)). Qed.
Lemma lem7673703 {A : Type'} (r : nat) (h1 : (term83 A) = False) : (term91 A r) = (term32 r).
Proof. exact (MK_COMB (@lem7673702 r) (@lem7673701 A h1)). Qed.
Lemma lem7673704 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7673705 {A : Type'} (r : nat) (h1 : (term83 A) = False) : (term92 A r) = (term46 r).
Proof. exact (MK_COMB (@lem7673704) (@lem7673703 A r h1)). Qed.
Lemma lem7673708 {A : Type'} (r : nat) : ((term93 A r) = r) = ((term93 A r) = r).
Proof. exact (eq_refl ((term93 A r) = r)). Qed.
Lemma lem7673709 {A : Type'} (r : nat) (h1 : (term83 A) = False) : ((term91 A r) = ((term93 A r) = r)) = ((term32 r) = ((term93 A r) = r)).
Proof. exact (MK_COMB (@lem7673705 A r h1) (@lem7673708 A r)). Qed.
Lemma lem7673712 {A : Type'} (h1 : (term83 A) = False) : (term94 A) = (term95 A).
Proof. exact (fun_ext (fun r : nat => @lem7673709 A r h1)). Qed.
Lemma lem7673713 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7673714 {A : Type'} (h1 : (term83 A) = False) : (term96 A) = (term97 A).
Proof. exact (MK_COMB (@lem7673713) (@lem7673712 A h1)). Qed.
Lemma lem7673719 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (eq_refl (term98 A)). Qed.
Lemma lem7673720 {A : Type'} (h1 : (term83 A) = False) : (term5 A) = (term99 A).
Proof. exact (MK_COMB (@lem7673719 A) (@lem7673714 A h1)). Qed.
Lemma lem7673723 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7673724 {A : Type'} (h1 : (term83 A) = False) : (term15 A) = (term100 A).
Proof. exact (MK_COMB (@lem7673723) (@lem7673720 A h1)). Qed.
Lemma lem7673762 {A B : Type'} : (term55 A B) = (term55 A B).
Proof. exact (eq_refl (term55 A B)). Qed.
Lemma lem7673763 {A B : Type'} (h1 : (term83 A) = False) : (term56 A B) = (term108 A B).
Proof. exact (MK_COMB (@lem7673724 A h1) (@lem7673762 A B)). Qed.
Lemma lem7673766 {A B : Type'} : (term44 A B) = (term44 A B).
Proof. exact (eq_refl (term44 A B)). Qed.
Lemma lem7673767 {A B : Type'} (h1 : (term83 A) = False) : (term57 A B) = (term109 A B).
Proof. exact (MK_COMB (@lem7673766 A B) (@lem7673763 A B h1)). Qed.
Lemma lem7673770 {A B : Type'} : (term110 A B) = (term110 A B).
Proof. exact (eq_refl (term110 A B)). Qed.
Lemma lem7673771 {A B : Type'} (h1 : (term83 A) = False) : (term111 A B) = (term112 A B).
Proof. exact (MK_COMB (@lem7673770 A B) (@lem7673767 A B h1)). Qed.
Lemma lem7673774 {A B : Type'} (h1 : (term83 A) = False) : (term82 A B) = (term113 A B).
Proof. exact (MK_COMB (@lem7673665 A B h1) (@lem7673771 A B h1)). Qed.
Lemma lem7673777 {A B : Type'} : term114 A B.
Proof. exact (fun h0 : (term83 A) = False => @lem7673774 A B h0). Qed.
Lemma lem7673800 {A : Type'} (h1 : (term83 A) = True) : (term83 A) = True.
Proof. exact (h1). Qed.
Lemma lem7673801 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7673802 {A : Type'} (h1 : (term83 A) = True) : (term84 A) = (@COND nat True).
Proof. exact (MK_COMB (@lem7673801) (@lem7673800 A h1)). Qed.
Lemma lem7673803 {A : Type'} : (term85 A) = (term85 A).
Proof. exact (eq_refl (term85 A)). Qed.
Lemma lem7673804 {A : Type'} (h1 : (term83 A) = True) : (term86 A) = (term115 A).
Proof. exact (MK_COMB (@lem7673802 A h1) (@lem7673803 A)). Qed.
Lemma lem7673805 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7673806 {A : Type'} (h1 : (term83 A) = True) : (term88 A) = (term116 A).
Proof. exact (MK_COMB (@lem7673804 A h1) (@lem7673805)). Qed.
Lemma lem7673808 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7673809 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7673808 nat t2 t1). Qed.
Lemma lem7673810 {A : Type'} : (term116 A) = (term85 A).
Proof. exact (@lem7673809 term25 (term85 A)). Qed.
Lemma lem7673811 {A : Type'} (h1 : (term83 A) = True) : (term88 A) = (term85 A).
Proof. exact (TRANS (@lem7673806 A h1) (@lem7673810 A)). Qed.
Lemma lem7673812 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7673813 {A : Type'} (h1 : (term83 A) = True) : (term90 A) = (term117 A).
Proof. exact (MK_COMB (@lem7673812) (@lem7673811 A h1)). Qed.
Lemma lem7673814 (r : nat) : (@IN nat r) = (@IN nat r).
Proof. exact (eq_refl (@IN nat r)). Qed.
Lemma lem7673815 {A : Type'} (r : nat) (h1 : (term83 A) = True) : (term91 A r) = (term118 A r).
Proof. exact (MK_COMB (@lem7673814 r) (@lem7673813 A h1)). Qed.
Lemma lem7673816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7673817 {A : Type'} (r : nat) (h1 : (term83 A) = True) : (term92 A r) = (term119 A r).
Proof. exact (MK_COMB (@lem7673816) (@lem7673815 A r h1)). Qed.
Lemma lem7673820 {A : Type'} (r : nat) : ((term93 A r) = r) = ((term93 A r) = r).
Proof. exact (eq_refl ((term93 A r) = r)). Qed.
Lemma lem7673821 {A : Type'} (r : nat) (h1 : (term83 A) = True) : ((term91 A r) = ((term93 A r) = r)) = ((term118 A r) = ((term93 A r) = r)).
Proof. exact (MK_COMB (@lem7673817 A r h1) (@lem7673820 A r)). Qed.
Lemma lem7673824 {A : Type'} (h1 : (term83 A) = True) : (term94 A) = (term120 A).
Proof. exact (fun_ext (fun r : nat => @lem7673821 A r h1)). Qed.
Lemma lem7673825 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7673826 {A : Type'} (h1 : (term83 A) = True) : (term96 A) = (term121 A).
Proof. exact (MK_COMB (@lem7673825) (@lem7673824 A h1)). Qed.
Lemma lem7673831 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (eq_refl (term98 A)). Qed.
Lemma lem7673832 {A : Type'} (h1 : (term83 A) = True) : (term5 A) = (term122 A).
Proof. exact (MK_COMB (@lem7673831 A) (@lem7673826 A h1)). Qed.
Lemma lem7673835 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7673836 {A : Type'} (h1 : (term83 A) = True) : (term15 A) = (term123 A).
Proof. exact (MK_COMB (@lem7673835) (@lem7673832 A h1)). Qed.
Lemma lem7673874 {A B : Type'} : (term75 A B) = (term75 A B).
Proof. exact (eq_refl (term75 A B)). Qed.
Lemma lem7673875 {A B : Type'} (h1 : (term83 A) = True) : (term76 A B) = (term124 A B).
Proof. exact (MK_COMB (@lem7673836 A h1) (@lem7673874 A B)). Qed.
Lemma lem7673878 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (eq_refl (term69 A B)). Qed.
Lemma lem7673879 {A B : Type'} (h1 : (term83 A) = True) : (term77 A B) = (term125 A B).
Proof. exact (MK_COMB (@lem7673878 A B) (@lem7673875 A B h1)). Qed.
Lemma lem7673882 {A B : Type'} : (term103 A B) = (term103 A B).
Proof. exact (eq_refl (term103 A B)). Qed.
Lemma lem7673883 {A B : Type'} (h1 : (term83 A) = True) : (term104 A B) = (term126 A B).
Proof. exact (MK_COMB (@lem7673882 A B) (@lem7673879 A B h1)). Qed.
Lemma lem7673886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7673887 {A B : Type'} (h1 : (term83 A) = True) : (term106 A B) = (term127 A B).
Proof. exact (MK_COMB (@lem7673886) (@lem7673883 A B h1)). Qed.
Lemma lem7673910 {A : Type'} (h1 : (term83 A) = True) : (term83 A) = True.
Proof. exact (h1). Qed.
Lemma lem7673911 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7673912 {A : Type'} (h1 : (term83 A) = True) : (term84 A) = (@COND nat True).
Proof. exact (MK_COMB (@lem7673911) (@lem7673910 A h1)). Qed.
Lemma lem7673913 {A : Type'} : (term85 A) = (term85 A).
Proof. exact (eq_refl (term85 A)). Qed.
Lemma lem7673914 {A : Type'} (h1 : (term83 A) = True) : (term86 A) = (term115 A).
Proof. exact (MK_COMB (@lem7673912 A h1) (@lem7673913 A)). Qed.
Lemma lem7673915 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7673916 {A : Type'} (h1 : (term83 A) = True) : (term88 A) = (term116 A).
Proof. exact (MK_COMB (@lem7673914 A h1) (@lem7673915)). Qed.
Lemma lem7673918 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7673919 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7673918 nat t2 t1). Qed.
Lemma lem7673920 {A : Type'} : (term116 A) = (term85 A).
Proof. exact (@lem7673919 term25 (term85 A)). Qed.
Lemma lem7673921 {A : Type'} (h1 : (term83 A) = True) : (term88 A) = (term85 A).
Proof. exact (TRANS (@lem7673916 A h1) (@lem7673920 A)). Qed.
Lemma lem7673922 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7673923 {A : Type'} (h1 : (term83 A) = True) : (term90 A) = (term117 A).
Proof. exact (MK_COMB (@lem7673922) (@lem7673921 A h1)). Qed.
Lemma lem7673924 (r : nat) : (@IN nat r) = (@IN nat r).
Proof. exact (eq_refl (@IN nat r)). Qed.
Lemma lem7673925 {A : Type'} (r : nat) (h1 : (term83 A) = True) : (term91 A r) = (term118 A r).
Proof. exact (MK_COMB (@lem7673924 r) (@lem7673923 A h1)). Qed.
Lemma lem7673926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7673927 {A : Type'} (r : nat) (h1 : (term83 A) = True) : (term92 A r) = (term119 A r).
Proof. exact (MK_COMB (@lem7673926) (@lem7673925 A r h1)). Qed.
Lemma lem7673930 {A : Type'} (r : nat) : ((term93 A r) = r) = ((term93 A r) = r).
Proof. exact (eq_refl ((term93 A r) = r)). Qed.
Lemma lem7673931 {A : Type'} (r : nat) (h1 : (term83 A) = True) : ((term91 A r) = ((term93 A r) = r)) = ((term118 A r) = ((term93 A r) = r)).
Proof. exact (MK_COMB (@lem7673927 A r h1) (@lem7673930 A r)). Qed.
Lemma lem7673934 {A : Type'} (h1 : (term83 A) = True) : (term94 A) = (term120 A).
Proof. exact (fun_ext (fun r : nat => @lem7673931 A r h1)). Qed.
Lemma lem7673935 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7673936 {A : Type'} (h1 : (term83 A) = True) : (term96 A) = (term121 A).
Proof. exact (MK_COMB (@lem7673935) (@lem7673934 A h1)). Qed.
Lemma lem7673941 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (eq_refl (term98 A)). Qed.
Lemma lem7673942 {A : Type'} (h1 : (term83 A) = True) : (term5 A) = (term122 A).
Proof. exact (MK_COMB (@lem7673941 A) (@lem7673936 A h1)). Qed.
Lemma lem7673945 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7673946 {A : Type'} (h1 : (term83 A) = True) : (term15 A) = (term123 A).
Proof. exact (MK_COMB (@lem7673945) (@lem7673942 A h1)). Qed.
Lemma lem7673984 {A B : Type'} : (term55 A B) = (term55 A B).
Proof. exact (eq_refl (term55 A B)). Qed.
Lemma lem7673985 {A B : Type'} (h1 : (term83 A) = True) : (term56 A B) = (term128 A B).
Proof. exact (MK_COMB (@lem7673946 A h1) (@lem7673984 A B)). Qed.
Lemma lem7673988 {A B : Type'} : (term44 A B) = (term44 A B).
Proof. exact (eq_refl (term44 A B)). Qed.
Lemma lem7673989 {A B : Type'} (h1 : (term83 A) = True) : (term57 A B) = (term129 A B).
Proof. exact (MK_COMB (@lem7673988 A B) (@lem7673985 A B h1)). Qed.
Lemma lem7673992 {A B : Type'} : (term110 A B) = (term110 A B).
Proof. exact (eq_refl (term110 A B)). Qed.
Lemma lem7673993 {A B : Type'} (h1 : (term83 A) = True) : (term111 A B) = (term130 A B).
Proof. exact (MK_COMB (@lem7673992 A B) (@lem7673989 A B h1)). Qed.
Lemma lem7673996 {A B : Type'} (h1 : (term83 A) = True) : (term82 A B) = (term131 A B).
Proof. exact (MK_COMB (@lem7673887 A B h1) (@lem7673993 A B h1)). Qed.
Lemma lem7673999 {A B : Type'} : term132 A B.
Proof. exact (fun h0 : (term83 A) = True => @lem7673996 A B h0). Qed.
Lemma lem7674000 {A B : Type'} : term133 A B.
Proof. exact (conj (@lem7673777 A B) (@lem7673999 A B)). Qed.
Lemma lem7674002 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term80 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem7674003 {A B : Type'} : term134 A B.
Proof. exact (@lem7674002 (term82 A B) (term131 A B) (term83 A) (term113 A B)). Qed.
Lemma lem7674018 {A B : Type'} : (term82 A B) = (term135 A B).
Proof. exact (@lem7674003 A B (@lem7674000 A B)). Qed.
Lemma lem7674078 {B : Type'} (h1 : (term83 B) = False) : (term83 B) = False.
Proof. exact (h1). Qed.
Lemma lem7674079 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7674080 {B : Type'} (h1 : (term83 B) = False) : (term84 B) = (@COND nat False).
Proof. exact (MK_COMB (@lem7674079) (@lem7674078 B h1)). Qed.
Lemma lem7674081 {B : Type'} : (term85 B) = (term85 B).
Proof. exact (eq_refl (term85 B)). Qed.
Lemma lem7674082 {B : Type'} (h1 : (term83 B) = False) : (term86 B) = (term87 B).
Proof. exact (MK_COMB (@lem7674080 B h1) (@lem7674081 B)). Qed.
Lemma lem7674083 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7674084 {B : Type'} (h1 : (term83 B) = False) : (term88 B) = (term89 B).
Proof. exact (MK_COMB (@lem7674082 B h1) (@lem7674083)). Qed.
Lemma lem7674086 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7674087 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7674086 nat t1 t2). Qed.
Lemma lem7674088 {B : Type'} : (term89 B) = term25.
Proof. exact (@lem7674087 (term85 B) term25). Qed.
Lemma lem7674089 {B : Type'} (h1 : (term83 B) = False) : (term88 B) = term25.
Proof. exact (TRANS (@lem7674084 B h1) (@lem7674088 B)). Qed.
Lemma lem7674090 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7674091 {B : Type'} (h1 : (term83 B) = False) : (term90 B) = term30.
Proof. exact (MK_COMB (@lem7674090) (@lem7674089 B h1)). Qed.
Lemma lem7674092 (r : nat) : (@IN nat r) = (@IN nat r).
Proof. exact (eq_refl (@IN nat r)). Qed.
Lemma lem7674093 {B : Type'} (r : nat) (h1 : (term83 B) = False) : (term91 B r) = (term32 r).
Proof. exact (MK_COMB (@lem7674092 r) (@lem7674091 B h1)). Qed.
Lemma lem7674094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7674095 {B : Type'} (r : nat) (h1 : (term83 B) = False) : (term92 B r) = (term46 r).
Proof. exact (MK_COMB (@lem7674094) (@lem7674093 B r h1)). Qed.
Lemma lem7674098 {B : Type'} (r : nat) : ((term93 B r) = r) = ((term93 B r) = r).
Proof. exact (eq_refl ((term93 B r) = r)). Qed.
Lemma lem7674099 {B : Type'} (r : nat) (h1 : (term83 B) = False) : ((term91 B r) = ((term93 B r) = r)) = ((term32 r) = ((term93 B r) = r)).
Proof. exact (MK_COMB (@lem7674095 B r h1) (@lem7674098 B r)). Qed.
Lemma lem7674102 {B : Type'} (h1 : (term83 B) = False) : (term94 B) = (term95 B).
Proof. exact (fun_ext (fun r : nat => @lem7674099 B r h1)). Qed.
Lemma lem7674103 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7674104 {B : Type'} (h1 : (term83 B) = False) : (term96 B) = (term97 B).
Proof. exact (MK_COMB (@lem7674103) (@lem7674102 B h1)). Qed.
Lemma lem7674109 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7674110 {B : Type'} (h1 : (term83 B) = False) : (term5 B) = (term99 B).
Proof. exact (MK_COMB (@lem7674109 B) (@lem7674104 B h1)). Qed.
Lemma lem7674113 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7674114 {B : Type'} (h1 : (term83 B) = False) : (term11 B) = (term136 B).
Proof. exact (MK_COMB (@lem7674113) (@lem7674110 B h1)). Qed.
Lemma lem7674115 {A B : Type'} : (term74 A B) = (term74 A B).
Proof. exact (eq_refl (term74 A B)). Qed.
Lemma lem7674116 {A B : Type'} (h1 : (term83 B) = False) : (term75 A B) = (term137 A B).
Proof. exact (MK_COMB (@lem7674115 A B) (@lem7674114 B h1)). Qed.
Lemma lem7674119 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (eq_refl (term123 A)). Qed.
Lemma lem7674120 {A B : Type'} (h1 : (term83 B) = False) : (term124 A B) = (term138 A B).
Proof. exact (MK_COMB (@lem7674119 A) (@lem7674116 A B h1)). Qed.
Lemma lem7674123 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (eq_refl (term69 A B)). Qed.
Lemma lem7674124 {A B : Type'} (h1 : (term83 B) = False) : (term125 A B) = (term139 A B).
Proof. exact (MK_COMB (@lem7674123 A B) (@lem7674120 A B h1)). Qed.
Lemma lem7674127 {A B : Type'} : (term103 A B) = (term103 A B).
Proof. exact (eq_refl (term103 A B)). Qed.
Lemma lem7674128 {A B : Type'} (h1 : (term83 B) = False) : (term126 A B) = (term140 A B).
Proof. exact (MK_COMB (@lem7674127 A B) (@lem7674124 A B h1)). Qed.
Lemma lem7674131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7674132 {A B : Type'} (h1 : (term83 B) = False) : (term127 A B) = (term141 A B).
Proof. exact (MK_COMB (@lem7674131) (@lem7674128 A B h1)). Qed.
Lemma lem7674187 {B : Type'} (h1 : (term83 B) = False) : (term83 B) = False.
Proof. exact (h1). Qed.
Lemma lem7674188 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7674189 {B : Type'} (h1 : (term83 B) = False) : (term84 B) = (@COND nat False).
Proof. exact (MK_COMB (@lem7674188) (@lem7674187 B h1)). Qed.
Lemma lem7674190 {B : Type'} : (term85 B) = (term85 B).
Proof. exact (eq_refl (term85 B)). Qed.
Lemma lem7674191 {B : Type'} (h1 : (term83 B) = False) : (term86 B) = (term87 B).
Proof. exact (MK_COMB (@lem7674189 B h1) (@lem7674190 B)). Qed.
Lemma lem7674192 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7674193 {B : Type'} (h1 : (term83 B) = False) : (term88 B) = (term89 B).
Proof. exact (MK_COMB (@lem7674191 B h1) (@lem7674192)). Qed.
Lemma lem7674195 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7674196 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7674195 nat t1 t2). Qed.
Lemma lem7674197 {B : Type'} : (term89 B) = term25.
Proof. exact (@lem7674196 (term85 B) term25). Qed.
Lemma lem7674198 {B : Type'} (h1 : (term83 B) = False) : (term88 B) = term25.
Proof. exact (TRANS (@lem7674193 B h1) (@lem7674197 B)). Qed.
Lemma lem7674199 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7674200 {B : Type'} (h1 : (term83 B) = False) : (term90 B) = term30.
Proof. exact (MK_COMB (@lem7674199) (@lem7674198 B h1)). Qed.
Lemma lem7674201 (r : nat) : (@IN nat r) = (@IN nat r).
Proof. exact (eq_refl (@IN nat r)). Qed.
Lemma lem7674202 {B : Type'} (r : nat) (h1 : (term83 B) = False) : (term91 B r) = (term32 r).
Proof. exact (MK_COMB (@lem7674201 r) (@lem7674200 B h1)). Qed.
Lemma lem7674203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7674204 {B : Type'} (r : nat) (h1 : (term83 B) = False) : (term92 B r) = (term46 r).
Proof. exact (MK_COMB (@lem7674203) (@lem7674202 B r h1)). Qed.
Lemma lem7674207 {B : Type'} (r : nat) : ((term93 B r) = r) = ((term93 B r) = r).
Proof. exact (eq_refl ((term93 B r) = r)). Qed.
Lemma lem7674208 {B : Type'} (r : nat) (h1 : (term83 B) = False) : ((term91 B r) = ((term93 B r) = r)) = ((term32 r) = ((term93 B r) = r)).
Proof. exact (MK_COMB (@lem7674204 B r h1) (@lem7674207 B r)). Qed.
Lemma lem7674211 {B : Type'} (h1 : (term83 B) = False) : (term94 B) = (term95 B).
Proof. exact (fun_ext (fun r : nat => @lem7674208 B r h1)). Qed.
Lemma lem7674212 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7674213 {B : Type'} (h1 : (term83 B) = False) : (term96 B) = (term97 B).
Proof. exact (MK_COMB (@lem7674212) (@lem7674211 B h1)). Qed.
Lemma lem7674218 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7674219 {B : Type'} (h1 : (term83 B) = False) : (term5 B) = (term99 B).
Proof. exact (MK_COMB (@lem7674218 B) (@lem7674213 B h1)). Qed.
Lemma lem7674222 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7674223 {B : Type'} (h1 : (term83 B) = False) : (term11 B) = (term136 B).
Proof. exact (MK_COMB (@lem7674222) (@lem7674219 B h1)). Qed.
Lemma lem7674224 {A B : Type'} : (term54 A B) = (term54 A B).
Proof. exact (eq_refl (term54 A B)). Qed.
Lemma lem7674225 {A B : Type'} (h1 : (term83 B) = False) : (term55 A B) = (term142 A B).
Proof. exact (MK_COMB (@lem7674224 A B) (@lem7674223 B h1)). Qed.
Lemma lem7674228 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (eq_refl (term123 A)). Qed.
Lemma lem7674229 {A B : Type'} (h1 : (term83 B) = False) : (term128 A B) = (term143 A B).
Proof. exact (MK_COMB (@lem7674228 A) (@lem7674225 A B h1)). Qed.
Lemma lem7674232 {A B : Type'} : (term44 A B) = (term44 A B).
Proof. exact (eq_refl (term44 A B)). Qed.
Lemma lem7674233 {A B : Type'} (h1 : (term83 B) = False) : (term129 A B) = (term144 A B).
Proof. exact (MK_COMB (@lem7674232 A B) (@lem7674229 A B h1)). Qed.
Lemma lem7674236 {A B : Type'} : (term110 A B) = (term110 A B).
Proof. exact (eq_refl (term110 A B)). Qed.
Lemma lem7674237 {A B : Type'} (h1 : (term83 B) = False) : (term130 A B) = (term145 A B).
Proof. exact (MK_COMB (@lem7674236 A B) (@lem7674233 A B h1)). Qed.
Lemma lem7674240 {A B : Type'} (h1 : (term83 B) = False) : (term131 A B) = (term146 A B).
Proof. exact (MK_COMB (@lem7674132 A B h1) (@lem7674237 A B h1)). Qed.
Lemma lem7674243 {A : Type'} : (term147 A) = (term147 A).
Proof. exact (eq_refl (term147 A)). Qed.
Lemma lem7674244 {A B : Type'} (h1 : (term83 B) = False) : (term148 A B) = (term149 A B).
Proof. exact (MK_COMB (@lem7674243 A) (@lem7674240 A B h1)). Qed.
Lemma lem7674247 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7674248 {A B : Type'} (h1 : (term83 B) = False) : (term150 A B) = (term151 A B).
Proof. exact (MK_COMB (@lem7674247) (@lem7674244 A B h1)). Qed.
Lemma lem7674306 {B : Type'} (h1 : (term83 B) = False) : (term83 B) = False.
Proof. exact (h1). Qed.
Lemma lem7674307 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7674308 {B : Type'} (h1 : (term83 B) = False) : (term84 B) = (@COND nat False).
Proof. exact (MK_COMB (@lem7674307) (@lem7674306 B h1)). Qed.
Lemma lem7674309 {B : Type'} : (term85 B) = (term85 B).
Proof. exact (eq_refl (term85 B)). Qed.
Lemma lem7674310 {B : Type'} (h1 : (term83 B) = False) : (term86 B) = (term87 B).
Proof. exact (MK_COMB (@lem7674308 B h1) (@lem7674309 B)). Qed.
Lemma lem7674311 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7674312 {B : Type'} (h1 : (term83 B) = False) : (term88 B) = (term89 B).
Proof. exact (MK_COMB (@lem7674310 B h1) (@lem7674311)). Qed.
Lemma lem7674314 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7674315 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7674314 nat t1 t2). Qed.
Lemma lem7674316 {B : Type'} : (term89 B) = term25.
Proof. exact (@lem7674315 (term85 B) term25). Qed.
Lemma lem7674317 {B : Type'} (h1 : (term83 B) = False) : (term88 B) = term25.
Proof. exact (TRANS (@lem7674312 B h1) (@lem7674316 B)). Qed.
Lemma lem7674318 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7674319 {B : Type'} (h1 : (term83 B) = False) : (term90 B) = term30.
Proof. exact (MK_COMB (@lem7674318) (@lem7674317 B h1)). Qed.
Lemma lem7674320 (r : nat) : (@IN nat r) = (@IN nat r).
Proof. exact (eq_refl (@IN nat r)). Qed.
Lemma lem7674321 {B : Type'} (r : nat) (h1 : (term83 B) = False) : (term91 B r) = (term32 r).
Proof. exact (MK_COMB (@lem7674320 r) (@lem7674319 B h1)). Qed.
Lemma lem7674322 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7674323 {B : Type'} (r : nat) (h1 : (term83 B) = False) : (term92 B r) = (term46 r).
Proof. exact (MK_COMB (@lem7674322) (@lem7674321 B r h1)). Qed.
Lemma lem7674326 {B : Type'} (r : nat) : ((term93 B r) = r) = ((term93 B r) = r).
Proof. exact (eq_refl ((term93 B r) = r)). Qed.
Lemma lem7674327 {B : Type'} (r : nat) (h1 : (term83 B) = False) : ((term91 B r) = ((term93 B r) = r)) = ((term32 r) = ((term93 B r) = r)).
Proof. exact (MK_COMB (@lem7674323 B r h1) (@lem7674326 B r)). Qed.
Lemma lem7674330 {B : Type'} (h1 : (term83 B) = False) : (term94 B) = (term95 B).
Proof. exact (fun_ext (fun r : nat => @lem7674327 B r h1)). Qed.
Lemma lem7674331 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7674332 {B : Type'} (h1 : (term83 B) = False) : (term96 B) = (term97 B).
Proof. exact (MK_COMB (@lem7674331) (@lem7674330 B h1)). Qed.
Lemma lem7674337 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7674338 {B : Type'} (h1 : (term83 B) = False) : (term5 B) = (term99 B).
Proof. exact (MK_COMB (@lem7674337 B) (@lem7674332 B h1)). Qed.
Lemma lem7674341 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7674342 {B : Type'} (h1 : (term83 B) = False) : (term11 B) = (term136 B).
Proof. exact (MK_COMB (@lem7674341) (@lem7674338 B h1)). Qed.
Lemma lem7674343 {A B : Type'} : (term74 A B) = (term74 A B).
Proof. exact (eq_refl (term74 A B)). Qed.
Lemma lem7674344 {A B : Type'} (h1 : (term83 B) = False) : (term75 A B) = (term137 A B).
Proof. exact (MK_COMB (@lem7674343 A B) (@lem7674342 B h1)). Qed.
Lemma lem7674347 {A : Type'} : (term100 A) = (term100 A).
Proof. exact (eq_refl (term100 A)). Qed.
Lemma lem7674348 {A B : Type'} (h1 : (term83 B) = False) : (term101 A B) = (term152 A B).
Proof. exact (MK_COMB (@lem7674347 A) (@lem7674344 A B h1)). Qed.
Lemma lem7674351 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (eq_refl (term69 A B)). Qed.
Lemma lem7674352 {A B : Type'} (h1 : (term83 B) = False) : (term102 A B) = (term153 A B).
Proof. exact (MK_COMB (@lem7674351 A B) (@lem7674348 A B h1)). Qed.
Lemma lem7674355 {A B : Type'} : (term103 A B) = (term103 A B).
Proof. exact (eq_refl (term103 A B)). Qed.
Lemma lem7674356 {A B : Type'} (h1 : (term83 B) = False) : (term105 A B) = (term154 A B).
Proof. exact (MK_COMB (@lem7674355 A B) (@lem7674352 A B h1)). Qed.
Lemma lem7674359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7674360 {A B : Type'} (h1 : (term83 B) = False) : (term107 A B) = (term155 A B).
Proof. exact (MK_COMB (@lem7674359) (@lem7674356 A B h1)). Qed.
Lemma lem7674415 {B : Type'} (h1 : (term83 B) = False) : (term83 B) = False.
Proof. exact (h1). Qed.
Lemma lem7674416 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7674417 {B : Type'} (h1 : (term83 B) = False) : (term84 B) = (@COND nat False).
Proof. exact (MK_COMB (@lem7674416) (@lem7674415 B h1)). Qed.
Lemma lem7674418 {B : Type'} : (term85 B) = (term85 B).
Proof. exact (eq_refl (term85 B)). Qed.
Lemma lem7674419 {B : Type'} (h1 : (term83 B) = False) : (term86 B) = (term87 B).
Proof. exact (MK_COMB (@lem7674417 B h1) (@lem7674418 B)). Qed.
Lemma lem7674420 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7674421 {B : Type'} (h1 : (term83 B) = False) : (term88 B) = (term89 B).
Proof. exact (MK_COMB (@lem7674419 B h1) (@lem7674420)). Qed.
Lemma lem7674423 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7674424 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7674423 nat t1 t2). Qed.
Lemma lem7674425 {B : Type'} : (term89 B) = term25.
Proof. exact (@lem7674424 (term85 B) term25). Qed.
Lemma lem7674426 {B : Type'} (h1 : (term83 B) = False) : (term88 B) = term25.
Proof. exact (TRANS (@lem7674421 B h1) (@lem7674425 B)). Qed.
Lemma lem7674427 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7674428 {B : Type'} (h1 : (term83 B) = False) : (term90 B) = term30.
Proof. exact (MK_COMB (@lem7674427) (@lem7674426 B h1)). Qed.
Lemma lem7674429 (r : nat) : (@IN nat r) = (@IN nat r).
Proof. exact (eq_refl (@IN nat r)). Qed.
Lemma lem7674430 {B : Type'} (r : nat) (h1 : (term83 B) = False) : (term91 B r) = (term32 r).
Proof. exact (MK_COMB (@lem7674429 r) (@lem7674428 B h1)). Qed.
Lemma lem7674431 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7674432 {B : Type'} (r : nat) (h1 : (term83 B) = False) : (term92 B r) = (term46 r).
Proof. exact (MK_COMB (@lem7674431) (@lem7674430 B r h1)). Qed.
Lemma lem7674435 {B : Type'} (r : nat) : ((term93 B r) = r) = ((term93 B r) = r).
Proof. exact (eq_refl ((term93 B r) = r)). Qed.
Lemma lem7674436 {B : Type'} (r : nat) (h1 : (term83 B) = False) : ((term91 B r) = ((term93 B r) = r)) = ((term32 r) = ((term93 B r) = r)).
Proof. exact (MK_COMB (@lem7674432 B r h1) (@lem7674435 B r)). Qed.
Lemma lem7674439 {B : Type'} (h1 : (term83 B) = False) : (term94 B) = (term95 B).
Proof. exact (fun_ext (fun r : nat => @lem7674436 B r h1)). Qed.
Lemma lem7674440 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7674441 {B : Type'} (h1 : (term83 B) = False) : (term96 B) = (term97 B).
Proof. exact (MK_COMB (@lem7674440) (@lem7674439 B h1)). Qed.
Lemma lem7674446 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7674447 {B : Type'} (h1 : (term83 B) = False) : (term5 B) = (term99 B).
Proof. exact (MK_COMB (@lem7674446 B) (@lem7674441 B h1)). Qed.
Lemma lem7674450 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7674451 {B : Type'} (h1 : (term83 B) = False) : (term11 B) = (term136 B).
Proof. exact (MK_COMB (@lem7674450) (@lem7674447 B h1)). Qed.
Lemma lem7674452 {A B : Type'} : (term54 A B) = (term54 A B).
Proof. exact (eq_refl (term54 A B)). Qed.
Lemma lem7674453 {A B : Type'} (h1 : (term83 B) = False) : (term55 A B) = (term142 A B).
Proof. exact (MK_COMB (@lem7674452 A B) (@lem7674451 B h1)). Qed.
Lemma lem7674456 {A : Type'} : (term100 A) = (term100 A).
Proof. exact (eq_refl (term100 A)). Qed.
Lemma lem7674457 {A B : Type'} (h1 : (term83 B) = False) : (term108 A B) = (term156 A B).
Proof. exact (MK_COMB (@lem7674456 A) (@lem7674453 A B h1)). Qed.
Lemma lem7674460 {A B : Type'} : (term44 A B) = (term44 A B).
Proof. exact (eq_refl (term44 A B)). Qed.
Lemma lem7674461 {A B : Type'} (h1 : (term83 B) = False) : (term109 A B) = (term157 A B).
Proof. exact (MK_COMB (@lem7674460 A B) (@lem7674457 A B h1)). Qed.
Lemma lem7674464 {A B : Type'} : (term110 A B) = (term110 A B).
Proof. exact (eq_refl (term110 A B)). Qed.
Lemma lem7674465 {A B : Type'} (h1 : (term83 B) = False) : (term112 A B) = (term158 A B).
Proof. exact (MK_COMB (@lem7674464 A B) (@lem7674461 A B h1)). Qed.
Lemma lem7674468 {A B : Type'} (h1 : (term83 B) = False) : (term113 A B) = (term159 A B).
Proof. exact (MK_COMB (@lem7674360 A B h1) (@lem7674465 A B h1)). Qed.
Lemma lem7674471 {A : Type'} : (term160 A) = (term160 A).
Proof. exact (eq_refl (term160 A)). Qed.
Lemma lem7674472 {A B : Type'} (h1 : (term83 B) = False) : (term161 A B) = (term162 A B).
Proof. exact (MK_COMB (@lem7674471 A) (@lem7674468 A B h1)). Qed.
Lemma lem7674475 {A B : Type'} (h1 : (term83 B) = False) : (term135 A B) = (term163 A B).
Proof. exact (MK_COMB (@lem7674248 A B h1) (@lem7674472 A B h1)). Qed.
Lemma lem7674478 {A B : Type'} : term164 A B.
Proof. exact (fun h0 : (term83 B) = False => @lem7674475 A B h0). Qed.
Lemma lem7674536 {B : Type'} (h1 : (term83 B) = True) : (term83 B) = True.
Proof. exact (h1). Qed.
Lemma lem7674537 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7674538 {B : Type'} (h1 : (term83 B) = True) : (term84 B) = (@COND nat True).
Proof. exact (MK_COMB (@lem7674537) (@lem7674536 B h1)). Qed.
Lemma lem7674539 {B : Type'} : (term85 B) = (term85 B).
Proof. exact (eq_refl (term85 B)). Qed.
Lemma lem7674540 {B : Type'} (h1 : (term83 B) = True) : (term86 B) = (term115 B).
Proof. exact (MK_COMB (@lem7674538 B h1) (@lem7674539 B)). Qed.
Lemma lem7674541 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7674542 {B : Type'} (h1 : (term83 B) = True) : (term88 B) = (term116 B).
Proof. exact (MK_COMB (@lem7674540 B h1) (@lem7674541)). Qed.
Lemma lem7674544 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7674545 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7674544 nat t2 t1). Qed.
Lemma lem7674546 {B : Type'} : (term116 B) = (term85 B).
Proof. exact (@lem7674545 term25 (term85 B)). Qed.
Lemma lem7674547 {B : Type'} (h1 : (term83 B) = True) : (term88 B) = (term85 B).
Proof. exact (TRANS (@lem7674542 B h1) (@lem7674546 B)). Qed.
Lemma lem7674548 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7674549 {B : Type'} (h1 : (term83 B) = True) : (term90 B) = (term117 B).
Proof. exact (MK_COMB (@lem7674548) (@lem7674547 B h1)). Qed.
Lemma lem7674550 (r : nat) : (@IN nat r) = (@IN nat r).
Proof. exact (eq_refl (@IN nat r)). Qed.
Lemma lem7674551 {B : Type'} (r : nat) (h1 : (term83 B) = True) : (term91 B r) = (term118 B r).
Proof. exact (MK_COMB (@lem7674550 r) (@lem7674549 B h1)). Qed.
Lemma lem7674552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7674553 {B : Type'} (r : nat) (h1 : (term83 B) = True) : (term92 B r) = (term119 B r).
Proof. exact (MK_COMB (@lem7674552) (@lem7674551 B r h1)). Qed.
Lemma lem7674556 {B : Type'} (r : nat) : ((term93 B r) = r) = ((term93 B r) = r).
Proof. exact (eq_refl ((term93 B r) = r)). Qed.
Lemma lem7674557 {B : Type'} (r : nat) (h1 : (term83 B) = True) : ((term91 B r) = ((term93 B r) = r)) = ((term118 B r) = ((term93 B r) = r)).
Proof. exact (MK_COMB (@lem7674553 B r h1) (@lem7674556 B r)). Qed.
Lemma lem7674560 {B : Type'} (h1 : (term83 B) = True) : (term94 B) = (term120 B).
Proof. exact (fun_ext (fun r : nat => @lem7674557 B r h1)). Qed.
Lemma lem7674561 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7674562 {B : Type'} (h1 : (term83 B) = True) : (term96 B) = (term121 B).
Proof. exact (MK_COMB (@lem7674561) (@lem7674560 B h1)). Qed.
Lemma lem7674567 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7674568 {B : Type'} (h1 : (term83 B) = True) : (term5 B) = (term122 B).
Proof. exact (MK_COMB (@lem7674567 B) (@lem7674562 B h1)). Qed.
Lemma lem7674571 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7674572 {B : Type'} (h1 : (term83 B) = True) : (term11 B) = (term165 B).
Proof. exact (MK_COMB (@lem7674571) (@lem7674568 B h1)). Qed.
Lemma lem7674573 {A B : Type'} : (term74 A B) = (term74 A B).
Proof. exact (eq_refl (term74 A B)). Qed.
Lemma lem7674574 {A B : Type'} (h1 : (term83 B) = True) : (term75 A B) = (term166 A B).
Proof. exact (MK_COMB (@lem7674573 A B) (@lem7674572 B h1)). Qed.
Lemma lem7674577 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (eq_refl (term123 A)). Qed.
Lemma lem7674578 {A B : Type'} (h1 : (term83 B) = True) : (term124 A B) = (term167 A B).
Proof. exact (MK_COMB (@lem7674577 A) (@lem7674574 A B h1)). Qed.
Lemma lem7674581 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (eq_refl (term69 A B)). Qed.
Lemma lem7674582 {A B : Type'} (h1 : (term83 B) = True) : (term125 A B) = (term168 A B).
Proof. exact (MK_COMB (@lem7674581 A B) (@lem7674578 A B h1)). Qed.
Lemma lem7674585 {A B : Type'} : (term103 A B) = (term103 A B).
Proof. exact (eq_refl (term103 A B)). Qed.
Lemma lem7674586 {A B : Type'} (h1 : (term83 B) = True) : (term126 A B) = (term169 A B).
Proof. exact (MK_COMB (@lem7674585 A B) (@lem7674582 A B h1)). Qed.
Lemma lem7674589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7674590 {A B : Type'} (h1 : (term83 B) = True) : (term127 A B) = (term170 A B).
Proof. exact (MK_COMB (@lem7674589) (@lem7674586 A B h1)). Qed.
Lemma lem7674645 {B : Type'} (h1 : (term83 B) = True) : (term83 B) = True.
Proof. exact (h1). Qed.
Lemma lem7674646 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7674647 {B : Type'} (h1 : (term83 B) = True) : (term84 B) = (@COND nat True).
Proof. exact (MK_COMB (@lem7674646) (@lem7674645 B h1)). Qed.
Lemma lem7674648 {B : Type'} : (term85 B) = (term85 B).
Proof. exact (eq_refl (term85 B)). Qed.
Lemma lem7674649 {B : Type'} (h1 : (term83 B) = True) : (term86 B) = (term115 B).
Proof. exact (MK_COMB (@lem7674647 B h1) (@lem7674648 B)). Qed.
Lemma lem7674650 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7674651 {B : Type'} (h1 : (term83 B) = True) : (term88 B) = (term116 B).
Proof. exact (MK_COMB (@lem7674649 B h1) (@lem7674650)). Qed.
Lemma lem7674653 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7674654 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7674653 nat t2 t1). Qed.
Lemma lem7674655 {B : Type'} : (term116 B) = (term85 B).
Proof. exact (@lem7674654 term25 (term85 B)). Qed.
Lemma lem7674656 {B : Type'} (h1 : (term83 B) = True) : (term88 B) = (term85 B).
Proof. exact (TRANS (@lem7674651 B h1) (@lem7674655 B)). Qed.
Lemma lem7674657 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7674658 {B : Type'} (h1 : (term83 B) = True) : (term90 B) = (term117 B).
Proof. exact (MK_COMB (@lem7674657) (@lem7674656 B h1)). Qed.
Lemma lem7674659 (r : nat) : (@IN nat r) = (@IN nat r).
Proof. exact (eq_refl (@IN nat r)). Qed.
Lemma lem7674660 {B : Type'} (r : nat) (h1 : (term83 B) = True) : (term91 B r) = (term118 B r).
Proof. exact (MK_COMB (@lem7674659 r) (@lem7674658 B h1)). Qed.
Lemma lem7674661 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7674662 {B : Type'} (r : nat) (h1 : (term83 B) = True) : (term92 B r) = (term119 B r).
Proof. exact (MK_COMB (@lem7674661) (@lem7674660 B r h1)). Qed.
Lemma lem7674665 {B : Type'} (r : nat) : ((term93 B r) = r) = ((term93 B r) = r).
Proof. exact (eq_refl ((term93 B r) = r)). Qed.
Lemma lem7674666 {B : Type'} (r : nat) (h1 : (term83 B) = True) : ((term91 B r) = ((term93 B r) = r)) = ((term118 B r) = ((term93 B r) = r)).
Proof. exact (MK_COMB (@lem7674662 B r h1) (@lem7674665 B r)). Qed.
Lemma lem7674669 {B : Type'} (h1 : (term83 B) = True) : (term94 B) = (term120 B).
Proof. exact (fun_ext (fun r : nat => @lem7674666 B r h1)). Qed.
Lemma lem7674670 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7674671 {B : Type'} (h1 : (term83 B) = True) : (term96 B) = (term121 B).
Proof. exact (MK_COMB (@lem7674670) (@lem7674669 B h1)). Qed.
Lemma lem7674676 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7674677 {B : Type'} (h1 : (term83 B) = True) : (term5 B) = (term122 B).
Proof. exact (MK_COMB (@lem7674676 B) (@lem7674671 B h1)). Qed.
Lemma lem7674680 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7674681 {B : Type'} (h1 : (term83 B) = True) : (term11 B) = (term165 B).
Proof. exact (MK_COMB (@lem7674680) (@lem7674677 B h1)). Qed.
Lemma lem7674682 {A B : Type'} : (term54 A B) = (term54 A B).
Proof. exact (eq_refl (term54 A B)). Qed.
Lemma lem7674683 {A B : Type'} (h1 : (term83 B) = True) : (term55 A B) = (term171 A B).
Proof. exact (MK_COMB (@lem7674682 A B) (@lem7674681 B h1)). Qed.
Lemma lem7674686 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (eq_refl (term123 A)). Qed.
Lemma lem7674687 {A B : Type'} (h1 : (term83 B) = True) : (term128 A B) = (term172 A B).
Proof. exact (MK_COMB (@lem7674686 A) (@lem7674683 A B h1)). Qed.
Lemma lem7674690 {A B : Type'} : (term44 A B) = (term44 A B).
Proof. exact (eq_refl (term44 A B)). Qed.
Lemma lem7674691 {A B : Type'} (h1 : (term83 B) = True) : (term129 A B) = (term173 A B).
Proof. exact (MK_COMB (@lem7674690 A B) (@lem7674687 A B h1)). Qed.
Lemma lem7674694 {A B : Type'} : (term110 A B) = (term110 A B).
Proof. exact (eq_refl (term110 A B)). Qed.
Lemma lem7674695 {A B : Type'} (h1 : (term83 B) = True) : (term130 A B) = (term174 A B).
Proof. exact (MK_COMB (@lem7674694 A B) (@lem7674691 A B h1)). Qed.
Lemma lem7674698 {A B : Type'} (h1 : (term83 B) = True) : (term131 A B) = (term175 A B).
Proof. exact (MK_COMB (@lem7674590 A B h1) (@lem7674695 A B h1)). Qed.
Lemma lem7674701 {A : Type'} : (term147 A) = (term147 A).
Proof. exact (eq_refl (term147 A)). Qed.
Lemma lem7674702 {A B : Type'} (h1 : (term83 B) = True) : (term148 A B) = (term176 A B).
Proof. exact (MK_COMB (@lem7674701 A) (@lem7674698 A B h1)). Qed.
Lemma lem7674705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7674706 {A B : Type'} (h1 : (term83 B) = True) : (term150 A B) = (term177 A B).
Proof. exact (MK_COMB (@lem7674705) (@lem7674702 A B h1)). Qed.
Lemma lem7674764 {B : Type'} (h1 : (term83 B) = True) : (term83 B) = True.
Proof. exact (h1). Qed.
Lemma lem7674765 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7674766 {B : Type'} (h1 : (term83 B) = True) : (term84 B) = (@COND nat True).
Proof. exact (MK_COMB (@lem7674765) (@lem7674764 B h1)). Qed.
Lemma lem7674767 {B : Type'} : (term85 B) = (term85 B).
Proof. exact (eq_refl (term85 B)). Qed.
Lemma lem7674768 {B : Type'} (h1 : (term83 B) = True) : (term86 B) = (term115 B).
Proof. exact (MK_COMB (@lem7674766 B h1) (@lem7674767 B)). Qed.
Lemma lem7674769 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7674770 {B : Type'} (h1 : (term83 B) = True) : (term88 B) = (term116 B).
Proof. exact (MK_COMB (@lem7674768 B h1) (@lem7674769)). Qed.
Lemma lem7674772 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7674773 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7674772 nat t2 t1). Qed.
Lemma lem7674774 {B : Type'} : (term116 B) = (term85 B).
Proof. exact (@lem7674773 term25 (term85 B)). Qed.
Lemma lem7674775 {B : Type'} (h1 : (term83 B) = True) : (term88 B) = (term85 B).
Proof. exact (TRANS (@lem7674770 B h1) (@lem7674774 B)). Qed.
Lemma lem7674776 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7674777 {B : Type'} (h1 : (term83 B) = True) : (term90 B) = (term117 B).
Proof. exact (MK_COMB (@lem7674776) (@lem7674775 B h1)). Qed.
Lemma lem7674778 (r : nat) : (@IN nat r) = (@IN nat r).
Proof. exact (eq_refl (@IN nat r)). Qed.
Lemma lem7674779 {B : Type'} (r : nat) (h1 : (term83 B) = True) : (term91 B r) = (term118 B r).
Proof. exact (MK_COMB (@lem7674778 r) (@lem7674777 B h1)). Qed.
Lemma lem7674780 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7674781 {B : Type'} (r : nat) (h1 : (term83 B) = True) : (term92 B r) = (term119 B r).
Proof. exact (MK_COMB (@lem7674780) (@lem7674779 B r h1)). Qed.
Lemma lem7674784 {B : Type'} (r : nat) : ((term93 B r) = r) = ((term93 B r) = r).
Proof. exact (eq_refl ((term93 B r) = r)). Qed.
Lemma lem7674785 {B : Type'} (r : nat) (h1 : (term83 B) = True) : ((term91 B r) = ((term93 B r) = r)) = ((term118 B r) = ((term93 B r) = r)).
Proof. exact (MK_COMB (@lem7674781 B r h1) (@lem7674784 B r)). Qed.
Lemma lem7674788 {B : Type'} (h1 : (term83 B) = True) : (term94 B) = (term120 B).
Proof. exact (fun_ext (fun r : nat => @lem7674785 B r h1)). Qed.
Lemma lem7674789 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7674790 {B : Type'} (h1 : (term83 B) = True) : (term96 B) = (term121 B).
Proof. exact (MK_COMB (@lem7674789) (@lem7674788 B h1)). Qed.
Lemma lem7674795 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7674796 {B : Type'} (h1 : (term83 B) = True) : (term5 B) = (term122 B).
Proof. exact (MK_COMB (@lem7674795 B) (@lem7674790 B h1)). Qed.
Lemma lem7674799 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7674800 {B : Type'} (h1 : (term83 B) = True) : (term11 B) = (term165 B).
Proof. exact (MK_COMB (@lem7674799) (@lem7674796 B h1)). Qed.
Lemma lem7674801 {A B : Type'} : (term74 A B) = (term74 A B).
Proof. exact (eq_refl (term74 A B)). Qed.
Lemma lem7674802 {A B : Type'} (h1 : (term83 B) = True) : (term75 A B) = (term166 A B).
Proof. exact (MK_COMB (@lem7674801 A B) (@lem7674800 B h1)). Qed.
Lemma lem7674805 {A : Type'} : (term100 A) = (term100 A).
Proof. exact (eq_refl (term100 A)). Qed.
Lemma lem7674806 {A B : Type'} (h1 : (term83 B) = True) : (term101 A B) = (term178 A B).
Proof. exact (MK_COMB (@lem7674805 A) (@lem7674802 A B h1)). Qed.
Lemma lem7674809 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (eq_refl (term69 A B)). Qed.
Lemma lem7674810 {A B : Type'} (h1 : (term83 B) = True) : (term102 A B) = (term179 A B).
Proof. exact (MK_COMB (@lem7674809 A B) (@lem7674806 A B h1)). Qed.
Lemma lem7674813 {A B : Type'} : (term103 A B) = (term103 A B).
Proof. exact (eq_refl (term103 A B)). Qed.
Lemma lem7674814 {A B : Type'} (h1 : (term83 B) = True) : (term105 A B) = (term180 A B).
Proof. exact (MK_COMB (@lem7674813 A B) (@lem7674810 A B h1)). Qed.
Lemma lem7674817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7674818 {A B : Type'} (h1 : (term83 B) = True) : (term107 A B) = (term181 A B).
Proof. exact (MK_COMB (@lem7674817) (@lem7674814 A B h1)). Qed.
Lemma lem7674873 {B : Type'} (h1 : (term83 B) = True) : (term83 B) = True.
Proof. exact (h1). Qed.
Lemma lem7674874 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7674875 {B : Type'} (h1 : (term83 B) = True) : (term84 B) = (@COND nat True).
Proof. exact (MK_COMB (@lem7674874) (@lem7674873 B h1)). Qed.
Lemma lem7674876 {B : Type'} : (term85 B) = (term85 B).
Proof. exact (eq_refl (term85 B)). Qed.
Lemma lem7674877 {B : Type'} (h1 : (term83 B) = True) : (term86 B) = (term115 B).
Proof. exact (MK_COMB (@lem7674875 B h1) (@lem7674876 B)). Qed.
Lemma lem7674878 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7674879 {B : Type'} (h1 : (term83 B) = True) : (term88 B) = (term116 B).
Proof. exact (MK_COMB (@lem7674877 B h1) (@lem7674878)). Qed.
Lemma lem7674881 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7674882 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7674881 nat t2 t1). Qed.
Lemma lem7674883 {B : Type'} : (term116 B) = (term85 B).
Proof. exact (@lem7674882 term25 (term85 B)). Qed.
Lemma lem7674884 {B : Type'} (h1 : (term83 B) = True) : (term88 B) = (term85 B).
Proof. exact (TRANS (@lem7674879 B h1) (@lem7674883 B)). Qed.
Lemma lem7674885 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7674886 {B : Type'} (h1 : (term83 B) = True) : (term90 B) = (term117 B).
Proof. exact (MK_COMB (@lem7674885) (@lem7674884 B h1)). Qed.
Lemma lem7674887 (r : nat) : (@IN nat r) = (@IN nat r).
Proof. exact (eq_refl (@IN nat r)). Qed.
Lemma lem7674888 {B : Type'} (r : nat) (h1 : (term83 B) = True) : (term91 B r) = (term118 B r).
Proof. exact (MK_COMB (@lem7674887 r) (@lem7674886 B h1)). Qed.
Lemma lem7674889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7674890 {B : Type'} (r : nat) (h1 : (term83 B) = True) : (term92 B r) = (term119 B r).
Proof. exact (MK_COMB (@lem7674889) (@lem7674888 B r h1)). Qed.
Lemma lem7674893 {B : Type'} (r : nat) : ((term93 B r) = r) = ((term93 B r) = r).
Proof. exact (eq_refl ((term93 B r) = r)). Qed.
Lemma lem7674894 {B : Type'} (r : nat) (h1 : (term83 B) = True) : ((term91 B r) = ((term93 B r) = r)) = ((term118 B r) = ((term93 B r) = r)).
Proof. exact (MK_COMB (@lem7674890 B r h1) (@lem7674893 B r)). Qed.
Lemma lem7674897 {B : Type'} (h1 : (term83 B) = True) : (term94 B) = (term120 B).
Proof. exact (fun_ext (fun r : nat => @lem7674894 B r h1)). Qed.
Lemma lem7674898 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7674899 {B : Type'} (h1 : (term83 B) = True) : (term96 B) = (term121 B).
Proof. exact (MK_COMB (@lem7674898) (@lem7674897 B h1)). Qed.
Lemma lem7674904 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7674905 {B : Type'} (h1 : (term83 B) = True) : (term5 B) = (term122 B).
Proof. exact (MK_COMB (@lem7674904 B) (@lem7674899 B h1)). Qed.
Lemma lem7674908 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7674909 {B : Type'} (h1 : (term83 B) = True) : (term11 B) = (term165 B).
Proof. exact (MK_COMB (@lem7674908) (@lem7674905 B h1)). Qed.
Lemma lem7674910 {A B : Type'} : (term54 A B) = (term54 A B).
Proof. exact (eq_refl (term54 A B)). Qed.
Lemma lem7674911 {A B : Type'} (h1 : (term83 B) = True) : (term55 A B) = (term171 A B).
Proof. exact (MK_COMB (@lem7674910 A B) (@lem7674909 B h1)). Qed.
Lemma lem7674914 {A : Type'} : (term100 A) = (term100 A).
Proof. exact (eq_refl (term100 A)). Qed.
Lemma lem7674915 {A B : Type'} (h1 : (term83 B) = True) : (term108 A B) = (term182 A B).
Proof. exact (MK_COMB (@lem7674914 A) (@lem7674911 A B h1)). Qed.
Lemma lem7674918 {A B : Type'} : (term44 A B) = (term44 A B).
Proof. exact (eq_refl (term44 A B)). Qed.
Lemma lem7674919 {A B : Type'} (h1 : (term83 B) = True) : (term109 A B) = (term183 A B).
Proof. exact (MK_COMB (@lem7674918 A B) (@lem7674915 A B h1)). Qed.
Lemma lem7674922 {A B : Type'} : (term110 A B) = (term110 A B).
Proof. exact (eq_refl (term110 A B)). Qed.
Lemma lem7674923 {A B : Type'} (h1 : (term83 B) = True) : (term112 A B) = (term184 A B).
Proof. exact (MK_COMB (@lem7674922 A B) (@lem7674919 A B h1)). Qed.
Lemma lem7674926 {A B : Type'} (h1 : (term83 B) = True) : (term113 A B) = (term185 A B).
Proof. exact (MK_COMB (@lem7674818 A B h1) (@lem7674923 A B h1)). Qed.
Lemma lem7674929 {A : Type'} : (term160 A) = (term160 A).
Proof. exact (eq_refl (term160 A)). Qed.
Lemma lem7674930 {A B : Type'} (h1 : (term83 B) = True) : (term161 A B) = (term186 A B).
Proof. exact (MK_COMB (@lem7674929 A) (@lem7674926 A B h1)). Qed.
Lemma lem7674933 {A B : Type'} (h1 : (term83 B) = True) : (term135 A B) = (term187 A B).
Proof. exact (MK_COMB (@lem7674706 A B h1) (@lem7674930 A B h1)). Qed.
Lemma lem7674936 {A B : Type'} : term188 A B.
Proof. exact (fun h0 : (term83 B) = True => @lem7674933 A B h0). Qed.
Lemma lem7674937 {A B : Type'} : term189 A B.
Proof. exact (conj (@lem7674478 A B) (@lem7674936 A B)). Qed.
Lemma lem7674939 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term80 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem7674940 {A B : Type'} : term190 A B.
Proof. exact (@lem7674939 (term135 A B) (term187 A B) (term83 B) (term163 A B)). Qed.
Lemma lem7674955 {A B : Type'} : (term135 A B) = (term191 A B).
Proof. exact (@lem7674940 A B (@lem7674937 A B)). Qed.
Lemma lem7674960 {B : Type'} (r : nat) : ((term32 r) = ((term93 B r) = r)) = ((term32 r) = ((term93 B r) = r)).
Proof. exact (eq_refl ((term32 r) = ((term93 B r) = r))). Qed.
Lemma lem7674961 {B : Type'} : (term95 B) = (term95 B).
Proof. exact (fun_ext (fun r : nat => @lem7674960 B r)). Qed.
Lemma lem7674962 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7674963 {B : Type'} : (term97 B) = (term97 B).
Proof. exact (MK_COMB (@lem7674962) (@lem7674961 B)). Qed.
Lemma lem7674964 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7674965 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7674964 B a)). Qed.
Lemma lem7674966 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7674967 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7674966 B) (@lem7674965 B)). Qed.
Lemma lem7674968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7674969 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7674968) (@lem7674967 B)). Qed.
Lemma lem7674970 {B : Type'} : (term99 B) = (term99 B).
Proof. exact (MK_COMB (@lem7674969 B) (@lem7674963 B)). Qed.
Lemma lem7674971 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7674972 {B : Type'} : (term136 B) = (term136 B).
Proof. exact (MK_COMB (@lem7674971) (@lem7674970 B)). Qed.
Lemma lem7674977 {A B : Type'} (r : nat) : ((term32 r) = ((term47 A B r) = r)) = ((term32 r) = ((term47 A B r) = r)).
Proof. exact (eq_refl ((term32 r) = ((term47 A B r) = r))). Qed.
Lemma lem7674978 {A B : Type'} : (term49 A B) = (term49 A B).
Proof. exact (fun_ext (fun r : nat => @lem7674977 A B r)). Qed.
Lemma lem7674979 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7674980 {A B : Type'} : (term51 A B) = (term51 A B).
Proof. exact (MK_COMB (@lem7674979) (@lem7674978 A B)). Qed.
Lemma lem7674981 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7674982 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7674981 A B a)). Qed.
Lemma lem7674983 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7674984 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7674983 A B) (@lem7674982 A B)). Qed.
Lemma lem7674985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7674986 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7674985) (@lem7674984 A B)). Qed.
Lemma lem7674987 {A B : Type'} : (term53 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem7674986 A B) (@lem7674980 A B)). Qed.
Lemma lem7674988 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7674989 {A B : Type'} : (term54 A B) = (term54 A B).
Proof. exact (MK_COMB (@lem7674988) (@lem7674987 A B)). Qed.
Lemma lem7674990 {A B : Type'} : (term142 A B) = (term142 A B).
Proof. exact (MK_COMB (@lem7674989 A B) (@lem7674972 B)). Qed.
Lemma lem7674995 {A : Type'} (r : nat) : ((term32 r) = ((term93 A r) = r)) = ((term32 r) = ((term93 A r) = r)).
Proof. exact (eq_refl ((term32 r) = ((term93 A r) = r))). Qed.
Lemma lem7674996 {A : Type'} : (term95 A) = (term95 A).
Proof. exact (fun_ext (fun r : nat => @lem7674995 A r)). Qed.
Lemma lem7674997 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7674998 {A : Type'} : (term97 A) = (term97 A).
Proof. exact (MK_COMB (@lem7674997) (@lem7674996 A)). Qed.
Lemma lem7674999 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7675000 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7674999 A a)). Qed.
Lemma lem7675001 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7675002 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7675001 A) (@lem7675000 A)). Qed.
Lemma lem7675003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675004 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7675003) (@lem7675002 A)). Qed.
Lemma lem7675005 {A : Type'} : (term99 A) = (term99 A).
Proof. exact (MK_COMB (@lem7675004 A) (@lem7674998 A)). Qed.
Lemma lem7675006 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675007 {A : Type'} : (term100 A) = (term100 A).
Proof. exact (MK_COMB (@lem7675006) (@lem7675005 A)). Qed.
Lemma lem7675008 {A B : Type'} : (term156 A B) = (term156 A B).
Proof. exact (MK_COMB (@lem7675007 A) (@lem7674990 A B)). Qed.
Lemma lem7675013 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term35 A B x x') = (term35 A B x x').
Proof. exact (eq_refl (term35 A B x x')). Qed.
Lemma lem7675014 {A B : Type'} (x : finite_diff A B) : (term37 A B x) = (term37 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7675013 A B x x')). Qed.
Lemma lem7675015 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7675016 {A B : Type'} (x : finite_diff A B) : (term39 A B x) = (term39 A B x).
Proof. exact (MK_COMB (@lem7675015) (@lem7675014 A B x)). Qed.
Lemma lem7675017 {A B : Type'} : (term41 A B) = (term41 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7675016 A B x)). Qed.
Lemma lem7675018 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7675019 {A B : Type'} : (term42 A B) = (term42 A B).
Proof. exact (MK_COMB (@lem7675018 A B) (@lem7675017 A B)). Qed.
Lemma lem7675020 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7675021 {A B : Type'} : (term43 A B) = (term43 A B).
Proof. exact (MK_COMB (@lem7675020) (@lem7675019 A B)). Qed.
Lemma lem7675022 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675023 {A B : Type'} : (term44 A B) = (term44 A B).
Proof. exact (MK_COMB (@lem7675022) (@lem7675021 A B)). Qed.
Lemma lem7675024 {A B : Type'} : (term157 A B) = (term157 A B).
Proof. exact (MK_COMB (@lem7675023 A B) (@lem7675008 A B)). Qed.
Lemma lem7675027 {A B : Type'} : (term110 A B) = (term110 A B).
Proof. exact (eq_refl (term110 A B)). Qed.
Lemma lem7675028 {A B : Type'} : (term158 A B) = (term158 A B).
Proof. exact (MK_COMB (@lem7675027 A B) (@lem7675024 A B)). Qed.
Lemma lem7675033 {B : Type'} (r : nat) : ((term32 r) = ((term93 B r) = r)) = ((term32 r) = ((term93 B r) = r)).
Proof. exact (eq_refl ((term32 r) = ((term93 B r) = r))). Qed.
Lemma lem7675034 {B : Type'} : (term95 B) = (term95 B).
Proof. exact (fun_ext (fun r : nat => @lem7675033 B r)). Qed.
Lemma lem7675035 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675036 {B : Type'} : (term97 B) = (term97 B).
Proof. exact (MK_COMB (@lem7675035) (@lem7675034 B)). Qed.
Lemma lem7675037 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7675038 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7675037 B a)). Qed.
Lemma lem7675039 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7675040 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7675039 B) (@lem7675038 B)). Qed.
Lemma lem7675041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675042 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7675041) (@lem7675040 B)). Qed.
Lemma lem7675043 {B : Type'} : (term99 B) = (term99 B).
Proof. exact (MK_COMB (@lem7675042 B) (@lem7675036 B)). Qed.
Lemma lem7675044 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7675045 {B : Type'} : (term136 B) = (term136 B).
Proof. exact (MK_COMB (@lem7675044) (@lem7675043 B)). Qed.
Lemma lem7675050 {A B : Type'} (r : nat) : ((term62 A B r) = ((term47 A B r) = r)) = ((term62 A B r) = ((term47 A B r) = r)).
Proof. exact (eq_refl ((term62 A B r) = ((term47 A B r) = r))). Qed.
Lemma lem7675051 {A B : Type'} : (term71 A B) = (term71 A B).
Proof. exact (fun_ext (fun r : nat => @lem7675050 A B r)). Qed.
Lemma lem7675052 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675053 {A B : Type'} : (term72 A B) = (term72 A B).
Proof. exact (MK_COMB (@lem7675052) (@lem7675051 A B)). Qed.
Lemma lem7675054 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7675055 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7675054 A B a)). Qed.
Lemma lem7675056 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7675057 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7675056 A B) (@lem7675055 A B)). Qed.
Lemma lem7675058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675059 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7675058) (@lem7675057 A B)). Qed.
Lemma lem7675060 {A B : Type'} : (term73 A B) = (term73 A B).
Proof. exact (MK_COMB (@lem7675059 A B) (@lem7675053 A B)). Qed.
Lemma lem7675061 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675062 {A B : Type'} : (term74 A B) = (term74 A B).
Proof. exact (MK_COMB (@lem7675061) (@lem7675060 A B)). Qed.
Lemma lem7675063 {A B : Type'} : (term137 A B) = (term137 A B).
Proof. exact (MK_COMB (@lem7675062 A B) (@lem7675045 B)). Qed.
Lemma lem7675068 {A : Type'} (r : nat) : ((term32 r) = ((term93 A r) = r)) = ((term32 r) = ((term93 A r) = r)).
Proof. exact (eq_refl ((term32 r) = ((term93 A r) = r))). Qed.
Lemma lem7675069 {A : Type'} : (term95 A) = (term95 A).
Proof. exact (fun_ext (fun r : nat => @lem7675068 A r)). Qed.
Lemma lem7675070 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675071 {A : Type'} : (term97 A) = (term97 A).
Proof. exact (MK_COMB (@lem7675070) (@lem7675069 A)). Qed.
Lemma lem7675072 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7675073 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7675072 A a)). Qed.
Lemma lem7675074 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7675075 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7675074 A) (@lem7675073 A)). Qed.
Lemma lem7675076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675077 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7675076) (@lem7675075 A)). Qed.
Lemma lem7675078 {A : Type'} : (term99 A) = (term99 A).
Proof. exact (MK_COMB (@lem7675077 A) (@lem7675071 A)). Qed.
Lemma lem7675079 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675080 {A : Type'} : (term100 A) = (term100 A).
Proof. exact (MK_COMB (@lem7675079) (@lem7675078 A)). Qed.
Lemma lem7675081 {A B : Type'} : (term152 A B) = (term152 A B).
Proof. exact (MK_COMB (@lem7675080 A) (@lem7675063 A B)). Qed.
Lemma lem7675086 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term63 A B x x') = (term63 A B x x').
Proof. exact (eq_refl (term63 A B x x')). Qed.
Lemma lem7675087 {A B : Type'} (x : finite_diff A B) : (term64 A B x) = (term64 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7675086 A B x x')). Qed.
Lemma lem7675088 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7675089 {A B : Type'} (x : finite_diff A B) : (term65 A B x) = (term65 A B x).
Proof. exact (MK_COMB (@lem7675088) (@lem7675087 A B x)). Qed.
Lemma lem7675090 {A B : Type'} : (term66 A B) = (term66 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7675089 A B x)). Qed.
Lemma lem7675091 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7675092 {A B : Type'} : (term67 A B) = (term67 A B).
Proof. exact (MK_COMB (@lem7675091 A B) (@lem7675090 A B)). Qed.
Lemma lem7675093 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7675094 {A B : Type'} : (term68 A B) = (term68 A B).
Proof. exact (MK_COMB (@lem7675093) (@lem7675092 A B)). Qed.
Lemma lem7675095 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675096 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (MK_COMB (@lem7675095) (@lem7675094 A B)). Qed.
Lemma lem7675097 {A B : Type'} : (term153 A B) = (term153 A B).
Proof. exact (MK_COMB (@lem7675096 A B) (@lem7675081 A B)). Qed.
Lemma lem7675102 {A B : Type'} : (term103 A B) = (term103 A B).
Proof. exact (eq_refl (term103 A B)). Qed.
Lemma lem7675103 {A B : Type'} : (term154 A B) = (term154 A B).
Proof. exact (MK_COMB (@lem7675102 A B) (@lem7675097 A B)). Qed.
Lemma lem7675104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675105 {A B : Type'} : (term155 A B) = (term155 A B).
Proof. exact (MK_COMB (@lem7675104) (@lem7675103 A B)). Qed.
Lemma lem7675106 {A B : Type'} : (term159 A B) = (term159 A B).
Proof. exact (MK_COMB (@lem7675105 A B) (@lem7675028 A B)). Qed.
Lemma lem7675109 {A : Type'} : (term160 A) = (term160 A).
Proof. exact (eq_refl (term160 A)). Qed.
Lemma lem7675110 {A B : Type'} : (term162 A B) = (term162 A B).
Proof. exact (MK_COMB (@lem7675109 A) (@lem7675106 A B)). Qed.
Lemma lem7675115 {B : Type'} (r : nat) : ((term32 r) = ((term93 B r) = r)) = ((term32 r) = ((term93 B r) = r)).
Proof. exact (eq_refl ((term32 r) = ((term93 B r) = r))). Qed.
Lemma lem7675116 {B : Type'} : (term95 B) = (term95 B).
Proof. exact (fun_ext (fun r : nat => @lem7675115 B r)). Qed.
Lemma lem7675117 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675118 {B : Type'} : (term97 B) = (term97 B).
Proof. exact (MK_COMB (@lem7675117) (@lem7675116 B)). Qed.
Lemma lem7675119 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7675120 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7675119 B a)). Qed.
Lemma lem7675121 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7675122 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7675121 B) (@lem7675120 B)). Qed.
Lemma lem7675123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675124 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7675123) (@lem7675122 B)). Qed.
Lemma lem7675125 {B : Type'} : (term99 B) = (term99 B).
Proof. exact (MK_COMB (@lem7675124 B) (@lem7675118 B)). Qed.
Lemma lem7675126 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7675127 {B : Type'} : (term136 B) = (term136 B).
Proof. exact (MK_COMB (@lem7675126) (@lem7675125 B)). Qed.
Lemma lem7675132 {A B : Type'} (r : nat) : ((term32 r) = ((term47 A B r) = r)) = ((term32 r) = ((term47 A B r) = r)).
Proof. exact (eq_refl ((term32 r) = ((term47 A B r) = r))). Qed.
Lemma lem7675133 {A B : Type'} : (term49 A B) = (term49 A B).
Proof. exact (fun_ext (fun r : nat => @lem7675132 A B r)). Qed.
Lemma lem7675134 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675135 {A B : Type'} : (term51 A B) = (term51 A B).
Proof. exact (MK_COMB (@lem7675134) (@lem7675133 A B)). Qed.
Lemma lem7675136 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7675137 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7675136 A B a)). Qed.
Lemma lem7675138 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7675139 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7675138 A B) (@lem7675137 A B)). Qed.
Lemma lem7675140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675141 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7675140) (@lem7675139 A B)). Qed.
Lemma lem7675142 {A B : Type'} : (term53 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem7675141 A B) (@lem7675135 A B)). Qed.
Lemma lem7675143 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675144 {A B : Type'} : (term54 A B) = (term54 A B).
Proof. exact (MK_COMB (@lem7675143) (@lem7675142 A B)). Qed.
Lemma lem7675145 {A B : Type'} : (term142 A B) = (term142 A B).
Proof. exact (MK_COMB (@lem7675144 A B) (@lem7675127 B)). Qed.
Lemma lem7675150 {A : Type'} (r : nat) : ((term118 A r) = ((term93 A r) = r)) = ((term118 A r) = ((term93 A r) = r)).
Proof. exact (eq_refl ((term118 A r) = ((term93 A r) = r))). Qed.
Lemma lem7675151 {A : Type'} : (term120 A) = (term120 A).
Proof. exact (fun_ext (fun r : nat => @lem7675150 A r)). Qed.
Lemma lem7675152 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675153 {A : Type'} : (term121 A) = (term121 A).
Proof. exact (MK_COMB (@lem7675152) (@lem7675151 A)). Qed.
Lemma lem7675154 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7675155 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7675154 A a)). Qed.
Lemma lem7675156 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7675157 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7675156 A) (@lem7675155 A)). Qed.
Lemma lem7675158 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675159 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7675158) (@lem7675157 A)). Qed.
Lemma lem7675160 {A : Type'} : (term122 A) = (term122 A).
Proof. exact (MK_COMB (@lem7675159 A) (@lem7675153 A)). Qed.
Lemma lem7675161 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675162 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (MK_COMB (@lem7675161) (@lem7675160 A)). Qed.
Lemma lem7675163 {A B : Type'} : (term143 A B) = (term143 A B).
Proof. exact (MK_COMB (@lem7675162 A) (@lem7675145 A B)). Qed.
Lemma lem7675168 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term35 A B x x') = (term35 A B x x').
Proof. exact (eq_refl (term35 A B x x')). Qed.
Lemma lem7675169 {A B : Type'} (x : finite_diff A B) : (term37 A B x) = (term37 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7675168 A B x x')). Qed.
Lemma lem7675170 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7675171 {A B : Type'} (x : finite_diff A B) : (term39 A B x) = (term39 A B x).
Proof. exact (MK_COMB (@lem7675170) (@lem7675169 A B x)). Qed.
Lemma lem7675172 {A B : Type'} : (term41 A B) = (term41 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7675171 A B x)). Qed.
Lemma lem7675173 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7675174 {A B : Type'} : (term42 A B) = (term42 A B).
Proof. exact (MK_COMB (@lem7675173 A B) (@lem7675172 A B)). Qed.
Lemma lem7675175 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7675176 {A B : Type'} : (term43 A B) = (term43 A B).
Proof. exact (MK_COMB (@lem7675175) (@lem7675174 A B)). Qed.
Lemma lem7675177 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675178 {A B : Type'} : (term44 A B) = (term44 A B).
Proof. exact (MK_COMB (@lem7675177) (@lem7675176 A B)). Qed.
Lemma lem7675179 {A B : Type'} : (term144 A B) = (term144 A B).
Proof. exact (MK_COMB (@lem7675178 A B) (@lem7675163 A B)). Qed.
Lemma lem7675182 {A B : Type'} : (term110 A B) = (term110 A B).
Proof. exact (eq_refl (term110 A B)). Qed.
Lemma lem7675183 {A B : Type'} : (term145 A B) = (term145 A B).
Proof. exact (MK_COMB (@lem7675182 A B) (@lem7675179 A B)). Qed.
Lemma lem7675188 {B : Type'} (r : nat) : ((term32 r) = ((term93 B r) = r)) = ((term32 r) = ((term93 B r) = r)).
Proof. exact (eq_refl ((term32 r) = ((term93 B r) = r))). Qed.
Lemma lem7675189 {B : Type'} : (term95 B) = (term95 B).
Proof. exact (fun_ext (fun r : nat => @lem7675188 B r)). Qed.
Lemma lem7675190 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675191 {B : Type'} : (term97 B) = (term97 B).
Proof. exact (MK_COMB (@lem7675190) (@lem7675189 B)). Qed.
Lemma lem7675192 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7675193 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7675192 B a)). Qed.
Lemma lem7675194 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7675195 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7675194 B) (@lem7675193 B)). Qed.
Lemma lem7675196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675197 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7675196) (@lem7675195 B)). Qed.
Lemma lem7675198 {B : Type'} : (term99 B) = (term99 B).
Proof. exact (MK_COMB (@lem7675197 B) (@lem7675191 B)). Qed.
Lemma lem7675199 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7675200 {B : Type'} : (term136 B) = (term136 B).
Proof. exact (MK_COMB (@lem7675199) (@lem7675198 B)). Qed.
Lemma lem7675205 {A B : Type'} (r : nat) : ((term62 A B r) = ((term47 A B r) = r)) = ((term62 A B r) = ((term47 A B r) = r)).
Proof. exact (eq_refl ((term62 A B r) = ((term47 A B r) = r))). Qed.
Lemma lem7675206 {A B : Type'} : (term71 A B) = (term71 A B).
Proof. exact (fun_ext (fun r : nat => @lem7675205 A B r)). Qed.
Lemma lem7675207 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675208 {A B : Type'} : (term72 A B) = (term72 A B).
Proof. exact (MK_COMB (@lem7675207) (@lem7675206 A B)). Qed.
Lemma lem7675209 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7675210 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7675209 A B a)). Qed.
Lemma lem7675211 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7675212 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7675211 A B) (@lem7675210 A B)). Qed.
Lemma lem7675213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675214 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7675213) (@lem7675212 A B)). Qed.
Lemma lem7675215 {A B : Type'} : (term73 A B) = (term73 A B).
Proof. exact (MK_COMB (@lem7675214 A B) (@lem7675208 A B)). Qed.
Lemma lem7675216 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675217 {A B : Type'} : (term74 A B) = (term74 A B).
Proof. exact (MK_COMB (@lem7675216) (@lem7675215 A B)). Qed.
Lemma lem7675218 {A B : Type'} : (term137 A B) = (term137 A B).
Proof. exact (MK_COMB (@lem7675217 A B) (@lem7675200 B)). Qed.
Lemma lem7675223 {A : Type'} (r : nat) : ((term118 A r) = ((term93 A r) = r)) = ((term118 A r) = ((term93 A r) = r)).
Proof. exact (eq_refl ((term118 A r) = ((term93 A r) = r))). Qed.
Lemma lem7675224 {A : Type'} : (term120 A) = (term120 A).
Proof. exact (fun_ext (fun r : nat => @lem7675223 A r)). Qed.
Lemma lem7675225 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675226 {A : Type'} : (term121 A) = (term121 A).
Proof. exact (MK_COMB (@lem7675225) (@lem7675224 A)). Qed.
Lemma lem7675227 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7675228 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7675227 A a)). Qed.
Lemma lem7675229 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7675230 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7675229 A) (@lem7675228 A)). Qed.
Lemma lem7675231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675232 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7675231) (@lem7675230 A)). Qed.
Lemma lem7675233 {A : Type'} : (term122 A) = (term122 A).
Proof. exact (MK_COMB (@lem7675232 A) (@lem7675226 A)). Qed.
Lemma lem7675234 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675235 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (MK_COMB (@lem7675234) (@lem7675233 A)). Qed.
Lemma lem7675236 {A B : Type'} : (term138 A B) = (term138 A B).
Proof. exact (MK_COMB (@lem7675235 A) (@lem7675218 A B)). Qed.
Lemma lem7675241 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term63 A B x x') = (term63 A B x x').
Proof. exact (eq_refl (term63 A B x x')). Qed.
Lemma lem7675242 {A B : Type'} (x : finite_diff A B) : (term64 A B x) = (term64 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7675241 A B x x')). Qed.
Lemma lem7675243 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7675244 {A B : Type'} (x : finite_diff A B) : (term65 A B x) = (term65 A B x).
Proof. exact (MK_COMB (@lem7675243) (@lem7675242 A B x)). Qed.
Lemma lem7675245 {A B : Type'} : (term66 A B) = (term66 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7675244 A B x)). Qed.
Lemma lem7675246 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7675247 {A B : Type'} : (term67 A B) = (term67 A B).
Proof. exact (MK_COMB (@lem7675246 A B) (@lem7675245 A B)). Qed.
Lemma lem7675248 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7675249 {A B : Type'} : (term68 A B) = (term68 A B).
Proof. exact (MK_COMB (@lem7675248) (@lem7675247 A B)). Qed.
Lemma lem7675250 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675251 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (MK_COMB (@lem7675250) (@lem7675249 A B)). Qed.
Lemma lem7675252 {A B : Type'} : (term139 A B) = (term139 A B).
Proof. exact (MK_COMB (@lem7675251 A B) (@lem7675236 A B)). Qed.
Lemma lem7675257 {A B : Type'} : (term103 A B) = (term103 A B).
Proof. exact (eq_refl (term103 A B)). Qed.
Lemma lem7675258 {A B : Type'} : (term140 A B) = (term140 A B).
Proof. exact (MK_COMB (@lem7675257 A B) (@lem7675252 A B)). Qed.
Lemma lem7675259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675260 {A B : Type'} : (term141 A B) = (term141 A B).
Proof. exact (MK_COMB (@lem7675259) (@lem7675258 A B)). Qed.
Lemma lem7675261 {A B : Type'} : (term146 A B) = (term146 A B).
Proof. exact (MK_COMB (@lem7675260 A B) (@lem7675183 A B)). Qed.
Lemma lem7675266 {A : Type'} : (term147 A) = (term147 A).
Proof. exact (eq_refl (term147 A)). Qed.
Lemma lem7675267 {A B : Type'} : (term149 A B) = (term149 A B).
Proof. exact (MK_COMB (@lem7675266 A) (@lem7675261 A B)). Qed.
Lemma lem7675268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675269 {A B : Type'} : (term151 A B) = (term151 A B).
Proof. exact (MK_COMB (@lem7675268) (@lem7675267 A B)). Qed.
Lemma lem7675270 {A B : Type'} : (term163 A B) = (term163 A B).
Proof. exact (MK_COMB (@lem7675269 A B) (@lem7675110 A B)). Qed.
Lemma lem7675273 {B : Type'} : (term160 B) = (term160 B).
Proof. exact (eq_refl (term160 B)). Qed.
Lemma lem7675274 {A B : Type'} : (term198 A B) = (term198 A B).
Proof. exact (MK_COMB (@lem7675273 B) (@lem7675270 A B)). Qed.
Lemma lem7675279 {B : Type'} (r : nat) : ((term118 B r) = ((term93 B r) = r)) = ((term118 B r) = ((term93 B r) = r)).
Proof. exact (eq_refl ((term118 B r) = ((term93 B r) = r))). Qed.
Lemma lem7675280 {B : Type'} : (term120 B) = (term120 B).
Proof. exact (fun_ext (fun r : nat => @lem7675279 B r)). Qed.
Lemma lem7675281 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675282 {B : Type'} : (term121 B) = (term121 B).
Proof. exact (MK_COMB (@lem7675281) (@lem7675280 B)). Qed.
Lemma lem7675283 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7675284 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7675283 B a)). Qed.
Lemma lem7675285 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7675286 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7675285 B) (@lem7675284 B)). Qed.
Lemma lem7675287 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675288 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7675287) (@lem7675286 B)). Qed.
Lemma lem7675289 {B : Type'} : (term122 B) = (term122 B).
Proof. exact (MK_COMB (@lem7675288 B) (@lem7675282 B)). Qed.
Lemma lem7675290 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7675291 {B : Type'} : (term165 B) = (term165 B).
Proof. exact (MK_COMB (@lem7675290) (@lem7675289 B)). Qed.
Lemma lem7675296 {A B : Type'} (r : nat) : ((term32 r) = ((term47 A B r) = r)) = ((term32 r) = ((term47 A B r) = r)).
Proof. exact (eq_refl ((term32 r) = ((term47 A B r) = r))). Qed.
Lemma lem7675297 {A B : Type'} : (term49 A B) = (term49 A B).
Proof. exact (fun_ext (fun r : nat => @lem7675296 A B r)). Qed.
Lemma lem7675298 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675299 {A B : Type'} : (term51 A B) = (term51 A B).
Proof. exact (MK_COMB (@lem7675298) (@lem7675297 A B)). Qed.
Lemma lem7675300 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7675301 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7675300 A B a)). Qed.
Lemma lem7675302 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7675303 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7675302 A B) (@lem7675301 A B)). Qed.
Lemma lem7675304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675305 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7675304) (@lem7675303 A B)). Qed.
Lemma lem7675306 {A B : Type'} : (term53 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem7675305 A B) (@lem7675299 A B)). Qed.
Lemma lem7675307 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675308 {A B : Type'} : (term54 A B) = (term54 A B).
Proof. exact (MK_COMB (@lem7675307) (@lem7675306 A B)). Qed.
Lemma lem7675309 {A B : Type'} : (term171 A B) = (term171 A B).
Proof. exact (MK_COMB (@lem7675308 A B) (@lem7675291 B)). Qed.
Lemma lem7675314 {A : Type'} (r : nat) : ((term32 r) = ((term93 A r) = r)) = ((term32 r) = ((term93 A r) = r)).
Proof. exact (eq_refl ((term32 r) = ((term93 A r) = r))). Qed.
Lemma lem7675315 {A : Type'} : (term95 A) = (term95 A).
Proof. exact (fun_ext (fun r : nat => @lem7675314 A r)). Qed.
Lemma lem7675316 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675317 {A : Type'} : (term97 A) = (term97 A).
Proof. exact (MK_COMB (@lem7675316) (@lem7675315 A)). Qed.
Lemma lem7675318 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7675319 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7675318 A a)). Qed.
Lemma lem7675320 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7675321 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7675320 A) (@lem7675319 A)). Qed.
Lemma lem7675322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675323 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7675322) (@lem7675321 A)). Qed.
Lemma lem7675324 {A : Type'} : (term99 A) = (term99 A).
Proof. exact (MK_COMB (@lem7675323 A) (@lem7675317 A)). Qed.
Lemma lem7675325 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675326 {A : Type'} : (term100 A) = (term100 A).
Proof. exact (MK_COMB (@lem7675325) (@lem7675324 A)). Qed.
Lemma lem7675327 {A B : Type'} : (term182 A B) = (term182 A B).
Proof. exact (MK_COMB (@lem7675326 A) (@lem7675309 A B)). Qed.
Lemma lem7675332 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term35 A B x x') = (term35 A B x x').
Proof. exact (eq_refl (term35 A B x x')). Qed.
Lemma lem7675333 {A B : Type'} (x : finite_diff A B) : (term37 A B x) = (term37 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7675332 A B x x')). Qed.
Lemma lem7675334 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7675335 {A B : Type'} (x : finite_diff A B) : (term39 A B x) = (term39 A B x).
Proof. exact (MK_COMB (@lem7675334) (@lem7675333 A B x)). Qed.
Lemma lem7675336 {A B : Type'} : (term41 A B) = (term41 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7675335 A B x)). Qed.
Lemma lem7675337 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7675338 {A B : Type'} : (term42 A B) = (term42 A B).
Proof. exact (MK_COMB (@lem7675337 A B) (@lem7675336 A B)). Qed.
Lemma lem7675339 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7675340 {A B : Type'} : (term43 A B) = (term43 A B).
Proof. exact (MK_COMB (@lem7675339) (@lem7675338 A B)). Qed.
Lemma lem7675341 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675342 {A B : Type'} : (term44 A B) = (term44 A B).
Proof. exact (MK_COMB (@lem7675341) (@lem7675340 A B)). Qed.
Lemma lem7675343 {A B : Type'} : (term183 A B) = (term183 A B).
Proof. exact (MK_COMB (@lem7675342 A B) (@lem7675327 A B)). Qed.
Lemma lem7675346 {A B : Type'} : (term110 A B) = (term110 A B).
Proof. exact (eq_refl (term110 A B)). Qed.
Lemma lem7675347 {A B : Type'} : (term184 A B) = (term184 A B).
Proof. exact (MK_COMB (@lem7675346 A B) (@lem7675343 A B)). Qed.
Lemma lem7675352 {B : Type'} (r : nat) : ((term118 B r) = ((term93 B r) = r)) = ((term118 B r) = ((term93 B r) = r)).
Proof. exact (eq_refl ((term118 B r) = ((term93 B r) = r))). Qed.
Lemma lem7675353 {B : Type'} : (term120 B) = (term120 B).
Proof. exact (fun_ext (fun r : nat => @lem7675352 B r)). Qed.
Lemma lem7675354 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675355 {B : Type'} : (term121 B) = (term121 B).
Proof. exact (MK_COMB (@lem7675354) (@lem7675353 B)). Qed.
Lemma lem7675356 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7675357 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7675356 B a)). Qed.
Lemma lem7675358 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7675359 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7675358 B) (@lem7675357 B)). Qed.
Lemma lem7675360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675361 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7675360) (@lem7675359 B)). Qed.
Lemma lem7675362 {B : Type'} : (term122 B) = (term122 B).
Proof. exact (MK_COMB (@lem7675361 B) (@lem7675355 B)). Qed.
Lemma lem7675363 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7675364 {B : Type'} : (term165 B) = (term165 B).
Proof. exact (MK_COMB (@lem7675363) (@lem7675362 B)). Qed.
Lemma lem7675369 {A B : Type'} (r : nat) : ((term62 A B r) = ((term47 A B r) = r)) = ((term62 A B r) = ((term47 A B r) = r)).
Proof. exact (eq_refl ((term62 A B r) = ((term47 A B r) = r))). Qed.
Lemma lem7675370 {A B : Type'} : (term71 A B) = (term71 A B).
Proof. exact (fun_ext (fun r : nat => @lem7675369 A B r)). Qed.
Lemma lem7675371 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675372 {A B : Type'} : (term72 A B) = (term72 A B).
Proof. exact (MK_COMB (@lem7675371) (@lem7675370 A B)). Qed.
Lemma lem7675373 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7675374 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7675373 A B a)). Qed.
Lemma lem7675375 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7675376 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7675375 A B) (@lem7675374 A B)). Qed.
Lemma lem7675377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675378 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7675377) (@lem7675376 A B)). Qed.
Lemma lem7675379 {A B : Type'} : (term73 A B) = (term73 A B).
Proof. exact (MK_COMB (@lem7675378 A B) (@lem7675372 A B)). Qed.
Lemma lem7675380 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675381 {A B : Type'} : (term74 A B) = (term74 A B).
Proof. exact (MK_COMB (@lem7675380) (@lem7675379 A B)). Qed.
Lemma lem7675382 {A B : Type'} : (term166 A B) = (term166 A B).
Proof. exact (MK_COMB (@lem7675381 A B) (@lem7675364 B)). Qed.
Lemma lem7675387 {A : Type'} (r : nat) : ((term32 r) = ((term93 A r) = r)) = ((term32 r) = ((term93 A r) = r)).
Proof. exact (eq_refl ((term32 r) = ((term93 A r) = r))). Qed.
Lemma lem7675388 {A : Type'} : (term95 A) = (term95 A).
Proof. exact (fun_ext (fun r : nat => @lem7675387 A r)). Qed.
Lemma lem7675389 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675390 {A : Type'} : (term97 A) = (term97 A).
Proof. exact (MK_COMB (@lem7675389) (@lem7675388 A)). Qed.
Lemma lem7675391 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7675392 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7675391 A a)). Qed.
Lemma lem7675393 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7675394 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7675393 A) (@lem7675392 A)). Qed.
Lemma lem7675395 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675396 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7675395) (@lem7675394 A)). Qed.
Lemma lem7675397 {A : Type'} : (term99 A) = (term99 A).
Proof. exact (MK_COMB (@lem7675396 A) (@lem7675390 A)). Qed.
Lemma lem7675398 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675399 {A : Type'} : (term100 A) = (term100 A).
Proof. exact (MK_COMB (@lem7675398) (@lem7675397 A)). Qed.
Lemma lem7675400 {A B : Type'} : (term178 A B) = (term178 A B).
Proof. exact (MK_COMB (@lem7675399 A) (@lem7675382 A B)). Qed.
Lemma lem7675405 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term63 A B x x') = (term63 A B x x').
Proof. exact (eq_refl (term63 A B x x')). Qed.
Lemma lem7675406 {A B : Type'} (x : finite_diff A B) : (term64 A B x) = (term64 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7675405 A B x x')). Qed.
Lemma lem7675407 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7675408 {A B : Type'} (x : finite_diff A B) : (term65 A B x) = (term65 A B x).
Proof. exact (MK_COMB (@lem7675407) (@lem7675406 A B x)). Qed.
Lemma lem7675409 {A B : Type'} : (term66 A B) = (term66 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7675408 A B x)). Qed.
Lemma lem7675410 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7675411 {A B : Type'} : (term67 A B) = (term67 A B).
Proof. exact (MK_COMB (@lem7675410 A B) (@lem7675409 A B)). Qed.
Lemma lem7675412 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7675413 {A B : Type'} : (term68 A B) = (term68 A B).
Proof. exact (MK_COMB (@lem7675412) (@lem7675411 A B)). Qed.
Lemma lem7675414 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675415 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (MK_COMB (@lem7675414) (@lem7675413 A B)). Qed.
Lemma lem7675416 {A B : Type'} : (term179 A B) = (term179 A B).
Proof. exact (MK_COMB (@lem7675415 A B) (@lem7675400 A B)). Qed.
Lemma lem7675421 {A B : Type'} : (term103 A B) = (term103 A B).
Proof. exact (eq_refl (term103 A B)). Qed.
Lemma lem7675422 {A B : Type'} : (term180 A B) = (term180 A B).
Proof. exact (MK_COMB (@lem7675421 A B) (@lem7675416 A B)). Qed.
Lemma lem7675423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675424 {A B : Type'} : (term181 A B) = (term181 A B).
Proof. exact (MK_COMB (@lem7675423) (@lem7675422 A B)). Qed.
Lemma lem7675425 {A B : Type'} : (term185 A B) = (term185 A B).
Proof. exact (MK_COMB (@lem7675424 A B) (@lem7675347 A B)). Qed.
Lemma lem7675428 {A : Type'} : (term160 A) = (term160 A).
Proof. exact (eq_refl (term160 A)). Qed.
Lemma lem7675429 {A B : Type'} : (term186 A B) = (term186 A B).
Proof. exact (MK_COMB (@lem7675428 A) (@lem7675425 A B)). Qed.
Lemma lem7675434 {B : Type'} (r : nat) : ((term118 B r) = ((term93 B r) = r)) = ((term118 B r) = ((term93 B r) = r)).
Proof. exact (eq_refl ((term118 B r) = ((term93 B r) = r))). Qed.
Lemma lem7675435 {B : Type'} : (term120 B) = (term120 B).
Proof. exact (fun_ext (fun r : nat => @lem7675434 B r)). Qed.
Lemma lem7675436 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675437 {B : Type'} : (term121 B) = (term121 B).
Proof. exact (MK_COMB (@lem7675436) (@lem7675435 B)). Qed.
Lemma lem7675438 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7675439 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7675438 B a)). Qed.
Lemma lem7675440 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7675441 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7675440 B) (@lem7675439 B)). Qed.
Lemma lem7675442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675443 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7675442) (@lem7675441 B)). Qed.
Lemma lem7675444 {B : Type'} : (term122 B) = (term122 B).
Proof. exact (MK_COMB (@lem7675443 B) (@lem7675437 B)). Qed.
Lemma lem7675445 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7675446 {B : Type'} : (term165 B) = (term165 B).
Proof. exact (MK_COMB (@lem7675445) (@lem7675444 B)). Qed.
Lemma lem7675451 {A B : Type'} (r : nat) : ((term32 r) = ((term47 A B r) = r)) = ((term32 r) = ((term47 A B r) = r)).
Proof. exact (eq_refl ((term32 r) = ((term47 A B r) = r))). Qed.
Lemma lem7675452 {A B : Type'} : (term49 A B) = (term49 A B).
Proof. exact (fun_ext (fun r : nat => @lem7675451 A B r)). Qed.
Lemma lem7675453 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675454 {A B : Type'} : (term51 A B) = (term51 A B).
Proof. exact (MK_COMB (@lem7675453) (@lem7675452 A B)). Qed.
Lemma lem7675455 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7675456 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7675455 A B a)). Qed.
Lemma lem7675457 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7675458 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7675457 A B) (@lem7675456 A B)). Qed.
Lemma lem7675459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675460 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7675459) (@lem7675458 A B)). Qed.
Lemma lem7675461 {A B : Type'} : (term53 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem7675460 A B) (@lem7675454 A B)). Qed.
Lemma lem7675462 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675463 {A B : Type'} : (term54 A B) = (term54 A B).
Proof. exact (MK_COMB (@lem7675462) (@lem7675461 A B)). Qed.
Lemma lem7675464 {A B : Type'} : (term171 A B) = (term171 A B).
Proof. exact (MK_COMB (@lem7675463 A B) (@lem7675446 B)). Qed.
Lemma lem7675469 {A : Type'} (r : nat) : ((term118 A r) = ((term93 A r) = r)) = ((term118 A r) = ((term93 A r) = r)).
Proof. exact (eq_refl ((term118 A r) = ((term93 A r) = r))). Qed.
Lemma lem7675470 {A : Type'} : (term120 A) = (term120 A).
Proof. exact (fun_ext (fun r : nat => @lem7675469 A r)). Qed.
Lemma lem7675471 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675472 {A : Type'} : (term121 A) = (term121 A).
Proof. exact (MK_COMB (@lem7675471) (@lem7675470 A)). Qed.
Lemma lem7675473 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7675474 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7675473 A a)). Qed.
Lemma lem7675475 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7675476 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7675475 A) (@lem7675474 A)). Qed.
Lemma lem7675477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675478 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7675477) (@lem7675476 A)). Qed.
Lemma lem7675479 {A : Type'} : (term122 A) = (term122 A).
Proof. exact (MK_COMB (@lem7675478 A) (@lem7675472 A)). Qed.
Lemma lem7675480 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675481 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (MK_COMB (@lem7675480) (@lem7675479 A)). Qed.
Lemma lem7675482 {A B : Type'} : (term172 A B) = (term172 A B).
Proof. exact (MK_COMB (@lem7675481 A) (@lem7675464 A B)). Qed.
Lemma lem7675487 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term35 A B x x') = (term35 A B x x').
Proof. exact (eq_refl (term35 A B x x')). Qed.
Lemma lem7675488 {A B : Type'} (x : finite_diff A B) : (term37 A B x) = (term37 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7675487 A B x x')). Qed.
Lemma lem7675489 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7675490 {A B : Type'} (x : finite_diff A B) : (term39 A B x) = (term39 A B x).
Proof. exact (MK_COMB (@lem7675489) (@lem7675488 A B x)). Qed.
Lemma lem7675491 {A B : Type'} : (term41 A B) = (term41 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7675490 A B x)). Qed.
Lemma lem7675492 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7675493 {A B : Type'} : (term42 A B) = (term42 A B).
Proof. exact (MK_COMB (@lem7675492 A B) (@lem7675491 A B)). Qed.
Lemma lem7675494 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7675495 {A B : Type'} : (term43 A B) = (term43 A B).
Proof. exact (MK_COMB (@lem7675494) (@lem7675493 A B)). Qed.
Lemma lem7675496 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675497 {A B : Type'} : (term44 A B) = (term44 A B).
Proof. exact (MK_COMB (@lem7675496) (@lem7675495 A B)). Qed.
Lemma lem7675498 {A B : Type'} : (term173 A B) = (term173 A B).
Proof. exact (MK_COMB (@lem7675497 A B) (@lem7675482 A B)). Qed.
Lemma lem7675501 {A B : Type'} : (term110 A B) = (term110 A B).
Proof. exact (eq_refl (term110 A B)). Qed.
Lemma lem7675502 {A B : Type'} : (term174 A B) = (term174 A B).
Proof. exact (MK_COMB (@lem7675501 A B) (@lem7675498 A B)). Qed.
Lemma lem7675507 {B : Type'} (r : nat) : ((term118 B r) = ((term93 B r) = r)) = ((term118 B r) = ((term93 B r) = r)).
Proof. exact (eq_refl ((term118 B r) = ((term93 B r) = r))). Qed.
Lemma lem7675508 {B : Type'} : (term120 B) = (term120 B).
Proof. exact (fun_ext (fun r : nat => @lem7675507 B r)). Qed.
Lemma lem7675509 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675510 {B : Type'} : (term121 B) = (term121 B).
Proof. exact (MK_COMB (@lem7675509) (@lem7675508 B)). Qed.
Lemma lem7675511 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7675512 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7675511 B a)). Qed.
Lemma lem7675513 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7675514 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7675513 B) (@lem7675512 B)). Qed.
Lemma lem7675515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675516 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7675515) (@lem7675514 B)). Qed.
Lemma lem7675517 {B : Type'} : (term122 B) = (term122 B).
Proof. exact (MK_COMB (@lem7675516 B) (@lem7675510 B)). Qed.
Lemma lem7675518 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7675519 {B : Type'} : (term165 B) = (term165 B).
Proof. exact (MK_COMB (@lem7675518) (@lem7675517 B)). Qed.
Lemma lem7675524 {A B : Type'} (r : nat) : ((term62 A B r) = ((term47 A B r) = r)) = ((term62 A B r) = ((term47 A B r) = r)).
Proof. exact (eq_refl ((term62 A B r) = ((term47 A B r) = r))). Qed.
Lemma lem7675525 {A B : Type'} : (term71 A B) = (term71 A B).
Proof. exact (fun_ext (fun r : nat => @lem7675524 A B r)). Qed.
Lemma lem7675526 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675527 {A B : Type'} : (term72 A B) = (term72 A B).
Proof. exact (MK_COMB (@lem7675526) (@lem7675525 A B)). Qed.
Lemma lem7675528 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7675529 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7675528 A B a)). Qed.
Lemma lem7675530 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7675531 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7675530 A B) (@lem7675529 A B)). Qed.
Lemma lem7675532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675533 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7675532) (@lem7675531 A B)). Qed.
Lemma lem7675534 {A B : Type'} : (term73 A B) = (term73 A B).
Proof. exact (MK_COMB (@lem7675533 A B) (@lem7675527 A B)). Qed.
Lemma lem7675535 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675536 {A B : Type'} : (term74 A B) = (term74 A B).
Proof. exact (MK_COMB (@lem7675535) (@lem7675534 A B)). Qed.
Lemma lem7675537 {A B : Type'} : (term166 A B) = (term166 A B).
Proof. exact (MK_COMB (@lem7675536 A B) (@lem7675519 B)). Qed.
Lemma lem7675542 {A : Type'} (r : nat) : ((term118 A r) = ((term93 A r) = r)) = ((term118 A r) = ((term93 A r) = r)).
Proof. exact (eq_refl ((term118 A r) = ((term93 A r) = r))). Qed.
Lemma lem7675543 {A : Type'} : (term120 A) = (term120 A).
Proof. exact (fun_ext (fun r : nat => @lem7675542 A r)). Qed.
Lemma lem7675544 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7675545 {A : Type'} : (term121 A) = (term121 A).
Proof. exact (MK_COMB (@lem7675544) (@lem7675543 A)). Qed.
Lemma lem7675546 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7675547 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7675546 A a)). Qed.
Lemma lem7675548 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7675549 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7675548 A) (@lem7675547 A)). Qed.
Lemma lem7675550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675551 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7675550) (@lem7675549 A)). Qed.
Lemma lem7675552 {A : Type'} : (term122 A) = (term122 A).
Proof. exact (MK_COMB (@lem7675551 A) (@lem7675545 A)). Qed.
Lemma lem7675553 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675554 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (MK_COMB (@lem7675553) (@lem7675552 A)). Qed.
Lemma lem7675555 {A B : Type'} : (term167 A B) = (term167 A B).
Proof. exact (MK_COMB (@lem7675554 A) (@lem7675537 A B)). Qed.
Lemma lem7675560 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term63 A B x x') = (term63 A B x x').
Proof. exact (eq_refl (term63 A B x x')). Qed.
Lemma lem7675561 {A B : Type'} (x : finite_diff A B) : (term64 A B x) = (term64 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7675560 A B x x')). Qed.
Lemma lem7675562 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7675563 {A B : Type'} (x : finite_diff A B) : (term65 A B x) = (term65 A B x).
Proof. exact (MK_COMB (@lem7675562) (@lem7675561 A B x)). Qed.
Lemma lem7675564 {A B : Type'} : (term66 A B) = (term66 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7675563 A B x)). Qed.
Lemma lem7675565 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7675566 {A B : Type'} : (term67 A B) = (term67 A B).
Proof. exact (MK_COMB (@lem7675565 A B) (@lem7675564 A B)). Qed.
Lemma lem7675567 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7675568 {A B : Type'} : (term68 A B) = (term68 A B).
Proof. exact (MK_COMB (@lem7675567) (@lem7675566 A B)). Qed.
Lemma lem7675569 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7675570 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (MK_COMB (@lem7675569) (@lem7675568 A B)). Qed.
Lemma lem7675571 {A B : Type'} : (term168 A B) = (term168 A B).
Proof. exact (MK_COMB (@lem7675570 A B) (@lem7675555 A B)). Qed.
Lemma lem7675576 {A B : Type'} : (term103 A B) = (term103 A B).
Proof. exact (eq_refl (term103 A B)). Qed.
Lemma lem7675577 {A B : Type'} : (term169 A B) = (term169 A B).
Proof. exact (MK_COMB (@lem7675576 A B) (@lem7675571 A B)). Qed.
Lemma lem7675578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675579 {A B : Type'} : (term170 A B) = (term170 A B).
Proof. exact (MK_COMB (@lem7675578) (@lem7675577 A B)). Qed.
Lemma lem7675580 {A B : Type'} : (term175 A B) = (term175 A B).
Proof. exact (MK_COMB (@lem7675579 A B) (@lem7675502 A B)). Qed.
Lemma lem7675585 {A : Type'} : (term147 A) = (term147 A).
Proof. exact (eq_refl (term147 A)). Qed.
Lemma lem7675586 {A B : Type'} : (term176 A B) = (term176 A B).
Proof. exact (MK_COMB (@lem7675585 A) (@lem7675580 A B)). Qed.
Lemma lem7675587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675588 {A B : Type'} : (term177 A B) = (term177 A B).
Proof. exact (MK_COMB (@lem7675587) (@lem7675586 A B)). Qed.
Lemma lem7675589 {A B : Type'} : (term187 A B) = (term187 A B).
Proof. exact (MK_COMB (@lem7675588 A B) (@lem7675429 A B)). Qed.
Lemma lem7675594 {B : Type'} : (term147 B) = (term147 B).
Proof. exact (eq_refl (term147 B)). Qed.
Lemma lem7675595 {A B : Type'} : (term199 A B) = (term199 A B).
Proof. exact (MK_COMB (@lem7675594 B) (@lem7675589 A B)). Qed.
Lemma lem7675596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7675597 {A B : Type'} : (term200 A B) = (term200 A B).
Proof. exact (MK_COMB (@lem7675596) (@lem7675595 A B)). Qed.
Lemma lem7675598 {A B : Type'} : (term191 A B) = (term191 A B).
Proof. exact (MK_COMB (@lem7675597 A B) (@lem7675274 A B)). Qed.
Lemma lem7675599 {A B : Type'} : (term201 A B) = (term201 A B).
Proof. exact (eq_refl (term201 A B)). Qed.
Lemma lem7675600 {A B : Type'} : ((term135 A B) = (term191 A B)) = ((term135 A B) = (term191 A B)).
Proof. exact (MK_COMB (@lem7675599 A B) (@lem7675598 A B)). Qed.
Lemma lem7675601 {A B : Type'} : (term135 A B) = (term191 A B).
Proof. exact (EQ_MP (@lem7675600 A B) (@lem7674955 A B)). Qed.
Lemma lem7675602 {A B : Type'} : (term202 A B) = (term202 A B).
Proof. exact (eq_refl (term202 A B)). Qed.
Lemma lem7675603 {A B : Type'} : ((term82 A B) = (term135 A B)) = ((term82 A B) = (term191 A B)).
Proof. exact (MK_COMB (@lem7675602 A B) (@lem7675601 A B)). Qed.
Lemma lem7675604 {A B : Type'} : (term82 A B) = (term191 A B).
Proof. exact (EQ_MP (@lem7675603 A B) (@lem7674018 A B)). Qed.
Lemma lem7675605 {A B : Type'} : (term203 A B) = (term203 A B).
Proof. exact (eq_refl (term203 A B)). Qed.
Lemma lem7675606 {A B : Type'} : ((term19 A B) = (term82 A B)) = ((term19 A B) = (term191 A B)).
Proof. exact (MK_COMB (@lem7675605 A B) (@lem7675604 A B)). Qed.
Lemma lem7675607 {A B : Type'} : (term19 A B) = (term191 A B).
Proof. exact (EQ_MP (@lem7675606 A B) (@lem7673553 A B)). Qed.
Lemma lem7676148 {A B : Type'} : (term6 A B) = (term191 A B).
Proof. exact (TRANS (@lem7673262 A B) (@lem7675607 A B)). Qed.
Lemma lem7676149 {A B : Type'} : (term191 A B) = (term6 A B).
Proof. exact (SYM (@lem7676148 A B)). Qed.
Lemma lem7676151 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7676152 {A B : Type'} : (term191 A B) = (term204 A B).
Proof. exact (@lem7676151 (term191 A B)). Qed.
Lemma lem7676153 {A B : Type'} : (term204 A B) = (term191 A B).
Proof. exact (SYM (@lem7676152 A B)). Qed.
Lemma lem7676154 {A B : Type'} (h1 : term205 A B) : term205 A B.
Proof. exact (h1). Qed.
Lemma lem7676157 {B : Type'} : (term206 B) = (term83 B).
Proof. exact (@lem16933 (term83 B)). Qed.
Lemma lem7676160 {A : Type'} : (term206 A) = (term83 A).
Proof. exact (@lem16933 (term83 A)). Qed.
Lemma lem7676163 {A B : Type'} : (term207 A B) = (term20 A B).
Proof. exact (@lem16933 (term20 A B)). Qed.
Lemma lem7676170 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term208 A B x x') = (term209 A B x x').
Proof. exact (@lem17045 (x = (@mk_finite_diff A B x')) (term62 A B x')). Qed.
Lemma lem7676171 (P : nat -> Prop) : (term210 P) = (term211 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem7676172 {A B : Type'} (x : finite_diff A B) : (term212 A B x) = (term213 A B x).
Proof. exact (@lem7676171 (term64 A B x)). Qed.
Lemma lem7676173 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term214 A B x x') = (term63 A B x x').
Proof. exact (eq_refl (term214 A B x x')). Qed.
Lemma lem7676174 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7676175 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term215 A B x x') = (term208 A B x x').
Proof. exact (MK_COMB (@lem7676174) (@lem7676173 A B x x')). Qed.
Lemma lem7676176 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term215 A B x x') = (term209 A B x x').
Proof. exact (TRANS (@lem7676175 A B x x') (@lem7676170 A B x x')). Qed.
Lemma lem7676177 {A B : Type'} (x : finite_diff A B) : (term216 A B x) = (term217 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7676176 A B x x')). Qed.
Lemma lem7676178 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676179 {A B : Type'} (x : finite_diff A B) : (term213 A B x) = (term218 A B x).
Proof. exact (MK_COMB (@lem7676178) (@lem7676177 A B x)). Qed.
Lemma lem7676180 {A B : Type'} (x : finite_diff A B) : (term212 A B x) = (term218 A B x).
Proof. exact (TRANS (@lem7676172 A B x) (@lem7676179 A B x)). Qed.
Lemma lem7676181 {A B : Type'} (P : type31 A B) : (term219 A B P) = (term220 A B P).
Proof. exact (@lem18392 (finite_diff A B) P). Qed.
Lemma lem7676182 {A B : Type'} : (term68 A B) = (term221 A B).
Proof. exact (@lem7676181 A B (term66 A B)). Qed.
Lemma lem7676183 {A B : Type'} (x : finite_diff A B) : (term222 A B x) = (term65 A B x).
Proof. exact (eq_refl (term222 A B x)). Qed.
Lemma lem7676184 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7676185 {A B : Type'} (x : finite_diff A B) : (term223 A B x) = (term212 A B x).
Proof. exact (MK_COMB (@lem7676184) (@lem7676183 A B x)). Qed.
Lemma lem7676186 {A B : Type'} (x : finite_diff A B) : (term223 A B x) = (term218 A B x).
Proof. exact (TRANS (@lem7676185 A B x) (@lem7676180 A B x)). Qed.
Lemma lem7676187 {A B : Type'} : (term224 A B) = (term225 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7676186 A B x)). Qed.
Lemma lem7676188 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7676189 {A B : Type'} : (term221 A B) = (term226 A B).
Proof. exact (MK_COMB (@lem7676188 A B) (@lem7676187 A B)). Qed.
Lemma lem7676190 {A B : Type'} : (term68 A B) = (term226 A B).
Proof. exact (TRANS (@lem7676182 A B) (@lem7676189 A B)). Qed.
Lemma lem7676191 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7676192 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7676191 A a)). Qed.
Lemma lem7676193 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7676194 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7676193 A) (@lem7676192 A)). Qed.
Lemma lem7676209 {A : Type'} (r : nat) : ((term118 A r) = ((term93 A r) = r)) = (term227 A r).
Proof. exact (@lem17784 (term118 A r) ((term93 A r) = r)). Qed.
Lemma lem7676210 {A : Type'} : (term120 A) = (term228 A).
Proof. exact (fun_ext (fun r : nat => @lem7676209 A r)). Qed.
Lemma lem7676211 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676212 {A : Type'} : (term121 A) = (term229 A).
Proof. exact (MK_COMB (@lem7676211) (@lem7676210 A)). Qed.
Lemma lem7676213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676214 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7676213) (@lem7676194 A)). Qed.
Lemma lem7676215 {A : Type'} : (term122 A) = (term230 A).
Proof. exact (MK_COMB (@lem7676214 A) (@lem7676212 A)). Qed.
Lemma lem7676216 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7676217 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7676216 A B a)). Qed.
Lemma lem7676218 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7676219 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7676218 A B) (@lem7676217 A B)). Qed.
Lemma lem7676234 {A B : Type'} (r : nat) : ((term62 A B r) = ((term47 A B r) = r)) = (term231 A B r).
Proof. exact (@lem17784 (term62 A B r) ((term47 A B r) = r)). Qed.
Lemma lem7676235 {A B : Type'} : (term71 A B) = (term232 A B).
Proof. exact (fun_ext (fun r : nat => @lem7676234 A B r)). Qed.
Lemma lem7676236 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676237 {A B : Type'} : (term72 A B) = (term233 A B).
Proof. exact (MK_COMB (@lem7676236) (@lem7676235 A B)). Qed.
Lemma lem7676238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676239 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7676238) (@lem7676219 A B)). Qed.
Lemma lem7676240 {A B : Type'} : (term73 A B) = (term234 A B).
Proof. exact (MK_COMB (@lem7676239 A B) (@lem7676237 A B)). Qed.
Lemma lem7676241 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7676242 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7676241 B a)). Qed.
Lemma lem7676243 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7676244 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7676243 B) (@lem7676242 B)). Qed.
Lemma lem7676259 {B : Type'} (r : nat) : ((term118 B r) = ((term93 B r) = r)) = (term227 B r).
Proof. exact (@lem17784 (term118 B r) ((term93 B r) = r)). Qed.
Lemma lem7676260 {B : Type'} : (term120 B) = (term228 B).
Proof. exact (fun_ext (fun r : nat => @lem7676259 B r)). Qed.
Lemma lem7676261 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676262 {B : Type'} : (term121 B) = (term229 B).
Proof. exact (MK_COMB (@lem7676261) (@lem7676260 B)). Qed.
Lemma lem7676263 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676264 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7676263) (@lem7676244 B)). Qed.
Lemma lem7676265 {B : Type'} : (term122 B) = (term230 B).
Proof. exact (MK_COMB (@lem7676264 B) (@lem7676262 B)). Qed.
Lemma lem7676266 {B : Type'} : (term235 B) = (term122 B).
Proof. exact (@lem16933 (term122 B)). Qed.
Lemma lem7676267 {B : Type'} : (term235 B) = (term230 B).
Proof. exact (TRANS (@lem7676266 B) (@lem7676265 B)). Qed.
Lemma lem7676268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676269 {A B : Type'} : (term236 A B) = (term237 A B).
Proof. exact (MK_COMB (@lem7676268) (@lem7676240 A B)). Qed.
Lemma lem7676270 {A B : Type'} : (term238 A B) = (term239 A B).
Proof. exact (MK_COMB (@lem7676269 A B) (@lem7676267 B)). Qed.
Lemma lem7676271 {A B : Type'} : (term240 A B) = (term238 A B).
Proof. exact (@lem17362 (term73 A B) (term165 B)). Qed.
Lemma lem7676272 {A B : Type'} : (term240 A B) = (term239 A B).
Proof. exact (TRANS (@lem7676271 A B) (@lem7676270 A B)). Qed.
Lemma lem7676273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676274 {A : Type'} : (term241 A) = (term242 A).
Proof. exact (MK_COMB (@lem7676273) (@lem7676215 A)). Qed.
Lemma lem7676275 {A B : Type'} : (term243 A B) = (term244 A B).
Proof. exact (MK_COMB (@lem7676274 A) (@lem7676272 A B)). Qed.
Lemma lem7676276 {A B : Type'} : (term245 A B) = (term243 A B).
Proof. exact (@lem17362 (term122 A) (term166 A B)). Qed.
Lemma lem7676277 {A B : Type'} : (term245 A B) = (term244 A B).
Proof. exact (TRANS (@lem7676276 A B) (@lem7676275 A B)). Qed.
Lemma lem7676278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676279 {A B : Type'} : (term246 A B) = (term247 A B).
Proof. exact (MK_COMB (@lem7676278) (@lem7676190 A B)). Qed.
Lemma lem7676280 {A B : Type'} : (term248 A B) = (term249 A B).
Proof. exact (MK_COMB (@lem7676279 A B) (@lem7676277 A B)). Qed.
Lemma lem7676281 {A B : Type'} : (term250 A B) = (term248 A B).
Proof. exact (@lem17362 (term68 A B) (term167 A B)). Qed.
Lemma lem7676282 {A B : Type'} : (term250 A B) = (term249 A B).
Proof. exact (TRANS (@lem7676281 A B) (@lem7676280 A B)). Qed.
Lemma lem7676283 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676284 {A B : Type'} : (term251 A B) = (term252 A B).
Proof. exact (MK_COMB (@lem7676283) (@lem7676163 A B)). Qed.
Lemma lem7676285 {A B : Type'} : (term253 A B) = (term254 A B).
Proof. exact (MK_COMB (@lem7676284 A B) (@lem7676282 A B)). Qed.
Lemma lem7676286 {A B : Type'} : (term255 A B) = (term253 A B).
Proof. exact (@lem17160 (term256 A B) (term168 A B)). Qed.
Lemma lem7676287 {A B : Type'} : (term255 A B) = (term254 A B).
Proof. exact (TRANS (@lem7676286 A B) (@lem7676285 A B)). Qed.
Lemma lem7676295 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term257 A B x x') = (term258 A B x x').
Proof. exact (@lem17045 (x = (@mk_finite_diff A B x')) (term32 x')). Qed.
Lemma lem7676296 (P : nat -> Prop) : (term210 P) = (term211 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem7676297 {A B : Type'} (x : finite_diff A B) : (term259 A B x) = (term260 A B x).
Proof. exact (@lem7676296 (term37 A B x)). Qed.
Lemma lem7676298 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term261 A B x x') = (term35 A B x x').
Proof. exact (eq_refl (term261 A B x x')). Qed.
Lemma lem7676299 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7676300 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term262 A B x x') = (term257 A B x x').
Proof. exact (MK_COMB (@lem7676299) (@lem7676298 A B x x')). Qed.
Lemma lem7676301 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term262 A B x x') = (term258 A B x x').
Proof. exact (TRANS (@lem7676300 A B x x') (@lem7676295 A B x x')). Qed.
Lemma lem7676302 {A B : Type'} (x : finite_diff A B) : (term263 A B x) = (term264 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7676301 A B x x')). Qed.
Lemma lem7676303 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676304 {A B : Type'} (x : finite_diff A B) : (term260 A B x) = (term265 A B x).
Proof. exact (MK_COMB (@lem7676303) (@lem7676302 A B x)). Qed.
Lemma lem7676305 {A B : Type'} (x : finite_diff A B) : (term259 A B x) = (term265 A B x).
Proof. exact (TRANS (@lem7676297 A B x) (@lem7676304 A B x)). Qed.
Lemma lem7676306 {A B : Type'} (P : type31 A B) : (term219 A B P) = (term220 A B P).
Proof. exact (@lem18392 (finite_diff A B) P). Qed.
Lemma lem7676307 {A B : Type'} : (term43 A B) = (term266 A B).
Proof. exact (@lem7676306 A B (term41 A B)). Qed.
Lemma lem7676308 {A B : Type'} (x : finite_diff A B) : (term267 A B x) = (term39 A B x).
Proof. exact (eq_refl (term267 A B x)). Qed.
Lemma lem7676309 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7676310 {A B : Type'} (x : finite_diff A B) : (term268 A B x) = (term259 A B x).
Proof. exact (MK_COMB (@lem7676309) (@lem7676308 A B x)). Qed.
Lemma lem7676311 {A B : Type'} (x : finite_diff A B) : (term268 A B x) = (term265 A B x).
Proof. exact (TRANS (@lem7676310 A B x) (@lem7676305 A B x)). Qed.
Lemma lem7676312 {A B : Type'} : (term269 A B) = (term270 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7676311 A B x)). Qed.
Lemma lem7676313 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7676314 {A B : Type'} : (term266 A B) = (term271 A B).
Proof. exact (MK_COMB (@lem7676313 A B) (@lem7676312 A B)). Qed.
Lemma lem7676315 {A B : Type'} : (term43 A B) = (term271 A B).
Proof. exact (TRANS (@lem7676307 A B) (@lem7676314 A B)). Qed.
Lemma lem7676316 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7676317 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7676316 A a)). Qed.
Lemma lem7676318 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7676319 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7676318 A) (@lem7676317 A)). Qed.
Lemma lem7676334 {A : Type'} (r : nat) : ((term118 A r) = ((term93 A r) = r)) = (term227 A r).
Proof. exact (@lem17784 (term118 A r) ((term93 A r) = r)). Qed.
Lemma lem7676335 {A : Type'} : (term120 A) = (term228 A).
Proof. exact (fun_ext (fun r : nat => @lem7676334 A r)). Qed.
Lemma lem7676336 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676337 {A : Type'} : (term121 A) = (term229 A).
Proof. exact (MK_COMB (@lem7676336) (@lem7676335 A)). Qed.
Lemma lem7676338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676339 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7676338) (@lem7676319 A)). Qed.
Lemma lem7676340 {A : Type'} : (term122 A) = (term230 A).
Proof. exact (MK_COMB (@lem7676339 A) (@lem7676337 A)). Qed.
Lemma lem7676341 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7676342 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7676341 A B a)). Qed.
Lemma lem7676343 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7676344 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7676343 A B) (@lem7676342 A B)). Qed.
Lemma lem7676359 {A B : Type'} (r : nat) : ((term32 r) = ((term47 A B r) = r)) = (term272 A B r).
Proof. exact (@lem17784 (term32 r) ((term47 A B r) = r)). Qed.
Lemma lem7676360 {A B : Type'} : (term49 A B) = (term273 A B).
Proof. exact (fun_ext (fun r : nat => @lem7676359 A B r)). Qed.
Lemma lem7676361 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676362 {A B : Type'} : (term51 A B) = (term274 A B).
Proof. exact (MK_COMB (@lem7676361) (@lem7676360 A B)). Qed.
Lemma lem7676363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676364 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7676363) (@lem7676344 A B)). Qed.
Lemma lem7676365 {A B : Type'} : (term53 A B) = (term275 A B).
Proof. exact (MK_COMB (@lem7676364 A B) (@lem7676362 A B)). Qed.
Lemma lem7676366 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7676367 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7676366 B a)). Qed.
Lemma lem7676368 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7676369 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7676368 B) (@lem7676367 B)). Qed.
Lemma lem7676384 {B : Type'} (r : nat) : ((term118 B r) = ((term93 B r) = r)) = (term227 B r).
Proof. exact (@lem17784 (term118 B r) ((term93 B r) = r)). Qed.
Lemma lem7676385 {B : Type'} : (term120 B) = (term228 B).
Proof. exact (fun_ext (fun r : nat => @lem7676384 B r)). Qed.
Lemma lem7676386 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676387 {B : Type'} : (term121 B) = (term229 B).
Proof. exact (MK_COMB (@lem7676386) (@lem7676385 B)). Qed.
Lemma lem7676388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676389 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7676388) (@lem7676369 B)). Qed.
Lemma lem7676390 {B : Type'} : (term122 B) = (term230 B).
Proof. exact (MK_COMB (@lem7676389 B) (@lem7676387 B)). Qed.
Lemma lem7676391 {B : Type'} : (term235 B) = (term122 B).
Proof. exact (@lem16933 (term122 B)). Qed.
Lemma lem7676392 {B : Type'} : (term235 B) = (term230 B).
Proof. exact (TRANS (@lem7676391 B) (@lem7676390 B)). Qed.
Lemma lem7676393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676394 {A B : Type'} : (term276 A B) = (term277 A B).
Proof. exact (MK_COMB (@lem7676393) (@lem7676365 A B)). Qed.
Lemma lem7676395 {A B : Type'} : (term278 A B) = (term279 A B).
Proof. exact (MK_COMB (@lem7676394 A B) (@lem7676392 B)). Qed.
Lemma lem7676396 {A B : Type'} : (term280 A B) = (term278 A B).
Proof. exact (@lem17362 (term53 A B) (term165 B)). Qed.
Lemma lem7676397 {A B : Type'} : (term280 A B) = (term279 A B).
Proof. exact (TRANS (@lem7676396 A B) (@lem7676395 A B)). Qed.
Lemma lem7676398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676399 {A : Type'} : (term241 A) = (term242 A).
Proof. exact (MK_COMB (@lem7676398) (@lem7676340 A)). Qed.
Lemma lem7676400 {A B : Type'} : (term281 A B) = (term282 A B).
Proof. exact (MK_COMB (@lem7676399 A) (@lem7676397 A B)). Qed.
Lemma lem7676401 {A B : Type'} : (term283 A B) = (term281 A B).
Proof. exact (@lem17362 (term122 A) (term171 A B)). Qed.
Lemma lem7676402 {A B : Type'} : (term283 A B) = (term282 A B).
Proof. exact (TRANS (@lem7676401 A B) (@lem7676400 A B)). Qed.
Lemma lem7676403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676404 {A B : Type'} : (term284 A B) = (term285 A B).
Proof. exact (MK_COMB (@lem7676403) (@lem7676315 A B)). Qed.
Lemma lem7676405 {A B : Type'} : (term286 A B) = (term287 A B).
Proof. exact (MK_COMB (@lem7676404 A B) (@lem7676402 A B)). Qed.
Lemma lem7676406 {A B : Type'} : (term288 A B) = (term286 A B).
Proof. exact (@lem17362 (term43 A B) (term172 A B)). Qed.
Lemma lem7676407 {A B : Type'} : (term288 A B) = (term287 A B).
Proof. exact (TRANS (@lem7676406 A B) (@lem7676405 A B)). Qed.
Lemma lem7676409 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7676410 {A B : Type'} : (term290 A B) = (term291 A B).
Proof. exact (MK_COMB (@lem7676409 A B) (@lem7676407 A B)). Qed.
Lemma lem7676411 {A B : Type'} : (term292 A B) = (term290 A B).
Proof. exact (@lem17160 (term20 A B) (term173 A B)). Qed.
Lemma lem7676412 {A B : Type'} : (term292 A B) = (term291 A B).
Proof. exact (TRANS (@lem7676411 A B) (@lem7676410 A B)). Qed.
Lemma lem7676413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7676414 {A B : Type'} : (term293 A B) = (term294 A B).
Proof. exact (MK_COMB (@lem7676413) (@lem7676287 A B)). Qed.
Lemma lem7676415 {A B : Type'} : (term295 A B) = (term296 A B).
Proof. exact (MK_COMB (@lem7676414 A B) (@lem7676412 A B)). Qed.
Lemma lem7676416 {A B : Type'} : (term297 A B) = (term295 A B).
Proof. exact (@lem17045 (term169 A B) (term174 A B)). Qed.
Lemma lem7676417 {A B : Type'} : (term297 A B) = (term296 A B).
Proof. exact (TRANS (@lem7676416 A B) (@lem7676415 A B)). Qed.
Lemma lem7676418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676419 {A : Type'} : (term298 A) = (term299 A).
Proof. exact (MK_COMB (@lem7676418) (@lem7676160 A)). Qed.
Lemma lem7676420 {A B : Type'} : (term300 A B) = (term301 A B).
Proof. exact (MK_COMB (@lem7676419 A) (@lem7676417 A B)). Qed.
Lemma lem7676421 {A B : Type'} : (term302 A B) = (term300 A B).
Proof. exact (@lem17160 (term303 A) (term175 A B)). Qed.
Lemma lem7676422 {A B : Type'} : (term302 A B) = (term301 A B).
Proof. exact (TRANS (@lem7676421 A B) (@lem7676420 A B)). Qed.
Lemma lem7676426 {A B : Type'} : (term207 A B) = (term20 A B).
Proof. exact (@lem16933 (term20 A B)). Qed.
Lemma lem7676433 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term208 A B x x') = (term209 A B x x').
Proof. exact (@lem17045 (x = (@mk_finite_diff A B x')) (term62 A B x')). Qed.
Lemma lem7676434 (P : nat -> Prop) : (term210 P) = (term211 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem7676435 {A B : Type'} (x : finite_diff A B) : (term212 A B x) = (term213 A B x).
Proof. exact (@lem7676434 (term64 A B x)). Qed.
Lemma lem7676436 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term214 A B x x') = (term63 A B x x').
Proof. exact (eq_refl (term214 A B x x')). Qed.
Lemma lem7676437 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7676438 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term215 A B x x') = (term208 A B x x').
Proof. exact (MK_COMB (@lem7676437) (@lem7676436 A B x x')). Qed.
Lemma lem7676439 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term215 A B x x') = (term209 A B x x').
Proof. exact (TRANS (@lem7676438 A B x x') (@lem7676433 A B x x')). Qed.
Lemma lem7676440 {A B : Type'} (x : finite_diff A B) : (term216 A B x) = (term217 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7676439 A B x x')). Qed.
Lemma lem7676441 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676442 {A B : Type'} (x : finite_diff A B) : (term213 A B x) = (term218 A B x).
Proof. exact (MK_COMB (@lem7676441) (@lem7676440 A B x)). Qed.
Lemma lem7676443 {A B : Type'} (x : finite_diff A B) : (term212 A B x) = (term218 A B x).
Proof. exact (TRANS (@lem7676435 A B x) (@lem7676442 A B x)). Qed.
Lemma lem7676444 {A B : Type'} (P : type31 A B) : (term219 A B P) = (term220 A B P).
Proof. exact (@lem18392 (finite_diff A B) P). Qed.
Lemma lem7676445 {A B : Type'} : (term68 A B) = (term221 A B).
Proof. exact (@lem7676444 A B (term66 A B)). Qed.
Lemma lem7676446 {A B : Type'} (x : finite_diff A B) : (term222 A B x) = (term65 A B x).
Proof. exact (eq_refl (term222 A B x)). Qed.
Lemma lem7676447 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7676448 {A B : Type'} (x : finite_diff A B) : (term223 A B x) = (term212 A B x).
Proof. exact (MK_COMB (@lem7676447) (@lem7676446 A B x)). Qed.
Lemma lem7676449 {A B : Type'} (x : finite_diff A B) : (term223 A B x) = (term218 A B x).
Proof. exact (TRANS (@lem7676448 A B x) (@lem7676443 A B x)). Qed.
Lemma lem7676450 {A B : Type'} : (term224 A B) = (term225 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7676449 A B x)). Qed.
Lemma lem7676451 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7676452 {A B : Type'} : (term221 A B) = (term226 A B).
Proof. exact (MK_COMB (@lem7676451 A B) (@lem7676450 A B)). Qed.
Lemma lem7676453 {A B : Type'} : (term68 A B) = (term226 A B).
Proof. exact (TRANS (@lem7676445 A B) (@lem7676452 A B)). Qed.
Lemma lem7676454 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7676455 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7676454 A a)). Qed.
Lemma lem7676456 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7676457 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7676456 A) (@lem7676455 A)). Qed.
Lemma lem7676472 {A : Type'} (r : nat) : ((term32 r) = ((term93 A r) = r)) = (term304 A r).
Proof. exact (@lem17784 (term32 r) ((term93 A r) = r)). Qed.
Lemma lem7676473 {A : Type'} : (term95 A) = (term305 A).
Proof. exact (fun_ext (fun r : nat => @lem7676472 A r)). Qed.
Lemma lem7676474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676475 {A : Type'} : (term97 A) = (term306 A).
Proof. exact (MK_COMB (@lem7676474) (@lem7676473 A)). Qed.
Lemma lem7676476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676477 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7676476) (@lem7676457 A)). Qed.
Lemma lem7676478 {A : Type'} : (term99 A) = (term307 A).
Proof. exact (MK_COMB (@lem7676477 A) (@lem7676475 A)). Qed.
Lemma lem7676479 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7676480 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7676479 A B a)). Qed.
Lemma lem7676481 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7676482 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7676481 A B) (@lem7676480 A B)). Qed.
Lemma lem7676497 {A B : Type'} (r : nat) : ((term62 A B r) = ((term47 A B r) = r)) = (term231 A B r).
Proof. exact (@lem17784 (term62 A B r) ((term47 A B r) = r)). Qed.
Lemma lem7676498 {A B : Type'} : (term71 A B) = (term232 A B).
Proof. exact (fun_ext (fun r : nat => @lem7676497 A B r)). Qed.
Lemma lem7676499 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676500 {A B : Type'} : (term72 A B) = (term233 A B).
Proof. exact (MK_COMB (@lem7676499) (@lem7676498 A B)). Qed.
Lemma lem7676501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676502 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7676501) (@lem7676482 A B)). Qed.
Lemma lem7676503 {A B : Type'} : (term73 A B) = (term234 A B).
Proof. exact (MK_COMB (@lem7676502 A B) (@lem7676500 A B)). Qed.
Lemma lem7676504 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7676505 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7676504 B a)). Qed.
Lemma lem7676506 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7676507 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7676506 B) (@lem7676505 B)). Qed.
Lemma lem7676522 {B : Type'} (r : nat) : ((term118 B r) = ((term93 B r) = r)) = (term227 B r).
Proof. exact (@lem17784 (term118 B r) ((term93 B r) = r)). Qed.
Lemma lem7676523 {B : Type'} : (term120 B) = (term228 B).
Proof. exact (fun_ext (fun r : nat => @lem7676522 B r)). Qed.
Lemma lem7676524 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676525 {B : Type'} : (term121 B) = (term229 B).
Proof. exact (MK_COMB (@lem7676524) (@lem7676523 B)). Qed.
Lemma lem7676526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676527 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7676526) (@lem7676507 B)). Qed.
Lemma lem7676528 {B : Type'} : (term122 B) = (term230 B).
Proof. exact (MK_COMB (@lem7676527 B) (@lem7676525 B)). Qed.
Lemma lem7676529 {B : Type'} : (term235 B) = (term122 B).
Proof. exact (@lem16933 (term122 B)). Qed.
Lemma lem7676530 {B : Type'} : (term235 B) = (term230 B).
Proof. exact (TRANS (@lem7676529 B) (@lem7676528 B)). Qed.
Lemma lem7676531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676532 {A B : Type'} : (term236 A B) = (term237 A B).
Proof. exact (MK_COMB (@lem7676531) (@lem7676503 A B)). Qed.
Lemma lem7676533 {A B : Type'} : (term238 A B) = (term239 A B).
Proof. exact (MK_COMB (@lem7676532 A B) (@lem7676530 B)). Qed.
Lemma lem7676534 {A B : Type'} : (term240 A B) = (term238 A B).
Proof. exact (@lem17362 (term73 A B) (term165 B)). Qed.
Lemma lem7676535 {A B : Type'} : (term240 A B) = (term239 A B).
Proof. exact (TRANS (@lem7676534 A B) (@lem7676533 A B)). Qed.
Lemma lem7676536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676537 {A : Type'} : (term308 A) = (term309 A).
Proof. exact (MK_COMB (@lem7676536) (@lem7676478 A)). Qed.
Lemma lem7676538 {A B : Type'} : (term310 A B) = (term311 A B).
Proof. exact (MK_COMB (@lem7676537 A) (@lem7676535 A B)). Qed.
Lemma lem7676539 {A B : Type'} : (term312 A B) = (term310 A B).
Proof. exact (@lem17362 (term99 A) (term166 A B)). Qed.
Lemma lem7676540 {A B : Type'} : (term312 A B) = (term311 A B).
Proof. exact (TRANS (@lem7676539 A B) (@lem7676538 A B)). Qed.
Lemma lem7676541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676542 {A B : Type'} : (term246 A B) = (term247 A B).
Proof. exact (MK_COMB (@lem7676541) (@lem7676453 A B)). Qed.
Lemma lem7676543 {A B : Type'} : (term313 A B) = (term314 A B).
Proof. exact (MK_COMB (@lem7676542 A B) (@lem7676540 A B)). Qed.
Lemma lem7676544 {A B : Type'} : (term315 A B) = (term313 A B).
Proof. exact (@lem17362 (term68 A B) (term178 A B)). Qed.
Lemma lem7676545 {A B : Type'} : (term315 A B) = (term314 A B).
Proof. exact (TRANS (@lem7676544 A B) (@lem7676543 A B)). Qed.
Lemma lem7676546 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676547 {A B : Type'} : (term251 A B) = (term252 A B).
Proof. exact (MK_COMB (@lem7676546) (@lem7676426 A B)). Qed.
Lemma lem7676548 {A B : Type'} : (term316 A B) = (term317 A B).
Proof. exact (MK_COMB (@lem7676547 A B) (@lem7676545 A B)). Qed.
Lemma lem7676549 {A B : Type'} : (term318 A B) = (term316 A B).
Proof. exact (@lem17160 (term256 A B) (term179 A B)). Qed.
Lemma lem7676550 {A B : Type'} : (term318 A B) = (term317 A B).
Proof. exact (TRANS (@lem7676549 A B) (@lem7676548 A B)). Qed.
Lemma lem7676558 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term257 A B x x') = (term258 A B x x').
Proof. exact (@lem17045 (x = (@mk_finite_diff A B x')) (term32 x')). Qed.
Lemma lem7676559 (P : nat -> Prop) : (term210 P) = (term211 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem7676560 {A B : Type'} (x : finite_diff A B) : (term259 A B x) = (term260 A B x).
Proof. exact (@lem7676559 (term37 A B x)). Qed.
Lemma lem7676561 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term261 A B x x') = (term35 A B x x').
Proof. exact (eq_refl (term261 A B x x')). Qed.
Lemma lem7676562 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7676563 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term262 A B x x') = (term257 A B x x').
Proof. exact (MK_COMB (@lem7676562) (@lem7676561 A B x x')). Qed.
Lemma lem7676564 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term262 A B x x') = (term258 A B x x').
Proof. exact (TRANS (@lem7676563 A B x x') (@lem7676558 A B x x')). Qed.
Lemma lem7676565 {A B : Type'} (x : finite_diff A B) : (term263 A B x) = (term264 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7676564 A B x x')). Qed.
Lemma lem7676566 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676567 {A B : Type'} (x : finite_diff A B) : (term260 A B x) = (term265 A B x).
Proof. exact (MK_COMB (@lem7676566) (@lem7676565 A B x)). Qed.
Lemma lem7676568 {A B : Type'} (x : finite_diff A B) : (term259 A B x) = (term265 A B x).
Proof. exact (TRANS (@lem7676560 A B x) (@lem7676567 A B x)). Qed.
Lemma lem7676569 {A B : Type'} (P : type31 A B) : (term219 A B P) = (term220 A B P).
Proof. exact (@lem18392 (finite_diff A B) P). Qed.
Lemma lem7676570 {A B : Type'} : (term43 A B) = (term266 A B).
Proof. exact (@lem7676569 A B (term41 A B)). Qed.
Lemma lem7676571 {A B : Type'} (x : finite_diff A B) : (term267 A B x) = (term39 A B x).
Proof. exact (eq_refl (term267 A B x)). Qed.
Lemma lem7676572 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7676573 {A B : Type'} (x : finite_diff A B) : (term268 A B x) = (term259 A B x).
Proof. exact (MK_COMB (@lem7676572) (@lem7676571 A B x)). Qed.
Lemma lem7676574 {A B : Type'} (x : finite_diff A B) : (term268 A B x) = (term265 A B x).
Proof. exact (TRANS (@lem7676573 A B x) (@lem7676568 A B x)). Qed.
Lemma lem7676575 {A B : Type'} : (term269 A B) = (term270 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7676574 A B x)). Qed.
Lemma lem7676576 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7676577 {A B : Type'} : (term266 A B) = (term271 A B).
Proof. exact (MK_COMB (@lem7676576 A B) (@lem7676575 A B)). Qed.
Lemma lem7676578 {A B : Type'} : (term43 A B) = (term271 A B).
Proof. exact (TRANS (@lem7676570 A B) (@lem7676577 A B)). Qed.
Lemma lem7676579 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7676580 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7676579 A a)). Qed.
Lemma lem7676581 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7676582 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7676581 A) (@lem7676580 A)). Qed.
Lemma lem7676597 {A : Type'} (r : nat) : ((term32 r) = ((term93 A r) = r)) = (term304 A r).
Proof. exact (@lem17784 (term32 r) ((term93 A r) = r)). Qed.
Lemma lem7676598 {A : Type'} : (term95 A) = (term305 A).
Proof. exact (fun_ext (fun r : nat => @lem7676597 A r)). Qed.
Lemma lem7676599 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676600 {A : Type'} : (term97 A) = (term306 A).
Proof. exact (MK_COMB (@lem7676599) (@lem7676598 A)). Qed.
Lemma lem7676601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676602 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7676601) (@lem7676582 A)). Qed.
Lemma lem7676603 {A : Type'} : (term99 A) = (term307 A).
Proof. exact (MK_COMB (@lem7676602 A) (@lem7676600 A)). Qed.
Lemma lem7676604 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7676605 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7676604 A B a)). Qed.
Lemma lem7676606 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7676607 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7676606 A B) (@lem7676605 A B)). Qed.
Lemma lem7676622 {A B : Type'} (r : nat) : ((term32 r) = ((term47 A B r) = r)) = (term272 A B r).
Proof. exact (@lem17784 (term32 r) ((term47 A B r) = r)). Qed.
Lemma lem7676623 {A B : Type'} : (term49 A B) = (term273 A B).
Proof. exact (fun_ext (fun r : nat => @lem7676622 A B r)). Qed.
Lemma lem7676624 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676625 {A B : Type'} : (term51 A B) = (term274 A B).
Proof. exact (MK_COMB (@lem7676624) (@lem7676623 A B)). Qed.
Lemma lem7676626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676627 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7676626) (@lem7676607 A B)). Qed.
Lemma lem7676628 {A B : Type'} : (term53 A B) = (term275 A B).
Proof. exact (MK_COMB (@lem7676627 A B) (@lem7676625 A B)). Qed.
Lemma lem7676629 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7676630 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7676629 B a)). Qed.
Lemma lem7676631 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7676632 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7676631 B) (@lem7676630 B)). Qed.
Lemma lem7676647 {B : Type'} (r : nat) : ((term118 B r) = ((term93 B r) = r)) = (term227 B r).
Proof. exact (@lem17784 (term118 B r) ((term93 B r) = r)). Qed.
Lemma lem7676648 {B : Type'} : (term120 B) = (term228 B).
Proof. exact (fun_ext (fun r : nat => @lem7676647 B r)). Qed.
Lemma lem7676649 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676650 {B : Type'} : (term121 B) = (term229 B).
Proof. exact (MK_COMB (@lem7676649) (@lem7676648 B)). Qed.
Lemma lem7676651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676652 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7676651) (@lem7676632 B)). Qed.
Lemma lem7676653 {B : Type'} : (term122 B) = (term230 B).
Proof. exact (MK_COMB (@lem7676652 B) (@lem7676650 B)). Qed.
Lemma lem7676654 {B : Type'} : (term235 B) = (term122 B).
Proof. exact (@lem16933 (term122 B)). Qed.
Lemma lem7676655 {B : Type'} : (term235 B) = (term230 B).
Proof. exact (TRANS (@lem7676654 B) (@lem7676653 B)). Qed.
Lemma lem7676656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676657 {A B : Type'} : (term276 A B) = (term277 A B).
Proof. exact (MK_COMB (@lem7676656) (@lem7676628 A B)). Qed.
Lemma lem7676658 {A B : Type'} : (term278 A B) = (term279 A B).
Proof. exact (MK_COMB (@lem7676657 A B) (@lem7676655 B)). Qed.
Lemma lem7676659 {A B : Type'} : (term280 A B) = (term278 A B).
Proof. exact (@lem17362 (term53 A B) (term165 B)). Qed.
Lemma lem7676660 {A B : Type'} : (term280 A B) = (term279 A B).
Proof. exact (TRANS (@lem7676659 A B) (@lem7676658 A B)). Qed.
Lemma lem7676661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676662 {A : Type'} : (term308 A) = (term309 A).
Proof. exact (MK_COMB (@lem7676661) (@lem7676603 A)). Qed.
Lemma lem7676663 {A B : Type'} : (term319 A B) = (term320 A B).
Proof. exact (MK_COMB (@lem7676662 A) (@lem7676660 A B)). Qed.
Lemma lem7676664 {A B : Type'} : (term321 A B) = (term319 A B).
Proof. exact (@lem17362 (term99 A) (term171 A B)). Qed.
Lemma lem7676665 {A B : Type'} : (term321 A B) = (term320 A B).
Proof. exact (TRANS (@lem7676664 A B) (@lem7676663 A B)). Qed.
Lemma lem7676666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676667 {A B : Type'} : (term284 A B) = (term285 A B).
Proof. exact (MK_COMB (@lem7676666) (@lem7676578 A B)). Qed.
Lemma lem7676668 {A B : Type'} : (term322 A B) = (term323 A B).
Proof. exact (MK_COMB (@lem7676667 A B) (@lem7676665 A B)). Qed.
Lemma lem7676669 {A B : Type'} : (term324 A B) = (term322 A B).
Proof. exact (@lem17362 (term43 A B) (term182 A B)). Qed.
Lemma lem7676670 {A B : Type'} : (term324 A B) = (term323 A B).
Proof. exact (TRANS (@lem7676669 A B) (@lem7676668 A B)). Qed.
Lemma lem7676672 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7676673 {A B : Type'} : (term325 A B) = (term326 A B).
Proof. exact (MK_COMB (@lem7676672 A B) (@lem7676670 A B)). Qed.
Lemma lem7676674 {A B : Type'} : (term327 A B) = (term325 A B).
Proof. exact (@lem17160 (term20 A B) (term183 A B)). Qed.
Lemma lem7676675 {A B : Type'} : (term327 A B) = (term326 A B).
Proof. exact (TRANS (@lem7676674 A B) (@lem7676673 A B)). Qed.
Lemma lem7676676 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7676677 {A B : Type'} : (term328 A B) = (term329 A B).
Proof. exact (MK_COMB (@lem7676676) (@lem7676550 A B)). Qed.
Lemma lem7676678 {A B : Type'} : (term330 A B) = (term331 A B).
Proof. exact (MK_COMB (@lem7676677 A B) (@lem7676675 A B)). Qed.
Lemma lem7676679 {A B : Type'} : (term332 A B) = (term330 A B).
Proof. exact (@lem17045 (term180 A B) (term184 A B)). Qed.
Lemma lem7676680 {A B : Type'} : (term332 A B) = (term331 A B).
Proof. exact (TRANS (@lem7676679 A B) (@lem7676678 A B)). Qed.
Lemma lem7676682 {A : Type'} : (term333 A) = (term333 A).
Proof. exact (eq_refl (term333 A)). Qed.
Lemma lem7676683 {A B : Type'} : (term334 A B) = (term335 A B).
Proof. exact (MK_COMB (@lem7676682 A) (@lem7676680 A B)). Qed.
Lemma lem7676684 {A B : Type'} : (term336 A B) = (term334 A B).
Proof. exact (@lem17160 (term83 A) (term185 A B)). Qed.
Lemma lem7676685 {A B : Type'} : (term336 A B) = (term335 A B).
Proof. exact (TRANS (@lem7676684 A B) (@lem7676683 A B)). Qed.
Lemma lem7676686 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7676687 {A B : Type'} : (term337 A B) = (term338 A B).
Proof. exact (MK_COMB (@lem7676686) (@lem7676422 A B)). Qed.
Lemma lem7676688 {A B : Type'} : (term339 A B) = (term340 A B).
Proof. exact (MK_COMB (@lem7676687 A B) (@lem7676685 A B)). Qed.
Lemma lem7676689 {A B : Type'} : (term341 A B) = (term339 A B).
Proof. exact (@lem17045 (term176 A B) (term186 A B)). Qed.
Lemma lem7676690 {A B : Type'} : (term341 A B) = (term340 A B).
Proof. exact (TRANS (@lem7676689 A B) (@lem7676688 A B)). Qed.
Lemma lem7676691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676692 {B : Type'} : (term298 B) = (term299 B).
Proof. exact (MK_COMB (@lem7676691) (@lem7676157 B)). Qed.
Lemma lem7676693 {A B : Type'} : (term342 A B) = (term343 A B).
Proof. exact (MK_COMB (@lem7676692 B) (@lem7676690 A B)). Qed.
Lemma lem7676694 {A B : Type'} : (term344 A B) = (term342 A B).
Proof. exact (@lem17160 (term303 B) (term187 A B)). Qed.
Lemma lem7676695 {A B : Type'} : (term344 A B) = (term343 A B).
Proof. exact (TRANS (@lem7676694 A B) (@lem7676693 A B)). Qed.
Lemma lem7676699 {A : Type'} : (term206 A) = (term83 A).
Proof. exact (@lem16933 (term83 A)). Qed.
Lemma lem7676702 {A B : Type'} : (term207 A B) = (term20 A B).
Proof. exact (@lem16933 (term20 A B)). Qed.
Lemma lem7676709 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term208 A B x x') = (term209 A B x x').
Proof. exact (@lem17045 (x = (@mk_finite_diff A B x')) (term62 A B x')). Qed.
Lemma lem7676710 (P : nat -> Prop) : (term210 P) = (term211 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem7676711 {A B : Type'} (x : finite_diff A B) : (term212 A B x) = (term213 A B x).
Proof. exact (@lem7676710 (term64 A B x)). Qed.
Lemma lem7676712 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term214 A B x x') = (term63 A B x x').
Proof. exact (eq_refl (term214 A B x x')). Qed.
Lemma lem7676713 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7676714 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term215 A B x x') = (term208 A B x x').
Proof. exact (MK_COMB (@lem7676713) (@lem7676712 A B x x')). Qed.
Lemma lem7676715 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term215 A B x x') = (term209 A B x x').
Proof. exact (TRANS (@lem7676714 A B x x') (@lem7676709 A B x x')). Qed.
Lemma lem7676716 {A B : Type'} (x : finite_diff A B) : (term216 A B x) = (term217 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7676715 A B x x')). Qed.
Lemma lem7676717 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676718 {A B : Type'} (x : finite_diff A B) : (term213 A B x) = (term218 A B x).
Proof. exact (MK_COMB (@lem7676717) (@lem7676716 A B x)). Qed.
Lemma lem7676719 {A B : Type'} (x : finite_diff A B) : (term212 A B x) = (term218 A B x).
Proof. exact (TRANS (@lem7676711 A B x) (@lem7676718 A B x)). Qed.
Lemma lem7676720 {A B : Type'} (P : type31 A B) : (term219 A B P) = (term220 A B P).
Proof. exact (@lem18392 (finite_diff A B) P). Qed.
Lemma lem7676721 {A B : Type'} : (term68 A B) = (term221 A B).
Proof. exact (@lem7676720 A B (term66 A B)). Qed.
Lemma lem7676722 {A B : Type'} (x : finite_diff A B) : (term222 A B x) = (term65 A B x).
Proof. exact (eq_refl (term222 A B x)). Qed.
Lemma lem7676723 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7676724 {A B : Type'} (x : finite_diff A B) : (term223 A B x) = (term212 A B x).
Proof. exact (MK_COMB (@lem7676723) (@lem7676722 A B x)). Qed.
Lemma lem7676725 {A B : Type'} (x : finite_diff A B) : (term223 A B x) = (term218 A B x).
Proof. exact (TRANS (@lem7676724 A B x) (@lem7676719 A B x)). Qed.
Lemma lem7676726 {A B : Type'} : (term224 A B) = (term225 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7676725 A B x)). Qed.
Lemma lem7676727 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7676728 {A B : Type'} : (term221 A B) = (term226 A B).
Proof. exact (MK_COMB (@lem7676727 A B) (@lem7676726 A B)). Qed.
Lemma lem7676729 {A B : Type'} : (term68 A B) = (term226 A B).
Proof. exact (TRANS (@lem7676721 A B) (@lem7676728 A B)). Qed.
Lemma lem7676730 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7676731 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7676730 A a)). Qed.
Lemma lem7676732 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7676733 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7676732 A) (@lem7676731 A)). Qed.
Lemma lem7676748 {A : Type'} (r : nat) : ((term118 A r) = ((term93 A r) = r)) = (term227 A r).
Proof. exact (@lem17784 (term118 A r) ((term93 A r) = r)). Qed.
Lemma lem7676749 {A : Type'} : (term120 A) = (term228 A).
Proof. exact (fun_ext (fun r : nat => @lem7676748 A r)). Qed.
Lemma lem7676750 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676751 {A : Type'} : (term121 A) = (term229 A).
Proof. exact (MK_COMB (@lem7676750) (@lem7676749 A)). Qed.
Lemma lem7676752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676753 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7676752) (@lem7676733 A)). Qed.
Lemma lem7676754 {A : Type'} : (term122 A) = (term230 A).
Proof. exact (MK_COMB (@lem7676753 A) (@lem7676751 A)). Qed.
Lemma lem7676755 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7676756 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7676755 A B a)). Qed.
Lemma lem7676757 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7676758 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7676757 A B) (@lem7676756 A B)). Qed.
Lemma lem7676773 {A B : Type'} (r : nat) : ((term62 A B r) = ((term47 A B r) = r)) = (term231 A B r).
Proof. exact (@lem17784 (term62 A B r) ((term47 A B r) = r)). Qed.
Lemma lem7676774 {A B : Type'} : (term71 A B) = (term232 A B).
Proof. exact (fun_ext (fun r : nat => @lem7676773 A B r)). Qed.
Lemma lem7676775 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676776 {A B : Type'} : (term72 A B) = (term233 A B).
Proof. exact (MK_COMB (@lem7676775) (@lem7676774 A B)). Qed.
Lemma lem7676777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676778 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7676777) (@lem7676758 A B)). Qed.
Lemma lem7676779 {A B : Type'} : (term73 A B) = (term234 A B).
Proof. exact (MK_COMB (@lem7676778 A B) (@lem7676776 A B)). Qed.
Lemma lem7676780 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7676781 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7676780 B a)). Qed.
Lemma lem7676782 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7676783 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7676782 B) (@lem7676781 B)). Qed.
Lemma lem7676798 {B : Type'} (r : nat) : ((term32 r) = ((term93 B r) = r)) = (term304 B r).
Proof. exact (@lem17784 (term32 r) ((term93 B r) = r)). Qed.
Lemma lem7676799 {B : Type'} : (term95 B) = (term305 B).
Proof. exact (fun_ext (fun r : nat => @lem7676798 B r)). Qed.
Lemma lem7676800 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676801 {B : Type'} : (term97 B) = (term306 B).
Proof. exact (MK_COMB (@lem7676800) (@lem7676799 B)). Qed.
Lemma lem7676802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676803 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7676802) (@lem7676783 B)). Qed.
Lemma lem7676804 {B : Type'} : (term99 B) = (term307 B).
Proof. exact (MK_COMB (@lem7676803 B) (@lem7676801 B)). Qed.
Lemma lem7676805 {B : Type'} : (term345 B) = (term99 B).
Proof. exact (@lem16933 (term99 B)). Qed.
Lemma lem7676806 {B : Type'} : (term345 B) = (term307 B).
Proof. exact (TRANS (@lem7676805 B) (@lem7676804 B)). Qed.
Lemma lem7676807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676808 {A B : Type'} : (term236 A B) = (term237 A B).
Proof. exact (MK_COMB (@lem7676807) (@lem7676779 A B)). Qed.
Lemma lem7676809 {A B : Type'} : (term346 A B) = (term347 A B).
Proof. exact (MK_COMB (@lem7676808 A B) (@lem7676806 B)). Qed.
Lemma lem7676810 {A B : Type'} : (term348 A B) = (term346 A B).
Proof. exact (@lem17362 (term73 A B) (term136 B)). Qed.
Lemma lem7676811 {A B : Type'} : (term348 A B) = (term347 A B).
Proof. exact (TRANS (@lem7676810 A B) (@lem7676809 A B)). Qed.
Lemma lem7676812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676813 {A : Type'} : (term241 A) = (term242 A).
Proof. exact (MK_COMB (@lem7676812) (@lem7676754 A)). Qed.
Lemma lem7676814 {A B : Type'} : (term349 A B) = (term350 A B).
Proof. exact (MK_COMB (@lem7676813 A) (@lem7676811 A B)). Qed.
Lemma lem7676815 {A B : Type'} : (term351 A B) = (term349 A B).
Proof. exact (@lem17362 (term122 A) (term137 A B)). Qed.
Lemma lem7676816 {A B : Type'} : (term351 A B) = (term350 A B).
Proof. exact (TRANS (@lem7676815 A B) (@lem7676814 A B)). Qed.
Lemma lem7676817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676818 {A B : Type'} : (term246 A B) = (term247 A B).
Proof. exact (MK_COMB (@lem7676817) (@lem7676729 A B)). Qed.
Lemma lem7676819 {A B : Type'} : (term352 A B) = (term353 A B).
Proof. exact (MK_COMB (@lem7676818 A B) (@lem7676816 A B)). Qed.
Lemma lem7676820 {A B : Type'} : (term354 A B) = (term352 A B).
Proof. exact (@lem17362 (term68 A B) (term138 A B)). Qed.
Lemma lem7676821 {A B : Type'} : (term354 A B) = (term353 A B).
Proof. exact (TRANS (@lem7676820 A B) (@lem7676819 A B)). Qed.
Lemma lem7676822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676823 {A B : Type'} : (term251 A B) = (term252 A B).
Proof. exact (MK_COMB (@lem7676822) (@lem7676702 A B)). Qed.
Lemma lem7676824 {A B : Type'} : (term355 A B) = (term356 A B).
Proof. exact (MK_COMB (@lem7676823 A B) (@lem7676821 A B)). Qed.
Lemma lem7676825 {A B : Type'} : (term357 A B) = (term355 A B).
Proof. exact (@lem17160 (term256 A B) (term139 A B)). Qed.
Lemma lem7676826 {A B : Type'} : (term357 A B) = (term356 A B).
Proof. exact (TRANS (@lem7676825 A B) (@lem7676824 A B)). Qed.
Lemma lem7676834 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term257 A B x x') = (term258 A B x x').
Proof. exact (@lem17045 (x = (@mk_finite_diff A B x')) (term32 x')). Qed.
Lemma lem7676835 (P : nat -> Prop) : (term210 P) = (term211 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem7676836 {A B : Type'} (x : finite_diff A B) : (term259 A B x) = (term260 A B x).
Proof. exact (@lem7676835 (term37 A B x)). Qed.
Lemma lem7676837 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term261 A B x x') = (term35 A B x x').
Proof. exact (eq_refl (term261 A B x x')). Qed.
Lemma lem7676838 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7676839 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term262 A B x x') = (term257 A B x x').
Proof. exact (MK_COMB (@lem7676838) (@lem7676837 A B x x')). Qed.
Lemma lem7676840 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term262 A B x x') = (term258 A B x x').
Proof. exact (TRANS (@lem7676839 A B x x') (@lem7676834 A B x x')). Qed.
Lemma lem7676841 {A B : Type'} (x : finite_diff A B) : (term263 A B x) = (term264 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7676840 A B x x')). Qed.
Lemma lem7676842 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676843 {A B : Type'} (x : finite_diff A B) : (term260 A B x) = (term265 A B x).
Proof. exact (MK_COMB (@lem7676842) (@lem7676841 A B x)). Qed.
Lemma lem7676844 {A B : Type'} (x : finite_diff A B) : (term259 A B x) = (term265 A B x).
Proof. exact (TRANS (@lem7676836 A B x) (@lem7676843 A B x)). Qed.
Lemma lem7676845 {A B : Type'} (P : type31 A B) : (term219 A B P) = (term220 A B P).
Proof. exact (@lem18392 (finite_diff A B) P). Qed.
Lemma lem7676846 {A B : Type'} : (term43 A B) = (term266 A B).
Proof. exact (@lem7676845 A B (term41 A B)). Qed.
Lemma lem7676847 {A B : Type'} (x : finite_diff A B) : (term267 A B x) = (term39 A B x).
Proof. exact (eq_refl (term267 A B x)). Qed.
Lemma lem7676848 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7676849 {A B : Type'} (x : finite_diff A B) : (term268 A B x) = (term259 A B x).
Proof. exact (MK_COMB (@lem7676848) (@lem7676847 A B x)). Qed.
Lemma lem7676850 {A B : Type'} (x : finite_diff A B) : (term268 A B x) = (term265 A B x).
Proof. exact (TRANS (@lem7676849 A B x) (@lem7676844 A B x)). Qed.
Lemma lem7676851 {A B : Type'} : (term269 A B) = (term270 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7676850 A B x)). Qed.
Lemma lem7676852 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7676853 {A B : Type'} : (term266 A B) = (term271 A B).
Proof. exact (MK_COMB (@lem7676852 A B) (@lem7676851 A B)). Qed.
Lemma lem7676854 {A B : Type'} : (term43 A B) = (term271 A B).
Proof. exact (TRANS (@lem7676846 A B) (@lem7676853 A B)). Qed.
Lemma lem7676855 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7676856 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7676855 A a)). Qed.
Lemma lem7676857 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7676858 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7676857 A) (@lem7676856 A)). Qed.
Lemma lem7676873 {A : Type'} (r : nat) : ((term118 A r) = ((term93 A r) = r)) = (term227 A r).
Proof. exact (@lem17784 (term118 A r) ((term93 A r) = r)). Qed.
Lemma lem7676874 {A : Type'} : (term120 A) = (term228 A).
Proof. exact (fun_ext (fun r : nat => @lem7676873 A r)). Qed.
Lemma lem7676875 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676876 {A : Type'} : (term121 A) = (term229 A).
Proof. exact (MK_COMB (@lem7676875) (@lem7676874 A)). Qed.
Lemma lem7676877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676878 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7676877) (@lem7676858 A)). Qed.
Lemma lem7676879 {A : Type'} : (term122 A) = (term230 A).
Proof. exact (MK_COMB (@lem7676878 A) (@lem7676876 A)). Qed.
Lemma lem7676880 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7676881 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7676880 A B a)). Qed.
Lemma lem7676882 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7676883 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7676882 A B) (@lem7676881 A B)). Qed.
Lemma lem7676898 {A B : Type'} (r : nat) : ((term32 r) = ((term47 A B r) = r)) = (term272 A B r).
Proof. exact (@lem17784 (term32 r) ((term47 A B r) = r)). Qed.
Lemma lem7676899 {A B : Type'} : (term49 A B) = (term273 A B).
Proof. exact (fun_ext (fun r : nat => @lem7676898 A B r)). Qed.
Lemma lem7676900 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676901 {A B : Type'} : (term51 A B) = (term274 A B).
Proof. exact (MK_COMB (@lem7676900) (@lem7676899 A B)). Qed.
Lemma lem7676902 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676903 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7676902) (@lem7676883 A B)). Qed.
Lemma lem7676904 {A B : Type'} : (term53 A B) = (term275 A B).
Proof. exact (MK_COMB (@lem7676903 A B) (@lem7676901 A B)). Qed.
Lemma lem7676905 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7676906 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7676905 B a)). Qed.
Lemma lem7676907 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7676908 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7676907 B) (@lem7676906 B)). Qed.
Lemma lem7676923 {B : Type'} (r : nat) : ((term32 r) = ((term93 B r) = r)) = (term304 B r).
Proof. exact (@lem17784 (term32 r) ((term93 B r) = r)). Qed.
Lemma lem7676924 {B : Type'} : (term95 B) = (term305 B).
Proof. exact (fun_ext (fun r : nat => @lem7676923 B r)). Qed.
Lemma lem7676925 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676926 {B : Type'} : (term97 B) = (term306 B).
Proof. exact (MK_COMB (@lem7676925) (@lem7676924 B)). Qed.
Lemma lem7676927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676928 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7676927) (@lem7676908 B)). Qed.
Lemma lem7676929 {B : Type'} : (term99 B) = (term307 B).
Proof. exact (MK_COMB (@lem7676928 B) (@lem7676926 B)). Qed.
Lemma lem7676930 {B : Type'} : (term345 B) = (term99 B).
Proof. exact (@lem16933 (term99 B)). Qed.
Lemma lem7676931 {B : Type'} : (term345 B) = (term307 B).
Proof. exact (TRANS (@lem7676930 B) (@lem7676929 B)). Qed.
Lemma lem7676932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676933 {A B : Type'} : (term276 A B) = (term277 A B).
Proof. exact (MK_COMB (@lem7676932) (@lem7676904 A B)). Qed.
Lemma lem7676934 {A B : Type'} : (term358 A B) = (term359 A B).
Proof. exact (MK_COMB (@lem7676933 A B) (@lem7676931 B)). Qed.
Lemma lem7676935 {A B : Type'} : (term360 A B) = (term358 A B).
Proof. exact (@lem17362 (term53 A B) (term136 B)). Qed.
Lemma lem7676936 {A B : Type'} : (term360 A B) = (term359 A B).
Proof. exact (TRANS (@lem7676935 A B) (@lem7676934 A B)). Qed.
Lemma lem7676937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676938 {A : Type'} : (term241 A) = (term242 A).
Proof. exact (MK_COMB (@lem7676937) (@lem7676879 A)). Qed.
Lemma lem7676939 {A B : Type'} : (term361 A B) = (term362 A B).
Proof. exact (MK_COMB (@lem7676938 A) (@lem7676936 A B)). Qed.
Lemma lem7676940 {A B : Type'} : (term363 A B) = (term361 A B).
Proof. exact (@lem17362 (term122 A) (term142 A B)). Qed.
Lemma lem7676941 {A B : Type'} : (term363 A B) = (term362 A B).
Proof. exact (TRANS (@lem7676940 A B) (@lem7676939 A B)). Qed.
Lemma lem7676942 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676943 {A B : Type'} : (term284 A B) = (term285 A B).
Proof. exact (MK_COMB (@lem7676942) (@lem7676854 A B)). Qed.
Lemma lem7676944 {A B : Type'} : (term364 A B) = (term365 A B).
Proof. exact (MK_COMB (@lem7676943 A B) (@lem7676941 A B)). Qed.
Lemma lem7676945 {A B : Type'} : (term366 A B) = (term364 A B).
Proof. exact (@lem17362 (term43 A B) (term143 A B)). Qed.
Lemma lem7676946 {A B : Type'} : (term366 A B) = (term365 A B).
Proof. exact (TRANS (@lem7676945 A B) (@lem7676944 A B)). Qed.
Lemma lem7676948 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7676949 {A B : Type'} : (term367 A B) = (term368 A B).
Proof. exact (MK_COMB (@lem7676948 A B) (@lem7676946 A B)). Qed.
Lemma lem7676950 {A B : Type'} : (term369 A B) = (term367 A B).
Proof. exact (@lem17160 (term20 A B) (term144 A B)). Qed.
Lemma lem7676951 {A B : Type'} : (term369 A B) = (term368 A B).
Proof. exact (TRANS (@lem7676950 A B) (@lem7676949 A B)). Qed.
Lemma lem7676952 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7676953 {A B : Type'} : (term370 A B) = (term371 A B).
Proof. exact (MK_COMB (@lem7676952) (@lem7676826 A B)). Qed.
Lemma lem7676954 {A B : Type'} : (term372 A B) = (term373 A B).
Proof. exact (MK_COMB (@lem7676953 A B) (@lem7676951 A B)). Qed.
Lemma lem7676955 {A B : Type'} : (term374 A B) = (term372 A B).
Proof. exact (@lem17045 (term140 A B) (term145 A B)). Qed.
Lemma lem7676956 {A B : Type'} : (term374 A B) = (term373 A B).
Proof. exact (TRANS (@lem7676955 A B) (@lem7676954 A B)). Qed.
Lemma lem7676957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7676958 {A : Type'} : (term298 A) = (term299 A).
Proof. exact (MK_COMB (@lem7676957) (@lem7676699 A)). Qed.
Lemma lem7676959 {A B : Type'} : (term375 A B) = (term376 A B).
Proof. exact (MK_COMB (@lem7676958 A) (@lem7676956 A B)). Qed.
Lemma lem7676960 {A B : Type'} : (term377 A B) = (term375 A B).
Proof. exact (@lem17160 (term303 A) (term146 A B)). Qed.
Lemma lem7676961 {A B : Type'} : (term377 A B) = (term376 A B).
Proof. exact (TRANS (@lem7676960 A B) (@lem7676959 A B)). Qed.
Lemma lem7676965 {A B : Type'} : (term207 A B) = (term20 A B).
Proof. exact (@lem16933 (term20 A B)). Qed.
Lemma lem7676972 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term208 A B x x') = (term209 A B x x').
Proof. exact (@lem17045 (x = (@mk_finite_diff A B x')) (term62 A B x')). Qed.
Lemma lem7676973 (P : nat -> Prop) : (term210 P) = (term211 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem7676974 {A B : Type'} (x : finite_diff A B) : (term212 A B x) = (term213 A B x).
Proof. exact (@lem7676973 (term64 A B x)). Qed.
Lemma lem7676975 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term214 A B x x') = (term63 A B x x').
Proof. exact (eq_refl (term214 A B x x')). Qed.
Lemma lem7676976 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7676977 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term215 A B x x') = (term208 A B x x').
Proof. exact (MK_COMB (@lem7676976) (@lem7676975 A B x x')). Qed.
Lemma lem7676978 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term215 A B x x') = (term209 A B x x').
Proof. exact (TRANS (@lem7676977 A B x x') (@lem7676972 A B x x')). Qed.
Lemma lem7676979 {A B : Type'} (x : finite_diff A B) : (term216 A B x) = (term217 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7676978 A B x x')). Qed.
Lemma lem7676980 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7676981 {A B : Type'} (x : finite_diff A B) : (term213 A B x) = (term218 A B x).
Proof. exact (MK_COMB (@lem7676980) (@lem7676979 A B x)). Qed.
Lemma lem7676982 {A B : Type'} (x : finite_diff A B) : (term212 A B x) = (term218 A B x).
Proof. exact (TRANS (@lem7676974 A B x) (@lem7676981 A B x)). Qed.
Lemma lem7676983 {A B : Type'} (P : type31 A B) : (term219 A B P) = (term220 A B P).
Proof. exact (@lem18392 (finite_diff A B) P). Qed.
Lemma lem7676984 {A B : Type'} : (term68 A B) = (term221 A B).
Proof. exact (@lem7676983 A B (term66 A B)). Qed.
Lemma lem7676985 {A B : Type'} (x : finite_diff A B) : (term222 A B x) = (term65 A B x).
Proof. exact (eq_refl (term222 A B x)). Qed.
Lemma lem7676986 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7676987 {A B : Type'} (x : finite_diff A B) : (term223 A B x) = (term212 A B x).
Proof. exact (MK_COMB (@lem7676986) (@lem7676985 A B x)). Qed.
Lemma lem7676988 {A B : Type'} (x : finite_diff A B) : (term223 A B x) = (term218 A B x).
Proof. exact (TRANS (@lem7676987 A B x) (@lem7676982 A B x)). Qed.
Lemma lem7676989 {A B : Type'} : (term224 A B) = (term225 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7676988 A B x)). Qed.
Lemma lem7676990 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7676991 {A B : Type'} : (term221 A B) = (term226 A B).
Proof. exact (MK_COMB (@lem7676990 A B) (@lem7676989 A B)). Qed.
Lemma lem7676992 {A B : Type'} : (term68 A B) = (term226 A B).
Proof. exact (TRANS (@lem7676984 A B) (@lem7676991 A B)). Qed.
Lemma lem7676993 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7676994 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7676993 A a)). Qed.
Lemma lem7676995 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7676996 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7676995 A) (@lem7676994 A)). Qed.
Lemma lem7677011 {A : Type'} (r : nat) : ((term32 r) = ((term93 A r) = r)) = (term304 A r).
Proof. exact (@lem17784 (term32 r) ((term93 A r) = r)). Qed.
Lemma lem7677012 {A : Type'} : (term95 A) = (term305 A).
Proof. exact (fun_ext (fun r : nat => @lem7677011 A r)). Qed.
Lemma lem7677013 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677014 {A : Type'} : (term97 A) = (term306 A).
Proof. exact (MK_COMB (@lem7677013) (@lem7677012 A)). Qed.
Lemma lem7677015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677016 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7677015) (@lem7676996 A)). Qed.
Lemma lem7677017 {A : Type'} : (term99 A) = (term307 A).
Proof. exact (MK_COMB (@lem7677016 A) (@lem7677014 A)). Qed.
Lemma lem7677018 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7677019 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7677018 A B a)). Qed.
Lemma lem7677020 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7677021 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7677020 A B) (@lem7677019 A B)). Qed.
Lemma lem7677036 {A B : Type'} (r : nat) : ((term62 A B r) = ((term47 A B r) = r)) = (term231 A B r).
Proof. exact (@lem17784 (term62 A B r) ((term47 A B r) = r)). Qed.
Lemma lem7677037 {A B : Type'} : (term71 A B) = (term232 A B).
Proof. exact (fun_ext (fun r : nat => @lem7677036 A B r)). Qed.
Lemma lem7677038 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677039 {A B : Type'} : (term72 A B) = (term233 A B).
Proof. exact (MK_COMB (@lem7677038) (@lem7677037 A B)). Qed.
Lemma lem7677040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677041 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7677040) (@lem7677021 A B)). Qed.
Lemma lem7677042 {A B : Type'} : (term73 A B) = (term234 A B).
Proof. exact (MK_COMB (@lem7677041 A B) (@lem7677039 A B)). Qed.
Lemma lem7677043 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7677044 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7677043 B a)). Qed.
Lemma lem7677045 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7677046 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7677045 B) (@lem7677044 B)). Qed.
Lemma lem7677061 {B : Type'} (r : nat) : ((term32 r) = ((term93 B r) = r)) = (term304 B r).
Proof. exact (@lem17784 (term32 r) ((term93 B r) = r)). Qed.
Lemma lem7677062 {B : Type'} : (term95 B) = (term305 B).
Proof. exact (fun_ext (fun r : nat => @lem7677061 B r)). Qed.
Lemma lem7677063 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677064 {B : Type'} : (term97 B) = (term306 B).
Proof. exact (MK_COMB (@lem7677063) (@lem7677062 B)). Qed.
Lemma lem7677065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677066 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7677065) (@lem7677046 B)). Qed.
Lemma lem7677067 {B : Type'} : (term99 B) = (term307 B).
Proof. exact (MK_COMB (@lem7677066 B) (@lem7677064 B)). Qed.
Lemma lem7677068 {B : Type'} : (term345 B) = (term99 B).
Proof. exact (@lem16933 (term99 B)). Qed.
Lemma lem7677069 {B : Type'} : (term345 B) = (term307 B).
Proof. exact (TRANS (@lem7677068 B) (@lem7677067 B)). Qed.
Lemma lem7677070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677071 {A B : Type'} : (term236 A B) = (term237 A B).
Proof. exact (MK_COMB (@lem7677070) (@lem7677042 A B)). Qed.
Lemma lem7677072 {A B : Type'} : (term346 A B) = (term347 A B).
Proof. exact (MK_COMB (@lem7677071 A B) (@lem7677069 B)). Qed.
Lemma lem7677073 {A B : Type'} : (term348 A B) = (term346 A B).
Proof. exact (@lem17362 (term73 A B) (term136 B)). Qed.
Lemma lem7677074 {A B : Type'} : (term348 A B) = (term347 A B).
Proof. exact (TRANS (@lem7677073 A B) (@lem7677072 A B)). Qed.
Lemma lem7677075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677076 {A : Type'} : (term308 A) = (term309 A).
Proof. exact (MK_COMB (@lem7677075) (@lem7677017 A)). Qed.
Lemma lem7677077 {A B : Type'} : (term378 A B) = (term379 A B).
Proof. exact (MK_COMB (@lem7677076 A) (@lem7677074 A B)). Qed.
Lemma lem7677078 {A B : Type'} : (term380 A B) = (term378 A B).
Proof. exact (@lem17362 (term99 A) (term137 A B)). Qed.
Lemma lem7677079 {A B : Type'} : (term380 A B) = (term379 A B).
Proof. exact (TRANS (@lem7677078 A B) (@lem7677077 A B)). Qed.
Lemma lem7677080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677081 {A B : Type'} : (term246 A B) = (term247 A B).
Proof. exact (MK_COMB (@lem7677080) (@lem7676992 A B)). Qed.
Lemma lem7677082 {A B : Type'} : (term381 A B) = (term382 A B).
Proof. exact (MK_COMB (@lem7677081 A B) (@lem7677079 A B)). Qed.
Lemma lem7677083 {A B : Type'} : (term383 A B) = (term381 A B).
Proof. exact (@lem17362 (term68 A B) (term152 A B)). Qed.
Lemma lem7677084 {A B : Type'} : (term383 A B) = (term382 A B).
Proof. exact (TRANS (@lem7677083 A B) (@lem7677082 A B)). Qed.
Lemma lem7677085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677086 {A B : Type'} : (term251 A B) = (term252 A B).
Proof. exact (MK_COMB (@lem7677085) (@lem7676965 A B)). Qed.
Lemma lem7677087 {A B : Type'} : (term384 A B) = (term385 A B).
Proof. exact (MK_COMB (@lem7677086 A B) (@lem7677084 A B)). Qed.
Lemma lem7677088 {A B : Type'} : (term386 A B) = (term384 A B).
Proof. exact (@lem17160 (term256 A B) (term153 A B)). Qed.
Lemma lem7677089 {A B : Type'} : (term386 A B) = (term385 A B).
Proof. exact (TRANS (@lem7677088 A B) (@lem7677087 A B)). Qed.
Lemma lem7677097 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term257 A B x x') = (term258 A B x x').
Proof. exact (@lem17045 (x = (@mk_finite_diff A B x')) (term32 x')). Qed.
Lemma lem7677098 (P : nat -> Prop) : (term210 P) = (term211 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem7677099 {A B : Type'} (x : finite_diff A B) : (term259 A B x) = (term260 A B x).
Proof. exact (@lem7677098 (term37 A B x)). Qed.
Lemma lem7677100 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term261 A B x x') = (term35 A B x x').
Proof. exact (eq_refl (term261 A B x x')). Qed.
Lemma lem7677101 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7677102 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term262 A B x x') = (term257 A B x x').
Proof. exact (MK_COMB (@lem7677101) (@lem7677100 A B x x')). Qed.
Lemma lem7677103 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term262 A B x x') = (term258 A B x x').
Proof. exact (TRANS (@lem7677102 A B x x') (@lem7677097 A B x x')). Qed.
Lemma lem7677104 {A B : Type'} (x : finite_diff A B) : (term263 A B x) = (term264 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7677103 A B x x')). Qed.
Lemma lem7677105 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677106 {A B : Type'} (x : finite_diff A B) : (term260 A B x) = (term265 A B x).
Proof. exact (MK_COMB (@lem7677105) (@lem7677104 A B x)). Qed.
Lemma lem7677107 {A B : Type'} (x : finite_diff A B) : (term259 A B x) = (term265 A B x).
Proof. exact (TRANS (@lem7677099 A B x) (@lem7677106 A B x)). Qed.
Lemma lem7677108 {A B : Type'} (P : type31 A B) : (term219 A B P) = (term220 A B P).
Proof. exact (@lem18392 (finite_diff A B) P). Qed.
Lemma lem7677109 {A B : Type'} : (term43 A B) = (term266 A B).
Proof. exact (@lem7677108 A B (term41 A B)). Qed.
Lemma lem7677110 {A B : Type'} (x : finite_diff A B) : (term267 A B x) = (term39 A B x).
Proof. exact (eq_refl (term267 A B x)). Qed.
Lemma lem7677111 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7677112 {A B : Type'} (x : finite_diff A B) : (term268 A B x) = (term259 A B x).
Proof. exact (MK_COMB (@lem7677111) (@lem7677110 A B x)). Qed.
Lemma lem7677113 {A B : Type'} (x : finite_diff A B) : (term268 A B x) = (term265 A B x).
Proof. exact (TRANS (@lem7677112 A B x) (@lem7677107 A B x)). Qed.
Lemma lem7677114 {A B : Type'} : (term269 A B) = (term270 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7677113 A B x)). Qed.
Lemma lem7677115 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7677116 {A B : Type'} : (term266 A B) = (term271 A B).
Proof. exact (MK_COMB (@lem7677115 A B) (@lem7677114 A B)). Qed.
Lemma lem7677117 {A B : Type'} : (term43 A B) = (term271 A B).
Proof. exact (TRANS (@lem7677109 A B) (@lem7677116 A B)). Qed.
Lemma lem7677118 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7677119 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7677118 A a)). Qed.
Lemma lem7677120 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7677121 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7677120 A) (@lem7677119 A)). Qed.
Lemma lem7677136 {A : Type'} (r : nat) : ((term32 r) = ((term93 A r) = r)) = (term304 A r).
Proof. exact (@lem17784 (term32 r) ((term93 A r) = r)). Qed.
Lemma lem7677137 {A : Type'} : (term95 A) = (term305 A).
Proof. exact (fun_ext (fun r : nat => @lem7677136 A r)). Qed.
Lemma lem7677138 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677139 {A : Type'} : (term97 A) = (term306 A).
Proof. exact (MK_COMB (@lem7677138) (@lem7677137 A)). Qed.
Lemma lem7677140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677141 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7677140) (@lem7677121 A)). Qed.
Lemma lem7677142 {A : Type'} : (term99 A) = (term307 A).
Proof. exact (MK_COMB (@lem7677141 A) (@lem7677139 A)). Qed.
Lemma lem7677143 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7677144 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7677143 A B a)). Qed.
Lemma lem7677145 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7677146 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7677145 A B) (@lem7677144 A B)). Qed.
Lemma lem7677161 {A B : Type'} (r : nat) : ((term32 r) = ((term47 A B r) = r)) = (term272 A B r).
Proof. exact (@lem17784 (term32 r) ((term47 A B r) = r)). Qed.
Lemma lem7677162 {A B : Type'} : (term49 A B) = (term273 A B).
Proof. exact (fun_ext (fun r : nat => @lem7677161 A B r)). Qed.
Lemma lem7677163 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677164 {A B : Type'} : (term51 A B) = (term274 A B).
Proof. exact (MK_COMB (@lem7677163) (@lem7677162 A B)). Qed.
Lemma lem7677165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677166 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7677165) (@lem7677146 A B)). Qed.
Lemma lem7677167 {A B : Type'} : (term53 A B) = (term275 A B).
Proof. exact (MK_COMB (@lem7677166 A B) (@lem7677164 A B)). Qed.
Lemma lem7677168 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7677169 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7677168 B a)). Qed.
Lemma lem7677170 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7677171 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7677170 B) (@lem7677169 B)). Qed.
Lemma lem7677186 {B : Type'} (r : nat) : ((term32 r) = ((term93 B r) = r)) = (term304 B r).
Proof. exact (@lem17784 (term32 r) ((term93 B r) = r)). Qed.
Lemma lem7677187 {B : Type'} : (term95 B) = (term305 B).
Proof. exact (fun_ext (fun r : nat => @lem7677186 B r)). Qed.
Lemma lem7677188 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677189 {B : Type'} : (term97 B) = (term306 B).
Proof. exact (MK_COMB (@lem7677188) (@lem7677187 B)). Qed.
Lemma lem7677190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677191 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7677190) (@lem7677171 B)). Qed.
Lemma lem7677192 {B : Type'} : (term99 B) = (term307 B).
Proof. exact (MK_COMB (@lem7677191 B) (@lem7677189 B)). Qed.
Lemma lem7677193 {B : Type'} : (term345 B) = (term99 B).
Proof. exact (@lem16933 (term99 B)). Qed.
Lemma lem7677194 {B : Type'} : (term345 B) = (term307 B).
Proof. exact (TRANS (@lem7677193 B) (@lem7677192 B)). Qed.
Lemma lem7677195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677196 {A B : Type'} : (term276 A B) = (term277 A B).
Proof. exact (MK_COMB (@lem7677195) (@lem7677167 A B)). Qed.
Lemma lem7677197 {A B : Type'} : (term358 A B) = (term359 A B).
Proof. exact (MK_COMB (@lem7677196 A B) (@lem7677194 B)). Qed.
Lemma lem7677198 {A B : Type'} : (term360 A B) = (term358 A B).
Proof. exact (@lem17362 (term53 A B) (term136 B)). Qed.
Lemma lem7677199 {A B : Type'} : (term360 A B) = (term359 A B).
Proof. exact (TRANS (@lem7677198 A B) (@lem7677197 A B)). Qed.
Lemma lem7677200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677201 {A : Type'} : (term308 A) = (term309 A).
Proof. exact (MK_COMB (@lem7677200) (@lem7677142 A)). Qed.
Lemma lem7677202 {A B : Type'} : (term387 A B) = (term388 A B).
Proof. exact (MK_COMB (@lem7677201 A) (@lem7677199 A B)). Qed.
Lemma lem7677203 {A B : Type'} : (term389 A B) = (term387 A B).
Proof. exact (@lem17362 (term99 A) (term142 A B)). Qed.
Lemma lem7677204 {A B : Type'} : (term389 A B) = (term388 A B).
Proof. exact (TRANS (@lem7677203 A B) (@lem7677202 A B)). Qed.
Lemma lem7677205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677206 {A B : Type'} : (term284 A B) = (term285 A B).
Proof. exact (MK_COMB (@lem7677205) (@lem7677117 A B)). Qed.
Lemma lem7677207 {A B : Type'} : (term390 A B) = (term391 A B).
Proof. exact (MK_COMB (@lem7677206 A B) (@lem7677204 A B)). Qed.
Lemma lem7677208 {A B : Type'} : (term392 A B) = (term390 A B).
Proof. exact (@lem17362 (term43 A B) (term156 A B)). Qed.
Lemma lem7677209 {A B : Type'} : (term392 A B) = (term391 A B).
Proof. exact (TRANS (@lem7677208 A B) (@lem7677207 A B)). Qed.
Lemma lem7677211 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7677212 {A B : Type'} : (term393 A B) = (term394 A B).
Proof. exact (MK_COMB (@lem7677211 A B) (@lem7677209 A B)). Qed.
Lemma lem7677213 {A B : Type'} : (term395 A B) = (term393 A B).
Proof. exact (@lem17160 (term20 A B) (term157 A B)). Qed.
Lemma lem7677214 {A B : Type'} : (term395 A B) = (term394 A B).
Proof. exact (TRANS (@lem7677213 A B) (@lem7677212 A B)). Qed.
Lemma lem7677215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7677216 {A B : Type'} : (term396 A B) = (term397 A B).
Proof. exact (MK_COMB (@lem7677215) (@lem7677089 A B)). Qed.
Lemma lem7677217 {A B : Type'} : (term398 A B) = (term399 A B).
Proof. exact (MK_COMB (@lem7677216 A B) (@lem7677214 A B)). Qed.
Lemma lem7677218 {A B : Type'} : (term400 A B) = (term398 A B).
Proof. exact (@lem17045 (term154 A B) (term158 A B)). Qed.
Lemma lem7677219 {A B : Type'} : (term400 A B) = (term399 A B).
Proof. exact (TRANS (@lem7677218 A B) (@lem7677217 A B)). Qed.
Lemma lem7677221 {A : Type'} : (term333 A) = (term333 A).
Proof. exact (eq_refl (term333 A)). Qed.
Lemma lem7677222 {A B : Type'} : (term401 A B) = (term402 A B).
Proof. exact (MK_COMB (@lem7677221 A) (@lem7677219 A B)). Qed.
Lemma lem7677223 {A B : Type'} : (term403 A B) = (term401 A B).
Proof. exact (@lem17160 (term83 A) (term159 A B)). Qed.
Lemma lem7677224 {A B : Type'} : (term403 A B) = (term402 A B).
Proof. exact (TRANS (@lem7677223 A B) (@lem7677222 A B)). Qed.
Lemma lem7677225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7677226 {A B : Type'} : (term404 A B) = (term405 A B).
Proof. exact (MK_COMB (@lem7677225) (@lem7676961 A B)). Qed.
Lemma lem7677227 {A B : Type'} : (term406 A B) = (term407 A B).
Proof. exact (MK_COMB (@lem7677226 A B) (@lem7677224 A B)). Qed.
Lemma lem7677228 {A B : Type'} : (term408 A B) = (term406 A B).
Proof. exact (@lem17045 (term149 A B) (term162 A B)). Qed.
Lemma lem7677229 {A B : Type'} : (term408 A B) = (term407 A B).
Proof. exact (TRANS (@lem7677228 A B) (@lem7677227 A B)). Qed.
Lemma lem7677231 {B : Type'} : (term333 B) = (term333 B).
Proof. exact (eq_refl (term333 B)). Qed.
Lemma lem7677232 {A B : Type'} : (term409 A B) = (term410 A B).
Proof. exact (MK_COMB (@lem7677231 B) (@lem7677229 A B)). Qed.
Lemma lem7677233 {A B : Type'} : (term411 A B) = (term409 A B).
Proof. exact (@lem17160 (term83 B) (term163 A B)). Qed.
Lemma lem7677234 {A B : Type'} : (term411 A B) = (term410 A B).
Proof. exact (TRANS (@lem7677233 A B) (@lem7677232 A B)). Qed.
Lemma lem7677235 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7677236 {A B : Type'} : (term412 A B) = (term413 A B).
Proof. exact (MK_COMB (@lem7677235) (@lem7676695 A B)). Qed.
Lemma lem7677237 {A B : Type'} : (term414 A B) = (term415 A B).
Proof. exact (MK_COMB (@lem7677236 A B) (@lem7677234 A B)). Qed.
Lemma lem7677238 {A B : Type'} : (term205 A B) = (term414 A B).
Proof. exact (@lem17045 (term199 A B) (term198 A B)). Qed.
Lemma lem7677239 {A B : Type'} : (term205 A B) = (term415 A B).
Proof. exact (TRANS (@lem7677238 A B) (@lem7677237 A B)). Qed.
Lemma lem7677297 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7677298 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7677297 nat P Q). Qed.
Lemma lem7677299 {A : Type'} : (term420 A) = (term421 A).
Proof. exact (@lem7677298 (term422 A) (term423 A)). Qed.
Lemma lem7677300 {A : Type'} (r : nat) : (term424 A r) = (term425 A r).
Proof. exact (eq_refl (term424 A r)). Qed.
Lemma lem7677301 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677302 {A : Type'} (r : nat) : (term426 A r) = (term427 A r).
Proof. exact (MK_COMB (@lem7677301) (@lem7677300 A r)). Qed.
Lemma lem7677303 {A : Type'} (r : nat) : (term428 A r) = (term429 A r).
Proof. exact (eq_refl (term428 A r)). Qed.
Lemma lem7677304 {A : Type'} (r : nat) : (term430 A r) = (term227 A r).
Proof. exact (MK_COMB (@lem7677302 A r) (@lem7677303 A r)). Qed.
Lemma lem7677305 {A : Type'} : (term431 A) = (term228 A).
Proof. exact (fun_ext (fun r : nat => @lem7677304 A r)). Qed.
Lemma lem7677306 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677307 {A : Type'} : (term420 A) = (term229 A).
Proof. exact (MK_COMB (@lem7677306) (@lem7677305 A)). Qed.
Lemma lem7677308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7677309 {A : Type'} : (term432 A) = (term433 A).
Proof. exact (MK_COMB (@lem7677308) (@lem7677307 A)). Qed.
Lemma lem7677310 {A : Type'} (r : nat) : (term424 A r) = (term425 A r).
Proof. exact (eq_refl (term424 A r)). Qed.
Lemma lem7677311 {A : Type'} : (term434 A) = (term422 A).
Proof. exact (fun_ext (fun r : nat => @lem7677310 A r)). Qed.
Lemma lem7677312 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677313 {A : Type'} : (term435 A) = (term436 A).
Proof. exact (MK_COMB (@lem7677312) (@lem7677311 A)). Qed.
Lemma lem7677314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677315 {A : Type'} : (term437 A) = (term438 A).
Proof. exact (MK_COMB (@lem7677314) (@lem7677313 A)). Qed.
Lemma lem7677316 {A : Type'} (r : nat) : (term428 A r) = (term429 A r).
Proof. exact (eq_refl (term428 A r)). Qed.
Lemma lem7677317 {A : Type'} : (term439 A) = (term423 A).
Proof. exact (fun_ext (fun r : nat => @lem7677316 A r)). Qed.
Lemma lem7677318 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677319 {A : Type'} : (term440 A) = (term441 A).
Proof. exact (MK_COMB (@lem7677318) (@lem7677317 A)). Qed.
Lemma lem7677320 {A : Type'} : (term421 A) = (term442 A).
Proof. exact (MK_COMB (@lem7677315 A) (@lem7677319 A)). Qed.
Lemma lem7677321 {A : Type'} : ((term420 A) = (term421 A)) = ((term229 A) = (term442 A)).
Proof. exact (MK_COMB (@lem7677309 A) (@lem7677320 A)). Qed.
Lemma lem7677322 {A : Type'} : (term229 A) = (term442 A).
Proof. exact (EQ_MP (@lem7677321 A) (@lem7677299 A)). Qed.
Lemma lem7677419 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (eq_refl (term98 A)). Qed.
Lemma lem7677420 {A : Type'} : (term230 A) = (term443 A).
Proof. exact (MK_COMB (@lem7677419 A) (@lem7677322 A)). Qed.
Lemma lem7677421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677422 {A : Type'} : (term242 A) = (term444 A).
Proof. exact (MK_COMB (@lem7677421) (@lem7677420 A)). Qed.
Lemma lem7677428 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7677429 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7677428 nat P Q). Qed.
Lemma lem7677430 {A B : Type'} : (term445 A B) = (term446 A B).
Proof. exact (@lem7677429 (term447 A B) (term448 A B)). Qed.
Lemma lem7677431 {A B : Type'} (r : nat) : (term449 A B r) = (term450 A B r).
Proof. exact (eq_refl (term449 A B r)). Qed.
Lemma lem7677432 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677433 {A B : Type'} (r : nat) : (term451 A B r) = (term452 A B r).
Proof. exact (MK_COMB (@lem7677432) (@lem7677431 A B r)). Qed.
Lemma lem7677434 {A B : Type'} (r : nat) : (term453 A B r) = (term454 A B r).
Proof. exact (eq_refl (term453 A B r)). Qed.
Lemma lem7677435 {A B : Type'} (r : nat) : (term455 A B r) = (term231 A B r).
Proof. exact (MK_COMB (@lem7677433 A B r) (@lem7677434 A B r)). Qed.
Lemma lem7677436 {A B : Type'} : (term456 A B) = (term232 A B).
Proof. exact (fun_ext (fun r : nat => @lem7677435 A B r)). Qed.
Lemma lem7677437 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677438 {A B : Type'} : (term445 A B) = (term233 A B).
Proof. exact (MK_COMB (@lem7677437) (@lem7677436 A B)). Qed.
Lemma lem7677439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7677440 {A B : Type'} : (term457 A B) = (term458 A B).
Proof. exact (MK_COMB (@lem7677439) (@lem7677438 A B)). Qed.
Lemma lem7677441 {A B : Type'} (r : nat) : (term449 A B r) = (term450 A B r).
Proof. exact (eq_refl (term449 A B r)). Qed.
Lemma lem7677442 {A B : Type'} : (term459 A B) = (term447 A B).
Proof. exact (fun_ext (fun r : nat => @lem7677441 A B r)). Qed.
Lemma lem7677443 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677444 {A B : Type'} : (term460 A B) = (term461 A B).
Proof. exact (MK_COMB (@lem7677443) (@lem7677442 A B)). Qed.
Lemma lem7677445 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677446 {A B : Type'} : (term462 A B) = (term463 A B).
Proof. exact (MK_COMB (@lem7677445) (@lem7677444 A B)). Qed.
Lemma lem7677447 {A B : Type'} (r : nat) : (term453 A B r) = (term454 A B r).
Proof. exact (eq_refl (term453 A B r)). Qed.
Lemma lem7677448 {A B : Type'} : (term464 A B) = (term448 A B).
Proof. exact (fun_ext (fun r : nat => @lem7677447 A B r)). Qed.
Lemma lem7677449 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677450 {A B : Type'} : (term465 A B) = (term466 A B).
Proof. exact (MK_COMB (@lem7677449) (@lem7677448 A B)). Qed.
Lemma lem7677451 {A B : Type'} : (term446 A B) = (term467 A B).
Proof. exact (MK_COMB (@lem7677446 A B) (@lem7677450 A B)). Qed.
Lemma lem7677452 {A B : Type'} : ((term445 A B) = (term446 A B)) = ((term233 A B) = (term467 A B)).
Proof. exact (MK_COMB (@lem7677440 A B) (@lem7677451 A B)). Qed.
Lemma lem7677453 {A B : Type'} : (term233 A B) = (term467 A B).
Proof. exact (EQ_MP (@lem7677452 A B) (@lem7677430 A B)). Qed.
Lemma lem7677550 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (eq_refl (term52 A B)). Qed.
Lemma lem7677551 {A B : Type'} : (term234 A B) = (term468 A B).
Proof. exact (MK_COMB (@lem7677550 A B) (@lem7677453 A B)). Qed.
Lemma lem7677552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677553 {A B : Type'} : (term237 A B) = (term469 A B).
Proof. exact (MK_COMB (@lem7677552) (@lem7677551 A B)). Qed.
Lemma lem7677559 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7677560 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7677559 nat P Q). Qed.
Lemma lem7677561 {B : Type'} : (term420 B) = (term421 B).
Proof. exact (@lem7677560 (term422 B) (term423 B)). Qed.
Lemma lem7677562 {B : Type'} (r : nat) : (term424 B r) = (term425 B r).
Proof. exact (eq_refl (term424 B r)). Qed.
Lemma lem7677563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677564 {B : Type'} (r : nat) : (term426 B r) = (term427 B r).
Proof. exact (MK_COMB (@lem7677563) (@lem7677562 B r)). Qed.
Lemma lem7677565 {B : Type'} (r : nat) : (term428 B r) = (term429 B r).
Proof. exact (eq_refl (term428 B r)). Qed.
Lemma lem7677566 {B : Type'} (r : nat) : (term430 B r) = (term227 B r).
Proof. exact (MK_COMB (@lem7677564 B r) (@lem7677565 B r)). Qed.
Lemma lem7677567 {B : Type'} : (term431 B) = (term228 B).
Proof. exact (fun_ext (fun r : nat => @lem7677566 B r)). Qed.
Lemma lem7677568 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677569 {B : Type'} : (term420 B) = (term229 B).
Proof. exact (MK_COMB (@lem7677568) (@lem7677567 B)). Qed.
Lemma lem7677570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7677571 {B : Type'} : (term432 B) = (term433 B).
Proof. exact (MK_COMB (@lem7677570) (@lem7677569 B)). Qed.
Lemma lem7677572 {B : Type'} (r : nat) : (term424 B r) = (term425 B r).
Proof. exact (eq_refl (term424 B r)). Qed.
Lemma lem7677573 {B : Type'} : (term434 B) = (term422 B).
Proof. exact (fun_ext (fun r : nat => @lem7677572 B r)). Qed.
Lemma lem7677574 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677575 {B : Type'} : (term435 B) = (term436 B).
Proof. exact (MK_COMB (@lem7677574) (@lem7677573 B)). Qed.
Lemma lem7677576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677577 {B : Type'} : (term437 B) = (term438 B).
Proof. exact (MK_COMB (@lem7677576) (@lem7677575 B)). Qed.
Lemma lem7677578 {B : Type'} (r : nat) : (term428 B r) = (term429 B r).
Proof. exact (eq_refl (term428 B r)). Qed.
Lemma lem7677579 {B : Type'} : (term439 B) = (term423 B).
Proof. exact (fun_ext (fun r : nat => @lem7677578 B r)). Qed.
Lemma lem7677580 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677581 {B : Type'} : (term440 B) = (term441 B).
Proof. exact (MK_COMB (@lem7677580) (@lem7677579 B)). Qed.
Lemma lem7677582 {B : Type'} : (term421 B) = (term442 B).
Proof. exact (MK_COMB (@lem7677577 B) (@lem7677581 B)). Qed.
Lemma lem7677583 {B : Type'} : ((term420 B) = (term421 B)) = ((term229 B) = (term442 B)).
Proof. exact (MK_COMB (@lem7677571 B) (@lem7677582 B)). Qed.
Lemma lem7677584 {B : Type'} : (term229 B) = (term442 B).
Proof. exact (EQ_MP (@lem7677583 B) (@lem7677561 B)). Qed.
Lemma lem7677681 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7677682 {B : Type'} : (term230 B) = (term443 B).
Proof. exact (MK_COMB (@lem7677681 B) (@lem7677584 B)). Qed.
Lemma lem7677683 {A B : Type'} : (term239 A B) = (term470 A B).
Proof. exact (MK_COMB (@lem7677553 A B) (@lem7677682 B)). Qed.
Lemma lem7677684 {A B : Type'} : (term244 A B) = (term471 A B).
Proof. exact (MK_COMB (@lem7677422 A) (@lem7677683 A B)). Qed.
Lemma lem7677685 {A B : Type'} : (term247 A B) = (term247 A B).
Proof. exact (eq_refl (term247 A B)). Qed.
Lemma lem7677686 {A B : Type'} : (term249 A B) = (term472 A B).
Proof. exact (MK_COMB (@lem7677685 A B) (@lem7677684 A B)). Qed.
Lemma lem7677687 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7677688 {A B : Type'} : (term254 A B) = (term473 A B).
Proof. exact (MK_COMB (@lem7677687 A B) (@lem7677686 A B)). Qed.
Lemma lem7677689 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7677690 {A B : Type'} : (term294 A B) = (term474 A B).
Proof. exact (MK_COMB (@lem7677689) (@lem7677688 A B)). Qed.
Lemma lem7677748 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7677749 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7677748 nat P Q). Qed.
Lemma lem7677750 {A : Type'} : (term420 A) = (term421 A).
Proof. exact (@lem7677749 (term422 A) (term423 A)). Qed.
Lemma lem7677751 {A : Type'} (r : nat) : (term424 A r) = (term425 A r).
Proof. exact (eq_refl (term424 A r)). Qed.
Lemma lem7677752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677753 {A : Type'} (r : nat) : (term426 A r) = (term427 A r).
Proof. exact (MK_COMB (@lem7677752) (@lem7677751 A r)). Qed.
Lemma lem7677754 {A : Type'} (r : nat) : (term428 A r) = (term429 A r).
Proof. exact (eq_refl (term428 A r)). Qed.
Lemma lem7677755 {A : Type'} (r : nat) : (term430 A r) = (term227 A r).
Proof. exact (MK_COMB (@lem7677753 A r) (@lem7677754 A r)). Qed.
Lemma lem7677756 {A : Type'} : (term431 A) = (term228 A).
Proof. exact (fun_ext (fun r : nat => @lem7677755 A r)). Qed.
Lemma lem7677757 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677758 {A : Type'} : (term420 A) = (term229 A).
Proof. exact (MK_COMB (@lem7677757) (@lem7677756 A)). Qed.
Lemma lem7677759 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7677760 {A : Type'} : (term432 A) = (term433 A).
Proof. exact (MK_COMB (@lem7677759) (@lem7677758 A)). Qed.
Lemma lem7677761 {A : Type'} (r : nat) : (term424 A r) = (term425 A r).
Proof. exact (eq_refl (term424 A r)). Qed.
Lemma lem7677762 {A : Type'} : (term434 A) = (term422 A).
Proof. exact (fun_ext (fun r : nat => @lem7677761 A r)). Qed.
Lemma lem7677763 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677764 {A : Type'} : (term435 A) = (term436 A).
Proof. exact (MK_COMB (@lem7677763) (@lem7677762 A)). Qed.
Lemma lem7677765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677766 {A : Type'} : (term437 A) = (term438 A).
Proof. exact (MK_COMB (@lem7677765) (@lem7677764 A)). Qed.
Lemma lem7677767 {A : Type'} (r : nat) : (term428 A r) = (term429 A r).
Proof. exact (eq_refl (term428 A r)). Qed.
Lemma lem7677768 {A : Type'} : (term439 A) = (term423 A).
Proof. exact (fun_ext (fun r : nat => @lem7677767 A r)). Qed.
Lemma lem7677769 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677770 {A : Type'} : (term440 A) = (term441 A).
Proof. exact (MK_COMB (@lem7677769) (@lem7677768 A)). Qed.
Lemma lem7677771 {A : Type'} : (term421 A) = (term442 A).
Proof. exact (MK_COMB (@lem7677766 A) (@lem7677770 A)). Qed.
Lemma lem7677772 {A : Type'} : ((term420 A) = (term421 A)) = ((term229 A) = (term442 A)).
Proof. exact (MK_COMB (@lem7677760 A) (@lem7677771 A)). Qed.
Lemma lem7677773 {A : Type'} : (term229 A) = (term442 A).
Proof. exact (EQ_MP (@lem7677772 A) (@lem7677750 A)). Qed.
Lemma lem7677870 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (eq_refl (term98 A)). Qed.
Lemma lem7677871 {A : Type'} : (term230 A) = (term443 A).
Proof. exact (MK_COMB (@lem7677870 A) (@lem7677773 A)). Qed.
Lemma lem7677872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677873 {A : Type'} : (term242 A) = (term444 A).
Proof. exact (MK_COMB (@lem7677872) (@lem7677871 A)). Qed.
Lemma lem7677879 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7677880 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7677879 nat P Q). Qed.
Lemma lem7677881 {A B : Type'} : (term475 A B) = (term476 A B).
Proof. exact (@lem7677880 (term477 A B) (term478 A B)). Qed.
Lemma lem7677882 {A B : Type'} (r : nat) : (term479 A B r) = (term480 A B r).
Proof. exact (eq_refl (term479 A B r)). Qed.
Lemma lem7677883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677884 {A B : Type'} (r : nat) : (term481 A B r) = (term482 A B r).
Proof. exact (MK_COMB (@lem7677883) (@lem7677882 A B r)). Qed.
Lemma lem7677885 {A B : Type'} (r : nat) : (term483 A B r) = (term484 A B r).
Proof. exact (eq_refl (term483 A B r)). Qed.
Lemma lem7677886 {A B : Type'} (r : nat) : (term485 A B r) = (term272 A B r).
Proof. exact (MK_COMB (@lem7677884 A B r) (@lem7677885 A B r)). Qed.
Lemma lem7677887 {A B : Type'} : (term486 A B) = (term273 A B).
Proof. exact (fun_ext (fun r : nat => @lem7677886 A B r)). Qed.
Lemma lem7677888 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677889 {A B : Type'} : (term475 A B) = (term274 A B).
Proof. exact (MK_COMB (@lem7677888) (@lem7677887 A B)). Qed.
Lemma lem7677890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7677891 {A B : Type'} : (term487 A B) = (term488 A B).
Proof. exact (MK_COMB (@lem7677890) (@lem7677889 A B)). Qed.
Lemma lem7677892 {A B : Type'} (r : nat) : (term479 A B r) = (term480 A B r).
Proof. exact (eq_refl (term479 A B r)). Qed.
Lemma lem7677893 {A B : Type'} : (term489 A B) = (term477 A B).
Proof. exact (fun_ext (fun r : nat => @lem7677892 A B r)). Qed.
Lemma lem7677894 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677895 {A B : Type'} : (term490 A B) = (term491 A B).
Proof. exact (MK_COMB (@lem7677894) (@lem7677893 A B)). Qed.
Lemma lem7677896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7677897 {A B : Type'} : (term492 A B) = (term493 A B).
Proof. exact (MK_COMB (@lem7677896) (@lem7677895 A B)). Qed.
Lemma lem7677898 {A B : Type'} (r : nat) : (term483 A B r) = (term484 A B r).
Proof. exact (eq_refl (term483 A B r)). Qed.
Lemma lem7677899 {A B : Type'} : (term494 A B) = (term478 A B).
Proof. exact (fun_ext (fun r : nat => @lem7677898 A B r)). Qed.
Lemma lem7677900 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7677901 {A B : Type'} : (term495 A B) = (term496 A B).
Proof. exact (MK_COMB (@lem7677900) (@lem7677899 A B)). Qed.
Lemma lem7677902 {A B : Type'} : (term476 A B) = (term497 A B).
Proof. exact (MK_COMB (@lem7677897 A B) (@lem7677901 A B)). Qed.
Lemma lem7677903 {A B : Type'} : ((term475 A B) = (term476 A B)) = ((term274 A B) = (term497 A B)).
Proof. exact (MK_COMB (@lem7677891 A B) (@lem7677902 A B)). Qed.
Lemma lem7677904 {A B : Type'} : (term274 A B) = (term497 A B).
Proof. exact (EQ_MP (@lem7677903 A B) (@lem7677881 A B)). Qed.
Lemma lem7678001 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (eq_refl (term52 A B)). Qed.
Lemma lem7678002 {A B : Type'} : (term275 A B) = (term498 A B).
Proof. exact (MK_COMB (@lem7678001 A B) (@lem7677904 A B)). Qed.
Lemma lem7678003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678004 {A B : Type'} : (term277 A B) = (term499 A B).
Proof. exact (MK_COMB (@lem7678003) (@lem7678002 A B)). Qed.
Lemma lem7678010 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7678011 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7678010 nat P Q). Qed.
Lemma lem7678012 {B : Type'} : (term420 B) = (term421 B).
Proof. exact (@lem7678011 (term422 B) (term423 B)). Qed.
Lemma lem7678013 {B : Type'} (r : nat) : (term424 B r) = (term425 B r).
Proof. exact (eq_refl (term424 B r)). Qed.
Lemma lem7678014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678015 {B : Type'} (r : nat) : (term426 B r) = (term427 B r).
Proof. exact (MK_COMB (@lem7678014) (@lem7678013 B r)). Qed.
Lemma lem7678016 {B : Type'} (r : nat) : (term428 B r) = (term429 B r).
Proof. exact (eq_refl (term428 B r)). Qed.
Lemma lem7678017 {B : Type'} (r : nat) : (term430 B r) = (term227 B r).
Proof. exact (MK_COMB (@lem7678015 B r) (@lem7678016 B r)). Qed.
Lemma lem7678018 {B : Type'} : (term431 B) = (term228 B).
Proof. exact (fun_ext (fun r : nat => @lem7678017 B r)). Qed.
Lemma lem7678019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678020 {B : Type'} : (term420 B) = (term229 B).
Proof. exact (MK_COMB (@lem7678019) (@lem7678018 B)). Qed.
Lemma lem7678021 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7678022 {B : Type'} : (term432 B) = (term433 B).
Proof. exact (MK_COMB (@lem7678021) (@lem7678020 B)). Qed.
Lemma lem7678023 {B : Type'} (r : nat) : (term424 B r) = (term425 B r).
Proof. exact (eq_refl (term424 B r)). Qed.
Lemma lem7678024 {B : Type'} : (term434 B) = (term422 B).
Proof. exact (fun_ext (fun r : nat => @lem7678023 B r)). Qed.
Lemma lem7678025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678026 {B : Type'} : (term435 B) = (term436 B).
Proof. exact (MK_COMB (@lem7678025) (@lem7678024 B)). Qed.
Lemma lem7678027 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678028 {B : Type'} : (term437 B) = (term438 B).
Proof. exact (MK_COMB (@lem7678027) (@lem7678026 B)). Qed.
Lemma lem7678029 {B : Type'} (r : nat) : (term428 B r) = (term429 B r).
Proof. exact (eq_refl (term428 B r)). Qed.
Lemma lem7678030 {B : Type'} : (term439 B) = (term423 B).
Proof. exact (fun_ext (fun r : nat => @lem7678029 B r)). Qed.
Lemma lem7678031 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678032 {B : Type'} : (term440 B) = (term441 B).
Proof. exact (MK_COMB (@lem7678031) (@lem7678030 B)). Qed.
Lemma lem7678033 {B : Type'} : (term421 B) = (term442 B).
Proof. exact (MK_COMB (@lem7678028 B) (@lem7678032 B)). Qed.
Lemma lem7678034 {B : Type'} : ((term420 B) = (term421 B)) = ((term229 B) = (term442 B)).
Proof. exact (MK_COMB (@lem7678022 B) (@lem7678033 B)). Qed.
Lemma lem7678035 {B : Type'} : (term229 B) = (term442 B).
Proof. exact (EQ_MP (@lem7678034 B) (@lem7678012 B)). Qed.
Lemma lem7678132 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7678133 {B : Type'} : (term230 B) = (term443 B).
Proof. exact (MK_COMB (@lem7678132 B) (@lem7678035 B)). Qed.
Lemma lem7678134 {A B : Type'} : (term279 A B) = (term500 A B).
Proof. exact (MK_COMB (@lem7678004 A B) (@lem7678133 B)). Qed.
Lemma lem7678135 {A B : Type'} : (term282 A B) = (term501 A B).
Proof. exact (MK_COMB (@lem7677873 A) (@lem7678134 A B)). Qed.
Lemma lem7678136 {A B : Type'} : (term285 A B) = (term285 A B).
Proof. exact (eq_refl (term285 A B)). Qed.
Lemma lem7678137 {A B : Type'} : (term287 A B) = (term502 A B).
Proof. exact (MK_COMB (@lem7678136 A B) (@lem7678135 A B)). Qed.
Lemma lem7678138 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7678139 {A B : Type'} : (term291 A B) = (term503 A B).
Proof. exact (MK_COMB (@lem7678138 A B) (@lem7678137 A B)). Qed.
Lemma lem7678140 {A B : Type'} : (term296 A B) = (term504 A B).
Proof. exact (MK_COMB (@lem7677690 A B) (@lem7678139 A B)). Qed.
Lemma lem7678141 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (eq_refl (term299 A)). Qed.
Lemma lem7678142 {A B : Type'} : (term301 A B) = (term505 A B).
Proof. exact (MK_COMB (@lem7678141 A) (@lem7678140 A B)). Qed.
Lemma lem7678143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7678144 {A B : Type'} : (term338 A B) = (term506 A B).
Proof. exact (MK_COMB (@lem7678143) (@lem7678142 A B)). Qed.
Lemma lem7678202 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7678203 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7678202 nat P Q). Qed.
Lemma lem7678204 {A : Type'} : (term507 A) = (term508 A).
Proof. exact (@lem7678203 (term509 A) (term510 A)). Qed.
Lemma lem7678205 {A : Type'} (r : nat) : (term511 A r) = (term512 A r).
Proof. exact (eq_refl (term511 A r)). Qed.
Lemma lem7678206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678207 {A : Type'} (r : nat) : (term513 A r) = (term514 A r).
Proof. exact (MK_COMB (@lem7678206) (@lem7678205 A r)). Qed.
Lemma lem7678208 {A : Type'} (r : nat) : (term515 A r) = (term516 A r).
Proof. exact (eq_refl (term515 A r)). Qed.
Lemma lem7678209 {A : Type'} (r : nat) : (term517 A r) = (term304 A r).
Proof. exact (MK_COMB (@lem7678207 A r) (@lem7678208 A r)). Qed.
Lemma lem7678210 {A : Type'} : (term518 A) = (term305 A).
Proof. exact (fun_ext (fun r : nat => @lem7678209 A r)). Qed.
Lemma lem7678211 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678212 {A : Type'} : (term507 A) = (term306 A).
Proof. exact (MK_COMB (@lem7678211) (@lem7678210 A)). Qed.
Lemma lem7678213 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7678214 {A : Type'} : (term519 A) = (term520 A).
Proof. exact (MK_COMB (@lem7678213) (@lem7678212 A)). Qed.
Lemma lem7678215 {A : Type'} (r : nat) : (term511 A r) = (term512 A r).
Proof. exact (eq_refl (term511 A r)). Qed.
Lemma lem7678216 {A : Type'} : (term521 A) = (term509 A).
Proof. exact (fun_ext (fun r : nat => @lem7678215 A r)). Qed.
Lemma lem7678217 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678218 {A : Type'} : (term522 A) = (term523 A).
Proof. exact (MK_COMB (@lem7678217) (@lem7678216 A)). Qed.
Lemma lem7678219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678220 {A : Type'} : (term524 A) = (term525 A).
Proof. exact (MK_COMB (@lem7678219) (@lem7678218 A)). Qed.
Lemma lem7678221 {A : Type'} (r : nat) : (term515 A r) = (term516 A r).
Proof. exact (eq_refl (term515 A r)). Qed.
Lemma lem7678222 {A : Type'} : (term526 A) = (term510 A).
Proof. exact (fun_ext (fun r : nat => @lem7678221 A r)). Qed.
Lemma lem7678223 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678224 {A : Type'} : (term527 A) = (term528 A).
Proof. exact (MK_COMB (@lem7678223) (@lem7678222 A)). Qed.
Lemma lem7678225 {A : Type'} : (term508 A) = (term529 A).
Proof. exact (MK_COMB (@lem7678220 A) (@lem7678224 A)). Qed.
Lemma lem7678226 {A : Type'} : ((term507 A) = (term508 A)) = ((term306 A) = (term529 A)).
Proof. exact (MK_COMB (@lem7678214 A) (@lem7678225 A)). Qed.
Lemma lem7678227 {A : Type'} : (term306 A) = (term529 A).
Proof. exact (EQ_MP (@lem7678226 A) (@lem7678204 A)). Qed.
Lemma lem7678324 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (eq_refl (term98 A)). Qed.
Lemma lem7678325 {A : Type'} : (term307 A) = (term530 A).
Proof. exact (MK_COMB (@lem7678324 A) (@lem7678227 A)). Qed.
Lemma lem7678326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678327 {A : Type'} : (term309 A) = (term531 A).
Proof. exact (MK_COMB (@lem7678326) (@lem7678325 A)). Qed.
Lemma lem7678333 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7678334 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7678333 nat P Q). Qed.
Lemma lem7678335 {A B : Type'} : (term445 A B) = (term446 A B).
Proof. exact (@lem7678334 (term447 A B) (term448 A B)). Qed.
Lemma lem7678336 {A B : Type'} (r : nat) : (term449 A B r) = (term450 A B r).
Proof. exact (eq_refl (term449 A B r)). Qed.
Lemma lem7678337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678338 {A B : Type'} (r : nat) : (term451 A B r) = (term452 A B r).
Proof. exact (MK_COMB (@lem7678337) (@lem7678336 A B r)). Qed.
Lemma lem7678339 {A B : Type'} (r : nat) : (term453 A B r) = (term454 A B r).
Proof. exact (eq_refl (term453 A B r)). Qed.
Lemma lem7678340 {A B : Type'} (r : nat) : (term455 A B r) = (term231 A B r).
Proof. exact (MK_COMB (@lem7678338 A B r) (@lem7678339 A B r)). Qed.
Lemma lem7678341 {A B : Type'} : (term456 A B) = (term232 A B).
Proof. exact (fun_ext (fun r : nat => @lem7678340 A B r)). Qed.
Lemma lem7678342 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678343 {A B : Type'} : (term445 A B) = (term233 A B).
Proof. exact (MK_COMB (@lem7678342) (@lem7678341 A B)). Qed.
Lemma lem7678344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7678345 {A B : Type'} : (term457 A B) = (term458 A B).
Proof. exact (MK_COMB (@lem7678344) (@lem7678343 A B)). Qed.
Lemma lem7678346 {A B : Type'} (r : nat) : (term449 A B r) = (term450 A B r).
Proof. exact (eq_refl (term449 A B r)). Qed.
Lemma lem7678347 {A B : Type'} : (term459 A B) = (term447 A B).
Proof. exact (fun_ext (fun r : nat => @lem7678346 A B r)). Qed.
Lemma lem7678348 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678349 {A B : Type'} : (term460 A B) = (term461 A B).
Proof. exact (MK_COMB (@lem7678348) (@lem7678347 A B)). Qed.
Lemma lem7678350 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678351 {A B : Type'} : (term462 A B) = (term463 A B).
Proof. exact (MK_COMB (@lem7678350) (@lem7678349 A B)). Qed.
Lemma lem7678352 {A B : Type'} (r : nat) : (term453 A B r) = (term454 A B r).
Proof. exact (eq_refl (term453 A B r)). Qed.
Lemma lem7678353 {A B : Type'} : (term464 A B) = (term448 A B).
Proof. exact (fun_ext (fun r : nat => @lem7678352 A B r)). Qed.
Lemma lem7678354 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678355 {A B : Type'} : (term465 A B) = (term466 A B).
Proof. exact (MK_COMB (@lem7678354) (@lem7678353 A B)). Qed.
Lemma lem7678356 {A B : Type'} : (term446 A B) = (term467 A B).
Proof. exact (MK_COMB (@lem7678351 A B) (@lem7678355 A B)). Qed.
Lemma lem7678357 {A B : Type'} : ((term445 A B) = (term446 A B)) = ((term233 A B) = (term467 A B)).
Proof. exact (MK_COMB (@lem7678345 A B) (@lem7678356 A B)). Qed.
Lemma lem7678358 {A B : Type'} : (term233 A B) = (term467 A B).
Proof. exact (EQ_MP (@lem7678357 A B) (@lem7678335 A B)). Qed.
Lemma lem7678455 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (eq_refl (term52 A B)). Qed.
Lemma lem7678456 {A B : Type'} : (term234 A B) = (term468 A B).
Proof. exact (MK_COMB (@lem7678455 A B) (@lem7678358 A B)). Qed.
Lemma lem7678457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678458 {A B : Type'} : (term237 A B) = (term469 A B).
Proof. exact (MK_COMB (@lem7678457) (@lem7678456 A B)). Qed.
Lemma lem7678464 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7678465 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7678464 nat P Q). Qed.
Lemma lem7678466 {B : Type'} : (term420 B) = (term421 B).
Proof. exact (@lem7678465 (term422 B) (term423 B)). Qed.
Lemma lem7678467 {B : Type'} (r : nat) : (term424 B r) = (term425 B r).
Proof. exact (eq_refl (term424 B r)). Qed.
Lemma lem7678468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678469 {B : Type'} (r : nat) : (term426 B r) = (term427 B r).
Proof. exact (MK_COMB (@lem7678468) (@lem7678467 B r)). Qed.
Lemma lem7678470 {B : Type'} (r : nat) : (term428 B r) = (term429 B r).
Proof. exact (eq_refl (term428 B r)). Qed.
Lemma lem7678471 {B : Type'} (r : nat) : (term430 B r) = (term227 B r).
Proof. exact (MK_COMB (@lem7678469 B r) (@lem7678470 B r)). Qed.
Lemma lem7678472 {B : Type'} : (term431 B) = (term228 B).
Proof. exact (fun_ext (fun r : nat => @lem7678471 B r)). Qed.
Lemma lem7678473 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678474 {B : Type'} : (term420 B) = (term229 B).
Proof. exact (MK_COMB (@lem7678473) (@lem7678472 B)). Qed.
Lemma lem7678475 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7678476 {B : Type'} : (term432 B) = (term433 B).
Proof. exact (MK_COMB (@lem7678475) (@lem7678474 B)). Qed.
Lemma lem7678477 {B : Type'} (r : nat) : (term424 B r) = (term425 B r).
Proof. exact (eq_refl (term424 B r)). Qed.
Lemma lem7678478 {B : Type'} : (term434 B) = (term422 B).
Proof. exact (fun_ext (fun r : nat => @lem7678477 B r)). Qed.
Lemma lem7678479 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678480 {B : Type'} : (term435 B) = (term436 B).
Proof. exact (MK_COMB (@lem7678479) (@lem7678478 B)). Qed.
Lemma lem7678481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678482 {B : Type'} : (term437 B) = (term438 B).
Proof. exact (MK_COMB (@lem7678481) (@lem7678480 B)). Qed.
Lemma lem7678483 {B : Type'} (r : nat) : (term428 B r) = (term429 B r).
Proof. exact (eq_refl (term428 B r)). Qed.
Lemma lem7678484 {B : Type'} : (term439 B) = (term423 B).
Proof. exact (fun_ext (fun r : nat => @lem7678483 B r)). Qed.
Lemma lem7678485 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678486 {B : Type'} : (term440 B) = (term441 B).
Proof. exact (MK_COMB (@lem7678485) (@lem7678484 B)). Qed.
Lemma lem7678487 {B : Type'} : (term421 B) = (term442 B).
Proof. exact (MK_COMB (@lem7678482 B) (@lem7678486 B)). Qed.
Lemma lem7678488 {B : Type'} : ((term420 B) = (term421 B)) = ((term229 B) = (term442 B)).
Proof. exact (MK_COMB (@lem7678476 B) (@lem7678487 B)). Qed.
Lemma lem7678489 {B : Type'} : (term229 B) = (term442 B).
Proof. exact (EQ_MP (@lem7678488 B) (@lem7678466 B)). Qed.
Lemma lem7678586 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7678587 {B : Type'} : (term230 B) = (term443 B).
Proof. exact (MK_COMB (@lem7678586 B) (@lem7678489 B)). Qed.
Lemma lem7678588 {A B : Type'} : (term239 A B) = (term470 A B).
Proof. exact (MK_COMB (@lem7678458 A B) (@lem7678587 B)). Qed.
Lemma lem7678589 {A B : Type'} : (term311 A B) = (term532 A B).
Proof. exact (MK_COMB (@lem7678327 A) (@lem7678588 A B)). Qed.
Lemma lem7678590 {A B : Type'} : (term247 A B) = (term247 A B).
Proof. exact (eq_refl (term247 A B)). Qed.
Lemma lem7678591 {A B : Type'} : (term314 A B) = (term533 A B).
Proof. exact (MK_COMB (@lem7678590 A B) (@lem7678589 A B)). Qed.
Lemma lem7678592 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7678593 {A B : Type'} : (term317 A B) = (term534 A B).
Proof. exact (MK_COMB (@lem7678592 A B) (@lem7678591 A B)). Qed.
Lemma lem7678594 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7678595 {A B : Type'} : (term329 A B) = (term535 A B).
Proof. exact (MK_COMB (@lem7678594) (@lem7678593 A B)). Qed.
Lemma lem7678653 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7678654 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7678653 nat P Q). Qed.
Lemma lem7678655 {A : Type'} : (term507 A) = (term508 A).
Proof. exact (@lem7678654 (term509 A) (term510 A)). Qed.
Lemma lem7678656 {A : Type'} (r : nat) : (term511 A r) = (term512 A r).
Proof. exact (eq_refl (term511 A r)). Qed.
Lemma lem7678657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678658 {A : Type'} (r : nat) : (term513 A r) = (term514 A r).
Proof. exact (MK_COMB (@lem7678657) (@lem7678656 A r)). Qed.
Lemma lem7678659 {A : Type'} (r : nat) : (term515 A r) = (term516 A r).
Proof. exact (eq_refl (term515 A r)). Qed.
Lemma lem7678660 {A : Type'} (r : nat) : (term517 A r) = (term304 A r).
Proof. exact (MK_COMB (@lem7678658 A r) (@lem7678659 A r)). Qed.
Lemma lem7678661 {A : Type'} : (term518 A) = (term305 A).
Proof. exact (fun_ext (fun r : nat => @lem7678660 A r)). Qed.
Lemma lem7678662 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678663 {A : Type'} : (term507 A) = (term306 A).
Proof. exact (MK_COMB (@lem7678662) (@lem7678661 A)). Qed.
Lemma lem7678664 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7678665 {A : Type'} : (term519 A) = (term520 A).
Proof. exact (MK_COMB (@lem7678664) (@lem7678663 A)). Qed.
Lemma lem7678666 {A : Type'} (r : nat) : (term511 A r) = (term512 A r).
Proof. exact (eq_refl (term511 A r)). Qed.
Lemma lem7678667 {A : Type'} : (term521 A) = (term509 A).
Proof. exact (fun_ext (fun r : nat => @lem7678666 A r)). Qed.
Lemma lem7678668 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678669 {A : Type'} : (term522 A) = (term523 A).
Proof. exact (MK_COMB (@lem7678668) (@lem7678667 A)). Qed.
Lemma lem7678670 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678671 {A : Type'} : (term524 A) = (term525 A).
Proof. exact (MK_COMB (@lem7678670) (@lem7678669 A)). Qed.
Lemma lem7678672 {A : Type'} (r : nat) : (term515 A r) = (term516 A r).
Proof. exact (eq_refl (term515 A r)). Qed.
Lemma lem7678673 {A : Type'} : (term526 A) = (term510 A).
Proof. exact (fun_ext (fun r : nat => @lem7678672 A r)). Qed.
Lemma lem7678674 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678675 {A : Type'} : (term527 A) = (term528 A).
Proof. exact (MK_COMB (@lem7678674) (@lem7678673 A)). Qed.
Lemma lem7678676 {A : Type'} : (term508 A) = (term529 A).
Proof. exact (MK_COMB (@lem7678671 A) (@lem7678675 A)). Qed.
Lemma lem7678677 {A : Type'} : ((term507 A) = (term508 A)) = ((term306 A) = (term529 A)).
Proof. exact (MK_COMB (@lem7678665 A) (@lem7678676 A)). Qed.
Lemma lem7678678 {A : Type'} : (term306 A) = (term529 A).
Proof. exact (EQ_MP (@lem7678677 A) (@lem7678655 A)). Qed.
Lemma lem7678775 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (eq_refl (term98 A)). Qed.
Lemma lem7678776 {A : Type'} : (term307 A) = (term530 A).
Proof. exact (MK_COMB (@lem7678775 A) (@lem7678678 A)). Qed.
Lemma lem7678777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678778 {A : Type'} : (term309 A) = (term531 A).
Proof. exact (MK_COMB (@lem7678777) (@lem7678776 A)). Qed.
Lemma lem7678784 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7678785 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7678784 nat P Q). Qed.
Lemma lem7678786 {A B : Type'} : (term475 A B) = (term476 A B).
Proof. exact (@lem7678785 (term477 A B) (term478 A B)). Qed.
Lemma lem7678787 {A B : Type'} (r : nat) : (term479 A B r) = (term480 A B r).
Proof. exact (eq_refl (term479 A B r)). Qed.
Lemma lem7678788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678789 {A B : Type'} (r : nat) : (term481 A B r) = (term482 A B r).
Proof. exact (MK_COMB (@lem7678788) (@lem7678787 A B r)). Qed.
Lemma lem7678790 {A B : Type'} (r : nat) : (term483 A B r) = (term484 A B r).
Proof. exact (eq_refl (term483 A B r)). Qed.
Lemma lem7678791 {A B : Type'} (r : nat) : (term485 A B r) = (term272 A B r).
Proof. exact (MK_COMB (@lem7678789 A B r) (@lem7678790 A B r)). Qed.
Lemma lem7678792 {A B : Type'} : (term486 A B) = (term273 A B).
Proof. exact (fun_ext (fun r : nat => @lem7678791 A B r)). Qed.
Lemma lem7678793 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678794 {A B : Type'} : (term475 A B) = (term274 A B).
Proof. exact (MK_COMB (@lem7678793) (@lem7678792 A B)). Qed.
Lemma lem7678795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7678796 {A B : Type'} : (term487 A B) = (term488 A B).
Proof. exact (MK_COMB (@lem7678795) (@lem7678794 A B)). Qed.
Lemma lem7678797 {A B : Type'} (r : nat) : (term479 A B r) = (term480 A B r).
Proof. exact (eq_refl (term479 A B r)). Qed.
Lemma lem7678798 {A B : Type'} : (term489 A B) = (term477 A B).
Proof. exact (fun_ext (fun r : nat => @lem7678797 A B r)). Qed.
Lemma lem7678799 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678800 {A B : Type'} : (term490 A B) = (term491 A B).
Proof. exact (MK_COMB (@lem7678799) (@lem7678798 A B)). Qed.
Lemma lem7678801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678802 {A B : Type'} : (term492 A B) = (term493 A B).
Proof. exact (MK_COMB (@lem7678801) (@lem7678800 A B)). Qed.
Lemma lem7678803 {A B : Type'} (r : nat) : (term483 A B r) = (term484 A B r).
Proof. exact (eq_refl (term483 A B r)). Qed.
Lemma lem7678804 {A B : Type'} : (term494 A B) = (term478 A B).
Proof. exact (fun_ext (fun r : nat => @lem7678803 A B r)). Qed.
Lemma lem7678805 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678806 {A B : Type'} : (term495 A B) = (term496 A B).
Proof. exact (MK_COMB (@lem7678805) (@lem7678804 A B)). Qed.
Lemma lem7678807 {A B : Type'} : (term476 A B) = (term497 A B).
Proof. exact (MK_COMB (@lem7678802 A B) (@lem7678806 A B)). Qed.
Lemma lem7678808 {A B : Type'} : ((term475 A B) = (term476 A B)) = ((term274 A B) = (term497 A B)).
Proof. exact (MK_COMB (@lem7678796 A B) (@lem7678807 A B)). Qed.
Lemma lem7678809 {A B : Type'} : (term274 A B) = (term497 A B).
Proof. exact (EQ_MP (@lem7678808 A B) (@lem7678786 A B)). Qed.
Lemma lem7678906 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (eq_refl (term52 A B)). Qed.
Lemma lem7678907 {A B : Type'} : (term275 A B) = (term498 A B).
Proof. exact (MK_COMB (@lem7678906 A B) (@lem7678809 A B)). Qed.
Lemma lem7678908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678909 {A B : Type'} : (term277 A B) = (term499 A B).
Proof. exact (MK_COMB (@lem7678908) (@lem7678907 A B)). Qed.
Lemma lem7678915 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7678916 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7678915 nat P Q). Qed.
Lemma lem7678917 {B : Type'} : (term420 B) = (term421 B).
Proof. exact (@lem7678916 (term422 B) (term423 B)). Qed.
Lemma lem7678918 {B : Type'} (r : nat) : (term424 B r) = (term425 B r).
Proof. exact (eq_refl (term424 B r)). Qed.
Lemma lem7678919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678920 {B : Type'} (r : nat) : (term426 B r) = (term427 B r).
Proof. exact (MK_COMB (@lem7678919) (@lem7678918 B r)). Qed.
Lemma lem7678921 {B : Type'} (r : nat) : (term428 B r) = (term429 B r).
Proof. exact (eq_refl (term428 B r)). Qed.
Lemma lem7678922 {B : Type'} (r : nat) : (term430 B r) = (term227 B r).
Proof. exact (MK_COMB (@lem7678920 B r) (@lem7678921 B r)). Qed.
Lemma lem7678923 {B : Type'} : (term431 B) = (term228 B).
Proof. exact (fun_ext (fun r : nat => @lem7678922 B r)). Qed.
Lemma lem7678924 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678925 {B : Type'} : (term420 B) = (term229 B).
Proof. exact (MK_COMB (@lem7678924) (@lem7678923 B)). Qed.
Lemma lem7678926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7678927 {B : Type'} : (term432 B) = (term433 B).
Proof. exact (MK_COMB (@lem7678926) (@lem7678925 B)). Qed.
Lemma lem7678928 {B : Type'} (r : nat) : (term424 B r) = (term425 B r).
Proof. exact (eq_refl (term424 B r)). Qed.
Lemma lem7678929 {B : Type'} : (term434 B) = (term422 B).
Proof. exact (fun_ext (fun r : nat => @lem7678928 B r)). Qed.
Lemma lem7678930 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678931 {B : Type'} : (term435 B) = (term436 B).
Proof. exact (MK_COMB (@lem7678930) (@lem7678929 B)). Qed.
Lemma lem7678932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7678933 {B : Type'} : (term437 B) = (term438 B).
Proof. exact (MK_COMB (@lem7678932) (@lem7678931 B)). Qed.
Lemma lem7678934 {B : Type'} (r : nat) : (term428 B r) = (term429 B r).
Proof. exact (eq_refl (term428 B r)). Qed.
Lemma lem7678935 {B : Type'} : (term439 B) = (term423 B).
Proof. exact (fun_ext (fun r : nat => @lem7678934 B r)). Qed.
Lemma lem7678936 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7678937 {B : Type'} : (term440 B) = (term441 B).
Proof. exact (MK_COMB (@lem7678936) (@lem7678935 B)). Qed.
Lemma lem7678938 {B : Type'} : (term421 B) = (term442 B).
Proof. exact (MK_COMB (@lem7678933 B) (@lem7678937 B)). Qed.
Lemma lem7678939 {B : Type'} : ((term420 B) = (term421 B)) = ((term229 B) = (term442 B)).
Proof. exact (MK_COMB (@lem7678927 B) (@lem7678938 B)). Qed.
Lemma lem7678940 {B : Type'} : (term229 B) = (term442 B).
Proof. exact (EQ_MP (@lem7678939 B) (@lem7678917 B)). Qed.
Lemma lem7679037 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7679038 {B : Type'} : (term230 B) = (term443 B).
Proof. exact (MK_COMB (@lem7679037 B) (@lem7678940 B)). Qed.
Lemma lem7679039 {A B : Type'} : (term279 A B) = (term500 A B).
Proof. exact (MK_COMB (@lem7678909 A B) (@lem7679038 B)). Qed.
Lemma lem7679040 {A B : Type'} : (term320 A B) = (term536 A B).
Proof. exact (MK_COMB (@lem7678778 A) (@lem7679039 A B)). Qed.
Lemma lem7679041 {A B : Type'} : (term285 A B) = (term285 A B).
Proof. exact (eq_refl (term285 A B)). Qed.
Lemma lem7679042 {A B : Type'} : (term323 A B) = (term537 A B).
Proof. exact (MK_COMB (@lem7679041 A B) (@lem7679040 A B)). Qed.
Lemma lem7679043 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7679044 {A B : Type'} : (term326 A B) = (term538 A B).
Proof. exact (MK_COMB (@lem7679043 A B) (@lem7679042 A B)). Qed.
Lemma lem7679045 {A B : Type'} : (term331 A B) = (term539 A B).
Proof. exact (MK_COMB (@lem7678595 A B) (@lem7679044 A B)). Qed.
Lemma lem7679046 {A : Type'} : (term333 A) = (term333 A).
Proof. exact (eq_refl (term333 A)). Qed.
Lemma lem7679047 {A B : Type'} : (term335 A B) = (term540 A B).
Proof. exact (MK_COMB (@lem7679046 A) (@lem7679045 A B)). Qed.
Lemma lem7679048 {A B : Type'} : (term340 A B) = (term541 A B).
Proof. exact (MK_COMB (@lem7678144 A B) (@lem7679047 A B)). Qed.
Lemma lem7679049 {B : Type'} : (term299 B) = (term299 B).
Proof. exact (eq_refl (term299 B)). Qed.
Lemma lem7679050 {A B : Type'} : (term343 A B) = (term542 A B).
Proof. exact (MK_COMB (@lem7679049 B) (@lem7679048 A B)). Qed.
Lemma lem7679051 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7679052 {A B : Type'} : (term413 A B) = (term543 A B).
Proof. exact (MK_COMB (@lem7679051) (@lem7679050 A B)). Qed.
Lemma lem7679110 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7679111 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7679110 nat P Q). Qed.
Lemma lem7679112 {A : Type'} : (term420 A) = (term421 A).
Proof. exact (@lem7679111 (term422 A) (term423 A)). Qed.
Lemma lem7679113 {A : Type'} (r : nat) : (term424 A r) = (term425 A r).
Proof. exact (eq_refl (term424 A r)). Qed.
Lemma lem7679114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679115 {A : Type'} (r : nat) : (term426 A r) = (term427 A r).
Proof. exact (MK_COMB (@lem7679114) (@lem7679113 A r)). Qed.
Lemma lem7679116 {A : Type'} (r : nat) : (term428 A r) = (term429 A r).
Proof. exact (eq_refl (term428 A r)). Qed.
Lemma lem7679117 {A : Type'} (r : nat) : (term430 A r) = (term227 A r).
Proof. exact (MK_COMB (@lem7679115 A r) (@lem7679116 A r)). Qed.
Lemma lem7679118 {A : Type'} : (term431 A) = (term228 A).
Proof. exact (fun_ext (fun r : nat => @lem7679117 A r)). Qed.
Lemma lem7679119 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679120 {A : Type'} : (term420 A) = (term229 A).
Proof. exact (MK_COMB (@lem7679119) (@lem7679118 A)). Qed.
Lemma lem7679121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7679122 {A : Type'} : (term432 A) = (term433 A).
Proof. exact (MK_COMB (@lem7679121) (@lem7679120 A)). Qed.
Lemma lem7679123 {A : Type'} (r : nat) : (term424 A r) = (term425 A r).
Proof. exact (eq_refl (term424 A r)). Qed.
Lemma lem7679124 {A : Type'} : (term434 A) = (term422 A).
Proof. exact (fun_ext (fun r : nat => @lem7679123 A r)). Qed.
Lemma lem7679125 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679126 {A : Type'} : (term435 A) = (term436 A).
Proof. exact (MK_COMB (@lem7679125) (@lem7679124 A)). Qed.
Lemma lem7679127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679128 {A : Type'} : (term437 A) = (term438 A).
Proof. exact (MK_COMB (@lem7679127) (@lem7679126 A)). Qed.
Lemma lem7679129 {A : Type'} (r : nat) : (term428 A r) = (term429 A r).
Proof. exact (eq_refl (term428 A r)). Qed.
Lemma lem7679130 {A : Type'} : (term439 A) = (term423 A).
Proof. exact (fun_ext (fun r : nat => @lem7679129 A r)). Qed.
Lemma lem7679131 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679132 {A : Type'} : (term440 A) = (term441 A).
Proof. exact (MK_COMB (@lem7679131) (@lem7679130 A)). Qed.
Lemma lem7679133 {A : Type'} : (term421 A) = (term442 A).
Proof. exact (MK_COMB (@lem7679128 A) (@lem7679132 A)). Qed.
Lemma lem7679134 {A : Type'} : ((term420 A) = (term421 A)) = ((term229 A) = (term442 A)).
Proof. exact (MK_COMB (@lem7679122 A) (@lem7679133 A)). Qed.
Lemma lem7679135 {A : Type'} : (term229 A) = (term442 A).
Proof. exact (EQ_MP (@lem7679134 A) (@lem7679112 A)). Qed.
Lemma lem7679232 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (eq_refl (term98 A)). Qed.
Lemma lem7679233 {A : Type'} : (term230 A) = (term443 A).
Proof. exact (MK_COMB (@lem7679232 A) (@lem7679135 A)). Qed.
Lemma lem7679234 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679235 {A : Type'} : (term242 A) = (term444 A).
Proof. exact (MK_COMB (@lem7679234) (@lem7679233 A)). Qed.
Lemma lem7679241 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7679242 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7679241 nat P Q). Qed.
Lemma lem7679243 {A B : Type'} : (term445 A B) = (term446 A B).
Proof. exact (@lem7679242 (term447 A B) (term448 A B)). Qed.
Lemma lem7679244 {A B : Type'} (r : nat) : (term449 A B r) = (term450 A B r).
Proof. exact (eq_refl (term449 A B r)). Qed.
Lemma lem7679245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679246 {A B : Type'} (r : nat) : (term451 A B r) = (term452 A B r).
Proof. exact (MK_COMB (@lem7679245) (@lem7679244 A B r)). Qed.
Lemma lem7679247 {A B : Type'} (r : nat) : (term453 A B r) = (term454 A B r).
Proof. exact (eq_refl (term453 A B r)). Qed.
Lemma lem7679248 {A B : Type'} (r : nat) : (term455 A B r) = (term231 A B r).
Proof. exact (MK_COMB (@lem7679246 A B r) (@lem7679247 A B r)). Qed.
Lemma lem7679249 {A B : Type'} : (term456 A B) = (term232 A B).
Proof. exact (fun_ext (fun r : nat => @lem7679248 A B r)). Qed.
Lemma lem7679250 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679251 {A B : Type'} : (term445 A B) = (term233 A B).
Proof. exact (MK_COMB (@lem7679250) (@lem7679249 A B)). Qed.
Lemma lem7679252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7679253 {A B : Type'} : (term457 A B) = (term458 A B).
Proof. exact (MK_COMB (@lem7679252) (@lem7679251 A B)). Qed.
Lemma lem7679254 {A B : Type'} (r : nat) : (term449 A B r) = (term450 A B r).
Proof. exact (eq_refl (term449 A B r)). Qed.
Lemma lem7679255 {A B : Type'} : (term459 A B) = (term447 A B).
Proof. exact (fun_ext (fun r : nat => @lem7679254 A B r)). Qed.
Lemma lem7679256 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679257 {A B : Type'} : (term460 A B) = (term461 A B).
Proof. exact (MK_COMB (@lem7679256) (@lem7679255 A B)). Qed.
Lemma lem7679258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679259 {A B : Type'} : (term462 A B) = (term463 A B).
Proof. exact (MK_COMB (@lem7679258) (@lem7679257 A B)). Qed.
Lemma lem7679260 {A B : Type'} (r : nat) : (term453 A B r) = (term454 A B r).
Proof. exact (eq_refl (term453 A B r)). Qed.
Lemma lem7679261 {A B : Type'} : (term464 A B) = (term448 A B).
Proof. exact (fun_ext (fun r : nat => @lem7679260 A B r)). Qed.
Lemma lem7679262 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679263 {A B : Type'} : (term465 A B) = (term466 A B).
Proof. exact (MK_COMB (@lem7679262) (@lem7679261 A B)). Qed.
Lemma lem7679264 {A B : Type'} : (term446 A B) = (term467 A B).
Proof. exact (MK_COMB (@lem7679259 A B) (@lem7679263 A B)). Qed.
Lemma lem7679265 {A B : Type'} : ((term445 A B) = (term446 A B)) = ((term233 A B) = (term467 A B)).
Proof. exact (MK_COMB (@lem7679253 A B) (@lem7679264 A B)). Qed.
Lemma lem7679266 {A B : Type'} : (term233 A B) = (term467 A B).
Proof. exact (EQ_MP (@lem7679265 A B) (@lem7679243 A B)). Qed.
Lemma lem7679363 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (eq_refl (term52 A B)). Qed.
Lemma lem7679364 {A B : Type'} : (term234 A B) = (term468 A B).
Proof. exact (MK_COMB (@lem7679363 A B) (@lem7679266 A B)). Qed.
Lemma lem7679365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679366 {A B : Type'} : (term237 A B) = (term469 A B).
Proof. exact (MK_COMB (@lem7679365) (@lem7679364 A B)). Qed.
Lemma lem7679372 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7679373 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7679372 nat P Q). Qed.
Lemma lem7679374 {B : Type'} : (term507 B) = (term508 B).
Proof. exact (@lem7679373 (term509 B) (term510 B)). Qed.
Lemma lem7679375 {B : Type'} (r : nat) : (term511 B r) = (term512 B r).
Proof. exact (eq_refl (term511 B r)). Qed.
Lemma lem7679376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679377 {B : Type'} (r : nat) : (term513 B r) = (term514 B r).
Proof. exact (MK_COMB (@lem7679376) (@lem7679375 B r)). Qed.
Lemma lem7679378 {B : Type'} (r : nat) : (term515 B r) = (term516 B r).
Proof. exact (eq_refl (term515 B r)). Qed.
Lemma lem7679379 {B : Type'} (r : nat) : (term517 B r) = (term304 B r).
Proof. exact (MK_COMB (@lem7679377 B r) (@lem7679378 B r)). Qed.
Lemma lem7679380 {B : Type'} : (term518 B) = (term305 B).
Proof. exact (fun_ext (fun r : nat => @lem7679379 B r)). Qed.
Lemma lem7679381 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679382 {B : Type'} : (term507 B) = (term306 B).
Proof. exact (MK_COMB (@lem7679381) (@lem7679380 B)). Qed.
Lemma lem7679383 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7679384 {B : Type'} : (term519 B) = (term520 B).
Proof. exact (MK_COMB (@lem7679383) (@lem7679382 B)). Qed.
Lemma lem7679385 {B : Type'} (r : nat) : (term511 B r) = (term512 B r).
Proof. exact (eq_refl (term511 B r)). Qed.
Lemma lem7679386 {B : Type'} : (term521 B) = (term509 B).
Proof. exact (fun_ext (fun r : nat => @lem7679385 B r)). Qed.
Lemma lem7679387 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679388 {B : Type'} : (term522 B) = (term523 B).
Proof. exact (MK_COMB (@lem7679387) (@lem7679386 B)). Qed.
Lemma lem7679389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679390 {B : Type'} : (term524 B) = (term525 B).
Proof. exact (MK_COMB (@lem7679389) (@lem7679388 B)). Qed.
Lemma lem7679391 {B : Type'} (r : nat) : (term515 B r) = (term516 B r).
Proof. exact (eq_refl (term515 B r)). Qed.
Lemma lem7679392 {B : Type'} : (term526 B) = (term510 B).
Proof. exact (fun_ext (fun r : nat => @lem7679391 B r)). Qed.
Lemma lem7679393 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679394 {B : Type'} : (term527 B) = (term528 B).
Proof. exact (MK_COMB (@lem7679393) (@lem7679392 B)). Qed.
Lemma lem7679395 {B : Type'} : (term508 B) = (term529 B).
Proof. exact (MK_COMB (@lem7679390 B) (@lem7679394 B)). Qed.
Lemma lem7679396 {B : Type'} : ((term507 B) = (term508 B)) = ((term306 B) = (term529 B)).
Proof. exact (MK_COMB (@lem7679384 B) (@lem7679395 B)). Qed.
Lemma lem7679397 {B : Type'} : (term306 B) = (term529 B).
Proof. exact (EQ_MP (@lem7679396 B) (@lem7679374 B)). Qed.
Lemma lem7679494 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7679495 {B : Type'} : (term307 B) = (term530 B).
Proof. exact (MK_COMB (@lem7679494 B) (@lem7679397 B)). Qed.
Lemma lem7679496 {A B : Type'} : (term347 A B) = (term544 A B).
Proof. exact (MK_COMB (@lem7679366 A B) (@lem7679495 B)). Qed.
Lemma lem7679497 {A B : Type'} : (term350 A B) = (term545 A B).
Proof. exact (MK_COMB (@lem7679235 A) (@lem7679496 A B)). Qed.
Lemma lem7679498 {A B : Type'} : (term247 A B) = (term247 A B).
Proof. exact (eq_refl (term247 A B)). Qed.
Lemma lem7679499 {A B : Type'} : (term353 A B) = (term546 A B).
Proof. exact (MK_COMB (@lem7679498 A B) (@lem7679497 A B)). Qed.
Lemma lem7679500 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7679501 {A B : Type'} : (term356 A B) = (term547 A B).
Proof. exact (MK_COMB (@lem7679500 A B) (@lem7679499 A B)). Qed.
Lemma lem7679502 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7679503 {A B : Type'} : (term371 A B) = (term548 A B).
Proof. exact (MK_COMB (@lem7679502) (@lem7679501 A B)). Qed.
Lemma lem7679561 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7679562 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7679561 nat P Q). Qed.
Lemma lem7679563 {A : Type'} : (term420 A) = (term421 A).
Proof. exact (@lem7679562 (term422 A) (term423 A)). Qed.
Lemma lem7679564 {A : Type'} (r : nat) : (term424 A r) = (term425 A r).
Proof. exact (eq_refl (term424 A r)). Qed.
Lemma lem7679565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679566 {A : Type'} (r : nat) : (term426 A r) = (term427 A r).
Proof. exact (MK_COMB (@lem7679565) (@lem7679564 A r)). Qed.
Lemma lem7679567 {A : Type'} (r : nat) : (term428 A r) = (term429 A r).
Proof. exact (eq_refl (term428 A r)). Qed.
Lemma lem7679568 {A : Type'} (r : nat) : (term430 A r) = (term227 A r).
Proof. exact (MK_COMB (@lem7679566 A r) (@lem7679567 A r)). Qed.
Lemma lem7679569 {A : Type'} : (term431 A) = (term228 A).
Proof. exact (fun_ext (fun r : nat => @lem7679568 A r)). Qed.
Lemma lem7679570 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679571 {A : Type'} : (term420 A) = (term229 A).
Proof. exact (MK_COMB (@lem7679570) (@lem7679569 A)). Qed.
Lemma lem7679572 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7679573 {A : Type'} : (term432 A) = (term433 A).
Proof. exact (MK_COMB (@lem7679572) (@lem7679571 A)). Qed.
Lemma lem7679574 {A : Type'} (r : nat) : (term424 A r) = (term425 A r).
Proof. exact (eq_refl (term424 A r)). Qed.
Lemma lem7679575 {A : Type'} : (term434 A) = (term422 A).
Proof. exact (fun_ext (fun r : nat => @lem7679574 A r)). Qed.
Lemma lem7679576 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679577 {A : Type'} : (term435 A) = (term436 A).
Proof. exact (MK_COMB (@lem7679576) (@lem7679575 A)). Qed.
Lemma lem7679578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679579 {A : Type'} : (term437 A) = (term438 A).
Proof. exact (MK_COMB (@lem7679578) (@lem7679577 A)). Qed.
Lemma lem7679580 {A : Type'} (r : nat) : (term428 A r) = (term429 A r).
Proof. exact (eq_refl (term428 A r)). Qed.
Lemma lem7679581 {A : Type'} : (term439 A) = (term423 A).
Proof. exact (fun_ext (fun r : nat => @lem7679580 A r)). Qed.
Lemma lem7679582 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679583 {A : Type'} : (term440 A) = (term441 A).
Proof. exact (MK_COMB (@lem7679582) (@lem7679581 A)). Qed.
Lemma lem7679584 {A : Type'} : (term421 A) = (term442 A).
Proof. exact (MK_COMB (@lem7679579 A) (@lem7679583 A)). Qed.
Lemma lem7679585 {A : Type'} : ((term420 A) = (term421 A)) = ((term229 A) = (term442 A)).
Proof. exact (MK_COMB (@lem7679573 A) (@lem7679584 A)). Qed.
Lemma lem7679586 {A : Type'} : (term229 A) = (term442 A).
Proof. exact (EQ_MP (@lem7679585 A) (@lem7679563 A)). Qed.
Lemma lem7679683 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (eq_refl (term98 A)). Qed.
Lemma lem7679684 {A : Type'} : (term230 A) = (term443 A).
Proof. exact (MK_COMB (@lem7679683 A) (@lem7679586 A)). Qed.
Lemma lem7679685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679686 {A : Type'} : (term242 A) = (term444 A).
Proof. exact (MK_COMB (@lem7679685) (@lem7679684 A)). Qed.
Lemma lem7679692 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7679693 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7679692 nat P Q). Qed.
Lemma lem7679694 {A B : Type'} : (term475 A B) = (term476 A B).
Proof. exact (@lem7679693 (term477 A B) (term478 A B)). Qed.
Lemma lem7679695 {A B : Type'} (r : nat) : (term479 A B r) = (term480 A B r).
Proof. exact (eq_refl (term479 A B r)). Qed.
Lemma lem7679696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679697 {A B : Type'} (r : nat) : (term481 A B r) = (term482 A B r).
Proof. exact (MK_COMB (@lem7679696) (@lem7679695 A B r)). Qed.
Lemma lem7679698 {A B : Type'} (r : nat) : (term483 A B r) = (term484 A B r).
Proof. exact (eq_refl (term483 A B r)). Qed.
Lemma lem7679699 {A B : Type'} (r : nat) : (term485 A B r) = (term272 A B r).
Proof. exact (MK_COMB (@lem7679697 A B r) (@lem7679698 A B r)). Qed.
Lemma lem7679700 {A B : Type'} : (term486 A B) = (term273 A B).
Proof. exact (fun_ext (fun r : nat => @lem7679699 A B r)). Qed.
Lemma lem7679701 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679702 {A B : Type'} : (term475 A B) = (term274 A B).
Proof. exact (MK_COMB (@lem7679701) (@lem7679700 A B)). Qed.
Lemma lem7679703 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7679704 {A B : Type'} : (term487 A B) = (term488 A B).
Proof. exact (MK_COMB (@lem7679703) (@lem7679702 A B)). Qed.
Lemma lem7679705 {A B : Type'} (r : nat) : (term479 A B r) = (term480 A B r).
Proof. exact (eq_refl (term479 A B r)). Qed.
Lemma lem7679706 {A B : Type'} : (term489 A B) = (term477 A B).
Proof. exact (fun_ext (fun r : nat => @lem7679705 A B r)). Qed.
Lemma lem7679707 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679708 {A B : Type'} : (term490 A B) = (term491 A B).
Proof. exact (MK_COMB (@lem7679707) (@lem7679706 A B)). Qed.
Lemma lem7679709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679710 {A B : Type'} : (term492 A B) = (term493 A B).
Proof. exact (MK_COMB (@lem7679709) (@lem7679708 A B)). Qed.
Lemma lem7679711 {A B : Type'} (r : nat) : (term483 A B r) = (term484 A B r).
Proof. exact (eq_refl (term483 A B r)). Qed.
Lemma lem7679712 {A B : Type'} : (term494 A B) = (term478 A B).
Proof. exact (fun_ext (fun r : nat => @lem7679711 A B r)). Qed.
Lemma lem7679713 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679714 {A B : Type'} : (term495 A B) = (term496 A B).
Proof. exact (MK_COMB (@lem7679713) (@lem7679712 A B)). Qed.
Lemma lem7679715 {A B : Type'} : (term476 A B) = (term497 A B).
Proof. exact (MK_COMB (@lem7679710 A B) (@lem7679714 A B)). Qed.
Lemma lem7679716 {A B : Type'} : ((term475 A B) = (term476 A B)) = ((term274 A B) = (term497 A B)).
Proof. exact (MK_COMB (@lem7679704 A B) (@lem7679715 A B)). Qed.
Lemma lem7679717 {A B : Type'} : (term274 A B) = (term497 A B).
Proof. exact (EQ_MP (@lem7679716 A B) (@lem7679694 A B)). Qed.
Lemma lem7679814 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (eq_refl (term52 A B)). Qed.
Lemma lem7679815 {A B : Type'} : (term275 A B) = (term498 A B).
Proof. exact (MK_COMB (@lem7679814 A B) (@lem7679717 A B)). Qed.
Lemma lem7679816 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679817 {A B : Type'} : (term277 A B) = (term499 A B).
Proof. exact (MK_COMB (@lem7679816) (@lem7679815 A B)). Qed.
Lemma lem7679823 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7679824 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7679823 nat P Q). Qed.
Lemma lem7679825 {B : Type'} : (term507 B) = (term508 B).
Proof. exact (@lem7679824 (term509 B) (term510 B)). Qed.
Lemma lem7679826 {B : Type'} (r : nat) : (term511 B r) = (term512 B r).
Proof. exact (eq_refl (term511 B r)). Qed.
Lemma lem7679827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679828 {B : Type'} (r : nat) : (term513 B r) = (term514 B r).
Proof. exact (MK_COMB (@lem7679827) (@lem7679826 B r)). Qed.
Lemma lem7679829 {B : Type'} (r : nat) : (term515 B r) = (term516 B r).
Proof. exact (eq_refl (term515 B r)). Qed.
Lemma lem7679830 {B : Type'} (r : nat) : (term517 B r) = (term304 B r).
Proof. exact (MK_COMB (@lem7679828 B r) (@lem7679829 B r)). Qed.
Lemma lem7679831 {B : Type'} : (term518 B) = (term305 B).
Proof. exact (fun_ext (fun r : nat => @lem7679830 B r)). Qed.
Lemma lem7679832 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679833 {B : Type'} : (term507 B) = (term306 B).
Proof. exact (MK_COMB (@lem7679832) (@lem7679831 B)). Qed.
Lemma lem7679834 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7679835 {B : Type'} : (term519 B) = (term520 B).
Proof. exact (MK_COMB (@lem7679834) (@lem7679833 B)). Qed.
Lemma lem7679836 {B : Type'} (r : nat) : (term511 B r) = (term512 B r).
Proof. exact (eq_refl (term511 B r)). Qed.
Lemma lem7679837 {B : Type'} : (term521 B) = (term509 B).
Proof. exact (fun_ext (fun r : nat => @lem7679836 B r)). Qed.
Lemma lem7679838 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679839 {B : Type'} : (term522 B) = (term523 B).
Proof. exact (MK_COMB (@lem7679838) (@lem7679837 B)). Qed.
Lemma lem7679840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7679841 {B : Type'} : (term524 B) = (term525 B).
Proof. exact (MK_COMB (@lem7679840) (@lem7679839 B)). Qed.
Lemma lem7679842 {B : Type'} (r : nat) : (term515 B r) = (term516 B r).
Proof. exact (eq_refl (term515 B r)). Qed.
Lemma lem7679843 {B : Type'} : (term526 B) = (term510 B).
Proof. exact (fun_ext (fun r : nat => @lem7679842 B r)). Qed.
Lemma lem7679844 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7679845 {B : Type'} : (term527 B) = (term528 B).
Proof. exact (MK_COMB (@lem7679844) (@lem7679843 B)). Qed.
Lemma lem7679846 {B : Type'} : (term508 B) = (term529 B).
Proof. exact (MK_COMB (@lem7679841 B) (@lem7679845 B)). Qed.
Lemma lem7679847 {B : Type'} : ((term507 B) = (term508 B)) = ((term306 B) = (term529 B)).
Proof. exact (MK_COMB (@lem7679835 B) (@lem7679846 B)). Qed.
Lemma lem7679848 {B : Type'} : (term306 B) = (term529 B).
Proof. exact (EQ_MP (@lem7679847 B) (@lem7679825 B)). Qed.
Lemma lem7679945 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7679946 {B : Type'} : (term307 B) = (term530 B).
Proof. exact (MK_COMB (@lem7679945 B) (@lem7679848 B)). Qed.
Lemma lem7679947 {A B : Type'} : (term359 A B) = (term549 A B).
Proof. exact (MK_COMB (@lem7679817 A B) (@lem7679946 B)). Qed.
Lemma lem7679948 {A B : Type'} : (term362 A B) = (term550 A B).
Proof. exact (MK_COMB (@lem7679686 A) (@lem7679947 A B)). Qed.
Lemma lem7679949 {A B : Type'} : (term285 A B) = (term285 A B).
Proof. exact (eq_refl (term285 A B)). Qed.
Lemma lem7679950 {A B : Type'} : (term365 A B) = (term551 A B).
Proof. exact (MK_COMB (@lem7679949 A B) (@lem7679948 A B)). Qed.
Lemma lem7679951 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7679952 {A B : Type'} : (term368 A B) = (term552 A B).
Proof. exact (MK_COMB (@lem7679951 A B) (@lem7679950 A B)). Qed.
Lemma lem7679953 {A B : Type'} : (term373 A B) = (term553 A B).
Proof. exact (MK_COMB (@lem7679503 A B) (@lem7679952 A B)). Qed.
Lemma lem7679954 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (eq_refl (term299 A)). Qed.
Lemma lem7679955 {A B : Type'} : (term376 A B) = (term554 A B).
Proof. exact (MK_COMB (@lem7679954 A) (@lem7679953 A B)). Qed.
Lemma lem7679956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7679957 {A B : Type'} : (term405 A B) = (term555 A B).
Proof. exact (MK_COMB (@lem7679956) (@lem7679955 A B)). Qed.
Lemma lem7680015 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7680016 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7680015 nat P Q). Qed.
Lemma lem7680017 {A : Type'} : (term507 A) = (term508 A).
Proof. exact (@lem7680016 (term509 A) (term510 A)). Qed.
Lemma lem7680018 {A : Type'} (r : nat) : (term511 A r) = (term512 A r).
Proof. exact (eq_refl (term511 A r)). Qed.
Lemma lem7680019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680020 {A : Type'} (r : nat) : (term513 A r) = (term514 A r).
Proof. exact (MK_COMB (@lem7680019) (@lem7680018 A r)). Qed.
Lemma lem7680021 {A : Type'} (r : nat) : (term515 A r) = (term516 A r).
Proof. exact (eq_refl (term515 A r)). Qed.
Lemma lem7680022 {A : Type'} (r : nat) : (term517 A r) = (term304 A r).
Proof. exact (MK_COMB (@lem7680020 A r) (@lem7680021 A r)). Qed.
Lemma lem7680023 {A : Type'} : (term518 A) = (term305 A).
Proof. exact (fun_ext (fun r : nat => @lem7680022 A r)). Qed.
Lemma lem7680024 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680025 {A : Type'} : (term507 A) = (term306 A).
Proof. exact (MK_COMB (@lem7680024) (@lem7680023 A)). Qed.
Lemma lem7680026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7680027 {A : Type'} : (term519 A) = (term520 A).
Proof. exact (MK_COMB (@lem7680026) (@lem7680025 A)). Qed.
Lemma lem7680028 {A : Type'} (r : nat) : (term511 A r) = (term512 A r).
Proof. exact (eq_refl (term511 A r)). Qed.
Lemma lem7680029 {A : Type'} : (term521 A) = (term509 A).
Proof. exact (fun_ext (fun r : nat => @lem7680028 A r)). Qed.
Lemma lem7680030 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680031 {A : Type'} : (term522 A) = (term523 A).
Proof. exact (MK_COMB (@lem7680030) (@lem7680029 A)). Qed.
Lemma lem7680032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680033 {A : Type'} : (term524 A) = (term525 A).
Proof. exact (MK_COMB (@lem7680032) (@lem7680031 A)). Qed.
Lemma lem7680034 {A : Type'} (r : nat) : (term515 A r) = (term516 A r).
Proof. exact (eq_refl (term515 A r)). Qed.
Lemma lem7680035 {A : Type'} : (term526 A) = (term510 A).
Proof. exact (fun_ext (fun r : nat => @lem7680034 A r)). Qed.
Lemma lem7680036 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680037 {A : Type'} : (term527 A) = (term528 A).
Proof. exact (MK_COMB (@lem7680036) (@lem7680035 A)). Qed.
Lemma lem7680038 {A : Type'} : (term508 A) = (term529 A).
Proof. exact (MK_COMB (@lem7680033 A) (@lem7680037 A)). Qed.
Lemma lem7680039 {A : Type'} : ((term507 A) = (term508 A)) = ((term306 A) = (term529 A)).
Proof. exact (MK_COMB (@lem7680027 A) (@lem7680038 A)). Qed.
Lemma lem7680040 {A : Type'} : (term306 A) = (term529 A).
Proof. exact (EQ_MP (@lem7680039 A) (@lem7680017 A)). Qed.
Lemma lem7680137 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (eq_refl (term98 A)). Qed.
Lemma lem7680138 {A : Type'} : (term307 A) = (term530 A).
Proof. exact (MK_COMB (@lem7680137 A) (@lem7680040 A)). Qed.
Lemma lem7680139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680140 {A : Type'} : (term309 A) = (term531 A).
Proof. exact (MK_COMB (@lem7680139) (@lem7680138 A)). Qed.
Lemma lem7680146 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7680147 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7680146 nat P Q). Qed.
Lemma lem7680148 {A B : Type'} : (term445 A B) = (term446 A B).
Proof. exact (@lem7680147 (term447 A B) (term448 A B)). Qed.
Lemma lem7680149 {A B : Type'} (r : nat) : (term449 A B r) = (term450 A B r).
Proof. exact (eq_refl (term449 A B r)). Qed.
Lemma lem7680150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680151 {A B : Type'} (r : nat) : (term451 A B r) = (term452 A B r).
Proof. exact (MK_COMB (@lem7680150) (@lem7680149 A B r)). Qed.
Lemma lem7680152 {A B : Type'} (r : nat) : (term453 A B r) = (term454 A B r).
Proof. exact (eq_refl (term453 A B r)). Qed.
Lemma lem7680153 {A B : Type'} (r : nat) : (term455 A B r) = (term231 A B r).
Proof. exact (MK_COMB (@lem7680151 A B r) (@lem7680152 A B r)). Qed.
Lemma lem7680154 {A B : Type'} : (term456 A B) = (term232 A B).
Proof. exact (fun_ext (fun r : nat => @lem7680153 A B r)). Qed.
Lemma lem7680155 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680156 {A B : Type'} : (term445 A B) = (term233 A B).
Proof. exact (MK_COMB (@lem7680155) (@lem7680154 A B)). Qed.
Lemma lem7680157 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7680158 {A B : Type'} : (term457 A B) = (term458 A B).
Proof. exact (MK_COMB (@lem7680157) (@lem7680156 A B)). Qed.
Lemma lem7680159 {A B : Type'} (r : nat) : (term449 A B r) = (term450 A B r).
Proof. exact (eq_refl (term449 A B r)). Qed.
Lemma lem7680160 {A B : Type'} : (term459 A B) = (term447 A B).
Proof. exact (fun_ext (fun r : nat => @lem7680159 A B r)). Qed.
Lemma lem7680161 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680162 {A B : Type'} : (term460 A B) = (term461 A B).
Proof. exact (MK_COMB (@lem7680161) (@lem7680160 A B)). Qed.
Lemma lem7680163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680164 {A B : Type'} : (term462 A B) = (term463 A B).
Proof. exact (MK_COMB (@lem7680163) (@lem7680162 A B)). Qed.
Lemma lem7680165 {A B : Type'} (r : nat) : (term453 A B r) = (term454 A B r).
Proof. exact (eq_refl (term453 A B r)). Qed.
Lemma lem7680166 {A B : Type'} : (term464 A B) = (term448 A B).
Proof. exact (fun_ext (fun r : nat => @lem7680165 A B r)). Qed.
Lemma lem7680167 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680168 {A B : Type'} : (term465 A B) = (term466 A B).
Proof. exact (MK_COMB (@lem7680167) (@lem7680166 A B)). Qed.
Lemma lem7680169 {A B : Type'} : (term446 A B) = (term467 A B).
Proof. exact (MK_COMB (@lem7680164 A B) (@lem7680168 A B)). Qed.
Lemma lem7680170 {A B : Type'} : ((term445 A B) = (term446 A B)) = ((term233 A B) = (term467 A B)).
Proof. exact (MK_COMB (@lem7680158 A B) (@lem7680169 A B)). Qed.
Lemma lem7680171 {A B : Type'} : (term233 A B) = (term467 A B).
Proof. exact (EQ_MP (@lem7680170 A B) (@lem7680148 A B)). Qed.
Lemma lem7680268 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (eq_refl (term52 A B)). Qed.
Lemma lem7680269 {A B : Type'} : (term234 A B) = (term468 A B).
Proof. exact (MK_COMB (@lem7680268 A B) (@lem7680171 A B)). Qed.
Lemma lem7680270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680271 {A B : Type'} : (term237 A B) = (term469 A B).
Proof. exact (MK_COMB (@lem7680270) (@lem7680269 A B)). Qed.
Lemma lem7680277 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7680278 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7680277 nat P Q). Qed.
Lemma lem7680279 {B : Type'} : (term507 B) = (term508 B).
Proof. exact (@lem7680278 (term509 B) (term510 B)). Qed.
Lemma lem7680280 {B : Type'} (r : nat) : (term511 B r) = (term512 B r).
Proof. exact (eq_refl (term511 B r)). Qed.
Lemma lem7680281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680282 {B : Type'} (r : nat) : (term513 B r) = (term514 B r).
Proof. exact (MK_COMB (@lem7680281) (@lem7680280 B r)). Qed.
Lemma lem7680283 {B : Type'} (r : nat) : (term515 B r) = (term516 B r).
Proof. exact (eq_refl (term515 B r)). Qed.
Lemma lem7680284 {B : Type'} (r : nat) : (term517 B r) = (term304 B r).
Proof. exact (MK_COMB (@lem7680282 B r) (@lem7680283 B r)). Qed.
Lemma lem7680285 {B : Type'} : (term518 B) = (term305 B).
Proof. exact (fun_ext (fun r : nat => @lem7680284 B r)). Qed.
Lemma lem7680286 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680287 {B : Type'} : (term507 B) = (term306 B).
Proof. exact (MK_COMB (@lem7680286) (@lem7680285 B)). Qed.
Lemma lem7680288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7680289 {B : Type'} : (term519 B) = (term520 B).
Proof. exact (MK_COMB (@lem7680288) (@lem7680287 B)). Qed.
Lemma lem7680290 {B : Type'} (r : nat) : (term511 B r) = (term512 B r).
Proof. exact (eq_refl (term511 B r)). Qed.
Lemma lem7680291 {B : Type'} : (term521 B) = (term509 B).
Proof. exact (fun_ext (fun r : nat => @lem7680290 B r)). Qed.
Lemma lem7680292 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680293 {B : Type'} : (term522 B) = (term523 B).
Proof. exact (MK_COMB (@lem7680292) (@lem7680291 B)). Qed.
Lemma lem7680294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680295 {B : Type'} : (term524 B) = (term525 B).
Proof. exact (MK_COMB (@lem7680294) (@lem7680293 B)). Qed.
Lemma lem7680296 {B : Type'} (r : nat) : (term515 B r) = (term516 B r).
Proof. exact (eq_refl (term515 B r)). Qed.
Lemma lem7680297 {B : Type'} : (term526 B) = (term510 B).
Proof. exact (fun_ext (fun r : nat => @lem7680296 B r)). Qed.
Lemma lem7680298 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680299 {B : Type'} : (term527 B) = (term528 B).
Proof. exact (MK_COMB (@lem7680298) (@lem7680297 B)). Qed.
Lemma lem7680300 {B : Type'} : (term508 B) = (term529 B).
Proof. exact (MK_COMB (@lem7680295 B) (@lem7680299 B)). Qed.
Lemma lem7680301 {B : Type'} : ((term507 B) = (term508 B)) = ((term306 B) = (term529 B)).
Proof. exact (MK_COMB (@lem7680289 B) (@lem7680300 B)). Qed.
Lemma lem7680302 {B : Type'} : (term306 B) = (term529 B).
Proof. exact (EQ_MP (@lem7680301 B) (@lem7680279 B)). Qed.
Lemma lem7680399 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7680400 {B : Type'} : (term307 B) = (term530 B).
Proof. exact (MK_COMB (@lem7680399 B) (@lem7680302 B)). Qed.
Lemma lem7680401 {A B : Type'} : (term347 A B) = (term544 A B).
Proof. exact (MK_COMB (@lem7680271 A B) (@lem7680400 B)). Qed.
Lemma lem7680402 {A B : Type'} : (term379 A B) = (term556 A B).
Proof. exact (MK_COMB (@lem7680140 A) (@lem7680401 A B)). Qed.
Lemma lem7680403 {A B : Type'} : (term247 A B) = (term247 A B).
Proof. exact (eq_refl (term247 A B)). Qed.
Lemma lem7680404 {A B : Type'} : (term382 A B) = (term557 A B).
Proof. exact (MK_COMB (@lem7680403 A B) (@lem7680402 A B)). Qed.
Lemma lem7680405 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7680406 {A B : Type'} : (term385 A B) = (term558 A B).
Proof. exact (MK_COMB (@lem7680405 A B) (@lem7680404 A B)). Qed.
Lemma lem7680407 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7680408 {A B : Type'} : (term397 A B) = (term559 A B).
Proof. exact (MK_COMB (@lem7680407) (@lem7680406 A B)). Qed.
Lemma lem7680466 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7680467 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7680466 nat P Q). Qed.
Lemma lem7680468 {A : Type'} : (term507 A) = (term508 A).
Proof. exact (@lem7680467 (term509 A) (term510 A)). Qed.
Lemma lem7680469 {A : Type'} (r : nat) : (term511 A r) = (term512 A r).
Proof. exact (eq_refl (term511 A r)). Qed.
Lemma lem7680470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680471 {A : Type'} (r : nat) : (term513 A r) = (term514 A r).
Proof. exact (MK_COMB (@lem7680470) (@lem7680469 A r)). Qed.
Lemma lem7680472 {A : Type'} (r : nat) : (term515 A r) = (term516 A r).
Proof. exact (eq_refl (term515 A r)). Qed.
Lemma lem7680473 {A : Type'} (r : nat) : (term517 A r) = (term304 A r).
Proof. exact (MK_COMB (@lem7680471 A r) (@lem7680472 A r)). Qed.
Lemma lem7680474 {A : Type'} : (term518 A) = (term305 A).
Proof. exact (fun_ext (fun r : nat => @lem7680473 A r)). Qed.
Lemma lem7680475 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680476 {A : Type'} : (term507 A) = (term306 A).
Proof. exact (MK_COMB (@lem7680475) (@lem7680474 A)). Qed.
Lemma lem7680477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7680478 {A : Type'} : (term519 A) = (term520 A).
Proof. exact (MK_COMB (@lem7680477) (@lem7680476 A)). Qed.
Lemma lem7680479 {A : Type'} (r : nat) : (term511 A r) = (term512 A r).
Proof. exact (eq_refl (term511 A r)). Qed.
Lemma lem7680480 {A : Type'} : (term521 A) = (term509 A).
Proof. exact (fun_ext (fun r : nat => @lem7680479 A r)). Qed.
Lemma lem7680481 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680482 {A : Type'} : (term522 A) = (term523 A).
Proof. exact (MK_COMB (@lem7680481) (@lem7680480 A)). Qed.
Lemma lem7680483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680484 {A : Type'} : (term524 A) = (term525 A).
Proof. exact (MK_COMB (@lem7680483) (@lem7680482 A)). Qed.
Lemma lem7680485 {A : Type'} (r : nat) : (term515 A r) = (term516 A r).
Proof. exact (eq_refl (term515 A r)). Qed.
Lemma lem7680486 {A : Type'} : (term526 A) = (term510 A).
Proof. exact (fun_ext (fun r : nat => @lem7680485 A r)). Qed.
Lemma lem7680487 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680488 {A : Type'} : (term527 A) = (term528 A).
Proof. exact (MK_COMB (@lem7680487) (@lem7680486 A)). Qed.
Lemma lem7680489 {A : Type'} : (term508 A) = (term529 A).
Proof. exact (MK_COMB (@lem7680484 A) (@lem7680488 A)). Qed.
Lemma lem7680490 {A : Type'} : ((term507 A) = (term508 A)) = ((term306 A) = (term529 A)).
Proof. exact (MK_COMB (@lem7680478 A) (@lem7680489 A)). Qed.
Lemma lem7680491 {A : Type'} : (term306 A) = (term529 A).
Proof. exact (EQ_MP (@lem7680490 A) (@lem7680468 A)). Qed.
Lemma lem7680588 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (eq_refl (term98 A)). Qed.
Lemma lem7680589 {A : Type'} : (term307 A) = (term530 A).
Proof. exact (MK_COMB (@lem7680588 A) (@lem7680491 A)). Qed.
Lemma lem7680590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680591 {A : Type'} : (term309 A) = (term531 A).
Proof. exact (MK_COMB (@lem7680590) (@lem7680589 A)). Qed.
Lemma lem7680597 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7680598 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7680597 nat P Q). Qed.
Lemma lem7680599 {A B : Type'} : (term475 A B) = (term476 A B).
Proof. exact (@lem7680598 (term477 A B) (term478 A B)). Qed.
Lemma lem7680600 {A B : Type'} (r : nat) : (term479 A B r) = (term480 A B r).
Proof. exact (eq_refl (term479 A B r)). Qed.
Lemma lem7680601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680602 {A B : Type'} (r : nat) : (term481 A B r) = (term482 A B r).
Proof. exact (MK_COMB (@lem7680601) (@lem7680600 A B r)). Qed.
Lemma lem7680603 {A B : Type'} (r : nat) : (term483 A B r) = (term484 A B r).
Proof. exact (eq_refl (term483 A B r)). Qed.
Lemma lem7680604 {A B : Type'} (r : nat) : (term485 A B r) = (term272 A B r).
Proof. exact (MK_COMB (@lem7680602 A B r) (@lem7680603 A B r)). Qed.
Lemma lem7680605 {A B : Type'} : (term486 A B) = (term273 A B).
Proof. exact (fun_ext (fun r : nat => @lem7680604 A B r)). Qed.
Lemma lem7680606 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680607 {A B : Type'} : (term475 A B) = (term274 A B).
Proof. exact (MK_COMB (@lem7680606) (@lem7680605 A B)). Qed.
Lemma lem7680608 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7680609 {A B : Type'} : (term487 A B) = (term488 A B).
Proof. exact (MK_COMB (@lem7680608) (@lem7680607 A B)). Qed.
Lemma lem7680610 {A B : Type'} (r : nat) : (term479 A B r) = (term480 A B r).
Proof. exact (eq_refl (term479 A B r)). Qed.
Lemma lem7680611 {A B : Type'} : (term489 A B) = (term477 A B).
Proof. exact (fun_ext (fun r : nat => @lem7680610 A B r)). Qed.
Lemma lem7680612 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680613 {A B : Type'} : (term490 A B) = (term491 A B).
Proof. exact (MK_COMB (@lem7680612) (@lem7680611 A B)). Qed.
Lemma lem7680614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680615 {A B : Type'} : (term492 A B) = (term493 A B).
Proof. exact (MK_COMB (@lem7680614) (@lem7680613 A B)). Qed.
Lemma lem7680616 {A B : Type'} (r : nat) : (term483 A B r) = (term484 A B r).
Proof. exact (eq_refl (term483 A B r)). Qed.
Lemma lem7680617 {A B : Type'} : (term494 A B) = (term478 A B).
Proof. exact (fun_ext (fun r : nat => @lem7680616 A B r)). Qed.
Lemma lem7680618 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680619 {A B : Type'} : (term495 A B) = (term496 A B).
Proof. exact (MK_COMB (@lem7680618) (@lem7680617 A B)). Qed.
Lemma lem7680620 {A B : Type'} : (term476 A B) = (term497 A B).
Proof. exact (MK_COMB (@lem7680615 A B) (@lem7680619 A B)). Qed.
Lemma lem7680621 {A B : Type'} : ((term475 A B) = (term476 A B)) = ((term274 A B) = (term497 A B)).
Proof. exact (MK_COMB (@lem7680609 A B) (@lem7680620 A B)). Qed.
Lemma lem7680622 {A B : Type'} : (term274 A B) = (term497 A B).
Proof. exact (EQ_MP (@lem7680621 A B) (@lem7680599 A B)). Qed.
Lemma lem7680719 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (eq_refl (term52 A B)). Qed.
Lemma lem7680720 {A B : Type'} : (term275 A B) = (term498 A B).
Proof. exact (MK_COMB (@lem7680719 A B) (@lem7680622 A B)). Qed.
Lemma lem7680721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680722 {A B : Type'} : (term277 A B) = (term499 A B).
Proof. exact (MK_COMB (@lem7680721) (@lem7680720 A B)). Qed.
Lemma lem7680728 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7680729 (P : nat -> Prop) (Q : nat -> Prop) : (term418 P Q) = (term419 P Q).
Proof. exact (@lem7680728 nat P Q). Qed.
Lemma lem7680730 {B : Type'} : (term507 B) = (term508 B).
Proof. exact (@lem7680729 (term509 B) (term510 B)). Qed.
Lemma lem7680731 {B : Type'} (r : nat) : (term511 B r) = (term512 B r).
Proof. exact (eq_refl (term511 B r)). Qed.
Lemma lem7680732 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680733 {B : Type'} (r : nat) : (term513 B r) = (term514 B r).
Proof. exact (MK_COMB (@lem7680732) (@lem7680731 B r)). Qed.
Lemma lem7680734 {B : Type'} (r : nat) : (term515 B r) = (term516 B r).
Proof. exact (eq_refl (term515 B r)). Qed.
Lemma lem7680735 {B : Type'} (r : nat) : (term517 B r) = (term304 B r).
Proof. exact (MK_COMB (@lem7680733 B r) (@lem7680734 B r)). Qed.
Lemma lem7680736 {B : Type'} : (term518 B) = (term305 B).
Proof. exact (fun_ext (fun r : nat => @lem7680735 B r)). Qed.
Lemma lem7680737 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680738 {B : Type'} : (term507 B) = (term306 B).
Proof. exact (MK_COMB (@lem7680737) (@lem7680736 B)). Qed.
Lemma lem7680739 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7680740 {B : Type'} : (term519 B) = (term520 B).
Proof. exact (MK_COMB (@lem7680739) (@lem7680738 B)). Qed.
Lemma lem7680741 {B : Type'} (r : nat) : (term511 B r) = (term512 B r).
Proof. exact (eq_refl (term511 B r)). Qed.
Lemma lem7680742 {B : Type'} : (term521 B) = (term509 B).
Proof. exact (fun_ext (fun r : nat => @lem7680741 B r)). Qed.
Lemma lem7680743 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680744 {B : Type'} : (term522 B) = (term523 B).
Proof. exact (MK_COMB (@lem7680743) (@lem7680742 B)). Qed.
Lemma lem7680745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680746 {B : Type'} : (term524 B) = (term525 B).
Proof. exact (MK_COMB (@lem7680745) (@lem7680744 B)). Qed.
Lemma lem7680747 {B : Type'} (r : nat) : (term515 B r) = (term516 B r).
Proof. exact (eq_refl (term515 B r)). Qed.
Lemma lem7680748 {B : Type'} : (term526 B) = (term510 B).
Proof. exact (fun_ext (fun r : nat => @lem7680747 B r)). Qed.
Lemma lem7680749 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7680750 {B : Type'} : (term527 B) = (term528 B).
Proof. exact (MK_COMB (@lem7680749) (@lem7680748 B)). Qed.
Lemma lem7680751 {B : Type'} : (term508 B) = (term529 B).
Proof. exact (MK_COMB (@lem7680746 B) (@lem7680750 B)). Qed.
Lemma lem7680752 {B : Type'} : ((term507 B) = (term508 B)) = ((term306 B) = (term529 B)).
Proof. exact (MK_COMB (@lem7680740 B) (@lem7680751 B)). Qed.
Lemma lem7680753 {B : Type'} : (term306 B) = (term529 B).
Proof. exact (EQ_MP (@lem7680752 B) (@lem7680730 B)). Qed.
Lemma lem7680850 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (eq_refl (term98 B)). Qed.
Lemma lem7680851 {B : Type'} : (term307 B) = (term530 B).
Proof. exact (MK_COMB (@lem7680850 B) (@lem7680753 B)). Qed.
Lemma lem7680852 {A B : Type'} : (term359 A B) = (term549 A B).
Proof. exact (MK_COMB (@lem7680722 A B) (@lem7680851 B)). Qed.
Lemma lem7680853 {A B : Type'} : (term388 A B) = (term560 A B).
Proof. exact (MK_COMB (@lem7680591 A) (@lem7680852 A B)). Qed.
Lemma lem7680854 {A B : Type'} : (term285 A B) = (term285 A B).
Proof. exact (eq_refl (term285 A B)). Qed.
Lemma lem7680855 {A B : Type'} : (term391 A B) = (term561 A B).
Proof. exact (MK_COMB (@lem7680854 A B) (@lem7680853 A B)). Qed.
Lemma lem7680856 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7680857 {A B : Type'} : (term394 A B) = (term562 A B).
Proof. exact (MK_COMB (@lem7680856 A B) (@lem7680855 A B)). Qed.
Lemma lem7680858 {A B : Type'} : (term399 A B) = (term563 A B).
Proof. exact (MK_COMB (@lem7680408 A B) (@lem7680857 A B)). Qed.
Lemma lem7680859 {A : Type'} : (term333 A) = (term333 A).
Proof. exact (eq_refl (term333 A)). Qed.
Lemma lem7680860 {A B : Type'} : (term402 A B) = (term564 A B).
Proof. exact (MK_COMB (@lem7680859 A) (@lem7680858 A B)). Qed.
Lemma lem7680861 {A B : Type'} : (term407 A B) = (term565 A B).
Proof. exact (MK_COMB (@lem7679957 A B) (@lem7680860 A B)). Qed.
Lemma lem7680862 {B : Type'} : (term333 B) = (term333 B).
Proof. exact (eq_refl (term333 B)). Qed.
Lemma lem7680863 {A B : Type'} : (term410 A B) = (term566 A B).
Proof. exact (MK_COMB (@lem7680862 B) (@lem7680861 A B)). Qed.
Lemma lem7680864 {A B : Type'} : (term415 A B) = (term567 A B).
Proof. exact (MK_COMB (@lem7679052 A B) (@lem7680863 A B)). Qed.
Lemma lem7680866 {A : Type'} (P : A -> Prop) (Q : Prop) : (term568 A P Q) = (term569 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7680867 {A B : Type'} (P : type31 A B) (Q : Prop) : (term570 A B P Q) = (term571 A B P Q).
Proof. exact (@lem7680866 (finite_diff A B) P Q). Qed.
Lemma lem7680868 {A B : Type'} : (term572 A B) = (term573 A B).
Proof. exact (@lem7680867 A B (term225 A B) (term471 A B)). Qed.
Lemma lem7680869 {A B : Type'} (x : finite_diff A B) : (term574 A B x) = (term218 A B x).
Proof. exact (eq_refl (term574 A B x)). Qed.
Lemma lem7680870 {A B : Type'} : (term575 A B) = (term225 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7680869 A B x)). Qed.
Lemma lem7680871 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7680872 {A B : Type'} : (term576 A B) = (term226 A B).
Proof. exact (MK_COMB (@lem7680871 A B) (@lem7680870 A B)). Qed.
Lemma lem7680873 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680874 {A B : Type'} : (term577 A B) = (term247 A B).
Proof. exact (MK_COMB (@lem7680873) (@lem7680872 A B)). Qed.
Lemma lem7680875 {A B : Type'} : (term471 A B) = (term471 A B).
Proof. exact (eq_refl (term471 A B)). Qed.
Lemma lem7680876 {A B : Type'} : (term572 A B) = (term472 A B).
Proof. exact (MK_COMB (@lem7680874 A B) (@lem7680875 A B)). Qed.
Lemma lem7680877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7680878 {A B : Type'} : (term578 A B) = (term579 A B).
Proof. exact (MK_COMB (@lem7680877) (@lem7680876 A B)). Qed.
Lemma lem7680879 {A B : Type'} (x : finite_diff A B) : (term574 A B x) = (term218 A B x).
Proof. exact (eq_refl (term574 A B x)). Qed.
Lemma lem7680880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680881 {A B : Type'} (x : finite_diff A B) : (term580 A B x) = (term581 A B x).
Proof. exact (MK_COMB (@lem7680880) (@lem7680879 A B x)). Qed.
Lemma lem7680882 {A B : Type'} : (term471 A B) = (term471 A B).
Proof. exact (eq_refl (term471 A B)). Qed.
Lemma lem7680883 {A B : Type'} (x : finite_diff A B) : (term582 A B x) = (term583 A B x).
Proof. exact (MK_COMB (@lem7680881 A B x) (@lem7680882 A B)). Qed.
Lemma lem7680884 {A B : Type'} : (term584 A B) = (term585 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7680883 A B x)). Qed.
Lemma lem7680885 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7680886 {A B : Type'} : (term573 A B) = (term586 A B).
Proof. exact (MK_COMB (@lem7680885 A B) (@lem7680884 A B)). Qed.
Lemma lem7680887 {A B : Type'} : ((term572 A B) = (term573 A B)) = ((term472 A B) = (term586 A B)).
Proof. exact (MK_COMB (@lem7680878 A B) (@lem7680886 A B)). Qed.
Lemma lem7680888 {A B : Type'} : (term472 A B) = (term586 A B).
Proof. exact (EQ_MP (@lem7680887 A B) (@lem7680868 A B)). Qed.
Lemma lem7680889 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7680890 {A B : Type'} : (term473 A B) = (term587 A B).
Proof. exact (MK_COMB (@lem7680889 A B) (@lem7680888 A B)). Qed.
Lemma lem7680892 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7680893 {A B : Type'} (P : Prop) (Q : type31 A B) : (term590 A B P Q) = (term591 A B P Q).
Proof. exact (@lem7680892 (finite_diff A B) P Q). Qed.
Lemma lem7680894 {A B : Type'} : (term592 A B) = (term593 A B).
Proof. exact (@lem7680893 A B (term20 A B) (term585 A B)). Qed.
Lemma lem7680895 {A B : Type'} (x : finite_diff A B) : (term594 A B x) = (term583 A B x).
Proof. exact (eq_refl (term594 A B x)). Qed.
Lemma lem7680896 {A B : Type'} : (term595 A B) = (term585 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7680895 A B x)). Qed.
Lemma lem7680897 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7680898 {A B : Type'} : (term596 A B) = (term586 A B).
Proof. exact (MK_COMB (@lem7680897 A B) (@lem7680896 A B)). Qed.
Lemma lem7680899 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7680900 {A B : Type'} : (term592 A B) = (term587 A B).
Proof. exact (MK_COMB (@lem7680899 A B) (@lem7680898 A B)). Qed.
Lemma lem7680901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7680902 {A B : Type'} : (term597 A B) = (term598 A B).
Proof. exact (MK_COMB (@lem7680901) (@lem7680900 A B)). Qed.
Lemma lem7680903 {A B : Type'} (x : finite_diff A B) : (term594 A B x) = (term583 A B x).
Proof. exact (eq_refl (term594 A B x)). Qed.
Lemma lem7680904 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7680905 {A B : Type'} (x : finite_diff A B) : (term599 A B x) = (term600 A B x).
Proof. exact (MK_COMB (@lem7680904 A B) (@lem7680903 A B x)). Qed.
Lemma lem7680906 {A B : Type'} : (term601 A B) = (term602 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7680905 A B x)). Qed.
Lemma lem7680907 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7680908 {A B : Type'} : (term593 A B) = (term603 A B).
Proof. exact (MK_COMB (@lem7680907 A B) (@lem7680906 A B)). Qed.
Lemma lem7680909 {A B : Type'} : ((term592 A B) = (term593 A B)) = ((term587 A B) = (term603 A B)).
Proof. exact (MK_COMB (@lem7680902 A B) (@lem7680908 A B)). Qed.
Lemma lem7680910 {A B : Type'} : (term587 A B) = (term603 A B).
Proof. exact (EQ_MP (@lem7680909 A B) (@lem7680894 A B)). Qed.
Lemma lem7680911 {A B : Type'} : (term473 A B) = (term603 A B).
Proof. exact (TRANS (@lem7680890 A B) (@lem7680910 A B)). Qed.
Lemma lem7680912 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7680913 {A B : Type'} : (term474 A B) = (term604 A B).
Proof. exact (MK_COMB (@lem7680912) (@lem7680911 A B)). Qed.
Lemma lem7680915 {A : Type'} (P : A -> Prop) (Q : Prop) : (term568 A P Q) = (term569 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7680916 {A B : Type'} (P : type31 A B) (Q : Prop) : (term570 A B P Q) = (term571 A B P Q).
Proof. exact (@lem7680915 (finite_diff A B) P Q). Qed.
Lemma lem7680917 {A B : Type'} : (term605 A B) = (term606 A B).
Proof. exact (@lem7680916 A B (term270 A B) (term501 A B)). Qed.
Lemma lem7680918 {A B : Type'} (x : finite_diff A B) : (term607 A B x) = (term265 A B x).
Proof. exact (eq_refl (term607 A B x)). Qed.
Lemma lem7680919 {A B : Type'} : (term608 A B) = (term270 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7680918 A B x)). Qed.
Lemma lem7680920 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7680921 {A B : Type'} : (term609 A B) = (term271 A B).
Proof. exact (MK_COMB (@lem7680920 A B) (@lem7680919 A B)). Qed.
Lemma lem7680922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680923 {A B : Type'} : (term610 A B) = (term285 A B).
Proof. exact (MK_COMB (@lem7680922) (@lem7680921 A B)). Qed.
Lemma lem7680924 {A B : Type'} : (term501 A B) = (term501 A B).
Proof. exact (eq_refl (term501 A B)). Qed.
Lemma lem7680925 {A B : Type'} : (term605 A B) = (term502 A B).
Proof. exact (MK_COMB (@lem7680923 A B) (@lem7680924 A B)). Qed.
Lemma lem7680926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7680927 {A B : Type'} : (term611 A B) = (term612 A B).
Proof. exact (MK_COMB (@lem7680926) (@lem7680925 A B)). Qed.
Lemma lem7680928 {A B : Type'} (x : finite_diff A B) : (term607 A B x) = (term265 A B x).
Proof. exact (eq_refl (term607 A B x)). Qed.
Lemma lem7680929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7680930 {A B : Type'} (x : finite_diff A B) : (term613 A B x) = (term614 A B x).
Proof. exact (MK_COMB (@lem7680929) (@lem7680928 A B x)). Qed.
Lemma lem7680931 {A B : Type'} : (term501 A B) = (term501 A B).
Proof. exact (eq_refl (term501 A B)). Qed.
Lemma lem7680932 {A B : Type'} (x : finite_diff A B) : (term615 A B x) = (term616 A B x).
Proof. exact (MK_COMB (@lem7680930 A B x) (@lem7680931 A B)). Qed.
Lemma lem7680933 {A B : Type'} : (term617 A B) = (term618 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7680932 A B x)). Qed.
Lemma lem7680934 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7680935 {A B : Type'} : (term606 A B) = (term619 A B).
Proof. exact (MK_COMB (@lem7680934 A B) (@lem7680933 A B)). Qed.
Lemma lem7680936 {A B : Type'} : ((term605 A B) = (term606 A B)) = ((term502 A B) = (term619 A B)).
Proof. exact (MK_COMB (@lem7680927 A B) (@lem7680935 A B)). Qed.
Lemma lem7680937 {A B : Type'} : (term502 A B) = (term619 A B).
Proof. exact (EQ_MP (@lem7680936 A B) (@lem7680917 A B)). Qed.
Lemma lem7680938 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7680939 {A B : Type'} : (term503 A B) = (term620 A B).
Proof. exact (MK_COMB (@lem7680938 A B) (@lem7680937 A B)). Qed.
Lemma lem7680941 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7680942 {A B : Type'} (P : Prop) (Q : type31 A B) : (term590 A B P Q) = (term591 A B P Q).
Proof. exact (@lem7680941 (finite_diff A B) P Q). Qed.
Lemma lem7680943 {A B : Type'} : (term621 A B) = (term622 A B).
Proof. exact (@lem7680942 A B (term256 A B) (term618 A B)). Qed.
Lemma lem7680944 {A B : Type'} (x : finite_diff A B) : (term623 A B x) = (term616 A B x).
Proof. exact (eq_refl (term623 A B x)). Qed.
Lemma lem7680945 {A B : Type'} : (term624 A B) = (term618 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7680944 A B x)). Qed.
Lemma lem7680946 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7680947 {A B : Type'} : (term625 A B) = (term619 A B).
Proof. exact (MK_COMB (@lem7680946 A B) (@lem7680945 A B)). Qed.
Lemma lem7680948 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7680949 {A B : Type'} : (term621 A B) = (term620 A B).
Proof. exact (MK_COMB (@lem7680948 A B) (@lem7680947 A B)). Qed.
Lemma lem7680950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7680951 {A B : Type'} : (term626 A B) = (term627 A B).
Proof. exact (MK_COMB (@lem7680950) (@lem7680949 A B)). Qed.
Lemma lem7680952 {A B : Type'} (x : finite_diff A B) : (term623 A B x) = (term616 A B x).
Proof. exact (eq_refl (term623 A B x)). Qed.
Lemma lem7680953 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7680954 {A B : Type'} (x : finite_diff A B) : (term628 A B x) = (term629 A B x).
Proof. exact (MK_COMB (@lem7680953 A B) (@lem7680952 A B x)). Qed.
Lemma lem7680955 {A B : Type'} : (term630 A B) = (term631 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7680954 A B x)). Qed.
Lemma lem7680956 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7680957 {A B : Type'} : (term622 A B) = (term632 A B).
Proof. exact (MK_COMB (@lem7680956 A B) (@lem7680955 A B)). Qed.
Lemma lem7680958 {A B : Type'} : ((term621 A B) = (term622 A B)) = ((term620 A B) = (term632 A B)).
Proof. exact (MK_COMB (@lem7680951 A B) (@lem7680957 A B)). Qed.
Lemma lem7680959 {A B : Type'} : (term620 A B) = (term632 A B).
Proof. exact (EQ_MP (@lem7680958 A B) (@lem7680943 A B)). Qed.
Lemma lem7680960 {A B : Type'} : (term503 A B) = (term632 A B).
Proof. exact (TRANS (@lem7680939 A B) (@lem7680959 A B)). Qed.
Lemma lem7680961 {A B : Type'} : (term504 A B) = (term633 A B).
Proof. exact (MK_COMB (@lem7680913 A B) (@lem7680960 A B)). Qed.
Lemma lem7680963 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term634 A P Q) = (term635 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7680964 {A B : Type'} (P : type31 A B) (Q : type31 A B) : (term636 A B P Q) = (term637 A B P Q).
Proof. exact (@lem7680963 (finite_diff A B) P Q). Qed.
Lemma lem7680965 {A B : Type'} : (term638 A B) = (term639 A B).
Proof. exact (@lem7680964 A B (term602 A B) (term631 A B)). Qed.
Lemma lem7680966 {A B : Type'} (x : finite_diff A B) : (term640 A B x) = (term600 A B x).
Proof. exact (eq_refl (term640 A B x)). Qed.
Lemma lem7680967 {A B : Type'} : (term641 A B) = (term602 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7680966 A B x)). Qed.
Lemma lem7680968 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7680969 {A B : Type'} : (term642 A B) = (term603 A B).
Proof. exact (MK_COMB (@lem7680968 A B) (@lem7680967 A B)). Qed.
Lemma lem7680970 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7680971 {A B : Type'} : (term643 A B) = (term604 A B).
Proof. exact (MK_COMB (@lem7680970) (@lem7680969 A B)). Qed.
Lemma lem7680972 {A B : Type'} (x : finite_diff A B) : (term644 A B x) = (term629 A B x).
Proof. exact (eq_refl (term644 A B x)). Qed.
Lemma lem7680973 {A B : Type'} : (term645 A B) = (term631 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7680972 A B x)). Qed.
Lemma lem7680974 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7680975 {A B : Type'} : (term646 A B) = (term632 A B).
Proof. exact (MK_COMB (@lem7680974 A B) (@lem7680973 A B)). Qed.
Lemma lem7680976 {A B : Type'} : (term638 A B) = (term633 A B).
Proof. exact (MK_COMB (@lem7680971 A B) (@lem7680975 A B)). Qed.
Lemma lem7680977 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7680978 {A B : Type'} : (term647 A B) = (term648 A B).
Proof. exact (MK_COMB (@lem7680977) (@lem7680976 A B)). Qed.
Lemma lem7680979 {A B : Type'} (x : finite_diff A B) : (term640 A B x) = (term600 A B x).
Proof. exact (eq_refl (term640 A B x)). Qed.
Lemma lem7680980 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7680981 {A B : Type'} (x : finite_diff A B) : (term649 A B x) = (term650 A B x).
Proof. exact (MK_COMB (@lem7680980) (@lem7680979 A B x)). Qed.
Lemma lem7680982 {A B : Type'} (x : finite_diff A B) : (term644 A B x) = (term629 A B x).
Proof. exact (eq_refl (term644 A B x)). Qed.
Lemma lem7680983 {A B : Type'} (x : finite_diff A B) : (term651 A B x) = (term652 A B x).
Proof. exact (MK_COMB (@lem7680981 A B x) (@lem7680982 A B x)). Qed.
Lemma lem7680984 {A B : Type'} : (term653 A B) = (term654 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7680983 A B x)). Qed.
Lemma lem7680985 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7680986 {A B : Type'} : (term639 A B) = (term655 A B).
Proof. exact (MK_COMB (@lem7680985 A B) (@lem7680984 A B)). Qed.
Lemma lem7680987 {A B : Type'} : ((term638 A B) = (term639 A B)) = ((term633 A B) = (term655 A B)).
Proof. exact (MK_COMB (@lem7680978 A B) (@lem7680986 A B)). Qed.
Lemma lem7680988 {A B : Type'} : (term633 A B) = (term655 A B).
Proof. exact (EQ_MP (@lem7680987 A B) (@lem7680965 A B)). Qed.
Lemma lem7680989 {A B : Type'} : (term504 A B) = (term655 A B).
Proof. exact (TRANS (@lem7680961 A B) (@lem7680988 A B)). Qed.
Lemma lem7680990 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (eq_refl (term299 A)). Qed.
Lemma lem7680991 {A B : Type'} : (term505 A B) = (term656 A B).
Proof. exact (MK_COMB (@lem7680990 A) (@lem7680989 A B)). Qed.
Lemma lem7680993 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7680994 {A B : Type'} (P : Prop) (Q : type31 A B) : (term590 A B P Q) = (term591 A B P Q).
Proof. exact (@lem7680993 (finite_diff A B) P Q). Qed.
Lemma lem7680995 {A B : Type'} : (term657 A B) = (term658 A B).
Proof. exact (@lem7680994 A B (term83 A) (term654 A B)). Qed.
Lemma lem7680996 {A B : Type'} (x : finite_diff A B) : (term659 A B x) = (term652 A B x).
Proof. exact (eq_refl (term659 A B x)). Qed.
Lemma lem7680997 {A B : Type'} : (term660 A B) = (term654 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7680996 A B x)). Qed.
Lemma lem7680998 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7680999 {A B : Type'} : (term661 A B) = (term655 A B).
Proof. exact (MK_COMB (@lem7680998 A B) (@lem7680997 A B)). Qed.
Lemma lem7681000 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (eq_refl (term299 A)). Qed.
Lemma lem7681001 {A B : Type'} : (term657 A B) = (term656 A B).
Proof. exact (MK_COMB (@lem7681000 A) (@lem7680999 A B)). Qed.
Lemma lem7681002 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681003 {A B : Type'} : (term662 A B) = (term663 A B).
Proof. exact (MK_COMB (@lem7681002) (@lem7681001 A B)). Qed.
Lemma lem7681004 {A B : Type'} (x : finite_diff A B) : (term659 A B x) = (term652 A B x).
Proof. exact (eq_refl (term659 A B x)). Qed.
Lemma lem7681005 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (eq_refl (term299 A)). Qed.
Lemma lem7681006 {A B : Type'} (x : finite_diff A B) : (term664 A B x) = (term665 A B x).
Proof. exact (MK_COMB (@lem7681005 A) (@lem7681004 A B x)). Qed.
Lemma lem7681007 {A B : Type'} : (term666 A B) = (term667 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681006 A B x)). Qed.
Lemma lem7681008 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681009 {A B : Type'} : (term658 A B) = (term668 A B).
Proof. exact (MK_COMB (@lem7681008 A B) (@lem7681007 A B)). Qed.
Lemma lem7681010 {A B : Type'} : ((term657 A B) = (term658 A B)) = ((term656 A B) = (term668 A B)).
Proof. exact (MK_COMB (@lem7681003 A B) (@lem7681009 A B)). Qed.
Lemma lem7681011 {A B : Type'} : (term656 A B) = (term668 A B).
Proof. exact (EQ_MP (@lem7681010 A B) (@lem7680995 A B)). Qed.
Lemma lem7681012 {A B : Type'} : (term505 A B) = (term668 A B).
Proof. exact (TRANS (@lem7680991 A B) (@lem7681011 A B)). Qed.
Lemma lem7681013 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681014 {A B : Type'} : (term506 A B) = (term669 A B).
Proof. exact (MK_COMB (@lem7681013) (@lem7681012 A B)). Qed.
Lemma lem7681016 {A : Type'} (P : A -> Prop) (Q : Prop) : (term568 A P Q) = (term569 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7681017 {A B : Type'} (P : type31 A B) (Q : Prop) : (term570 A B P Q) = (term571 A B P Q).
Proof. exact (@lem7681016 (finite_diff A B) P Q). Qed.
Lemma lem7681018 {A B : Type'} : (term670 A B) = (term671 A B).
Proof. exact (@lem7681017 A B (term225 A B) (term532 A B)). Qed.
Lemma lem7681019 {A B : Type'} (x : finite_diff A B) : (term574 A B x) = (term218 A B x).
Proof. exact (eq_refl (term574 A B x)). Qed.
Lemma lem7681020 {A B : Type'} : (term575 A B) = (term225 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681019 A B x)). Qed.
Lemma lem7681021 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681022 {A B : Type'} : (term576 A B) = (term226 A B).
Proof. exact (MK_COMB (@lem7681021 A B) (@lem7681020 A B)). Qed.
Lemma lem7681023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681024 {A B : Type'} : (term577 A B) = (term247 A B).
Proof. exact (MK_COMB (@lem7681023) (@lem7681022 A B)). Qed.
Lemma lem7681025 {A B : Type'} : (term532 A B) = (term532 A B).
Proof. exact (eq_refl (term532 A B)). Qed.
Lemma lem7681026 {A B : Type'} : (term670 A B) = (term533 A B).
Proof. exact (MK_COMB (@lem7681024 A B) (@lem7681025 A B)). Qed.
Lemma lem7681027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681028 {A B : Type'} : (term672 A B) = (term673 A B).
Proof. exact (MK_COMB (@lem7681027) (@lem7681026 A B)). Qed.
Lemma lem7681029 {A B : Type'} (x : finite_diff A B) : (term574 A B x) = (term218 A B x).
Proof. exact (eq_refl (term574 A B x)). Qed.
Lemma lem7681030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681031 {A B : Type'} (x : finite_diff A B) : (term580 A B x) = (term581 A B x).
Proof. exact (MK_COMB (@lem7681030) (@lem7681029 A B x)). Qed.
Lemma lem7681032 {A B : Type'} : (term532 A B) = (term532 A B).
Proof. exact (eq_refl (term532 A B)). Qed.
Lemma lem7681033 {A B : Type'} (x : finite_diff A B) : (term674 A B x) = (term675 A B x).
Proof. exact (MK_COMB (@lem7681031 A B x) (@lem7681032 A B)). Qed.
Lemma lem7681034 {A B : Type'} : (term676 A B) = (term677 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681033 A B x)). Qed.
Lemma lem7681035 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681036 {A B : Type'} : (term671 A B) = (term678 A B).
Proof. exact (MK_COMB (@lem7681035 A B) (@lem7681034 A B)). Qed.
Lemma lem7681037 {A B : Type'} : ((term670 A B) = (term671 A B)) = ((term533 A B) = (term678 A B)).
Proof. exact (MK_COMB (@lem7681028 A B) (@lem7681036 A B)). Qed.
Lemma lem7681038 {A B : Type'} : (term533 A B) = (term678 A B).
Proof. exact (EQ_MP (@lem7681037 A B) (@lem7681018 A B)). Qed.
Lemma lem7681039 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7681040 {A B : Type'} : (term534 A B) = (term679 A B).
Proof. exact (MK_COMB (@lem7681039 A B) (@lem7681038 A B)). Qed.
Lemma lem7681042 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7681043 {A B : Type'} (P : Prop) (Q : type31 A B) : (term590 A B P Q) = (term591 A B P Q).
Proof. exact (@lem7681042 (finite_diff A B) P Q). Qed.
Lemma lem7681044 {A B : Type'} : (term680 A B) = (term681 A B).
Proof. exact (@lem7681043 A B (term20 A B) (term677 A B)). Qed.
Lemma lem7681045 {A B : Type'} (x : finite_diff A B) : (term682 A B x) = (term675 A B x).
Proof. exact (eq_refl (term682 A B x)). Qed.
Lemma lem7681046 {A B : Type'} : (term683 A B) = (term677 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681045 A B x)). Qed.
Lemma lem7681047 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681048 {A B : Type'} : (term684 A B) = (term678 A B).
Proof. exact (MK_COMB (@lem7681047 A B) (@lem7681046 A B)). Qed.
Lemma lem7681049 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7681050 {A B : Type'} : (term680 A B) = (term679 A B).
Proof. exact (MK_COMB (@lem7681049 A B) (@lem7681048 A B)). Qed.
Lemma lem7681051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681052 {A B : Type'} : (term685 A B) = (term686 A B).
Proof. exact (MK_COMB (@lem7681051) (@lem7681050 A B)). Qed.
Lemma lem7681053 {A B : Type'} (x : finite_diff A B) : (term682 A B x) = (term675 A B x).
Proof. exact (eq_refl (term682 A B x)). Qed.
Lemma lem7681054 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7681055 {A B : Type'} (x : finite_diff A B) : (term687 A B x) = (term688 A B x).
Proof. exact (MK_COMB (@lem7681054 A B) (@lem7681053 A B x)). Qed.
Lemma lem7681056 {A B : Type'} : (term689 A B) = (term690 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681055 A B x)). Qed.
Lemma lem7681057 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681058 {A B : Type'} : (term681 A B) = (term691 A B).
Proof. exact (MK_COMB (@lem7681057 A B) (@lem7681056 A B)). Qed.
Lemma lem7681059 {A B : Type'} : ((term680 A B) = (term681 A B)) = ((term679 A B) = (term691 A B)).
Proof. exact (MK_COMB (@lem7681052 A B) (@lem7681058 A B)). Qed.
Lemma lem7681060 {A B : Type'} : (term679 A B) = (term691 A B).
Proof. exact (EQ_MP (@lem7681059 A B) (@lem7681044 A B)). Qed.
Lemma lem7681061 {A B : Type'} : (term534 A B) = (term691 A B).
Proof. exact (TRANS (@lem7681040 A B) (@lem7681060 A B)). Qed.
Lemma lem7681062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681063 {A B : Type'} : (term535 A B) = (term692 A B).
Proof. exact (MK_COMB (@lem7681062) (@lem7681061 A B)). Qed.
Lemma lem7681065 {A : Type'} (P : A -> Prop) (Q : Prop) : (term568 A P Q) = (term569 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7681066 {A B : Type'} (P : type31 A B) (Q : Prop) : (term570 A B P Q) = (term571 A B P Q).
Proof. exact (@lem7681065 (finite_diff A B) P Q). Qed.
Lemma lem7681067 {A B : Type'} : (term693 A B) = (term694 A B).
Proof. exact (@lem7681066 A B (term270 A B) (term536 A B)). Qed.
Lemma lem7681068 {A B : Type'} (x : finite_diff A B) : (term607 A B x) = (term265 A B x).
Proof. exact (eq_refl (term607 A B x)). Qed.
Lemma lem7681069 {A B : Type'} : (term608 A B) = (term270 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681068 A B x)). Qed.
Lemma lem7681070 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681071 {A B : Type'} : (term609 A B) = (term271 A B).
Proof. exact (MK_COMB (@lem7681070 A B) (@lem7681069 A B)). Qed.
Lemma lem7681072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681073 {A B : Type'} : (term610 A B) = (term285 A B).
Proof. exact (MK_COMB (@lem7681072) (@lem7681071 A B)). Qed.
Lemma lem7681074 {A B : Type'} : (term536 A B) = (term536 A B).
Proof. exact (eq_refl (term536 A B)). Qed.
Lemma lem7681075 {A B : Type'} : (term693 A B) = (term537 A B).
Proof. exact (MK_COMB (@lem7681073 A B) (@lem7681074 A B)). Qed.
Lemma lem7681076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681077 {A B : Type'} : (term695 A B) = (term696 A B).
Proof. exact (MK_COMB (@lem7681076) (@lem7681075 A B)). Qed.
Lemma lem7681078 {A B : Type'} (x : finite_diff A B) : (term607 A B x) = (term265 A B x).
Proof. exact (eq_refl (term607 A B x)). Qed.
Lemma lem7681079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681080 {A B : Type'} (x : finite_diff A B) : (term613 A B x) = (term614 A B x).
Proof. exact (MK_COMB (@lem7681079) (@lem7681078 A B x)). Qed.
Lemma lem7681081 {A B : Type'} : (term536 A B) = (term536 A B).
Proof. exact (eq_refl (term536 A B)). Qed.
Lemma lem7681082 {A B : Type'} (x : finite_diff A B) : (term697 A B x) = (term698 A B x).
Proof. exact (MK_COMB (@lem7681080 A B x) (@lem7681081 A B)). Qed.
Lemma lem7681083 {A B : Type'} : (term699 A B) = (term700 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681082 A B x)). Qed.
Lemma lem7681084 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681085 {A B : Type'} : (term694 A B) = (term701 A B).
Proof. exact (MK_COMB (@lem7681084 A B) (@lem7681083 A B)). Qed.
Lemma lem7681086 {A B : Type'} : ((term693 A B) = (term694 A B)) = ((term537 A B) = (term701 A B)).
Proof. exact (MK_COMB (@lem7681077 A B) (@lem7681085 A B)). Qed.
Lemma lem7681087 {A B : Type'} : (term537 A B) = (term701 A B).
Proof. exact (EQ_MP (@lem7681086 A B) (@lem7681067 A B)). Qed.
Lemma lem7681088 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7681089 {A B : Type'} : (term538 A B) = (term702 A B).
Proof. exact (MK_COMB (@lem7681088 A B) (@lem7681087 A B)). Qed.
Lemma lem7681091 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7681092 {A B : Type'} (P : Prop) (Q : type31 A B) : (term590 A B P Q) = (term591 A B P Q).
Proof. exact (@lem7681091 (finite_diff A B) P Q). Qed.
Lemma lem7681093 {A B : Type'} : (term703 A B) = (term704 A B).
Proof. exact (@lem7681092 A B (term256 A B) (term700 A B)). Qed.
Lemma lem7681094 {A B : Type'} (x : finite_diff A B) : (term705 A B x) = (term698 A B x).
Proof. exact (eq_refl (term705 A B x)). Qed.
Lemma lem7681095 {A B : Type'} : (term706 A B) = (term700 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681094 A B x)). Qed.
Lemma lem7681096 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681097 {A B : Type'} : (term707 A B) = (term701 A B).
Proof. exact (MK_COMB (@lem7681096 A B) (@lem7681095 A B)). Qed.
Lemma lem7681098 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7681099 {A B : Type'} : (term703 A B) = (term702 A B).
Proof. exact (MK_COMB (@lem7681098 A B) (@lem7681097 A B)). Qed.
Lemma lem7681100 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681101 {A B : Type'} : (term708 A B) = (term709 A B).
Proof. exact (MK_COMB (@lem7681100) (@lem7681099 A B)). Qed.
Lemma lem7681102 {A B : Type'} (x : finite_diff A B) : (term705 A B x) = (term698 A B x).
Proof. exact (eq_refl (term705 A B x)). Qed.
Lemma lem7681103 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7681104 {A B : Type'} (x : finite_diff A B) : (term710 A B x) = (term711 A B x).
Proof. exact (MK_COMB (@lem7681103 A B) (@lem7681102 A B x)). Qed.
Lemma lem7681105 {A B : Type'} : (term712 A B) = (term713 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681104 A B x)). Qed.
Lemma lem7681106 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681107 {A B : Type'} : (term704 A B) = (term714 A B).
Proof. exact (MK_COMB (@lem7681106 A B) (@lem7681105 A B)). Qed.
Lemma lem7681108 {A B : Type'} : ((term703 A B) = (term704 A B)) = ((term702 A B) = (term714 A B)).
Proof. exact (MK_COMB (@lem7681101 A B) (@lem7681107 A B)). Qed.
Lemma lem7681109 {A B : Type'} : (term702 A B) = (term714 A B).
Proof. exact (EQ_MP (@lem7681108 A B) (@lem7681093 A B)). Qed.
Lemma lem7681110 {A B : Type'} : (term538 A B) = (term714 A B).
Proof. exact (TRANS (@lem7681089 A B) (@lem7681109 A B)). Qed.
Lemma lem7681111 {A B : Type'} : (term539 A B) = (term715 A B).
Proof. exact (MK_COMB (@lem7681063 A B) (@lem7681110 A B)). Qed.
Lemma lem7681113 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term634 A P Q) = (term635 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7681114 {A B : Type'} (P : type31 A B) (Q : type31 A B) : (term636 A B P Q) = (term637 A B P Q).
Proof. exact (@lem7681113 (finite_diff A B) P Q). Qed.
Lemma lem7681115 {A B : Type'} : (term716 A B) = (term717 A B).
Proof. exact (@lem7681114 A B (term690 A B) (term713 A B)). Qed.
Lemma lem7681116 {A B : Type'} (x : finite_diff A B) : (term718 A B x) = (term688 A B x).
Proof. exact (eq_refl (term718 A B x)). Qed.
Lemma lem7681117 {A B : Type'} : (term719 A B) = (term690 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681116 A B x)). Qed.
Lemma lem7681118 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681119 {A B : Type'} : (term720 A B) = (term691 A B).
Proof. exact (MK_COMB (@lem7681118 A B) (@lem7681117 A B)). Qed.
Lemma lem7681120 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681121 {A B : Type'} : (term721 A B) = (term692 A B).
Proof. exact (MK_COMB (@lem7681120) (@lem7681119 A B)). Qed.
Lemma lem7681122 {A B : Type'} (x : finite_diff A B) : (term722 A B x) = (term711 A B x).
Proof. exact (eq_refl (term722 A B x)). Qed.
Lemma lem7681123 {A B : Type'} : (term723 A B) = (term713 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681122 A B x)). Qed.
Lemma lem7681124 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681125 {A B : Type'} : (term724 A B) = (term714 A B).
Proof. exact (MK_COMB (@lem7681124 A B) (@lem7681123 A B)). Qed.
Lemma lem7681126 {A B : Type'} : (term716 A B) = (term715 A B).
Proof. exact (MK_COMB (@lem7681121 A B) (@lem7681125 A B)). Qed.
Lemma lem7681127 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681128 {A B : Type'} : (term725 A B) = (term726 A B).
Proof. exact (MK_COMB (@lem7681127) (@lem7681126 A B)). Qed.
Lemma lem7681129 {A B : Type'} (x : finite_diff A B) : (term718 A B x) = (term688 A B x).
Proof. exact (eq_refl (term718 A B x)). Qed.
Lemma lem7681130 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681131 {A B : Type'} (x : finite_diff A B) : (term727 A B x) = (term728 A B x).
Proof. exact (MK_COMB (@lem7681130) (@lem7681129 A B x)). Qed.
Lemma lem7681132 {A B : Type'} (x : finite_diff A B) : (term722 A B x) = (term711 A B x).
Proof. exact (eq_refl (term722 A B x)). Qed.
Lemma lem7681133 {A B : Type'} (x : finite_diff A B) : (term729 A B x) = (term730 A B x).
Proof. exact (MK_COMB (@lem7681131 A B x) (@lem7681132 A B x)). Qed.
Lemma lem7681134 {A B : Type'} : (term731 A B) = (term732 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681133 A B x)). Qed.
Lemma lem7681135 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681136 {A B : Type'} : (term717 A B) = (term733 A B).
Proof. exact (MK_COMB (@lem7681135 A B) (@lem7681134 A B)). Qed.
Lemma lem7681137 {A B : Type'} : ((term716 A B) = (term717 A B)) = ((term715 A B) = (term733 A B)).
Proof. exact (MK_COMB (@lem7681128 A B) (@lem7681136 A B)). Qed.
Lemma lem7681138 {A B : Type'} : (term715 A B) = (term733 A B).
Proof. exact (EQ_MP (@lem7681137 A B) (@lem7681115 A B)). Qed.
Lemma lem7681139 {A B : Type'} : (term539 A B) = (term733 A B).
Proof. exact (TRANS (@lem7681111 A B) (@lem7681138 A B)). Qed.
Lemma lem7681140 {A : Type'} : (term333 A) = (term333 A).
Proof. exact (eq_refl (term333 A)). Qed.
Lemma lem7681141 {A B : Type'} : (term540 A B) = (term734 A B).
Proof. exact (MK_COMB (@lem7681140 A) (@lem7681139 A B)). Qed.
Lemma lem7681143 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7681144 {A B : Type'} (P : Prop) (Q : type31 A B) : (term590 A B P Q) = (term591 A B P Q).
Proof. exact (@lem7681143 (finite_diff A B) P Q). Qed.
Lemma lem7681145 {A B : Type'} : (term735 A B) = (term736 A B).
Proof. exact (@lem7681144 A B (term303 A) (term732 A B)). Qed.
Lemma lem7681146 {A B : Type'} (x : finite_diff A B) : (term737 A B x) = (term730 A B x).
Proof. exact (eq_refl (term737 A B x)). Qed.
Lemma lem7681147 {A B : Type'} : (term738 A B) = (term732 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681146 A B x)). Qed.
Lemma lem7681148 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681149 {A B : Type'} : (term739 A B) = (term733 A B).
Proof. exact (MK_COMB (@lem7681148 A B) (@lem7681147 A B)). Qed.
Lemma lem7681150 {A : Type'} : (term333 A) = (term333 A).
Proof. exact (eq_refl (term333 A)). Qed.
Lemma lem7681151 {A B : Type'} : (term735 A B) = (term734 A B).
Proof. exact (MK_COMB (@lem7681150 A) (@lem7681149 A B)). Qed.
Lemma lem7681152 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681153 {A B : Type'} : (term740 A B) = (term741 A B).
Proof. exact (MK_COMB (@lem7681152) (@lem7681151 A B)). Qed.
Lemma lem7681154 {A B : Type'} (x : finite_diff A B) : (term737 A B x) = (term730 A B x).
Proof. exact (eq_refl (term737 A B x)). Qed.
Lemma lem7681155 {A : Type'} : (term333 A) = (term333 A).
Proof. exact (eq_refl (term333 A)). Qed.
Lemma lem7681156 {A B : Type'} (x : finite_diff A B) : (term742 A B x) = (term743 A B x).
Proof. exact (MK_COMB (@lem7681155 A) (@lem7681154 A B x)). Qed.
Lemma lem7681157 {A B : Type'} : (term744 A B) = (term745 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681156 A B x)). Qed.
Lemma lem7681158 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681159 {A B : Type'} : (term736 A B) = (term746 A B).
Proof. exact (MK_COMB (@lem7681158 A B) (@lem7681157 A B)). Qed.
Lemma lem7681160 {A B : Type'} : ((term735 A B) = (term736 A B)) = ((term734 A B) = (term746 A B)).
Proof. exact (MK_COMB (@lem7681153 A B) (@lem7681159 A B)). Qed.
Lemma lem7681161 {A B : Type'} : (term734 A B) = (term746 A B).
Proof. exact (EQ_MP (@lem7681160 A B) (@lem7681145 A B)). Qed.
Lemma lem7681162 {A B : Type'} : (term540 A B) = (term746 A B).
Proof. exact (TRANS (@lem7681141 A B) (@lem7681161 A B)). Qed.
Lemma lem7681163 {A B : Type'} : (term541 A B) = (term747 A B).
Proof. exact (MK_COMB (@lem7681014 A B) (@lem7681162 A B)). Qed.
Lemma lem7681165 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term634 A P Q) = (term635 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7681166 {A B : Type'} (P : type31 A B) (Q : type31 A B) : (term636 A B P Q) = (term637 A B P Q).
Proof. exact (@lem7681165 (finite_diff A B) P Q). Qed.
Lemma lem7681167 {A B : Type'} : (term748 A B) = (term749 A B).
Proof. exact (@lem7681166 A B (term667 A B) (term745 A B)). Qed.
Lemma lem7681168 {A B : Type'} (x : finite_diff A B) : (term750 A B x) = (term665 A B x).
Proof. exact (eq_refl (term750 A B x)). Qed.
Lemma lem7681169 {A B : Type'} : (term751 A B) = (term667 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681168 A B x)). Qed.
Lemma lem7681170 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681171 {A B : Type'} : (term752 A B) = (term668 A B).
Proof. exact (MK_COMB (@lem7681170 A B) (@lem7681169 A B)). Qed.
Lemma lem7681172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681173 {A B : Type'} : (term753 A B) = (term669 A B).
Proof. exact (MK_COMB (@lem7681172) (@lem7681171 A B)). Qed.
Lemma lem7681174 {A B : Type'} (x : finite_diff A B) : (term754 A B x) = (term743 A B x).
Proof. exact (eq_refl (term754 A B x)). Qed.
Lemma lem7681175 {A B : Type'} : (term755 A B) = (term745 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681174 A B x)). Qed.
Lemma lem7681176 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681177 {A B : Type'} : (term756 A B) = (term746 A B).
Proof. exact (MK_COMB (@lem7681176 A B) (@lem7681175 A B)). Qed.
Lemma lem7681178 {A B : Type'} : (term748 A B) = (term747 A B).
Proof. exact (MK_COMB (@lem7681173 A B) (@lem7681177 A B)). Qed.
Lemma lem7681179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681180 {A B : Type'} : (term757 A B) = (term758 A B).
Proof. exact (MK_COMB (@lem7681179) (@lem7681178 A B)). Qed.
Lemma lem7681181 {A B : Type'} (x : finite_diff A B) : (term750 A B x) = (term665 A B x).
Proof. exact (eq_refl (term750 A B x)). Qed.
Lemma lem7681182 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681183 {A B : Type'} (x : finite_diff A B) : (term759 A B x) = (term760 A B x).
Proof. exact (MK_COMB (@lem7681182) (@lem7681181 A B x)). Qed.
Lemma lem7681184 {A B : Type'} (x : finite_diff A B) : (term754 A B x) = (term743 A B x).
Proof. exact (eq_refl (term754 A B x)). Qed.
Lemma lem7681185 {A B : Type'} (x : finite_diff A B) : (term761 A B x) = (term762 A B x).
Proof. exact (MK_COMB (@lem7681183 A B x) (@lem7681184 A B x)). Qed.
Lemma lem7681186 {A B : Type'} : (term763 A B) = (term764 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681185 A B x)). Qed.
Lemma lem7681187 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681188 {A B : Type'} : (term749 A B) = (term765 A B).
Proof. exact (MK_COMB (@lem7681187 A B) (@lem7681186 A B)). Qed.
Lemma lem7681189 {A B : Type'} : ((term748 A B) = (term749 A B)) = ((term747 A B) = (term765 A B)).
Proof. exact (MK_COMB (@lem7681180 A B) (@lem7681188 A B)). Qed.
Lemma lem7681190 {A B : Type'} : (term747 A B) = (term765 A B).
Proof. exact (EQ_MP (@lem7681189 A B) (@lem7681167 A B)). Qed.
Lemma lem7681191 {A B : Type'} : (term541 A B) = (term765 A B).
Proof. exact (TRANS (@lem7681163 A B) (@lem7681190 A B)). Qed.
Lemma lem7681192 {B : Type'} : (term299 B) = (term299 B).
Proof. exact (eq_refl (term299 B)). Qed.
Lemma lem7681193 {A B : Type'} : (term542 A B) = (term766 A B).
Proof. exact (MK_COMB (@lem7681192 B) (@lem7681191 A B)). Qed.
Lemma lem7681195 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7681196 {A B : Type'} (P : Prop) (Q : type31 A B) : (term590 A B P Q) = (term591 A B P Q).
Proof. exact (@lem7681195 (finite_diff A B) P Q). Qed.
Lemma lem7681197 {A B : Type'} : (term767 A B) = (term768 A B).
Proof. exact (@lem7681196 A B (term83 B) (term764 A B)). Qed.
Lemma lem7681198 {A B : Type'} (x : finite_diff A B) : (term769 A B x) = (term762 A B x).
Proof. exact (eq_refl (term769 A B x)). Qed.
Lemma lem7681199 {A B : Type'} : (term770 A B) = (term764 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681198 A B x)). Qed.
Lemma lem7681200 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681201 {A B : Type'} : (term771 A B) = (term765 A B).
Proof. exact (MK_COMB (@lem7681200 A B) (@lem7681199 A B)). Qed.
Lemma lem7681202 {B : Type'} : (term299 B) = (term299 B).
Proof. exact (eq_refl (term299 B)). Qed.
Lemma lem7681203 {A B : Type'} : (term767 A B) = (term766 A B).
Proof. exact (MK_COMB (@lem7681202 B) (@lem7681201 A B)). Qed.
Lemma lem7681204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681205 {A B : Type'} : (term772 A B) = (term773 A B).
Proof. exact (MK_COMB (@lem7681204) (@lem7681203 A B)). Qed.
Lemma lem7681206 {A B : Type'} (x : finite_diff A B) : (term769 A B x) = (term762 A B x).
Proof. exact (eq_refl (term769 A B x)). Qed.
Lemma lem7681207 {B : Type'} : (term299 B) = (term299 B).
Proof. exact (eq_refl (term299 B)). Qed.
Lemma lem7681208 {A B : Type'} (x : finite_diff A B) : (term774 A B x) = (term775 A B x).
Proof. exact (MK_COMB (@lem7681207 B) (@lem7681206 A B x)). Qed.
Lemma lem7681209 {A B : Type'} : (term776 A B) = (term777 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681208 A B x)). Qed.
Lemma lem7681210 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681211 {A B : Type'} : (term768 A B) = (term778 A B).
Proof. exact (MK_COMB (@lem7681210 A B) (@lem7681209 A B)). Qed.
Lemma lem7681212 {A B : Type'} : ((term767 A B) = (term768 A B)) = ((term766 A B) = (term778 A B)).
Proof. exact (MK_COMB (@lem7681205 A B) (@lem7681211 A B)). Qed.
Lemma lem7681213 {A B : Type'} : (term766 A B) = (term778 A B).
Proof. exact (EQ_MP (@lem7681212 A B) (@lem7681197 A B)). Qed.
Lemma lem7681214 {A B : Type'} : (term542 A B) = (term778 A B).
Proof. exact (TRANS (@lem7681193 A B) (@lem7681213 A B)). Qed.
Lemma lem7681215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681216 {A B : Type'} : (term543 A B) = (term779 A B).
Proof. exact (MK_COMB (@lem7681215) (@lem7681214 A B)). Qed.
Lemma lem7681218 {A : Type'} (P : A -> Prop) (Q : Prop) : (term568 A P Q) = (term569 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7681219 {A B : Type'} (P : type31 A B) (Q : Prop) : (term570 A B P Q) = (term571 A B P Q).
Proof. exact (@lem7681218 (finite_diff A B) P Q). Qed.
Lemma lem7681220 {A B : Type'} : (term780 A B) = (term781 A B).
Proof. exact (@lem7681219 A B (term225 A B) (term545 A B)). Qed.
Lemma lem7681221 {A B : Type'} (x : finite_diff A B) : (term574 A B x) = (term218 A B x).
Proof. exact (eq_refl (term574 A B x)). Qed.
Lemma lem7681222 {A B : Type'} : (term575 A B) = (term225 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681221 A B x)). Qed.
Lemma lem7681223 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681224 {A B : Type'} : (term576 A B) = (term226 A B).
Proof. exact (MK_COMB (@lem7681223 A B) (@lem7681222 A B)). Qed.
Lemma lem7681225 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681226 {A B : Type'} : (term577 A B) = (term247 A B).
Proof. exact (MK_COMB (@lem7681225) (@lem7681224 A B)). Qed.
Lemma lem7681227 {A B : Type'} : (term545 A B) = (term545 A B).
Proof. exact (eq_refl (term545 A B)). Qed.
Lemma lem7681228 {A B : Type'} : (term780 A B) = (term546 A B).
Proof. exact (MK_COMB (@lem7681226 A B) (@lem7681227 A B)). Qed.
Lemma lem7681229 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681230 {A B : Type'} : (term782 A B) = (term783 A B).
Proof. exact (MK_COMB (@lem7681229) (@lem7681228 A B)). Qed.
Lemma lem7681231 {A B : Type'} (x : finite_diff A B) : (term574 A B x) = (term218 A B x).
Proof. exact (eq_refl (term574 A B x)). Qed.
Lemma lem7681232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681233 {A B : Type'} (x : finite_diff A B) : (term580 A B x) = (term581 A B x).
Proof. exact (MK_COMB (@lem7681232) (@lem7681231 A B x)). Qed.
Lemma lem7681234 {A B : Type'} : (term545 A B) = (term545 A B).
Proof. exact (eq_refl (term545 A B)). Qed.
Lemma lem7681235 {A B : Type'} (x : finite_diff A B) : (term784 A B x) = (term785 A B x).
Proof. exact (MK_COMB (@lem7681233 A B x) (@lem7681234 A B)). Qed.
Lemma lem7681236 {A B : Type'} : (term786 A B) = (term787 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681235 A B x)). Qed.
Lemma lem7681237 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681238 {A B : Type'} : (term781 A B) = (term788 A B).
Proof. exact (MK_COMB (@lem7681237 A B) (@lem7681236 A B)). Qed.
Lemma lem7681239 {A B : Type'} : ((term780 A B) = (term781 A B)) = ((term546 A B) = (term788 A B)).
Proof. exact (MK_COMB (@lem7681230 A B) (@lem7681238 A B)). Qed.
Lemma lem7681240 {A B : Type'} : (term546 A B) = (term788 A B).
Proof. exact (EQ_MP (@lem7681239 A B) (@lem7681220 A B)). Qed.
Lemma lem7681241 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7681242 {A B : Type'} : (term547 A B) = (term789 A B).
Proof. exact (MK_COMB (@lem7681241 A B) (@lem7681240 A B)). Qed.
Lemma lem7681244 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7681245 {A B : Type'} (P : Prop) (Q : type31 A B) : (term590 A B P Q) = (term591 A B P Q).
Proof. exact (@lem7681244 (finite_diff A B) P Q). Qed.
Lemma lem7681246 {A B : Type'} : (term790 A B) = (term791 A B).
Proof. exact (@lem7681245 A B (term20 A B) (term787 A B)). Qed.
Lemma lem7681247 {A B : Type'} (x : finite_diff A B) : (term792 A B x) = (term785 A B x).
Proof. exact (eq_refl (term792 A B x)). Qed.
Lemma lem7681248 {A B : Type'} : (term793 A B) = (term787 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681247 A B x)). Qed.
Lemma lem7681249 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681250 {A B : Type'} : (term794 A B) = (term788 A B).
Proof. exact (MK_COMB (@lem7681249 A B) (@lem7681248 A B)). Qed.
Lemma lem7681251 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7681252 {A B : Type'} : (term790 A B) = (term789 A B).
Proof. exact (MK_COMB (@lem7681251 A B) (@lem7681250 A B)). Qed.
Lemma lem7681253 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681254 {A B : Type'} : (term795 A B) = (term796 A B).
Proof. exact (MK_COMB (@lem7681253) (@lem7681252 A B)). Qed.
Lemma lem7681255 {A B : Type'} (x : finite_diff A B) : (term792 A B x) = (term785 A B x).
Proof. exact (eq_refl (term792 A B x)). Qed.
Lemma lem7681256 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7681257 {A B : Type'} (x : finite_diff A B) : (term797 A B x) = (term798 A B x).
Proof. exact (MK_COMB (@lem7681256 A B) (@lem7681255 A B x)). Qed.
Lemma lem7681258 {A B : Type'} : (term799 A B) = (term800 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681257 A B x)). Qed.
Lemma lem7681259 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681260 {A B : Type'} : (term791 A B) = (term801 A B).
Proof. exact (MK_COMB (@lem7681259 A B) (@lem7681258 A B)). Qed.
Lemma lem7681261 {A B : Type'} : ((term790 A B) = (term791 A B)) = ((term789 A B) = (term801 A B)).
Proof. exact (MK_COMB (@lem7681254 A B) (@lem7681260 A B)). Qed.
Lemma lem7681262 {A B : Type'} : (term789 A B) = (term801 A B).
Proof. exact (EQ_MP (@lem7681261 A B) (@lem7681246 A B)). Qed.
Lemma lem7681263 {A B : Type'} : (term547 A B) = (term801 A B).
Proof. exact (TRANS (@lem7681242 A B) (@lem7681262 A B)). Qed.
Lemma lem7681264 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681265 {A B : Type'} : (term548 A B) = (term802 A B).
Proof. exact (MK_COMB (@lem7681264) (@lem7681263 A B)). Qed.
Lemma lem7681267 {A : Type'} (P : A -> Prop) (Q : Prop) : (term568 A P Q) = (term569 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7681268 {A B : Type'} (P : type31 A B) (Q : Prop) : (term570 A B P Q) = (term571 A B P Q).
Proof. exact (@lem7681267 (finite_diff A B) P Q). Qed.
Lemma lem7681269 {A B : Type'} : (term803 A B) = (term804 A B).
Proof. exact (@lem7681268 A B (term270 A B) (term550 A B)). Qed.
Lemma lem7681270 {A B : Type'} (x : finite_diff A B) : (term607 A B x) = (term265 A B x).
Proof. exact (eq_refl (term607 A B x)). Qed.
Lemma lem7681271 {A B : Type'} : (term608 A B) = (term270 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681270 A B x)). Qed.
Lemma lem7681272 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681273 {A B : Type'} : (term609 A B) = (term271 A B).
Proof. exact (MK_COMB (@lem7681272 A B) (@lem7681271 A B)). Qed.
Lemma lem7681274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681275 {A B : Type'} : (term610 A B) = (term285 A B).
Proof. exact (MK_COMB (@lem7681274) (@lem7681273 A B)). Qed.
Lemma lem7681276 {A B : Type'} : (term550 A B) = (term550 A B).
Proof. exact (eq_refl (term550 A B)). Qed.
Lemma lem7681277 {A B : Type'} : (term803 A B) = (term551 A B).
Proof. exact (MK_COMB (@lem7681275 A B) (@lem7681276 A B)). Qed.
Lemma lem7681278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681279 {A B : Type'} : (term805 A B) = (term806 A B).
Proof. exact (MK_COMB (@lem7681278) (@lem7681277 A B)). Qed.
Lemma lem7681280 {A B : Type'} (x : finite_diff A B) : (term607 A B x) = (term265 A B x).
Proof. exact (eq_refl (term607 A B x)). Qed.
Lemma lem7681281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681282 {A B : Type'} (x : finite_diff A B) : (term613 A B x) = (term614 A B x).
Proof. exact (MK_COMB (@lem7681281) (@lem7681280 A B x)). Qed.
Lemma lem7681283 {A B : Type'} : (term550 A B) = (term550 A B).
Proof. exact (eq_refl (term550 A B)). Qed.
Lemma lem7681284 {A B : Type'} (x : finite_diff A B) : (term807 A B x) = (term808 A B x).
Proof. exact (MK_COMB (@lem7681282 A B x) (@lem7681283 A B)). Qed.
Lemma lem7681285 {A B : Type'} : (term809 A B) = (term810 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681284 A B x)). Qed.
Lemma lem7681286 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681287 {A B : Type'} : (term804 A B) = (term811 A B).
Proof. exact (MK_COMB (@lem7681286 A B) (@lem7681285 A B)). Qed.
Lemma lem7681288 {A B : Type'} : ((term803 A B) = (term804 A B)) = ((term551 A B) = (term811 A B)).
Proof. exact (MK_COMB (@lem7681279 A B) (@lem7681287 A B)). Qed.
Lemma lem7681289 {A B : Type'} : (term551 A B) = (term811 A B).
Proof. exact (EQ_MP (@lem7681288 A B) (@lem7681269 A B)). Qed.
Lemma lem7681290 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7681291 {A B : Type'} : (term552 A B) = (term812 A B).
Proof. exact (MK_COMB (@lem7681290 A B) (@lem7681289 A B)). Qed.
Lemma lem7681293 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7681294 {A B : Type'} (P : Prop) (Q : type31 A B) : (term590 A B P Q) = (term591 A B P Q).
Proof. exact (@lem7681293 (finite_diff A B) P Q). Qed.
Lemma lem7681295 {A B : Type'} : (term813 A B) = (term814 A B).
Proof. exact (@lem7681294 A B (term256 A B) (term810 A B)). Qed.
Lemma lem7681296 {A B : Type'} (x : finite_diff A B) : (term815 A B x) = (term808 A B x).
Proof. exact (eq_refl (term815 A B x)). Qed.
Lemma lem7681297 {A B : Type'} : (term816 A B) = (term810 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681296 A B x)). Qed.
Lemma lem7681298 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681299 {A B : Type'} : (term817 A B) = (term811 A B).
Proof. exact (MK_COMB (@lem7681298 A B) (@lem7681297 A B)). Qed.
Lemma lem7681300 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7681301 {A B : Type'} : (term813 A B) = (term812 A B).
Proof. exact (MK_COMB (@lem7681300 A B) (@lem7681299 A B)). Qed.
Lemma lem7681302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681303 {A B : Type'} : (term818 A B) = (term819 A B).
Proof. exact (MK_COMB (@lem7681302) (@lem7681301 A B)). Qed.
Lemma lem7681304 {A B : Type'} (x : finite_diff A B) : (term815 A B x) = (term808 A B x).
Proof. exact (eq_refl (term815 A B x)). Qed.
Lemma lem7681305 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7681306 {A B : Type'} (x : finite_diff A B) : (term820 A B x) = (term821 A B x).
Proof. exact (MK_COMB (@lem7681305 A B) (@lem7681304 A B x)). Qed.
Lemma lem7681307 {A B : Type'} : (term822 A B) = (term823 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681306 A B x)). Qed.
Lemma lem7681308 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681309 {A B : Type'} : (term814 A B) = (term824 A B).
Proof. exact (MK_COMB (@lem7681308 A B) (@lem7681307 A B)). Qed.
Lemma lem7681310 {A B : Type'} : ((term813 A B) = (term814 A B)) = ((term812 A B) = (term824 A B)).
Proof. exact (MK_COMB (@lem7681303 A B) (@lem7681309 A B)). Qed.
Lemma lem7681311 {A B : Type'} : (term812 A B) = (term824 A B).
Proof. exact (EQ_MP (@lem7681310 A B) (@lem7681295 A B)). Qed.
Lemma lem7681312 {A B : Type'} : (term552 A B) = (term824 A B).
Proof. exact (TRANS (@lem7681291 A B) (@lem7681311 A B)). Qed.
Lemma lem7681313 {A B : Type'} : (term553 A B) = (term825 A B).
Proof. exact (MK_COMB (@lem7681265 A B) (@lem7681312 A B)). Qed.
Lemma lem7681315 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term634 A P Q) = (term635 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7681316 {A B : Type'} (P : type31 A B) (Q : type31 A B) : (term636 A B P Q) = (term637 A B P Q).
Proof. exact (@lem7681315 (finite_diff A B) P Q). Qed.
Lemma lem7681317 {A B : Type'} : (term826 A B) = (term827 A B).
Proof. exact (@lem7681316 A B (term800 A B) (term823 A B)). Qed.
Lemma lem7681318 {A B : Type'} (x : finite_diff A B) : (term828 A B x) = (term798 A B x).
Proof. exact (eq_refl (term828 A B x)). Qed.
Lemma lem7681319 {A B : Type'} : (term829 A B) = (term800 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681318 A B x)). Qed.
Lemma lem7681320 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681321 {A B : Type'} : (term830 A B) = (term801 A B).
Proof. exact (MK_COMB (@lem7681320 A B) (@lem7681319 A B)). Qed.
Lemma lem7681322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681323 {A B : Type'} : (term831 A B) = (term802 A B).
Proof. exact (MK_COMB (@lem7681322) (@lem7681321 A B)). Qed.
Lemma lem7681324 {A B : Type'} (x : finite_diff A B) : (term832 A B x) = (term821 A B x).
Proof. exact (eq_refl (term832 A B x)). Qed.
Lemma lem7681325 {A B : Type'} : (term833 A B) = (term823 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681324 A B x)). Qed.
Lemma lem7681326 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681327 {A B : Type'} : (term834 A B) = (term824 A B).
Proof. exact (MK_COMB (@lem7681326 A B) (@lem7681325 A B)). Qed.
Lemma lem7681328 {A B : Type'} : (term826 A B) = (term825 A B).
Proof. exact (MK_COMB (@lem7681323 A B) (@lem7681327 A B)). Qed.
Lemma lem7681329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681330 {A B : Type'} : (term835 A B) = (term836 A B).
Proof. exact (MK_COMB (@lem7681329) (@lem7681328 A B)). Qed.
Lemma lem7681331 {A B : Type'} (x : finite_diff A B) : (term828 A B x) = (term798 A B x).
Proof. exact (eq_refl (term828 A B x)). Qed.
Lemma lem7681332 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681333 {A B : Type'} (x : finite_diff A B) : (term837 A B x) = (term838 A B x).
Proof. exact (MK_COMB (@lem7681332) (@lem7681331 A B x)). Qed.
Lemma lem7681334 {A B : Type'} (x : finite_diff A B) : (term832 A B x) = (term821 A B x).
Proof. exact (eq_refl (term832 A B x)). Qed.
Lemma lem7681335 {A B : Type'} (x : finite_diff A B) : (term839 A B x) = (term840 A B x).
Proof. exact (MK_COMB (@lem7681333 A B x) (@lem7681334 A B x)). Qed.
Lemma lem7681336 {A B : Type'} : (term841 A B) = (term842 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681335 A B x)). Qed.
Lemma lem7681337 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681338 {A B : Type'} : (term827 A B) = (term843 A B).
Proof. exact (MK_COMB (@lem7681337 A B) (@lem7681336 A B)). Qed.
Lemma lem7681339 {A B : Type'} : ((term826 A B) = (term827 A B)) = ((term825 A B) = (term843 A B)).
Proof. exact (MK_COMB (@lem7681330 A B) (@lem7681338 A B)). Qed.
Lemma lem7681340 {A B : Type'} : (term825 A B) = (term843 A B).
Proof. exact (EQ_MP (@lem7681339 A B) (@lem7681317 A B)). Qed.
Lemma lem7681341 {A B : Type'} : (term553 A B) = (term843 A B).
Proof. exact (TRANS (@lem7681313 A B) (@lem7681340 A B)). Qed.
Lemma lem7681342 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (eq_refl (term299 A)). Qed.
Lemma lem7681343 {A B : Type'} : (term554 A B) = (term844 A B).
Proof. exact (MK_COMB (@lem7681342 A) (@lem7681341 A B)). Qed.
Lemma lem7681345 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7681346 {A B : Type'} (P : Prop) (Q : type31 A B) : (term590 A B P Q) = (term591 A B P Q).
Proof. exact (@lem7681345 (finite_diff A B) P Q). Qed.
Lemma lem7681347 {A B : Type'} : (term845 A B) = (term846 A B).
Proof. exact (@lem7681346 A B (term83 A) (term842 A B)). Qed.
Lemma lem7681348 {A B : Type'} (x : finite_diff A B) : (term847 A B x) = (term840 A B x).
Proof. exact (eq_refl (term847 A B x)). Qed.
Lemma lem7681349 {A B : Type'} : (term848 A B) = (term842 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681348 A B x)). Qed.
Lemma lem7681350 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681351 {A B : Type'} : (term849 A B) = (term843 A B).
Proof. exact (MK_COMB (@lem7681350 A B) (@lem7681349 A B)). Qed.
Lemma lem7681352 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (eq_refl (term299 A)). Qed.
Lemma lem7681353 {A B : Type'} : (term845 A B) = (term844 A B).
Proof. exact (MK_COMB (@lem7681352 A) (@lem7681351 A B)). Qed.
Lemma lem7681354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681355 {A B : Type'} : (term850 A B) = (term851 A B).
Proof. exact (MK_COMB (@lem7681354) (@lem7681353 A B)). Qed.
Lemma lem7681356 {A B : Type'} (x : finite_diff A B) : (term847 A B x) = (term840 A B x).
Proof. exact (eq_refl (term847 A B x)). Qed.
Lemma lem7681357 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (eq_refl (term299 A)). Qed.
Lemma lem7681358 {A B : Type'} (x : finite_diff A B) : (term852 A B x) = (term853 A B x).
Proof. exact (MK_COMB (@lem7681357 A) (@lem7681356 A B x)). Qed.
Lemma lem7681359 {A B : Type'} : (term854 A B) = (term855 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681358 A B x)). Qed.
Lemma lem7681360 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681361 {A B : Type'} : (term846 A B) = (term856 A B).
Proof. exact (MK_COMB (@lem7681360 A B) (@lem7681359 A B)). Qed.
Lemma lem7681362 {A B : Type'} : ((term845 A B) = (term846 A B)) = ((term844 A B) = (term856 A B)).
Proof. exact (MK_COMB (@lem7681355 A B) (@lem7681361 A B)). Qed.
Lemma lem7681363 {A B : Type'} : (term844 A B) = (term856 A B).
Proof. exact (EQ_MP (@lem7681362 A B) (@lem7681347 A B)). Qed.
Lemma lem7681364 {A B : Type'} : (term554 A B) = (term856 A B).
Proof. exact (TRANS (@lem7681343 A B) (@lem7681363 A B)). Qed.
Lemma lem7681365 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681366 {A B : Type'} : (term555 A B) = (term857 A B).
Proof. exact (MK_COMB (@lem7681365) (@lem7681364 A B)). Qed.
Lemma lem7681368 {A : Type'} (P : A -> Prop) (Q : Prop) : (term568 A P Q) = (term569 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7681369 {A B : Type'} (P : type31 A B) (Q : Prop) : (term570 A B P Q) = (term571 A B P Q).
Proof. exact (@lem7681368 (finite_diff A B) P Q). Qed.
Lemma lem7681370 {A B : Type'} : (term858 A B) = (term859 A B).
Proof. exact (@lem7681369 A B (term225 A B) (term556 A B)). Qed.
Lemma lem7681371 {A B : Type'} (x : finite_diff A B) : (term574 A B x) = (term218 A B x).
Proof. exact (eq_refl (term574 A B x)). Qed.
Lemma lem7681372 {A B : Type'} : (term575 A B) = (term225 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681371 A B x)). Qed.
Lemma lem7681373 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681374 {A B : Type'} : (term576 A B) = (term226 A B).
Proof. exact (MK_COMB (@lem7681373 A B) (@lem7681372 A B)). Qed.
Lemma lem7681375 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681376 {A B : Type'} : (term577 A B) = (term247 A B).
Proof. exact (MK_COMB (@lem7681375) (@lem7681374 A B)). Qed.
Lemma lem7681377 {A B : Type'} : (term556 A B) = (term556 A B).
Proof. exact (eq_refl (term556 A B)). Qed.
Lemma lem7681378 {A B : Type'} : (term858 A B) = (term557 A B).
Proof. exact (MK_COMB (@lem7681376 A B) (@lem7681377 A B)). Qed.
Lemma lem7681379 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681380 {A B : Type'} : (term860 A B) = (term861 A B).
Proof. exact (MK_COMB (@lem7681379) (@lem7681378 A B)). Qed.
Lemma lem7681381 {A B : Type'} (x : finite_diff A B) : (term574 A B x) = (term218 A B x).
Proof. exact (eq_refl (term574 A B x)). Qed.
Lemma lem7681382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681383 {A B : Type'} (x : finite_diff A B) : (term580 A B x) = (term581 A B x).
Proof. exact (MK_COMB (@lem7681382) (@lem7681381 A B x)). Qed.
Lemma lem7681384 {A B : Type'} : (term556 A B) = (term556 A B).
Proof. exact (eq_refl (term556 A B)). Qed.
Lemma lem7681385 {A B : Type'} (x : finite_diff A B) : (term862 A B x) = (term863 A B x).
Proof. exact (MK_COMB (@lem7681383 A B x) (@lem7681384 A B)). Qed.
Lemma lem7681386 {A B : Type'} : (term864 A B) = (term865 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681385 A B x)). Qed.
Lemma lem7681387 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681388 {A B : Type'} : (term859 A B) = (term866 A B).
Proof. exact (MK_COMB (@lem7681387 A B) (@lem7681386 A B)). Qed.
Lemma lem7681389 {A B : Type'} : ((term858 A B) = (term859 A B)) = ((term557 A B) = (term866 A B)).
Proof. exact (MK_COMB (@lem7681380 A B) (@lem7681388 A B)). Qed.
Lemma lem7681390 {A B : Type'} : (term557 A B) = (term866 A B).
Proof. exact (EQ_MP (@lem7681389 A B) (@lem7681370 A B)). Qed.
Lemma lem7681391 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7681392 {A B : Type'} : (term558 A B) = (term867 A B).
Proof. exact (MK_COMB (@lem7681391 A B) (@lem7681390 A B)). Qed.
Lemma lem7681394 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7681395 {A B : Type'} (P : Prop) (Q : type31 A B) : (term590 A B P Q) = (term591 A B P Q).
Proof. exact (@lem7681394 (finite_diff A B) P Q). Qed.
Lemma lem7681396 {A B : Type'} : (term868 A B) = (term869 A B).
Proof. exact (@lem7681395 A B (term20 A B) (term865 A B)). Qed.
Lemma lem7681397 {A B : Type'} (x : finite_diff A B) : (term870 A B x) = (term863 A B x).
Proof. exact (eq_refl (term870 A B x)). Qed.
Lemma lem7681398 {A B : Type'} : (term871 A B) = (term865 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681397 A B x)). Qed.
Lemma lem7681399 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681400 {A B : Type'} : (term872 A B) = (term866 A B).
Proof. exact (MK_COMB (@lem7681399 A B) (@lem7681398 A B)). Qed.
Lemma lem7681401 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7681402 {A B : Type'} : (term868 A B) = (term867 A B).
Proof. exact (MK_COMB (@lem7681401 A B) (@lem7681400 A B)). Qed.
Lemma lem7681403 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681404 {A B : Type'} : (term873 A B) = (term874 A B).
Proof. exact (MK_COMB (@lem7681403) (@lem7681402 A B)). Qed.
Lemma lem7681405 {A B : Type'} (x : finite_diff A B) : (term870 A B x) = (term863 A B x).
Proof. exact (eq_refl (term870 A B x)). Qed.
Lemma lem7681406 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7681407 {A B : Type'} (x : finite_diff A B) : (term875 A B x) = (term876 A B x).
Proof. exact (MK_COMB (@lem7681406 A B) (@lem7681405 A B x)). Qed.
Lemma lem7681408 {A B : Type'} : (term877 A B) = (term878 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681407 A B x)). Qed.
Lemma lem7681409 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681410 {A B : Type'} : (term869 A B) = (term879 A B).
Proof. exact (MK_COMB (@lem7681409 A B) (@lem7681408 A B)). Qed.
Lemma lem7681411 {A B : Type'} : ((term868 A B) = (term869 A B)) = ((term867 A B) = (term879 A B)).
Proof. exact (MK_COMB (@lem7681404 A B) (@lem7681410 A B)). Qed.
Lemma lem7681412 {A B : Type'} : (term867 A B) = (term879 A B).
Proof. exact (EQ_MP (@lem7681411 A B) (@lem7681396 A B)). Qed.
Lemma lem7681413 {A B : Type'} : (term558 A B) = (term879 A B).
Proof. exact (TRANS (@lem7681392 A B) (@lem7681412 A B)). Qed.
Lemma lem7681414 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681415 {A B : Type'} : (term559 A B) = (term880 A B).
Proof. exact (MK_COMB (@lem7681414) (@lem7681413 A B)). Qed.
Lemma lem7681417 {A : Type'} (P : A -> Prop) (Q : Prop) : (term568 A P Q) = (term569 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7681418 {A B : Type'} (P : type31 A B) (Q : Prop) : (term570 A B P Q) = (term571 A B P Q).
Proof. exact (@lem7681417 (finite_diff A B) P Q). Qed.
Lemma lem7681419 {A B : Type'} : (term881 A B) = (term882 A B).
Proof. exact (@lem7681418 A B (term270 A B) (term560 A B)). Qed.
Lemma lem7681420 {A B : Type'} (x : finite_diff A B) : (term607 A B x) = (term265 A B x).
Proof. exact (eq_refl (term607 A B x)). Qed.
Lemma lem7681421 {A B : Type'} : (term608 A B) = (term270 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681420 A B x)). Qed.
Lemma lem7681422 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681423 {A B : Type'} : (term609 A B) = (term271 A B).
Proof. exact (MK_COMB (@lem7681422 A B) (@lem7681421 A B)). Qed.
Lemma lem7681424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681425 {A B : Type'} : (term610 A B) = (term285 A B).
Proof. exact (MK_COMB (@lem7681424) (@lem7681423 A B)). Qed.
Lemma lem7681426 {A B : Type'} : (term560 A B) = (term560 A B).
Proof. exact (eq_refl (term560 A B)). Qed.
Lemma lem7681427 {A B : Type'} : (term881 A B) = (term561 A B).
Proof. exact (MK_COMB (@lem7681425 A B) (@lem7681426 A B)). Qed.
Lemma lem7681428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681429 {A B : Type'} : (term883 A B) = (term884 A B).
Proof. exact (MK_COMB (@lem7681428) (@lem7681427 A B)). Qed.
Lemma lem7681430 {A B : Type'} (x : finite_diff A B) : (term607 A B x) = (term265 A B x).
Proof. exact (eq_refl (term607 A B x)). Qed.
Lemma lem7681431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681432 {A B : Type'} (x : finite_diff A B) : (term613 A B x) = (term614 A B x).
Proof. exact (MK_COMB (@lem7681431) (@lem7681430 A B x)). Qed.
Lemma lem7681433 {A B : Type'} : (term560 A B) = (term560 A B).
Proof. exact (eq_refl (term560 A B)). Qed.
Lemma lem7681434 {A B : Type'} (x : finite_diff A B) : (term885 A B x) = (term886 A B x).
Proof. exact (MK_COMB (@lem7681432 A B x) (@lem7681433 A B)). Qed.
Lemma lem7681435 {A B : Type'} : (term887 A B) = (term888 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681434 A B x)). Qed.
Lemma lem7681436 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681437 {A B : Type'} : (term882 A B) = (term889 A B).
Proof. exact (MK_COMB (@lem7681436 A B) (@lem7681435 A B)). Qed.
Lemma lem7681438 {A B : Type'} : ((term881 A B) = (term882 A B)) = ((term561 A B) = (term889 A B)).
Proof. exact (MK_COMB (@lem7681429 A B) (@lem7681437 A B)). Qed.
Lemma lem7681439 {A B : Type'} : (term561 A B) = (term889 A B).
Proof. exact (EQ_MP (@lem7681438 A B) (@lem7681419 A B)). Qed.
Lemma lem7681440 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7681441 {A B : Type'} : (term562 A B) = (term890 A B).
Proof. exact (MK_COMB (@lem7681440 A B) (@lem7681439 A B)). Qed.
Lemma lem7681443 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7681444 {A B : Type'} (P : Prop) (Q : type31 A B) : (term590 A B P Q) = (term591 A B P Q).
Proof. exact (@lem7681443 (finite_diff A B) P Q). Qed.
Lemma lem7681445 {A B : Type'} : (term891 A B) = (term892 A B).
Proof. exact (@lem7681444 A B (term256 A B) (term888 A B)). Qed.
Lemma lem7681446 {A B : Type'} (x : finite_diff A B) : (term893 A B x) = (term886 A B x).
Proof. exact (eq_refl (term893 A B x)). Qed.
Lemma lem7681447 {A B : Type'} : (term894 A B) = (term888 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681446 A B x)). Qed.
Lemma lem7681448 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681449 {A B : Type'} : (term895 A B) = (term889 A B).
Proof. exact (MK_COMB (@lem7681448 A B) (@lem7681447 A B)). Qed.
Lemma lem7681450 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7681451 {A B : Type'} : (term891 A B) = (term890 A B).
Proof. exact (MK_COMB (@lem7681450 A B) (@lem7681449 A B)). Qed.
Lemma lem7681452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681453 {A B : Type'} : (term896 A B) = (term897 A B).
Proof. exact (MK_COMB (@lem7681452) (@lem7681451 A B)). Qed.
Lemma lem7681454 {A B : Type'} (x : finite_diff A B) : (term893 A B x) = (term886 A B x).
Proof. exact (eq_refl (term893 A B x)). Qed.
Lemma lem7681455 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7681456 {A B : Type'} (x : finite_diff A B) : (term898 A B x) = (term899 A B x).
Proof. exact (MK_COMB (@lem7681455 A B) (@lem7681454 A B x)). Qed.
Lemma lem7681457 {A B : Type'} : (term900 A B) = (term901 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681456 A B x)). Qed.
Lemma lem7681458 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681459 {A B : Type'} : (term892 A B) = (term902 A B).
Proof. exact (MK_COMB (@lem7681458 A B) (@lem7681457 A B)). Qed.
Lemma lem7681460 {A B : Type'} : ((term891 A B) = (term892 A B)) = ((term890 A B) = (term902 A B)).
Proof. exact (MK_COMB (@lem7681453 A B) (@lem7681459 A B)). Qed.
Lemma lem7681461 {A B : Type'} : (term890 A B) = (term902 A B).
Proof. exact (EQ_MP (@lem7681460 A B) (@lem7681445 A B)). Qed.
Lemma lem7681462 {A B : Type'} : (term562 A B) = (term902 A B).
Proof. exact (TRANS (@lem7681441 A B) (@lem7681461 A B)). Qed.
Lemma lem7681463 {A B : Type'} : (term563 A B) = (term903 A B).
Proof. exact (MK_COMB (@lem7681415 A B) (@lem7681462 A B)). Qed.
Lemma lem7681465 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term634 A P Q) = (term635 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7681466 {A B : Type'} (P : type31 A B) (Q : type31 A B) : (term636 A B P Q) = (term637 A B P Q).
Proof. exact (@lem7681465 (finite_diff A B) P Q). Qed.
Lemma lem7681467 {A B : Type'} : (term904 A B) = (term905 A B).
Proof. exact (@lem7681466 A B (term878 A B) (term901 A B)). Qed.
Lemma lem7681468 {A B : Type'} (x : finite_diff A B) : (term906 A B x) = (term876 A B x).
Proof. exact (eq_refl (term906 A B x)). Qed.
Lemma lem7681469 {A B : Type'} : (term907 A B) = (term878 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681468 A B x)). Qed.
Lemma lem7681470 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681471 {A B : Type'} : (term908 A B) = (term879 A B).
Proof. exact (MK_COMB (@lem7681470 A B) (@lem7681469 A B)). Qed.
Lemma lem7681472 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681473 {A B : Type'} : (term909 A B) = (term880 A B).
Proof. exact (MK_COMB (@lem7681472) (@lem7681471 A B)). Qed.
Lemma lem7681474 {A B : Type'} (x : finite_diff A B) : (term910 A B x) = (term899 A B x).
Proof. exact (eq_refl (term910 A B x)). Qed.
Lemma lem7681475 {A B : Type'} : (term911 A B) = (term901 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681474 A B x)). Qed.
Lemma lem7681476 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681477 {A B : Type'} : (term912 A B) = (term902 A B).
Proof. exact (MK_COMB (@lem7681476 A B) (@lem7681475 A B)). Qed.
Lemma lem7681478 {A B : Type'} : (term904 A B) = (term903 A B).
Proof. exact (MK_COMB (@lem7681473 A B) (@lem7681477 A B)). Qed.
Lemma lem7681479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681480 {A B : Type'} : (term913 A B) = (term914 A B).
Proof. exact (MK_COMB (@lem7681479) (@lem7681478 A B)). Qed.
Lemma lem7681481 {A B : Type'} (x : finite_diff A B) : (term906 A B x) = (term876 A B x).
Proof. exact (eq_refl (term906 A B x)). Qed.
Lemma lem7681482 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681483 {A B : Type'} (x : finite_diff A B) : (term915 A B x) = (term916 A B x).
Proof. exact (MK_COMB (@lem7681482) (@lem7681481 A B x)). Qed.
Lemma lem7681484 {A B : Type'} (x : finite_diff A B) : (term910 A B x) = (term899 A B x).
Proof. exact (eq_refl (term910 A B x)). Qed.
Lemma lem7681485 {A B : Type'} (x : finite_diff A B) : (term917 A B x) = (term918 A B x).
Proof. exact (MK_COMB (@lem7681483 A B x) (@lem7681484 A B x)). Qed.
Lemma lem7681486 {A B : Type'} : (term919 A B) = (term920 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681485 A B x)). Qed.
Lemma lem7681487 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681488 {A B : Type'} : (term905 A B) = (term921 A B).
Proof. exact (MK_COMB (@lem7681487 A B) (@lem7681486 A B)). Qed.
Lemma lem7681489 {A B : Type'} : ((term904 A B) = (term905 A B)) = ((term903 A B) = (term921 A B)).
Proof. exact (MK_COMB (@lem7681480 A B) (@lem7681488 A B)). Qed.
Lemma lem7681490 {A B : Type'} : (term903 A B) = (term921 A B).
Proof. exact (EQ_MP (@lem7681489 A B) (@lem7681467 A B)). Qed.
Lemma lem7681491 {A B : Type'} : (term563 A B) = (term921 A B).
Proof. exact (TRANS (@lem7681463 A B) (@lem7681490 A B)). Qed.
Lemma lem7681492 {A : Type'} : (term333 A) = (term333 A).
Proof. exact (eq_refl (term333 A)). Qed.
Lemma lem7681493 {A B : Type'} : (term564 A B) = (term922 A B).
Proof. exact (MK_COMB (@lem7681492 A) (@lem7681491 A B)). Qed.
Lemma lem7681495 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7681496 {A B : Type'} (P : Prop) (Q : type31 A B) : (term590 A B P Q) = (term591 A B P Q).
Proof. exact (@lem7681495 (finite_diff A B) P Q). Qed.
Lemma lem7681497 {A B : Type'} : (term923 A B) = (term924 A B).
Proof. exact (@lem7681496 A B (term303 A) (term920 A B)). Qed.
Lemma lem7681498 {A B : Type'} (x : finite_diff A B) : (term925 A B x) = (term918 A B x).
Proof. exact (eq_refl (term925 A B x)). Qed.
Lemma lem7681499 {A B : Type'} : (term926 A B) = (term920 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681498 A B x)). Qed.
Lemma lem7681500 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681501 {A B : Type'} : (term927 A B) = (term921 A B).
Proof. exact (MK_COMB (@lem7681500 A B) (@lem7681499 A B)). Qed.
Lemma lem7681502 {A : Type'} : (term333 A) = (term333 A).
Proof. exact (eq_refl (term333 A)). Qed.
Lemma lem7681503 {A B : Type'} : (term923 A B) = (term922 A B).
Proof. exact (MK_COMB (@lem7681502 A) (@lem7681501 A B)). Qed.
Lemma lem7681504 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681505 {A B : Type'} : (term928 A B) = (term929 A B).
Proof. exact (MK_COMB (@lem7681504) (@lem7681503 A B)). Qed.
Lemma lem7681506 {A B : Type'} (x : finite_diff A B) : (term925 A B x) = (term918 A B x).
Proof. exact (eq_refl (term925 A B x)). Qed.
Lemma lem7681507 {A : Type'} : (term333 A) = (term333 A).
Proof. exact (eq_refl (term333 A)). Qed.
Lemma lem7681508 {A B : Type'} (x : finite_diff A B) : (term930 A B x) = (term931 A B x).
Proof. exact (MK_COMB (@lem7681507 A) (@lem7681506 A B x)). Qed.
Lemma lem7681509 {A B : Type'} : (term932 A B) = (term933 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681508 A B x)). Qed.
Lemma lem7681510 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681511 {A B : Type'} : (term924 A B) = (term934 A B).
Proof. exact (MK_COMB (@lem7681510 A B) (@lem7681509 A B)). Qed.
Lemma lem7681512 {A B : Type'} : ((term923 A B) = (term924 A B)) = ((term922 A B) = (term934 A B)).
Proof. exact (MK_COMB (@lem7681505 A B) (@lem7681511 A B)). Qed.
Lemma lem7681513 {A B : Type'} : (term922 A B) = (term934 A B).
Proof. exact (EQ_MP (@lem7681512 A B) (@lem7681497 A B)). Qed.
Lemma lem7681514 {A B : Type'} : (term564 A B) = (term934 A B).
Proof. exact (TRANS (@lem7681493 A B) (@lem7681513 A B)). Qed.
Lemma lem7681515 {A B : Type'} : (term565 A B) = (term935 A B).
Proof. exact (MK_COMB (@lem7681366 A B) (@lem7681514 A B)). Qed.
Lemma lem7681517 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term634 A P Q) = (term635 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7681518 {A B : Type'} (P : type31 A B) (Q : type31 A B) : (term636 A B P Q) = (term637 A B P Q).
Proof. exact (@lem7681517 (finite_diff A B) P Q). Qed.
Lemma lem7681519 {A B : Type'} : (term936 A B) = (term937 A B).
Proof. exact (@lem7681518 A B (term855 A B) (term933 A B)). Qed.
Lemma lem7681520 {A B : Type'} (x : finite_diff A B) : (term938 A B x) = (term853 A B x).
Proof. exact (eq_refl (term938 A B x)). Qed.
Lemma lem7681521 {A B : Type'} : (term939 A B) = (term855 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681520 A B x)). Qed.
Lemma lem7681522 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681523 {A B : Type'} : (term940 A B) = (term856 A B).
Proof. exact (MK_COMB (@lem7681522 A B) (@lem7681521 A B)). Qed.
Lemma lem7681524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681525 {A B : Type'} : (term941 A B) = (term857 A B).
Proof. exact (MK_COMB (@lem7681524) (@lem7681523 A B)). Qed.
Lemma lem7681526 {A B : Type'} (x : finite_diff A B) : (term942 A B x) = (term931 A B x).
Proof. exact (eq_refl (term942 A B x)). Qed.
Lemma lem7681527 {A B : Type'} : (term943 A B) = (term933 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681526 A B x)). Qed.
Lemma lem7681528 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681529 {A B : Type'} : (term944 A B) = (term934 A B).
Proof. exact (MK_COMB (@lem7681528 A B) (@lem7681527 A B)). Qed.
Lemma lem7681530 {A B : Type'} : (term936 A B) = (term935 A B).
Proof. exact (MK_COMB (@lem7681525 A B) (@lem7681529 A B)). Qed.
Lemma lem7681531 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681532 {A B : Type'} : (term945 A B) = (term946 A B).
Proof. exact (MK_COMB (@lem7681531) (@lem7681530 A B)). Qed.
Lemma lem7681533 {A B : Type'} (x : finite_diff A B) : (term938 A B x) = (term853 A B x).
Proof. exact (eq_refl (term938 A B x)). Qed.
Lemma lem7681534 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681535 {A B : Type'} (x : finite_diff A B) : (term947 A B x) = (term948 A B x).
Proof. exact (MK_COMB (@lem7681534) (@lem7681533 A B x)). Qed.
Lemma lem7681536 {A B : Type'} (x : finite_diff A B) : (term942 A B x) = (term931 A B x).
Proof. exact (eq_refl (term942 A B x)). Qed.
Lemma lem7681537 {A B : Type'} (x : finite_diff A B) : (term949 A B x) = (term950 A B x).
Proof. exact (MK_COMB (@lem7681535 A B x) (@lem7681536 A B x)). Qed.
Lemma lem7681538 {A B : Type'} : (term951 A B) = (term952 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681537 A B x)). Qed.
Lemma lem7681539 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681540 {A B : Type'} : (term937 A B) = (term953 A B).
Proof. exact (MK_COMB (@lem7681539 A B) (@lem7681538 A B)). Qed.
Lemma lem7681541 {A B : Type'} : ((term936 A B) = (term937 A B)) = ((term935 A B) = (term953 A B)).
Proof. exact (MK_COMB (@lem7681532 A B) (@lem7681540 A B)). Qed.
Lemma lem7681542 {A B : Type'} : (term935 A B) = (term953 A B).
Proof. exact (EQ_MP (@lem7681541 A B) (@lem7681519 A B)). Qed.
Lemma lem7681543 {A B : Type'} : (term565 A B) = (term953 A B).
Proof. exact (TRANS (@lem7681515 A B) (@lem7681542 A B)). Qed.
Lemma lem7681544 {B : Type'} : (term333 B) = (term333 B).
Proof. exact (eq_refl (term333 B)). Qed.
Lemma lem7681545 {A B : Type'} : (term566 A B) = (term954 A B).
Proof. exact (MK_COMB (@lem7681544 B) (@lem7681543 A B)). Qed.
Lemma lem7681547 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7681548 {A B : Type'} (P : Prop) (Q : type31 A B) : (term590 A B P Q) = (term591 A B P Q).
Proof. exact (@lem7681547 (finite_diff A B) P Q). Qed.
Lemma lem7681549 {A B : Type'} : (term955 A B) = (term956 A B).
Proof. exact (@lem7681548 A B (term303 B) (term952 A B)). Qed.
Lemma lem7681550 {A B : Type'} (x : finite_diff A B) : (term957 A B x) = (term950 A B x).
Proof. exact (eq_refl (term957 A B x)). Qed.
Lemma lem7681551 {A B : Type'} : (term958 A B) = (term952 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681550 A B x)). Qed.
Lemma lem7681552 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681553 {A B : Type'} : (term959 A B) = (term953 A B).
Proof. exact (MK_COMB (@lem7681552 A B) (@lem7681551 A B)). Qed.
Lemma lem7681554 {B : Type'} : (term333 B) = (term333 B).
Proof. exact (eq_refl (term333 B)). Qed.
Lemma lem7681555 {A B : Type'} : (term955 A B) = (term954 A B).
Proof. exact (MK_COMB (@lem7681554 B) (@lem7681553 A B)). Qed.
Lemma lem7681556 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681557 {A B : Type'} : (term960 A B) = (term961 A B).
Proof. exact (MK_COMB (@lem7681556) (@lem7681555 A B)). Qed.
Lemma lem7681558 {A B : Type'} (x : finite_diff A B) : (term957 A B x) = (term950 A B x).
Proof. exact (eq_refl (term957 A B x)). Qed.
Lemma lem7681559 {B : Type'} : (term333 B) = (term333 B).
Proof. exact (eq_refl (term333 B)). Qed.
Lemma lem7681560 {A B : Type'} (x : finite_diff A B) : (term962 A B x) = (term963 A B x).
Proof. exact (MK_COMB (@lem7681559 B) (@lem7681558 A B x)). Qed.
Lemma lem7681561 {A B : Type'} : (term964 A B) = (term965 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681560 A B x)). Qed.
Lemma lem7681562 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681563 {A B : Type'} : (term956 A B) = (term966 A B).
Proof. exact (MK_COMB (@lem7681562 A B) (@lem7681561 A B)). Qed.
Lemma lem7681564 {A B : Type'} : ((term955 A B) = (term956 A B)) = ((term954 A B) = (term966 A B)).
Proof. exact (MK_COMB (@lem7681557 A B) (@lem7681563 A B)). Qed.
Lemma lem7681565 {A B : Type'} : (term954 A B) = (term966 A B).
Proof. exact (EQ_MP (@lem7681564 A B) (@lem7681549 A B)). Qed.
Lemma lem7681566 {A B : Type'} : (term566 A B) = (term966 A B).
Proof. exact (TRANS (@lem7681545 A B) (@lem7681565 A B)). Qed.
Lemma lem7681567 {A B : Type'} : (term567 A B) = (term967 A B).
Proof. exact (MK_COMB (@lem7681216 A B) (@lem7681566 A B)). Qed.
Lemma lem7681569 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term634 A P Q) = (term635 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7681570 {A B : Type'} (P : type31 A B) (Q : type31 A B) : (term636 A B P Q) = (term637 A B P Q).
Proof. exact (@lem7681569 (finite_diff A B) P Q). Qed.
Lemma lem7681571 {A B : Type'} : (term968 A B) = (term969 A B).
Proof. exact (@lem7681570 A B (term777 A B) (term965 A B)). Qed.
Lemma lem7681572 {A B : Type'} (x : finite_diff A B) : (term970 A B x) = (term775 A B x).
Proof. exact (eq_refl (term970 A B x)). Qed.
Lemma lem7681573 {A B : Type'} : (term971 A B) = (term777 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681572 A B x)). Qed.
Lemma lem7681574 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681575 {A B : Type'} : (term972 A B) = (term778 A B).
Proof. exact (MK_COMB (@lem7681574 A B) (@lem7681573 A B)). Qed.
Lemma lem7681576 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681577 {A B : Type'} : (term973 A B) = (term779 A B).
Proof. exact (MK_COMB (@lem7681576) (@lem7681575 A B)). Qed.
Lemma lem7681578 {A B : Type'} (x : finite_diff A B) : (term974 A B x) = (term963 A B x).
Proof. exact (eq_refl (term974 A B x)). Qed.
Lemma lem7681579 {A B : Type'} : (term975 A B) = (term965 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681578 A B x)). Qed.
Lemma lem7681580 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681581 {A B : Type'} : (term976 A B) = (term966 A B).
Proof. exact (MK_COMB (@lem7681580 A B) (@lem7681579 A B)). Qed.
Lemma lem7681582 {A B : Type'} : (term968 A B) = (term967 A B).
Proof. exact (MK_COMB (@lem7681577 A B) (@lem7681581 A B)). Qed.
Lemma lem7681583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7681584 {A B : Type'} : (term977 A B) = (term978 A B).
Proof. exact (MK_COMB (@lem7681583) (@lem7681582 A B)). Qed.
Lemma lem7681585 {A B : Type'} (x : finite_diff A B) : (term970 A B x) = (term775 A B x).
Proof. exact (eq_refl (term970 A B x)). Qed.
Lemma lem7681586 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7681587 {A B : Type'} (x : finite_diff A B) : (term979 A B x) = (term980 A B x).
Proof. exact (MK_COMB (@lem7681586) (@lem7681585 A B x)). Qed.
Lemma lem7681588 {A B : Type'} (x : finite_diff A B) : (term974 A B x) = (term963 A B x).
Proof. exact (eq_refl (term974 A B x)). Qed.
Lemma lem7681589 {A B : Type'} (x : finite_diff A B) : (term981 A B x) = (term982 A B x).
Proof. exact (MK_COMB (@lem7681587 A B x) (@lem7681588 A B x)). Qed.
Lemma lem7681590 {A B : Type'} : (term983 A B) = (term984 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7681589 A B x)). Qed.
Lemma lem7681591 {A B : Type'} : (@ex (finite_diff A B)) = (@ex (finite_diff A B)).
Proof. exact (eq_refl (@ex (finite_diff A B))). Qed.
Lemma lem7681592 {A B : Type'} : (term969 A B) = (term985 A B).
Proof. exact (MK_COMB (@lem7681591 A B) (@lem7681590 A B)). Qed.
Lemma lem7681593 {A B : Type'} : ((term968 A B) = (term969 A B)) = ((term967 A B) = (term985 A B)).
Proof. exact (MK_COMB (@lem7681584 A B) (@lem7681592 A B)). Qed.
Lemma lem7681594 {A B : Type'} : (term967 A B) = (term985 A B).
Proof. exact (EQ_MP (@lem7681593 A B) (@lem7681571 A B)). Qed.
Lemma lem7681595 {A B : Type'} : (term567 A B) = (term985 A B).
Proof. exact (TRANS (@lem7681567 A B) (@lem7681594 A B)). Qed.
Lemma lem7681596 {A B : Type'} : (term415 A B) = (term985 A B).
Proof. exact (TRANS (@lem7680864 A B) (@lem7681595 A B)). Qed.
Lemma lem7681597 {A B : Type'} : (term205 A B) = (term985 A B).
Proof. exact (TRANS (@lem7677239 A B) (@lem7681596 A B)). Qed.
Lemma lem7681598 {A B : Type'} (h1 : term205 A B) : term985 A B.
Proof. exact (EQ_MP (@lem7681597 A B) (@lem7676154 A B h1)). Qed.
Lemma lem7681599 {A B : Type'} (x : finite_diff A B) (h1 : term982 A B x) : term982 A B x.
Proof. exact (h1). Qed.
Lemma lem7681630 {B : Type'} (r : nat) : (term516 B r) = (term516 B r).
Proof. exact (eq_refl (term516 B r)). Qed.
Lemma lem7681631 {B : Type'} : (term510 B) = (term510 B).
Proof. exact (fun_ext (fun r : nat => @lem7681630 B r)). Qed.
Lemma lem7681632 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7681633 {B : Type'} : (term528 B) = (term528 B).
Proof. exact (MK_COMB (@lem7681632) (@lem7681631 B)). Qed.
Lemma lem7681664 {B : Type'} (r : nat) : (term512 B r) = (term512 B r).
Proof. exact (eq_refl (term512 B r)). Qed.
Lemma lem7681665 {B : Type'} : (term509 B) = (term509 B).
Proof. exact (fun_ext (fun r : nat => @lem7681664 B r)). Qed.
Lemma lem7681666 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7681667 {B : Type'} : (term523 B) = (term523 B).
Proof. exact (MK_COMB (@lem7681666) (@lem7681665 B)). Qed.
Lemma lem7681668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681669 {B : Type'} : (term525 B) = (term525 B).
Proof. exact (MK_COMB (@lem7681668) (@lem7681667 B)). Qed.
Lemma lem7681670 {B : Type'} : (term529 B) = (term529 B).
Proof. exact (MK_COMB (@lem7681669 B) (@lem7681633 B)). Qed.
Lemma lem7681679 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7681680 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7681679 B a)). Qed.
Lemma lem7681681 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7681682 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7681681 B) (@lem7681680 B)). Qed.
Lemma lem7681683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681684 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7681683) (@lem7681682 B)). Qed.
Lemma lem7681685 {B : Type'} : (term530 B) = (term530 B).
Proof. exact (MK_COMB (@lem7681684 B) (@lem7681670 B)). Qed.
Lemma lem7681716 {A B : Type'} (r : nat) : (term484 A B r) = (term484 A B r).
Proof. exact (eq_refl (term484 A B r)). Qed.
Lemma lem7681717 {A B : Type'} : (term478 A B) = (term478 A B).
Proof. exact (fun_ext (fun r : nat => @lem7681716 A B r)). Qed.
Lemma lem7681718 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7681719 {A B : Type'} : (term496 A B) = (term496 A B).
Proof. exact (MK_COMB (@lem7681718) (@lem7681717 A B)). Qed.
Lemma lem7681750 {A B : Type'} (r : nat) : (term480 A B r) = (term480 A B r).
Proof. exact (eq_refl (term480 A B r)). Qed.
Lemma lem7681751 {A B : Type'} : (term477 A B) = (term477 A B).
Proof. exact (fun_ext (fun r : nat => @lem7681750 A B r)). Qed.
Lemma lem7681752 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7681753 {A B : Type'} : (term491 A B) = (term491 A B).
Proof. exact (MK_COMB (@lem7681752) (@lem7681751 A B)). Qed.
Lemma lem7681754 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681755 {A B : Type'} : (term493 A B) = (term493 A B).
Proof. exact (MK_COMB (@lem7681754) (@lem7681753 A B)). Qed.
Lemma lem7681756 {A B : Type'} : (term497 A B) = (term497 A B).
Proof. exact (MK_COMB (@lem7681755 A B) (@lem7681719 A B)). Qed.
Lemma lem7681765 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7681766 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7681765 A B a)). Qed.
Lemma lem7681767 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7681768 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7681767 A B) (@lem7681766 A B)). Qed.
Lemma lem7681769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681770 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7681769) (@lem7681768 A B)). Qed.
Lemma lem7681771 {A B : Type'} : (term498 A B) = (term498 A B).
Proof. exact (MK_COMB (@lem7681770 A B) (@lem7681756 A B)). Qed.
Lemma lem7681772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681773 {A B : Type'} : (term499 A B) = (term499 A B).
Proof. exact (MK_COMB (@lem7681772) (@lem7681771 A B)). Qed.
Lemma lem7681774 {A B : Type'} : (term549 A B) = (term549 A B).
Proof. exact (MK_COMB (@lem7681773 A B) (@lem7681685 B)). Qed.
Lemma lem7681805 {A : Type'} (r : nat) : (term516 A r) = (term516 A r).
Proof. exact (eq_refl (term516 A r)). Qed.
Lemma lem7681806 {A : Type'} : (term510 A) = (term510 A).
Proof. exact (fun_ext (fun r : nat => @lem7681805 A r)). Qed.
Lemma lem7681807 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7681808 {A : Type'} : (term528 A) = (term528 A).
Proof. exact (MK_COMB (@lem7681807) (@lem7681806 A)). Qed.
Lemma lem7681839 {A : Type'} (r : nat) : (term512 A r) = (term512 A r).
Proof. exact (eq_refl (term512 A r)). Qed.
Lemma lem7681840 {A : Type'} : (term509 A) = (term509 A).
Proof. exact (fun_ext (fun r : nat => @lem7681839 A r)). Qed.
Lemma lem7681841 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7681842 {A : Type'} : (term523 A) = (term523 A).
Proof. exact (MK_COMB (@lem7681841) (@lem7681840 A)). Qed.
Lemma lem7681843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681844 {A : Type'} : (term525 A) = (term525 A).
Proof. exact (MK_COMB (@lem7681843) (@lem7681842 A)). Qed.
Lemma lem7681845 {A : Type'} : (term529 A) = (term529 A).
Proof. exact (MK_COMB (@lem7681844 A) (@lem7681808 A)). Qed.
Lemma lem7681854 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7681855 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7681854 A a)). Qed.
Lemma lem7681856 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7681857 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7681856 A) (@lem7681855 A)). Qed.
Lemma lem7681858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681859 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7681858) (@lem7681857 A)). Qed.
Lemma lem7681860 {A : Type'} : (term530 A) = (term530 A).
Proof. exact (MK_COMB (@lem7681859 A) (@lem7681845 A)). Qed.
Lemma lem7681861 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681862 {A : Type'} : (term531 A) = (term531 A).
Proof. exact (MK_COMB (@lem7681861) (@lem7681860 A)). Qed.
Lemma lem7681863 {A B : Type'} : (term560 A B) = (term560 A B).
Proof. exact (MK_COMB (@lem7681862 A) (@lem7681774 A B)). Qed.
Lemma lem7681894 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term258 A B x x') = (term258 A B x x').
Proof. exact (eq_refl (term258 A B x x')). Qed.
Lemma lem7681895 {A B : Type'} (x : finite_diff A B) : (term264 A B x) = (term264 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7681894 A B x x')). Qed.
Lemma lem7681896 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7681897 {A B : Type'} (x : finite_diff A B) : (term265 A B x) = (term265 A B x).
Proof. exact (MK_COMB (@lem7681896) (@lem7681895 A B x)). Qed.
Lemma lem7681898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681899 {A B : Type'} (x : finite_diff A B) : (term614 A B x) = (term614 A B x).
Proof. exact (MK_COMB (@lem7681898) (@lem7681897 A B x)). Qed.
Lemma lem7681900 {A B : Type'} (x : finite_diff A B) : (term886 A B x) = (term886 A B x).
Proof. exact (MK_COMB (@lem7681899 A B x) (@lem7681863 A B)). Qed.
Lemma lem7681913 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7681914 {A B : Type'} (x : finite_diff A B) : (term899 A B x) = (term899 A B x).
Proof. exact (MK_COMB (@lem7681913 A B) (@lem7681900 A B x)). Qed.
Lemma lem7681945 {B : Type'} (r : nat) : (term516 B r) = (term516 B r).
Proof. exact (eq_refl (term516 B r)). Qed.
Lemma lem7681946 {B : Type'} : (term510 B) = (term510 B).
Proof. exact (fun_ext (fun r : nat => @lem7681945 B r)). Qed.
Lemma lem7681947 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7681948 {B : Type'} : (term528 B) = (term528 B).
Proof. exact (MK_COMB (@lem7681947) (@lem7681946 B)). Qed.
Lemma lem7681979 {B : Type'} (r : nat) : (term512 B r) = (term512 B r).
Proof. exact (eq_refl (term512 B r)). Qed.
Lemma lem7681980 {B : Type'} : (term509 B) = (term509 B).
Proof. exact (fun_ext (fun r : nat => @lem7681979 B r)). Qed.
Lemma lem7681981 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7681982 {B : Type'} : (term523 B) = (term523 B).
Proof. exact (MK_COMB (@lem7681981) (@lem7681980 B)). Qed.
Lemma lem7681983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681984 {B : Type'} : (term525 B) = (term525 B).
Proof. exact (MK_COMB (@lem7681983) (@lem7681982 B)). Qed.
Lemma lem7681985 {B : Type'} : (term529 B) = (term529 B).
Proof. exact (MK_COMB (@lem7681984 B) (@lem7681948 B)). Qed.
Lemma lem7681994 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7681995 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7681994 B a)). Qed.
Lemma lem7681996 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7681997 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7681996 B) (@lem7681995 B)). Qed.
Lemma lem7681998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7681999 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7681998) (@lem7681997 B)). Qed.
Lemma lem7682000 {B : Type'} : (term530 B) = (term530 B).
Proof. exact (MK_COMB (@lem7681999 B) (@lem7681985 B)). Qed.
Lemma lem7682035 {A B : Type'} (r : nat) : (term454 A B r) = (term454 A B r).
Proof. exact (eq_refl (term454 A B r)). Qed.
Lemma lem7682036 {A B : Type'} : (term448 A B) = (term448 A B).
Proof. exact (fun_ext (fun r : nat => @lem7682035 A B r)). Qed.
Lemma lem7682037 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682038 {A B : Type'} : (term466 A B) = (term466 A B).
Proof. exact (MK_COMB (@lem7682037) (@lem7682036 A B)). Qed.
Lemma lem7682073 {A B : Type'} (r : nat) : (term450 A B r) = (term450 A B r).
Proof. exact (eq_refl (term450 A B r)). Qed.
Lemma lem7682074 {A B : Type'} : (term447 A B) = (term447 A B).
Proof. exact (fun_ext (fun r : nat => @lem7682073 A B r)). Qed.
Lemma lem7682075 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682076 {A B : Type'} : (term461 A B) = (term461 A B).
Proof. exact (MK_COMB (@lem7682075) (@lem7682074 A B)). Qed.
Lemma lem7682077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682078 {A B : Type'} : (term463 A B) = (term463 A B).
Proof. exact (MK_COMB (@lem7682077) (@lem7682076 A B)). Qed.
Lemma lem7682079 {A B : Type'} : (term467 A B) = (term467 A B).
Proof. exact (MK_COMB (@lem7682078 A B) (@lem7682038 A B)). Qed.
Lemma lem7682088 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7682089 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7682088 A B a)). Qed.
Lemma lem7682090 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7682091 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7682090 A B) (@lem7682089 A B)). Qed.
Lemma lem7682092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682093 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7682092) (@lem7682091 A B)). Qed.
Lemma lem7682094 {A B : Type'} : (term468 A B) = (term468 A B).
Proof. exact (MK_COMB (@lem7682093 A B) (@lem7682079 A B)). Qed.
Lemma lem7682095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682096 {A B : Type'} : (term469 A B) = (term469 A B).
Proof. exact (MK_COMB (@lem7682095) (@lem7682094 A B)). Qed.
Lemma lem7682097 {A B : Type'} : (term544 A B) = (term544 A B).
Proof. exact (MK_COMB (@lem7682096 A B) (@lem7682000 B)). Qed.
Lemma lem7682128 {A : Type'} (r : nat) : (term516 A r) = (term516 A r).
Proof. exact (eq_refl (term516 A r)). Qed.
Lemma lem7682129 {A : Type'} : (term510 A) = (term510 A).
Proof. exact (fun_ext (fun r : nat => @lem7682128 A r)). Qed.
Lemma lem7682130 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682131 {A : Type'} : (term528 A) = (term528 A).
Proof. exact (MK_COMB (@lem7682130) (@lem7682129 A)). Qed.
Lemma lem7682162 {A : Type'} (r : nat) : (term512 A r) = (term512 A r).
Proof. exact (eq_refl (term512 A r)). Qed.
Lemma lem7682163 {A : Type'} : (term509 A) = (term509 A).
Proof. exact (fun_ext (fun r : nat => @lem7682162 A r)). Qed.
Lemma lem7682164 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682165 {A : Type'} : (term523 A) = (term523 A).
Proof. exact (MK_COMB (@lem7682164) (@lem7682163 A)). Qed.
Lemma lem7682166 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682167 {A : Type'} : (term525 A) = (term525 A).
Proof. exact (MK_COMB (@lem7682166) (@lem7682165 A)). Qed.
Lemma lem7682168 {A : Type'} : (term529 A) = (term529 A).
Proof. exact (MK_COMB (@lem7682167 A) (@lem7682131 A)). Qed.
Lemma lem7682177 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7682178 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7682177 A a)). Qed.
Lemma lem7682179 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7682180 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7682179 A) (@lem7682178 A)). Qed.
Lemma lem7682181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682182 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7682181) (@lem7682180 A)). Qed.
Lemma lem7682183 {A : Type'} : (term530 A) = (term530 A).
Proof. exact (MK_COMB (@lem7682182 A) (@lem7682168 A)). Qed.
Lemma lem7682184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682185 {A : Type'} : (term531 A) = (term531 A).
Proof. exact (MK_COMB (@lem7682184) (@lem7682183 A)). Qed.
Lemma lem7682186 {A B : Type'} : (term556 A B) = (term556 A B).
Proof. exact (MK_COMB (@lem7682185 A) (@lem7682097 A B)). Qed.
Lemma lem7682221 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term209 A B x x') = (term209 A B x x').
Proof. exact (eq_refl (term209 A B x x')). Qed.
Lemma lem7682222 {A B : Type'} (x : finite_diff A B) : (term217 A B x) = (term217 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7682221 A B x x')). Qed.
Lemma lem7682223 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682224 {A B : Type'} (x : finite_diff A B) : (term218 A B x) = (term218 A B x).
Proof. exact (MK_COMB (@lem7682223) (@lem7682222 A B x)). Qed.
Lemma lem7682225 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682226 {A B : Type'} (x : finite_diff A B) : (term581 A B x) = (term581 A B x).
Proof. exact (MK_COMB (@lem7682225) (@lem7682224 A B x)). Qed.
Lemma lem7682227 {A B : Type'} (x : finite_diff A B) : (term863 A B x) = (term863 A B x).
Proof. exact (MK_COMB (@lem7682226 A B x) (@lem7682186 A B)). Qed.
Lemma lem7682238 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7682239 {A B : Type'} (x : finite_diff A B) : (term876 A B x) = (term876 A B x).
Proof. exact (MK_COMB (@lem7682238 A B) (@lem7682227 A B x)). Qed.
Lemma lem7682240 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7682241 {A B : Type'} (x : finite_diff A B) : (term916 A B x) = (term916 A B x).
Proof. exact (MK_COMB (@lem7682240) (@lem7682239 A B x)). Qed.
Lemma lem7682242 {A B : Type'} (x : finite_diff A B) : (term918 A B x) = (term918 A B x).
Proof. exact (MK_COMB (@lem7682241 A B x) (@lem7681914 A B x)). Qed.
Lemma lem7682255 {A : Type'} : (term333 A) = (term333 A).
Proof. exact (eq_refl (term333 A)). Qed.
Lemma lem7682256 {A B : Type'} (x : finite_diff A B) : (term931 A B x) = (term931 A B x).
Proof. exact (MK_COMB (@lem7682255 A) (@lem7682242 A B x)). Qed.
Lemma lem7682287 {B : Type'} (r : nat) : (term516 B r) = (term516 B r).
Proof. exact (eq_refl (term516 B r)). Qed.
Lemma lem7682288 {B : Type'} : (term510 B) = (term510 B).
Proof. exact (fun_ext (fun r : nat => @lem7682287 B r)). Qed.
Lemma lem7682289 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682290 {B : Type'} : (term528 B) = (term528 B).
Proof. exact (MK_COMB (@lem7682289) (@lem7682288 B)). Qed.
Lemma lem7682321 {B : Type'} (r : nat) : (term512 B r) = (term512 B r).
Proof. exact (eq_refl (term512 B r)). Qed.
Lemma lem7682322 {B : Type'} : (term509 B) = (term509 B).
Proof. exact (fun_ext (fun r : nat => @lem7682321 B r)). Qed.
Lemma lem7682323 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682324 {B : Type'} : (term523 B) = (term523 B).
Proof. exact (MK_COMB (@lem7682323) (@lem7682322 B)). Qed.
Lemma lem7682325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682326 {B : Type'} : (term525 B) = (term525 B).
Proof. exact (MK_COMB (@lem7682325) (@lem7682324 B)). Qed.
Lemma lem7682327 {B : Type'} : (term529 B) = (term529 B).
Proof. exact (MK_COMB (@lem7682326 B) (@lem7682290 B)). Qed.
Lemma lem7682336 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7682337 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7682336 B a)). Qed.
Lemma lem7682338 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7682339 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7682338 B) (@lem7682337 B)). Qed.
Lemma lem7682340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682341 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7682340) (@lem7682339 B)). Qed.
Lemma lem7682342 {B : Type'} : (term530 B) = (term530 B).
Proof. exact (MK_COMB (@lem7682341 B) (@lem7682327 B)). Qed.
Lemma lem7682373 {A B : Type'} (r : nat) : (term484 A B r) = (term484 A B r).
Proof. exact (eq_refl (term484 A B r)). Qed.
Lemma lem7682374 {A B : Type'} : (term478 A B) = (term478 A B).
Proof. exact (fun_ext (fun r : nat => @lem7682373 A B r)). Qed.
Lemma lem7682375 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682376 {A B : Type'} : (term496 A B) = (term496 A B).
Proof. exact (MK_COMB (@lem7682375) (@lem7682374 A B)). Qed.
Lemma lem7682407 {A B : Type'} (r : nat) : (term480 A B r) = (term480 A B r).
Proof. exact (eq_refl (term480 A B r)). Qed.
Lemma lem7682408 {A B : Type'} : (term477 A B) = (term477 A B).
Proof. exact (fun_ext (fun r : nat => @lem7682407 A B r)). Qed.
Lemma lem7682409 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682410 {A B : Type'} : (term491 A B) = (term491 A B).
Proof. exact (MK_COMB (@lem7682409) (@lem7682408 A B)). Qed.
Lemma lem7682411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682412 {A B : Type'} : (term493 A B) = (term493 A B).
Proof. exact (MK_COMB (@lem7682411) (@lem7682410 A B)). Qed.
Lemma lem7682413 {A B : Type'} : (term497 A B) = (term497 A B).
Proof. exact (MK_COMB (@lem7682412 A B) (@lem7682376 A B)). Qed.
Lemma lem7682422 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7682423 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7682422 A B a)). Qed.
Lemma lem7682424 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7682425 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7682424 A B) (@lem7682423 A B)). Qed.
Lemma lem7682426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682427 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7682426) (@lem7682425 A B)). Qed.
Lemma lem7682428 {A B : Type'} : (term498 A B) = (term498 A B).
Proof. exact (MK_COMB (@lem7682427 A B) (@lem7682413 A B)). Qed.
Lemma lem7682429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682430 {A B : Type'} : (term499 A B) = (term499 A B).
Proof. exact (MK_COMB (@lem7682429) (@lem7682428 A B)). Qed.
Lemma lem7682431 {A B : Type'} : (term549 A B) = (term549 A B).
Proof. exact (MK_COMB (@lem7682430 A B) (@lem7682342 B)). Qed.
Lemma lem7682466 {A : Type'} (r : nat) : (term429 A r) = (term429 A r).
Proof. exact (eq_refl (term429 A r)). Qed.
Lemma lem7682467 {A : Type'} : (term423 A) = (term423 A).
Proof. exact (fun_ext (fun r : nat => @lem7682466 A r)). Qed.
Lemma lem7682468 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682469 {A : Type'} : (term441 A) = (term441 A).
Proof. exact (MK_COMB (@lem7682468) (@lem7682467 A)). Qed.
Lemma lem7682504 {A : Type'} (r : nat) : (term425 A r) = (term425 A r).
Proof. exact (eq_refl (term425 A r)). Qed.
Lemma lem7682505 {A : Type'} : (term422 A) = (term422 A).
Proof. exact (fun_ext (fun r : nat => @lem7682504 A r)). Qed.
Lemma lem7682506 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682507 {A : Type'} : (term436 A) = (term436 A).
Proof. exact (MK_COMB (@lem7682506) (@lem7682505 A)). Qed.
Lemma lem7682508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682509 {A : Type'} : (term438 A) = (term438 A).
Proof. exact (MK_COMB (@lem7682508) (@lem7682507 A)). Qed.
Lemma lem7682510 {A : Type'} : (term442 A) = (term442 A).
Proof. exact (MK_COMB (@lem7682509 A) (@lem7682469 A)). Qed.
Lemma lem7682519 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7682520 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7682519 A a)). Qed.
Lemma lem7682521 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7682522 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7682521 A) (@lem7682520 A)). Qed.
Lemma lem7682523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682524 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7682523) (@lem7682522 A)). Qed.
Lemma lem7682525 {A : Type'} : (term443 A) = (term443 A).
Proof. exact (MK_COMB (@lem7682524 A) (@lem7682510 A)). Qed.
Lemma lem7682526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682527 {A : Type'} : (term444 A) = (term444 A).
Proof. exact (MK_COMB (@lem7682526) (@lem7682525 A)). Qed.
Lemma lem7682528 {A B : Type'} : (term550 A B) = (term550 A B).
Proof. exact (MK_COMB (@lem7682527 A) (@lem7682431 A B)). Qed.
Lemma lem7682559 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term258 A B x x') = (term258 A B x x').
Proof. exact (eq_refl (term258 A B x x')). Qed.
Lemma lem7682560 {A B : Type'} (x : finite_diff A B) : (term264 A B x) = (term264 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7682559 A B x x')). Qed.
Lemma lem7682561 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682562 {A B : Type'} (x : finite_diff A B) : (term265 A B x) = (term265 A B x).
Proof. exact (MK_COMB (@lem7682561) (@lem7682560 A B x)). Qed.
Lemma lem7682563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682564 {A B : Type'} (x : finite_diff A B) : (term614 A B x) = (term614 A B x).
Proof. exact (MK_COMB (@lem7682563) (@lem7682562 A B x)). Qed.
Lemma lem7682565 {A B : Type'} (x : finite_diff A B) : (term808 A B x) = (term808 A B x).
Proof. exact (MK_COMB (@lem7682564 A B x) (@lem7682528 A B)). Qed.
Lemma lem7682578 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7682579 {A B : Type'} (x : finite_diff A B) : (term821 A B x) = (term821 A B x).
Proof. exact (MK_COMB (@lem7682578 A B) (@lem7682565 A B x)). Qed.
Lemma lem7682610 {B : Type'} (r : nat) : (term516 B r) = (term516 B r).
Proof. exact (eq_refl (term516 B r)). Qed.
Lemma lem7682611 {B : Type'} : (term510 B) = (term510 B).
Proof. exact (fun_ext (fun r : nat => @lem7682610 B r)). Qed.
Lemma lem7682612 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682613 {B : Type'} : (term528 B) = (term528 B).
Proof. exact (MK_COMB (@lem7682612) (@lem7682611 B)). Qed.
Lemma lem7682644 {B : Type'} (r : nat) : (term512 B r) = (term512 B r).
Proof. exact (eq_refl (term512 B r)). Qed.
Lemma lem7682645 {B : Type'} : (term509 B) = (term509 B).
Proof. exact (fun_ext (fun r : nat => @lem7682644 B r)). Qed.
Lemma lem7682646 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682647 {B : Type'} : (term523 B) = (term523 B).
Proof. exact (MK_COMB (@lem7682646) (@lem7682645 B)). Qed.
Lemma lem7682648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682649 {B : Type'} : (term525 B) = (term525 B).
Proof. exact (MK_COMB (@lem7682648) (@lem7682647 B)). Qed.
Lemma lem7682650 {B : Type'} : (term529 B) = (term529 B).
Proof. exact (MK_COMB (@lem7682649 B) (@lem7682613 B)). Qed.
Lemma lem7682659 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7682660 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7682659 B a)). Qed.
Lemma lem7682661 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7682662 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7682661 B) (@lem7682660 B)). Qed.
Lemma lem7682663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682664 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7682663) (@lem7682662 B)). Qed.
Lemma lem7682665 {B : Type'} : (term530 B) = (term530 B).
Proof. exact (MK_COMB (@lem7682664 B) (@lem7682650 B)). Qed.
Lemma lem7682700 {A B : Type'} (r : nat) : (term454 A B r) = (term454 A B r).
Proof. exact (eq_refl (term454 A B r)). Qed.
Lemma lem7682701 {A B : Type'} : (term448 A B) = (term448 A B).
Proof. exact (fun_ext (fun r : nat => @lem7682700 A B r)). Qed.
Lemma lem7682702 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682703 {A B : Type'} : (term466 A B) = (term466 A B).
Proof. exact (MK_COMB (@lem7682702) (@lem7682701 A B)). Qed.
Lemma lem7682738 {A B : Type'} (r : nat) : (term450 A B r) = (term450 A B r).
Proof. exact (eq_refl (term450 A B r)). Qed.
Lemma lem7682739 {A B : Type'} : (term447 A B) = (term447 A B).
Proof. exact (fun_ext (fun r : nat => @lem7682738 A B r)). Qed.
Lemma lem7682740 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682741 {A B : Type'} : (term461 A B) = (term461 A B).
Proof. exact (MK_COMB (@lem7682740) (@lem7682739 A B)). Qed.
Lemma lem7682742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682743 {A B : Type'} : (term463 A B) = (term463 A B).
Proof. exact (MK_COMB (@lem7682742) (@lem7682741 A B)). Qed.
Lemma lem7682744 {A B : Type'} : (term467 A B) = (term467 A B).
Proof. exact (MK_COMB (@lem7682743 A B) (@lem7682703 A B)). Qed.
Lemma lem7682753 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7682754 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7682753 A B a)). Qed.
Lemma lem7682755 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7682756 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7682755 A B) (@lem7682754 A B)). Qed.
Lemma lem7682757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682758 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7682757) (@lem7682756 A B)). Qed.
Lemma lem7682759 {A B : Type'} : (term468 A B) = (term468 A B).
Proof. exact (MK_COMB (@lem7682758 A B) (@lem7682744 A B)). Qed.
Lemma lem7682760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682761 {A B : Type'} : (term469 A B) = (term469 A B).
Proof. exact (MK_COMB (@lem7682760) (@lem7682759 A B)). Qed.
Lemma lem7682762 {A B : Type'} : (term544 A B) = (term544 A B).
Proof. exact (MK_COMB (@lem7682761 A B) (@lem7682665 B)). Qed.
Lemma lem7682797 {A : Type'} (r : nat) : (term429 A r) = (term429 A r).
Proof. exact (eq_refl (term429 A r)). Qed.
Lemma lem7682798 {A : Type'} : (term423 A) = (term423 A).
Proof. exact (fun_ext (fun r : nat => @lem7682797 A r)). Qed.
Lemma lem7682799 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682800 {A : Type'} : (term441 A) = (term441 A).
Proof. exact (MK_COMB (@lem7682799) (@lem7682798 A)). Qed.
Lemma lem7682835 {A : Type'} (r : nat) : (term425 A r) = (term425 A r).
Proof. exact (eq_refl (term425 A r)). Qed.
Lemma lem7682836 {A : Type'} : (term422 A) = (term422 A).
Proof. exact (fun_ext (fun r : nat => @lem7682835 A r)). Qed.
Lemma lem7682837 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682838 {A : Type'} : (term436 A) = (term436 A).
Proof. exact (MK_COMB (@lem7682837) (@lem7682836 A)). Qed.
Lemma lem7682839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682840 {A : Type'} : (term438 A) = (term438 A).
Proof. exact (MK_COMB (@lem7682839) (@lem7682838 A)). Qed.
Lemma lem7682841 {A : Type'} : (term442 A) = (term442 A).
Proof. exact (MK_COMB (@lem7682840 A) (@lem7682800 A)). Qed.
Lemma lem7682850 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7682851 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7682850 A a)). Qed.
Lemma lem7682852 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7682853 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7682852 A) (@lem7682851 A)). Qed.
Lemma lem7682854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682855 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7682854) (@lem7682853 A)). Qed.
Lemma lem7682856 {A : Type'} : (term443 A) = (term443 A).
Proof. exact (MK_COMB (@lem7682855 A) (@lem7682841 A)). Qed.
Lemma lem7682857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682858 {A : Type'} : (term444 A) = (term444 A).
Proof. exact (MK_COMB (@lem7682857) (@lem7682856 A)). Qed.
Lemma lem7682859 {A B : Type'} : (term545 A B) = (term545 A B).
Proof. exact (MK_COMB (@lem7682858 A) (@lem7682762 A B)). Qed.
Lemma lem7682894 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term209 A B x x') = (term209 A B x x').
Proof. exact (eq_refl (term209 A B x x')). Qed.
Lemma lem7682895 {A B : Type'} (x : finite_diff A B) : (term217 A B x) = (term217 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7682894 A B x x')). Qed.
Lemma lem7682896 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682897 {A B : Type'} (x : finite_diff A B) : (term218 A B x) = (term218 A B x).
Proof. exact (MK_COMB (@lem7682896) (@lem7682895 A B x)). Qed.
Lemma lem7682898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7682899 {A B : Type'} (x : finite_diff A B) : (term581 A B x) = (term581 A B x).
Proof. exact (MK_COMB (@lem7682898) (@lem7682897 A B x)). Qed.
Lemma lem7682900 {A B : Type'} (x : finite_diff A B) : (term785 A B x) = (term785 A B x).
Proof. exact (MK_COMB (@lem7682899 A B x) (@lem7682859 A B)). Qed.
Lemma lem7682911 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7682912 {A B : Type'} (x : finite_diff A B) : (term798 A B x) = (term798 A B x).
Proof. exact (MK_COMB (@lem7682911 A B) (@lem7682900 A B x)). Qed.
Lemma lem7682913 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7682914 {A B : Type'} (x : finite_diff A B) : (term838 A B x) = (term838 A B x).
Proof. exact (MK_COMB (@lem7682913) (@lem7682912 A B x)). Qed.
Lemma lem7682915 {A B : Type'} (x : finite_diff A B) : (term840 A B x) = (term840 A B x).
Proof. exact (MK_COMB (@lem7682914 A B x) (@lem7682579 A B x)). Qed.
Lemma lem7682926 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (eq_refl (term299 A)). Qed.
Lemma lem7682927 {A B : Type'} (x : finite_diff A B) : (term853 A B x) = (term853 A B x).
Proof. exact (MK_COMB (@lem7682926 A) (@lem7682915 A B x)). Qed.
Lemma lem7682928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7682929 {A B : Type'} (x : finite_diff A B) : (term948 A B x) = (term948 A B x).
Proof. exact (MK_COMB (@lem7682928) (@lem7682927 A B x)). Qed.
Lemma lem7682930 {A B : Type'} (x : finite_diff A B) : (term950 A B x) = (term950 A B x).
Proof. exact (MK_COMB (@lem7682929 A B x) (@lem7682256 A B x)). Qed.
Lemma lem7682943 {B : Type'} : (term333 B) = (term333 B).
Proof. exact (eq_refl (term333 B)). Qed.
Lemma lem7682944 {A B : Type'} (x : finite_diff A B) : (term963 A B x) = (term963 A B x).
Proof. exact (MK_COMB (@lem7682943 B) (@lem7682930 A B x)). Qed.
Lemma lem7682979 {B : Type'} (r : nat) : (term429 B r) = (term429 B r).
Proof. exact (eq_refl (term429 B r)). Qed.
Lemma lem7682980 {B : Type'} : (term423 B) = (term423 B).
Proof. exact (fun_ext (fun r : nat => @lem7682979 B r)). Qed.
Lemma lem7682981 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7682982 {B : Type'} : (term441 B) = (term441 B).
Proof. exact (MK_COMB (@lem7682981) (@lem7682980 B)). Qed.
Lemma lem7683017 {B : Type'} (r : nat) : (term425 B r) = (term425 B r).
Proof. exact (eq_refl (term425 B r)). Qed.
Lemma lem7683018 {B : Type'} : (term422 B) = (term422 B).
Proof. exact (fun_ext (fun r : nat => @lem7683017 B r)). Qed.
Lemma lem7683019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683020 {B : Type'} : (term436 B) = (term436 B).
Proof. exact (MK_COMB (@lem7683019) (@lem7683018 B)). Qed.
Lemma lem7683021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683022 {B : Type'} : (term438 B) = (term438 B).
Proof. exact (MK_COMB (@lem7683021) (@lem7683020 B)). Qed.
Lemma lem7683023 {B : Type'} : (term442 B) = (term442 B).
Proof. exact (MK_COMB (@lem7683022 B) (@lem7682982 B)). Qed.
Lemma lem7683032 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7683033 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7683032 B a)). Qed.
Lemma lem7683034 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7683035 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7683034 B) (@lem7683033 B)). Qed.
Lemma lem7683036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683037 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7683036) (@lem7683035 B)). Qed.
Lemma lem7683038 {B : Type'} : (term443 B) = (term443 B).
Proof. exact (MK_COMB (@lem7683037 B) (@lem7683023 B)). Qed.
Lemma lem7683069 {A B : Type'} (r : nat) : (term484 A B r) = (term484 A B r).
Proof. exact (eq_refl (term484 A B r)). Qed.
Lemma lem7683070 {A B : Type'} : (term478 A B) = (term478 A B).
Proof. exact (fun_ext (fun r : nat => @lem7683069 A B r)). Qed.
Lemma lem7683071 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683072 {A B : Type'} : (term496 A B) = (term496 A B).
Proof. exact (MK_COMB (@lem7683071) (@lem7683070 A B)). Qed.
Lemma lem7683103 {A B : Type'} (r : nat) : (term480 A B r) = (term480 A B r).
Proof. exact (eq_refl (term480 A B r)). Qed.
Lemma lem7683104 {A B : Type'} : (term477 A B) = (term477 A B).
Proof. exact (fun_ext (fun r : nat => @lem7683103 A B r)). Qed.
Lemma lem7683105 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683106 {A B : Type'} : (term491 A B) = (term491 A B).
Proof. exact (MK_COMB (@lem7683105) (@lem7683104 A B)). Qed.
Lemma lem7683107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683108 {A B : Type'} : (term493 A B) = (term493 A B).
Proof. exact (MK_COMB (@lem7683107) (@lem7683106 A B)). Qed.
Lemma lem7683109 {A B : Type'} : (term497 A B) = (term497 A B).
Proof. exact (MK_COMB (@lem7683108 A B) (@lem7683072 A B)). Qed.
Lemma lem7683118 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7683119 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7683118 A B a)). Qed.
Lemma lem7683120 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7683121 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7683120 A B) (@lem7683119 A B)). Qed.
Lemma lem7683122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683123 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7683122) (@lem7683121 A B)). Qed.
Lemma lem7683124 {A B : Type'} : (term498 A B) = (term498 A B).
Proof. exact (MK_COMB (@lem7683123 A B) (@lem7683109 A B)). Qed.
Lemma lem7683125 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683126 {A B : Type'} : (term499 A B) = (term499 A B).
Proof. exact (MK_COMB (@lem7683125) (@lem7683124 A B)). Qed.
Lemma lem7683127 {A B : Type'} : (term500 A B) = (term500 A B).
Proof. exact (MK_COMB (@lem7683126 A B) (@lem7683038 B)). Qed.
Lemma lem7683158 {A : Type'} (r : nat) : (term516 A r) = (term516 A r).
Proof. exact (eq_refl (term516 A r)). Qed.
Lemma lem7683159 {A : Type'} : (term510 A) = (term510 A).
Proof. exact (fun_ext (fun r : nat => @lem7683158 A r)). Qed.
Lemma lem7683160 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683161 {A : Type'} : (term528 A) = (term528 A).
Proof. exact (MK_COMB (@lem7683160) (@lem7683159 A)). Qed.
Lemma lem7683192 {A : Type'} (r : nat) : (term512 A r) = (term512 A r).
Proof. exact (eq_refl (term512 A r)). Qed.
Lemma lem7683193 {A : Type'} : (term509 A) = (term509 A).
Proof. exact (fun_ext (fun r : nat => @lem7683192 A r)). Qed.
Lemma lem7683194 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683195 {A : Type'} : (term523 A) = (term523 A).
Proof. exact (MK_COMB (@lem7683194) (@lem7683193 A)). Qed.
Lemma lem7683196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683197 {A : Type'} : (term525 A) = (term525 A).
Proof. exact (MK_COMB (@lem7683196) (@lem7683195 A)). Qed.
Lemma lem7683198 {A : Type'} : (term529 A) = (term529 A).
Proof. exact (MK_COMB (@lem7683197 A) (@lem7683161 A)). Qed.
Lemma lem7683207 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7683208 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7683207 A a)). Qed.
Lemma lem7683209 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7683210 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7683209 A) (@lem7683208 A)). Qed.
Lemma lem7683211 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683212 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7683211) (@lem7683210 A)). Qed.
Lemma lem7683213 {A : Type'} : (term530 A) = (term530 A).
Proof. exact (MK_COMB (@lem7683212 A) (@lem7683198 A)). Qed.
Lemma lem7683214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683215 {A : Type'} : (term531 A) = (term531 A).
Proof. exact (MK_COMB (@lem7683214) (@lem7683213 A)). Qed.
Lemma lem7683216 {A B : Type'} : (term536 A B) = (term536 A B).
Proof. exact (MK_COMB (@lem7683215 A) (@lem7683127 A B)). Qed.
Lemma lem7683247 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term258 A B x x') = (term258 A B x x').
Proof. exact (eq_refl (term258 A B x x')). Qed.
Lemma lem7683248 {A B : Type'} (x : finite_diff A B) : (term264 A B x) = (term264 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7683247 A B x x')). Qed.
Lemma lem7683249 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683250 {A B : Type'} (x : finite_diff A B) : (term265 A B x) = (term265 A B x).
Proof. exact (MK_COMB (@lem7683249) (@lem7683248 A B x)). Qed.
Lemma lem7683251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683252 {A B : Type'} (x : finite_diff A B) : (term614 A B x) = (term614 A B x).
Proof. exact (MK_COMB (@lem7683251) (@lem7683250 A B x)). Qed.
Lemma lem7683253 {A B : Type'} (x : finite_diff A B) : (term698 A B x) = (term698 A B x).
Proof. exact (MK_COMB (@lem7683252 A B x) (@lem7683216 A B)). Qed.
Lemma lem7683266 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7683267 {A B : Type'} (x : finite_diff A B) : (term711 A B x) = (term711 A B x).
Proof. exact (MK_COMB (@lem7683266 A B) (@lem7683253 A B x)). Qed.
Lemma lem7683302 {B : Type'} (r : nat) : (term429 B r) = (term429 B r).
Proof. exact (eq_refl (term429 B r)). Qed.
Lemma lem7683303 {B : Type'} : (term423 B) = (term423 B).
Proof. exact (fun_ext (fun r : nat => @lem7683302 B r)). Qed.
Lemma lem7683304 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683305 {B : Type'} : (term441 B) = (term441 B).
Proof. exact (MK_COMB (@lem7683304) (@lem7683303 B)). Qed.
Lemma lem7683340 {B : Type'} (r : nat) : (term425 B r) = (term425 B r).
Proof. exact (eq_refl (term425 B r)). Qed.
Lemma lem7683341 {B : Type'} : (term422 B) = (term422 B).
Proof. exact (fun_ext (fun r : nat => @lem7683340 B r)). Qed.
Lemma lem7683342 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683343 {B : Type'} : (term436 B) = (term436 B).
Proof. exact (MK_COMB (@lem7683342) (@lem7683341 B)). Qed.
Lemma lem7683344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683345 {B : Type'} : (term438 B) = (term438 B).
Proof. exact (MK_COMB (@lem7683344) (@lem7683343 B)). Qed.
Lemma lem7683346 {B : Type'} : (term442 B) = (term442 B).
Proof. exact (MK_COMB (@lem7683345 B) (@lem7683305 B)). Qed.
Lemma lem7683355 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7683356 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7683355 B a)). Qed.
Lemma lem7683357 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7683358 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7683357 B) (@lem7683356 B)). Qed.
Lemma lem7683359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683360 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7683359) (@lem7683358 B)). Qed.
Lemma lem7683361 {B : Type'} : (term443 B) = (term443 B).
Proof. exact (MK_COMB (@lem7683360 B) (@lem7683346 B)). Qed.
Lemma lem7683396 {A B : Type'} (r : nat) : (term454 A B r) = (term454 A B r).
Proof. exact (eq_refl (term454 A B r)). Qed.
Lemma lem7683397 {A B : Type'} : (term448 A B) = (term448 A B).
Proof. exact (fun_ext (fun r : nat => @lem7683396 A B r)). Qed.
Lemma lem7683398 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683399 {A B : Type'} : (term466 A B) = (term466 A B).
Proof. exact (MK_COMB (@lem7683398) (@lem7683397 A B)). Qed.
Lemma lem7683434 {A B : Type'} (r : nat) : (term450 A B r) = (term450 A B r).
Proof. exact (eq_refl (term450 A B r)). Qed.
Lemma lem7683435 {A B : Type'} : (term447 A B) = (term447 A B).
Proof. exact (fun_ext (fun r : nat => @lem7683434 A B r)). Qed.
Lemma lem7683436 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683437 {A B : Type'} : (term461 A B) = (term461 A B).
Proof. exact (MK_COMB (@lem7683436) (@lem7683435 A B)). Qed.
Lemma lem7683438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683439 {A B : Type'} : (term463 A B) = (term463 A B).
Proof. exact (MK_COMB (@lem7683438) (@lem7683437 A B)). Qed.
Lemma lem7683440 {A B : Type'} : (term467 A B) = (term467 A B).
Proof. exact (MK_COMB (@lem7683439 A B) (@lem7683399 A B)). Qed.
Lemma lem7683449 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7683450 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7683449 A B a)). Qed.
Lemma lem7683451 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7683452 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7683451 A B) (@lem7683450 A B)). Qed.
Lemma lem7683453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683454 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7683453) (@lem7683452 A B)). Qed.
Lemma lem7683455 {A B : Type'} : (term468 A B) = (term468 A B).
Proof. exact (MK_COMB (@lem7683454 A B) (@lem7683440 A B)). Qed.
Lemma lem7683456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683457 {A B : Type'} : (term469 A B) = (term469 A B).
Proof. exact (MK_COMB (@lem7683456) (@lem7683455 A B)). Qed.
Lemma lem7683458 {A B : Type'} : (term470 A B) = (term470 A B).
Proof. exact (MK_COMB (@lem7683457 A B) (@lem7683361 B)). Qed.
Lemma lem7683489 {A : Type'} (r : nat) : (term516 A r) = (term516 A r).
Proof. exact (eq_refl (term516 A r)). Qed.
Lemma lem7683490 {A : Type'} : (term510 A) = (term510 A).
Proof. exact (fun_ext (fun r : nat => @lem7683489 A r)). Qed.
Lemma lem7683491 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683492 {A : Type'} : (term528 A) = (term528 A).
Proof. exact (MK_COMB (@lem7683491) (@lem7683490 A)). Qed.
Lemma lem7683523 {A : Type'} (r : nat) : (term512 A r) = (term512 A r).
Proof. exact (eq_refl (term512 A r)). Qed.
Lemma lem7683524 {A : Type'} : (term509 A) = (term509 A).
Proof. exact (fun_ext (fun r : nat => @lem7683523 A r)). Qed.
Lemma lem7683525 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683526 {A : Type'} : (term523 A) = (term523 A).
Proof. exact (MK_COMB (@lem7683525) (@lem7683524 A)). Qed.
Lemma lem7683527 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683528 {A : Type'} : (term525 A) = (term525 A).
Proof. exact (MK_COMB (@lem7683527) (@lem7683526 A)). Qed.
Lemma lem7683529 {A : Type'} : (term529 A) = (term529 A).
Proof. exact (MK_COMB (@lem7683528 A) (@lem7683492 A)). Qed.
Lemma lem7683538 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7683539 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7683538 A a)). Qed.
Lemma lem7683540 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7683541 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7683540 A) (@lem7683539 A)). Qed.
Lemma lem7683542 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683543 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7683542) (@lem7683541 A)). Qed.
Lemma lem7683544 {A : Type'} : (term530 A) = (term530 A).
Proof. exact (MK_COMB (@lem7683543 A) (@lem7683529 A)). Qed.
Lemma lem7683545 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683546 {A : Type'} : (term531 A) = (term531 A).
Proof. exact (MK_COMB (@lem7683545) (@lem7683544 A)). Qed.
Lemma lem7683547 {A B : Type'} : (term532 A B) = (term532 A B).
Proof. exact (MK_COMB (@lem7683546 A) (@lem7683458 A B)). Qed.
Lemma lem7683582 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term209 A B x x') = (term209 A B x x').
Proof. exact (eq_refl (term209 A B x x')). Qed.
Lemma lem7683583 {A B : Type'} (x : finite_diff A B) : (term217 A B x) = (term217 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7683582 A B x x')). Qed.
Lemma lem7683584 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683585 {A B : Type'} (x : finite_diff A B) : (term218 A B x) = (term218 A B x).
Proof. exact (MK_COMB (@lem7683584) (@lem7683583 A B x)). Qed.
Lemma lem7683586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683587 {A B : Type'} (x : finite_diff A B) : (term581 A B x) = (term581 A B x).
Proof. exact (MK_COMB (@lem7683586) (@lem7683585 A B x)). Qed.
Lemma lem7683588 {A B : Type'} (x : finite_diff A B) : (term675 A B x) = (term675 A B x).
Proof. exact (MK_COMB (@lem7683587 A B x) (@lem7683547 A B)). Qed.
Lemma lem7683599 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7683600 {A B : Type'} (x : finite_diff A B) : (term688 A B x) = (term688 A B x).
Proof. exact (MK_COMB (@lem7683599 A B) (@lem7683588 A B x)). Qed.
Lemma lem7683601 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7683602 {A B : Type'} (x : finite_diff A B) : (term728 A B x) = (term728 A B x).
Proof. exact (MK_COMB (@lem7683601) (@lem7683600 A B x)). Qed.
Lemma lem7683603 {A B : Type'} (x : finite_diff A B) : (term730 A B x) = (term730 A B x).
Proof. exact (MK_COMB (@lem7683602 A B x) (@lem7683267 A B x)). Qed.
Lemma lem7683616 {A : Type'} : (term333 A) = (term333 A).
Proof. exact (eq_refl (term333 A)). Qed.
Lemma lem7683617 {A B : Type'} (x : finite_diff A B) : (term743 A B x) = (term743 A B x).
Proof. exact (MK_COMB (@lem7683616 A) (@lem7683603 A B x)). Qed.
Lemma lem7683652 {B : Type'} (r : nat) : (term429 B r) = (term429 B r).
Proof. exact (eq_refl (term429 B r)). Qed.
Lemma lem7683653 {B : Type'} : (term423 B) = (term423 B).
Proof. exact (fun_ext (fun r : nat => @lem7683652 B r)). Qed.
Lemma lem7683654 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683655 {B : Type'} : (term441 B) = (term441 B).
Proof. exact (MK_COMB (@lem7683654) (@lem7683653 B)). Qed.
Lemma lem7683690 {B : Type'} (r : nat) : (term425 B r) = (term425 B r).
Proof. exact (eq_refl (term425 B r)). Qed.
Lemma lem7683691 {B : Type'} : (term422 B) = (term422 B).
Proof. exact (fun_ext (fun r : nat => @lem7683690 B r)). Qed.
Lemma lem7683692 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683693 {B : Type'} : (term436 B) = (term436 B).
Proof. exact (MK_COMB (@lem7683692) (@lem7683691 B)). Qed.
Lemma lem7683694 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683695 {B : Type'} : (term438 B) = (term438 B).
Proof. exact (MK_COMB (@lem7683694) (@lem7683693 B)). Qed.
Lemma lem7683696 {B : Type'} : (term442 B) = (term442 B).
Proof. exact (MK_COMB (@lem7683695 B) (@lem7683655 B)). Qed.
Lemma lem7683705 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7683706 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7683705 B a)). Qed.
Lemma lem7683707 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7683708 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7683707 B) (@lem7683706 B)). Qed.
Lemma lem7683709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683710 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7683709) (@lem7683708 B)). Qed.
Lemma lem7683711 {B : Type'} : (term443 B) = (term443 B).
Proof. exact (MK_COMB (@lem7683710 B) (@lem7683696 B)). Qed.
Lemma lem7683742 {A B : Type'} (r : nat) : (term484 A B r) = (term484 A B r).
Proof. exact (eq_refl (term484 A B r)). Qed.
Lemma lem7683743 {A B : Type'} : (term478 A B) = (term478 A B).
Proof. exact (fun_ext (fun r : nat => @lem7683742 A B r)). Qed.
Lemma lem7683744 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683745 {A B : Type'} : (term496 A B) = (term496 A B).
Proof. exact (MK_COMB (@lem7683744) (@lem7683743 A B)). Qed.
Lemma lem7683776 {A B : Type'} (r : nat) : (term480 A B r) = (term480 A B r).
Proof. exact (eq_refl (term480 A B r)). Qed.
Lemma lem7683777 {A B : Type'} : (term477 A B) = (term477 A B).
Proof. exact (fun_ext (fun r : nat => @lem7683776 A B r)). Qed.
Lemma lem7683778 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683779 {A B : Type'} : (term491 A B) = (term491 A B).
Proof. exact (MK_COMB (@lem7683778) (@lem7683777 A B)). Qed.
Lemma lem7683780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683781 {A B : Type'} : (term493 A B) = (term493 A B).
Proof. exact (MK_COMB (@lem7683780) (@lem7683779 A B)). Qed.
Lemma lem7683782 {A B : Type'} : (term497 A B) = (term497 A B).
Proof. exact (MK_COMB (@lem7683781 A B) (@lem7683745 A B)). Qed.
Lemma lem7683791 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7683792 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7683791 A B a)). Qed.
Lemma lem7683793 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7683794 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7683793 A B) (@lem7683792 A B)). Qed.
Lemma lem7683795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683796 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7683795) (@lem7683794 A B)). Qed.
Lemma lem7683797 {A B : Type'} : (term498 A B) = (term498 A B).
Proof. exact (MK_COMB (@lem7683796 A B) (@lem7683782 A B)). Qed.
Lemma lem7683798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683799 {A B : Type'} : (term499 A B) = (term499 A B).
Proof. exact (MK_COMB (@lem7683798) (@lem7683797 A B)). Qed.
Lemma lem7683800 {A B : Type'} : (term500 A B) = (term500 A B).
Proof. exact (MK_COMB (@lem7683799 A B) (@lem7683711 B)). Qed.
Lemma lem7683835 {A : Type'} (r : nat) : (term429 A r) = (term429 A r).
Proof. exact (eq_refl (term429 A r)). Qed.
Lemma lem7683836 {A : Type'} : (term423 A) = (term423 A).
Proof. exact (fun_ext (fun r : nat => @lem7683835 A r)). Qed.
Lemma lem7683837 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683838 {A : Type'} : (term441 A) = (term441 A).
Proof. exact (MK_COMB (@lem7683837) (@lem7683836 A)). Qed.
Lemma lem7683873 {A : Type'} (r : nat) : (term425 A r) = (term425 A r).
Proof. exact (eq_refl (term425 A r)). Qed.
Lemma lem7683874 {A : Type'} : (term422 A) = (term422 A).
Proof. exact (fun_ext (fun r : nat => @lem7683873 A r)). Qed.
Lemma lem7683875 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683876 {A : Type'} : (term436 A) = (term436 A).
Proof. exact (MK_COMB (@lem7683875) (@lem7683874 A)). Qed.
Lemma lem7683877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683878 {A : Type'} : (term438 A) = (term438 A).
Proof. exact (MK_COMB (@lem7683877) (@lem7683876 A)). Qed.
Lemma lem7683879 {A : Type'} : (term442 A) = (term442 A).
Proof. exact (MK_COMB (@lem7683878 A) (@lem7683838 A)). Qed.
Lemma lem7683888 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7683889 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7683888 A a)). Qed.
Lemma lem7683890 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7683891 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7683890 A) (@lem7683889 A)). Qed.
Lemma lem7683892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683893 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7683892) (@lem7683891 A)). Qed.
Lemma lem7683894 {A : Type'} : (term443 A) = (term443 A).
Proof. exact (MK_COMB (@lem7683893 A) (@lem7683879 A)). Qed.
Lemma lem7683895 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683896 {A : Type'} : (term444 A) = (term444 A).
Proof. exact (MK_COMB (@lem7683895) (@lem7683894 A)). Qed.
Lemma lem7683897 {A B : Type'} : (term501 A B) = (term501 A B).
Proof. exact (MK_COMB (@lem7683896 A) (@lem7683800 A B)). Qed.
Lemma lem7683928 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term258 A B x x') = (term258 A B x x').
Proof. exact (eq_refl (term258 A B x x')). Qed.
Lemma lem7683929 {A B : Type'} (x : finite_diff A B) : (term264 A B x) = (term264 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7683928 A B x x')). Qed.
Lemma lem7683930 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683931 {A B : Type'} (x : finite_diff A B) : (term265 A B x) = (term265 A B x).
Proof. exact (MK_COMB (@lem7683930) (@lem7683929 A B x)). Qed.
Lemma lem7683932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7683933 {A B : Type'} (x : finite_diff A B) : (term614 A B x) = (term614 A B x).
Proof. exact (MK_COMB (@lem7683932) (@lem7683931 A B x)). Qed.
Lemma lem7683934 {A B : Type'} (x : finite_diff A B) : (term616 A B x) = (term616 A B x).
Proof. exact (MK_COMB (@lem7683933 A B x) (@lem7683897 A B)). Qed.
Lemma lem7683947 {A B : Type'} : (term289 A B) = (term289 A B).
Proof. exact (eq_refl (term289 A B)). Qed.
Lemma lem7683948 {A B : Type'} (x : finite_diff A B) : (term629 A B x) = (term629 A B x).
Proof. exact (MK_COMB (@lem7683947 A B) (@lem7683934 A B x)). Qed.
Lemma lem7683983 {B : Type'} (r : nat) : (term429 B r) = (term429 B r).
Proof. exact (eq_refl (term429 B r)). Qed.
Lemma lem7683984 {B : Type'} : (term423 B) = (term423 B).
Proof. exact (fun_ext (fun r : nat => @lem7683983 B r)). Qed.
Lemma lem7683985 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7683986 {B : Type'} : (term441 B) = (term441 B).
Proof. exact (MK_COMB (@lem7683985) (@lem7683984 B)). Qed.
Lemma lem7684021 {B : Type'} (r : nat) : (term425 B r) = (term425 B r).
Proof. exact (eq_refl (term425 B r)). Qed.
Lemma lem7684022 {B : Type'} : (term422 B) = (term422 B).
Proof. exact (fun_ext (fun r : nat => @lem7684021 B r)). Qed.
Lemma lem7684023 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7684024 {B : Type'} : (term436 B) = (term436 B).
Proof. exact (MK_COMB (@lem7684023) (@lem7684022 B)). Qed.
Lemma lem7684025 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7684026 {B : Type'} : (term438 B) = (term438 B).
Proof. exact (MK_COMB (@lem7684025) (@lem7684024 B)). Qed.
Lemma lem7684027 {B : Type'} : (term442 B) = (term442 B).
Proof. exact (MK_COMB (@lem7684026 B) (@lem7683986 B)). Qed.
Lemma lem7684036 {B : Type'} (a : finite_diff B B) : ((term192 B a) = a) = ((term192 B a) = a).
Proof. exact (eq_refl ((term192 B a) = a)). Qed.
Lemma lem7684037 {B : Type'} : (term193 B) = (term193 B).
Proof. exact (fun_ext (fun a : finite_diff B B => @lem7684036 B a)). Qed.
Lemma lem7684038 {B : Type'} : (@all (finite_diff B B)) = (@all (finite_diff B B)).
Proof. exact (eq_refl (@all (finite_diff B B))). Qed.
Lemma lem7684039 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (MK_COMB (@lem7684038 B) (@lem7684037 B)). Qed.
Lemma lem7684040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7684041 {B : Type'} : (term98 B) = (term98 B).
Proof. exact (MK_COMB (@lem7684040) (@lem7684039 B)). Qed.
Lemma lem7684042 {B : Type'} : (term443 B) = (term443 B).
Proof. exact (MK_COMB (@lem7684041 B) (@lem7684027 B)). Qed.
Lemma lem7684077 {A B : Type'} (r : nat) : (term454 A B r) = (term454 A B r).
Proof. exact (eq_refl (term454 A B r)). Qed.
Lemma lem7684078 {A B : Type'} : (term448 A B) = (term448 A B).
Proof. exact (fun_ext (fun r : nat => @lem7684077 A B r)). Qed.
Lemma lem7684079 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7684080 {A B : Type'} : (term466 A B) = (term466 A B).
Proof. exact (MK_COMB (@lem7684079) (@lem7684078 A B)). Qed.
Lemma lem7684115 {A B : Type'} (r : nat) : (term450 A B r) = (term450 A B r).
Proof. exact (eq_refl (term450 A B r)). Qed.
Lemma lem7684116 {A B : Type'} : (term447 A B) = (term447 A B).
Proof. exact (fun_ext (fun r : nat => @lem7684115 A B r)). Qed.
Lemma lem7684117 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7684118 {A B : Type'} : (term461 A B) = (term461 A B).
Proof. exact (MK_COMB (@lem7684117) (@lem7684116 A B)). Qed.
Lemma lem7684119 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7684120 {A B : Type'} : (term463 A B) = (term463 A B).
Proof. exact (MK_COMB (@lem7684119) (@lem7684118 A B)). Qed.
Lemma lem7684121 {A B : Type'} : (term467 A B) = (term467 A B).
Proof. exact (MK_COMB (@lem7684120 A B) (@lem7684080 A B)). Qed.
Lemma lem7684130 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7684131 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7684130 A B a)). Qed.
Lemma lem7684132 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7684133 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7684132 A B) (@lem7684131 A B)). Qed.
Lemma lem7684134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7684135 {A B : Type'} : (term52 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7684134) (@lem7684133 A B)). Qed.
Lemma lem7684136 {A B : Type'} : (term468 A B) = (term468 A B).
Proof. exact (MK_COMB (@lem7684135 A B) (@lem7684121 A B)). Qed.
Lemma lem7684137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7684138 {A B : Type'} : (term469 A B) = (term469 A B).
Proof. exact (MK_COMB (@lem7684137) (@lem7684136 A B)). Qed.
Lemma lem7684139 {A B : Type'} : (term470 A B) = (term470 A B).
Proof. exact (MK_COMB (@lem7684138 A B) (@lem7684042 B)). Qed.
Lemma lem7684174 {A : Type'} (r : nat) : (term429 A r) = (term429 A r).
Proof. exact (eq_refl (term429 A r)). Qed.
Lemma lem7684175 {A : Type'} : (term423 A) = (term423 A).
Proof. exact (fun_ext (fun r : nat => @lem7684174 A r)). Qed.
Lemma lem7684176 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7684177 {A : Type'} : (term441 A) = (term441 A).
Proof. exact (MK_COMB (@lem7684176) (@lem7684175 A)). Qed.
Lemma lem7684212 {A : Type'} (r : nat) : (term425 A r) = (term425 A r).
Proof. exact (eq_refl (term425 A r)). Qed.
Lemma lem7684213 {A : Type'} : (term422 A) = (term422 A).
Proof. exact (fun_ext (fun r : nat => @lem7684212 A r)). Qed.
Lemma lem7684214 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7684215 {A : Type'} : (term436 A) = (term436 A).
Proof. exact (MK_COMB (@lem7684214) (@lem7684213 A)). Qed.
Lemma lem7684216 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7684217 {A : Type'} : (term438 A) = (term438 A).
Proof. exact (MK_COMB (@lem7684216) (@lem7684215 A)). Qed.
Lemma lem7684218 {A : Type'} : (term442 A) = (term442 A).
Proof. exact (MK_COMB (@lem7684217 A) (@lem7684177 A)). Qed.
Lemma lem7684227 {A : Type'} (a : finite_diff A A) : ((term192 A a) = a) = ((term192 A a) = a).
Proof. exact (eq_refl ((term192 A a) = a)). Qed.
Lemma lem7684228 {A : Type'} : (term193 A) = (term193 A).
Proof. exact (fun_ext (fun a : finite_diff A A => @lem7684227 A a)). Qed.
Lemma lem7684229 {A : Type'} : (@all (finite_diff A A)) = (@all (finite_diff A A)).
Proof. exact (eq_refl (@all (finite_diff A A))). Qed.
Lemma lem7684230 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem7684229 A) (@lem7684228 A)). Qed.
Lemma lem7684231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7684232 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (MK_COMB (@lem7684231) (@lem7684230 A)). Qed.
Lemma lem7684233 {A : Type'} : (term443 A) = (term443 A).
Proof. exact (MK_COMB (@lem7684232 A) (@lem7684218 A)). Qed.
Lemma lem7684234 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7684235 {A : Type'} : (term444 A) = (term444 A).
Proof. exact (MK_COMB (@lem7684234) (@lem7684233 A)). Qed.
Lemma lem7684236 {A B : Type'} : (term471 A B) = (term471 A B).
Proof. exact (MK_COMB (@lem7684235 A) (@lem7684139 A B)). Qed.
Lemma lem7684271 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term209 A B x x') = (term209 A B x x').
Proof. exact (eq_refl (term209 A B x x')). Qed.
Lemma lem7684272 {A B : Type'} (x : finite_diff A B) : (term217 A B x) = (term217 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7684271 A B x x')). Qed.
Lemma lem7684273 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7684274 {A B : Type'} (x : finite_diff A B) : (term218 A B x) = (term218 A B x).
Proof. exact (MK_COMB (@lem7684273) (@lem7684272 A B x)). Qed.
Lemma lem7684275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7684276 {A B : Type'} (x : finite_diff A B) : (term581 A B x) = (term581 A B x).
Proof. exact (MK_COMB (@lem7684275) (@lem7684274 A B x)). Qed.
Lemma lem7684277 {A B : Type'} (x : finite_diff A B) : (term583 A B x) = (term583 A B x).
Proof. exact (MK_COMB (@lem7684276 A B x) (@lem7684236 A B)). Qed.
Lemma lem7684288 {A B : Type'} : (term252 A B) = (term252 A B).
Proof. exact (eq_refl (term252 A B)). Qed.
Lemma lem7684289 {A B : Type'} (x : finite_diff A B) : (term600 A B x) = (term600 A B x).
Proof. exact (MK_COMB (@lem7684288 A B) (@lem7684277 A B x)). Qed.
Lemma lem7684290 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7684291 {A B : Type'} (x : finite_diff A B) : (term650 A B x) = (term650 A B x).
Proof. exact (MK_COMB (@lem7684290) (@lem7684289 A B x)). Qed.
Lemma lem7684292 {A B : Type'} (x : finite_diff A B) : (term652 A B x) = (term652 A B x).
Proof. exact (MK_COMB (@lem7684291 A B x) (@lem7683948 A B x)). Qed.
Lemma lem7684303 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (eq_refl (term299 A)). Qed.
Lemma lem7684304 {A B : Type'} (x : finite_diff A B) : (term665 A B x) = (term665 A B x).
Proof. exact (MK_COMB (@lem7684303 A) (@lem7684292 A B x)). Qed.
Lemma lem7684305 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7684306 {A B : Type'} (x : finite_diff A B) : (term760 A B x) = (term760 A B x).
Proof. exact (MK_COMB (@lem7684305) (@lem7684304 A B x)). Qed.
Lemma lem7684307 {A B : Type'} (x : finite_diff A B) : (term762 A B x) = (term762 A B x).
Proof. exact (MK_COMB (@lem7684306 A B x) (@lem7683617 A B x)). Qed.
Lemma lem7684318 {B : Type'} : (term299 B) = (term299 B).
Proof. exact (eq_refl (term299 B)). Qed.
Lemma lem7684319 {A B : Type'} (x : finite_diff A B) : (term775 A B x) = (term775 A B x).
Proof. exact (MK_COMB (@lem7684318 B) (@lem7684307 A B x)). Qed.
Lemma lem7684320 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7684321 {A B : Type'} (x : finite_diff A B) : (term980 A B x) = (term980 A B x).
Proof. exact (MK_COMB (@lem7684320) (@lem7684319 A B x)). Qed.
Lemma lem7684322 {A B : Type'} (x : finite_diff A B) : (term982 A B x) = (term982 A B x).
Proof. exact (MK_COMB (@lem7684321 A B x) (@lem7682944 A B x)). Qed.
Lemma lem7684323 {A B : Type'} (x : finite_diff A B) (h1 : term982 A B x) : term982 A B x.
Proof. exact (EQ_MP (@lem7684322 A B x) (@lem7681599 A B x h1)). Qed.
Lemma lem7684324 {A B : Type'} (x : finite_diff A B) (h1 : term775 A B x) : term775 A B x.
Proof. exact (h1). Qed.
Lemma lem7684325 {A B : Type'} (x : finite_diff A B) (h1 : term963 A B x) : term963 A B x.
Proof. exact (h1). Qed.
Lemma lem7684326 {A B : Type'} (x : finite_diff A B) (h1 : term775 A B x) : term762 A B x.
Proof. exact (proj2 (@lem7684324 A B x h1)). Qed.
Lemma lem7684328 {A B : Type'} (x : finite_diff A B) (h1 : term665 A B x) : term665 A B x.
Proof. exact (h1). Qed.
Lemma lem7684329 {A B : Type'} (x : finite_diff A B) (h1 : term743 A B x) : term743 A B x.
Proof. exact (h1). Qed.
Lemma lem7684330 {A B : Type'} (x : finite_diff A B) (h1 : term665 A B x) : term652 A B x.
Proof. exact (proj2 (@lem7684328 A B x h1)). Qed.
Lemma lem7684332 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term600 A B x.
Proof. exact (h1). Qed.
Lemma lem7684333 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term629 A B x.
Proof. exact (h1). Qed.
Lemma lem7684334 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term583 A B x.
Proof. exact (proj2 (@lem7684332 A B x h1)). Qed.
Lemma lem7684336 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term471 A B.
Proof. exact (proj2 (@lem7684334 A B x h1)). Qed.
Lemma lem7684337 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term218 A B x.
Proof. exact (proj1 (@lem7684334 A B x h1)). Qed.
Lemma lem7684338 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term470 A B.
Proof. exact (proj2 (@lem7684336 A B x h1)). Qed.
Lemma lem7684341 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term468 A B.
Proof. exact (proj1 (@lem7684338 A B x h1)). Qed.
Lemma lem7684346 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term467 A B.
Proof. exact (proj2 (@lem7684341 A B x h1)). Qed.
Lemma lem7684347 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term197 A B.
Proof. exact (proj1 (@lem7684341 A B x h1)). Qed.
Lemma lem7684349 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term461 A B.
Proof. exact (proj1 (@lem7684346 A B x h1)). Qed.
Lemma lem7684354 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term616 A B x.
Proof. exact (proj2 (@lem7684333 A B x h1)). Qed.
Lemma lem7684356 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term501 A B.
Proof. exact (proj2 (@lem7684354 A B x h1)). Qed.
Lemma lem7684357 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term265 A B x.
Proof. exact (proj1 (@lem7684354 A B x h1)). Qed.
Lemma lem7684358 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term500 A B.
Proof. exact (proj2 (@lem7684356 A B x h1)). Qed.
Lemma lem7684361 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term498 A B.
Proof. exact (proj1 (@lem7684358 A B x h1)). Qed.
Lemma lem7684366 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term497 A B.
Proof. exact (proj2 (@lem7684361 A B x h1)). Qed.
Lemma lem7684367 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term197 A B.
Proof. exact (proj1 (@lem7684361 A B x h1)). Qed.
Lemma lem7684369 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term491 A B.
Proof. exact (proj1 (@lem7684366 A B x h1)). Qed.
Lemma lem7684374 {A B : Type'} (x : finite_diff A B) (h1 : term743 A B x) : term730 A B x.
Proof. exact (proj2 (@lem7684329 A B x h1)). Qed.
Lemma lem7684376 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term688 A B x.
Proof. exact (h1). Qed.
Lemma lem7684377 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term711 A B x.
Proof. exact (h1). Qed.
Lemma lem7684378 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term675 A B x.
Proof. exact (proj2 (@lem7684376 A B x h1)). Qed.
Lemma lem7684380 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term532 A B.
Proof. exact (proj2 (@lem7684378 A B x h1)). Qed.
Lemma lem7684381 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term218 A B x.
Proof. exact (proj1 (@lem7684378 A B x h1)). Qed.
Lemma lem7684382 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term470 A B.
Proof. exact (proj2 (@lem7684380 A B x h1)). Qed.
Lemma lem7684385 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term468 A B.
Proof. exact (proj1 (@lem7684382 A B x h1)). Qed.
Lemma lem7684390 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term467 A B.
Proof. exact (proj2 (@lem7684385 A B x h1)). Qed.
Lemma lem7684391 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term197 A B.
Proof. exact (proj1 (@lem7684385 A B x h1)). Qed.
Lemma lem7684393 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term461 A B.
Proof. exact (proj1 (@lem7684390 A B x h1)). Qed.
Lemma lem7684398 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term698 A B x.
Proof. exact (proj2 (@lem7684377 A B x h1)). Qed.
Lemma lem7684400 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term536 A B.
Proof. exact (proj2 (@lem7684398 A B x h1)). Qed.
Lemma lem7684401 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term265 A B x.
Proof. exact (proj1 (@lem7684398 A B x h1)). Qed.
Lemma lem7684402 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term500 A B.
Proof. exact (proj2 (@lem7684400 A B x h1)). Qed.
Lemma lem7684405 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term498 A B.
Proof. exact (proj1 (@lem7684402 A B x h1)). Qed.
Lemma lem7684410 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term497 A B.
Proof. exact (proj2 (@lem7684405 A B x h1)). Qed.
Lemma lem7684411 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term197 A B.
Proof. exact (proj1 (@lem7684405 A B x h1)). Qed.
Lemma lem7684413 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term491 A B.
Proof. exact (proj1 (@lem7684410 A B x h1)). Qed.
Lemma lem7684418 {A B : Type'} (x : finite_diff A B) (h1 : term963 A B x) : term950 A B x.
Proof. exact (proj2 (@lem7684325 A B x h1)). Qed.
Lemma lem7684420 {A B : Type'} (x : finite_diff A B) (h1 : term853 A B x) : term853 A B x.
Proof. exact (h1). Qed.
Lemma lem7684421 {A B : Type'} (x : finite_diff A B) (h1 : term931 A B x) : term931 A B x.
Proof. exact (h1). Qed.
Lemma lem7684422 {A B : Type'} (x : finite_diff A B) (h1 : term853 A B x) : term840 A B x.
Proof. exact (proj2 (@lem7684420 A B x h1)). Qed.
Lemma lem7684424 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term798 A B x.
Proof. exact (h1). Qed.
Lemma lem7684425 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term821 A B x.
Proof. exact (h1). Qed.
Lemma lem7684426 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term785 A B x.
Proof. exact (proj2 (@lem7684424 A B x h1)). Qed.
Lemma lem7684428 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term545 A B.
Proof. exact (proj2 (@lem7684426 A B x h1)). Qed.
Lemma lem7684429 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term218 A B x.
Proof. exact (proj1 (@lem7684426 A B x h1)). Qed.
Lemma lem7684430 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term544 A B.
Proof. exact (proj2 (@lem7684428 A B x h1)). Qed.
Lemma lem7684433 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term468 A B.
Proof. exact (proj1 (@lem7684430 A B x h1)). Qed.
Lemma lem7684438 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term467 A B.
Proof. exact (proj2 (@lem7684433 A B x h1)). Qed.
Lemma lem7684439 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term197 A B.
Proof. exact (proj1 (@lem7684433 A B x h1)). Qed.
Lemma lem7684441 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term461 A B.
Proof. exact (proj1 (@lem7684438 A B x h1)). Qed.
Lemma lem7684446 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term808 A B x.
Proof. exact (proj2 (@lem7684425 A B x h1)). Qed.
Lemma lem7684448 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term550 A B.
Proof. exact (proj2 (@lem7684446 A B x h1)). Qed.
Lemma lem7684449 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term265 A B x.
Proof. exact (proj1 (@lem7684446 A B x h1)). Qed.
Lemma lem7684450 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term549 A B.
Proof. exact (proj2 (@lem7684448 A B x h1)). Qed.
Lemma lem7684453 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term498 A B.
Proof. exact (proj1 (@lem7684450 A B x h1)). Qed.
Lemma lem7684458 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term497 A B.
Proof. exact (proj2 (@lem7684453 A B x h1)). Qed.
Lemma lem7684459 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term197 A B.
Proof. exact (proj1 (@lem7684453 A B x h1)). Qed.
Lemma lem7684461 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term491 A B.
Proof. exact (proj1 (@lem7684458 A B x h1)). Qed.
Lemma lem7684466 {A B : Type'} (x : finite_diff A B) (h1 : term931 A B x) : term918 A B x.
Proof. exact (proj2 (@lem7684421 A B x h1)). Qed.
Lemma lem7684468 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term876 A B x.
Proof. exact (h1). Qed.
Lemma lem7684469 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term899 A B x.
Proof. exact (h1). Qed.
Lemma lem7684470 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term863 A B x.
Proof. exact (proj2 (@lem7684468 A B x h1)). Qed.
Lemma lem7684472 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term556 A B.
Proof. exact (proj2 (@lem7684470 A B x h1)). Qed.
Lemma lem7684473 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term218 A B x.
Proof. exact (proj1 (@lem7684470 A B x h1)). Qed.
Lemma lem7684474 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term544 A B.
Proof. exact (proj2 (@lem7684472 A B x h1)). Qed.
Lemma lem7684477 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term468 A B.
Proof. exact (proj1 (@lem7684474 A B x h1)). Qed.
Lemma lem7684482 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term467 A B.
Proof. exact (proj2 (@lem7684477 A B x h1)). Qed.
Lemma lem7684483 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term197 A B.
Proof. exact (proj1 (@lem7684477 A B x h1)). Qed.
Lemma lem7684485 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term461 A B.
Proof. exact (proj1 (@lem7684482 A B x h1)). Qed.
Lemma lem7684490 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term886 A B x.
Proof. exact (proj2 (@lem7684469 A B x h1)). Qed.
Lemma lem7684492 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term560 A B.
Proof. exact (proj2 (@lem7684490 A B x h1)). Qed.
Lemma lem7684493 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term265 A B x.
Proof. exact (proj1 (@lem7684490 A B x h1)). Qed.
Lemma lem7684494 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term549 A B.
Proof. exact (proj2 (@lem7684492 A B x h1)). Qed.
Lemma lem7684497 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term498 A B.
Proof. exact (proj1 (@lem7684494 A B x h1)). Qed.
Lemma lem7684502 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term497 A B.
Proof. exact (proj2 (@lem7684497 A B x h1)). Qed.
Lemma lem7684503 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term197 A B.
Proof. exact (proj1 (@lem7684497 A B x h1)). Qed.
Lemma lem7684505 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term491 A B.
Proof. exact (proj1 (@lem7684502 A B x h1)). Qed.
Lemma lem7684529 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term209 A B x x') = (term209 A B x x').
Proof. exact (eq_refl (term209 A B x x')). Qed.
Lemma lem7684530 {A B : Type'} (x : finite_diff A B) : (term217 A B x) = (term217 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7684529 A B x x')). Qed.
Lemma lem7684531 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7684533 {A B : Type'} (x : finite_diff A B) : (term218 A B x) = (term218 A B x).
Proof. exact (MK_COMB (@lem7684531) (@lem7684530 A B x)). Qed.
Lemma lem7684534 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term218 A B x.
Proof. exact (EQ_MP (@lem7684533 A B x) (@lem7684337 A B x h1)). Qed.
Lemma lem7684569 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7684570 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7684569 A B a)). Qed.
Lemma lem7684571 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7684573 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7684571 A B) (@lem7684570 A B)). Qed.
Lemma lem7684574 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term197 A B.
Proof. exact (EQ_MP (@lem7684573 A B) (@lem7684347 A B x h1)). Qed.
Lemma lem7684582 {A B : Type'} (r : nat) : (term450 A B r) = (term450 A B r).
Proof. exact (eq_refl (term450 A B r)). Qed.
Lemma lem7684583 {A B : Type'} : (term447 A B) = (term447 A B).
Proof. exact (fun_ext (fun r : nat => @lem7684582 A B r)). Qed.
Lemma lem7684584 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7684586 {A B : Type'} : (term461 A B) = (term461 A B).
Proof. exact (MK_COMB (@lem7684584) (@lem7684583 A B)). Qed.
Lemma lem7684587 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term461 A B.
Proof. exact (EQ_MP (@lem7684586 A B) (@lem7684349 A B x h1)). Qed.
Lemma lem7684653 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term258 A B x x') = (term258 A B x x').
Proof. exact (eq_refl (term258 A B x x')). Qed.
Lemma lem7684654 {A B : Type'} (x : finite_diff A B) : (term264 A B x) = (term264 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7684653 A B x x')). Qed.
Lemma lem7684655 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7684657 {A B : Type'} (x : finite_diff A B) : (term265 A B x) = (term265 A B x).
Proof. exact (MK_COMB (@lem7684655) (@lem7684654 A B x)). Qed.
Lemma lem7684658 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term265 A B x.
Proof. exact (EQ_MP (@lem7684657 A B x) (@lem7684357 A B x h1)). Qed.
Lemma lem7684693 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7684694 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7684693 A B a)). Qed.
Lemma lem7684695 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7684697 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7684695 A B) (@lem7684694 A B)). Qed.
Lemma lem7684698 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term197 A B.
Proof. exact (EQ_MP (@lem7684697 A B) (@lem7684367 A B x h1)). Qed.
Lemma lem7684706 {A B : Type'} (r : nat) : (term480 A B r) = (term480 A B r).
Proof. exact (eq_refl (term480 A B r)). Qed.
Lemma lem7684707 {A B : Type'} : (term477 A B) = (term477 A B).
Proof. exact (fun_ext (fun r : nat => @lem7684706 A B r)). Qed.
Lemma lem7684708 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7684710 {A B : Type'} : (term491 A B) = (term491 A B).
Proof. exact (MK_COMB (@lem7684708) (@lem7684707 A B)). Qed.
Lemma lem7684711 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term491 A B.
Proof. exact (EQ_MP (@lem7684710 A B) (@lem7684369 A B x h1)). Qed.
Lemma lem7684777 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term209 A B x x') = (term209 A B x x').
Proof. exact (eq_refl (term209 A B x x')). Qed.
Lemma lem7684778 {A B : Type'} (x : finite_diff A B) : (term217 A B x) = (term217 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7684777 A B x x')). Qed.
Lemma lem7684779 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7684781 {A B : Type'} (x : finite_diff A B) : (term218 A B x) = (term218 A B x).
Proof. exact (MK_COMB (@lem7684779) (@lem7684778 A B x)). Qed.
Lemma lem7684782 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term218 A B x.
Proof. exact (EQ_MP (@lem7684781 A B x) (@lem7684381 A B x h1)). Qed.
Lemma lem7684817 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7684818 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7684817 A B a)). Qed.
Lemma lem7684819 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7684821 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7684819 A B) (@lem7684818 A B)). Qed.
Lemma lem7684822 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term197 A B.
Proof. exact (EQ_MP (@lem7684821 A B) (@lem7684391 A B x h1)). Qed.
Lemma lem7684830 {A B : Type'} (r : nat) : (term450 A B r) = (term450 A B r).
Proof. exact (eq_refl (term450 A B r)). Qed.
Lemma lem7684831 {A B : Type'} : (term447 A B) = (term447 A B).
Proof. exact (fun_ext (fun r : nat => @lem7684830 A B r)). Qed.
Lemma lem7684832 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7684834 {A B : Type'} : (term461 A B) = (term461 A B).
Proof. exact (MK_COMB (@lem7684832) (@lem7684831 A B)). Qed.
Lemma lem7684835 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term461 A B.
Proof. exact (EQ_MP (@lem7684834 A B) (@lem7684393 A B x h1)). Qed.
Lemma lem7684901 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term258 A B x x') = (term258 A B x x').
Proof. exact (eq_refl (term258 A B x x')). Qed.
Lemma lem7684902 {A B : Type'} (x : finite_diff A B) : (term264 A B x) = (term264 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7684901 A B x x')). Qed.
Lemma lem7684903 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7684905 {A B : Type'} (x : finite_diff A B) : (term265 A B x) = (term265 A B x).
Proof. exact (MK_COMB (@lem7684903) (@lem7684902 A B x)). Qed.
Lemma lem7684906 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term265 A B x.
Proof. exact (EQ_MP (@lem7684905 A B x) (@lem7684401 A B x h1)). Qed.
Lemma lem7684941 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7684942 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7684941 A B a)). Qed.
Lemma lem7684943 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7684945 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7684943 A B) (@lem7684942 A B)). Qed.
Lemma lem7684946 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term197 A B.
Proof. exact (EQ_MP (@lem7684945 A B) (@lem7684411 A B x h1)). Qed.
Lemma lem7684954 {A B : Type'} (r : nat) : (term480 A B r) = (term480 A B r).
Proof. exact (eq_refl (term480 A B r)). Qed.
Lemma lem7684955 {A B : Type'} : (term477 A B) = (term477 A B).
Proof. exact (fun_ext (fun r : nat => @lem7684954 A B r)). Qed.
Lemma lem7684956 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7684958 {A B : Type'} : (term491 A B) = (term491 A B).
Proof. exact (MK_COMB (@lem7684956) (@lem7684955 A B)). Qed.
Lemma lem7684959 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term491 A B.
Proof. exact (EQ_MP (@lem7684958 A B) (@lem7684413 A B x h1)). Qed.
Lemma lem7685025 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term209 A B x x') = (term209 A B x x').
Proof. exact (eq_refl (term209 A B x x')). Qed.
Lemma lem7685026 {A B : Type'} (x : finite_diff A B) : (term217 A B x) = (term217 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7685025 A B x x')). Qed.
Lemma lem7685027 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7685029 {A B : Type'} (x : finite_diff A B) : (term218 A B x) = (term218 A B x).
Proof. exact (MK_COMB (@lem7685027) (@lem7685026 A B x)). Qed.
Lemma lem7685030 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term218 A B x.
Proof. exact (EQ_MP (@lem7685029 A B x) (@lem7684429 A B x h1)). Qed.
Lemma lem7685065 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7685066 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7685065 A B a)). Qed.
Lemma lem7685067 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7685069 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7685067 A B) (@lem7685066 A B)). Qed.
Lemma lem7685070 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term197 A B.
Proof. exact (EQ_MP (@lem7685069 A B) (@lem7684439 A B x h1)). Qed.
Lemma lem7685078 {A B : Type'} (r : nat) : (term450 A B r) = (term450 A B r).
Proof. exact (eq_refl (term450 A B r)). Qed.
Lemma lem7685079 {A B : Type'} : (term447 A B) = (term447 A B).
Proof. exact (fun_ext (fun r : nat => @lem7685078 A B r)). Qed.
Lemma lem7685080 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7685082 {A B : Type'} : (term461 A B) = (term461 A B).
Proof. exact (MK_COMB (@lem7685080) (@lem7685079 A B)). Qed.
Lemma lem7685083 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term461 A B.
Proof. exact (EQ_MP (@lem7685082 A B) (@lem7684441 A B x h1)). Qed.
Lemma lem7685149 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term258 A B x x') = (term258 A B x x').
Proof. exact (eq_refl (term258 A B x x')). Qed.
Lemma lem7685150 {A B : Type'} (x : finite_diff A B) : (term264 A B x) = (term264 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7685149 A B x x')). Qed.
Lemma lem7685151 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7685153 {A B : Type'} (x : finite_diff A B) : (term265 A B x) = (term265 A B x).
Proof. exact (MK_COMB (@lem7685151) (@lem7685150 A B x)). Qed.
Lemma lem7685154 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term265 A B x.
Proof. exact (EQ_MP (@lem7685153 A B x) (@lem7684449 A B x h1)). Qed.
Lemma lem7685189 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7685190 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7685189 A B a)). Qed.
Lemma lem7685191 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7685193 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7685191 A B) (@lem7685190 A B)). Qed.
Lemma lem7685194 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term197 A B.
Proof. exact (EQ_MP (@lem7685193 A B) (@lem7684459 A B x h1)). Qed.
Lemma lem7685202 {A B : Type'} (r : nat) : (term480 A B r) = (term480 A B r).
Proof. exact (eq_refl (term480 A B r)). Qed.
Lemma lem7685203 {A B : Type'} : (term477 A B) = (term477 A B).
Proof. exact (fun_ext (fun r : nat => @lem7685202 A B r)). Qed.
Lemma lem7685204 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7685206 {A B : Type'} : (term491 A B) = (term491 A B).
Proof. exact (MK_COMB (@lem7685204) (@lem7685203 A B)). Qed.
Lemma lem7685207 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term491 A B.
Proof. exact (EQ_MP (@lem7685206 A B) (@lem7684461 A B x h1)). Qed.
Lemma lem7685273 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term209 A B x x') = (term209 A B x x').
Proof. exact (eq_refl (term209 A B x x')). Qed.
Lemma lem7685274 {A B : Type'} (x : finite_diff A B) : (term217 A B x) = (term217 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7685273 A B x x')). Qed.
Lemma lem7685275 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7685277 {A B : Type'} (x : finite_diff A B) : (term218 A B x) = (term218 A B x).
Proof. exact (MK_COMB (@lem7685275) (@lem7685274 A B x)). Qed.
Lemma lem7685278 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term218 A B x.
Proof. exact (EQ_MP (@lem7685277 A B x) (@lem7684473 A B x h1)). Qed.
Lemma lem7685313 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7685314 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7685313 A B a)). Qed.
Lemma lem7685315 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7685317 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7685315 A B) (@lem7685314 A B)). Qed.
Lemma lem7685318 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term197 A B.
Proof. exact (EQ_MP (@lem7685317 A B) (@lem7684483 A B x h1)). Qed.
Lemma lem7685326 {A B : Type'} (r : nat) : (term450 A B r) = (term450 A B r).
Proof. exact (eq_refl (term450 A B r)). Qed.
Lemma lem7685327 {A B : Type'} : (term447 A B) = (term447 A B).
Proof. exact (fun_ext (fun r : nat => @lem7685326 A B r)). Qed.
Lemma lem7685328 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7685330 {A B : Type'} : (term461 A B) = (term461 A B).
Proof. exact (MK_COMB (@lem7685328) (@lem7685327 A B)). Qed.
Lemma lem7685331 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term461 A B.
Proof. exact (EQ_MP (@lem7685330 A B) (@lem7684485 A B x h1)). Qed.
Lemma lem7685397 {A B : Type'} (x : finite_diff A B) (x' : nat) : (term258 A B x x') = (term258 A B x x').
Proof. exact (eq_refl (term258 A B x x')). Qed.
Lemma lem7685398 {A B : Type'} (x : finite_diff A B) : (term264 A B x) = (term264 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7685397 A B x x')). Qed.
Lemma lem7685399 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7685401 {A B : Type'} (x : finite_diff A B) : (term265 A B x) = (term265 A B x).
Proof. exact (MK_COMB (@lem7685399) (@lem7685398 A B x)). Qed.
Lemma lem7685402 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term265 A B x.
Proof. exact (EQ_MP (@lem7685401 A B x) (@lem7684493 A B x h1)). Qed.
Lemma lem7685437 {A B : Type'} (a : finite_diff A B) : ((term195 A B a) = a) = ((term195 A B a) = a).
Proof. exact (eq_refl ((term195 A B a) = a)). Qed.
Lemma lem7685438 {A B : Type'} : (term196 A B) = (term196 A B).
Proof. exact (fun_ext (fun a : finite_diff A B => @lem7685437 A B a)). Qed.
Lemma lem7685439 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7685441 {A B : Type'} : (term197 A B) = (term197 A B).
Proof. exact (MK_COMB (@lem7685439 A B) (@lem7685438 A B)). Qed.
Lemma lem7685442 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term197 A B.
Proof. exact (EQ_MP (@lem7685441 A B) (@lem7684503 A B x h1)). Qed.
Lemma lem7685450 {A B : Type'} (r : nat) : (term480 A B r) = (term480 A B r).
Proof. exact (eq_refl (term480 A B r)). Qed.
Lemma lem7685451 {A B : Type'} : (term477 A B) = (term477 A B).
Proof. exact (fun_ext (fun r : nat => @lem7685450 A B r)). Qed.
Lemma lem7685452 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7685454 {A B : Type'} : (term491 A B) = (term491 A B).
Proof. exact (MK_COMB (@lem7685452) (@lem7685451 A B)). Qed.
Lemma lem7685455 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term491 A B.
Proof. exact (EQ_MP (@lem7685454 A B) (@lem7684505 A B x h1)). Qed.
Lemma lem7685502 {A B : Type'} (_98803 : nat) (x : finite_diff A B) (h1 : term600 A B x) : term986 A B x _98803.
Proof. exact (@lem7684534 A B x h1 _98803). Qed.
Lemma lem7685503 {A B : Type'} (x : finite_diff A B) (_98803 : nat) : (term986 A B x _98803) = (term209 A B x _98803).
Proof. exact (eq_refl (term986 A B x _98803)). Qed.
Lemma lem7685514 {A B : Type'} (_98807 : finite_diff A B) (x : finite_diff A B) (h1 : term600 A B x) : term987 A B _98807.
Proof. exact (@lem7684574 A B x h1 _98807). Qed.
Lemma lem7685515 {A B : Type'} (_98807 : finite_diff A B) : (term987 A B _98807) = ((term195 A B _98807) = _98807).
Proof. exact (eq_refl (term987 A B _98807)). Qed.
Lemma lem7685517 {A B : Type'} (_98808 : nat) (x : finite_diff A B) (h1 : term600 A B x) : term449 A B _98808.
Proof. exact (@lem7684587 A B x h1 _98808). Qed.
Lemma lem7685518 {A B : Type'} (_98808 : nat) : (term449 A B _98808) = (term450 A B _98808).
Proof. exact (eq_refl (term449 A B _98808)). Qed.
Lemma lem7685532 {A B : Type'} (_98813 : nat) (x : finite_diff A B) (h1 : term629 A B x) : term988 A B x _98813.
Proof. exact (@lem7684658 A B x h1 _98813). Qed.
Lemma lem7685533 {A B : Type'} (x : finite_diff A B) (_98813 : nat) : (term988 A B x _98813) = (term258 A B x _98813).
Proof. exact (eq_refl (term988 A B x _98813)). Qed.
Lemma lem7685544 {A B : Type'} (_98817 : finite_diff A B) (x : finite_diff A B) (h1 : term629 A B x) : term987 A B _98817.
Proof. exact (@lem7684698 A B x h1 _98817). Qed.
Lemma lem7685545 {A B : Type'} (_98817 : finite_diff A B) : (term987 A B _98817) = ((term195 A B _98817) = _98817).
Proof. exact (eq_refl (term987 A B _98817)). Qed.
Lemma lem7685547 {A B : Type'} (_98818 : nat) (x : finite_diff A B) (h1 : term629 A B x) : term479 A B _98818.
Proof. exact (@lem7684711 A B x h1 _98818). Qed.
Lemma lem7685548 {A B : Type'} (_98818 : nat) : (term479 A B _98818) = (term480 A B _98818).
Proof. exact (eq_refl (term479 A B _98818)). Qed.
Lemma lem7685562 {A B : Type'} (_98823 : nat) (x : finite_diff A B) (h1 : term688 A B x) : term986 A B x _98823.
Proof. exact (@lem7684782 A B x h1 _98823). Qed.
Lemma lem7685563 {A B : Type'} (x : finite_diff A B) (_98823 : nat) : (term986 A B x _98823) = (term209 A B x _98823).
Proof. exact (eq_refl (term986 A B x _98823)). Qed.
Lemma lem7685574 {A B : Type'} (_98827 : finite_diff A B) (x : finite_diff A B) (h1 : term688 A B x) : term987 A B _98827.
Proof. exact (@lem7684822 A B x h1 _98827). Qed.
Lemma lem7685575 {A B : Type'} (_98827 : finite_diff A B) : (term987 A B _98827) = ((term195 A B _98827) = _98827).
Proof. exact (eq_refl (term987 A B _98827)). Qed.
Lemma lem7685577 {A B : Type'} (_98828 : nat) (x : finite_diff A B) (h1 : term688 A B x) : term449 A B _98828.
Proof. exact (@lem7684835 A B x h1 _98828). Qed.
Lemma lem7685578 {A B : Type'} (_98828 : nat) : (term449 A B _98828) = (term450 A B _98828).
Proof. exact (eq_refl (term449 A B _98828)). Qed.
Lemma lem7685592 {A B : Type'} (_98833 : nat) (x : finite_diff A B) (h1 : term711 A B x) : term988 A B x _98833.
Proof. exact (@lem7684906 A B x h1 _98833). Qed.
Lemma lem7685593 {A B : Type'} (x : finite_diff A B) (_98833 : nat) : (term988 A B x _98833) = (term258 A B x _98833).
Proof. exact (eq_refl (term988 A B x _98833)). Qed.
Lemma lem7685604 {A B : Type'} (_98837 : finite_diff A B) (x : finite_diff A B) (h1 : term711 A B x) : term987 A B _98837.
Proof. exact (@lem7684946 A B x h1 _98837). Qed.
Lemma lem7685605 {A B : Type'} (_98837 : finite_diff A B) : (term987 A B _98837) = ((term195 A B _98837) = _98837).
Proof. exact (eq_refl (term987 A B _98837)). Qed.
Lemma lem7685607 {A B : Type'} (_98838 : nat) (x : finite_diff A B) (h1 : term711 A B x) : term479 A B _98838.
Proof. exact (@lem7684959 A B x h1 _98838). Qed.
Lemma lem7685608 {A B : Type'} (_98838 : nat) : (term479 A B _98838) = (term480 A B _98838).
Proof. exact (eq_refl (term479 A B _98838)). Qed.
Lemma lem7685622 {A B : Type'} (_98843 : nat) (x : finite_diff A B) (h1 : term798 A B x) : term986 A B x _98843.
Proof. exact (@lem7685030 A B x h1 _98843). Qed.
Lemma lem7685623 {A B : Type'} (x : finite_diff A B) (_98843 : nat) : (term986 A B x _98843) = (term209 A B x _98843).
Proof. exact (eq_refl (term986 A B x _98843)). Qed.
Lemma lem7685634 {A B : Type'} (_98847 : finite_diff A B) (x : finite_diff A B) (h1 : term798 A B x) : term987 A B _98847.
Proof. exact (@lem7685070 A B x h1 _98847). Qed.
Lemma lem7685635 {A B : Type'} (_98847 : finite_diff A B) : (term987 A B _98847) = ((term195 A B _98847) = _98847).
Proof. exact (eq_refl (term987 A B _98847)). Qed.
Lemma lem7685637 {A B : Type'} (_98848 : nat) (x : finite_diff A B) (h1 : term798 A B x) : term449 A B _98848.
Proof. exact (@lem7685083 A B x h1 _98848). Qed.
Lemma lem7685638 {A B : Type'} (_98848 : nat) : (term449 A B _98848) = (term450 A B _98848).
Proof. exact (eq_refl (term449 A B _98848)). Qed.
Lemma lem7685652 {A B : Type'} (_98853 : nat) (x : finite_diff A B) (h1 : term821 A B x) : term988 A B x _98853.
Proof. exact (@lem7685154 A B x h1 _98853). Qed.
Lemma lem7685653 {A B : Type'} (x : finite_diff A B) (_98853 : nat) : (term988 A B x _98853) = (term258 A B x _98853).
Proof. exact (eq_refl (term988 A B x _98853)). Qed.
Lemma lem7685664 {A B : Type'} (_98857 : finite_diff A B) (x : finite_diff A B) (h1 : term821 A B x) : term987 A B _98857.
Proof. exact (@lem7685194 A B x h1 _98857). Qed.
Lemma lem7685665 {A B : Type'} (_98857 : finite_diff A B) : (term987 A B _98857) = ((term195 A B _98857) = _98857).
Proof. exact (eq_refl (term987 A B _98857)). Qed.
Lemma lem7685667 {A B : Type'} (_98858 : nat) (x : finite_diff A B) (h1 : term821 A B x) : term479 A B _98858.
Proof. exact (@lem7685207 A B x h1 _98858). Qed.
Lemma lem7685668 {A B : Type'} (_98858 : nat) : (term479 A B _98858) = (term480 A B _98858).
Proof. exact (eq_refl (term479 A B _98858)). Qed.
Lemma lem7685682 {A B : Type'} (_98863 : nat) (x : finite_diff A B) (h1 : term876 A B x) : term986 A B x _98863.
Proof. exact (@lem7685278 A B x h1 _98863). Qed.
Lemma lem7685683 {A B : Type'} (x : finite_diff A B) (_98863 : nat) : (term986 A B x _98863) = (term209 A B x _98863).
Proof. exact (eq_refl (term986 A B x _98863)). Qed.
Lemma lem7685694 {A B : Type'} (_98867 : finite_diff A B) (x : finite_diff A B) (h1 : term876 A B x) : term987 A B _98867.
Proof. exact (@lem7685318 A B x h1 _98867). Qed.
Lemma lem7685695 {A B : Type'} (_98867 : finite_diff A B) : (term987 A B _98867) = ((term195 A B _98867) = _98867).
Proof. exact (eq_refl (term987 A B _98867)). Qed.
Lemma lem7685697 {A B : Type'} (_98868 : nat) (x : finite_diff A B) (h1 : term876 A B x) : term449 A B _98868.
Proof. exact (@lem7685331 A B x h1 _98868). Qed.
Lemma lem7685698 {A B : Type'} (_98868 : nat) : (term449 A B _98868) = (term450 A B _98868).
Proof. exact (eq_refl (term449 A B _98868)). Qed.
Lemma lem7685712 {A B : Type'} (_98873 : nat) (x : finite_diff A B) (h1 : term899 A B x) : term988 A B x _98873.
Proof. exact (@lem7685402 A B x h1 _98873). Qed.
Lemma lem7685713 {A B : Type'} (x : finite_diff A B) (_98873 : nat) : (term988 A B x _98873) = (term258 A B x _98873).
Proof. exact (eq_refl (term988 A B x _98873)). Qed.
Lemma lem7685724 {A B : Type'} (_98877 : finite_diff A B) (x : finite_diff A B) (h1 : term899 A B x) : term987 A B _98877.
Proof. exact (@lem7685442 A B x h1 _98877). Qed.
Lemma lem7685725 {A B : Type'} (_98877 : finite_diff A B) : (term987 A B _98877) = ((term195 A B _98877) = _98877).
Proof. exact (eq_refl (term987 A B _98877)). Qed.
Lemma lem7685727 {A B : Type'} (_98878 : nat) (x : finite_diff A B) (h1 : term899 A B x) : term479 A B _98878.
Proof. exact (@lem7685455 A B x h1 _98878). Qed.
Lemma lem7685728 {A B : Type'} (_98878 : nat) : (term479 A B _98878) = (term480 A B _98878).
Proof. exact (eq_refl (term479 A B _98878)). Qed.
Lemma lem7685753 {A B : Type'} (_98803 : nat) (x : finite_diff A B) (h1 : term600 A B x) : term209 A B x _98803.
Proof. exact (EQ_MP (@lem7685503 A B x _98803) (@lem7685502 A B _98803 x h1)). Qed.
Lemma lem7685775 {A B : Type'} (_98808 : nat) (x : finite_diff A B) (h1 : term600 A B x) : term450 A B _98808.
Proof. exact (EQ_MP (@lem7685518 A B _98808) (@lem7685517 A B _98808 x h1)). Qed.
Lemma lem7685807 {A B : Type'} (_98813 : nat) (x : finite_diff A B) (h1 : term629 A B x) : term258 A B x _98813.
Proof. exact (EQ_MP (@lem7685533 A B x _98813) (@lem7685532 A B _98813 x h1)). Qed.
Lemma lem7685829 {A B : Type'} (_98818 : nat) (x : finite_diff A B) (h1 : term629 A B x) : term480 A B _98818.
Proof. exact (EQ_MP (@lem7685548 A B _98818) (@lem7685547 A B _98818 x h1)). Qed.
Lemma lem7685861 {A B : Type'} (_98823 : nat) (x : finite_diff A B) (h1 : term688 A B x) : term209 A B x _98823.
Proof. exact (EQ_MP (@lem7685563 A B x _98823) (@lem7685562 A B _98823 x h1)). Qed.
Lemma lem7685883 {A B : Type'} (_98828 : nat) (x : finite_diff A B) (h1 : term688 A B x) : term450 A B _98828.
Proof. exact (EQ_MP (@lem7685578 A B _98828) (@lem7685577 A B _98828 x h1)). Qed.
Lemma lem7685915 {A B : Type'} (_98833 : nat) (x : finite_diff A B) (h1 : term711 A B x) : term258 A B x _98833.
Proof. exact (EQ_MP (@lem7685593 A B x _98833) (@lem7685592 A B _98833 x h1)). Qed.
Lemma lem7685937 {A B : Type'} (_98838 : nat) (x : finite_diff A B) (h1 : term711 A B x) : term480 A B _98838.
Proof. exact (EQ_MP (@lem7685608 A B _98838) (@lem7685607 A B _98838 x h1)). Qed.
Lemma lem7685969 {A B : Type'} (_98843 : nat) (x : finite_diff A B) (h1 : term798 A B x) : term209 A B x _98843.
Proof. exact (EQ_MP (@lem7685623 A B x _98843) (@lem7685622 A B _98843 x h1)). Qed.
Lemma lem7685991 {A B : Type'} (_98848 : nat) (x : finite_diff A B) (h1 : term798 A B x) : term450 A B _98848.
Proof. exact (EQ_MP (@lem7685638 A B _98848) (@lem7685637 A B _98848 x h1)). Qed.
Lemma lem7686023 {A B : Type'} (_98853 : nat) (x : finite_diff A B) (h1 : term821 A B x) : term258 A B x _98853.
Proof. exact (EQ_MP (@lem7685653 A B x _98853) (@lem7685652 A B _98853 x h1)). Qed.
Lemma lem7686045 {A B : Type'} (_98858 : nat) (x : finite_diff A B) (h1 : term821 A B x) : term480 A B _98858.
Proof. exact (EQ_MP (@lem7685668 A B _98858) (@lem7685667 A B _98858 x h1)). Qed.
Lemma lem7686077 {A B : Type'} (_98863 : nat) (x : finite_diff A B) (h1 : term876 A B x) : term209 A B x _98863.
Proof. exact (EQ_MP (@lem7685683 A B x _98863) (@lem7685682 A B _98863 x h1)). Qed.
Lemma lem7686099 {A B : Type'} (_98868 : nat) (x : finite_diff A B) (h1 : term876 A B x) : term450 A B _98868.
Proof. exact (EQ_MP (@lem7685698 A B _98868) (@lem7685697 A B _98868 x h1)). Qed.
Lemma lem7686131 {A B : Type'} (_98873 : nat) (x : finite_diff A B) (h1 : term899 A B x) : term258 A B x _98873.
Proof. exact (EQ_MP (@lem7685713 A B x _98873) (@lem7685712 A B _98873 x h1)). Qed.
Lemma lem7686153 {A B : Type'} (_98878 : nat) (x : finite_diff A B) (h1 : term899 A B x) : term480 A B _98878.
Proof. exact (EQ_MP (@lem7685728 A B _98878) (@lem7685727 A B _98878 x h1)). Qed.
Lemma lem7686228 {A B : Type'} : (@dest_finite_diff A B) = (@dest_finite_diff A B).
Proof. exact (eq_refl (@dest_finite_diff A B)). Qed.
Lemma lem7686229 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) (h1 : _98895 = _98896) : _98895 = _98896.
Proof. exact (h1). Qed.
Lemma lem7686230 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) (h1 : _98895 = _98896) : (@dest_finite_diff A B _98895) = (@dest_finite_diff A B _98896).
Proof. exact (MK_COMB (@lem7686228 A B) (@lem7686229 A B _98895 _98896 h1)). Qed.
Lemma lem7686231 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : term989 A B _98895 _98896.
Proof. exact (fun h0 : _98895 = _98896 => @lem7686230 A B _98895 _98896 h0). Qed.
Lemma lem7686233 (a : Prop) (b : Prop) : (a -> b) = (term990 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7686234 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : (term989 A B _98895 _98896) = (term991 A B _98895 _98896).
Proof. exact (@lem7686233 (_98895 = _98896) ((@dest_finite_diff A B _98895) = (@dest_finite_diff A B _98896))). Qed.
Lemma lem7686235 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : term991 A B _98895 _98896.
Proof. exact (EQ_MP (@lem7686234 A B _98895 _98896) (@lem7686231 A B _98895 _98896)). Qed.
Lemma lem7686331 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term992 A B x y z.
Proof. exact (@lem21385 (finite_diff A B) x y z). Qed.
Lemma lem7686337 {A B : Type'} (_98807 : finite_diff A B) (x : finite_diff A B) (h1 : term600 A B x) : (term195 A B _98807) = _98807.
Proof. exact (EQ_MP (@lem7685515 A B _98807) (@lem7685514 A B _98807 x h1)). Qed.
Lemma lem7686338 {A B : Type'} (_98807 : finite_diff A B) (x : finite_diff A B) (h1 : term600 A B x) : (term195 A B _98807) = _98807.
Proof. exact (@lem7686337 A B _98807 x h1). Qed.
Lemma lem7686339 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : (term195 A B x) = x.
Proof. exact (@lem7686338 A B x x h1). Qed.
Lemma lem7686340 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7686339 A B x h1). Qed.
Lemma lem7686342 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7686343 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7686342 ((term195 A B x) = x)). Qed.
Lemma lem7686344 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7686343 A B x) (@lem7686340 A B x h1)). Qed.
Lemma lem7686346 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem21386 (finite_diff A B) x). Qed.
Lemma lem7686347 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem7686346 A B x). Qed.
Lemma lem7686348 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (@lem7686347 A B (term195 A B x)). Qed.
Lemma lem7686349 {A B : Type'} (x : finite_diff A B) : term996 A B x.
Proof. exact (fun h0 : term997 A B x => @lem7686348 A B x). Qed.
Lemma lem7686351 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7686352 {A B : Type'} (x : finite_diff A B) : (term996 A B x) = ((term195 A B x) = (term195 A B x)).
Proof. exact (@lem7686351 ((term195 A B x) = (term195 A B x))). Qed.
Lemma lem7686353 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (EQ_MP (@lem7686352 A B x) (@lem7686349 A B x)). Qed.
Lemma lem7686371 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7686372 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term998 A B x y z) = (term999 A B y x z).
Proof. exact (@lem7686371 (y = z) (term1000 A B x z)). Qed.
Lemma lem7686382 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1001 A B x y) = (term1001 A B x y).
Proof. exact (eq_refl (term1001 A B x y)). Qed.
Lemma lem7686383 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1002 A B y x z).
Proof. exact (MK_COMB (@lem7686382 A B x y) (@lem7686372 A B y x z)). Qed.
Lemma lem7686387 (q : Prop) (p : Prop) (r : Prop) : (term1003 p q r) = (term1003 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7686388 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1002 A B y x z) = (term1004 A B y x z).
Proof. exact (@lem7686387 (y = z) (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7686410 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (TRANS (@lem7686383 A B y x z) (@lem7686388 A B y x z)). Qed.
Lemma lem7686411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7686412 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1005 A B x y z) = (term1006 A B y x z).
Proof. exact (MK_COMB (@lem7686411) (@lem7686410 A B y x z)). Qed.
Lemma lem7686434 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1004 A B y x z).
Proof. exact (eq_refl (term1004 A B y x z)). Qed.
Lemma lem7686435 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = ((term1004 A B y x z) = (term1004 A B y x z)).
Proof. exact (MK_COMB (@lem7686412 A B y x z) (@lem7686434 A B y x z)). Qed.
Lemma lem7686437 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7686438 (x : Prop) : (x = x) = True.
Proof. exact (@lem7686437 Prop x). Qed.
Lemma lem7686439 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term1004 A B y x z) = (term1004 A B y x z)) = True.
Proof. exact (@lem7686438 (term1004 A B y x z)). Qed.
Lemma lem7686440 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = True.
Proof. exact (TRANS (@lem7686435 A B y x z) (@lem7686439 A B y x z)). Qed.
Lemma lem7686441 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : True = ((term992 A B x y z) = (term1004 A B y x z)).
Proof. exact (SYM (@lem7686440 A B y x z)). Qed.
Lemma lem7686442 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (EQ_MP (@lem7686441 A B y x z) (@lem0)). Qed.
Lemma lem7686443 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : term1004 A B y x z.
Proof. exact (EQ_MP (@lem7686442 A B y x z) (@lem7686331 A B x y z)). Qed.
Lemma lem7686445 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7686446 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1008 A B x y z).
Proof. exact (@lem7686445 (term1009 A B y x z) (y = z)). Qed.
Lemma lem7686448 (a : Prop) (b : Prop) : (term1010 a b) = (term1011 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7686449 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1013 A B y x z).
Proof. exact (@lem7686448 (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7686451 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7686452 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1015 A B x y) = (x = y).
Proof. exact (@lem7686451 (x = y)). Qed.
Lemma lem7686453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7686454 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1016 A B x y) = (term1017 A B x y).
Proof. exact (MK_COMB (@lem7686453) (@lem7686452 A B x y)). Qed.
Lemma lem7686456 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7686457 {A B : Type'} (x : finite_diff A B) (z : finite_diff A B) : (term1015 A B x z) = (x = z).
Proof. exact (@lem7686456 (x = z)). Qed.
Lemma lem7686458 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1013 A B y x z) = (term1018 A B y x z).
Proof. exact (MK_COMB (@lem7686454 A B x y) (@lem7686457 A B x z)). Qed.
Lemma lem7686459 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1018 A B y x z).
Proof. exact (TRANS (@lem7686449 A B y x z) (@lem7686458 A B y x z)). Qed.
Lemma lem7686460 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7686461 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1019 A B y x z) = (term1020 A B y x z).
Proof. exact (MK_COMB (@lem7686460) (@lem7686459 A B y x z)). Qed.
Lemma lem7686462 {A B : Type'} (y : finite_diff A B) (z : finite_diff A B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7686463 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1008 A B x y z) = (term1021 A B x y z).
Proof. exact (MK_COMB (@lem7686461 A B y x z) (@lem7686462 A B y z)). Qed.
Lemma lem7686464 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1021 A B x y z).
Proof. exact (TRANS (@lem7686446 A B x y z) (@lem7686463 A B x y z)). Qed.
Lemma lem7686466 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term1022 A B x.
Proof. exact (conj (@lem7686344 A B x h1) (@lem7686353 A B x)). Qed.
Lemma lem7686468 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (EQ_MP (@lem7686464 A B x y z) (@lem7686443 A B y x z)). Qed.
Lemma lem7686469 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (@lem7686468 A B x y z). Qed.
Lemma lem7686470 {A B : Type'} (x : finite_diff A B) : term1023 A B x.
Proof. exact (@lem7686469 A B (term195 A B x) x (term195 A B x)). Qed.
Lemma lem7686473 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : x = (term195 A B x).
Proof. exact (@lem7686470 A B x (@lem7686466 A B x h1)). Qed.
Lemma lem7686474 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term1024 A B x.
Proof. exact (fun h0 : term1025 A B x => @lem7686473 A B x h1). Qed.
Lemma lem7686476 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7686477 {A B : Type'} (x : finite_diff A B) : (term1024 A B x) = (x = (term195 A B x)).
Proof. exact (@lem7686476 (x = (term195 A B x))). Qed.
Lemma lem7686478 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : x = (term195 A B x).
Proof. exact (EQ_MP (@lem7686477 A B x) (@lem7686474 A B x h1)). Qed.
Lemma lem7686480 {A B : Type'} (_98807 : finite_diff A B) (x : finite_diff A B) (h1 : term600 A B x) : (term195 A B _98807) = _98807.
Proof. exact (EQ_MP (@lem7685515 A B _98807) (@lem7685514 A B _98807 x h1)). Qed.
Lemma lem7686481 {A B : Type'} (_98807 : finite_diff A B) (x : finite_diff A B) (h1 : term600 A B x) : (term195 A B _98807) = _98807.
Proof. exact (@lem7686480 A B _98807 x h1). Qed.
Lemma lem7686482 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : (term195 A B x) = x.
Proof. exact (@lem7686481 A B x x h1). Qed.
Lemma lem7686483 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7686482 A B x h1). Qed.
Lemma lem7686485 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7686486 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7686485 ((term195 A B x) = x)). Qed.
Lemma lem7686487 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7686486 A B x) (@lem7686483 A B x h1)). Qed.
Lemma lem7686493 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7686494 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : (term991 A B _98895 _98896) = (term1026 A B _98895 _98896).
Proof. exact (@lem7686493 ((@dest_finite_diff A B _98895) = (@dest_finite_diff A B _98896)) (term1000 A B _98895 _98896)). Qed.
Lemma lem7686504 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7686505 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : (term1027 A B _98895 _98896) = (term1028 A B _98895 _98896).
Proof. exact (MK_COMB (@lem7686504) (@lem7686494 A B _98895 _98896)). Qed.
Lemma lem7686515 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : (term1026 A B _98895 _98896) = (term1026 A B _98895 _98896).
Proof. exact (eq_refl (term1026 A B _98895 _98896)). Qed.
Lemma lem7686516 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : ((term991 A B _98895 _98896) = (term1026 A B _98895 _98896)) = ((term1026 A B _98895 _98896) = (term1026 A B _98895 _98896)).
Proof. exact (MK_COMB (@lem7686505 A B _98895 _98896) (@lem7686515 A B _98895 _98896)). Qed.
Lemma lem7686518 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7686519 (x : Prop) : (x = x) = True.
Proof. exact (@lem7686518 Prop x). Qed.
Lemma lem7686520 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : ((term1026 A B _98895 _98896) = (term1026 A B _98895 _98896)) = True.
Proof. exact (@lem7686519 (term1026 A B _98895 _98896)). Qed.
Lemma lem7686521 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : ((term991 A B _98895 _98896) = (term1026 A B _98895 _98896)) = True.
Proof. exact (TRANS (@lem7686516 A B _98895 _98896) (@lem7686520 A B _98895 _98896)). Qed.
Lemma lem7686522 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : True = ((term991 A B _98895 _98896) = (term1026 A B _98895 _98896)).
Proof. exact (SYM (@lem7686521 A B _98895 _98896)). Qed.
Lemma lem7686523 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : (term991 A B _98895 _98896) = (term1026 A B _98895 _98896).
Proof. exact (EQ_MP (@lem7686522 A B _98895 _98896) (@lem0)). Qed.
Lemma lem7686524 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : term1026 A B _98895 _98896.
Proof. exact (EQ_MP (@lem7686523 A B _98895 _98896) (@lem7686235 A B _98895 _98896)). Qed.
Lemma lem7686526 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7686527 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : (term1026 A B _98895 _98896) = (term1029 A B _98895 _98896).
Proof. exact (@lem7686526 (term1000 A B _98895 _98896) ((@dest_finite_diff A B _98895) = (@dest_finite_diff A B _98896))). Qed.
Lemma lem7686529 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7686530 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : (term1015 A B _98895 _98896) = (_98895 = _98896).
Proof. exact (@lem7686529 (_98895 = _98896)). Qed.
Lemma lem7686531 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7686532 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : (term1030 A B _98895 _98896) = (term1031 A B _98895 _98896).
Proof. exact (MK_COMB (@lem7686531) (@lem7686530 A B _98895 _98896)). Qed.
Lemma lem7686533 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : ((@dest_finite_diff A B _98895) = (@dest_finite_diff A B _98896)) = ((@dest_finite_diff A B _98895) = (@dest_finite_diff A B _98896)).
Proof. exact (eq_refl ((@dest_finite_diff A B _98895) = (@dest_finite_diff A B _98896))). Qed.
Lemma lem7686534 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : (term1029 A B _98895 _98896) = (term989 A B _98895 _98896).
Proof. exact (MK_COMB (@lem7686532 A B _98895 _98896) (@lem7686533 A B _98895 _98896)). Qed.
Lemma lem7686535 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : (term1026 A B _98895 _98896) = (term989 A B _98895 _98896).
Proof. exact (TRANS (@lem7686527 A B _98895 _98896) (@lem7686534 A B _98895 _98896)). Qed.
Lemma lem7686538 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : term989 A B _98895 _98896.
Proof. exact (EQ_MP (@lem7686535 A B _98895 _98896) (@lem7686524 A B _98895 _98896)). Qed.
Lemma lem7686539 {A B : Type'} (_98895 : finite_diff A B) (_98896 : finite_diff A B) : term989 A B _98895 _98896.
Proof. exact (@lem7686538 A B _98895 _98896). Qed.
Lemma lem7686540 {A B : Type'} (x : finite_diff A B) : term1032 A B x.
Proof. exact (@lem7686539 A B (term195 A B x) x). Qed.
Lemma lem7686543 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (@lem7686540 A B x (@lem7686487 A B x h1)). Qed.
Lemma lem7686544 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term1034 A B x.
Proof. exact (fun h0 : term1035 A B x => @lem7686543 A B x h1). Qed.
Lemma lem7686546 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7686547 {A B : Type'} (x : finite_diff A B) : (term1034 A B x) = ((term1033 A B x) = (@dest_finite_diff A B x)).
Proof. exact (@lem7686546 ((term1033 A B x) = (@dest_finite_diff A B x))). Qed.
Lemma lem7686548 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (EQ_MP (@lem7686547 A B x) (@lem7686544 A B x h1)). Qed.
Lemma lem7686550 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7686551 {A B : Type'} (_98808 : nat) : (term450 A B _98808) = (term1036 A B _98808).
Proof. exact (@lem7686550 (term1037 A B _98808) (term62 A B _98808)). Qed.
Lemma lem7686553 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7686554 {A B : Type'} (_98808 : nat) : (term1038 A B _98808) = ((term47 A B _98808) = _98808).
Proof. exact (@lem7686553 ((term47 A B _98808) = _98808)). Qed.
Lemma lem7686555 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7686556 {A B : Type'} (_98808 : nat) : (term1039 A B _98808) = (term1040 A B _98808).
Proof. exact (MK_COMB (@lem7686555) (@lem7686554 A B _98808)). Qed.
Lemma lem7686557 {A B : Type'} (_98808 : nat) : (term62 A B _98808) = (term62 A B _98808).
Proof. exact (eq_refl (term62 A B _98808)). Qed.
Lemma lem7686558 {A B : Type'} (_98808 : nat) : (term1036 A B _98808) = (term1041 A B _98808).
Proof. exact (MK_COMB (@lem7686556 A B _98808) (@lem7686557 A B _98808)). Qed.
Lemma lem7686559 {A B : Type'} (_98808 : nat) : (term450 A B _98808) = (term1041 A B _98808).
Proof. exact (TRANS (@lem7686551 A B _98808) (@lem7686558 A B _98808)). Qed.
Lemma lem7686562 {A B : Type'} (_98808 : nat) (x : finite_diff A B) (h1 : term600 A B x) : term1041 A B _98808.
Proof. exact (EQ_MP (@lem7686559 A B _98808) (@lem7685775 A B _98808 x h1)). Qed.
Lemma lem7686563 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term1042 A B x.
Proof. exact (@lem7686562 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7686566 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term1043 A B x.
Proof. exact (@lem7686563 A B x h1 (@lem7686548 A B x h1)). Qed.
Lemma lem7686567 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term1044 A B x.
Proof. exact (fun h0 : term1045 A B x => @lem7686566 A B x h1). Qed.
Lemma lem7686569 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7686570 {A B : Type'} (x : finite_diff A B) : (term1044 A B x) = (term1043 A B x).
Proof. exact (@lem7686569 (term1043 A B x)). Qed.
Lemma lem7686571 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term1043 A B x.
Proof. exact (EQ_MP (@lem7686570 A B x) (@lem7686567 A B x h1)). Qed.
Lemma lem7686573 (a : Prop) (b : Prop) : (term1046 a b) = (term1047 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7686574 {A B : Type'} (x : finite_diff A B) (_98803 : nat) : (term209 A B x _98803) = (term208 A B x _98803).
Proof. exact (@lem7686573 (x = (@mk_finite_diff A B _98803)) (term62 A B _98803)). Qed.
Lemma lem7686576 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7686577 {A B : Type'} (x : finite_diff A B) (_98803 : nat) : (term208 A B x _98803) = (term1048 A B x _98803).
Proof. exact (@lem7686576 (term63 A B x _98803)). Qed.
Lemma lem7686578 {A B : Type'} (x : finite_diff A B) (_98803 : nat) : (term209 A B x _98803) = (term1048 A B x _98803).
Proof. exact (TRANS (@lem7686574 A B x _98803) (@lem7686577 A B x _98803)). Qed.
Lemma lem7686580 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term1049 A B x.
Proof. exact (conj (@lem7686478 A B x h1) (@lem7686571 A B x h1)). Qed.
Lemma lem7686582 {A B : Type'} (_98803 : nat) (x : finite_diff A B) (h1 : term600 A B x) : term1048 A B x _98803.
Proof. exact (EQ_MP (@lem7686578 A B x _98803) (@lem7685753 A B _98803 x h1)). Qed.
Lemma lem7686583 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term1050 A B x.
Proof. exact (@lem7686582 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7686586 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : False.
Proof. exact (@lem7686583 A B x h1 (@lem7686580 A B x h1)). Qed.
Lemma lem7686587 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : term1051.
Proof. exact (fun h0 : ~ False => @lem7686586 A B x h1). Qed.
Lemma lem7686589 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7686590 : term1051 = False.
Proof. exact (@lem7686589 False). Qed.
Lemma lem7686591 {A B : Type'} (x : finite_diff A B) (h1 : term600 A B x) : False.
Proof. exact (EQ_MP (@lem7686590) (@lem7686587 A B x h1)). Qed.
Lemma lem7686646 {A B : Type'} : (@dest_finite_diff A B) = (@dest_finite_diff A B).
Proof. exact (eq_refl (@dest_finite_diff A B)). Qed.
Lemma lem7686647 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) (h1 : _98931 = _98932) : _98931 = _98932.
Proof. exact (h1). Qed.
Lemma lem7686648 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) (h1 : _98931 = _98932) : (@dest_finite_diff A B _98931) = (@dest_finite_diff A B _98932).
Proof. exact (MK_COMB (@lem7686646 A B) (@lem7686647 A B _98931 _98932 h1)). Qed.
Lemma lem7686649 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : term989 A B _98931 _98932.
Proof. exact (fun h0 : _98931 = _98932 => @lem7686648 A B _98931 _98932 h0). Qed.
Lemma lem7686651 (a : Prop) (b : Prop) : (a -> b) = (term990 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7686652 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : (term989 A B _98931 _98932) = (term991 A B _98931 _98932).
Proof. exact (@lem7686651 (_98931 = _98932) ((@dest_finite_diff A B _98931) = (@dest_finite_diff A B _98932))). Qed.
Lemma lem7686653 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : term991 A B _98931 _98932.
Proof. exact (EQ_MP (@lem7686652 A B _98931 _98932) (@lem7686649 A B _98931 _98932)). Qed.
Lemma lem7686749 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term992 A B x y z.
Proof. exact (@lem21385 (finite_diff A B) x y z). Qed.
Lemma lem7686755 {A B : Type'} (_98817 : finite_diff A B) (x : finite_diff A B) (h1 : term629 A B x) : (term195 A B _98817) = _98817.
Proof. exact (EQ_MP (@lem7685545 A B _98817) (@lem7685544 A B _98817 x h1)). Qed.
Lemma lem7686756 {A B : Type'} (_98817 : finite_diff A B) (x : finite_diff A B) (h1 : term629 A B x) : (term195 A B _98817) = _98817.
Proof. exact (@lem7686755 A B _98817 x h1). Qed.
Lemma lem7686757 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : (term195 A B x) = x.
Proof. exact (@lem7686756 A B x x h1). Qed.
Lemma lem7686758 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7686757 A B x h1). Qed.
Lemma lem7686760 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7686761 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7686760 ((term195 A B x) = x)). Qed.
Lemma lem7686762 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7686761 A B x) (@lem7686758 A B x h1)). Qed.
Lemma lem7686764 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem21386 (finite_diff A B) x). Qed.
Lemma lem7686765 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem7686764 A B x). Qed.
Lemma lem7686766 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (@lem7686765 A B (term195 A B x)). Qed.
Lemma lem7686767 {A B : Type'} (x : finite_diff A B) : term996 A B x.
Proof. exact (fun h0 : term997 A B x => @lem7686766 A B x). Qed.
Lemma lem7686769 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7686770 {A B : Type'} (x : finite_diff A B) : (term996 A B x) = ((term195 A B x) = (term195 A B x)).
Proof. exact (@lem7686769 ((term195 A B x) = (term195 A B x))). Qed.
Lemma lem7686771 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (EQ_MP (@lem7686770 A B x) (@lem7686767 A B x)). Qed.
Lemma lem7686789 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7686790 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term998 A B x y z) = (term999 A B y x z).
Proof. exact (@lem7686789 (y = z) (term1000 A B x z)). Qed.
Lemma lem7686800 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1001 A B x y) = (term1001 A B x y).
Proof. exact (eq_refl (term1001 A B x y)). Qed.
Lemma lem7686801 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1002 A B y x z).
Proof. exact (MK_COMB (@lem7686800 A B x y) (@lem7686790 A B y x z)). Qed.
Lemma lem7686805 (q : Prop) (p : Prop) (r : Prop) : (term1003 p q r) = (term1003 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7686806 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1002 A B y x z) = (term1004 A B y x z).
Proof. exact (@lem7686805 (y = z) (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7686828 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (TRANS (@lem7686801 A B y x z) (@lem7686806 A B y x z)). Qed.
Lemma lem7686829 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7686830 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1005 A B x y z) = (term1006 A B y x z).
Proof. exact (MK_COMB (@lem7686829) (@lem7686828 A B y x z)). Qed.
Lemma lem7686852 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1004 A B y x z).
Proof. exact (eq_refl (term1004 A B y x z)). Qed.
Lemma lem7686853 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = ((term1004 A B y x z) = (term1004 A B y x z)).
Proof. exact (MK_COMB (@lem7686830 A B y x z) (@lem7686852 A B y x z)). Qed.
Lemma lem7686855 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7686856 (x : Prop) : (x = x) = True.
Proof. exact (@lem7686855 Prop x). Qed.
Lemma lem7686857 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term1004 A B y x z) = (term1004 A B y x z)) = True.
Proof. exact (@lem7686856 (term1004 A B y x z)). Qed.
Lemma lem7686858 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = True.
Proof. exact (TRANS (@lem7686853 A B y x z) (@lem7686857 A B y x z)). Qed.
Lemma lem7686859 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : True = ((term992 A B x y z) = (term1004 A B y x z)).
Proof. exact (SYM (@lem7686858 A B y x z)). Qed.
Lemma lem7686860 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (EQ_MP (@lem7686859 A B y x z) (@lem0)). Qed.
Lemma lem7686861 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : term1004 A B y x z.
Proof. exact (EQ_MP (@lem7686860 A B y x z) (@lem7686749 A B x y z)). Qed.
Lemma lem7686863 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7686864 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1008 A B x y z).
Proof. exact (@lem7686863 (term1009 A B y x z) (y = z)). Qed.
Lemma lem7686866 (a : Prop) (b : Prop) : (term1010 a b) = (term1011 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7686867 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1013 A B y x z).
Proof. exact (@lem7686866 (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7686869 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7686870 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1015 A B x y) = (x = y).
Proof. exact (@lem7686869 (x = y)). Qed.
Lemma lem7686871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7686872 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1016 A B x y) = (term1017 A B x y).
Proof. exact (MK_COMB (@lem7686871) (@lem7686870 A B x y)). Qed.
Lemma lem7686874 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7686875 {A B : Type'} (x : finite_diff A B) (z : finite_diff A B) : (term1015 A B x z) = (x = z).
Proof. exact (@lem7686874 (x = z)). Qed.
Lemma lem7686876 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1013 A B y x z) = (term1018 A B y x z).
Proof. exact (MK_COMB (@lem7686872 A B x y) (@lem7686875 A B x z)). Qed.
Lemma lem7686877 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1018 A B y x z).
Proof. exact (TRANS (@lem7686867 A B y x z) (@lem7686876 A B y x z)). Qed.
Lemma lem7686878 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7686879 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1019 A B y x z) = (term1020 A B y x z).
Proof. exact (MK_COMB (@lem7686878) (@lem7686877 A B y x z)). Qed.
Lemma lem7686880 {A B : Type'} (y : finite_diff A B) (z : finite_diff A B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7686881 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1008 A B x y z) = (term1021 A B x y z).
Proof. exact (MK_COMB (@lem7686879 A B y x z) (@lem7686880 A B y z)). Qed.
Lemma lem7686882 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1021 A B x y z).
Proof. exact (TRANS (@lem7686864 A B x y z) (@lem7686881 A B x y z)). Qed.
Lemma lem7686884 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term1022 A B x.
Proof. exact (conj (@lem7686762 A B x h1) (@lem7686771 A B x)). Qed.
Lemma lem7686886 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (EQ_MP (@lem7686882 A B x y z) (@lem7686861 A B y x z)). Qed.
Lemma lem7686887 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (@lem7686886 A B x y z). Qed.
Lemma lem7686888 {A B : Type'} (x : finite_diff A B) : term1023 A B x.
Proof. exact (@lem7686887 A B (term195 A B x) x (term195 A B x)). Qed.
Lemma lem7686891 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : x = (term195 A B x).
Proof. exact (@lem7686888 A B x (@lem7686884 A B x h1)). Qed.
Lemma lem7686892 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term1024 A B x.
Proof. exact (fun h0 : term1025 A B x => @lem7686891 A B x h1). Qed.
Lemma lem7686894 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7686895 {A B : Type'} (x : finite_diff A B) : (term1024 A B x) = (x = (term195 A B x)).
Proof. exact (@lem7686894 (x = (term195 A B x))). Qed.
Lemma lem7686896 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : x = (term195 A B x).
Proof. exact (EQ_MP (@lem7686895 A B x) (@lem7686892 A B x h1)). Qed.
Lemma lem7686898 {A B : Type'} (_98817 : finite_diff A B) (x : finite_diff A B) (h1 : term629 A B x) : (term195 A B _98817) = _98817.
Proof. exact (EQ_MP (@lem7685545 A B _98817) (@lem7685544 A B _98817 x h1)). Qed.
Lemma lem7686899 {A B : Type'} (_98817 : finite_diff A B) (x : finite_diff A B) (h1 : term629 A B x) : (term195 A B _98817) = _98817.
Proof. exact (@lem7686898 A B _98817 x h1). Qed.
Lemma lem7686900 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : (term195 A B x) = x.
Proof. exact (@lem7686899 A B x x h1). Qed.
Lemma lem7686901 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7686900 A B x h1). Qed.
Lemma lem7686903 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7686904 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7686903 ((term195 A B x) = x)). Qed.
Lemma lem7686905 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7686904 A B x) (@lem7686901 A B x h1)). Qed.
Lemma lem7686911 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7686912 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : (term991 A B _98931 _98932) = (term1026 A B _98931 _98932).
Proof. exact (@lem7686911 ((@dest_finite_diff A B _98931) = (@dest_finite_diff A B _98932)) (term1000 A B _98931 _98932)). Qed.
Lemma lem7686922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7686923 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : (term1027 A B _98931 _98932) = (term1028 A B _98931 _98932).
Proof. exact (MK_COMB (@lem7686922) (@lem7686912 A B _98931 _98932)). Qed.
Lemma lem7686933 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : (term1026 A B _98931 _98932) = (term1026 A B _98931 _98932).
Proof. exact (eq_refl (term1026 A B _98931 _98932)). Qed.
Lemma lem7686934 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : ((term991 A B _98931 _98932) = (term1026 A B _98931 _98932)) = ((term1026 A B _98931 _98932) = (term1026 A B _98931 _98932)).
Proof. exact (MK_COMB (@lem7686923 A B _98931 _98932) (@lem7686933 A B _98931 _98932)). Qed.
Lemma lem7686936 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7686937 (x : Prop) : (x = x) = True.
Proof. exact (@lem7686936 Prop x). Qed.
Lemma lem7686938 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : ((term1026 A B _98931 _98932) = (term1026 A B _98931 _98932)) = True.
Proof. exact (@lem7686937 (term1026 A B _98931 _98932)). Qed.
Lemma lem7686939 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : ((term991 A B _98931 _98932) = (term1026 A B _98931 _98932)) = True.
Proof. exact (TRANS (@lem7686934 A B _98931 _98932) (@lem7686938 A B _98931 _98932)). Qed.
Lemma lem7686940 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : True = ((term991 A B _98931 _98932) = (term1026 A B _98931 _98932)).
Proof. exact (SYM (@lem7686939 A B _98931 _98932)). Qed.
Lemma lem7686941 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : (term991 A B _98931 _98932) = (term1026 A B _98931 _98932).
Proof. exact (EQ_MP (@lem7686940 A B _98931 _98932) (@lem0)). Qed.
Lemma lem7686942 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : term1026 A B _98931 _98932.
Proof. exact (EQ_MP (@lem7686941 A B _98931 _98932) (@lem7686653 A B _98931 _98932)). Qed.
Lemma lem7686944 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7686945 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : (term1026 A B _98931 _98932) = (term1029 A B _98931 _98932).
Proof. exact (@lem7686944 (term1000 A B _98931 _98932) ((@dest_finite_diff A B _98931) = (@dest_finite_diff A B _98932))). Qed.
Lemma lem7686947 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7686948 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : (term1015 A B _98931 _98932) = (_98931 = _98932).
Proof. exact (@lem7686947 (_98931 = _98932)). Qed.
Lemma lem7686949 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7686950 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : (term1030 A B _98931 _98932) = (term1031 A B _98931 _98932).
Proof. exact (MK_COMB (@lem7686949) (@lem7686948 A B _98931 _98932)). Qed.
Lemma lem7686951 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : ((@dest_finite_diff A B _98931) = (@dest_finite_diff A B _98932)) = ((@dest_finite_diff A B _98931) = (@dest_finite_diff A B _98932)).
Proof. exact (eq_refl ((@dest_finite_diff A B _98931) = (@dest_finite_diff A B _98932))). Qed.
Lemma lem7686952 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : (term1029 A B _98931 _98932) = (term989 A B _98931 _98932).
Proof. exact (MK_COMB (@lem7686950 A B _98931 _98932) (@lem7686951 A B _98931 _98932)). Qed.
Lemma lem7686953 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : (term1026 A B _98931 _98932) = (term989 A B _98931 _98932).
Proof. exact (TRANS (@lem7686945 A B _98931 _98932) (@lem7686952 A B _98931 _98932)). Qed.
Lemma lem7686956 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : term989 A B _98931 _98932.
Proof. exact (EQ_MP (@lem7686953 A B _98931 _98932) (@lem7686942 A B _98931 _98932)). Qed.
Lemma lem7686957 {A B : Type'} (_98931 : finite_diff A B) (_98932 : finite_diff A B) : term989 A B _98931 _98932.
Proof. exact (@lem7686956 A B _98931 _98932). Qed.
Lemma lem7686958 {A B : Type'} (x : finite_diff A B) : term1032 A B x.
Proof. exact (@lem7686957 A B (term195 A B x) x). Qed.
Lemma lem7686961 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (@lem7686958 A B x (@lem7686905 A B x h1)). Qed.
Lemma lem7686962 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term1034 A B x.
Proof. exact (fun h0 : term1035 A B x => @lem7686961 A B x h1). Qed.
Lemma lem7686964 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7686965 {A B : Type'} (x : finite_diff A B) : (term1034 A B x) = ((term1033 A B x) = (@dest_finite_diff A B x)).
Proof. exact (@lem7686964 ((term1033 A B x) = (@dest_finite_diff A B x))). Qed.
Lemma lem7686966 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (EQ_MP (@lem7686965 A B x) (@lem7686962 A B x h1)). Qed.
Lemma lem7686968 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7686969 {A B : Type'} (_98818 : nat) : (term480 A B _98818) = (term1052 A B _98818).
Proof. exact (@lem7686968 (term1037 A B _98818) (term32 _98818)). Qed.
Lemma lem7686971 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7686972 {A B : Type'} (_98818 : nat) : (term1038 A B _98818) = ((term47 A B _98818) = _98818).
Proof. exact (@lem7686971 ((term47 A B _98818) = _98818)). Qed.
Lemma lem7686973 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7686974 {A B : Type'} (_98818 : nat) : (term1039 A B _98818) = (term1040 A B _98818).
Proof. exact (MK_COMB (@lem7686973) (@lem7686972 A B _98818)). Qed.
Lemma lem7686975 (_98818 : nat) : (term32 _98818) = (term32 _98818).
Proof. exact (eq_refl (term32 _98818)). Qed.
Lemma lem7686976 {A B : Type'} (_98818 : nat) : (term1052 A B _98818) = (term1053 A B _98818).
Proof. exact (MK_COMB (@lem7686974 A B _98818) (@lem7686975 _98818)). Qed.
Lemma lem7686977 {A B : Type'} (_98818 : nat) : (term480 A B _98818) = (term1053 A B _98818).
Proof. exact (TRANS (@lem7686969 A B _98818) (@lem7686976 A B _98818)). Qed.
Lemma lem7686980 {A B : Type'} (_98818 : nat) (x : finite_diff A B) (h1 : term629 A B x) : term1053 A B _98818.
Proof. exact (EQ_MP (@lem7686977 A B _98818) (@lem7685829 A B _98818 x h1)). Qed.
Lemma lem7686981 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term1054 A B x.
Proof. exact (@lem7686980 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7686984 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term1055 A B x.
Proof. exact (@lem7686981 A B x h1 (@lem7686966 A B x h1)). Qed.
Lemma lem7686985 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term1056 A B x.
Proof. exact (fun h0 : term1057 A B x => @lem7686984 A B x h1). Qed.
Lemma lem7686987 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7686988 {A B : Type'} (x : finite_diff A B) : (term1056 A B x) = (term1055 A B x).
Proof. exact (@lem7686987 (term1055 A B x)). Qed.
Lemma lem7686989 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term1055 A B x.
Proof. exact (EQ_MP (@lem7686988 A B x) (@lem7686985 A B x h1)). Qed.
Lemma lem7686991 (a : Prop) (b : Prop) : (term1046 a b) = (term1047 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7686992 {A B : Type'} (x : finite_diff A B) (_98813 : nat) : (term258 A B x _98813) = (term257 A B x _98813).
Proof. exact (@lem7686991 (x = (@mk_finite_diff A B _98813)) (term32 _98813)). Qed.
Lemma lem7686994 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7686995 {A B : Type'} (x : finite_diff A B) (_98813 : nat) : (term257 A B x _98813) = (term1058 A B x _98813).
Proof. exact (@lem7686994 (term35 A B x _98813)). Qed.
Lemma lem7686996 {A B : Type'} (x : finite_diff A B) (_98813 : nat) : (term258 A B x _98813) = (term1058 A B x _98813).
Proof. exact (TRANS (@lem7686992 A B x _98813) (@lem7686995 A B x _98813)). Qed.
Lemma lem7686998 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term1059 A B x.
Proof. exact (conj (@lem7686896 A B x h1) (@lem7686989 A B x h1)). Qed.
Lemma lem7687000 {A B : Type'} (_98813 : nat) (x : finite_diff A B) (h1 : term629 A B x) : term1058 A B x _98813.
Proof. exact (EQ_MP (@lem7686996 A B x _98813) (@lem7685807 A B _98813 x h1)). Qed.
Lemma lem7687001 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term1060 A B x.
Proof. exact (@lem7687000 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7687004 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : False.
Proof. exact (@lem7687001 A B x h1 (@lem7686998 A B x h1)). Qed.
Lemma lem7687005 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : term1051.
Proof. exact (fun h0 : ~ False => @lem7687004 A B x h1). Qed.
Lemma lem7687007 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7687008 : term1051 = False.
Proof. exact (@lem7687007 False). Qed.
Lemma lem7687009 {A B : Type'} (x : finite_diff A B) (h1 : term629 A B x) : False.
Proof. exact (EQ_MP (@lem7687008) (@lem7687005 A B x h1)). Qed.
Lemma lem7687064 {A B : Type'} : (@dest_finite_diff A B) = (@dest_finite_diff A B).
Proof. exact (eq_refl (@dest_finite_diff A B)). Qed.
Lemma lem7687065 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) (h1 : _98967 = _98968) : _98967 = _98968.
Proof. exact (h1). Qed.
Lemma lem7687066 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) (h1 : _98967 = _98968) : (@dest_finite_diff A B _98967) = (@dest_finite_diff A B _98968).
Proof. exact (MK_COMB (@lem7687064 A B) (@lem7687065 A B _98967 _98968 h1)). Qed.
Lemma lem7687067 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : term989 A B _98967 _98968.
Proof. exact (fun h0 : _98967 = _98968 => @lem7687066 A B _98967 _98968 h0). Qed.
Lemma lem7687069 (a : Prop) (b : Prop) : (a -> b) = (term990 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7687070 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : (term989 A B _98967 _98968) = (term991 A B _98967 _98968).
Proof. exact (@lem7687069 (_98967 = _98968) ((@dest_finite_diff A B _98967) = (@dest_finite_diff A B _98968))). Qed.
Lemma lem7687071 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : term991 A B _98967 _98968.
Proof. exact (EQ_MP (@lem7687070 A B _98967 _98968) (@lem7687067 A B _98967 _98968)). Qed.
Lemma lem7687167 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term992 A B x y z.
Proof. exact (@lem21385 (finite_diff A B) x y z). Qed.
Lemma lem7687173 {A B : Type'} (_98827 : finite_diff A B) (x : finite_diff A B) (h1 : term688 A B x) : (term195 A B _98827) = _98827.
Proof. exact (EQ_MP (@lem7685575 A B _98827) (@lem7685574 A B _98827 x h1)). Qed.
Lemma lem7687174 {A B : Type'} (_98827 : finite_diff A B) (x : finite_diff A B) (h1 : term688 A B x) : (term195 A B _98827) = _98827.
Proof. exact (@lem7687173 A B _98827 x h1). Qed.
Lemma lem7687175 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : (term195 A B x) = x.
Proof. exact (@lem7687174 A B x x h1). Qed.
Lemma lem7687176 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7687175 A B x h1). Qed.
Lemma lem7687178 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7687179 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7687178 ((term195 A B x) = x)). Qed.
Lemma lem7687180 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7687179 A B x) (@lem7687176 A B x h1)). Qed.
Lemma lem7687182 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem21386 (finite_diff A B) x). Qed.
Lemma lem7687183 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem7687182 A B x). Qed.
Lemma lem7687184 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (@lem7687183 A B (term195 A B x)). Qed.
Lemma lem7687185 {A B : Type'} (x : finite_diff A B) : term996 A B x.
Proof. exact (fun h0 : term997 A B x => @lem7687184 A B x). Qed.
Lemma lem7687187 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7687188 {A B : Type'} (x : finite_diff A B) : (term996 A B x) = ((term195 A B x) = (term195 A B x)).
Proof. exact (@lem7687187 ((term195 A B x) = (term195 A B x))). Qed.
Lemma lem7687189 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (EQ_MP (@lem7687188 A B x) (@lem7687185 A B x)). Qed.
Lemma lem7687207 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7687208 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term998 A B x y z) = (term999 A B y x z).
Proof. exact (@lem7687207 (y = z) (term1000 A B x z)). Qed.
Lemma lem7687218 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1001 A B x y) = (term1001 A B x y).
Proof. exact (eq_refl (term1001 A B x y)). Qed.
Lemma lem7687219 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1002 A B y x z).
Proof. exact (MK_COMB (@lem7687218 A B x y) (@lem7687208 A B y x z)). Qed.
Lemma lem7687223 (q : Prop) (p : Prop) (r : Prop) : (term1003 p q r) = (term1003 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7687224 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1002 A B y x z) = (term1004 A B y x z).
Proof. exact (@lem7687223 (y = z) (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7687246 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (TRANS (@lem7687219 A B y x z) (@lem7687224 A B y x z)). Qed.
Lemma lem7687247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7687248 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1005 A B x y z) = (term1006 A B y x z).
Proof. exact (MK_COMB (@lem7687247) (@lem7687246 A B y x z)). Qed.
Lemma lem7687270 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1004 A B y x z).
Proof. exact (eq_refl (term1004 A B y x z)). Qed.
Lemma lem7687271 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = ((term1004 A B y x z) = (term1004 A B y x z)).
Proof. exact (MK_COMB (@lem7687248 A B y x z) (@lem7687270 A B y x z)). Qed.
Lemma lem7687273 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7687274 (x : Prop) : (x = x) = True.
Proof. exact (@lem7687273 Prop x). Qed.
Lemma lem7687275 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term1004 A B y x z) = (term1004 A B y x z)) = True.
Proof. exact (@lem7687274 (term1004 A B y x z)). Qed.
Lemma lem7687276 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = True.
Proof. exact (TRANS (@lem7687271 A B y x z) (@lem7687275 A B y x z)). Qed.
Lemma lem7687277 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : True = ((term992 A B x y z) = (term1004 A B y x z)).
Proof. exact (SYM (@lem7687276 A B y x z)). Qed.
Lemma lem7687278 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (EQ_MP (@lem7687277 A B y x z) (@lem0)). Qed.
Lemma lem7687279 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : term1004 A B y x z.
Proof. exact (EQ_MP (@lem7687278 A B y x z) (@lem7687167 A B x y z)). Qed.
Lemma lem7687281 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7687282 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1008 A B x y z).
Proof. exact (@lem7687281 (term1009 A B y x z) (y = z)). Qed.
Lemma lem7687284 (a : Prop) (b : Prop) : (term1010 a b) = (term1011 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7687285 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1013 A B y x z).
Proof. exact (@lem7687284 (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7687287 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7687288 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1015 A B x y) = (x = y).
Proof. exact (@lem7687287 (x = y)). Qed.
Lemma lem7687289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7687290 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1016 A B x y) = (term1017 A B x y).
Proof. exact (MK_COMB (@lem7687289) (@lem7687288 A B x y)). Qed.
Lemma lem7687292 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7687293 {A B : Type'} (x : finite_diff A B) (z : finite_diff A B) : (term1015 A B x z) = (x = z).
Proof. exact (@lem7687292 (x = z)). Qed.
Lemma lem7687294 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1013 A B y x z) = (term1018 A B y x z).
Proof. exact (MK_COMB (@lem7687290 A B x y) (@lem7687293 A B x z)). Qed.
Lemma lem7687295 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1018 A B y x z).
Proof. exact (TRANS (@lem7687285 A B y x z) (@lem7687294 A B y x z)). Qed.
Lemma lem7687296 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7687297 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1019 A B y x z) = (term1020 A B y x z).
Proof. exact (MK_COMB (@lem7687296) (@lem7687295 A B y x z)). Qed.
Lemma lem7687298 {A B : Type'} (y : finite_diff A B) (z : finite_diff A B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7687299 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1008 A B x y z) = (term1021 A B x y z).
Proof. exact (MK_COMB (@lem7687297 A B y x z) (@lem7687298 A B y z)). Qed.
Lemma lem7687300 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1021 A B x y z).
Proof. exact (TRANS (@lem7687282 A B x y z) (@lem7687299 A B x y z)). Qed.
Lemma lem7687302 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term1022 A B x.
Proof. exact (conj (@lem7687180 A B x h1) (@lem7687189 A B x)). Qed.
Lemma lem7687304 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (EQ_MP (@lem7687300 A B x y z) (@lem7687279 A B y x z)). Qed.
Lemma lem7687305 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (@lem7687304 A B x y z). Qed.
Lemma lem7687306 {A B : Type'} (x : finite_diff A B) : term1023 A B x.
Proof. exact (@lem7687305 A B (term195 A B x) x (term195 A B x)). Qed.
Lemma lem7687309 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : x = (term195 A B x).
Proof. exact (@lem7687306 A B x (@lem7687302 A B x h1)). Qed.
Lemma lem7687310 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term1024 A B x.
Proof. exact (fun h0 : term1025 A B x => @lem7687309 A B x h1). Qed.
Lemma lem7687312 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7687313 {A B : Type'} (x : finite_diff A B) : (term1024 A B x) = (x = (term195 A B x)).
Proof. exact (@lem7687312 (x = (term195 A B x))). Qed.
Lemma lem7687314 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : x = (term195 A B x).
Proof. exact (EQ_MP (@lem7687313 A B x) (@lem7687310 A B x h1)). Qed.
Lemma lem7687316 {A B : Type'} (_98827 : finite_diff A B) (x : finite_diff A B) (h1 : term688 A B x) : (term195 A B _98827) = _98827.
Proof. exact (EQ_MP (@lem7685575 A B _98827) (@lem7685574 A B _98827 x h1)). Qed.
Lemma lem7687317 {A B : Type'} (_98827 : finite_diff A B) (x : finite_diff A B) (h1 : term688 A B x) : (term195 A B _98827) = _98827.
Proof. exact (@lem7687316 A B _98827 x h1). Qed.
Lemma lem7687318 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : (term195 A B x) = x.
Proof. exact (@lem7687317 A B x x h1). Qed.
Lemma lem7687319 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7687318 A B x h1). Qed.
Lemma lem7687321 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7687322 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7687321 ((term195 A B x) = x)). Qed.
Lemma lem7687323 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7687322 A B x) (@lem7687319 A B x h1)). Qed.
Lemma lem7687329 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7687330 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : (term991 A B _98967 _98968) = (term1026 A B _98967 _98968).
Proof. exact (@lem7687329 ((@dest_finite_diff A B _98967) = (@dest_finite_diff A B _98968)) (term1000 A B _98967 _98968)). Qed.
Lemma lem7687340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7687341 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : (term1027 A B _98967 _98968) = (term1028 A B _98967 _98968).
Proof. exact (MK_COMB (@lem7687340) (@lem7687330 A B _98967 _98968)). Qed.
Lemma lem7687351 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : (term1026 A B _98967 _98968) = (term1026 A B _98967 _98968).
Proof. exact (eq_refl (term1026 A B _98967 _98968)). Qed.
Lemma lem7687352 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : ((term991 A B _98967 _98968) = (term1026 A B _98967 _98968)) = ((term1026 A B _98967 _98968) = (term1026 A B _98967 _98968)).
Proof. exact (MK_COMB (@lem7687341 A B _98967 _98968) (@lem7687351 A B _98967 _98968)). Qed.
Lemma lem7687354 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7687355 (x : Prop) : (x = x) = True.
Proof. exact (@lem7687354 Prop x). Qed.
Lemma lem7687356 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : ((term1026 A B _98967 _98968) = (term1026 A B _98967 _98968)) = True.
Proof. exact (@lem7687355 (term1026 A B _98967 _98968)). Qed.
Lemma lem7687357 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : ((term991 A B _98967 _98968) = (term1026 A B _98967 _98968)) = True.
Proof. exact (TRANS (@lem7687352 A B _98967 _98968) (@lem7687356 A B _98967 _98968)). Qed.
Lemma lem7687358 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : True = ((term991 A B _98967 _98968) = (term1026 A B _98967 _98968)).
Proof. exact (SYM (@lem7687357 A B _98967 _98968)). Qed.
Lemma lem7687359 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : (term991 A B _98967 _98968) = (term1026 A B _98967 _98968).
Proof. exact (EQ_MP (@lem7687358 A B _98967 _98968) (@lem0)). Qed.
Lemma lem7687360 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : term1026 A B _98967 _98968.
Proof. exact (EQ_MP (@lem7687359 A B _98967 _98968) (@lem7687071 A B _98967 _98968)). Qed.
Lemma lem7687362 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7687363 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : (term1026 A B _98967 _98968) = (term1029 A B _98967 _98968).
Proof. exact (@lem7687362 (term1000 A B _98967 _98968) ((@dest_finite_diff A B _98967) = (@dest_finite_diff A B _98968))). Qed.
Lemma lem7687365 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7687366 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : (term1015 A B _98967 _98968) = (_98967 = _98968).
Proof. exact (@lem7687365 (_98967 = _98968)). Qed.
Lemma lem7687367 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7687368 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : (term1030 A B _98967 _98968) = (term1031 A B _98967 _98968).
Proof. exact (MK_COMB (@lem7687367) (@lem7687366 A B _98967 _98968)). Qed.
Lemma lem7687369 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : ((@dest_finite_diff A B _98967) = (@dest_finite_diff A B _98968)) = ((@dest_finite_diff A B _98967) = (@dest_finite_diff A B _98968)).
Proof. exact (eq_refl ((@dest_finite_diff A B _98967) = (@dest_finite_diff A B _98968))). Qed.
Lemma lem7687370 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : (term1029 A B _98967 _98968) = (term989 A B _98967 _98968).
Proof. exact (MK_COMB (@lem7687368 A B _98967 _98968) (@lem7687369 A B _98967 _98968)). Qed.
Lemma lem7687371 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : (term1026 A B _98967 _98968) = (term989 A B _98967 _98968).
Proof. exact (TRANS (@lem7687363 A B _98967 _98968) (@lem7687370 A B _98967 _98968)). Qed.
Lemma lem7687374 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : term989 A B _98967 _98968.
Proof. exact (EQ_MP (@lem7687371 A B _98967 _98968) (@lem7687360 A B _98967 _98968)). Qed.
Lemma lem7687375 {A B : Type'} (_98967 : finite_diff A B) (_98968 : finite_diff A B) : term989 A B _98967 _98968.
Proof. exact (@lem7687374 A B _98967 _98968). Qed.
Lemma lem7687376 {A B : Type'} (x : finite_diff A B) : term1032 A B x.
Proof. exact (@lem7687375 A B (term195 A B x) x). Qed.
Lemma lem7687379 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (@lem7687376 A B x (@lem7687323 A B x h1)). Qed.
Lemma lem7687380 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term1034 A B x.
Proof. exact (fun h0 : term1035 A B x => @lem7687379 A B x h1). Qed.
Lemma lem7687382 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7687383 {A B : Type'} (x : finite_diff A B) : (term1034 A B x) = ((term1033 A B x) = (@dest_finite_diff A B x)).
Proof. exact (@lem7687382 ((term1033 A B x) = (@dest_finite_diff A B x))). Qed.
Lemma lem7687384 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (EQ_MP (@lem7687383 A B x) (@lem7687380 A B x h1)). Qed.
Lemma lem7687386 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7687387 {A B : Type'} (_98828 : nat) : (term450 A B _98828) = (term1036 A B _98828).
Proof. exact (@lem7687386 (term1037 A B _98828) (term62 A B _98828)). Qed.
Lemma lem7687389 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7687390 {A B : Type'} (_98828 : nat) : (term1038 A B _98828) = ((term47 A B _98828) = _98828).
Proof. exact (@lem7687389 ((term47 A B _98828) = _98828)). Qed.
Lemma lem7687391 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7687392 {A B : Type'} (_98828 : nat) : (term1039 A B _98828) = (term1040 A B _98828).
Proof. exact (MK_COMB (@lem7687391) (@lem7687390 A B _98828)). Qed.
Lemma lem7687393 {A B : Type'} (_98828 : nat) : (term62 A B _98828) = (term62 A B _98828).
Proof. exact (eq_refl (term62 A B _98828)). Qed.
Lemma lem7687394 {A B : Type'} (_98828 : nat) : (term1036 A B _98828) = (term1041 A B _98828).
Proof. exact (MK_COMB (@lem7687392 A B _98828) (@lem7687393 A B _98828)). Qed.
Lemma lem7687395 {A B : Type'} (_98828 : nat) : (term450 A B _98828) = (term1041 A B _98828).
Proof. exact (TRANS (@lem7687387 A B _98828) (@lem7687394 A B _98828)). Qed.
Lemma lem7687398 {A B : Type'} (_98828 : nat) (x : finite_diff A B) (h1 : term688 A B x) : term1041 A B _98828.
Proof. exact (EQ_MP (@lem7687395 A B _98828) (@lem7685883 A B _98828 x h1)). Qed.
Lemma lem7687399 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term1042 A B x.
Proof. exact (@lem7687398 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7687402 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term1043 A B x.
Proof. exact (@lem7687399 A B x h1 (@lem7687384 A B x h1)). Qed.
Lemma lem7687403 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term1044 A B x.
Proof. exact (fun h0 : term1045 A B x => @lem7687402 A B x h1). Qed.
Lemma lem7687405 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7687406 {A B : Type'} (x : finite_diff A B) : (term1044 A B x) = (term1043 A B x).
Proof. exact (@lem7687405 (term1043 A B x)). Qed.
Lemma lem7687407 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term1043 A B x.
Proof. exact (EQ_MP (@lem7687406 A B x) (@lem7687403 A B x h1)). Qed.
Lemma lem7687409 (a : Prop) (b : Prop) : (term1046 a b) = (term1047 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7687410 {A B : Type'} (x : finite_diff A B) (_98823 : nat) : (term209 A B x _98823) = (term208 A B x _98823).
Proof. exact (@lem7687409 (x = (@mk_finite_diff A B _98823)) (term62 A B _98823)). Qed.
Lemma lem7687412 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7687413 {A B : Type'} (x : finite_diff A B) (_98823 : nat) : (term208 A B x _98823) = (term1048 A B x _98823).
Proof. exact (@lem7687412 (term63 A B x _98823)). Qed.
Lemma lem7687414 {A B : Type'} (x : finite_diff A B) (_98823 : nat) : (term209 A B x _98823) = (term1048 A B x _98823).
Proof. exact (TRANS (@lem7687410 A B x _98823) (@lem7687413 A B x _98823)). Qed.
Lemma lem7687416 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term1049 A B x.
Proof. exact (conj (@lem7687314 A B x h1) (@lem7687407 A B x h1)). Qed.
Lemma lem7687418 {A B : Type'} (_98823 : nat) (x : finite_diff A B) (h1 : term688 A B x) : term1048 A B x _98823.
Proof. exact (EQ_MP (@lem7687414 A B x _98823) (@lem7685861 A B _98823 x h1)). Qed.
Lemma lem7687419 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term1050 A B x.
Proof. exact (@lem7687418 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7687422 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : False.
Proof. exact (@lem7687419 A B x h1 (@lem7687416 A B x h1)). Qed.
Lemma lem7687423 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : term1051.
Proof. exact (fun h0 : ~ False => @lem7687422 A B x h1). Qed.
Lemma lem7687425 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7687426 : term1051 = False.
Proof. exact (@lem7687425 False). Qed.
Lemma lem7687427 {A B : Type'} (x : finite_diff A B) (h1 : term688 A B x) : False.
Proof. exact (EQ_MP (@lem7687426) (@lem7687423 A B x h1)). Qed.
Lemma lem7687482 {A B : Type'} : (@dest_finite_diff A B) = (@dest_finite_diff A B).
Proof. exact (eq_refl (@dest_finite_diff A B)). Qed.
Lemma lem7687483 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) (h1 : _99003 = _99004) : _99003 = _99004.
Proof. exact (h1). Qed.
Lemma lem7687484 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) (h1 : _99003 = _99004) : (@dest_finite_diff A B _99003) = (@dest_finite_diff A B _99004).
Proof. exact (MK_COMB (@lem7687482 A B) (@lem7687483 A B _99003 _99004 h1)). Qed.
Lemma lem7687485 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : term989 A B _99003 _99004.
Proof. exact (fun h0 : _99003 = _99004 => @lem7687484 A B _99003 _99004 h0). Qed.
Lemma lem7687487 (a : Prop) (b : Prop) : (a -> b) = (term990 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7687488 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : (term989 A B _99003 _99004) = (term991 A B _99003 _99004).
Proof. exact (@lem7687487 (_99003 = _99004) ((@dest_finite_diff A B _99003) = (@dest_finite_diff A B _99004))). Qed.
Lemma lem7687489 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : term991 A B _99003 _99004.
Proof. exact (EQ_MP (@lem7687488 A B _99003 _99004) (@lem7687485 A B _99003 _99004)). Qed.
Lemma lem7687585 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term992 A B x y z.
Proof. exact (@lem21385 (finite_diff A B) x y z). Qed.
Lemma lem7687591 {A B : Type'} (_98837 : finite_diff A B) (x : finite_diff A B) (h1 : term711 A B x) : (term195 A B _98837) = _98837.
Proof. exact (EQ_MP (@lem7685605 A B _98837) (@lem7685604 A B _98837 x h1)). Qed.
Lemma lem7687592 {A B : Type'} (_98837 : finite_diff A B) (x : finite_diff A B) (h1 : term711 A B x) : (term195 A B _98837) = _98837.
Proof. exact (@lem7687591 A B _98837 x h1). Qed.
Lemma lem7687593 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : (term195 A B x) = x.
Proof. exact (@lem7687592 A B x x h1). Qed.
Lemma lem7687594 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7687593 A B x h1). Qed.
Lemma lem7687596 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7687597 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7687596 ((term195 A B x) = x)). Qed.
Lemma lem7687598 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7687597 A B x) (@lem7687594 A B x h1)). Qed.
Lemma lem7687600 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem21386 (finite_diff A B) x). Qed.
Lemma lem7687601 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem7687600 A B x). Qed.
Lemma lem7687602 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (@lem7687601 A B (term195 A B x)). Qed.
Lemma lem7687603 {A B : Type'} (x : finite_diff A B) : term996 A B x.
Proof. exact (fun h0 : term997 A B x => @lem7687602 A B x). Qed.
Lemma lem7687605 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7687606 {A B : Type'} (x : finite_diff A B) : (term996 A B x) = ((term195 A B x) = (term195 A B x)).
Proof. exact (@lem7687605 ((term195 A B x) = (term195 A B x))). Qed.
Lemma lem7687607 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (EQ_MP (@lem7687606 A B x) (@lem7687603 A B x)). Qed.
Lemma lem7687625 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7687626 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term998 A B x y z) = (term999 A B y x z).
Proof. exact (@lem7687625 (y = z) (term1000 A B x z)). Qed.
Lemma lem7687636 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1001 A B x y) = (term1001 A B x y).
Proof. exact (eq_refl (term1001 A B x y)). Qed.
Lemma lem7687637 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1002 A B y x z).
Proof. exact (MK_COMB (@lem7687636 A B x y) (@lem7687626 A B y x z)). Qed.
Lemma lem7687641 (q : Prop) (p : Prop) (r : Prop) : (term1003 p q r) = (term1003 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7687642 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1002 A B y x z) = (term1004 A B y x z).
Proof. exact (@lem7687641 (y = z) (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7687664 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (TRANS (@lem7687637 A B y x z) (@lem7687642 A B y x z)). Qed.
Lemma lem7687665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7687666 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1005 A B x y z) = (term1006 A B y x z).
Proof. exact (MK_COMB (@lem7687665) (@lem7687664 A B y x z)). Qed.
Lemma lem7687688 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1004 A B y x z).
Proof. exact (eq_refl (term1004 A B y x z)). Qed.
Lemma lem7687689 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = ((term1004 A B y x z) = (term1004 A B y x z)).
Proof. exact (MK_COMB (@lem7687666 A B y x z) (@lem7687688 A B y x z)). Qed.
Lemma lem7687691 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7687692 (x : Prop) : (x = x) = True.
Proof. exact (@lem7687691 Prop x). Qed.
Lemma lem7687693 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term1004 A B y x z) = (term1004 A B y x z)) = True.
Proof. exact (@lem7687692 (term1004 A B y x z)). Qed.
Lemma lem7687694 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = True.
Proof. exact (TRANS (@lem7687689 A B y x z) (@lem7687693 A B y x z)). Qed.
Lemma lem7687695 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : True = ((term992 A B x y z) = (term1004 A B y x z)).
Proof. exact (SYM (@lem7687694 A B y x z)). Qed.
Lemma lem7687696 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (EQ_MP (@lem7687695 A B y x z) (@lem0)). Qed.
Lemma lem7687697 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : term1004 A B y x z.
Proof. exact (EQ_MP (@lem7687696 A B y x z) (@lem7687585 A B x y z)). Qed.
Lemma lem7687699 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7687700 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1008 A B x y z).
Proof. exact (@lem7687699 (term1009 A B y x z) (y = z)). Qed.
Lemma lem7687702 (a : Prop) (b : Prop) : (term1010 a b) = (term1011 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7687703 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1013 A B y x z).
Proof. exact (@lem7687702 (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7687705 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7687706 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1015 A B x y) = (x = y).
Proof. exact (@lem7687705 (x = y)). Qed.
Lemma lem7687707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7687708 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1016 A B x y) = (term1017 A B x y).
Proof. exact (MK_COMB (@lem7687707) (@lem7687706 A B x y)). Qed.
Lemma lem7687710 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7687711 {A B : Type'} (x : finite_diff A B) (z : finite_diff A B) : (term1015 A B x z) = (x = z).
Proof. exact (@lem7687710 (x = z)). Qed.
Lemma lem7687712 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1013 A B y x z) = (term1018 A B y x z).
Proof. exact (MK_COMB (@lem7687708 A B x y) (@lem7687711 A B x z)). Qed.
Lemma lem7687713 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1018 A B y x z).
Proof. exact (TRANS (@lem7687703 A B y x z) (@lem7687712 A B y x z)). Qed.
Lemma lem7687714 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7687715 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1019 A B y x z) = (term1020 A B y x z).
Proof. exact (MK_COMB (@lem7687714) (@lem7687713 A B y x z)). Qed.
Lemma lem7687716 {A B : Type'} (y : finite_diff A B) (z : finite_diff A B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7687717 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1008 A B x y z) = (term1021 A B x y z).
Proof. exact (MK_COMB (@lem7687715 A B y x z) (@lem7687716 A B y z)). Qed.
Lemma lem7687718 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1021 A B x y z).
Proof. exact (TRANS (@lem7687700 A B x y z) (@lem7687717 A B x y z)). Qed.
Lemma lem7687720 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term1022 A B x.
Proof. exact (conj (@lem7687598 A B x h1) (@lem7687607 A B x)). Qed.
Lemma lem7687722 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (EQ_MP (@lem7687718 A B x y z) (@lem7687697 A B y x z)). Qed.
Lemma lem7687723 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (@lem7687722 A B x y z). Qed.
Lemma lem7687724 {A B : Type'} (x : finite_diff A B) : term1023 A B x.
Proof. exact (@lem7687723 A B (term195 A B x) x (term195 A B x)). Qed.
Lemma lem7687727 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : x = (term195 A B x).
Proof. exact (@lem7687724 A B x (@lem7687720 A B x h1)). Qed.
Lemma lem7687728 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term1024 A B x.
Proof. exact (fun h0 : term1025 A B x => @lem7687727 A B x h1). Qed.
Lemma lem7687730 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7687731 {A B : Type'} (x : finite_diff A B) : (term1024 A B x) = (x = (term195 A B x)).
Proof. exact (@lem7687730 (x = (term195 A B x))). Qed.
Lemma lem7687732 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : x = (term195 A B x).
Proof. exact (EQ_MP (@lem7687731 A B x) (@lem7687728 A B x h1)). Qed.
Lemma lem7687734 {A B : Type'} (_98837 : finite_diff A B) (x : finite_diff A B) (h1 : term711 A B x) : (term195 A B _98837) = _98837.
Proof. exact (EQ_MP (@lem7685605 A B _98837) (@lem7685604 A B _98837 x h1)). Qed.
Lemma lem7687735 {A B : Type'} (_98837 : finite_diff A B) (x : finite_diff A B) (h1 : term711 A B x) : (term195 A B _98837) = _98837.
Proof. exact (@lem7687734 A B _98837 x h1). Qed.
Lemma lem7687736 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : (term195 A B x) = x.
Proof. exact (@lem7687735 A B x x h1). Qed.
Lemma lem7687737 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7687736 A B x h1). Qed.
Lemma lem7687739 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7687740 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7687739 ((term195 A B x) = x)). Qed.
Lemma lem7687741 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7687740 A B x) (@lem7687737 A B x h1)). Qed.
Lemma lem7687747 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7687748 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : (term991 A B _99003 _99004) = (term1026 A B _99003 _99004).
Proof. exact (@lem7687747 ((@dest_finite_diff A B _99003) = (@dest_finite_diff A B _99004)) (term1000 A B _99003 _99004)). Qed.
Lemma lem7687758 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7687759 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : (term1027 A B _99003 _99004) = (term1028 A B _99003 _99004).
Proof. exact (MK_COMB (@lem7687758) (@lem7687748 A B _99003 _99004)). Qed.
Lemma lem7687769 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : (term1026 A B _99003 _99004) = (term1026 A B _99003 _99004).
Proof. exact (eq_refl (term1026 A B _99003 _99004)). Qed.
Lemma lem7687770 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : ((term991 A B _99003 _99004) = (term1026 A B _99003 _99004)) = ((term1026 A B _99003 _99004) = (term1026 A B _99003 _99004)).
Proof. exact (MK_COMB (@lem7687759 A B _99003 _99004) (@lem7687769 A B _99003 _99004)). Qed.
Lemma lem7687772 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7687773 (x : Prop) : (x = x) = True.
Proof. exact (@lem7687772 Prop x). Qed.
Lemma lem7687774 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : ((term1026 A B _99003 _99004) = (term1026 A B _99003 _99004)) = True.
Proof. exact (@lem7687773 (term1026 A B _99003 _99004)). Qed.
Lemma lem7687775 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : ((term991 A B _99003 _99004) = (term1026 A B _99003 _99004)) = True.
Proof. exact (TRANS (@lem7687770 A B _99003 _99004) (@lem7687774 A B _99003 _99004)). Qed.
Lemma lem7687776 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : True = ((term991 A B _99003 _99004) = (term1026 A B _99003 _99004)).
Proof. exact (SYM (@lem7687775 A B _99003 _99004)). Qed.
Lemma lem7687777 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : (term991 A B _99003 _99004) = (term1026 A B _99003 _99004).
Proof. exact (EQ_MP (@lem7687776 A B _99003 _99004) (@lem0)). Qed.
Lemma lem7687778 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : term1026 A B _99003 _99004.
Proof. exact (EQ_MP (@lem7687777 A B _99003 _99004) (@lem7687489 A B _99003 _99004)). Qed.
Lemma lem7687780 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7687781 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : (term1026 A B _99003 _99004) = (term1029 A B _99003 _99004).
Proof. exact (@lem7687780 (term1000 A B _99003 _99004) ((@dest_finite_diff A B _99003) = (@dest_finite_diff A B _99004))). Qed.
Lemma lem7687783 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7687784 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : (term1015 A B _99003 _99004) = (_99003 = _99004).
Proof. exact (@lem7687783 (_99003 = _99004)). Qed.
Lemma lem7687785 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7687786 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : (term1030 A B _99003 _99004) = (term1031 A B _99003 _99004).
Proof. exact (MK_COMB (@lem7687785) (@lem7687784 A B _99003 _99004)). Qed.
Lemma lem7687787 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : ((@dest_finite_diff A B _99003) = (@dest_finite_diff A B _99004)) = ((@dest_finite_diff A B _99003) = (@dest_finite_diff A B _99004)).
Proof. exact (eq_refl ((@dest_finite_diff A B _99003) = (@dest_finite_diff A B _99004))). Qed.
Lemma lem7687788 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : (term1029 A B _99003 _99004) = (term989 A B _99003 _99004).
Proof. exact (MK_COMB (@lem7687786 A B _99003 _99004) (@lem7687787 A B _99003 _99004)). Qed.
Lemma lem7687789 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : (term1026 A B _99003 _99004) = (term989 A B _99003 _99004).
Proof. exact (TRANS (@lem7687781 A B _99003 _99004) (@lem7687788 A B _99003 _99004)). Qed.
Lemma lem7687792 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : term989 A B _99003 _99004.
Proof. exact (EQ_MP (@lem7687789 A B _99003 _99004) (@lem7687778 A B _99003 _99004)). Qed.
Lemma lem7687793 {A B : Type'} (_99003 : finite_diff A B) (_99004 : finite_diff A B) : term989 A B _99003 _99004.
Proof. exact (@lem7687792 A B _99003 _99004). Qed.
Lemma lem7687794 {A B : Type'} (x : finite_diff A B) : term1032 A B x.
Proof. exact (@lem7687793 A B (term195 A B x) x). Qed.
Lemma lem7687797 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (@lem7687794 A B x (@lem7687741 A B x h1)). Qed.
Lemma lem7687798 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term1034 A B x.
Proof. exact (fun h0 : term1035 A B x => @lem7687797 A B x h1). Qed.
Lemma lem7687800 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7687801 {A B : Type'} (x : finite_diff A B) : (term1034 A B x) = ((term1033 A B x) = (@dest_finite_diff A B x)).
Proof. exact (@lem7687800 ((term1033 A B x) = (@dest_finite_diff A B x))). Qed.
Lemma lem7687802 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (EQ_MP (@lem7687801 A B x) (@lem7687798 A B x h1)). Qed.
Lemma lem7687804 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7687805 {A B : Type'} (_98838 : nat) : (term480 A B _98838) = (term1052 A B _98838).
Proof. exact (@lem7687804 (term1037 A B _98838) (term32 _98838)). Qed.
Lemma lem7687807 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7687808 {A B : Type'} (_98838 : nat) : (term1038 A B _98838) = ((term47 A B _98838) = _98838).
Proof. exact (@lem7687807 ((term47 A B _98838) = _98838)). Qed.
Lemma lem7687809 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7687810 {A B : Type'} (_98838 : nat) : (term1039 A B _98838) = (term1040 A B _98838).
Proof. exact (MK_COMB (@lem7687809) (@lem7687808 A B _98838)). Qed.
Lemma lem7687811 (_98838 : nat) : (term32 _98838) = (term32 _98838).
Proof. exact (eq_refl (term32 _98838)). Qed.
Lemma lem7687812 {A B : Type'} (_98838 : nat) : (term1052 A B _98838) = (term1053 A B _98838).
Proof. exact (MK_COMB (@lem7687810 A B _98838) (@lem7687811 _98838)). Qed.
Lemma lem7687813 {A B : Type'} (_98838 : nat) : (term480 A B _98838) = (term1053 A B _98838).
Proof. exact (TRANS (@lem7687805 A B _98838) (@lem7687812 A B _98838)). Qed.
Lemma lem7687816 {A B : Type'} (_98838 : nat) (x : finite_diff A B) (h1 : term711 A B x) : term1053 A B _98838.
Proof. exact (EQ_MP (@lem7687813 A B _98838) (@lem7685937 A B _98838 x h1)). Qed.
Lemma lem7687817 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term1054 A B x.
Proof. exact (@lem7687816 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7687820 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term1055 A B x.
Proof. exact (@lem7687817 A B x h1 (@lem7687802 A B x h1)). Qed.
Lemma lem7687821 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term1056 A B x.
Proof. exact (fun h0 : term1057 A B x => @lem7687820 A B x h1). Qed.
Lemma lem7687823 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7687824 {A B : Type'} (x : finite_diff A B) : (term1056 A B x) = (term1055 A B x).
Proof. exact (@lem7687823 (term1055 A B x)). Qed.
Lemma lem7687825 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term1055 A B x.
Proof. exact (EQ_MP (@lem7687824 A B x) (@lem7687821 A B x h1)). Qed.
Lemma lem7687827 (a : Prop) (b : Prop) : (term1046 a b) = (term1047 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7687828 {A B : Type'} (x : finite_diff A B) (_98833 : nat) : (term258 A B x _98833) = (term257 A B x _98833).
Proof. exact (@lem7687827 (x = (@mk_finite_diff A B _98833)) (term32 _98833)). Qed.
Lemma lem7687830 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7687831 {A B : Type'} (x : finite_diff A B) (_98833 : nat) : (term257 A B x _98833) = (term1058 A B x _98833).
Proof. exact (@lem7687830 (term35 A B x _98833)). Qed.
Lemma lem7687832 {A B : Type'} (x : finite_diff A B) (_98833 : nat) : (term258 A B x _98833) = (term1058 A B x _98833).
Proof. exact (TRANS (@lem7687828 A B x _98833) (@lem7687831 A B x _98833)). Qed.
Lemma lem7687834 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term1059 A B x.
Proof. exact (conj (@lem7687732 A B x h1) (@lem7687825 A B x h1)). Qed.
Lemma lem7687836 {A B : Type'} (_98833 : nat) (x : finite_diff A B) (h1 : term711 A B x) : term1058 A B x _98833.
Proof. exact (EQ_MP (@lem7687832 A B x _98833) (@lem7685915 A B _98833 x h1)). Qed.
Lemma lem7687837 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term1060 A B x.
Proof. exact (@lem7687836 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7687840 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : False.
Proof. exact (@lem7687837 A B x h1 (@lem7687834 A B x h1)). Qed.
Lemma lem7687841 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : term1051.
Proof. exact (fun h0 : ~ False => @lem7687840 A B x h1). Qed.
Lemma lem7687843 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7687844 : term1051 = False.
Proof. exact (@lem7687843 False). Qed.
Lemma lem7687845 {A B : Type'} (x : finite_diff A B) (h1 : term711 A B x) : False.
Proof. exact (EQ_MP (@lem7687844) (@lem7687841 A B x h1)). Qed.
Lemma lem7687900 {A B : Type'} : (@dest_finite_diff A B) = (@dest_finite_diff A B).
Proof. exact (eq_refl (@dest_finite_diff A B)). Qed.
Lemma lem7687901 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) (h1 : _99039 = _99040) : _99039 = _99040.
Proof. exact (h1). Qed.
Lemma lem7687902 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) (h1 : _99039 = _99040) : (@dest_finite_diff A B _99039) = (@dest_finite_diff A B _99040).
Proof. exact (MK_COMB (@lem7687900 A B) (@lem7687901 A B _99039 _99040 h1)). Qed.
Lemma lem7687903 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : term989 A B _99039 _99040.
Proof. exact (fun h0 : _99039 = _99040 => @lem7687902 A B _99039 _99040 h0). Qed.
Lemma lem7687905 (a : Prop) (b : Prop) : (a -> b) = (term990 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7687906 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : (term989 A B _99039 _99040) = (term991 A B _99039 _99040).
Proof. exact (@lem7687905 (_99039 = _99040) ((@dest_finite_diff A B _99039) = (@dest_finite_diff A B _99040))). Qed.
Lemma lem7687907 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : term991 A B _99039 _99040.
Proof. exact (EQ_MP (@lem7687906 A B _99039 _99040) (@lem7687903 A B _99039 _99040)). Qed.
Lemma lem7688003 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term992 A B x y z.
Proof. exact (@lem21385 (finite_diff A B) x y z). Qed.
Lemma lem7688009 {A B : Type'} (_98847 : finite_diff A B) (x : finite_diff A B) (h1 : term798 A B x) : (term195 A B _98847) = _98847.
Proof. exact (EQ_MP (@lem7685635 A B _98847) (@lem7685634 A B _98847 x h1)). Qed.
Lemma lem7688010 {A B : Type'} (_98847 : finite_diff A B) (x : finite_diff A B) (h1 : term798 A B x) : (term195 A B _98847) = _98847.
Proof. exact (@lem7688009 A B _98847 x h1). Qed.
Lemma lem7688011 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : (term195 A B x) = x.
Proof. exact (@lem7688010 A B x x h1). Qed.
Lemma lem7688012 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7688011 A B x h1). Qed.
Lemma lem7688014 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688015 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7688014 ((term195 A B x) = x)). Qed.
Lemma lem7688016 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7688015 A B x) (@lem7688012 A B x h1)). Qed.
Lemma lem7688018 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem21386 (finite_diff A B) x). Qed.
Lemma lem7688019 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem7688018 A B x). Qed.
Lemma lem7688020 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (@lem7688019 A B (term195 A B x)). Qed.
Lemma lem7688021 {A B : Type'} (x : finite_diff A B) : term996 A B x.
Proof. exact (fun h0 : term997 A B x => @lem7688020 A B x). Qed.
Lemma lem7688023 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688024 {A B : Type'} (x : finite_diff A B) : (term996 A B x) = ((term195 A B x) = (term195 A B x)).
Proof. exact (@lem7688023 ((term195 A B x) = (term195 A B x))). Qed.
Lemma lem7688025 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (EQ_MP (@lem7688024 A B x) (@lem7688021 A B x)). Qed.
Lemma lem7688043 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7688044 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term998 A B x y z) = (term999 A B y x z).
Proof. exact (@lem7688043 (y = z) (term1000 A B x z)). Qed.
Lemma lem7688054 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1001 A B x y) = (term1001 A B x y).
Proof. exact (eq_refl (term1001 A B x y)). Qed.
Lemma lem7688055 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1002 A B y x z).
Proof. exact (MK_COMB (@lem7688054 A B x y) (@lem7688044 A B y x z)). Qed.
Lemma lem7688059 (q : Prop) (p : Prop) (r : Prop) : (term1003 p q r) = (term1003 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7688060 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1002 A B y x z) = (term1004 A B y x z).
Proof. exact (@lem7688059 (y = z) (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7688082 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (TRANS (@lem7688055 A B y x z) (@lem7688060 A B y x z)). Qed.
Lemma lem7688083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7688084 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1005 A B x y z) = (term1006 A B y x z).
Proof. exact (MK_COMB (@lem7688083) (@lem7688082 A B y x z)). Qed.
Lemma lem7688106 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1004 A B y x z).
Proof. exact (eq_refl (term1004 A B y x z)). Qed.
Lemma lem7688107 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = ((term1004 A B y x z) = (term1004 A B y x z)).
Proof. exact (MK_COMB (@lem7688084 A B y x z) (@lem7688106 A B y x z)). Qed.
Lemma lem7688109 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7688110 (x : Prop) : (x = x) = True.
Proof. exact (@lem7688109 Prop x). Qed.
Lemma lem7688111 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term1004 A B y x z) = (term1004 A B y x z)) = True.
Proof. exact (@lem7688110 (term1004 A B y x z)). Qed.
Lemma lem7688112 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = True.
Proof. exact (TRANS (@lem7688107 A B y x z) (@lem7688111 A B y x z)). Qed.
Lemma lem7688113 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : True = ((term992 A B x y z) = (term1004 A B y x z)).
Proof. exact (SYM (@lem7688112 A B y x z)). Qed.
Lemma lem7688114 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (EQ_MP (@lem7688113 A B y x z) (@lem0)). Qed.
Lemma lem7688115 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : term1004 A B y x z.
Proof. exact (EQ_MP (@lem7688114 A B y x z) (@lem7688003 A B x y z)). Qed.
Lemma lem7688117 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7688118 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1008 A B x y z).
Proof. exact (@lem7688117 (term1009 A B y x z) (y = z)). Qed.
Lemma lem7688120 (a : Prop) (b : Prop) : (term1010 a b) = (term1011 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7688121 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1013 A B y x z).
Proof. exact (@lem7688120 (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7688123 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7688124 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1015 A B x y) = (x = y).
Proof. exact (@lem7688123 (x = y)). Qed.
Lemma lem7688125 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7688126 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1016 A B x y) = (term1017 A B x y).
Proof. exact (MK_COMB (@lem7688125) (@lem7688124 A B x y)). Qed.
Lemma lem7688128 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7688129 {A B : Type'} (x : finite_diff A B) (z : finite_diff A B) : (term1015 A B x z) = (x = z).
Proof. exact (@lem7688128 (x = z)). Qed.
Lemma lem7688130 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1013 A B y x z) = (term1018 A B y x z).
Proof. exact (MK_COMB (@lem7688126 A B x y) (@lem7688129 A B x z)). Qed.
Lemma lem7688131 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1018 A B y x z).
Proof. exact (TRANS (@lem7688121 A B y x z) (@lem7688130 A B y x z)). Qed.
Lemma lem7688132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7688133 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1019 A B y x z) = (term1020 A B y x z).
Proof. exact (MK_COMB (@lem7688132) (@lem7688131 A B y x z)). Qed.
Lemma lem7688134 {A B : Type'} (y : finite_diff A B) (z : finite_diff A B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7688135 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1008 A B x y z) = (term1021 A B x y z).
Proof. exact (MK_COMB (@lem7688133 A B y x z) (@lem7688134 A B y z)). Qed.
Lemma lem7688136 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1021 A B x y z).
Proof. exact (TRANS (@lem7688118 A B x y z) (@lem7688135 A B x y z)). Qed.
Lemma lem7688138 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term1022 A B x.
Proof. exact (conj (@lem7688016 A B x h1) (@lem7688025 A B x)). Qed.
Lemma lem7688140 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (EQ_MP (@lem7688136 A B x y z) (@lem7688115 A B y x z)). Qed.
Lemma lem7688141 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (@lem7688140 A B x y z). Qed.
Lemma lem7688142 {A B : Type'} (x : finite_diff A B) : term1023 A B x.
Proof. exact (@lem7688141 A B (term195 A B x) x (term195 A B x)). Qed.
Lemma lem7688145 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : x = (term195 A B x).
Proof. exact (@lem7688142 A B x (@lem7688138 A B x h1)). Qed.
Lemma lem7688146 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term1024 A B x.
Proof. exact (fun h0 : term1025 A B x => @lem7688145 A B x h1). Qed.
Lemma lem7688148 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688149 {A B : Type'} (x : finite_diff A B) : (term1024 A B x) = (x = (term195 A B x)).
Proof. exact (@lem7688148 (x = (term195 A B x))). Qed.
Lemma lem7688150 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : x = (term195 A B x).
Proof. exact (EQ_MP (@lem7688149 A B x) (@lem7688146 A B x h1)). Qed.
Lemma lem7688152 {A B : Type'} (_98847 : finite_diff A B) (x : finite_diff A B) (h1 : term798 A B x) : (term195 A B _98847) = _98847.
Proof. exact (EQ_MP (@lem7685635 A B _98847) (@lem7685634 A B _98847 x h1)). Qed.
Lemma lem7688153 {A B : Type'} (_98847 : finite_diff A B) (x : finite_diff A B) (h1 : term798 A B x) : (term195 A B _98847) = _98847.
Proof. exact (@lem7688152 A B _98847 x h1). Qed.
Lemma lem7688154 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : (term195 A B x) = x.
Proof. exact (@lem7688153 A B x x h1). Qed.
Lemma lem7688155 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7688154 A B x h1). Qed.
Lemma lem7688157 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688158 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7688157 ((term195 A B x) = x)). Qed.
Lemma lem7688159 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7688158 A B x) (@lem7688155 A B x h1)). Qed.
Lemma lem7688165 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7688166 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : (term991 A B _99039 _99040) = (term1026 A B _99039 _99040).
Proof. exact (@lem7688165 ((@dest_finite_diff A B _99039) = (@dest_finite_diff A B _99040)) (term1000 A B _99039 _99040)). Qed.
Lemma lem7688176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7688177 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : (term1027 A B _99039 _99040) = (term1028 A B _99039 _99040).
Proof. exact (MK_COMB (@lem7688176) (@lem7688166 A B _99039 _99040)). Qed.
Lemma lem7688187 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : (term1026 A B _99039 _99040) = (term1026 A B _99039 _99040).
Proof. exact (eq_refl (term1026 A B _99039 _99040)). Qed.
Lemma lem7688188 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : ((term991 A B _99039 _99040) = (term1026 A B _99039 _99040)) = ((term1026 A B _99039 _99040) = (term1026 A B _99039 _99040)).
Proof. exact (MK_COMB (@lem7688177 A B _99039 _99040) (@lem7688187 A B _99039 _99040)). Qed.
Lemma lem7688190 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7688191 (x : Prop) : (x = x) = True.
Proof. exact (@lem7688190 Prop x). Qed.
Lemma lem7688192 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : ((term1026 A B _99039 _99040) = (term1026 A B _99039 _99040)) = True.
Proof. exact (@lem7688191 (term1026 A B _99039 _99040)). Qed.
Lemma lem7688193 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : ((term991 A B _99039 _99040) = (term1026 A B _99039 _99040)) = True.
Proof. exact (TRANS (@lem7688188 A B _99039 _99040) (@lem7688192 A B _99039 _99040)). Qed.
Lemma lem7688194 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : True = ((term991 A B _99039 _99040) = (term1026 A B _99039 _99040)).
Proof. exact (SYM (@lem7688193 A B _99039 _99040)). Qed.
Lemma lem7688195 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : (term991 A B _99039 _99040) = (term1026 A B _99039 _99040).
Proof. exact (EQ_MP (@lem7688194 A B _99039 _99040) (@lem0)). Qed.
Lemma lem7688196 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : term1026 A B _99039 _99040.
Proof. exact (EQ_MP (@lem7688195 A B _99039 _99040) (@lem7687907 A B _99039 _99040)). Qed.
Lemma lem7688198 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7688199 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : (term1026 A B _99039 _99040) = (term1029 A B _99039 _99040).
Proof. exact (@lem7688198 (term1000 A B _99039 _99040) ((@dest_finite_diff A B _99039) = (@dest_finite_diff A B _99040))). Qed.
Lemma lem7688201 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7688202 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : (term1015 A B _99039 _99040) = (_99039 = _99040).
Proof. exact (@lem7688201 (_99039 = _99040)). Qed.
Lemma lem7688203 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7688204 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : (term1030 A B _99039 _99040) = (term1031 A B _99039 _99040).
Proof. exact (MK_COMB (@lem7688203) (@lem7688202 A B _99039 _99040)). Qed.
Lemma lem7688205 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : ((@dest_finite_diff A B _99039) = (@dest_finite_diff A B _99040)) = ((@dest_finite_diff A B _99039) = (@dest_finite_diff A B _99040)).
Proof. exact (eq_refl ((@dest_finite_diff A B _99039) = (@dest_finite_diff A B _99040))). Qed.
Lemma lem7688206 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : (term1029 A B _99039 _99040) = (term989 A B _99039 _99040).
Proof. exact (MK_COMB (@lem7688204 A B _99039 _99040) (@lem7688205 A B _99039 _99040)). Qed.
Lemma lem7688207 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : (term1026 A B _99039 _99040) = (term989 A B _99039 _99040).
Proof. exact (TRANS (@lem7688199 A B _99039 _99040) (@lem7688206 A B _99039 _99040)). Qed.
Lemma lem7688210 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : term989 A B _99039 _99040.
Proof. exact (EQ_MP (@lem7688207 A B _99039 _99040) (@lem7688196 A B _99039 _99040)). Qed.
Lemma lem7688211 {A B : Type'} (_99039 : finite_diff A B) (_99040 : finite_diff A B) : term989 A B _99039 _99040.
Proof. exact (@lem7688210 A B _99039 _99040). Qed.
Lemma lem7688212 {A B : Type'} (x : finite_diff A B) : term1032 A B x.
Proof. exact (@lem7688211 A B (term195 A B x) x). Qed.
Lemma lem7688215 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (@lem7688212 A B x (@lem7688159 A B x h1)). Qed.
Lemma lem7688216 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term1034 A B x.
Proof. exact (fun h0 : term1035 A B x => @lem7688215 A B x h1). Qed.
Lemma lem7688218 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688219 {A B : Type'} (x : finite_diff A B) : (term1034 A B x) = ((term1033 A B x) = (@dest_finite_diff A B x)).
Proof. exact (@lem7688218 ((term1033 A B x) = (@dest_finite_diff A B x))). Qed.
Lemma lem7688220 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (EQ_MP (@lem7688219 A B x) (@lem7688216 A B x h1)). Qed.
Lemma lem7688222 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7688223 {A B : Type'} (_98848 : nat) : (term450 A B _98848) = (term1036 A B _98848).
Proof. exact (@lem7688222 (term1037 A B _98848) (term62 A B _98848)). Qed.
Lemma lem7688225 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7688226 {A B : Type'} (_98848 : nat) : (term1038 A B _98848) = ((term47 A B _98848) = _98848).
Proof. exact (@lem7688225 ((term47 A B _98848) = _98848)). Qed.
Lemma lem7688227 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7688228 {A B : Type'} (_98848 : nat) : (term1039 A B _98848) = (term1040 A B _98848).
Proof. exact (MK_COMB (@lem7688227) (@lem7688226 A B _98848)). Qed.
Lemma lem7688229 {A B : Type'} (_98848 : nat) : (term62 A B _98848) = (term62 A B _98848).
Proof. exact (eq_refl (term62 A B _98848)). Qed.
Lemma lem7688230 {A B : Type'} (_98848 : nat) : (term1036 A B _98848) = (term1041 A B _98848).
Proof. exact (MK_COMB (@lem7688228 A B _98848) (@lem7688229 A B _98848)). Qed.
Lemma lem7688231 {A B : Type'} (_98848 : nat) : (term450 A B _98848) = (term1041 A B _98848).
Proof. exact (TRANS (@lem7688223 A B _98848) (@lem7688230 A B _98848)). Qed.
Lemma lem7688234 {A B : Type'} (_98848 : nat) (x : finite_diff A B) (h1 : term798 A B x) : term1041 A B _98848.
Proof. exact (EQ_MP (@lem7688231 A B _98848) (@lem7685991 A B _98848 x h1)). Qed.
Lemma lem7688235 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term1042 A B x.
Proof. exact (@lem7688234 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7688238 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term1043 A B x.
Proof. exact (@lem7688235 A B x h1 (@lem7688220 A B x h1)). Qed.
Lemma lem7688239 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term1044 A B x.
Proof. exact (fun h0 : term1045 A B x => @lem7688238 A B x h1). Qed.
Lemma lem7688241 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688242 {A B : Type'} (x : finite_diff A B) : (term1044 A B x) = (term1043 A B x).
Proof. exact (@lem7688241 (term1043 A B x)). Qed.
Lemma lem7688243 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term1043 A B x.
Proof. exact (EQ_MP (@lem7688242 A B x) (@lem7688239 A B x h1)). Qed.
Lemma lem7688245 (a : Prop) (b : Prop) : (term1046 a b) = (term1047 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7688246 {A B : Type'} (x : finite_diff A B) (_98843 : nat) : (term209 A B x _98843) = (term208 A B x _98843).
Proof. exact (@lem7688245 (x = (@mk_finite_diff A B _98843)) (term62 A B _98843)). Qed.
Lemma lem7688248 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7688249 {A B : Type'} (x : finite_diff A B) (_98843 : nat) : (term208 A B x _98843) = (term1048 A B x _98843).
Proof. exact (@lem7688248 (term63 A B x _98843)). Qed.
Lemma lem7688250 {A B : Type'} (x : finite_diff A B) (_98843 : nat) : (term209 A B x _98843) = (term1048 A B x _98843).
Proof. exact (TRANS (@lem7688246 A B x _98843) (@lem7688249 A B x _98843)). Qed.
Lemma lem7688252 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term1049 A B x.
Proof. exact (conj (@lem7688150 A B x h1) (@lem7688243 A B x h1)). Qed.
Lemma lem7688254 {A B : Type'} (_98843 : nat) (x : finite_diff A B) (h1 : term798 A B x) : term1048 A B x _98843.
Proof. exact (EQ_MP (@lem7688250 A B x _98843) (@lem7685969 A B _98843 x h1)). Qed.
Lemma lem7688255 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term1050 A B x.
Proof. exact (@lem7688254 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7688258 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : False.
Proof. exact (@lem7688255 A B x h1 (@lem7688252 A B x h1)). Qed.
Lemma lem7688259 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : term1051.
Proof. exact (fun h0 : ~ False => @lem7688258 A B x h1). Qed.
Lemma lem7688261 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688262 : term1051 = False.
Proof. exact (@lem7688261 False). Qed.
Lemma lem7688263 {A B : Type'} (x : finite_diff A B) (h1 : term798 A B x) : False.
Proof. exact (EQ_MP (@lem7688262) (@lem7688259 A B x h1)). Qed.
Lemma lem7688333 {A B : Type'} : (@dest_finite_diff A B) = (@dest_finite_diff A B).
Proof. exact (eq_refl (@dest_finite_diff A B)). Qed.
Lemma lem7688334 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) (h1 : _99079 = _99080) : _99079 = _99080.
Proof. exact (h1). Qed.
Lemma lem7688335 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) (h1 : _99079 = _99080) : (@dest_finite_diff A B _99079) = (@dest_finite_diff A B _99080).
Proof. exact (MK_COMB (@lem7688333 A B) (@lem7688334 A B _99079 _99080 h1)). Qed.
Lemma lem7688336 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : term989 A B _99079 _99080.
Proof. exact (fun h0 : _99079 = _99080 => @lem7688335 A B _99079 _99080 h0). Qed.
Lemma lem7688338 (a : Prop) (b : Prop) : (a -> b) = (term990 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7688339 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : (term989 A B _99079 _99080) = (term991 A B _99079 _99080).
Proof. exact (@lem7688338 (_99079 = _99080) ((@dest_finite_diff A B _99079) = (@dest_finite_diff A B _99080))). Qed.
Lemma lem7688340 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : term991 A B _99079 _99080.
Proof. exact (EQ_MP (@lem7688339 A B _99079 _99080) (@lem7688336 A B _99079 _99080)). Qed.
Lemma lem7688421 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term992 A B x y z.
Proof. exact (@lem21385 (finite_diff A B) x y z). Qed.
Lemma lem7688427 {A B : Type'} (_98857 : finite_diff A B) (x : finite_diff A B) (h1 : term821 A B x) : (term195 A B _98857) = _98857.
Proof. exact (EQ_MP (@lem7685665 A B _98857) (@lem7685664 A B _98857 x h1)). Qed.
Lemma lem7688428 {A B : Type'} (_98857 : finite_diff A B) (x : finite_diff A B) (h1 : term821 A B x) : (term195 A B _98857) = _98857.
Proof. exact (@lem7688427 A B _98857 x h1). Qed.
Lemma lem7688429 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : (term195 A B x) = x.
Proof. exact (@lem7688428 A B x x h1). Qed.
Lemma lem7688430 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7688429 A B x h1). Qed.
Lemma lem7688432 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688433 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7688432 ((term195 A B x) = x)). Qed.
Lemma lem7688434 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7688433 A B x) (@lem7688430 A B x h1)). Qed.
Lemma lem7688436 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem21386 (finite_diff A B) x). Qed.
Lemma lem7688437 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem7688436 A B x). Qed.
Lemma lem7688438 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (@lem7688437 A B (term195 A B x)). Qed.
Lemma lem7688439 {A B : Type'} (x : finite_diff A B) : term996 A B x.
Proof. exact (fun h0 : term997 A B x => @lem7688438 A B x). Qed.
Lemma lem7688441 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688442 {A B : Type'} (x : finite_diff A B) : (term996 A B x) = ((term195 A B x) = (term195 A B x)).
Proof. exact (@lem7688441 ((term195 A B x) = (term195 A B x))). Qed.
Lemma lem7688443 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (EQ_MP (@lem7688442 A B x) (@lem7688439 A B x)). Qed.
Lemma lem7688461 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7688462 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term998 A B x y z) = (term999 A B y x z).
Proof. exact (@lem7688461 (y = z) (term1000 A B x z)). Qed.
Lemma lem7688472 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1001 A B x y) = (term1001 A B x y).
Proof. exact (eq_refl (term1001 A B x y)). Qed.
Lemma lem7688473 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1002 A B y x z).
Proof. exact (MK_COMB (@lem7688472 A B x y) (@lem7688462 A B y x z)). Qed.
Lemma lem7688477 (q : Prop) (p : Prop) (r : Prop) : (term1003 p q r) = (term1003 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7688478 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1002 A B y x z) = (term1004 A B y x z).
Proof. exact (@lem7688477 (y = z) (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7688500 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (TRANS (@lem7688473 A B y x z) (@lem7688478 A B y x z)). Qed.
Lemma lem7688501 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7688502 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1005 A B x y z) = (term1006 A B y x z).
Proof. exact (MK_COMB (@lem7688501) (@lem7688500 A B y x z)). Qed.
Lemma lem7688524 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1004 A B y x z).
Proof. exact (eq_refl (term1004 A B y x z)). Qed.
Lemma lem7688525 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = ((term1004 A B y x z) = (term1004 A B y x z)).
Proof. exact (MK_COMB (@lem7688502 A B y x z) (@lem7688524 A B y x z)). Qed.
Lemma lem7688527 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7688528 (x : Prop) : (x = x) = True.
Proof. exact (@lem7688527 Prop x). Qed.
Lemma lem7688529 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term1004 A B y x z) = (term1004 A B y x z)) = True.
Proof. exact (@lem7688528 (term1004 A B y x z)). Qed.
Lemma lem7688530 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = True.
Proof. exact (TRANS (@lem7688525 A B y x z) (@lem7688529 A B y x z)). Qed.
Lemma lem7688531 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : True = ((term992 A B x y z) = (term1004 A B y x z)).
Proof. exact (SYM (@lem7688530 A B y x z)). Qed.
Lemma lem7688532 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (EQ_MP (@lem7688531 A B y x z) (@lem0)). Qed.
Lemma lem7688533 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : term1004 A B y x z.
Proof. exact (EQ_MP (@lem7688532 A B y x z) (@lem7688421 A B x y z)). Qed.
Lemma lem7688535 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7688536 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1008 A B x y z).
Proof. exact (@lem7688535 (term1009 A B y x z) (y = z)). Qed.
Lemma lem7688538 (a : Prop) (b : Prop) : (term1010 a b) = (term1011 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7688539 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1013 A B y x z).
Proof. exact (@lem7688538 (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7688541 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7688542 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1015 A B x y) = (x = y).
Proof. exact (@lem7688541 (x = y)). Qed.
Lemma lem7688543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7688544 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1016 A B x y) = (term1017 A B x y).
Proof. exact (MK_COMB (@lem7688543) (@lem7688542 A B x y)). Qed.
Lemma lem7688546 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7688547 {A B : Type'} (x : finite_diff A B) (z : finite_diff A B) : (term1015 A B x z) = (x = z).
Proof. exact (@lem7688546 (x = z)). Qed.
Lemma lem7688548 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1013 A B y x z) = (term1018 A B y x z).
Proof. exact (MK_COMB (@lem7688544 A B x y) (@lem7688547 A B x z)). Qed.
Lemma lem7688549 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1018 A B y x z).
Proof. exact (TRANS (@lem7688539 A B y x z) (@lem7688548 A B y x z)). Qed.
Lemma lem7688550 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7688551 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1019 A B y x z) = (term1020 A B y x z).
Proof. exact (MK_COMB (@lem7688550) (@lem7688549 A B y x z)). Qed.
Lemma lem7688552 {A B : Type'} (y : finite_diff A B) (z : finite_diff A B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7688553 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1008 A B x y z) = (term1021 A B x y z).
Proof. exact (MK_COMB (@lem7688551 A B y x z) (@lem7688552 A B y z)). Qed.
Lemma lem7688554 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1021 A B x y z).
Proof. exact (TRANS (@lem7688536 A B x y z) (@lem7688553 A B x y z)). Qed.
Lemma lem7688556 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term1022 A B x.
Proof. exact (conj (@lem7688434 A B x h1) (@lem7688443 A B x)). Qed.
Lemma lem7688558 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (EQ_MP (@lem7688554 A B x y z) (@lem7688533 A B y x z)). Qed.
Lemma lem7688559 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (@lem7688558 A B x y z). Qed.
Lemma lem7688560 {A B : Type'} (x : finite_diff A B) : term1023 A B x.
Proof. exact (@lem7688559 A B (term195 A B x) x (term195 A B x)). Qed.
Lemma lem7688563 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : x = (term195 A B x).
Proof. exact (@lem7688560 A B x (@lem7688556 A B x h1)). Qed.
Lemma lem7688564 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term1024 A B x.
Proof. exact (fun h0 : term1025 A B x => @lem7688563 A B x h1). Qed.
Lemma lem7688566 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688567 {A B : Type'} (x : finite_diff A B) : (term1024 A B x) = (x = (term195 A B x)).
Proof. exact (@lem7688566 (x = (term195 A B x))). Qed.
Lemma lem7688568 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : x = (term195 A B x).
Proof. exact (EQ_MP (@lem7688567 A B x) (@lem7688564 A B x h1)). Qed.
Lemma lem7688570 {A B : Type'} (_98857 : finite_diff A B) (x : finite_diff A B) (h1 : term821 A B x) : (term195 A B _98857) = _98857.
Proof. exact (EQ_MP (@lem7685665 A B _98857) (@lem7685664 A B _98857 x h1)). Qed.
Lemma lem7688571 {A B : Type'} (_98857 : finite_diff A B) (x : finite_diff A B) (h1 : term821 A B x) : (term195 A B _98857) = _98857.
Proof. exact (@lem7688570 A B _98857 x h1). Qed.
Lemma lem7688572 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : (term195 A B x) = x.
Proof. exact (@lem7688571 A B x x h1). Qed.
Lemma lem7688573 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7688572 A B x h1). Qed.
Lemma lem7688575 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688576 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7688575 ((term195 A B x) = x)). Qed.
Lemma lem7688577 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7688576 A B x) (@lem7688573 A B x h1)). Qed.
Lemma lem7688583 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7688584 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : (term991 A B _99079 _99080) = (term1026 A B _99079 _99080).
Proof. exact (@lem7688583 ((@dest_finite_diff A B _99079) = (@dest_finite_diff A B _99080)) (term1000 A B _99079 _99080)). Qed.
Lemma lem7688594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7688595 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : (term1027 A B _99079 _99080) = (term1028 A B _99079 _99080).
Proof. exact (MK_COMB (@lem7688594) (@lem7688584 A B _99079 _99080)). Qed.
Lemma lem7688605 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : (term1026 A B _99079 _99080) = (term1026 A B _99079 _99080).
Proof. exact (eq_refl (term1026 A B _99079 _99080)). Qed.
Lemma lem7688606 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : ((term991 A B _99079 _99080) = (term1026 A B _99079 _99080)) = ((term1026 A B _99079 _99080) = (term1026 A B _99079 _99080)).
Proof. exact (MK_COMB (@lem7688595 A B _99079 _99080) (@lem7688605 A B _99079 _99080)). Qed.
Lemma lem7688608 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7688609 (x : Prop) : (x = x) = True.
Proof. exact (@lem7688608 Prop x). Qed.
Lemma lem7688610 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : ((term1026 A B _99079 _99080) = (term1026 A B _99079 _99080)) = True.
Proof. exact (@lem7688609 (term1026 A B _99079 _99080)). Qed.
Lemma lem7688611 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : ((term991 A B _99079 _99080) = (term1026 A B _99079 _99080)) = True.
Proof. exact (TRANS (@lem7688606 A B _99079 _99080) (@lem7688610 A B _99079 _99080)). Qed.
Lemma lem7688612 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : True = ((term991 A B _99079 _99080) = (term1026 A B _99079 _99080)).
Proof. exact (SYM (@lem7688611 A B _99079 _99080)). Qed.
Lemma lem7688613 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : (term991 A B _99079 _99080) = (term1026 A B _99079 _99080).
Proof. exact (EQ_MP (@lem7688612 A B _99079 _99080) (@lem0)). Qed.
Lemma lem7688614 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : term1026 A B _99079 _99080.
Proof. exact (EQ_MP (@lem7688613 A B _99079 _99080) (@lem7688340 A B _99079 _99080)). Qed.
Lemma lem7688616 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7688617 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : (term1026 A B _99079 _99080) = (term1029 A B _99079 _99080).
Proof. exact (@lem7688616 (term1000 A B _99079 _99080) ((@dest_finite_diff A B _99079) = (@dest_finite_diff A B _99080))). Qed.
Lemma lem7688619 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7688620 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : (term1015 A B _99079 _99080) = (_99079 = _99080).
Proof. exact (@lem7688619 (_99079 = _99080)). Qed.
Lemma lem7688621 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7688622 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : (term1030 A B _99079 _99080) = (term1031 A B _99079 _99080).
Proof. exact (MK_COMB (@lem7688621) (@lem7688620 A B _99079 _99080)). Qed.
Lemma lem7688623 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : ((@dest_finite_diff A B _99079) = (@dest_finite_diff A B _99080)) = ((@dest_finite_diff A B _99079) = (@dest_finite_diff A B _99080)).
Proof. exact (eq_refl ((@dest_finite_diff A B _99079) = (@dest_finite_diff A B _99080))). Qed.
Lemma lem7688624 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : (term1029 A B _99079 _99080) = (term989 A B _99079 _99080).
Proof. exact (MK_COMB (@lem7688622 A B _99079 _99080) (@lem7688623 A B _99079 _99080)). Qed.
Lemma lem7688625 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : (term1026 A B _99079 _99080) = (term989 A B _99079 _99080).
Proof. exact (TRANS (@lem7688617 A B _99079 _99080) (@lem7688624 A B _99079 _99080)). Qed.
Lemma lem7688628 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : term989 A B _99079 _99080.
Proof. exact (EQ_MP (@lem7688625 A B _99079 _99080) (@lem7688614 A B _99079 _99080)). Qed.
Lemma lem7688629 {A B : Type'} (_99079 : finite_diff A B) (_99080 : finite_diff A B) : term989 A B _99079 _99080.
Proof. exact (@lem7688628 A B _99079 _99080). Qed.
Lemma lem7688630 {A B : Type'} (x : finite_diff A B) : term1032 A B x.
Proof. exact (@lem7688629 A B (term195 A B x) x). Qed.
Lemma lem7688633 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (@lem7688630 A B x (@lem7688577 A B x h1)). Qed.
Lemma lem7688634 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term1034 A B x.
Proof. exact (fun h0 : term1035 A B x => @lem7688633 A B x h1). Qed.
Lemma lem7688636 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688637 {A B : Type'} (x : finite_diff A B) : (term1034 A B x) = ((term1033 A B x) = (@dest_finite_diff A B x)).
Proof. exact (@lem7688636 ((term1033 A B x) = (@dest_finite_diff A B x))). Qed.
Lemma lem7688638 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (EQ_MP (@lem7688637 A B x) (@lem7688634 A B x h1)). Qed.
Lemma lem7688640 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7688641 {A B : Type'} (_98858 : nat) : (term480 A B _98858) = (term1052 A B _98858).
Proof. exact (@lem7688640 (term1037 A B _98858) (term32 _98858)). Qed.
Lemma lem7688643 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7688644 {A B : Type'} (_98858 : nat) : (term1038 A B _98858) = ((term47 A B _98858) = _98858).
Proof. exact (@lem7688643 ((term47 A B _98858) = _98858)). Qed.
Lemma lem7688645 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7688646 {A B : Type'} (_98858 : nat) : (term1039 A B _98858) = (term1040 A B _98858).
Proof. exact (MK_COMB (@lem7688645) (@lem7688644 A B _98858)). Qed.
Lemma lem7688647 (_98858 : nat) : (term32 _98858) = (term32 _98858).
Proof. exact (eq_refl (term32 _98858)). Qed.
Lemma lem7688648 {A B : Type'} (_98858 : nat) : (term1052 A B _98858) = (term1053 A B _98858).
Proof. exact (MK_COMB (@lem7688646 A B _98858) (@lem7688647 _98858)). Qed.
Lemma lem7688649 {A B : Type'} (_98858 : nat) : (term480 A B _98858) = (term1053 A B _98858).
Proof. exact (TRANS (@lem7688641 A B _98858) (@lem7688648 A B _98858)). Qed.
Lemma lem7688652 {A B : Type'} (_98858 : nat) (x : finite_diff A B) (h1 : term821 A B x) : term1053 A B _98858.
Proof. exact (EQ_MP (@lem7688649 A B _98858) (@lem7686045 A B _98858 x h1)). Qed.
Lemma lem7688653 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term1054 A B x.
Proof. exact (@lem7688652 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7688656 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term1055 A B x.
Proof. exact (@lem7688653 A B x h1 (@lem7688638 A B x h1)). Qed.
Lemma lem7688657 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term1056 A B x.
Proof. exact (fun h0 : term1057 A B x => @lem7688656 A B x h1). Qed.
Lemma lem7688659 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688660 {A B : Type'} (x : finite_diff A B) : (term1056 A B x) = (term1055 A B x).
Proof. exact (@lem7688659 (term1055 A B x)). Qed.
Lemma lem7688661 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term1055 A B x.
Proof. exact (EQ_MP (@lem7688660 A B x) (@lem7688657 A B x h1)). Qed.
Lemma lem7688663 (a : Prop) (b : Prop) : (term1046 a b) = (term1047 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7688664 {A B : Type'} (x : finite_diff A B) (_98853 : nat) : (term258 A B x _98853) = (term257 A B x _98853).
Proof. exact (@lem7688663 (x = (@mk_finite_diff A B _98853)) (term32 _98853)). Qed.
Lemma lem7688666 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7688667 {A B : Type'} (x : finite_diff A B) (_98853 : nat) : (term257 A B x _98853) = (term1058 A B x _98853).
Proof. exact (@lem7688666 (term35 A B x _98853)). Qed.
Lemma lem7688668 {A B : Type'} (x : finite_diff A B) (_98853 : nat) : (term258 A B x _98853) = (term1058 A B x _98853).
Proof. exact (TRANS (@lem7688664 A B x _98853) (@lem7688667 A B x _98853)). Qed.
Lemma lem7688670 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term1059 A B x.
Proof. exact (conj (@lem7688568 A B x h1) (@lem7688661 A B x h1)). Qed.
Lemma lem7688672 {A B : Type'} (_98853 : nat) (x : finite_diff A B) (h1 : term821 A B x) : term1058 A B x _98853.
Proof. exact (EQ_MP (@lem7688668 A B x _98853) (@lem7686023 A B _98853 x h1)). Qed.
Lemma lem7688673 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term1060 A B x.
Proof. exact (@lem7688672 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7688676 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : False.
Proof. exact (@lem7688673 A B x h1 (@lem7688670 A B x h1)). Qed.
Lemma lem7688677 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : term1051.
Proof. exact (fun h0 : ~ False => @lem7688676 A B x h1). Qed.
Lemma lem7688679 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688680 : term1051 = False.
Proof. exact (@lem7688679 False). Qed.
Lemma lem7688681 {A B : Type'} (x : finite_diff A B) (h1 : term821 A B x) : False.
Proof. exact (EQ_MP (@lem7688680) (@lem7688677 A B x h1)). Qed.
Lemma lem7688736 {A B : Type'} : (@dest_finite_diff A B) = (@dest_finite_diff A B).
Proof. exact (eq_refl (@dest_finite_diff A B)). Qed.
Lemma lem7688737 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) (h1 : _99111 = _99112) : _99111 = _99112.
Proof. exact (h1). Qed.
Lemma lem7688738 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) (h1 : _99111 = _99112) : (@dest_finite_diff A B _99111) = (@dest_finite_diff A B _99112).
Proof. exact (MK_COMB (@lem7688736 A B) (@lem7688737 A B _99111 _99112 h1)). Qed.
Lemma lem7688739 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : term989 A B _99111 _99112.
Proof. exact (fun h0 : _99111 = _99112 => @lem7688738 A B _99111 _99112 h0). Qed.
Lemma lem7688741 (a : Prop) (b : Prop) : (a -> b) = (term990 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7688742 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : (term989 A B _99111 _99112) = (term991 A B _99111 _99112).
Proof. exact (@lem7688741 (_99111 = _99112) ((@dest_finite_diff A B _99111) = (@dest_finite_diff A B _99112))). Qed.
Lemma lem7688743 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : term991 A B _99111 _99112.
Proof. exact (EQ_MP (@lem7688742 A B _99111 _99112) (@lem7688739 A B _99111 _99112)). Qed.
Lemma lem7688839 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term992 A B x y z.
Proof. exact (@lem21385 (finite_diff A B) x y z). Qed.
Lemma lem7688845 {A B : Type'} (_98867 : finite_diff A B) (x : finite_diff A B) (h1 : term876 A B x) : (term195 A B _98867) = _98867.
Proof. exact (EQ_MP (@lem7685695 A B _98867) (@lem7685694 A B _98867 x h1)). Qed.
Lemma lem7688846 {A B : Type'} (_98867 : finite_diff A B) (x : finite_diff A B) (h1 : term876 A B x) : (term195 A B _98867) = _98867.
Proof. exact (@lem7688845 A B _98867 x h1). Qed.
Lemma lem7688847 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : (term195 A B x) = x.
Proof. exact (@lem7688846 A B x x h1). Qed.
Lemma lem7688848 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7688847 A B x h1). Qed.
Lemma lem7688850 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688851 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7688850 ((term195 A B x) = x)). Qed.
Lemma lem7688852 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7688851 A B x) (@lem7688848 A B x h1)). Qed.
Lemma lem7688854 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem21386 (finite_diff A B) x). Qed.
Lemma lem7688855 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem7688854 A B x). Qed.
Lemma lem7688856 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (@lem7688855 A B (term195 A B x)). Qed.
Lemma lem7688857 {A B : Type'} (x : finite_diff A B) : term996 A B x.
Proof. exact (fun h0 : term997 A B x => @lem7688856 A B x). Qed.
Lemma lem7688859 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688860 {A B : Type'} (x : finite_diff A B) : (term996 A B x) = ((term195 A B x) = (term195 A B x)).
Proof. exact (@lem7688859 ((term195 A B x) = (term195 A B x))). Qed.
Lemma lem7688861 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (EQ_MP (@lem7688860 A B x) (@lem7688857 A B x)). Qed.
Lemma lem7688879 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7688880 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term998 A B x y z) = (term999 A B y x z).
Proof. exact (@lem7688879 (y = z) (term1000 A B x z)). Qed.
Lemma lem7688890 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1001 A B x y) = (term1001 A B x y).
Proof. exact (eq_refl (term1001 A B x y)). Qed.
Lemma lem7688891 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1002 A B y x z).
Proof. exact (MK_COMB (@lem7688890 A B x y) (@lem7688880 A B y x z)). Qed.
Lemma lem7688895 (q : Prop) (p : Prop) (r : Prop) : (term1003 p q r) = (term1003 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7688896 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1002 A B y x z) = (term1004 A B y x z).
Proof. exact (@lem7688895 (y = z) (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7688918 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (TRANS (@lem7688891 A B y x z) (@lem7688896 A B y x z)). Qed.
Lemma lem7688919 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7688920 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1005 A B x y z) = (term1006 A B y x z).
Proof. exact (MK_COMB (@lem7688919) (@lem7688918 A B y x z)). Qed.
Lemma lem7688942 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1004 A B y x z).
Proof. exact (eq_refl (term1004 A B y x z)). Qed.
Lemma lem7688943 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = ((term1004 A B y x z) = (term1004 A B y x z)).
Proof. exact (MK_COMB (@lem7688920 A B y x z) (@lem7688942 A B y x z)). Qed.
Lemma lem7688945 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7688946 (x : Prop) : (x = x) = True.
Proof. exact (@lem7688945 Prop x). Qed.
Lemma lem7688947 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term1004 A B y x z) = (term1004 A B y x z)) = True.
Proof. exact (@lem7688946 (term1004 A B y x z)). Qed.
Lemma lem7688948 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = True.
Proof. exact (TRANS (@lem7688943 A B y x z) (@lem7688947 A B y x z)). Qed.
Lemma lem7688949 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : True = ((term992 A B x y z) = (term1004 A B y x z)).
Proof. exact (SYM (@lem7688948 A B y x z)). Qed.
Lemma lem7688950 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (EQ_MP (@lem7688949 A B y x z) (@lem0)). Qed.
Lemma lem7688951 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : term1004 A B y x z.
Proof. exact (EQ_MP (@lem7688950 A B y x z) (@lem7688839 A B x y z)). Qed.
Lemma lem7688953 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7688954 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1008 A B x y z).
Proof. exact (@lem7688953 (term1009 A B y x z) (y = z)). Qed.
Lemma lem7688956 (a : Prop) (b : Prop) : (term1010 a b) = (term1011 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7688957 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1013 A B y x z).
Proof. exact (@lem7688956 (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7688959 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7688960 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1015 A B x y) = (x = y).
Proof. exact (@lem7688959 (x = y)). Qed.
Lemma lem7688961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7688962 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1016 A B x y) = (term1017 A B x y).
Proof. exact (MK_COMB (@lem7688961) (@lem7688960 A B x y)). Qed.
Lemma lem7688964 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7688965 {A B : Type'} (x : finite_diff A B) (z : finite_diff A B) : (term1015 A B x z) = (x = z).
Proof. exact (@lem7688964 (x = z)). Qed.
Lemma lem7688966 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1013 A B y x z) = (term1018 A B y x z).
Proof. exact (MK_COMB (@lem7688962 A B x y) (@lem7688965 A B x z)). Qed.
Lemma lem7688967 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1018 A B y x z).
Proof. exact (TRANS (@lem7688957 A B y x z) (@lem7688966 A B y x z)). Qed.
Lemma lem7688968 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7688969 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1019 A B y x z) = (term1020 A B y x z).
Proof. exact (MK_COMB (@lem7688968) (@lem7688967 A B y x z)). Qed.
Lemma lem7688970 {A B : Type'} (y : finite_diff A B) (z : finite_diff A B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7688971 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1008 A B x y z) = (term1021 A B x y z).
Proof. exact (MK_COMB (@lem7688969 A B y x z) (@lem7688970 A B y z)). Qed.
Lemma lem7688972 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1021 A B x y z).
Proof. exact (TRANS (@lem7688954 A B x y z) (@lem7688971 A B x y z)). Qed.
Lemma lem7688974 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term1022 A B x.
Proof. exact (conj (@lem7688852 A B x h1) (@lem7688861 A B x)). Qed.
Lemma lem7688976 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (EQ_MP (@lem7688972 A B x y z) (@lem7688951 A B y x z)). Qed.
Lemma lem7688977 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (@lem7688976 A B x y z). Qed.
Lemma lem7688978 {A B : Type'} (x : finite_diff A B) : term1023 A B x.
Proof. exact (@lem7688977 A B (term195 A B x) x (term195 A B x)). Qed.
Lemma lem7688981 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : x = (term195 A B x).
Proof. exact (@lem7688978 A B x (@lem7688974 A B x h1)). Qed.
Lemma lem7688982 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term1024 A B x.
Proof. exact (fun h0 : term1025 A B x => @lem7688981 A B x h1). Qed.
Lemma lem7688984 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688985 {A B : Type'} (x : finite_diff A B) : (term1024 A B x) = (x = (term195 A B x)).
Proof. exact (@lem7688984 (x = (term195 A B x))). Qed.
Lemma lem7688986 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : x = (term195 A B x).
Proof. exact (EQ_MP (@lem7688985 A B x) (@lem7688982 A B x h1)). Qed.
Lemma lem7688988 {A B : Type'} (_98867 : finite_diff A B) (x : finite_diff A B) (h1 : term876 A B x) : (term195 A B _98867) = _98867.
Proof. exact (EQ_MP (@lem7685695 A B _98867) (@lem7685694 A B _98867 x h1)). Qed.
Lemma lem7688989 {A B : Type'} (_98867 : finite_diff A B) (x : finite_diff A B) (h1 : term876 A B x) : (term195 A B _98867) = _98867.
Proof. exact (@lem7688988 A B _98867 x h1). Qed.
Lemma lem7688990 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : (term195 A B x) = x.
Proof. exact (@lem7688989 A B x x h1). Qed.
Lemma lem7688991 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7688990 A B x h1). Qed.
Lemma lem7688993 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7688994 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7688993 ((term195 A B x) = x)). Qed.
Lemma lem7688995 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7688994 A B x) (@lem7688991 A B x h1)). Qed.
Lemma lem7689001 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7689002 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : (term991 A B _99111 _99112) = (term1026 A B _99111 _99112).
Proof. exact (@lem7689001 ((@dest_finite_diff A B _99111) = (@dest_finite_diff A B _99112)) (term1000 A B _99111 _99112)). Qed.
Lemma lem7689012 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7689013 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : (term1027 A B _99111 _99112) = (term1028 A B _99111 _99112).
Proof. exact (MK_COMB (@lem7689012) (@lem7689002 A B _99111 _99112)). Qed.
Lemma lem7689023 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : (term1026 A B _99111 _99112) = (term1026 A B _99111 _99112).
Proof. exact (eq_refl (term1026 A B _99111 _99112)). Qed.
Lemma lem7689024 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : ((term991 A B _99111 _99112) = (term1026 A B _99111 _99112)) = ((term1026 A B _99111 _99112) = (term1026 A B _99111 _99112)).
Proof. exact (MK_COMB (@lem7689013 A B _99111 _99112) (@lem7689023 A B _99111 _99112)). Qed.
Lemma lem7689026 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7689027 (x : Prop) : (x = x) = True.
Proof. exact (@lem7689026 Prop x). Qed.
Lemma lem7689028 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : ((term1026 A B _99111 _99112) = (term1026 A B _99111 _99112)) = True.
Proof. exact (@lem7689027 (term1026 A B _99111 _99112)). Qed.
Lemma lem7689029 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : ((term991 A B _99111 _99112) = (term1026 A B _99111 _99112)) = True.
Proof. exact (TRANS (@lem7689024 A B _99111 _99112) (@lem7689028 A B _99111 _99112)). Qed.
Lemma lem7689030 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : True = ((term991 A B _99111 _99112) = (term1026 A B _99111 _99112)).
Proof. exact (SYM (@lem7689029 A B _99111 _99112)). Qed.
Lemma lem7689031 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : (term991 A B _99111 _99112) = (term1026 A B _99111 _99112).
Proof. exact (EQ_MP (@lem7689030 A B _99111 _99112) (@lem0)). Qed.
Lemma lem7689032 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : term1026 A B _99111 _99112.
Proof. exact (EQ_MP (@lem7689031 A B _99111 _99112) (@lem7688743 A B _99111 _99112)). Qed.
Lemma lem7689034 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7689035 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : (term1026 A B _99111 _99112) = (term1029 A B _99111 _99112).
Proof. exact (@lem7689034 (term1000 A B _99111 _99112) ((@dest_finite_diff A B _99111) = (@dest_finite_diff A B _99112))). Qed.
Lemma lem7689037 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7689038 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : (term1015 A B _99111 _99112) = (_99111 = _99112).
Proof. exact (@lem7689037 (_99111 = _99112)). Qed.
Lemma lem7689039 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7689040 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : (term1030 A B _99111 _99112) = (term1031 A B _99111 _99112).
Proof. exact (MK_COMB (@lem7689039) (@lem7689038 A B _99111 _99112)). Qed.
Lemma lem7689041 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : ((@dest_finite_diff A B _99111) = (@dest_finite_diff A B _99112)) = ((@dest_finite_diff A B _99111) = (@dest_finite_diff A B _99112)).
Proof. exact (eq_refl ((@dest_finite_diff A B _99111) = (@dest_finite_diff A B _99112))). Qed.
Lemma lem7689042 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : (term1029 A B _99111 _99112) = (term989 A B _99111 _99112).
Proof. exact (MK_COMB (@lem7689040 A B _99111 _99112) (@lem7689041 A B _99111 _99112)). Qed.
Lemma lem7689043 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : (term1026 A B _99111 _99112) = (term989 A B _99111 _99112).
Proof. exact (TRANS (@lem7689035 A B _99111 _99112) (@lem7689042 A B _99111 _99112)). Qed.
Lemma lem7689046 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : term989 A B _99111 _99112.
Proof. exact (EQ_MP (@lem7689043 A B _99111 _99112) (@lem7689032 A B _99111 _99112)). Qed.
Lemma lem7689047 {A B : Type'} (_99111 : finite_diff A B) (_99112 : finite_diff A B) : term989 A B _99111 _99112.
Proof. exact (@lem7689046 A B _99111 _99112). Qed.
Lemma lem7689048 {A B : Type'} (x : finite_diff A B) : term1032 A B x.
Proof. exact (@lem7689047 A B (term195 A B x) x). Qed.
Lemma lem7689051 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (@lem7689048 A B x (@lem7688995 A B x h1)). Qed.
Lemma lem7689052 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term1034 A B x.
Proof. exact (fun h0 : term1035 A B x => @lem7689051 A B x h1). Qed.
Lemma lem7689054 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7689055 {A B : Type'} (x : finite_diff A B) : (term1034 A B x) = ((term1033 A B x) = (@dest_finite_diff A B x)).
Proof. exact (@lem7689054 ((term1033 A B x) = (@dest_finite_diff A B x))). Qed.
Lemma lem7689056 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (EQ_MP (@lem7689055 A B x) (@lem7689052 A B x h1)). Qed.
Lemma lem7689058 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7689059 {A B : Type'} (_98868 : nat) : (term450 A B _98868) = (term1036 A B _98868).
Proof. exact (@lem7689058 (term1037 A B _98868) (term62 A B _98868)). Qed.
Lemma lem7689061 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7689062 {A B : Type'} (_98868 : nat) : (term1038 A B _98868) = ((term47 A B _98868) = _98868).
Proof. exact (@lem7689061 ((term47 A B _98868) = _98868)). Qed.
Lemma lem7689063 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7689064 {A B : Type'} (_98868 : nat) : (term1039 A B _98868) = (term1040 A B _98868).
Proof. exact (MK_COMB (@lem7689063) (@lem7689062 A B _98868)). Qed.
Lemma lem7689065 {A B : Type'} (_98868 : nat) : (term62 A B _98868) = (term62 A B _98868).
Proof. exact (eq_refl (term62 A B _98868)). Qed.
Lemma lem7689066 {A B : Type'} (_98868 : nat) : (term1036 A B _98868) = (term1041 A B _98868).
Proof. exact (MK_COMB (@lem7689064 A B _98868) (@lem7689065 A B _98868)). Qed.
Lemma lem7689067 {A B : Type'} (_98868 : nat) : (term450 A B _98868) = (term1041 A B _98868).
Proof. exact (TRANS (@lem7689059 A B _98868) (@lem7689066 A B _98868)). Qed.
Lemma lem7689070 {A B : Type'} (_98868 : nat) (x : finite_diff A B) (h1 : term876 A B x) : term1041 A B _98868.
Proof. exact (EQ_MP (@lem7689067 A B _98868) (@lem7686099 A B _98868 x h1)). Qed.
Lemma lem7689071 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term1042 A B x.
Proof. exact (@lem7689070 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7689074 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term1043 A B x.
Proof. exact (@lem7689071 A B x h1 (@lem7689056 A B x h1)). Qed.
Lemma lem7689075 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term1044 A B x.
Proof. exact (fun h0 : term1045 A B x => @lem7689074 A B x h1). Qed.
Lemma lem7689077 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7689078 {A B : Type'} (x : finite_diff A B) : (term1044 A B x) = (term1043 A B x).
Proof. exact (@lem7689077 (term1043 A B x)). Qed.
Lemma lem7689079 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term1043 A B x.
Proof. exact (EQ_MP (@lem7689078 A B x) (@lem7689075 A B x h1)). Qed.
Lemma lem7689081 (a : Prop) (b : Prop) : (term1046 a b) = (term1047 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7689082 {A B : Type'} (x : finite_diff A B) (_98863 : nat) : (term209 A B x _98863) = (term208 A B x _98863).
Proof. exact (@lem7689081 (x = (@mk_finite_diff A B _98863)) (term62 A B _98863)). Qed.
Lemma lem7689084 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7689085 {A B : Type'} (x : finite_diff A B) (_98863 : nat) : (term208 A B x _98863) = (term1048 A B x _98863).
Proof. exact (@lem7689084 (term63 A B x _98863)). Qed.
Lemma lem7689086 {A B : Type'} (x : finite_diff A B) (_98863 : nat) : (term209 A B x _98863) = (term1048 A B x _98863).
Proof. exact (TRANS (@lem7689082 A B x _98863) (@lem7689085 A B x _98863)). Qed.
Lemma lem7689088 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term1049 A B x.
Proof. exact (conj (@lem7688986 A B x h1) (@lem7689079 A B x h1)). Qed.
Lemma lem7689090 {A B : Type'} (_98863 : nat) (x : finite_diff A B) (h1 : term876 A B x) : term1048 A B x _98863.
Proof. exact (EQ_MP (@lem7689086 A B x _98863) (@lem7686077 A B _98863 x h1)). Qed.
Lemma lem7689091 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term1050 A B x.
Proof. exact (@lem7689090 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7689094 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : False.
Proof. exact (@lem7689091 A B x h1 (@lem7689088 A B x h1)). Qed.
Lemma lem7689095 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : term1051.
Proof. exact (fun h0 : ~ False => @lem7689094 A B x h1). Qed.
Lemma lem7689097 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7689098 : term1051 = False.
Proof. exact (@lem7689097 False). Qed.
Lemma lem7689099 {A B : Type'} (x : finite_diff A B) (h1 : term876 A B x) : False.
Proof. exact (EQ_MP (@lem7689098) (@lem7689095 A B x h1)). Qed.
Lemma lem7689154 {A B : Type'} : (@dest_finite_diff A B) = (@dest_finite_diff A B).
Proof. exact (eq_refl (@dest_finite_diff A B)). Qed.
Lemma lem7689155 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) (h1 : _99147 = _99148) : _99147 = _99148.
Proof. exact (h1). Qed.
Lemma lem7689156 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) (h1 : _99147 = _99148) : (@dest_finite_diff A B _99147) = (@dest_finite_diff A B _99148).
Proof. exact (MK_COMB (@lem7689154 A B) (@lem7689155 A B _99147 _99148 h1)). Qed.
Lemma lem7689157 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : term989 A B _99147 _99148.
Proof. exact (fun h0 : _99147 = _99148 => @lem7689156 A B _99147 _99148 h0). Qed.
Lemma lem7689159 (a : Prop) (b : Prop) : (a -> b) = (term990 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7689160 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : (term989 A B _99147 _99148) = (term991 A B _99147 _99148).
Proof. exact (@lem7689159 (_99147 = _99148) ((@dest_finite_diff A B _99147) = (@dest_finite_diff A B _99148))). Qed.
Lemma lem7689161 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : term991 A B _99147 _99148.
Proof. exact (EQ_MP (@lem7689160 A B _99147 _99148) (@lem7689157 A B _99147 _99148)). Qed.
Lemma lem7689242 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term992 A B x y z.
Proof. exact (@lem21385 (finite_diff A B) x y z). Qed.
Lemma lem7689248 {A B : Type'} (_98877 : finite_diff A B) (x : finite_diff A B) (h1 : term899 A B x) : (term195 A B _98877) = _98877.
Proof. exact (EQ_MP (@lem7685725 A B _98877) (@lem7685724 A B _98877 x h1)). Qed.
Lemma lem7689249 {A B : Type'} (_98877 : finite_diff A B) (x : finite_diff A B) (h1 : term899 A B x) : (term195 A B _98877) = _98877.
Proof. exact (@lem7689248 A B _98877 x h1). Qed.
Lemma lem7689250 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : (term195 A B x) = x.
Proof. exact (@lem7689249 A B x x h1). Qed.
Lemma lem7689251 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7689250 A B x h1). Qed.
Lemma lem7689253 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7689254 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7689253 ((term195 A B x) = x)). Qed.
Lemma lem7689255 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7689254 A B x) (@lem7689251 A B x h1)). Qed.
Lemma lem7689257 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem21386 (finite_diff A B) x). Qed.
Lemma lem7689258 {A B : Type'} (x : finite_diff A B) : x = x.
Proof. exact (@lem7689257 A B x). Qed.
Lemma lem7689259 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (@lem7689258 A B (term195 A B x)). Qed.
Lemma lem7689260 {A B : Type'} (x : finite_diff A B) : term996 A B x.
Proof. exact (fun h0 : term997 A B x => @lem7689259 A B x). Qed.
Lemma lem7689262 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7689263 {A B : Type'} (x : finite_diff A B) : (term996 A B x) = ((term195 A B x) = (term195 A B x)).
Proof. exact (@lem7689262 ((term195 A B x) = (term195 A B x))). Qed.
Lemma lem7689264 {A B : Type'} (x : finite_diff A B) : (term195 A B x) = (term195 A B x).
Proof. exact (EQ_MP (@lem7689263 A B x) (@lem7689260 A B x)). Qed.
Lemma lem7689282 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7689283 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term998 A B x y z) = (term999 A B y x z).
Proof. exact (@lem7689282 (y = z) (term1000 A B x z)). Qed.
Lemma lem7689293 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1001 A B x y) = (term1001 A B x y).
Proof. exact (eq_refl (term1001 A B x y)). Qed.
Lemma lem7689294 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1002 A B y x z).
Proof. exact (MK_COMB (@lem7689293 A B x y) (@lem7689283 A B y x z)). Qed.
Lemma lem7689298 (q : Prop) (p : Prop) (r : Prop) : (term1003 p q r) = (term1003 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7689299 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1002 A B y x z) = (term1004 A B y x z).
Proof. exact (@lem7689298 (y = z) (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7689321 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (TRANS (@lem7689294 A B y x z) (@lem7689299 A B y x z)). Qed.
Lemma lem7689322 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7689323 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1005 A B x y z) = (term1006 A B y x z).
Proof. exact (MK_COMB (@lem7689322) (@lem7689321 A B y x z)). Qed.
Lemma lem7689345 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1004 A B y x z).
Proof. exact (eq_refl (term1004 A B y x z)). Qed.
Lemma lem7689346 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = ((term1004 A B y x z) = (term1004 A B y x z)).
Proof. exact (MK_COMB (@lem7689323 A B y x z) (@lem7689345 A B y x z)). Qed.
Lemma lem7689348 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7689349 (x : Prop) : (x = x) = True.
Proof. exact (@lem7689348 Prop x). Qed.
Lemma lem7689350 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term1004 A B y x z) = (term1004 A B y x z)) = True.
Proof. exact (@lem7689349 (term1004 A B y x z)). Qed.
Lemma lem7689351 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : ((term992 A B x y z) = (term1004 A B y x z)) = True.
Proof. exact (TRANS (@lem7689346 A B y x z) (@lem7689350 A B y x z)). Qed.
Lemma lem7689352 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : True = ((term992 A B x y z) = (term1004 A B y x z)).
Proof. exact (SYM (@lem7689351 A B y x z)). Qed.
Lemma lem7689353 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term992 A B x y z) = (term1004 A B y x z).
Proof. exact (EQ_MP (@lem7689352 A B y x z) (@lem0)). Qed.
Lemma lem7689354 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : term1004 A B y x z.
Proof. exact (EQ_MP (@lem7689353 A B y x z) (@lem7689242 A B x y z)). Qed.
Lemma lem7689356 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7689357 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1008 A B x y z).
Proof. exact (@lem7689356 (term1009 A B y x z) (y = z)). Qed.
Lemma lem7689359 (a : Prop) (b : Prop) : (term1010 a b) = (term1011 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7689360 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1013 A B y x z).
Proof. exact (@lem7689359 (term1000 A B x y) (term1000 A B x z)). Qed.
Lemma lem7689362 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7689363 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1015 A B x y) = (x = y).
Proof. exact (@lem7689362 (x = y)). Qed.
Lemma lem7689364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7689365 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) : (term1016 A B x y) = (term1017 A B x y).
Proof. exact (MK_COMB (@lem7689364) (@lem7689363 A B x y)). Qed.
Lemma lem7689367 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7689368 {A B : Type'} (x : finite_diff A B) (z : finite_diff A B) : (term1015 A B x z) = (x = z).
Proof. exact (@lem7689367 (x = z)). Qed.
Lemma lem7689369 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1013 A B y x z) = (term1018 A B y x z).
Proof. exact (MK_COMB (@lem7689365 A B x y) (@lem7689368 A B x z)). Qed.
Lemma lem7689370 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1012 A B y x z) = (term1018 A B y x z).
Proof. exact (TRANS (@lem7689360 A B y x z) (@lem7689369 A B y x z)). Qed.
Lemma lem7689371 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7689372 {A B : Type'} (y : finite_diff A B) (x : finite_diff A B) (z : finite_diff A B) : (term1019 A B y x z) = (term1020 A B y x z).
Proof. exact (MK_COMB (@lem7689371) (@lem7689370 A B y x z)). Qed.
Lemma lem7689373 {A B : Type'} (y : finite_diff A B) (z : finite_diff A B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7689374 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1008 A B x y z) = (term1021 A B x y z).
Proof. exact (MK_COMB (@lem7689372 A B y x z) (@lem7689373 A B y z)). Qed.
Lemma lem7689375 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : (term1004 A B y x z) = (term1021 A B x y z).
Proof. exact (TRANS (@lem7689357 A B x y z) (@lem7689374 A B x y z)). Qed.
Lemma lem7689377 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term1022 A B x.
Proof. exact (conj (@lem7689255 A B x h1) (@lem7689264 A B x)). Qed.
Lemma lem7689379 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (EQ_MP (@lem7689375 A B x y z) (@lem7689354 A B y x z)). Qed.
Lemma lem7689380 {A B : Type'} (x : finite_diff A B) (y : finite_diff A B) (z : finite_diff A B) : term1021 A B x y z.
Proof. exact (@lem7689379 A B x y z). Qed.
Lemma lem7689381 {A B : Type'} (x : finite_diff A B) : term1023 A B x.
Proof. exact (@lem7689380 A B (term195 A B x) x (term195 A B x)). Qed.
Lemma lem7689384 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : x = (term195 A B x).
Proof. exact (@lem7689381 A B x (@lem7689377 A B x h1)). Qed.
Lemma lem7689385 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term1024 A B x.
Proof. exact (fun h0 : term1025 A B x => @lem7689384 A B x h1). Qed.
Lemma lem7689387 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7689388 {A B : Type'} (x : finite_diff A B) : (term1024 A B x) = (x = (term195 A B x)).
Proof. exact (@lem7689387 (x = (term195 A B x))). Qed.
Lemma lem7689389 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : x = (term195 A B x).
Proof. exact (EQ_MP (@lem7689388 A B x) (@lem7689385 A B x h1)). Qed.
Lemma lem7689391 {A B : Type'} (_98877 : finite_diff A B) (x : finite_diff A B) (h1 : term899 A B x) : (term195 A B _98877) = _98877.
Proof. exact (EQ_MP (@lem7685725 A B _98877) (@lem7685724 A B _98877 x h1)). Qed.
Lemma lem7689392 {A B : Type'} (_98877 : finite_diff A B) (x : finite_diff A B) (h1 : term899 A B x) : (term195 A B _98877) = _98877.
Proof. exact (@lem7689391 A B _98877 x h1). Qed.
Lemma lem7689393 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : (term195 A B x) = x.
Proof. exact (@lem7689392 A B x x h1). Qed.
Lemma lem7689394 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term993 A B x.
Proof. exact (fun h0 : term994 A B x => @lem7689393 A B x h1). Qed.
Lemma lem7689396 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7689397 {A B : Type'} (x : finite_diff A B) : (term993 A B x) = ((term195 A B x) = x).
Proof. exact (@lem7689396 ((term195 A B x) = x)). Qed.
Lemma lem7689398 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : (term195 A B x) = x.
Proof. exact (EQ_MP (@lem7689397 A B x) (@lem7689394 A B x h1)). Qed.
Lemma lem7689404 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7689405 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : (term991 A B _99147 _99148) = (term1026 A B _99147 _99148).
Proof. exact (@lem7689404 ((@dest_finite_diff A B _99147) = (@dest_finite_diff A B _99148)) (term1000 A B _99147 _99148)). Qed.
Lemma lem7689415 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7689416 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : (term1027 A B _99147 _99148) = (term1028 A B _99147 _99148).
Proof. exact (MK_COMB (@lem7689415) (@lem7689405 A B _99147 _99148)). Qed.
Lemma lem7689426 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : (term1026 A B _99147 _99148) = (term1026 A B _99147 _99148).
Proof. exact (eq_refl (term1026 A B _99147 _99148)). Qed.
Lemma lem7689427 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : ((term991 A B _99147 _99148) = (term1026 A B _99147 _99148)) = ((term1026 A B _99147 _99148) = (term1026 A B _99147 _99148)).
Proof. exact (MK_COMB (@lem7689416 A B _99147 _99148) (@lem7689426 A B _99147 _99148)). Qed.
Lemma lem7689429 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7689430 (x : Prop) : (x = x) = True.
Proof. exact (@lem7689429 Prop x). Qed.
Lemma lem7689431 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : ((term1026 A B _99147 _99148) = (term1026 A B _99147 _99148)) = True.
Proof. exact (@lem7689430 (term1026 A B _99147 _99148)). Qed.
Lemma lem7689432 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : ((term991 A B _99147 _99148) = (term1026 A B _99147 _99148)) = True.
Proof. exact (TRANS (@lem7689427 A B _99147 _99148) (@lem7689431 A B _99147 _99148)). Qed.
Lemma lem7689433 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : True = ((term991 A B _99147 _99148) = (term1026 A B _99147 _99148)).
Proof. exact (SYM (@lem7689432 A B _99147 _99148)). Qed.
Lemma lem7689434 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : (term991 A B _99147 _99148) = (term1026 A B _99147 _99148).
Proof. exact (EQ_MP (@lem7689433 A B _99147 _99148) (@lem0)). Qed.
Lemma lem7689435 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : term1026 A B _99147 _99148.
Proof. exact (EQ_MP (@lem7689434 A B _99147 _99148) (@lem7689161 A B _99147 _99148)). Qed.
Lemma lem7689437 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7689438 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : (term1026 A B _99147 _99148) = (term1029 A B _99147 _99148).
Proof. exact (@lem7689437 (term1000 A B _99147 _99148) ((@dest_finite_diff A B _99147) = (@dest_finite_diff A B _99148))). Qed.
Lemma lem7689440 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7689441 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : (term1015 A B _99147 _99148) = (_99147 = _99148).
Proof. exact (@lem7689440 (_99147 = _99148)). Qed.
Lemma lem7689442 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7689443 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : (term1030 A B _99147 _99148) = (term1031 A B _99147 _99148).
Proof. exact (MK_COMB (@lem7689442) (@lem7689441 A B _99147 _99148)). Qed.
Lemma lem7689444 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : ((@dest_finite_diff A B _99147) = (@dest_finite_diff A B _99148)) = ((@dest_finite_diff A B _99147) = (@dest_finite_diff A B _99148)).
Proof. exact (eq_refl ((@dest_finite_diff A B _99147) = (@dest_finite_diff A B _99148))). Qed.
Lemma lem7689445 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : (term1029 A B _99147 _99148) = (term989 A B _99147 _99148).
Proof. exact (MK_COMB (@lem7689443 A B _99147 _99148) (@lem7689444 A B _99147 _99148)). Qed.
Lemma lem7689446 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : (term1026 A B _99147 _99148) = (term989 A B _99147 _99148).
Proof. exact (TRANS (@lem7689438 A B _99147 _99148) (@lem7689445 A B _99147 _99148)). Qed.
Lemma lem7689449 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : term989 A B _99147 _99148.
Proof. exact (EQ_MP (@lem7689446 A B _99147 _99148) (@lem7689435 A B _99147 _99148)). Qed.
Lemma lem7689450 {A B : Type'} (_99147 : finite_diff A B) (_99148 : finite_diff A B) : term989 A B _99147 _99148.
Proof. exact (@lem7689449 A B _99147 _99148). Qed.
Lemma lem7689451 {A B : Type'} (x : finite_diff A B) : term1032 A B x.
Proof. exact (@lem7689450 A B (term195 A B x) x). Qed.
Lemma lem7689454 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (@lem7689451 A B x (@lem7689398 A B x h1)). Qed.
Lemma lem7689455 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term1034 A B x.
Proof. exact (fun h0 : term1035 A B x => @lem7689454 A B x h1). Qed.
Lemma lem7689457 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7689458 {A B : Type'} (x : finite_diff A B) : (term1034 A B x) = ((term1033 A B x) = (@dest_finite_diff A B x)).
Proof. exact (@lem7689457 ((term1033 A B x) = (@dest_finite_diff A B x))). Qed.
Lemma lem7689459 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : (term1033 A B x) = (@dest_finite_diff A B x).
Proof. exact (EQ_MP (@lem7689458 A B x) (@lem7689455 A B x h1)). Qed.
Lemma lem7689461 (b : Prop) (a : Prop) : (a \/ b) = (term1007 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7689462 {A B : Type'} (_98878 : nat) : (term480 A B _98878) = (term1052 A B _98878).
Proof. exact (@lem7689461 (term1037 A B _98878) (term32 _98878)). Qed.
Lemma lem7689464 (a : Prop) : (term1014 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7689465 {A B : Type'} (_98878 : nat) : (term1038 A B _98878) = ((term47 A B _98878) = _98878).
Proof. exact (@lem7689464 ((term47 A B _98878) = _98878)). Qed.
Lemma lem7689466 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7689467 {A B : Type'} (_98878 : nat) : (term1039 A B _98878) = (term1040 A B _98878).
Proof. exact (MK_COMB (@lem7689466) (@lem7689465 A B _98878)). Qed.
Lemma lem7689468 (_98878 : nat) : (term32 _98878) = (term32 _98878).
Proof. exact (eq_refl (term32 _98878)). Qed.
Lemma lem7689469 {A B : Type'} (_98878 : nat) : (term1052 A B _98878) = (term1053 A B _98878).
Proof. exact (MK_COMB (@lem7689467 A B _98878) (@lem7689468 _98878)). Qed.
Lemma lem7689470 {A B : Type'} (_98878 : nat) : (term480 A B _98878) = (term1053 A B _98878).
Proof. exact (TRANS (@lem7689462 A B _98878) (@lem7689469 A B _98878)). Qed.
Lemma lem7689473 {A B : Type'} (_98878 : nat) (x : finite_diff A B) (h1 : term899 A B x) : term1053 A B _98878.
Proof. exact (EQ_MP (@lem7689470 A B _98878) (@lem7686153 A B _98878 x h1)). Qed.
Lemma lem7689474 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term1054 A B x.
Proof. exact (@lem7689473 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7689477 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term1055 A B x.
Proof. exact (@lem7689474 A B x h1 (@lem7689459 A B x h1)). Qed.
Lemma lem7689478 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term1056 A B x.
Proof. exact (fun h0 : term1057 A B x => @lem7689477 A B x h1). Qed.
Lemma lem7689480 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7689481 {A B : Type'} (x : finite_diff A B) : (term1056 A B x) = (term1055 A B x).
Proof. exact (@lem7689480 (term1055 A B x)). Qed.
Lemma lem7689482 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term1055 A B x.
Proof. exact (EQ_MP (@lem7689481 A B x) (@lem7689478 A B x h1)). Qed.
Lemma lem7689484 (a : Prop) (b : Prop) : (term1046 a b) = (term1047 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7689485 {A B : Type'} (x : finite_diff A B) (_98873 : nat) : (term258 A B x _98873) = (term257 A B x _98873).
Proof. exact (@lem7689484 (x = (@mk_finite_diff A B _98873)) (term32 _98873)). Qed.
Lemma lem7689487 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7689488 {A B : Type'} (x : finite_diff A B) (_98873 : nat) : (term257 A B x _98873) = (term1058 A B x _98873).
Proof. exact (@lem7689487 (term35 A B x _98873)). Qed.
Lemma lem7689489 {A B : Type'} (x : finite_diff A B) (_98873 : nat) : (term258 A B x _98873) = (term1058 A B x _98873).
Proof. exact (TRANS (@lem7689485 A B x _98873) (@lem7689488 A B x _98873)). Qed.
Lemma lem7689491 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term1059 A B x.
Proof. exact (conj (@lem7689389 A B x h1) (@lem7689482 A B x h1)). Qed.
Lemma lem7689493 {A B : Type'} (_98873 : nat) (x : finite_diff A B) (h1 : term899 A B x) : term1058 A B x _98873.
Proof. exact (EQ_MP (@lem7689489 A B x _98873) (@lem7686131 A B _98873 x h1)). Qed.
Lemma lem7689494 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term1060 A B x.
Proof. exact (@lem7689493 A B (@dest_finite_diff A B x) x h1). Qed.
Lemma lem7689497 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : False.
Proof. exact (@lem7689494 A B x h1 (@lem7689491 A B x h1)). Qed.
Lemma lem7689498 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : term1051.
Proof. exact (fun h0 : ~ False => @lem7689497 A B x h1). Qed.
Lemma lem7689500 (p : Prop) : (term995 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7689501 : term1051 = False.
Proof. exact (@lem7689500 False). Qed.
Lemma lem7689502 {A B : Type'} (x : finite_diff A B) (h1 : term899 A B x) : False.
Proof. exact (EQ_MP (@lem7689501) (@lem7689498 A B x h1)). Qed.
Lemma lem7689503 {A B : Type'} (x : finite_diff A B) (h1 : term931 A B x) : False.
Proof. exact (or_elim (@lem7684466 A B x h1) (fun h0 : term876 A B x => @lem7689099 A B x h0) (fun h0 : term899 A B x => @lem7689502 A B x h0)). Qed.
Lemma lem7689504 {A B : Type'} (x : finite_diff A B) (h1 : term853 A B x) : False.
Proof. exact (or_elim (@lem7684422 A B x h1) (fun h0 : term798 A B x => @lem7688263 A B x h0) (fun h0 : term821 A B x => @lem7688681 A B x h0)). Qed.
Lemma lem7689505 {A B : Type'} (x : finite_diff A B) (h1 : term963 A B x) : False.
Proof. exact (or_elim (@lem7684418 A B x h1) (fun h0 : term853 A B x => @lem7689504 A B x h0) (fun h0 : term931 A B x => @lem7689503 A B x h0)). Qed.
Lemma lem7689506 {A B : Type'} (x : finite_diff A B) (h1 : term743 A B x) : False.
Proof. exact (or_elim (@lem7684374 A B x h1) (fun h0 : term688 A B x => @lem7687427 A B x h0) (fun h0 : term711 A B x => @lem7687845 A B x h0)). Qed.
Lemma lem7689507 {A B : Type'} (x : finite_diff A B) (h1 : term665 A B x) : False.
Proof. exact (or_elim (@lem7684330 A B x h1) (fun h0 : term600 A B x => @lem7686591 A B x h0) (fun h0 : term629 A B x => @lem7687009 A B x h0)). Qed.
Lemma lem7689508 {A B : Type'} (x : finite_diff A B) (h1 : term775 A B x) : False.
Proof. exact (or_elim (@lem7684326 A B x h1) (fun h0 : term665 A B x => @lem7689507 A B x h0) (fun h0 : term743 A B x => @lem7689506 A B x h0)). Qed.
Lemma lem7689509 {A B : Type'} (x : finite_diff A B) (h1 : term982 A B x) : False.
Proof. exact (or_elim (@lem7684323 A B x h1) (fun h0 : term775 A B x => @lem7689508 A B x h0) (fun h0 : term963 A B x => @lem7689505 A B x h0)). Qed.
Lemma lem7689510 {A B : Type'} (x : finite_diff A B) (h1 : term982 A B x) : (term982 A B x) = False.
Proof. exact (prop_ext (fun h2 : term982 A B x => @lem7689509 A B x h1) (fun h2 : False => @lem7684323 A B x h1)). Qed.
Lemma lem7689511 {A B : Type'} (x : finite_diff A B) (h1 : term982 A B x) : False.
Proof. exact (EQ_MP (@lem7689510 A B x h1) (@lem7684323 A B x h1)). Qed.
Lemma lem7689512 {A B : Type'} (h1 : term205 A B) : False.
Proof. exact (ex_elim (@lem7681598 A B h1) (fun x : finite_diff A B => fun h0 : term984 A B x => @lem7689511 A B x h0)). Qed.
Lemma lem7689513 {A B : Type'} (h1 : term205 A B) : (term205 A B) = False.
Proof. exact (prop_ext (fun h2 : term205 A B => @lem7689512 A B h1) (fun h2 : False => @lem7676154 A B h1)). Qed.
Lemma lem7689514 {A B : Type'} (h1 : term205 A B) : False.
Proof. exact (EQ_MP (@lem7689513 A B h1) (@lem7676154 A B h1)). Qed.
Lemma lem7689515 {A B : Type'} : term204 A B.
Proof. exact (fun h0 : term205 A B => @lem7689514 A B h0). Qed.
Lemma lem7689516 {A B : Type'} : term191 A B.
Proof. exact (EQ_MP (@lem7676153 A B) (@lem7689515 A B)). Qed.
Lemma lem7689517 {A B : Type'} : term6 A B.
Proof. exact (EQ_MP (@lem7676149 A B) (@lem7689516 A B)). Qed.
Lemma lem7689519 {A B : Type'} : term6 A B.
Proof. exact (@lem7673153 A B (@lem7689517 A B)). Qed.
Lemma lem7689520 {A B : Type'} (h1 : term3 A B) : term16 A B.
Proof. exact (@lem7689519 A B (@lem7673127 A B h1)). Qed.
Lemma lem7689521 {A B : Type'} (h1 : term3 A B) : term13 A B.
Proof. exact (@lem7689520 A B h1 (@lem7673131 A)). Qed.
Lemma lem7689522 {A B : Type'} (h1 : term3 A B) : term10 B.
Proof. exact (@lem7689521 A B h1 (@lem7673128 A B)). Qed.
Lemma lem7689523 {A B : Type'} (h1 : term3 A B) : False.
Proof. exact (@lem7689522 A B h1 (@lem7673134 B)). Qed.
Lemma lem7689524 {A B : Type'} (h1 : term3 A B) : (term3 A B) = False.
Proof. exact (prop_ext (fun h2 : term3 A B => @lem7689523 A B h1) (fun h2 : False => @lem7673127 A B h1)). Qed.
Lemma lem7689525 {A B : Type'} (h1 : term3 A B) : False.
Proof. exact (EQ_MP (@lem7689524 A B h1) (@lem7673127 A B h1)). Qed.
Lemma lem7689526 {A B : Type'} : term2 A B.
Proof. exact (fun h0 : term3 A B => @lem7689525 A B h0). Qed.
Lemma lem7689527 {A B : Type'} : term1 A B.
Proof. exact (EQ_MP (@lem7673126 A B) (@lem7689526 A B)). Qed.
